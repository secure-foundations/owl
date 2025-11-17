{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Timestamping where

import AST
import TypingBase
import qualified PathResolution
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Bind
import Unbound.Generics.LocallyNameless.Name
import Unbound.Generics.LocallyNameless.Fresh
import Control.Lens
import Control.Monad.State
import Control.Monad
import Control.Monad.Trans
import Data.IORef
import Data.Maybe

-- State for timestamp generation
data TimestampState = TimestampState {
    _tsCounter :: IORef Integer,
    _tsConstraints :: IORef [TimestampConstraint],
    _tsCurrentTimestamp :: Timestamp,
    _tsDefName :: Maybe String
}

makeLenses ''TimestampState


-- Manage timestamp name generation. We fix the start and end timestamp names for each routine
-- to allow for subroutine calls to be ordered. 

freshTimestampRaw :: String -> Maybe Integer -> String -> Timestamp
freshTimestampRaw defName (Just n) baseName =
    Timestamp $ "t_" ++ defName ++ "_" ++ baseName ++ "_" ++ show n
freshTimestampRaw defName Nothing baseName =
    Timestamp $ "t_" ++ defName ++ "_" ++ baseName

startTs :: String -> Timestamp
startTs defName = freshTimestampRaw defName Nothing "start"

endTs :: String -> Timestamp
endTs defName = freshTimestampRaw defName Nothing "end"

freshTimestamp :: String -> StateT TimestampState (FreshMT IO) Timestamp
freshTimestamp baseName = do
    counter <- use tsCounter
    n <- liftIO $ do
        v <- readIORef counter
        writeIORef counter (v + 1)
        return v
    defName' <- use tsDefName
    let defPrefix = case defName' of
                      Just d -> d
                      Nothing -> "unknown"
    return $ freshTimestampRaw defPrefix (Just n) baseName

-- Add a timestamp constraint
addTimestampConstraint :: Timestamp -> Timestamp -> StateT TimestampState (FreshMT IO) ()
addTimestampConstraint t1 t2 = do
    constraints <- use tsConstraints
    liftIO $ modifyIORef constraints (\cs -> TimestampLeq t1 t2 : cs)

-- Set current timestamp
setCurrentTimestamp :: Timestamp -> StateT TimestampState (FreshMT IO) a -> StateT TimestampState (FreshMT IO) a
setCurrentTimestamp ts action = do
    oldTs <- use tsCurrentTimestamp
    modify (set tsCurrentTimestamp ts)
    result <- action
    modify (set tsCurrentTimestamp oldTs)
    return result

-- Get current timestamp
getCurrentTimestamp :: StateT TimestampState (FreshMT IO) Timestamp
getCurrentTimestamp = use tsCurrentTimestamp

-- Extract timestamp from an expression
extractTimestamp :: Expr -> Timestamp
extractTimestamp e = unignore $ e^.val.timestampOf

-- Timestamp an expression
timestampExpr :: Expr -> StateT TimestampState (FreshMT IO) (Timestamp, Expr)
timestampExpr e = do
    case e^.exprVal of
      -- Operations that increment timestamp
      EInput sx xsk -> do
          curTs <- getCurrentTimestamp
          ts <- freshTimestamp "input"
          addTimestampConstraint curTs ts
          tsAfter <- freshTimestamp "after_input"
          addTimestampConstraint ts tsAfter
          ((x, s), k) <- unbind xsk
          (endk, k') <- setCurrentTimestamp tsAfter $ timestampExpr k
          return $ (,) endk $ Spanned (e^.spanOf) $ Timestamped (ignore ts) $ EInput sx (bind (x, s) k')
      
      EOutput a ep -> do
          curTs <- getCurrentTimestamp
          ts <- freshTimestamp "output"
          addTimestampConstraint curTs ts
          tsAfter <- freshTimestamp "after_output"
          addTimestampConstraint ts tsAfter
          return $ (,) tsAfter $ Spanned (e^.spanOf) $ Timestamped (ignore ts) $ EOutput a ep
      
      ECall f (is1, is2) args -> do
          curTs <- getCurrentTimestamp
          ts <- freshTimestamp "call"
          tsAfter <- freshTimestamp "after_call"
          addTimestampConstraint curTs ts
          addTimestampConstraint ts tsAfter -- should be able to remove once below is done
          -- TODO: need something like the following but have to resolve paths
        --   let subroutineStartTs = startTs f
        --   addTimestampConstraint ts subroutineStartTs
        --   let subroutineEndTs = endTs f
        --   addTimestampConstraint subroutineEndTs tsAfter
          return $ (,) tsAfter $ Spanned (e^.spanOf) $ Timestamped (ignore ts) $ ECall f (is1, is2) args
      
      -- Control flow constructs
      EIf a e1 e2 -> do
          curTs <- getCurrentTimestamp
          ts <- freshTimestamp "if"
          addTimestampConstraint curTs ts
          tsThen <- freshTimestamp "if_then"
          tsElse <- freshTimestamp "if_else"
          addTimestampConstraint ts tsThen
          addTimestampConstraint ts tsElse
          (ende1, e1') <- setCurrentTimestamp tsThen $ timestampExpr e1
          (ende2, e2') <- setCurrentTimestamp tsElse $ timestampExpr e2
          tsEnd <- freshTimestamp "if_end"
          addTimestampConstraint ende1 tsEnd
          addTimestampConstraint ende2 tsEnd
          return $ (,) tsEnd $ Spanned (e^.spanOf) $ Timestamped (ignore ts) $ EIf a e1' e2'
      
      ECase e1 otk cases -> do
          curTs <- getCurrentTimestamp
          ts <- freshTimestamp "case"
          addTimestampConstraint curTs ts
          (e1EndT, e1') <- timestampExpr e1
          -- Generate timestamps for each branch
          branchTimestamps <- forM cases $ \(c, _) -> do
              tsBranch <- freshTimestamp ("case_" ++ c)
              addTimestampConstraint ts tsBranch
              return (c, tsBranch)
          cases'WithTs <- forM (zip cases branchTimestamps) $ \((c, cse), (_, tsBranch)) -> do
              case cse of
                Left ek -> do
                    (ekEndT, ek') <- setCurrentTimestamp tsBranch $ timestampExpr ek
                    return (c, Left ek', ekEndT)
                Right (xs, bnd) -> do
                    (x, k) <- unbind bnd
                    (kEndT, k') <- setCurrentTimestamp tsBranch $ timestampExpr k
                    return (c, Right (xs, bind x k'), kEndT)
          let cases' = map (\(c, cse, _) -> (c, cse)) cases'WithTs
          let branchEndTimestamps = map (\(_, _, endT) -> endT) cases'WithTs
          -- Handle otherwise branch
          (otk', tsOtherwise, tsOtherwiseEnd) <- case otk of
              Just (t, k) -> do
                  tsOther <- freshTimestamp "case_otherwise"
                  addTimestampConstraint ts tsOther
                  (otEndT, k') <- setCurrentTimestamp tsOther $ timestampExpr k
                  return (Just (t, k'), Just tsOther, Just otEndT)
              Nothing -> return (Nothing, Nothing, Nothing)
          -- Add constraints from all branches to end
          tsEnd <- freshTimestamp "case_end"
          forM_ branchEndTimestamps $ \tsBranch -> do
              addTimestampConstraint tsBranch tsEnd
          case tsOtherwise of
            Just tsOther -> addTimestampConstraint tsOther tsEnd
            Nothing -> return ()
          return $ (,) tsEnd $ Spanned (e^.spanOf) $ Timestamped (ignore ts) $ ECase e1' otk' cases'
      
      -- EParse can do control flow in case the parse fails
      EParse a t (Just otwk) bk -> do
          curTs <- getCurrentTimestamp
          parseStartTs <- freshTimestamp "parse"
          addTimestampConstraint curTs parseStartTs
          tsParseOk <- freshTimestamp "parse_ok"
          tsParseFail <- freshTimestamp "parse_fail"
          addTimestampConstraint parseStartTs tsParseOk
          addTimestampConstraint parseStartTs tsParseFail
          (otwkEndT, otwk') <- setCurrentTimestamp tsParseFail $ timestampExpr otwk
          (b, k) <- unbind bk
          (kEndT, k') <- setCurrentTimestamp tsParseOk $ timestampExpr k
          tsEnd <- freshTimestamp "parse_end"
          addTimestampConstraint tsParseOk tsEnd
          addTimestampConstraint tsParseFail tsEnd
          return $ (,) tsEnd $ Spanned (e^.spanOf) $ Timestamped (ignore parseStartTs) $ EParse a t (Just otwk') (bind b k')

      -- EParse can do control flow in case the parse fails
      EParse a t Nothing bk -> do
          curTs <- getCurrentTimestamp
          (b, k) <- unbind bk
          (kEndT, k') <- timestampExpr k
          return $ (,) kEndT $ Spanned (e^.spanOf) $ Timestamped (ignore curTs) $ EParse a t Nothing (bind b k')

      -- Expressions that don't increment timestamp but need to thread timestamp through to continuation

      -- `let x = e in k` expression gets the end timestamp of `e`, corresponding to when the "assignment to x" is done
      -- We thread the end timestamp of `e` as the current timestamp when timestamping `k`
      ELet e1 tyAnn anf sx xk -> do
          (e1EndT, e1') <- timestampExpr e1
          (x, k) <- unbind xk
          (kEndT, k') <- setCurrentTimestamp e1EndT $ timestampExpr k
          return $ (,) kEndT $ Spanned (e^.spanOf) $ Timestamped (ignore e1EndT) $ ELet e1' tyAnn anf sx (bind x k')
      
      ELetGhost a sx xk -> do
          (x, k) <- unbind xk
          (kEndT, k') <- timestampExpr k
          curTs <- getCurrentTimestamp
          return $ (,) kEndT $ Spanned (e^.spanOf) $ Timestamped (ignore curTs) $ ELetGhost a sx (bind x k')
      
      EBlock k b -> do
          (kEndT, k') <- timestampExpr k
          curTs <- getCurrentTimestamp
          return $ (,) kEndT $ Spanned (e^.spanOf) $ Timestamped (ignore curTs) $ EBlock k' b
      
      EUnpack a s ixe -> do
          ((i, x), e_) <- unbind ixe
          (e'EndT, e') <- timestampExpr e_
          curTs <- getCurrentTimestamp
          return $ (,) e'EndT $ Spanned (e^.spanOf) $ Timestamped (ignore curTs) $ EUnpack a s (bind (i, x) e')
      
      EChooseIdx s ip ik -> do
          (i, k) <- unbind ik
          (kEndT, k') <- timestampExpr k
          curTs <- getCurrentTimestamp
          return $ (,) kEndT $ Spanned (e^.spanOf) $ Timestamped (ignore curTs) $ EChooseIdx s ip (bind i k')
      
      EChooseBV s ip ik -> do
          (y, k) <- unbind ik
          (kEndT, k') <- timestampExpr k
          curTs <- getCurrentTimestamp
          return $ (,) kEndT $ Spanned (e^.spanOf) $ Timestamped (ignore curTs) $ EChooseBV s ip (bind y k')
      
      EPackIdx i e1 -> do
          (e1EndT, e1') <- timestampExpr e1
          curTs <- getCurrentTimestamp
          return $ (,) e1EndT $ Spanned (e^.spanOf) $ Timestamped (ignore curTs) $ EPackIdx i e1'
      
      EGuard a k -> do
          (kEndT, k') <- timestampExpr k
          curTs <- getCurrentTimestamp
          return $ (,) kEndT $ Spanned (e^.spanOf) $ Timestamped (ignore curTs) $ EGuard a k'
      
      EForallBV s xpk -> do
          (x, (op, k)) <- unbind xpk
          (kEndT, k') <- timestampExpr k
          curTs <- getCurrentTimestamp
          return $ (,) kEndT $ Spanned (e^.spanOf) $ Timestamped (ignore curTs) $ EForallBV s (bind x (op, k'))
      
      EForallIdx s xpk -> do
          (x, (op, k)) <- unbind xpk
          (kEndT, k') <- timestampExpr k
          curTs <- getCurrentTimestamp
          return $ (,) kEndT $ Spanned (e^.spanOf) $ Timestamped (ignore curTs) $ EForallIdx s (bind x (op, k'))
      
      EPCase p op ob k -> do
          (kEndT, k') <- timestampExpr k
          curTs <- getCurrentTimestamp
          return $ (,) kEndT $ Spanned (e^.spanOf) $ Timestamped (ignore curTs) $ EPCase p op ob k'

      EOpenTyOf a k -> do
          (kEndT, k') <- timestampExpr k
          curTs <- getCurrentTimestamp
          return $ (,) kEndT $ Spanned (e^.spanOf) $ Timestamped (ignore curTs) $ EOpenTyOf a k'
      
      ECorrCaseNameOf a op k -> do
          (kEndT, k') <- timestampExpr k
          curTs <- getCurrentTimestamp
          return $ (,) kEndT $ Spanned (e^.spanOf) $ Timestamped (ignore curTs) $ ECorrCaseNameOf a op k'
      
      ESetOption s1 s2 k -> do
          (kEndT, k') <- timestampExpr k
          curTs <- getCurrentTimestamp
          return $ (,) kEndT $ Spanned (e^.spanOf) $ Timestamped (ignore curTs) $ ESetOption s1 s2 k'
      
      EFalseElim k op -> do
          (kEndT, k') <- timestampExpr k
          curTs <- getCurrentTimestamp
          return $ (,) kEndT $ Spanned (e^.spanOf) $ Timestamped (ignore curTs) $ EFalseElim k' op
      
      EDebug dc -> do
          case dc of
            DebugPrintExpr e' -> do
                (e'EndT, e'') <- timestampExpr e'
                curTs <- getCurrentTimestamp
                return $ (,) e'EndT $ Spanned (e^.spanOf) $ Timestamped (ignore curTs) $ EDebug (DebugPrintExpr e'')
            _ -> do
                curTs <- getCurrentTimestamp
                return $ (,) curTs $ Spanned (e^.spanOf) $ Timestamped (ignore curTs) $ EDebug dc
      
      -- Expressions that don't need traversal but use current timestamp
      ERet a -> do
          curTs <- getCurrentTimestamp
          return $ (,) curTs $ Spanned (e^.spanOf) $ Timestamped (ignore curTs) $ ERet a
      ECrypt cop aes -> do
          curTs <- getCurrentTimestamp
          return $ (,) curTs $ Spanned (e^.spanOf) $ Timestamped (ignore curTs) $ ECrypt cop aes
      EGetCtr p ps -> do
          curTs <- getCurrentTimestamp
          return $ (,) curTs $ Spanned (e^.spanOf) $ Timestamped (ignore curTs) $ EGetCtr p ps
      EIncCtr p ps -> do
          curTs <- getCurrentTimestamp
          return $ (,) curTs $ Spanned (e^.spanOf) $ Timestamped (ignore curTs) $ EIncCtr p ps
      EAssert p -> do
          curTs <- getCurrentTimestamp
          return $ (,) curTs $ Spanned (e^.spanOf) $ Timestamped (ignore curTs) $ EAssert p
      EAssume p -> do
          curTs <- getCurrentTimestamp
          return $ (,) curTs $ Spanned (e^.spanOf) $ Timestamped (ignore curTs) $ EAssume p
      EAdmit -> do
          curTs <- getCurrentTimestamp
          return $ (,) curTs $ Spanned (e^.spanOf) $ Timestamped (ignore curTs) $ EAdmit
      ETLookup n a -> do
          curTs <- getCurrentTimestamp
          return $ (,) curTs $ Spanned (e^.spanOf) $ Timestamped (ignore curTs) $ ETLookup n a
      ETWrite n a1 a2 -> do
          curTs <- getCurrentTimestamp
          return $ (,) curTs $ Spanned (e^.spanOf) $ Timestamped (ignore curTs) $ ETWrite n a1 a2

-- Timestamp a definition body
-- Definition `foo` will always start at timestamp `t_foo_start` and end at `t_foo_end`.
-- Internal timestamps within the body will be named `t_foo_<base>_<n>` where `<base>` is 
-- a descriptive name of the operation and `<n>` is a unique counter. There should be no name clashes
-- The `start` and `end` timestamps must be fixed because they determine ordering between subroutine calls.
timestampDef :: String -> Expr -> IO (Expr, [TimestampConstraint])
timestampDef defName body = do
    counter <- newIORef 0
    constraints <- newIORef []
    let initialState = TimestampState {
            _tsCounter = counter,
            _tsConstraints = constraints,
            _tsCurrentTimestamp = startTs defName,
            _tsDefName = Just defName
        }
    -- Generate start timestamp and timestamp the body
    ((bodyEndT, body'), finalState) <- runFreshMT $ runStateT (do
            timestampExpr body
        ) initialState
    -- Generate end timestamp
    (_, finalState2) <- runFreshMT $ runStateT (do
            let tsEnd = endTs defName
            addTimestampConstraint bodyEndT tsEnd
        ) finalState
    constraints' <- readIORef (_tsConstraints finalState2)
    return (body', constraints')

