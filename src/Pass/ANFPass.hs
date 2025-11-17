{-# LANGUAGE TemplateHaskell #-} 
{-# LANGUAGE GeneralizedNewtypeDeriving #-} 
{-# LANGUAGE FlexibleInstances #-} 
{-# LANGUAGE MultiParamTypeClasses #-} 
{-# LANGUAGE UndecidableInstances #-} 
{-# LANGUAGE FlexibleContexts #-} 
{-# LANGUAGE DataKinds #-} 
{-# LANGUAGE DeriveGeneric #-}
module ANFPass where
import AST
import Error.Diagnose.Position (Position)
import Control.Lens
import Control.Monad
import TypingBase
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Bind
import Unbound.Generics.LocallyNameless.Unsafe
import Unbound.Generics.LocallyNameless.TH

elet :: Fresh m => Expr -> Maybe Ty -> Maybe AExpr -> Maybe String -> Timestamp -> (DataVar -> m Expr) -> m Expr
elet e tyann anf s ts k =       
    case e^.exprVal of
      ELet e1 tyann1 anf1 s1 xe1k -> do
          (x, e1k) <- unbind xe1k
          let ts1 = unignore $ e^.val.timestampOf
          elet e1 tyann1 anf1 (Just s1) ts1 $ \y -> 
              let anf' = subst x (mkSpanned $ AEVar (ignore s1) y) anf in 
              elet (subst x (mkSpanned $ AEVar (ignore s1) y) e1k) tyann anf' s ts k
      _ -> do
          x <- fresh $ s2n ".x"
          k' <- k x
          let (s', anf') = case s of
                     Just st -> (st, anf)
                     Nothing -> (show x, anf)
          return $ Spanned (e^.spanOf) $ Timestamped (ignore ts) $ ELet e tyann anf' s' (bind x $ k')

aevar :: Ignore Position -> DataVar -> AExpr
aevar sp x = Spanned sp $ AEVar (ignore $ show x) x

anfAExpr :: Fresh m => AExpr -> Timestamp -> m Expr
anfAExpr a ts =
    case a^.val of
      AEVar _ _ -> return $ Spanned (a^.spanOf) $ Timestamped (ignore ts) $ ERet a
      AEHex _ -> return $ Spanned (a^.spanOf) $ Timestamped (ignore ts) $ ERet a
      AEGet _ -> return $ Spanned (a^.spanOf) $ Timestamped (ignore ts) $ ERet a
      -- AEPreimage _ _ _ -> return $ Spanned (a^.spanOf) $ ERet a ts
      AEGetEncPK _ -> return $ Spanned (a^.spanOf) $ Timestamped (ignore ts) $ ERet a
      AEGetVK _ -> return $ Spanned (a^.spanOf) $ Timestamped (ignore ts) $ ERet a
      AELenConst _ -> return $ Spanned (a^.spanOf) $ Timestamped (ignore ts) $ ERet a
      AEInt _ -> return $ Spanned (a^.spanOf) $ Timestamped (ignore ts) $ ERet a
      AEKDF _ _ _ _ _ -> return $ Spanned (a^.spanOf) $ Timestamped (ignore ts) $ ERet a
      AEApp f ps args -> anfAExprList (a^.spanOf) args ts $ \xs -> 
        Spanned (a^.spanOf) $ Timestamped (ignore ts) $ ERet (Spanned (a^.spanOf) $ AEApp f ps xs)

anfAExprList :: Fresh m => Ignore Position -> [AExpr] -> Timestamp -> ([AExpr] -> Expr) -> m Expr
anfAExprList sp args ts k = go args []
    where
        go :: Fresh m => [AExpr] -> [AExpr] -> m Expr
        go [] acc = return $ k acc
        go (arg:args) acc = do
            e1 <- anfAExpr arg ts
            x <- fresh $ s2n ".x"
            ek <- go args (acc ++ [aevar (arg^.spanOf) x])
            return $ Spanned sp $ Timestamped (ignore ts) $ ELet e1 Nothing (Just arg) (show x) (bind x ek)


anfBind :: (Fresh m, Alpha a) => Bind a Expr -> m (Bind a Expr)
anfBind xk = do
    (p, k) <- unbind xk
    k' <- anf k
    return $ bind p k'

anf :: Fresh m => Expr -> m Expr
anf e = 
    let ts = unignore $ e^.val.timestampOf in
    case e^.exprVal of 
      EGetCtr p ps -> return $ Spanned (e^.spanOf) $ Timestamped (ignore ts) $ EGetCtr p ps
      EIncCtr p ps -> return $ Spanned (e^.spanOf) $ Timestamped (ignore ts) $ EIncCtr p ps
      EInput s xek -> do
          xek' <- anfBind xek
          return $ Spanned (e^.spanOf) $ Timestamped (ignore ts) $ EInput s xek'
      EOutput a oe -> do
          e1 <- anfAExpr a ts
          elet e1 Nothing (Just a) Nothing ts $ \x -> return $ Spanned (e^.spanOf) $ Timestamped (ignore ts) $ EOutput (aevar (a^.spanOf) x) oe
      -- If a bare let statement without a type annotation, treat it as an
      -- ANF-inserted one
      ELet e1' tyann' Nothing s' xk -> do
          let e1_spanned = Spanned (e1'^.spanOf) $ e1'^.val
          case e1'^.exprVal of
            -- ERet a -> do
            --     (x, k) <- unbind xk
            --     let ts1 = unignore $ e1'^.val.timestampOf
            --     a' <- anfAExpr a ts1
            --     elet a' Nothing (Just a) (Just s') ts1 $ \y -> 
            --         anf $ subst x (aevar (a^.spanOf) y) k
            _ -> do
                (x, k) <- unbind xk
                e' <- anf e1'
                elet e' tyann' Nothing (Just s') ts $ \y -> 
                    anf $ subst x (mkSpanned $ AEVar (ignore s') y) k
      ELet _ _ (Just _) _ _ -> error "Got anfVar in anf routine"
      ELetGhost a s xk -> do
          (x, k) <- unbind xk
          k' <- anf k
          return $ Spanned (e^.spanOf) $ Timestamped (ignore ts) $ ELetGhost a s (bind x k')
      EBlock k b -> do
          k' <- anf k
          return $ Spanned (e^.spanOf) $ Timestamped (ignore ts) $ EBlock k' b
      EUnpack a s ixe -> do
          ixe' <- anfBind ixe
          ea <- anfAExpr a ts
          elet ea Nothing (Just a) Nothing ts $ \y -> return $ Spanned (e^.spanOf) $ Timestamped (ignore ts) $ EUnpack (aevar (a^.spanOf) y) s ixe'
      EChooseIdx s p ixe -> do
          ixe' <- anfBind ixe
          return $ Spanned (e^.spanOf) $ Timestamped (ignore ts) $ EChooseIdx s p ixe'
      EChooseBV s p ixe -> do
          ixe' <- anfBind ixe
          return $ Spanned (e^.spanOf) $ Timestamped (ignore ts) $ EChooseBV s p ixe'
      EPackIdx i e1 -> do
          e1' <- anf e1
          let ts1 = unignore $ e1'^.val.timestampOf
          case e1'^.exprVal of
            -- ERet a' -> elet e1' Nothing Nothing Nothing ts $ \x -> return $ Spanned (e^.spanOf) $ Timestamped (ignore ts) $ EPackIdx i (Spanned (e1^.spanOf) $ Timestamped (ignore ts1) $ ERet (aevar (e1^.spanOf) x))
            _ ->       elet e1' Nothing Nothing Nothing ts $ \x -> return $ Spanned (e^.spanOf) $ Timestamped (ignore ts) $ EPackIdx i (Spanned (e1^.spanOf) $ Timestamped (ignore ts) $ ERet (aevar (e1^.spanOf) x))
      EIf a e1 e2 -> do
          e1' <- anf e1
          e2' <- anf e2
          ea <- anfAExpr a ts
          elet ea Nothing ( Just a) Nothing ts $ \y -> return $ Spanned (e^.spanOf) $ Timestamped (ignore ts) $ EIf (aevar (a^.spanOf) y) e1' e2'
      EForallBV s xpk -> do
          (x, (op, k)) <- unbind xpk
          k' <- anf k
          return $ Spanned (e^.spanOf) $ Timestamped (ignore ts) $ EForallBV s (bind x (op, k'))
      EForallIdx s xpk -> do
          (x, (op, k)) <- unbind xpk
          k' <- anf k
          return $ Spanned (e^.spanOf) $ Timestamped (ignore ts) $ EForallIdx s (bind x (op, k'))
      EGuard a e -> do
          e' <- anf e
          ea <- anfAExpr a ts
          elet ea Nothing ( Just a) Nothing ts $ \y -> return $ Spanned (e^.spanOf) $ Timestamped (ignore ts) $ EGuard (aevar (a^.spanOf) y) e'
      ERet a -> do
          ea <- anfAExpr a ts
          elet ea Nothing ( Just a) Nothing ts $ \y -> return $ Spanned (e^.spanOf) $ Timestamped (ignore ts) $ ERet (aevar (a^.spanOf) y)
      EDebug dc -> 
          case dc of
            DebugResolveANF a -> do
                ea <- anfAExpr a ts
                elet ea Nothing (Just a) Nothing ts $ \y -> return $ Spanned (e^.spanOf) $ Timestamped (ignore ts) $ EDebug (DebugResolveANF (aevar (e^.spanOf) y))
            DebugPrintExpr e' -> do
                e'' <- anf e'
                return $ Spanned (e^.spanOf) $ Timestamped (ignore ts) $ EDebug (DebugPrintExpr e'')
            _ -> return $ Spanned (e^.spanOf) $ Timestamped (ignore ts) $ EDebug dc
      EAssert p -> return $ Spanned (e^.spanOf) $ Timestamped (ignore ts) $ EAssert p
      EAssume p -> return $ Spanned (e^.spanOf) $ Timestamped (ignore ts) $ EAssume p
      EAdmit -> return $ Spanned (e^.spanOf) $ Timestamped (ignore ts) $ EAdmit
      ECrypt p as ->
          if isGhostOp p then return $ Spanned (e^.spanOf) $ Timestamped (ignore ts) $ ECrypt p as
                         else anfAExprList (e^.spanOf) as ts $ \xs -> Spanned (e^.spanOf) $ Timestamped (ignore ts) $ ECrypt p xs
      ECall s is as -> 
          anfAExprList (e^.spanOf) as ts $ \xs -> Spanned (e^.spanOf) $ Timestamped (ignore ts) $ ECall s is xs
      EParse a t ok bk -> do
          a' <- anfAExpr a ts
          ok' <- traverse anf ok 
          bk' <- anfBind bk
          elet a' Nothing (Just a) Nothing ts $ \x -> return $ Spanned (e^.spanOf) $ Timestamped (ignore ts) $ EParse (aevar (a^.spanOf) x) t ok' bk'
      ECase e1 otk cases -> do
          e1' <- anf e1
          -- Extract timestamp from e1' if it's an ERet, otherwise use ts
          let ts1 = case e1'^.exprVal of
                      ERet _ -> unignore $ e1'^.val.timestampOf
                      _ -> ts
          cases' <- forM cases $ \(s, o) ->
              case o of
                Left e1 -> do
                    e1' <- anf e1
                    return $ (s, Left e1')
                Right (c, be) -> do
                    be' <- anfBind be
                    return $ (s, Right (c, be'))
          otk' <- case otk of
                    Nothing -> return Nothing
                    Just (t, k) -> do
                        k' <- anf k
                        return $ Just (t, k')
          elet e1' Nothing (Nothing) Nothing ts1 $ \y -> return $ Spanned (e^.spanOf) $ Timestamped (ignore ts) $ ECase (Spanned (e1^.spanOf) $ Timestamped (ignore ts1) $ ERet (aevar (e1^.spanOf) y)) otk' cases'
      EPCase p op ob k -> do 
         k' <- anf k
         return $ Spanned (e^.spanOf) $ Timestamped (ignore ts) $ EPCase p op ob k'
      ECorrCaseNameOf a op k -> do 
         k' <- anf k
         return $ Spanned (e^.spanOf) $ Timestamped (ignore ts) $ ECorrCaseNameOf a op k'
      EOpenTyOf a k -> do 
         k' <- anf k
         return $ Spanned (e^.spanOf) $ Timestamped (ignore ts) $ EOpenTyOf a k'
      ESetOption s1 s2 k -> do
          k' <- anf k
          return $ Spanned (e^.spanOf) $ Timestamped (ignore ts) $ ESetOption s1 s2 k'
      EFalseElim k op -> do 
         k' <- anf k
         return $ Spanned (e^.spanOf) $ Timestamped (ignore ts) $ EFalseElim k' op
      ETLookup t a -> do
         ea <- anfAExpr a ts
         elet ea Nothing (Just a) Nothing ts $ \y -> return $ Spanned (e^.spanOf) $ Timestamped (ignore ts) $ ETLookup t (aevar (a^.spanOf) y)
      ETWrite t a1 a2 -> do
         ea1 <- anfAExpr a1 ts
         ea2 <- anfAExpr a2 ts
         elet ea1 Nothing (Just a1) Nothing ts $ \x -> 
             elet ea2 Nothing (Just a1) Nothing ts $ \y -> 
                 return $ Spanned (e^.spanOf) $ Timestamped (ignore ts) $ ETWrite t (aevar (a1^.spanOf) x) (aevar (a2^.spanOf) y)

isGhostOp :: CryptOp -> Bool
isGhostOp (CLemma _) = True
isGhostOp _ = False

isGhostTyAnn :: Maybe Ty -> Bool
isGhostTyAnn Nothing = False
isGhostTyAnn (Just t) =
    case t^.val of
      TGhost -> True
      TRefined (Spanned _ TGhost) _ _ -> True
      _ -> False

