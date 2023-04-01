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

elet :: Expr -> (DataVar -> Expr) -> Check Expr
elet e k = do
    x <- freshVar
    let k' = k $ s2n x
    return $ Spanned (e^.spanOf) $ ELet e Nothing x (bind (s2n x) k')

aevar :: Ignore Position -> DataVar -> AExpr
aevar sp x = Spanned sp $ AEVar (ignore $ show x) x

anfAExpr :: AExpr -> Check Expr
anfAExpr a =
    case a^.val of
      AEVar _ _ -> return $ Spanned (a^.spanOf) $ ERet a
      AEString _ -> return $ Spanned (a^.spanOf) $ ERet a
      AEGet _ -> return $ Spanned (a^.spanOf) $ ERet a
      AEGetEncPK _ -> return $ Spanned (a^.spanOf) $ ERet a
      AEGetVK _ -> return $ Spanned (a^.spanOf) $ ERet a
      AELenConst _ -> return $ Spanned (a^.spanOf) $ ERet a
      AEInt _ -> return $ Spanned (a^.spanOf) $ ERet a
      AEPackIdx i a' -> do
          e1 <- anfAExpr a'
          x <- freshVar
          return $ Spanned (a^.spanOf) $ ELet e1 Nothing x (bind (s2n x) $ Spanned (a^.spanOf) $ ERet $ Spanned (a^.spanOf) $ AEPackIdx i (Spanned (a^.spanOf) $ AEVar (ignore x) (s2n x)))
      AEApp f ps args -> anfAExprList (a^.spanOf) args $ \xs -> Spanned (a^.spanOf) $ ERet $ Spanned (a^.spanOf) $ AEApp f ps xs

anfAExprList :: Ignore Position -> [AExpr] -> ([AExpr] -> Expr) -> Check Expr
anfAExprList sp args k = go args []
    where
        go :: [AExpr] -> [AExpr] -> Check Expr
        go [] acc = return $ k acc
        go (arg:args) acc = do
            e1 <- anfAExpr arg
            x <- s2n <$> freshVar
            ek <- go args (acc ++ [aevar sp x])
            return $ Spanned sp $ ELet e1 Nothing (show x) (bind x ek)


anfBind :: Alpha a => Bind a Expr -> Check (Bind a Expr)
anfBind xk = do
    (p, k) <- unbind xk
    k' <- anf k
    return $ bind p k'

anf :: Expr -> Check Expr
anf e = 
    case e^.val of 
      EInput xek -> do
          xek' <- anfBind xek
          return $ Spanned (e^.spanOf) $ EInput xek'
      EOutput a oe -> do
          e1 <- anfAExpr a
          elet e1 $ \x -> Spanned (e^.spanOf) $ EOutput (aevar (a^.spanOf) x) oe
      ELet e tyann s xk -> do
          xk' <- anfBind xk
          e' <- anf e
          return $ Spanned (e^.spanOf) $ ELet e' tyann s xk'
      EUnionCase a xk -> do
          xk' <- anfBind xk
          ea <- anfAExpr a
          elet ea $ \y -> Spanned (e^.spanOf) $ EUnionCase (aevar (a^.spanOf) y) xk'
      EUnpack a ixe -> do
          ixe' <- anfBind ixe
          ea <- anfAExpr a
          elet ea $ \y -> Spanned (e^.spanOf) $ EUnpack (aevar (a^.spanOf) y) ixe'
      ESamp ds args -> anfAExprList (e^.spanOf) args $ \xs -> Spanned (e^.spanOf) $ ESamp ds xs
      EIf a e1 e2 -> do
          e1' <- anf e1
          e2' <- anf e2
          ea <- anfAExpr a
          elet ea $ \y -> Spanned (e^.spanOf) $ EIf (aevar (a^.spanOf) y) e1' e2'
      ERet a -> do
          ea <- anfAExpr a
          elet ea $ \y -> Spanned (e^.spanOf) $ ERet (aevar (a^.spanOf) y) 
      EDebug dc -> 
          case dc of
            DebugPrintExpr e -> do
                e' <- anf e
                return $ Spanned (e^.spanOf) $ EDebug $ DebugPrintExpr e'
            _ -> return e
      EAssert _ -> return e
      EAssume _ -> return e
      EAdmit -> return e
      ECall s is as -> 
          anfAExprList (e^.spanOf) as $ \xs -> Spanned (e^.spanOf) $ ECall s is xs
      ECase a cases -> do
          ea <- anfAExpr a
          cases' <- forM cases $ \(s, o) ->
              case o of
                Left e1 -> do
                    e1' <- anf e1
                    return $ (s, Left e1')
                Right (c, be) -> do
                    be' <- anfBind be
                    return $ (s, Right (c, be'))
          elet ea $ \y -> Spanned (e^.spanOf) $ ECase (aevar (a^.spanOf) y) cases'
      ECorrCase ne k -> do 
         k' <- anf k
         return $ Spanned (e^.spanOf) $ ECorrCase ne k'
      EFalseElim k -> do 
         k' <- anf k
         return $ Spanned (e^.spanOf) $ EFalseElim k'
      ETLookup t a -> do
         ea <- anfAExpr a
         elet ea $ \y -> Spanned (e^.spanOf) $ ETLookup t $ aevar (a^.spanOf) y
      ETWrite t a1 a2 -> do
         ea1 <- anfAExpr a1
         ea2 <- anfAExpr a2
         x <- s2n <$> freshVar
         y <- s2n <$> freshVar
         return $ Spanned (e^.spanOf) $ ELet ea1 Nothing (show x) $ bind x $ Spanned (e^.spanOf) $ ELet ea2 Nothing (show y) $ bind y $ Spanned (e^.spanOf) $ ETWrite t (aevar (a1^.spanOf) x) (aevar (a2^.spanOf) y)






    
