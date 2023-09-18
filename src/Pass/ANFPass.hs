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

elet :: Fresh m => Expr -> Maybe Ty -> Maybe AExpr -> Maybe String -> (DataVar -> m Expr) -> m Expr
elet e tyann anf s k =       
    case e^.val of
      ELet e1 tyann1 anf1 s1 xe1k -> do
          (x, e1k) <- unbind xe1k
          elet e1 tyann1 anf1 (Just s1) $ \y -> 
              let anf' = subst x (mkSpanned $ AEVar (ignore s1) y) anf in 
              elet (subst x (mkSpanned $ AEVar (ignore s1) y) e1k) tyann anf' s k
      _ -> do
          x <- fresh $ s2n ".x"
          k' <- k x
          let (s', anf') = case s of
                     Just st -> (st, anf)
                     Nothing -> (show x, anf)
          return $ Spanned (e^.spanOf) $ ELet e tyann anf' s' (bind x $ k')

aevar :: Ignore Position -> DataVar -> AExpr
aevar sp x = Spanned sp $ AEVar (ignore $ show x) x

anfAExpr :: Fresh m => AExpr -> m Expr
anfAExpr a =
    case a^.val of
      AEVar _ _ -> return $ Spanned (a^.spanOf) $ ERet a
      AEHex _ -> return $ Spanned (a^.spanOf) $ ERet a
      AEGet _ -> return $ Spanned (a^.spanOf) $ ERet a
      AEPreimage _ _ _ -> return $ Spanned (a^.spanOf) $ ERet a
      AEGetEncPK _ -> return $ Spanned (a^.spanOf) $ ERet a
      AEGetVK _ -> return $ Spanned (a^.spanOf) $ ERet a
      AELenConst _ -> return $ Spanned (a^.spanOf) $ ERet a
      AEInt _ -> return $ Spanned (a^.spanOf) $ ERet a
      AEPackIdx i a' -> do
          e1 <- anfAExpr a'
          x <- fresh $ s2n ".x"
          return $ 
            Spanned (a^.spanOf) $ ELet e1 Nothing (Just a) (show x) (bind x $ 
            Spanned (a^.spanOf) $ ERet $ Spanned (a^.spanOf) $ 
                AEPackIdx i (Spanned (a^.spanOf) $ AEVar (ignore $ show x) x))
      AEApp f ps args -> anfAExprList (a^.spanOf) args $ \xs -> 
        Spanned (a^.spanOf) $ ERet $ Spanned (a^.spanOf) $ AEApp f ps xs

anfAExprList :: Fresh m => Ignore Position -> [AExpr] -> ([AExpr] -> Expr) -> m Expr
anfAExprList sp args k = go args []
    where
        go :: Fresh m => [AExpr] -> [AExpr] -> m Expr
        go [] acc = return $ k acc
        go (arg:args) acc = do
            e1 <- anfAExpr arg
            x <- fresh $ s2n ".x"
            ek <- go args (acc ++ [aevar sp x])
            return $ Spanned sp $ ELet e1 Nothing (Just arg) (show x) (bind x ek)


anfBind :: (Fresh m, Alpha a) => Bind a Expr -> m (Bind a Expr)
anfBind xk = do
    (p, k) <- unbind xk
    k' <- anf k
    return $ bind p k'

anf :: Fresh m => Expr -> m Expr
anf e = 
    case e^.val of 
      EGetCtr _ _ -> return e
      EIncCtr _ _ -> return e
      EInput s xek -> do
          xek' <- anfBind xek
          return $ Spanned (e^.spanOf) $ EInput s xek'
      EOutput a oe -> do
          e1 <- anfAExpr a
          elet e1 Nothing (Just a) Nothing $ \x -> return $ Spanned (e^.spanOf) $ EOutput (aevar (a^.spanOf) x) oe
      ELet e1 tyann Nothing s xk -> do
          (x, k) <- unbind xk
          e' <- anf e1
          elet e' tyann (Nothing) (Just s) $ \y -> 
              anf $ subst x (mkSpanned $ AEVar (ignore s) y) k
      ELet _ _ (Just _) _ _ -> error "Got anfVar in anf routine"
      EBlock k -> do
          k' <- anf k
          return $ Spanned (e^.spanOf) $ EBlock k'
      EUnionCase a s xk -> do
          xk' <- anfBind xk
          ea <- anfAExpr a
          elet ea Nothing (Just a) Nothing $ \y -> return $ Spanned (e^.spanOf) $ EUnionCase (aevar (a^.spanOf) y) s xk'
      EUnpack a ixe -> do
          ixe' <- anfBind ixe
          ea <- anfAExpr a
          elet ea Nothing (Just a) Nothing $ \y -> return $ Spanned (e^.spanOf) $ EUnpack (aevar (a^.spanOf) y) ixe'
      EChooseIdx p ixe -> do
          ixe' <- anfBind ixe
          return $ Spanned (e^.spanOf) $ EChooseIdx p ixe'
      EIf a e1 e2 -> do
          e1' <- anf e1
          e2' <- anf e2
          ea <- anfAExpr a
          elet ea Nothing ( Just a) Nothing $ \y -> return $ Spanned (e^.spanOf) $ EIf (aevar (a^.spanOf) y) e1' e2'
      EForallBV xpk -> do
          (x, k) <- unbind xpk
          k' <- anf k
          return $ Spanned (e^.spanOf) $ EForallBV $ bind x k'
      EForallIdx xpk -> do
          (x, k) <- unbind xpk
          k' <- anf k
          return $ Spanned (e^.spanOf) $ EForallIdx $ bind x k'
      EGuard a e -> do
          e' <- anf e
          ea <- anfAExpr a
          elet ea Nothing ( Just a) Nothing $ \y -> return $ Spanned (e^.spanOf) $ EGuard (aevar (a^.spanOf) y) e'
      ERet a -> do
          ea <- anfAExpr a
          elet ea Nothing ( Just a) Nothing $ \y -> return $ Spanned (e^.spanOf) $ ERet (aevar (a^.spanOf) y) 
      EDebug dc -> 
          case dc of
            DebugResolveANF a -> do
                ea <- anfAExpr a
                elet ea Nothing (Just a) Nothing $ \y -> return $ Spanned (e^.spanOf) $ EDebug $ DebugResolveANF (aevar (e^.spanOf) y)
            DebugPrintExpr e -> do
                e' <- anf e
                return $ Spanned (e^.spanOf) $ EDebug $ DebugPrintExpr e'
            _ -> return e
      EAssert _ -> return e
      EAssume _ -> return e
      EAdmit -> return e
      ECrypt p as ->
          if isGhostOp p then return e
                         else anfAExprList (e^.spanOf) as $ \xs -> Spanned (e^.spanOf) $ ECrypt p xs 
      ECall s is as -> 
          anfAExprList (e^.spanOf) as $ \xs -> Spanned (e^.spanOf) $ ECall s is xs
      ECase e1 cases -> do
          e1' <- anf e1
          cases' <- forM cases $ \(s, o) ->
              case o of
                Left e1 -> do
                    e1' <- anf e1
                    return $ (s, Left e1')
                Right (c, be) -> do
                    be' <- anfBind be
                    return $ (s, Right (c, be'))
          elet e1' Nothing (Nothing) Nothing $ \y -> return $ Spanned (e^.spanOf) $ ECase (Spanned (e1^.spanOf) $ ERet $ aevar (e1^.spanOf) y) cases'
      EPCase p op k -> do 
         k' <- anf k
         return $ Spanned (e^.spanOf) $ EPCase p op k'
      ESetOption s1 s2 k -> do
          k' <- anf k
          return $ Spanned (e^.spanOf) $ ESetOption s1 s2 k'
      EFalseElim k -> do 
         k' <- anf k
         return $ Spanned (e^.spanOf) $ EFalseElim k'
      ETLookup t a -> do
         ea <- anfAExpr a
         elet ea Nothing (Just a) Nothing $ \y -> return $ Spanned (e^.spanOf) $ ETLookup t $ aevar (a^.spanOf) y
      ETWrite t a1 a2 -> do
         ea1 <- anfAExpr a1
         ea2 <- anfAExpr a2
         elet ea1 Nothing (Just a1) Nothing $ \x -> 
             elet ea2 Nothing (Just a1) Nothing $ \y -> 
                 return $ Spanned (e^.spanOf) $ ETWrite t (aevar (a1^.spanOf) x) (aevar (a2^.spanOf) y)

isGhostOp :: CryptOp -> Bool
isGhostOp (CLemma _) = True
isGhostOp _ = False

