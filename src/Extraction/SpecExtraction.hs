{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
module SpecExtraction where
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.List
import Data.Maybe
import Control.Monad
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Control.Lens
import Prettyprinter
import Data.Type.Equality
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Bind
import Unbound.Generics.LocallyNameless.Name ( Name(Bn, Fn) )
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)
import Unbound.Generics.LocallyNameless.TH
import GHC.Generics (Generic)
import Data.Typeable (Typeable)
import AST
import ConcreteAST
import System.IO
import qualified Text.Parsec as P
import qualified Parse as OwlP
import qualified TypingBase as TB
import ExtractionBase 



----------------------------------------------------------------------------------
--- Spec extraction for Owl code

extractEndpoint :: Endpoint -> Doc ann
extractEndpoint (Endpoint evar) = pretty evar
extractEndpoint (EndpointLocality (Locality s _)) = pretty "Endpoint::Loc_" <> pretty s

extractAExpr :: AExpr -> Doc ann
extractAExpr ae = extractAExpr' (ae ^. val) where
    extractAExpr' (AEVar s n) = pretty . replacePrimes . unignore $ s
    extractAExpr' (AEApp f _ as) = pretty f <> tupled (map extractAExpr as)
    extractAExpr' (AEString s) = pretty "\"" <> pretty s <> pretty "\""
    extractAExpr' (AELenConst s) = pretty s <> pretty "_len"
    extractAExpr' (AEInt i) = pretty i
    extractAExpr' (AEGet ne) = parens (pretty "*loc." <> rustifyName' (pretty ne)) <> pretty ".view()"
    extractAExpr' (AEGetEncPK ne) = pretty "get_encpk" <> pretty "(" <> pretty ne <> pretty ")"
    extractAExpr' (AEGetVK ne) = pretty "get_vk" <> pretty "(" <> pretty ne <> pretty ")"
    extractAExpr' (AEPackIdx s a) = extractAExpr a

extractExpr :: CExpr -> ExtractionMonad (Doc ann)
extractExpr CSkip = return $ pretty "skip"
extractExpr (CInput xsk) = return $
    let (x, sk) = unsafeUnbind xsk in
    parens (pretty "input" <+> replacePrimes' (pretty x)) <+> pretty "in" <> line <> pretty sk
extractExpr (COutput a l) = return $
    parens $ pretty "output " <> parens (extractAExpr a) <+> 
    (case l of
        Nothing -> pretty ""
        Just s -> pretty "to" <+> parens (extractEndpoint s))
-- -- Special case for `let _ = samp _ in ...` which is special-cased in the ITree syntax
-- extractExpr (CLet (CSamp d xs) xk) =
--     let (x, k) = prettyBind xk in
--     parens (pretty "sample" <> parens (coinsSize d <> comma <+> pretty d <> tupled (map extractAExpr xs) <> comma <+> replacePrimes' x)) <+>
--     pretty "in" <> line <> k
extractExpr (CLet (COutput a l) xk) = do
    let (_, k) = unsafeUnbind xk 
    k' <- extractExpr k
    return $ pretty (COutput a l) <+> pretty "in" <> line <> k'
extractExpr (CLet CSkip xk) = 
    let (_, k) = unsafeUnbind xk in extractExpr k
extractExpr (CLet e xk) = do
    let (x, k) = unsafeUnbind xk 
    e' <- extractExpr e
    k' <- extractExpr k
    return $ pretty "let" <+> replacePrimes' (pretty x) <+> pretty "=" <+> e' <+> pretty "in" <> line <> k'
-- extractExpr (CSamp d xs) = pretty "sample" <> parens (coinsSize d <> comma <+> pretty d <> tupled (map extractAExpr xs))
extractExpr (CIf a e1 e2) = do
    e1' <- extractExpr e1
    e2' <- extractExpr e2
    return $ parens $
        pretty "if" <+> parens (extractAExpr a) <+> pretty "then" <+> parens (pretty e1) <+> pretty "else" <+> parens (pretty e2)
extractExpr (CRet a) = return $ parens $ pretty "ret " <> parens (extractAExpr a)
extractExpr (CCall f is as) = return $
    let inds = case is of
                ([], []) -> mempty
                (v1, v2) -> pretty "<" <> mconcat (map pretty v1) <> pretty "@" <> mconcat (map pretty v2) <> pretty ">"
    in
    parens (pretty "call" <> parens (pretty f <> pretty "_spec" <> inds <> tupled (pretty "loc" : map extractAExpr as)))
extractExpr (CCase a xs) = do
    pcases <-
            mapM (\(c, o) ->
                case o of
                Left e -> do 
                    e' <- extractExpr e
                    return $ pretty c <+> pretty "=>" <+> braces e' <> comma
                Right xe -> do
                    let (x, e) = unsafeUnbind xe
                    e' <- extractExpr e
                    return $ pretty c <+> parens (replacePrimes' (pretty x)) <+> pretty "=>" <+> e' <> comma
                ) xs 
    return $ parens $ pretty "case" <+> parens (extractAExpr a) <> line <> braces (vsep pcases)
extractExpr c = throwError . ErrSomethingFailed . show $ pretty "unimplemented case for extractExpr:" <+> pretty c
-- extractExpr (CTLookup n a) = return $ pretty "lookup" <> tupled [pretty n, extractAExpr a]
-- extractExpr (CTWrite n a a') = return $ pretty "write" <> tupled [pretty n, extractAExpr a, extractAExpr a']
