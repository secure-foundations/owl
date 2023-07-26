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

extractAExpr :: AExpr -> ExtractionMonad (Doc ann)
extractAExpr ae = extractAExpr' (ae ^. val) where
    extractAExpr' (AEVar s n) = return $ replacePrimes' . pretty $ n
    extractAExpr' (AEApp f _ as) = do 
        f' <- flattenPath f
        as' <- mapM extractAExpr as
        return $ pretty f' <> tupled as'
    extractAExpr' (AEString s) = return $ pretty "\"" <> pretty s <> pretty "\""
    extractAExpr' (AELenConst s) = return $ pretty s <> pretty "_len"
    extractAExpr' (AEInt i) = return $ pretty i
    extractAExpr' (AEGet ne) = return $ parens (pretty "*loc." <> rustifyName' (pretty ne)) <> pretty ".view()"
    extractAExpr' (AEGetEncPK ne) = return $ pretty "get_encpk" <> pretty "(" <> pretty ne <> pretty ")"
    extractAExpr' (AEGetVK ne) = return $ pretty "get_vk" <> pretty "(" <> pretty ne <> pretty ")"
    extractAExpr' (AEPackIdx s a) = extractAExpr a

extractCryptOp :: CryptOp -> [AExpr] -> ExtractionMonad (Doc ann)
extractCryptOp op owlArgs = do
    args <- mapM extractAExpr owlArgs
    case (op, args) of
        (CHash p _ n, [x]) -> do 
            roname <- flattenPath p 
            orcls <- use oracles
            case orcls M.!? roname of
                Nothing -> throwError $ TypeError "unrecognized random oracle"
                Just outLen -> do
                    return $ x <> pretty ".owl_extract_expand_to_len(&self.salt, " <> pretty outLen <> pretty ")"
        (CPRF s, _) -> do throwError $ ErrSomethingFailed $ "TODO implement crypto op: " ++ show op
        (CAEnc, [k, x]) -> do return $ pretty "enc" <> parens (tupled [k, x])
        (CADec, [k, x]) -> do return $ pretty "dec" <> parens (tupled [k, x])
        (CAEncWithNonce p (sids, pids), _) -> do throwError $ ErrSomethingFailed $ "TODO implement crypto op: " ++ show op
        (CADecWithNonce, _) -> do throwError $ ErrSomethingFailed $ "TODO implement crypto op: " ++ show op
        (CPKEnc, [k, x]) -> do return $ x <> pretty ".owl_pkenc(&" <> k <> pretty ")"
        (CPKDec, [k, x]) -> do return $ x <> pretty ".owl_pkdec(&" <> k <> pretty ")"
        (CMac, [k, x]) -> do return $ x <> pretty ".owl_mac(&" <> k <> pretty ")"
        (CMacVrfy, [k, x, v]) -> do return $ x <> pretty ".owl_mac_vrfy(&" <> k <> pretty ", &" <> v <> pretty ")"
        (CSign, [k, x]) -> do return $ x <> pretty ".owl_sign(&" <> k <> pretty ")"
        (CSigVrfy, [k, x, v]) -> do return $ x <> pretty ".owl_vrfy(&" <> k <> pretty ", &" <> v <> pretty ")"
        (_, _) -> do throwError $ TypeError $ "got bad args for crypto op: " ++ show op ++ "(" ++ show args ++ ")"


extractExpr :: CExpr -> ExtractionMonad (Doc ann)
extractExpr CSkip = return $ pretty "skip"
extractExpr (CInput xsk) = do
    let (x, sk) = unsafeUnbind xsk
    sk' <- extractExpr sk
    return $ parens (pretty "input" <+> replacePrimes' (pretty x)) <+> pretty "in" <> line <> sk'
extractExpr (COutput a l) = do
    a' <- extractAExpr a
    return $ parens $ pretty "output " <> parens a' <+> 
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
    a' <- extractAExpr a
    e1' <- extractExpr e1
    e2' <- extractExpr e2
    return $ parens $
        pretty "if" <+> parens a' <+> pretty "then" <+> parens (pretty e1) <+> pretty "else" <+> parens (pretty e2)
extractExpr (CRet a) = do 
    a' <- extractAExpr a
    return $ parens $ pretty "ret" <+> parens a'
extractExpr (CCall f is as) = do
    as' <- mapM extractAExpr as
    let inds = case is of
                ([], []) -> mempty
                (v1, v2) -> pretty "<" <> mconcat (map pretty v1) <> pretty "@" <> mconcat (map pretty v2) <> pretty ">"
    return $ parens (pretty "call" <> parens (pretty f <> pretty "_spec" <> inds <> tupled (pretty "loc" : as')))
extractExpr (CCase a xs) = do
    a' <- extractAExpr a
    pcases <-
            mapM (\(c, o) ->
                case o of
                Left e -> do 
                    e' <- extractExpr e
                    return $ pretty c <+> pretty "=>" <+> braces e' <> comma
                Right xe -> do
                    let (x, e) = unsafeUnbind xe
                    e' <- extractExpr e
                    return $ pretty c <+> parens (replacePrimes' (pretty x)) <+> pretty "=>" <+> braces e' <> comma
                ) xs 
    return $ parens $ pretty "case" <+> parens a' <> line <> braces (vsep pcases)
extractExpr (CCrypt cop args) = do
    c <- extractCryptOp cop args
    -- ITree expects everything to be inside of a `ret`
    return $ parens $ pretty "ret" <+> parens c
extractExpr c = throwError . ErrSomethingFailed . show $ pretty "unimplemented case for extractExpr:" <+> pretty c
-- extractExpr (CTLookup n a) = return $ pretty "lookup" <> tupled [pretty n, extractAExpr a]
-- extractExpr (CTWrite n a a') = return $ pretty "write" <> tupled [pretty n, extractAExpr a, extractAExpr a']
