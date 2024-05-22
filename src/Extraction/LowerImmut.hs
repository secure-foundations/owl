{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
module LowerImmut where
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.List
import Data.Char
import Data.Maybe
import Control.Monad
import Control.Monad.Except
import Control.Lens
import Prettyprinter
import Pretty
import Data.Type.Equality
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Bind
import Unbound.Generics.LocallyNameless.Name
import Unbound.Generics.LocallyNameless.Unsafe
import Unbound.Generics.LocallyNameless.TH
import GHC.Generics (Generic)
import Data.Typeable (Typeable)
import ConcreteAST
import ExtractionBase
import Verus

type EM = ExtractionMonad FormatTy

lowerTy :: FormatTy -> EM VerusTy
lowerTy FUnit = return RTUnit
lowerTy FBool = return RTBool
lowerTy FInt = return RTUsize
lowerTy (FBuf Nothing) = return $ RTOwlBuf (Lifetime "_")
lowerTy (FBuf (Just flen)) = return $ RTOwlBuf (Lifetime "_")
lowerTy (FOption ft) = RTOption <$> lowerTy ft
lowerTy (FStruct fn ffs) = do
    let rn = execName fn
    rfs <- mapM (\(n, t) -> (,) (execName n) <$> lowerTy t) ffs
    return $ RTStruct rn rfs
lowerTy (FEnum n fcs) = do
    let rn = execName n
    rcs <- mapM (\(n, t) -> (,) (execName n) <$> mapM lowerTy t) fcs
    return $ RTEnum rn rcs
lowerTy FGhost = return $ RTVerusGhost
lowerTy FDummy = return $ RTDummy

-- lowerTyNoOwlBuf :: FormatTy -> EM VerusTy
-- lowerTyNoOwlBuf FUnit = return RTUnit
-- lowerTyNoOwlBuf FBool = return RTBool
-- lowerTyNoOwlBuf FInt = return RTUsize
-- lowerTyNoOwlBuf (FBuf Nothing) = return $ RTVec RTU8
-- lowerTyNoOwlBuf (FBuf (Just flen)) = return $ RTVec RTU8
-- lowerTyNoOwlBuf (FOption ft) = RTOption <$> lowerTyNoOwlBuf ft
-- lowerTyNoOwlBuf (FStruct fn ffs) = do
--     let rn = execName fn
--     rfs <- mapM (\(n, t) -> (,) (execName n) <$> lowerTyNoOwlBuf t) ffs
--     return $ RTStruct rn rfs
-- lowerTyNoOwlBuf (FEnum n fcs) = do
--     let rn = execName n
--     rcs <- mapM (\(n, t) -> (,) (execName n) <$> mapM lowerTyNoOwlBuf t) fcs
--     return $ RTEnum rn rcs
-- lowerTyNoOwlBuf FGhost = return $ RTVerusGhost




lowerExpr :: CExpr FormatTy -> EM (CExpr VerusTy)
lowerExpr e = traverseCExpr lowerTy e

lowerArg :: (CDataVar FormatTy, String, FormatTy) -> EM (CDataVar VerusTy, String, VerusTy)
lowerArg (n, s, t) = do
    t' <- lowerTy t
    return (castName n, s, t')

lowerDef :: CDef FormatTy -> EM (CDef VerusTy)
lowerDef (CDef name b) = do
    (args, (retTy, body)) <- unbindCDepBind b
    args' <- mapM lowerArg args
    retTy' <- lowerTy retTy
    body' <- traverse lowerExpr body
    b' <- bindCDepBind args' (retTy', body')
    return $ CDef name b'

lowerUserFunc :: CUserFunc FormatTy -> EM (CUserFunc VerusTy)
lowerUserFunc (CUserFunc name b) = do
    (args, (retTy, body)) <- unbindCDepBind b
    args' <- mapM lowerArg args
    retTy' <- lowerTy retTy
    body' <- traverseCAExpr lowerTy body
    b' <- bindCDepBind args' (retTy', body')
    return $ CUserFunc name b'


lowerFieldTy :: FormatTy -> EM VerusTy
lowerFieldTy = lowerTy -- for now, probably need to change it later


maybeLenOf :: FormatTy -> EM (Maybe ConstUsize)
maybeLenOf (FBuf (Just flen)) = return $ Just $ lowerFLen flen
maybeLenOf _ = return Nothing

lowerTyDef :: String -> CTyDef FormatTy -> EM (Maybe (CTyDef (Maybe ConstUsize, VerusTy)))
lowerTyDef _ (CStructDef (CStruct name fields isVest)) = do
    let lowerField (n, t) = do
            t' <- lowerFieldTy t
            l <- maybeLenOf t
            return (n, (l, t'))
    fields' <- mapM lowerField fields
    return $ Just $ CStructDef $ CStruct name fields' isVest
lowerTyDef _ (CEnumDef (CEnum name cases isVest)) = do
    let lowerCase (n, t) = do
            tt' <- case t of
                Just t -> do
                    t' <- lowerFieldTy t
                    l <- maybeLenOf t
                    return $ Just (l, t')
                Nothing -> return Nothing
            return (n, tt')
    cases' <- mapM lowerCase $ M.assocs cases
    return $ Just $ CEnumDef $ CEnum name (M.fromList cases') isVest

lowerName :: (String, FLen, Int) -> EM (String, ConstUsize, Int)
lowerName (n, l, i) = do
    let l' = lowerFLen l
    return (n, l', i)



--------------------------------------------------------------------------------
-- Helper functions

vecU8 :: VerusTy
vecU8 = RTVec RTU8

arrayU8 :: ConstUsize -> VerusTy
arrayU8 n = RTArray RTU8 n
