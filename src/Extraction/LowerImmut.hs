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


lowerLenConst :: String -> EM String
lowerLenConst s = return $ map toUpper s ++ "_SIZE"

lowerFLen :: FLen -> EM ConstUsize
lowerFLen (FLConst n) = return $ CUsizeLit n
lowerFLen (FLNamed n) = do
    n' <- lowerLenConst n
    return $ CUsizeConst n'
lowerFLen (FLPlus a b) = CUsizePlus <$> lowerFLen a <*> lowerFLen b


lowerArgTy :: FormatTy -> EM VerusTy
lowerArgTy FUnit = return RTUnit
lowerArgTy FBool = return RTBool
lowerArgTy FInt = return RTUsize
lowerArgTy (FBuf Nothing) = return $ RTOwlBuf (Lifetime "_")
lowerArgTy (FBuf (Just flen)) = return $ RTOwlBuf (Lifetime "_")
lowerArgTy (FOption ft) = RTOption <$> lowerArgTy ft
lowerArgTy (FStruct n _) = return $ RTNamed n
lowerArgTy (FEnum n _) = return $ RTNamed n
lowerArgTy FGhost = return $ RTVerusGhost


lowerExpr :: CExpr FormatTy -> EM (CExpr VerusTy)
lowerExpr e = traverseCExpr lowerArgTy e

lowerArg :: (CDataVar FormatTy, String, FormatTy) -> EM (CDataVar VerusTy, String, VerusTy)
lowerArg (n, s, t) = do
    t' <- lowerArgTy t
    return (castName n, s, t')

lowerDef :: CDef FormatTy -> EM (CDef VerusTy)
lowerDef (CDef name b) = do
    (args, (retTy, body)) <- unbindCDepBind b
    args' <- mapM lowerArg args
    retTy' <- lowerArgTy retTy
    body' <- lowerExpr body
    b' <- bindCDepBind args' (retTy', body')
    return $ CDef name b'


lowerFieldTy :: FormatTy -> EM VerusTy
lowerFieldTy = lowerArgTy -- for now, probably need to change it later


maybeLenOf :: FormatTy -> EM (Maybe ConstUsize)
maybeLenOf (FBuf (Just flen)) = Just <$> lowerFLen flen
maybeLenOf _ = return Nothing

lowerTyDef :: String -> CTyDef FormatTy -> EM (Maybe (CTyDef (Maybe ConstUsize, VerusTy)))
lowerTyDef _ (CStructDef (CStruct name fields)) = do
    let lowerField (n, t) = do
            t' <- lowerFieldTy t
            l <- maybeLenOf t
            return (n, (l, t'))
    fields' <- mapM lowerField fields
    return $ Just $ CStructDef $ CStruct name fields'
lowerTyDef _ (CEnumDef (CEnum name cases)) = do
    let lowerCase (n, t) = do
            tt' <- case t of
                Just t -> do
                    t' <- lowerFieldTy t
                    l <- maybeLenOf t
                    return $ Just (l, t')
                Nothing -> return Nothing
            return (n, tt')
    cases' <- mapM lowerCase $ M.assocs cases
    return $ Just $ CEnumDef $ CEnum name $ M.fromList cases'

lowerName :: (String, FLen, Int) -> EM (String, ConstUsize, Int)
lowerName (n, l, i) = do
    l' <- lowerFLen l
    return (n, l', i)



--------------------------------------------------------------------------------
-- Helper functions

vecU8 :: VerusTy
vecU8 = RTVec RTU8

arrayU8 :: ConstUsize -> VerusTy
arrayU8 n = RTArray RTU8 n
