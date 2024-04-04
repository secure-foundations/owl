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


lowerFLen :: FLen -> EM ConstUsize
lowerFLen (FLConst n) = return $ CUsizeLit n
lowerFLen (FLNamed n) = return $ CUsizeConst n -- TODO: make sure n is in the list of known len consts


lowerArgTy :: FormatTy -> EM VerusTy
lowerArgTy FUnit = return RTUnit
lowerArgTy FBool = return RTBool
lowerArgTy FInt = return RTUsize
lowerArgTy (FBuf Nothing) = return vecU8
lowerArgTy (FBuf (Just flen)) = arrayU8 <$> lowerFLen flen -- in return types, don't care abou
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


--------------------------------------------------------------------------------
-- Helper functions

vecU8 :: VerusTy
vecU8 = RTVec RTU8

arrayU8 :: ConstUsize -> VerusTy
arrayU8 n = RTArray RTU8 n
