{-# LANGUAGE TemplateHaskell #-} 
{-# LANGUAGE GeneralizedNewtypeDeriving #-} 
{-# LANGUAGE FlexibleInstances #-} 
{-# LANGUAGE MultiParamTypeClasses #-} 
{-# LANGUAGE UndecidableInstances #-} 
{-# LANGUAGE FlexibleContexts #-} 
{-# LANGUAGE DataKinds #-} 
{-# LANGUAGE RankNTypes #-} 
{-# LANGUAGE DeriveGeneric #-}
module ModuleFlattening where
import AST
import Error.Diagnose
import qualified Data.Set as S
import Data.Maybe
import Data.IORef
import Control.Monad
import qualified Data.List as L
import Data.Semigroup
import Data.List.NonEmpty
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.Cont
import Prettyprinter
import Control.Lens
import Control.Lens.At
import GHC.Generics (Generic)
import Data.Typeable (Typeable)
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Name
import Unbound.Generics.LocallyNameless.Unsafe
import System.FilePath ((</>))
import System.IO
import TypingBase
import Debug.Trace
import System.IO.Unsafe

instance Semigroup ModBody where
    md1 <> md2 = 
        ModBody (md1^.isModuleType)
                (md1^.localities <> md2^.localities)
                (md1^.defs <> md2^.defs)
                (md1^.tableEnv <> md2^.tableEnv)
                (md1^.flowAxioms <> md2^.flowAxioms)
                (md1^.advCorrConstraints <> md2^.advCorrConstraints)
                (md1^.tyDefs <> md2^.tyDefs)
                (md1^.userFuncs <> md2^.userFuncs)
                (md1^.nameEnv <> md2^.nameEnv)
                (md1^.ctrEnv <> md2^.ctrEnv)
                (md1^.randomOracle <> md2^.randomOracle)
                (md1^.modules <> md2^.modules)

globalName :: ResolvedPath -> String
globalName PTop = "Top"
globalName (PDot p s) = globalName p ++ "_" ++ s
globalName _ = error "globalName : Got path var"

globalizeMap :: ResolvedPath -> Map String a -> Map String a
globalizeMap p0 mp = Prelude.map (\(x, y) -> (globalName p0 ++ "_" ++ x, y)) mp

flattenModules :: Fresh m => ResolvedPath -> ModBody -> m ModBody
flattenModules p0 md = do
    -- traceM $ "Flattening " ++ show p0 ++ " with nameEnv " ++ show (Prelude.map fst $ md ^. nameEnv)
    mbs <- forM (md^.modules) $ \(s, md) ->
        case md of
          MFun _ _ _ -> return []
          MBody xb -> do
              (x, bdy) <- unbind xb
              if bdy ^. isModuleType == ModConcrete then do
                let bdy' = subst x (PDot p0 s) bdy
                -- traceM $ "Mods: " ++ (show $ Prelude.map fst (bdy' ^. modules))
                bdy'' <- flattenModules (PDot p0 s) bdy'
                return [bdy'']
              else return []
    let md' = 
            ModBody
                ModConcrete
                (globalizeMap p0 $ md^.localities)
                (globalizeMap p0 $ md^.defs)
                (globalizeMap p0 $ md^.tableEnv)
                (md^.flowAxioms)
                (md^.advCorrConstraints)
                (globalizeMap p0 $ md^.tyDefs)
                (globalizeMap p0 $ md^.userFuncs)
                (globalizeMap p0 $ md^.nameEnv)
                (globalizeMap p0 $ md^.ctrEnv)
                (globalizeMap p0 $ md^.randomOracle)
                []
    --traceM $ "---------> " ++ show p0 ++ " with localities " ++ show (md' ^. localities)            
    let res = sconcat $ md' :| concat mbs
    -- traceM $ "|||||||||> " ++ show p0 ++ " with localities " ++ show (res ^. localities)            
    -- return $ traceShow ("end  ", p0, res ^. localities) res
    return res

doFlattening :: Env -> ModBody
doFlattening e = 
    runFreshM $ flattenModules PTop (e^.curMod) 
    




