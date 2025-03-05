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
                (md1^.predicates <> md2^.predicates)
                (md1^.advCorrConstraints <> md2^.advCorrConstraints)
                (md1^.tyDefs <> md2^.tyDefs)
                -- (md1^.odh <> md2^.odh)
                (md1^.nameTypeDefs <> md2^.nameTypeDefs)
                (md1^.userFuncs <> md2^.userFuncs)
                (md1^.nameDefs <> md2^.nameDefs)
                (md1^.ctrEnv <> md2^.ctrEnv)
                (md1^.modules <> md2^.modules)

globalName :: ResolvedPath -> String
globalName PTop = ""
globalName (PDot PTop s) = s
globalName (PDot p s) = globalName p ++ "_" ++ s
globalName _ = error "globalName : Got path var"

globalNameWith :: ResolvedPath -> String -> String
globalNameWith PTop s = s
globalNameWith p s = globalName p ++ "_" ++ s

globalizeMap :: ResolvedPath -> Map String a -> Map String a
globalizeMap p0 mp = Prelude.map (\(x, y) -> (globalNameWith p0 x, y)) mp

flattenModules :: ResolvedPath -> ModBody -> FreshMT IO ([(Name ResolvedPath, ResolvedPath)], ModBody)
flattenModules p0 md = do
    -- traceM $ "Flattening " ++ show p0 ++ " with nameEnv " ++ show (Prelude.map fst $ md ^. nameEnv)
    sbts_mbs <- forM (md^.modules) $ \(s, md) ->
        case md of
          MFun _ _ _ -> return ([], [])
          MAlias _ -> return ([], [])
          MBody xb -> do
              (x, bdy) <- unbind xb
              if bdy ^. isModuleType == ModConcrete then do
                -- traceM $ "Mods: " ++ (show $ Prelude.map fst (bdy' ^. modules))
                (sbts, mb) <- flattenModules (PDot p0 s) bdy
                return ((x, PDot p0 s) : sbts, [mb])
              else return ([], [])
    let sbts = Prelude.concat $ Prelude.map fst sbts_mbs
    let mbs = Prelude.concat $ Prelude.map snd sbts_mbs
    let md' = 
            ModBody
                ModConcrete
                (globalizeMap p0 $ md^.localities)
                (globalizeMap p0 $ md^.defs)
                (globalizeMap p0 $ md^.tableEnv)
                (md^.flowAxioms)
                (md^.predicates)
                (md^.advCorrConstraints)
                (globalizeMap p0 $ md^.tyDefs)
                -- (globalizeMap p0 $ md^.odh)
                (globalizeMap p0 $ md^.nameTypeDefs)
                (globalizeMap p0 $ md^.userFuncs)
                (globalizeMap p0 $ md^.nameDefs)
                (globalizeMap p0 $ md^.ctrEnv)
                []
    let res = sconcat $ md' :| mbs
    return (sbts, res)

doFlattening :: Env senv -> IO ModBody
doFlattening e = do 
    (x, y) <- runFreshMT $ flattenModules PTop (e^.curMod) 
    return $ substs x y
    





