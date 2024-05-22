{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
module ExtractionTop where
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
import CmdArgs
import ConcreteAST
import ExtractionBase
import Verus
import qualified SMTBase
import qualified TypingBase as TB
import qualified Concretify
import qualified LowerImmut
import qualified GenVerus
import qualified SpecExtraction


extract :: Flags -> TB.Env SMTBase.SolverEnv -> String -> TB.ModBody -> IO (Either ExtractionError (Doc ann, Doc ann, Doc ann))
extract flags tcEnv path modbody = runExtractionMonad tcEnv (initEnv flags path (modbody ^. TB.userFuncs)) $ extract' modbody


extract' :: TB.ModBody -> ExtractionMonad FormatTy (Doc ann, Doc ann, Doc ann)
extract' modbody = do
    owlExtrData <- preprocessModBody modbody
    concreteExtrData <- concretifyPass owlExtrData
    specs <- specExtractPass concreteExtrData
    verusTyExtrData <- do
        fs <- use flags
        if fs ^. fExtractBufOpt then 
            throwError $ ErrSomethingFailed "TODO: buffer-optimization for extraction"
        else lowerImmutPass concreteExtrData
    (extractedOwl, extractedVest) <- liftExtractionMonad $ genVerusPass verusTyExtrData
    (entryPoint, libHarness, callMain) <- mkEntryPoint verusTyExtrData
    p <- prettyFile "extraction/preamble.rs"
    lp <- prettyFile "extraction/lib_preamble.rs"
    return (
        p                       <> line <> line <> line <> line <> 
        pretty "verus! {"       <> line <> line <> 
        pretty "// ------------------------------------" <> line <>
        pretty "// ---------- SPECIFICATIONS ----------" <> line <>
        pretty "// ------------------------------------" <> line <> line <>
        specs                   <> line <> line <> line <> line <>
        pretty "// ------------------------------------" <> line <>
        pretty "// ---------- IMPLEMENTATIONS ---------" <> line <>
        pretty "// ------------------------------------" <> line <> line <>
        extractedOwl            <> line <> line <> line <> line <>
        pretty "// ------------------------------------" <> line <>
        pretty "// ------------ ENTRY POINT -----------" <> line <>
        pretty "// ------------------------------------" <> line <> line <>
        entryPoint                 <> line <> line <>
        pretty "} // verus!"    <> line <> line <>
        callMain                <> line <> line
      , lp                      <> line <> line <> line <> line <> 
        libHarness
      , extractedVest
      )

preprocessModBody :: TB.ModBody -> ExtractionMonad t OwlExtractionData
preprocessModBody mb = do
    debugLog "Preprocessing"
    let (locs, locAliases) = sortLocs $ mb ^. TB.localities
    let lookupLoc = lookupLoc' locs locAliases
    let locMap = M.map (\npids -> LocalityData npids [] [] [] [] []) locs
    locMap <- foldM (sortTable lookupLoc) locMap (mb ^. TB.tableEnv)
    locMap <- foldM (sortCtr lookupLoc) locMap (mb ^. TB.ctrEnv)
    (locMap, shared, pubkeys) <- foldM (sortName lookupLoc) (locMap, [], []) (mb ^. TB.nameDefs)
    locMap <- foldM (sortDef lookupLoc) locMap (mb ^. TB.defs)
    let tydefs = reverse $ mb ^. TB.tyDefs
    debugLog "Finished preprocessing"
    -- User funcs get filled in during concretization, since we only want to extract 
    -- user funcs that are used in concrete (non-ghost) code
    return $ ExtractionData locMap shared pubkeys tydefs []
    where
        sortLocs = foldl' (\(locs, locAliases) (locName, locType) -> 
                                case locType of 
                                    Left i -> (M.insert locName i locs, locAliases)
                                    Right p -> (locs, M.insert locName (flattenResolvedPath p) locAliases)) 
                             (M.empty, M.empty)

        lookupLoc' :: M.Map LocalityName Int -> M.Map LocalityName LocalityName -> LocalityName -> ExtractionMonad t LocalityName
        lookupLoc' locs locAliases l = do
                case locs M.!? l of
                    Just _ -> return l
                    Nothing -> 
                        case locAliases M.!? l of
                            Just l' -> lookupLoc' locs locAliases l'
                            Nothing -> throwError $ ErrSomethingFailed $ "couldn't lookup locality alias " ++ show l
        
        sortTable :: (LocalityName -> ExtractionMonad t LocalityName) -> M.Map LocalityName OwlLocalityData -> (String, (Ty, Locality)) -> ExtractionMonad t (M.Map LocalityName OwlLocalityData)
        sortTable lookupLoc locMap (name, (ty, Locality locP _)) = do
            locName <- lookupLoc =<< flattenPath locP
            let f = tables %~ flip (++) [(name, ty)] 
            return $ M.adjust f locName locMap

        sortCtr :: (LocalityName -> ExtractionMonad t LocalityName) -> M.Map LocalityName OwlLocalityData -> (String, Bind ([IdxVar], [IdxVar]) Locality) -> ExtractionMonad t (M.Map LocalityName OwlLocalityData)
        sortCtr lookupLoc locMap (name, b) = do
            let ((sids, pids), Locality locP _) = unsafeUnbind b
            when (length sids > 0) $ debugPrint $ "WARNING: ignoring sid indices on counter " ++ name
            locName <- lookupLoc =<< flattenPath locP
            let f = counters %~ flip (++) [name]
            return $ M.adjust f locName locMap

            -- case (sids, pids) of
            --     ([], _) -> do
                    -- ...
                -- _ -> throwError $ ErrSomethingFailed "TODO indexed counters"

        resolveNameApp :: Path -> ExtractionMonad t (Bind (([IdxVar], [IdxVar]), [DataVar]) NameType)
        resolveNameApp p = do
            s <- tailPath p
            let ntds = mb ^. TB.nameTypeDefs
            case lookup s ntds of
                Just b -> return b
                _ -> throwError $ ErrSomethingFailed $ "couldn't resolve name app " ++ show s

        sortName :: (LocalityName -> ExtractionMonad t LocalityName) 
                    -> (M.Map LocalityName OwlLocalityData, [(NameData, [LocalityName])], [NameData]) 
                    -> (String, (Bind ([IdxVar], [IdxVar]) TB.NameDef))
                    -> ExtractionMonad t (M.Map LocalityName OwlLocalityData, [(NameData, [LocalityName])], [NameData]) 
        sortName lookupLoc (locMap, shared, pubkeys) (name, binds) = do
            let ((sids, pids), nd) = unsafeUnbind binds
            case nd of
              TB.AbstractName -> return (locMap, shared, pubkeys) -- ignore abstract names, they should be concretized when used
              TB.BaseDef (nt, loc) -> do
                nt <- case nt ^. val of
                    NT_App p _ _ -> do
                        b <- resolveNameApp p
                        let (_, nt) = unsafeUnbind b
                        return nt
                    _ -> return nt
                flen <- fLenOfNameTy nt
                let nsids = length sids
                let npids = length pids
                when (nsids > 1) $ throwError $ DefWithTooManySids name
                let gPub m lo = M.adjust (sharedNames %~ flip (++) [(name, flen, npids)]) lo m
                let gPriv m lo = M.adjust (localNames %~ flip (++) [(name, flen, npids)]) lo m
                locNames <- mapM (\(Locality lname _) -> flattenPath lname) loc
                case nt ^.val of
                    -- public keys must be shared, so pub/priv key pairs are generated by the initializer
                    NT_PKE _ ->
                        return (foldl gPub locMap locNames, shared ++ [((name, flen, npids), locNames)], pubkeys ++ [(name, flen, npids)])
                    NT_Sig _ ->
                        return (foldl gPub locMap locNames, shared ++ [((name, flen, npids), locNames)], pubkeys ++ [(name, flen, npids)])
                    NT_DH ->
                        return (foldl gPub locMap locNames, shared ++ [((name, flen, npids), locNames)], pubkeys ++ [(name, flen, npids)])
                    _ -> if length loc /= 1 then
                            -- name is shared among multiple localities
                            return (foldl gPub locMap locNames, shared ++ [((name, flen, npids), locNames)], pubkeys)
                        else
                            -- name is local and can be locally generated
                            return (foldl gPriv locMap locNames, shared, pubkeys)
              TB.AbbrevNameDef _ -> do
                throwError $ ErrSomethingFailed "TODO sortName for AbbrevNameDef"

        sortDef :: (LocalityName -> ExtractionMonad t LocalityName) -> M.Map LocalityName OwlLocalityData -> (String, TB.Def) -> ExtractionMonad t (M.Map LocalityName OwlLocalityData)
        sortDef _ m (_, TB.DefHeader _) = return m
        sortDef lookupLoc m (owlName, def@(TB.Def idxs_defSpec)) = do
                let ((sids, pids), defspec) = unsafeUnbind idxs_defSpec 
                when (length sids > 1) $ throwError $ DefWithTooManySids owlName
                let loc@(Locality locP _) = defspec ^. TB.defLocality
                locName <- lookupLoc =<< flattenPath locP
                let f = defs %~ flip (++) [(owlName, def)]
                return $ M.adjust f locName m

traverseExtractionData :: 
    (def -> ExtractionMonad t def') ->
    (name -> ExtractionMonad t name') ->
    (String -> ty -> ExtractionMonad t (Maybe ty')) ->
    (uf -> ExtractionMonad t uf') ->
    ExtractionData def ty name uf -> ExtractionMonad t (ExtractionData def' ty' name' uf')
traverseExtractionData traverseDef traverseName traverseTyDef traverseUF extrData = do
    ufs' <- mapM traverseUF (extrData ^. userFuncs)
    locMap' <- M.traverseWithKey traverseLoc (extrData ^. locMap)
    preshared' <- mapM (\(nameData, locs) -> do
        nameData' <- traverseName nameData
        return (nameData', locs)) (extrData ^. presharedNames)
    pubKeys' <- mapM traverseName (extrData ^. pubKeys)
    tyDefs' <- catMaybes <$> mapM (\(name, ty) -> do
            ty' <- traverseTyDef name ty
            case ty' of
                Nothing -> return Nothing
                Just ty' -> return $ Just (name, ty')
        ) (extrData ^. tyDefs)
    return $ ExtractionData locMap' preshared' pubKeys' tyDefs' ufs'
    where
        traverseLoc lname locData = do
            localNames' <- mapM traverseName (locData ^. localNames)
            sharedNames' <- mapM traverseName (locData ^. sharedNames)
            defs' <- mapM traverseDef (locData ^. defs)
            return $ LocalityData (locData ^. nLocIdxs) localNames' sharedNames' defs' (locData ^. tables) (locData ^. counters)


concretifyPass :: OwlExtractionData -> ExtractionMonad FormatTy CFExtractionData
concretifyPass owlExtrData = do
    debugLog "Concretifying"
    Concretify.setupEnv $ owlExtrData ^. tyDefs
    cfExtrData <- traverseExtractionData
        (uncurry Concretify.concretifyDef)
        return
        Concretify.concretifyTyDef
        (uncurry Concretify.concretifyUserFunc) -- Dummy, doesn't actually get used here
        owlExtrData
    concreteUserFuncs <- catMaybes <$> concretifyUserFuncs
    return $ cfExtrData & userFuncs .~ concreteUserFuncs
    where
        -- Extract only the user funcs that need to be extracted
        concretifyUserFuncs = do
            oufs <- M.assocs <$> use owlUserFuncs 
            let oufs' = mapMaybe (\(name, (uf, rtopt)) -> case rtopt of Just _ -> Just (name, uf) ; Nothing -> Nothing) oufs
            mapM (uncurry Concretify.concretifyUserFunc) oufs'
    
lowerImmutPass :: CFExtractionData -> ExtractionMonad FormatTy CRExtractionData
lowerImmutPass cfExtrData = do
    debugLog "Lowering to Verus types: immutable translation"
    traverseExtractionData
        lowerDef
        LowerImmut.lowerName
        LowerImmut.lowerTyDef
        LowerImmut.lowerUserFunc
        cfExtrData
    where lowerDef (Just d) = Just <$> LowerImmut.lowerDef d
          lowerDef Nothing = return Nothing

-- Directly generate strings; first ret val is the Verus code, second is the generated Vest code
genVerusPass :: CRExtractionData -> ExtractionMonad VerusTy (Doc ann, Doc ann)
genVerusPass crExtrData = do
    debugLog "Generating Verus code"
    endpointDef <- GenVerus.genVerusEndpointDef <$> M.keys $ crExtrData ^. locMap
    (tyDefs, vestDefs) <- GenVerus.genVerusTyDefs $ crExtrData ^. tyDefs
    locDefs <- mapM (GenVerus.genVerusLocality $ crExtrData ^. pubKeys) <$> M.assocs $ crExtrData ^. locMap
    userFuncDefs <- mapM GenVerus.genVerusUserFunc $ crExtrData ^. userFuncs
    let verusDefs = vsep $ endpointDef : tyDefs : locDefs ++ userFuncDefs
    return (verusDefs, vestDefs)

specExtractPass :: CFExtractionData -> ExtractionMonad FormatTy (Doc ann)
specExtractPass cfExtrData = do
    debugLog $ "Generating Verus specs"
    tyDefs <- mapM (SpecExtraction.extractCTyDef . snd) $ cfExtrData ^. tyDefs
    defSpecs <- mapM SpecExtraction.extractLoc <$> M.assocs $ cfExtrData ^. locMap
    userFuncSpecs <- mapM SpecExtraction.extractUserFunc $ cfExtrData ^. userFuncs
    return $ vsep $ tyDefs ++ defSpecs ++ userFuncSpecs

mkEntryPoint :: CRExtractionData -> ExtractionMonad t (Doc ann, Doc ann, Doc ann)
mkEntryPoint verusExtrData = do
    debugLog "Generating entry point"
    fs <- use flags
    if fs ^. fExtractHarness then do
        throwError $ ErrSomethingFailed "TODO harness generation in mkEntryPoint"
    else 
        return (
                pretty "/* no entry point */"
            ,   pretty "/* no library harness routines */"
            ,   pretty "fn main() { }" <> line
        )


prettyFile :: String -> ExtractionMonad t (Doc ann)
prettyFile fn = do
    s <- liftIO $ readFile fn
    return $ pretty s
