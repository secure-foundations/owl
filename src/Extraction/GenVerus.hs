{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module GenVerus where
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
import ANFPass (isGhostTyAnn)
import Verus
import PrettyVerus
import ConcreteAST
import ExtractionBase
import AST
--import Data.String.Interpolate (i, __i, iii)
import Prettyprinter.Interpolate

type EM = ExtractionMonad VerusTy


genVerusUserFunc :: CUserFunc VerusTy -> EM (Doc ann)
genVerusUserFunc (CUserFunc name b) = do
    let execname = execName name
    let specname = name
    (args, (retTy, body)) <- unbindCDepBind b
    let argdefs = hsep . punctuate comma $ fmap (\(n, _, t) -> [di|#{execName . show $ n}: #{pretty t}|]) args
    let viewArgs = hsep . punctuate comma $ fmap (\(n, _, t) -> [di|#{execName . show $ n}.dview()|]) args
    body' <- genVerusCAExpr body
    let needsLifetime = tyNeedsLifetime retTy
    let lifetimeConst = "a"
    let lifetimeAnnot = pretty $ if needsLifetime then "<'" ++ lifetimeConst ++ ">" else ""
    let retTy' = liftLifetime lifetimeConst retTy
    let retval = [di|res: #{pretty retTy'}|]
    let ensuresLenValid = case retTy of
            RTOwlBuf _ -> [di|res.len_valid()|]
            RTStruct _ _ -> [di|res.len_valid()|]
            RTEnum _ _ -> [di|res.len_valid()|]
            _ -> [di||]
    return [__di|
    pub fn #{execname}#{lifetimeAnnot}(#{argdefs}) -> (#{retval})
        ensures
            res.dview() == #{specname}(#{viewArgs}),
            #{ensuresLenValid}
    {
        reveal(#{specname});
        #{body'}
    }
    |]


genVerusEndpointDef :: [LocalityName] -> EM (Doc ann)
genVerusEndpointDef lnames = do
    let locNameOf s = [di|Loc_#{s}|]
    let locEnum = [__di|
    \#[derive(Clone,Copy)]
    pub enum Endpoint {
        #{vsep . punctuate comma . map locNameOf $ lnames}
    }
    |]
    let endpointOfAddr = [__di|
    \#[verifier(external_body)]
    pub closed spec fn endpoint_of_addr(addr: Seq<char>) -> Endpoint {
        unimplemented!() /* axiomatized */
    }
    |]
    let mkLocAddr (lname, ipport) = [__di|
    \#[verifier(external_body)]
    pub const fn #{lname}_addr() -> (a: StrSlice<'static>) 
        ensures endpoint_of_addr(a.view()) == Endpoint::#{locNameOf lname}
    {
        new_strlit("127.0.0.1:#{pretty ipport}")
    }
    |]
    let locNameAddrs :: [(LocalityName, Int)] = zip lnames $ [9000 + x | x <- [1..]]
    let locAddrDefs = map mkLocAddr locNameAddrs
    return $ vsep $ locEnum : endpointOfAddr : locAddrDefs


genVerusLocality :: [VNameData] -> (LocalityName, VerusLocalityData) -> EM (Doc ann)
genVerusLocality pubkeys (lname, ldata) = do
    let stateName = pretty $ "state_" ++ lname
    let cfgName = pretty $ "cfg_" ++ lname
    let (localNameDecls, localNameInits) = unzip . map (genVerusName False) $ ldata ^. localNames
    let (sharedNameDecls, sharedNameInits) = unzip . map (genVerusName True) $ ldata ^. sharedNames
    let (pkDecls, pkInits) = unzip . map (genVerusPk True) $ pubkeys
    let (ctrDecls, ctrInits) = unzip . map genVerusCtr $ ldata ^. counters
    execFns <- mapM (genVerusDef lname) . catMaybes $ ldata ^. defs
    return [__di|
    pub struct #{stateName} {
        #{vsep . punctuate comma $ ctrDecls}
    }
    impl #{stateName} {
        \#[verifier::external_body]
        pub fn init_#{stateName}() -> Self {
            #{stateName} { 
                #{vsep . punctuate comma $ ctrInits}
            }
        }
    }
    pub struct #{cfgName} {
        pub listener: TcpListener,
        pub salt: Vec<u8>,
        #{vsep . punctuate comma $ localNameDecls ++ sharedNameDecls ++ pkDecls},
    }
    impl #{cfgName} {
        // TODO: library routines for reading configs
        /*
        \#[verifier::external_body]
        pub fn init_#{cfgName}(config_path: &StrSlice) -> Self {
            let listener = TcpListener::bind(#{lname}_addr().into_rust_str()).unwrap();
            let config_str = fs::read_to_string(config_path.into_rust_str()).expect("Config file not found");
            let config = deserialize_cfg_alice_config(&config_str);
            #{cfgName} { 
                listener,
                salt: (config.salt),
                #{vsep . punctuate comma $ localNameInits ++ sharedNameInits ++ pkInits}
            }
        }
        */

        #{vsep . punctuate (line <> line) $ execFns}
    }
    |]

-- ctr decl, ctr init
genVerusCtr :: VerusName -> (Doc ann, Doc ann)
genVerusCtr counterName =
    let counterName' = execName counterName in
    let ctrDecl = [di|pub #{counterName'} : usize|] in
    let ctrInit = [di|#{counterName'} : 0|] in
    (ctrDecl, ctrInit)

nameTy :: VerusTy
nameTy = vecU8

-- name decl, name initializer
genVerusName :: Bool -> VNameData -> (Doc ann, Doc ann)
genVerusName fromConfig (vname, vsize, _) = 
    -- We ignore PID indices for now
    -- debugLog $ "genVerusName: " ++ vname
    let execname = execName vname in
    let nameDecl = [di|pub #{execname} : #{pretty nameTy}|] in
    let nameInitBody = 
            if fromConfig then [di|config.#{execname}|]
            else [di|owl_util::gen_rand_bytes(#{pretty vsize})|] in
    let nameInit = [di|#{execname} : (#{nameInitBody})|] in
    (nameDecl, nameInit)

-- name decl, name initializer
genVerusPk :: Bool -> VNameData -> (Doc ann, Doc ann)
genVerusPk fromConfig (vname, vsize, _) = 
    -- We ignore PID indices for now
    -- debugLog $ "genVerusName: " ++ vname
    let execname = "pk_" ++ execName vname in
    let nameDecl = [di|pub #{execname} : #{pretty nameTy}|] in
    let nameInitBody = 
            if fromConfig then [di|config.#{execname}|]
            else [di|owl_util::gen_rand_bytes(#{pretty vsize})|] in
    let nameInit = [di|#{execname} : (#{nameInitBody})|] in
    (nameDecl, nameInit)

-- These should be kept in one-to-one correspondence with execlib.rs
-- TODO in the far future, somehow have these generated from the Rust code?
builtins :: M.Map String (String, [VerusTy], VerusTy)
builtins = M.mapWithKey addExecName builtins' `M.union` diffNameBuiltins where
    addExecName n (args, rty) = (execName n, args, rty)
    builtins' = M.fromList [
          ("enc", ([u8slice, u8slice, u8slice], vecU8))
        , ("dec", ([u8slice, u8slice], RTOption vecU8))
        , ("sign", ([u8slice, u8slice], vecU8))
        , ("vrfy", ([u8slice, u8slice, u8slice], RTOption vecU8))
        , ("dhpk", ([u8slice], vecU8))
        , ("dh_combine", ([u8slice, u8slice], vecU8))
        , ("mac", ([u8slice, u8slice], vecU8))
        , ("mac_vrfy", ([u8slice, u8slice, u8slice], RTOption vecU8))
        , ("pkenc", ([u8slice, u8slice], vecU8))
        , ("pkdec", ([u8slice, u8slice], vecU8))
        -- , ("enc_st_aead", ([u8slice, u8slice, u8slice, u8slice], vecU8)) -- special-cased
        , ("dec_st_aead", ([u8slice, u8slice, u8slice, u8slice], RTOption vecU8))
        , ("is_group_elem", ([u8slice], RTBool))
        , ("crh", ([u8slice], vecU8))
        , ("bytes_as_counter", ([u8slice], RTUsize))
        , ("counter_as_bytes", ([RTRef RShared RTUsize], RTArray RTU8 (CUsizeConst "COUNTER_SIZE")))
        ]
    diffNameBuiltins = M.fromList [
          ("kdf", ("extract_expand_to_len", [u8slice, u8slice, u8slice, u8slice], vecU8))
        ]

genVerusCAExpr :: CAExpr VerusTy -> EM (Doc ann)
genVerusCAExpr ae = do
    case ae ^. tval of
        CAVar s v -> return $ pretty $ execName $ show v
        CAApp f args -> do
            case builtins M.!? f of
                Just (fExecName, argDstTys, rSrcTy) -> do
                    args' <- mapM genVerusCAExpr args
                    let argtys = map (^. tty) args
                    args'' <- zipWithM cast (zip args' argtys) argDstTys
                    castRes <- cast ([di|val|], rSrcTy) (ae ^. tty)
                    return [__di|
                    {
                        let val = #{fExecName}(#{hsep . punctuate comma $ args''});
                        #{castRes}
                    }
                    |]
                Nothing -> do
                    -- Special cases for things which aren't regular function calls in Rust
                    case (f, args) of
                        ("enc_st_aead", [k, x, nonce, aad]) -> do
                            k' <- genVerusCAExpr k
                            x' <- genVerusCAExpr x
                            nonce' <- genVerusCAExpr nonce
                            aad' <- genVerusCAExpr aad
                            castK <- cast (k', k ^. tty) u8slice
                            castX <- cast (x', x ^. tty) u8slice
                            castNonce <- cast (nonce', nonce ^. tty) (RTRef RMut RTUsize)
                            castAad <- cast (aad', aad ^. tty) u8slice
                            castRes <- cast ([di|ctxt|], vecU8) (ae ^. tty)
                            return [__di|{ 
                                match owl_enc_st_aead(#{castK}, #{castX}, #{castNonce}, #{castAad}) {
                                    Ok(ctxt) => { #{castRes} },
                                    Err(e) => { return Err(e) },
                                }                                
                            }|]
                        ("true", []) -> return [di|true|]
                        ("false", []) -> return [di|false|]
                        ("Some", [x]) -> do
                            x' <- genVerusCAExpr x
                            return [di|Some(#{x'})|]
                        ("None", []) -> return [di|None|]
                        ("eq", [x,y]) -> do
                            x' <- genVerusCAExpr x
                            y' <- genVerusCAExpr y
                            let castXTo = cast (x', x ^. tty)
                            let castYTo = cast (y', y ^. tty)
                            case (x ^. tty, y ^. tty) of
                                (RTVec RTU8, RTVec RTU8) -> do
                                    x'' <- castXTo u8slice
                                    y'' <- castYTo u8slice
                                    return [di|{ slice_eq(#{x''}, #{y''}) }|]
                                (RTRef _ (RTSlice RTU8), RTRef _ (RTSlice RTU8)) -> do
                                    x'' <- castXTo u8slice
                                    y'' <- castYTo u8slice
                                    return [di|{ slice_eq(#{x''}, #{y''}) }|]
                                (RTOwlBuf _, RTOwlBuf _) -> do
                                    x'' <- castXTo u8slice
                                    y'' <- castYTo u8slice
                                    return [di|{ slice_eq(#{x''}, #{y''}) }|]
                                _ -> return [di|#{x'} == #{y'}|] -- might not always work
                        _ -> do
                            args' <- mapM genVerusCAExpr args
                            return [di|#{execName f}(#{hsep . punctuate comma $ args'})|]
        CAGet n -> do
            let rustN = execName n
            castN <- cast ([di|self.#{rustN}|], nameTy) (ae ^. tty)
            return [di|#{castN}|]
        CAInt fl -> return $ pretty $ lowerFLen fl
        CACounter ctrname -> do
            let rustCtr = execName ctrname
            castCtr <- cast ([di|mut_state.#{rustCtr}|], RTUsize) (ae ^. tty)
            return [di|#{castCtr}|]
        CAHexConst s -> do
            s' <- hexStringToByteList s
            castX <- ([di|x|], vecU8) `cast` (ae ^. tty)
            return [di|{ let x = mk_vec_u8![#{s'}]; #{castX} }|] 
        _ -> return [__di|
        /*
            TODO: genVerusCAExpr #{show ae}
        */
        |]


-- Extra info needed just for `genVerusCExpr`
data GenCExprInfo ann = GenCExprInfo { 
    -- True if we are extracting the expression `k` in `let x = e in k`, false if we are extracting `e`
    -- We need to track this since at the end of `k`, Rust requires us to return the itree token as well (see CRet case)
    inK :: Bool, 
    -- The spec itree type of the current function, which is needed because Rust type inference cannot infer it
    specItreeTy :: Doc ann,
    curLocality :: LocalityName
} deriving (Show)


genVerusCExpr :: GenCExprInfo ann -> CExpr VerusTy -> EM (Doc ann)
genVerusCExpr info expr = do
    case expr ^. tval of
        CSkip -> return [di|()|]
        CRet ae -> do
            ae' <- genVerusCAExpr ae
            if inK info then
                return [di|(#{ae'}, Tracked(itree))|]
            else 
                return [di|#{ae'}|]
        CInput t xek -> do
            let ((x, ev), k) = unsafeUnbind xek
            let rustX = execName . show $ x
            let rustEv = if show ev == "_" then "_" else execName . show $ ev
            let itreeTy = specItreeTy info
            k' <- genVerusCExpr info k
            castTmp <- ([di|tmp_#{rustX}|], vecU8) `cast` t
            return [__di|
            let (tmp_#{rustX}, #{rustEv}) = { owl_input::<#{itreeTy}>(Tracked(&mut itree), &self.listener) };
            let #{rustX} = #{castTmp};
            #{k'}
            |]
        COutput ae dst -> do
            dst' <- case dst of
                Just (EndpointLocality (Locality lname _)) -> do
                    plname <- flattenPath lname
                    return [di|&#{plname}_addr()|]
                Just (Endpoint ev) -> return [di|&#{execName . show $ ev}.as_str()|]
                Nothing -> throwError OutputWithUnknownDestination 
            let myAddr = [di|&#{curLocality info}_addr()|]
            ae' <- genVerusCAExpr ae
            aeCast <- (ae', ae ^. tty) `cast` u8slice
            let retItree = if inK info then [di|((), Tracked(itree))|] else [di||]
            let itreeTy = specItreeTy info
            return [__di|
            owl_output::<#{itreeTy}>(Tracked(&mut itree), #{aeCast}, #{dst'}, #{myAddr}); 
            #{retItree}
            |]
        CSample fl xk -> do
            let (x, k) = unsafeUnbind xk
            let rustX = execName . show $ x
            let sz = lowerFLen fl
            k' <- genVerusCExpr info k
            let itreeTy = specItreeTy info
            return [__di|
            let #{rustX} = owl_sample::<#{itreeTy}>(Tracked(&mut itree), #{pretty sz});
            #{k'}
            |]
        CLet e oanf xk -> do
            let (x, k) = unsafeUnbind xk
            let rustX = execName . show $ x
            e' <- genVerusCExpr (info { inK = False }) e
            k' <- genVerusCExpr info k
            return [__di|
            let #{rustX} = { #{e'} };
            #{k'}
            |]
        CBlock ebody -> do
            ebody' <- genVerusCExpr info ebody
            return [__di|
            { 
                #{ebody'} 
            }
            |]
        CIf ae e1 e2 -> do
            ae' <- genVerusCAExpr ae
            e1' <- genVerusCExpr info e1
            e2' <- genVerusCExpr info e2
            return [__di|
            if #{ae'} {
                #{e1'}
            } else {
                #{e2'}
            }
            |]
        CCase ae cases -> do
            ae' <- genVerusCAExpr ae
            aeTyPrefix <- case ae ^. tty of
                RTEnum n _ -> return [di|#{execName n}::|]
                RTOption _ -> return [di|Option::|]
                t -> throwError $ UndefinedSymbol $ "attempt to case on type " ++ show t
            let genCase (c, o) = do
                    case o of
                        Left k -> do
                            k' <- genVerusCExpr info k
                            let parens = case ae ^. tty of
                                    RTOption _ -> ""
                                    _ -> "()"
                            return [__di|
                            #{aeTyPrefix}#{c}#{parens} => { 
                                #{k'} 
                            },
                            |]
                        Right xtk -> do
                            let (x, (t, k)) = unsafeUnbind xtk
                            let rustX = execName . show $ x
                            -- We include this in case we decide during type-lowering to 
                            -- represent the contained type differently in the enum and
                            -- in the case body (e.g., if the enum contains an owned Vec
                            -- but the case body should have an OwlBuf or something)
                            castTmp <- ([di|tmp_#{rustX}|], t) `cast` t
                            k' <- genVerusCExpr info k
                            return [__di|
                            #{aeTyPrefix}#{c}(tmp_#{rustX}) => {
                                let #{rustX} = #{castTmp}; 
                                #{k'} 
                            },
                            |]
            cases' <- mapM genCase cases
            return [__di|
            match #{ae'} {
                #{vsep cases'}
            }
            |]
        CParse pkind ae t maybeOtw xtsk -> do
            let (xts, k) = unsafeUnbind xtsk
            let castRustXs = map (\(x, _, t) -> (execName . show $ x, t)) xts
            (dstTyName, parsedTypeMembers) <- case t of
                    RTStruct tn fts -> do
                        let genField (f, ft) = do
                                return ([di|parseval.#{f}|], ft)
                        (,) tn <$> mapM genField fts
                    RTEnum tn _ -> return (tn, [([di|parseval|], t)])
                    _ -> throwError $ TypeError $ "Got bad destination type for parse: " ++ show t
            when (length castRustXs /= length parsedTypeMembers) $ throwError $ TypeError "bad number of parsed type members"
            let genSelector (fselector, fty) (dstVar, dstTy) = do
                    castTmp <- (fselector, fty) `cast` dstTy
                    return [__di|
                    let #{dstVar} = #{castTmp};
                    |]
            selectors <- zipWithM genSelector parsedTypeMembers castRustXs
            ae' <- genVerusCAExpr ae
            k' <- genVerusCExpr info k
            case (pkind, maybeOtw) of
                (PFromBuf, Just otw) -> do
                    otw' <- genVerusCExpr info otw
                    castParsevalTmp <- ([di|parseval_tmp|], ae ^. tty) `cast` u8slice
                    return [__di|
                    let parseval_tmp = #{ae'};
                    if let Some(parseval) = parse_#{dstTyName}(#{castParsevalTmp}) {
                        #{vsep selectors}
                        #{k'}
                    } else {
                        #{otw'}
                    }
                    |]
                (PFromDatatype, _) -> do
                    return [__di|
                    let parseval = #{ae'};
                    #{vsep selectors}
                    #{k'}
                    |]
                _ -> throwError $ TypeError "Tried to parse from buf without an otherwise case!"
        CGetCtr ctrname -> do
            let rustCtr = execName ctrname
            castCtr <- ([di|owl_counter_as_bytes(&mut_state.#{rustCtr})|], RTArray RTU8 (CUsizeConst "COUNTER_SIZE")) `cast` (expr ^. tty)
            return [di|#{castCtr}|]
        _ -> do
            return [__di|
            /*
                TODO: genVerusCExpr #{show expr}
            */
            |] 


-- Add lifetimes to references, structs, enums, OwlBufs for args/return types
addLifetime :: Lifetime -> VerusTy -> VerusTy
addLifetime lt (RTRef RMut ty) = RTRef (RMutWithLifetime lt) ty
addLifetime lt (RTRef RShared ty) = RTRef (RSharedWithLifetime lt) ty
addLifetime lt (RTStruct s fs) = if structNeedsLifetime s fs then RTWithLifetime (RTStruct s fs) lt else RTStruct s fs
addLifetime lt (RTEnum s cs) = if enumNeedsLifetime s cs then RTWithLifetime (RTEnum s cs) lt else RTEnum s cs
addLifetime lt (RTOwlBuf _) = RTOwlBuf lt
addLifetime _ t = t 

genVerusDef :: VerusName -> CDef VerusTy -> EM (Doc ann)
genVerusDef lname cdef = do
    let execname = execName $ cdef ^. defName
    let specname = cdef ^. defName ++ "_spec"
    (defArgs', (rty', body)) <- unbindCDepBind $ cdef ^. defBody
    -- If any of the arguments or return type have a lifetime, we parameterize the whole function with lifetime 'a
    -- and make all arguments and return types have that lifetime
    let lt = Lifetime "a"
    let ltArgs = map (\(n, s, t) -> (n, s, addLifetime lt t)) defArgs'
    let ltRty = addLifetime lt rty'
    let (defArgs, rty, needsLt) = 
            if ltArgs == defArgs' && ltRty == rty' then (defArgs', rty', False) else (ltArgs, ltRty, True)
    verusArgs <- mapM compileArg defArgs
    let specRt = specTyOfExecTySerialized rty
    let itreeTy = [di|Tracked<ITreeToken<(#{pretty specRt}, state_#{lname}),Endpoint>>|]
    let itreeArg = [di|Tracked(itree): |] <> itreeTy
    let mutStateArg = [di|mut_state: &mut state_#{lname}|]
    let argdefs = hsep . punctuate comma $ [di|&#{if needsLt then pretty lt else pretty ""} self|] : itreeArg : mutStateArg : verusArgs
    let retval = [di|(res: Result<(#{pretty rty}, #{itreeTy}), OwlError>)|]    
    specargs <- mapM viewArg defArgs
    let genInfo = GenCExprInfo { inK = True, specItreeTy = [di|(#{pretty specRt}, state_#{lname})|], curLocality = lname }
    body <- genVerusCExpr genInfo body
    viewRes <- viewVar "(r.0)" rty
    let mkArgLenVald (arg, s, argty) = case argty of
            RTOwlBuf _ -> Just [di|#{prettyArgName arg}.len_valid()|]
            RTStruct _ _ -> Just [di|#{prettyArgName arg}.len_valid()|]
            RTEnum _ _ -> Just [di|#{prettyArgName arg}.len_valid()|]
            RTWithLifetime t _ -> mkArgLenVald (arg, s, t)
            _ -> Nothing
    let requiresLenValid = hsep . punctuate comma $ mapMaybe mkArgLenVald defArgs
    let mkEnsuresLenValid rty'' = case rty'' of
            RTOwlBuf _ -> [di|res matches Ok(r) ==> r.0.len_valid()|]
            RTStruct _ _ -> [di|res matches Ok(r) ==> r.0.len_valid()|]
            RTEnum _ _ -> [di|res matches Ok(r) ==> r.0.len_valid()|]
            RTWithLifetime t _ -> mkEnsuresLenValid rty''
            _ -> [di||]
    let ensuresLenValid = mkEnsuresLenValid rty
    return [__di|
    \#[verifier::spinoff_prover]
    pub fn #{execname}#{if needsLt then angles (pretty lt) else pretty ""}(#{argdefs}) -> #{retval}
        requires 
            itree.view() == #{specname}(*self, *old(mut_state), #{hsep . punctuate comma $ specargs}),
            #{requiresLenValid}
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in((#{viewRes}, *mut_state)),
            #{ensuresLenValid}
    {
        let tracked mut itree = itree;
        let res_inner = {
            broadcast use itree_axioms;
            reveal(#{specname});
            #{body}
        };
        Ok(res_inner)
    }
    |]
    where
        compileArg (cdvar, strname, ty) = do
            return [di|#{prettyArgName $ cdvar}: #{pretty ty}|]
        viewArg (cdvar, strname, ty) = viewVar (execName . show $ cdvar) ty
        prettyArgName = pretty . execName . show


vestLayoutOf :: String -> Maybe ConstUsize -> VerusTy -> ExtractionMonad t (Maybe (Doc ann))
vestLayoutOf name _ (RTArray RTU8 len) = do
    lenConcrete <- concreteLength len
    return $ Just [di|#{name}: [u8; #{pretty lenConcrete}]|]
vestLayoutOf name (Just len) (RTVec RTU8) = do
    lenConcrete <- concreteLength len
    return $ Just [di|#{name}: [u8; #{pretty lenConcrete}]|]
vestLayoutOf name (Just len) (RTOwlBuf (Lifetime _)) = do
    lenConcrete <- concreteLength len
    return $ Just [di|#{name}: [u8; #{pretty lenConcrete}]|]
vestLayoutOf name _ (RTVec RTU8) = return $ Just [di|#{name}: Tail|]
vestLayoutOf name _ (RTOwlBuf (Lifetime _)) = return $ Just [di|#{name}: Tail|]
vestLayoutOf name _ t = return Nothing

vestLayoutOf' :: String -> Maybe ConstUsize -> VerusTy -> EM (Doc ann)
vestLayoutOf' name len t = do
    layout <- vestLayoutOf name len t
    case layout of
        Just l -> return l
        Nothing -> throwError $ ErrSomethingFailed $ "TODO: vestLayoutOf " ++ show t


tyNeedsLifetime :: VerusTy -> Bool
tyNeedsLifetime (RTOwlBuf _) = True
tyNeedsLifetime (RTWithLifetime _ _) = True
tyNeedsLifetime (RTStruct n' fs') = structNeedsLifetime n' fs'
tyNeedsLifetime (RTEnum n' cs') = enumNeedsLifetime n' cs'
tyNeedsLifetime _ = False 

structNeedsLifetime :: VerusName -> [(VerusName, VerusTy)] -> Bool
structNeedsLifetime _ = any (tyNeedsLifetime . snd) 

enumNeedsLifetime :: VerusName -> [(VerusName, Maybe VerusTy)] -> Bool
enumNeedsLifetime name cases = 
    let checkCase t = case t of 
            Just t' -> tyNeedsLifetime t'
            Nothing -> False 
        in
    any (checkCase . snd) cases

extraLt :: Doc ann -> VerusTy -> Doc ann
extraLt lt (RTStruct name fields) = if structNeedsLifetime name fields then lt else pretty ""
extraLt lt (RTEnum name cases) = if enumNeedsLifetime name cases then lt else pretty ""
extraLt _ _ = pretty ""

liftLifetime a (RTOwlBuf _) = RTOwlBuf (Lifetime a)
liftLifetime _ ty = ty

mkNestPattern :: [Doc ann] -> Doc ann
mkNestPattern l = 
        case l of
            [] -> pretty ""
            [x] -> x
            x:y:tl -> foldl (\acc v -> parens (acc <+> pretty "," <+> v)) (parens (x <> pretty "," <+> y)) tl   

genVerusStruct :: CStruct (Maybe ConstUsize, VerusTy) -> EM (Doc ann, Doc ann)
genVerusStruct (CStruct name fieldsFV isVest) = do
    debugLog $ "genVerusStruct: " ++ name
    let fields = map (\(fname, (formatty, fty)) -> (fname, fty)) fieldsFV
    -- Lift all member fields to have the lifetime annotation of the whole struct
    let needsLifetime = any (tyNeedsLifetime . snd) fields
    let lifetimeConst = "a"
    let lifetimeAnnot = pretty $ if needsLifetime then "<'" ++ lifetimeConst ++ ">" else ""
    let verusFields = fmap (\(fname, fty) -> (fname, execName fname, liftLifetime lifetimeConst fty)) fields
    let verusFieldsFV = fmap (\(fname, (formatty, fty)) -> (fname, execName fname, formatty, liftLifetime lifetimeConst fty)) fieldsFV
    let verusFields' = fmap (\(_, ename, fty) -> (ename, fty)) verusFields
    let verusName = execName name
    let specname = specName name
    let structTy = if needsLifetime then RTWithLifetime (RTStruct verusName verusFields') (Lifetime lifetimeConst) else RTStruct verusName verusFields'
    let structFields = vsep . punctuate comma $ fmap (\(_, fname, fty) -> [di|pub #{fname}: #{pretty fty}#{extraLt lifetimeAnnot fty}|]) verusFields
    let structDef = [__di|
    pub struct #{verusName}#{lifetimeAnnot} {
        #{structFields}
    } 
    |]
    let emptyLifetimeAnnot = pretty $ if needsLifetime then "<'_>" else ""
    vestFormat <- if isVest then genVestFormat verusName verusFieldsFV else return [di||]
    constructorShortcut <- genConstructorShortcut verusName verusFields lifetimeAnnot
    allLensValid <- genAllLensValid verusName verusFields emptyLifetimeAnnot
    viewImpl <- genViewImpl verusName specname verusFields emptyLifetimeAnnot
    parsleyWrappers <- if isVest then genParsleyWrappers verusName specname structTy verusFields lifetimeConst else return [di||]
    return $ (vsep [structDef, constructorShortcut, allLensValid, viewImpl, parsleyWrappers], vestFormat)
    where 

        genVestFormat name layoutFields = do
            let genField (_, f, format, l) = do 
                    layout <- vestLayoutOf' f format l
                    return [di|    #{layout},|]
            fields <- mapM genField layoutFields
            return [__di|
            #{name} = {
            #{vsep fields}
            }
            |]

        genConstructorShortcut :: VerusName -> [(String, VerusName, VerusTy)] -> Doc ann -> EM (Doc ann)
        genConstructorShortcut verusName fields lAnnot = do
            let body = vsep . punctuate comma . fmap (\(_, ename, _) -> [di|#{ename}: arg_#{ename}|]) $ fields
            let args = hsep . punctuate comma . fmap (\(_, ename, fty) -> [di|arg_#{ename}: #{pretty fty}#{extraLt lAnnot fty}|]) $ fields
            let reqs = vsep . punctuate comma . mapMaybe (
                        \(_, ename, fty) -> case fty of
                            RTOwlBuf _ -> Just [di|arg_#{ename}.len_valid()|]
                            _ -> Nothing
                    ) $ fields
            let fieldEnss = map (\(_, ename, _) -> [di|res.#{ename}.dview() == arg_#{ename}.dview()|]) fields
            let enss = vsep . punctuate comma $ [di|res.len_valid()|] : fieldEnss
            return [__di|
            // Allows us to use function call syntax to construct members of struct types, a la Owl,
            // so we don't have to special-case struct constructors in the compiler
            \#[inline]
            pub fn #{verusName}#{lAnnot}(#{args}) -> (res: #{verusName}#{lAnnot})
                requires #{reqs}
                ensures  #{enss}
            {
                #{verusName} { #{body} }
            }
            |]

        genAllLensValid :: VerusName -> [(String, VerusName, VerusTy)] -> Doc ann -> EM (Doc ann)
        genAllLensValid verusName fields lAnnot = do
            let fieldsValids = mapMaybe (\(_,fname, fty) -> 
                        case fty of 
                            RTWithLifetime (RTStruct _ _) _ -> Just [di|self.#{fname}.len_valid()|]
                            RTWithLifetime (RTEnum _ _) _ -> Just [di|self.#{fname}.len_valid()|]
                            RTOwlBuf _ -> Just [di|self.#{fname}.len_valid()|]
                            _ -> Nothing
                    ) fields
            let body = if null fieldsValids then [di|true|] else hsep . punctuate [di|&&|] $ fieldsValids
            return [__di|
            impl #{verusName}#{lAnnot} {
                pub open spec fn len_valid(&self) -> bool {
                    #{body}
                }
            }
            |]

        genViewImpl :: VerusName -> String -> [(String, VerusName, VerusTy)] -> Doc ann -> EM (Doc ann)
        genViewImpl verusName specname fields lAnnot = do
            let body = vsep . punctuate [di|,|] . fmap (\(fname, ename, _) -> [di|#{specName fname}: self.#{ename}.dview()|]) $ fields
            return [__di|
            impl DView for #{verusName}#{lAnnot} {
                type V = #{specname};
                open spec fn dview(&self) -> #{specname} {
                    #{specname} { 
                        #{body}
                    }
                }
            }
            |]
        
        genParsleyWrappers :: VerusName -> String -> VerusTy -> [(String, VerusName, VerusTy)] -> String -> EM (Doc ann)
        genParsleyWrappers verusName specname structTy fields lifetimeConst = do
            let specParse = [di|parse_#{specname}|] 
            let execParse = [di|parse_#{verusName}|]
            let tupPatFields = mkNestPattern . fmap (\(_, fname, _) -> pretty fname) $ fields
            let mkField fname fty = do
                    mkf <- (pretty fname, u8slice) `cast` fty
                    return [di|#{fname}: #{mkf}|]
            mkStructFields <- hsep . punctuate comma <$> mapM (\(_, fname, fty) -> mkField fname fty) fields
            let parse = [__di|
            pub exec fn #{execParse}<'#{lifetimeConst}>(arg: &'#{lifetimeConst} [u8]) -> (res: Option<#{pretty structTy}>) 
                // requires arg.len_valid()
                ensures
                    res is Some ==> #{specParse}(arg.dview()) is Some,
                    res is None ==> #{specParse}(arg.dview()) is None,
                    res matches Some(x) ==> x.dview() == #{specParse}(arg.dview())->Some_0,
                    res matches Some(x) ==> x.len_valid(),
            {
                reveal(#{specParse});
                let stream = parse_serialize::Stream { data: arg, start: 0 };
                if let Ok((_, _, parsed)) = parse_serialize::#{execParse}(stream) {
                    let #{tupPatFields} = parsed;
                    Some (#{verusName} { #{mkStructFields} })
                } else {
                    None
                }
            }
            |]
            let specSer = [di|serialize_#{specname}|]
            let execSer = [di|serialize_#{verusName}|]
            let specSerInner = [di|serialize_#{specname}_inner|]
            let execSerInner = [di|serialize_#{verusName}_inner|]
            let lens = (map (\(_, fname, _) -> [di|arg.#{fname}.len()|]) fields) ++ [pretty "0"]
            fieldsAsSlices <- mkNestPattern <$> mapM (\(_, fname, fty) -> (pretty ("arg." ++ fname), fty) `cast` u8slice) fields
            let ser = [__di|
            \#[verifier(external_body)] // to allow `as_mut_slice` call, TODO fix
            pub exec fn #{execSerInner}(arg: &#{verusName}) -> (res: Option<Vec<u8>>)
                requires arg.len_valid(),
                ensures
                    res is Some ==> #{specSerInner}(arg.dview()) is Some,
                    res is None ==> #{specSerInner}(arg.dview()) is None,
                    res matches Some(x) ==> x.dview() == #{specSerInner}(arg.dview())->Some_0,
            {
                reveal(#{specSerInner});
                if no_usize_overflows![ #{(hsep . punctuate comma) lens} ] {
                    let mut obuf = vec_u8_of_len(#{(hsep . punctuate (pretty "+")) lens});
                    let ser_result = parse_serialize::#{execSer}(obuf.as_mut_slice(), 0, (#{fieldsAsSlices}));
                    if let Ok((_new_start, num_written)) = ser_result {
                        vec_truncate(&mut obuf, num_written);
                        Some(obuf)
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            pub exec fn #{execSer}(arg: &#{verusName}) -> (res: Vec<u8>)
                requires arg.len_valid(),
                ensures  res.dview() == #{specSer}(arg.dview())
            {
                reveal(#{specSer});
                let res = #{execSerInner}(arg);
                assume(res is Some);
                res.unwrap()
            }
            |]
            return $ vsep [parse, ser]


genVerusEnum :: CEnum (Maybe ConstUsize, VerusTy) -> EM (Doc ann, Doc ann)
genVerusEnum (CEnum name casesFV isVest) = do
    debugLog $ "genVerusEnum: " ++ name
    let cases = M.mapWithKey (\fname opt -> case opt of Just (_, rty) -> Just rty; Nothing -> Nothing) casesFV
    -- Lift all member fields to have the lifetime annotation of the whole struct
    let needsLifetime = any (\t -> case t of Just (RTOwlBuf _) -> True; Just (RTWithLifetime _ _) -> True; _ -> False) . map snd . M.assocs $ cases
    let lifetimeConst = "a"
    let lifetimeAnnot = pretty $ if needsLifetime then "<'" ++ lifetimeConst ++ ">" else ""
    let verusCases = M.mapWithKey (\fname fty -> (execName fname, liftLifetime lifetimeConst fty)) cases
    let verusName = execName name
    let specname = specName name
    let enumTy = if needsLifetime then RTWithLifetime (RTEnum verusName (M.elems verusCases)) (Lifetime lifetimeConst) else RTEnum verusName (M.elems verusCases)
    let extraLt' fty = case fty of Just fty' -> extraLt lifetimeAnnot fty'; Nothing -> pretty ""
    let enumCases = vsep . punctuate comma . fmap (\(_, (fname, fty)) -> [di|#{fname}(#{pretty fty}#{extraLt' fty})|]) . M.assocs $ verusCases
    let enumDef = [__di|
    pub enum #{verusName}#{lifetimeAnnot} {
        #{enumCases}
    }
    use crate::#{verusName}::*;
    |]
    let emptyLifetimeAnnot = pretty $ if needsLifetime then "<'_>" else ""
    vestFormat <- genVestFormat verusName casesFV
    allLensValid <- genAllLensValid verusName verusCases emptyLifetimeAnnot
    viewImpl <- genViewImpl verusName specname verusCases emptyLifetimeAnnot
    -- parsleyWrappers <- genParsleyWrappers verusName specname enumTy verusCases lifetimeConst
    return $ (vsep [enumDef, allLensValid, viewImpl], vestFormat)
    where 
        liftLifetime a (Just (RTOwlBuf _)) = Just $ RTOwlBuf (Lifetime a)
        liftLifetime _ ty = ty

        genVestFormat name layoutCases = do
            debugLog $ "No vest format for enum: " ++ name
            return [__di||]
            -- let genField (_, (f, l)) = do 
            --         layout <- vestLayoutOf f l
            --         return [di|    #{layout},|]
            -- fields <- mapM genField layoutCases
            -- return [__di|
            -- #{name} = {
            -- #{vsep fields}
            -- }
            -- |]


        genAllLensValid :: VerusName -> M.Map String (VerusName, Maybe VerusTy) -> Doc ann -> EM (Doc ann)
        genAllLensValid verusName cases lAnnot = do
            let casesValids = M.map (\(fname, fty) -> 
                        case fty of 
                            Just (RTWithLifetime (RTStruct _ _) _) -> [di|#{fname}(x) => x.len_valid()|]
                            Just (RTWithLifetime (RTEnum _ _) _) -> [di|#{fname}(x) => x.len_valid()|]
                            Just (RTOwlBuf _) -> [di|#{fname}(x) => x.len_valid()|]
                            Just _ -> [di|#{fname}(_) => true|]
                            Nothing -> [di|#{fname}() => true|]
                    ) cases
            let body = vsep . punctuate comma $ M.elems casesValids
            return [__di|
            impl #{verusName}#{lAnnot} {
                pub open spec fn len_valid(&self) -> bool {
                    match self {
                        #{body}
                    }
                }
            }
            |]

        viewCase specname fname (ename, Just fty) = [di|#{ename}(v) => #{specname}::#{specName fname}(v.dview())|]
        viewCase specname fname (ename, Nothing) = [di|#{ename}() => #{specname}::#{specName fname}()|]

        genViewImpl :: VerusName -> String -> M.Map String (VerusName, Maybe VerusTy) -> Doc ann -> EM (Doc ann)
        genViewImpl verusName specname cases lAnnot = do
            let body = vsep . punctuate [di|,|] . M.elems . M.mapWithKey (viewCase specname) $ cases
            return [__di|
            impl DView for #{verusName}#{lAnnot} {
                type V = #{specname};
                open spec fn dview(&self) -> #{specname} {
                    match self { 
                        #{body}
                    }
                }
            }
            |]
        
        -- genParsleyWrappers :: VerusName -> String -> VerusTy -> [(String, VerusName, VerusTy)] -> String -> EM (Doc ann)
        -- genParsleyWrappers verusName specname structTy fields lifetimeConst = do
        --     let specParse = [di|parse_#{specname}|] 
        --     let execParse = [di|parse_#{verusName}|]
        --     let tupPatFields = tupled . fmap (\(_, fname, _) -> pretty fname) $ fields
        --     let mkField fname fty = do
        --             mkf <- (pretty fname, u8slice) `cast` fty
        --             return [di|#{fname}: #{mkf}|]
        --     mkStructFields <- tupled <$> mapM (\(_, fname, fty) -> mkField fname fty) fields
        --     let parse = [__di|
        --     pub exec fn #{execParse}<'#{lifetimeConst}>(arg: &'#{lifetimeConst} [u8]) -> (res: Option<#{pretty structTy}>) 
        --         // requires arg.len_valid()
        --         ensures
        --             res is Some ==> #{specParse}(arg.dview()) is Some,
        --             res is None ==> #{specParse}(arg.dview()) is None,
        --             res matches Some(x) ==> x.dview() == #{specParse}(arg.dview())->Some_0,
        --             res matches Some(x) ==> x.len_valid(),
        --     {
        --         reveal(#{specParse});
        --         let stream = parse_serialize::Stream { data: arg, start: 0 };
        --         if let Ok((_, _, parsed)) = parse_serialize::parse_owl_t(stream) {
        --             let #{tupPatFields} = parsed;
        --             Some (#{verusName} { #{mkStructFields} })
        --         } else {
        --             None
        --         }
        --     }
        --     |]
        --     let specSer = [di|serialize_#{specname}|]
        --     let execSer = [di|serialize_#{verusName}|]
        --     let specSerInner = [di|serialize_#{specname}_inner|]
        --     let execSerInner = [di|serialize_#{verusName}_inner|]
        --     let lens = map (\(_, fname, _) -> [di|arg.#{fname}.len()|]) fields
        --     fieldsAsSlices <- tupled <$> mapM (\(_, fname, fty) -> (pretty fname, fty) `cast` u8slice) fields
        --     let ser = [__di|
        --     \#[verifier(external_body)] // to allow `as_mut_slice` call, TODO fix
        --     pub exec fn #{execSerInner}(arg: &#{verusName}) -> (res: Option<Vec<u8>>)
        --         requires arg.len_valid(),
        --         ensures
        --             res is Some ==> #{specSerInner}(arg.dview()) is Some,
        --             res is None ==> #{specSerInner}(arg.dview()) is None,
        --             res matches Some(x) ==> x.dview() == #{specSerInner}(arg.dview())->Some_0,
        --     {
        --         reveal(#{specSerInner});
        --         if no_usize_overflows![ #{punctuate comma lens} ] {
        --             let mut obuf = vec_u8_of_len(#{punctuate (pretty "+") lens});
        --             let ser_result = parse_serialize::serialize_owl_t(obuf.as_mut_slice(), 0, (#{fieldsAsSlices}));
        --             if let OK((_new_start, num_written)) = ser_result {
        --                 vec_truncate(&mut obuf, num_written);
        --                 Some(obuf)
        --             } else {
        --                 None
        --             }
        --         } else {
        --             None
        --         }
        --     }
        --     pub exec fn #{execSer}(arg: &#{verusName}) -> (res: Vec<u8>)
        --         requires arg.len_valid(),
        --         ensures  res.dview() == #{specSer}(arg.dview())
        --     {
        --         reveal(#{specSer});
        --         let res = #{execSerInner}(arg);
        --         assume(res is Some);
        --         res.unwrap();
        --     }
        --     |]
        --     return $ vsep [parse, ser]


genVerusTyDef :: CTyDef (Maybe ConstUsize, VerusTy) -> EM (Doc ann, Doc ann)
genVerusTyDef (CStructDef s) = genVerusStruct s
genVerusTyDef (CEnumDef e) = genVerusEnum e


genVerusTyDefs :: [(String, CTyDef (Maybe ConstUsize, VerusTy))] -> EM (Doc ann, Doc ann)
genVerusTyDefs tydefs = do
    debugLog "genVerusTyDefs"
    (tyDefs, vestDefs) <- unzip <$> mapM (genVerusTyDef . snd) tydefs
    return (vsep tyDefs, vsep vestDefs)


-----------------------------------------------------------------------------
-- Utility functions

-- castType v t1 t2 v returns an expression of type t2 whose contents are v, which is of type t1
cast :: (Doc ann, VerusTy) -> VerusTy -> EM (Doc ann)
cast (v, t1) t2 | t2 == RTRef RShared t1 =
    return [di|&#{v}|]
cast (v, t1) t2 | t2 == RTRef RMut t1 =
    return [di|&mut #{v}|]    
cast (v, RTRef RMut t1) (RTRef RShared t2) | t1 == t2 =
    return [di|&#{v}|]
cast (v, RTVec t1) (RTRef b (RTSlice t2)) | t1 == t2 =
    return [di|&#{v}.as_slice()|]
cast (v, RTArray RTU8 _) (RTRef RShared (RTSlice RTU8)) =
    return [di|&#{v}.as_slice()|]
cast (v, RTRef _ (RTSlice RTU8)) (RTArray RTU8 _) =
    return [di|#{v}.try_into()|]
cast (v, RTRef _ (RTSlice RTU8)) (RTOwlBuf _) =
    return [di|OwlBuf::from_slice(&#{v})|]
cast (v, RTVec RTU8) (RTOwlBuf _) =
    return [di|OwlBuf::from_vec(#{v})|]
cast (v, RTArray RTU8 _) (RTOwlBuf _) =
    return [di|OwlBuf::from_slice(&#{v})|]
cast (v, RTOwlBuf _) (RTRef _ (RTSlice RTU8)) =
    return [di|#{v}.as_slice()|]
cast (v, RTOption (RTVec RTU8)) (RTOption (RTOwlBuf _)) = 
    return [di|OwlBuf::from_vec_option(#{v})|]
cast (v, RTStruct t fs) (RTVec RTU8) = 
    return [di|serialize_#{t}(&#{v})|]
cast (v, RTStruct t fs) (RTRef RShared (RTSlice RTU8)) = do
    c1 <- cast (v, RTStruct t fs) vecU8
    cast (c1, vecU8) u8slice
cast (v, RTStruct t fs) (RTOwlBuf l) = do
    c1 <- cast (v, RTStruct t fs) vecU8
    cast (c1, vecU8) (RTOwlBuf l)
cast (v, RTEnum t cs) (RTVec RTU8) = 
    return [di|serialize_#{t}(&#{v})|]
cast (v, RTEnum t cs) (RTRef RShared (RTSlice RTU8)) = do
    c1 <- cast (v, RTEnum t cs) vecU8
    cast (c1, vecU8) u8slice
cast (v, RTEnum t cs) (RTOwlBuf l) = do
    c1 <- cast (v, RTEnum t cs) vecU8
    cast (c1, vecU8) (RTOwlBuf l)
-- Special case: the `cast` in the compiler approximately corresponds to where we need to call OwlBuf::another_ref
cast (v, RTOwlBuf _) (RTOwlBuf _) =
    return [di|OwlBuf::another_ref(&#{v})|]
cast (v, t1) t2 | t1 == t2 = return v
cast (v, t1) t2 = throwError $ CantCastType (show v) (show . pretty $ t1) (show . pretty $ t2)

u8slice :: VerusTy
u8slice = RTRef RShared (RTSlice RTU8)

vecU8 :: VerusTy
vecU8 = RTVec RTU8



snOfEn n = if "owl_" `isPrefixOf` n then "owlSpec_" ++ drop 4 n else n

specTyOfExecTySerialized :: VerusTy -> VerusTy
specTyOfExecTySerialized (RTVec t) = RTSeq (specTyOfExecTySerialized t)
specTyOfExecTySerialized (RTOwlBuf _) = RTSeq RTU8
specTyOfExecTySerialized (RTRef _ (RTSlice t)) = RTSeq (specTyOfExecTySerialized t)
specTyOfExecTySerialized (RTArray t _) = RTSeq (specTyOfExecTySerialized t)
specTyOfExecTySerialized (RTOption t) = RTOption (specTyOfExecTySerialized t)
specTyOfExecTySerialized (RTTuple ts) = RTTuple (fmap specTyOfExecTySerialized ts)
specTyOfExecTySerialized (RTStruct n fs) = RTStruct (snOfEn n) (fmap (\(f, t) -> (f, specTyOfExecTySerialized t)) fs)
specTyOfExecTySerialized (RTEnum n cs) = RTEnum (snOfEn n) (fmap (\(c, mt) -> (c, fmap specTyOfExecTySerialized mt)) cs)
specTyOfExecTySerialized t = t -- TODO: not true in general
        

viewVar :: VerusName -> VerusTy -> EM (Doc ann)
viewVar vname RTUnit = return [di|()|]
viewVar vname (RTNamed _) = return [di|#{vname}.dview()|]
viewVar vname (RTStruct _ _) = return [di|#{vname}.dview()|]
viewVar vname (RTEnum _ _) = return [di|#{vname}.dview()|]
viewVar vname (RTOption (RTNamed _)) = return [di|option_as_seq(dview_option(#{vname}))|]
viewVar vname (RTOption _) = return [di|dview_option(#{vname})|]
viewVar vname (RTRef _ (RTSlice RTU8)) = return [di|#{vname}.dview()|]
viewVar vname (RTVec RTU8) = return [di|#{vname}.dview()|]
viewVar vname (RTArray RTU8 _) = return [di|#{vname}.dview()|]
viewVar vname (RTOwlBuf _) = return [di|#{vname}.dview()|]
viewVar vname RTBool = return [di|#{vname}|]
viewVar vname RTUsize = return [di|#{vname}|]
viewVar vname (RTWithLifetime t _) = viewVar vname t
viewVar vname ty = throwError $ ErrSomethingFailed $ "TODO: viewVar: " ++ vname ++ ": " ++ show ty