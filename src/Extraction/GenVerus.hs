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
import CmdArgs
import Prettyprinter.Interpolate

type EM = ExtractionMonad VerusTy

{- 
To avoid issues with "lifetime does not live long enough", we sometimes need to have inner subexpressions evaluated at the
"top level" of the function, e.g.:
```
let x = { 
    let arr: [u8; 8] = owl_counter_as_bytes(&mut_state.ctr_x);
    OwlBuf::from_slice(&arr)
};
```
This doesn't work since `arr` is dropped at the end of the inner block. Instead, we need to do:
```
let arr: [u8; 8] = owl_counter_as_bytes(&mut_state.ctr_x);
let x = OwlBuf::from_slice(&arr);
```
The GenRustExpr structure allows us to do the `cast` operation at the top level, if necessary
-}
data GenRustExpr ann = GenRustExpr {
    -- The generated type for the expression
    _eTy :: VerusTy,
    -- The Rust code for evaluating the expression without the cast applied
    _code :: Doc ann
}
makeLenses ''GenRustExpr


genVerusUserFunc :: CUserFunc VerusTy -> EM (Doc ann)
genVerusUserFunc (CUserFunc specName pubName secName pubBody secBody) = do
    secUF <- mkUserFuncDef specName (execName secName) secBody
    pubUF <- mkUserFuncDef specName (execName pubName) pubBody
    return $ vsep [secUF, pubUF]
    where
        mkUserFuncDef specname execname b = do
            (args, (retTy, body)) <- unbindCDepBind b
            let lifetimeConst = "a"
            let argdefs = hsep . punctuate comma $ fmap (\(n, _, t) -> [di|#{execName . show $ n}: #{pretty (liftLifetime (Lifetime lifetimeConst) t)}|]) args
            let viewArgs = hsep . punctuate comma $ fmap (\(n, _, t) -> [di|#{execName . show $ n}.view()|]) args
            body' <- genVerusCAExpr body
            body'' <- castGRE body' retTy
            let needsLifetime = tyNeedsLifetime retTy
            let lifetimeAnnot = pretty $ if needsLifetime then "<'" ++ lifetimeConst ++ ">" else ""
            let retTy' = liftLifetime (Lifetime lifetimeConst) retTy
            let retval = [di|res: #{pretty retTy'}|]
            return [__di|
            pub fn #{execname}#{lifetimeAnnot}(#{argdefs}) -> (#{retval})
                ensures
                    res.view() == #{specname}(#{viewArgs}),
            {
                reveal(#{specname});
                let res = { 
                    #{body''} 
                };
                assert(res.view() == #{specname}(#{viewArgs}));
                res
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
    pub const fn #{lname}_addr() -> (a: &'static str) 
        ensures endpoint_of_addr(a.view()) == Endpoint::#{locNameOf lname}
    {
        "127.0.0.1:#{pretty ipport}"
    }
    |]
    let locNameAddrs :: [(LocalityName, Int)] = zip lnames $ [9000 + x | x <- [1..]]
    let locAddrDefs = map mkLocAddr locNameAddrs
    return $ vsep $ locEnum : endpointOfAddr : locAddrDefs


genVerusLocality :: [VNameData] -> (LocalityName, VerusLocalityData) -> EM (Doc ann)
genVerusLocality pubkeys (lname, ldata) = do
    let stateName = pretty $ "state_" ++ lname
    let cfgName = pretty $ "cfg_" ++ lname
    let lifetimeConst = lname
    let locNeedsLifetime = any secrecyNeedsLifetime (ldata ^. localNames ++ ldata ^. sharedNames ++ pubkeys)
    let maybeLt = if locNeedsLifetime then Just (Lifetime lifetimeConst) else Nothing
    let lifetimeAnnot = pretty $ if locNeedsLifetime then "<'" ++ lifetimeConst ++ ">" else ""
    let emptyLifetimeAnnot = pretty $ if locNeedsLifetime then "<'_>" else ""
    let (localNameDecls, localNameInits) = unzip . map (genVerusName maybeLt False) $ ldata ^. localNames
    let (sharedNameDecls, sharedNameInits) = unzip . map (genVerusName maybeLt True) $ ldata ^. sharedNames
    let (pkDecls, pkInits) = unzip . map (genVerusPk maybeLt True) $ pubkeys
    let (ctrDecls, ctrInits) = unzip . map genVerusCtr $ ldata ^. counters
    execFns <- withCurNameEnv (ldata ^. localNames ++ ldata ^. sharedNames) pubkeys $ mapM (genVerusDef lname) . catMaybes $ ldata ^. defs
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
    pub struct #{cfgName}#{lifetimeAnnot} {
        #{vsep . punctuate comma $ localNameDecls ++ sharedNameDecls ++ pkDecls}
    }
    impl #{cfgName}#{emptyLifetimeAnnot} {
        #{vsep . punctuate (line <> line) $ execFns}
    }
    |]
    where
        secrecyNeedsLifetime (_,_,_,BufSecret) = True
        secrecyNeedsLifetime (_,_,_,BufPublic) = True 


-- ctr decl, ctr init
genVerusCtr :: VerusName -> (Doc ann, Doc ann)
genVerusCtr counterName =
    let counterName' = execName counterName in
    let ctrDecl = [di|pub #{counterName'} : usize|] in
    let ctrInit = [di|#{counterName'} : 0|] in
    (ctrDecl, ctrInit)

withCurNameEnv :: [VNameData] -> [VNameData] -> EM a -> EM a
withCurNameEnv vnames pubkeys m = do
    let vnameMap = M.fromList . map (\(n,l,i,s) -> (n, (n,l,i,s))) $ vnames
    let pkMap = M.fromList . map (\(n,l,i,s) -> (n, (n,l,i,s))) $ pubkeys
    genVerusNameEnv .= vnameMap
    genVerusPkEnv .= pkMap
    res <- m
    genVerusNameEnv .= M.empty
    genVerusPkEnv .= M.empty
    return res

buftyOfSecrecy :: BufSecrecy -> VerusTy
buftyOfSecrecy BufSecret = secBuf
buftyOfSecrecy BufPublic = owlBuf

lookupNameBufTy :: String -> EM VerusTy
lookupNameBufTy n = do
    vnameMap <- use genVerusNameEnv
    case vnameMap M.!? n of
        Just (_, _, _, secrecy) -> return $ buftyOfSecrecy secrecy
        Nothing -> throwError $ UndefinedSymbol n

lookupPkBufTy :: String -> EM VerusTy
lookupPkBufTy n = do
    pkMap <- use genVerusPkEnv
    case pkMap M.!? n of
        Just (_, _, _, secrecy) -> return $ buftyOfSecrecy secrecy
        Nothing -> throwError $ UndefinedSymbol n

-- name decl, name initializer
genVerusName :: Maybe Lifetime -> Bool -> VNameData -> (Doc ann, Doc ann)
genVerusName maybeLt fromConfig (vname, vsize, _, secrecy) =
    -- debugLog $ "genVerusName: " ++ vname
    let execname = execName vname in
    let bufty = buftyOfSecrecy secrecy in
    let bufty' = case maybeLt of
            Just lt -> liftLifetime lt bufty
            Nothing -> bufty in
    let nameDecl = [di|pub #{execname} : #{pretty bufty'}|] in
    let nameInitBody =
            if fromConfig then [di|config.#{execname}|]
            else [di|owl_util::gen_rand_bytes(#{pretty vsize})|] in
    let nameInit = [di|#{execname} : (#{nameInitBody})|] in
    (nameDecl, nameInit)

-- name decl, name initializer
genVerusPk :: Maybe Lifetime -> Bool -> VNameData -> (Doc ann, Doc ann)
genVerusPk maybeLt fromConfig (vname, vsize, _, secrecy) =
    -- debugLog $ "genVerusName: " ++ vname
    let execname = "pk_" ++ execName vname in
    let bufty = buftyOfSecrecy secrecy in
    let bufty' = case maybeLt of
            Just lt -> liftLifetime lt bufty
            Nothing -> bufty in
    let nameDecl = [di|pub #{execname} : #{pretty bufty'}|] in
    let nameInitBody =
            if fromConfig then [di|config.#{execname}|]
            else [di|owl_util::gen_rand_bytes(#{pretty vsize})|] in
    let nameInit = [di|#{execname} : (#{nameInitBody})|] in
    (nameDecl, nameInit)

-- These should be kept in one-to-one correspondence with execlib.rs
builtins :: M.Map String (String, [VerusTy], VerusTy)
builtins = M.mapWithKey addExecName builtins' `M.union` diffNameBuiltins where
    addExecName n (args, rty) = (execName n, args, rty)
    builtins' = M.fromList [
          ("enc", ([secBuf, secBuf, secBuf], vecU8))
        , ("dec", ([secBuf, owlBuf, RTVerusTracked RTDeclassifyTok], RTOption secBuf))
        , ("sign", ([secBuf, owlBuf], vecU8))
        , ("vrfy", ([owlBuf, secBuf, owlBuf, RTVerusTracked RTDeclassifyTok], RTOption secBuf))
        , ("dhpk", ([secBuf], vecU8))
        , ("dh_combine", ([secBuf, secBuf], secBuf))
        , ("mac", ([secBuf, owlBuf], vecU8))
        , ("mac_vrfy", ([secBuf, secBuf, owlBuf, RTVerusTracked RTDeclassifyTok], RTOption secBuf))
        , ("pkenc", ([owlBuf, secBuf], vecU8))
        , ("pkdec", ([secBuf, owlBuf, RTVerusTracked RTDeclassifyTok], RTOption secBuf))
        , ("enc_st_aead", ([secBuf, secBuf, secBuf, secBuf], vecU8))
        , ("enc_st_aead_builder", ([secBuf, secBuf, secBuf, secBuf], RTStAeadBuilder))
        , ("dec_st_aead", ([secBuf, owlBuf, secBuf, secBuf, RTVerusTracked RTDeclassifyTok], RTOption secBuf))
        , ("is_group_elem", ([secBuf], RTBool))
        , ("crh", ([u8slice], vecU8))
        , ("secret_crh", ([secBuf], secBuf))
        , ("concat", ([u8slice, u8slice], vecU8))
        , ("secret_concat", ([secBuf, secBuf], secBuf))
        , ("xor", ([u8slice, u8slice], vecU8))
        , ("secret_xor", ([secBuf, secBuf], secBuf))
        -- bytes_as_counter and counter_as_bytes are handled specially 
        ]
    diffNameBuiltins = M.fromList [
          ("kdf", ("owl_extract_expand_to_len", [RTUsize, secBuf, secBuf, owlBuf], secBuf))
        ]

genVerusCAExpr :: CAExpr VerusTy -> EM (GenRustExpr ann)
genVerusCAExpr ae = do
    case ae ^. tval of
        CAVar s v -> return $ GenRustExpr { _code = pretty $ execName $ show v, _eTy = ae ^. tty }
        CACast ae dstTy -> do
            ae' <- genVerusCAExpr ae
            ae'' <- castGRE ae' dstTy
            return $ GenRustExpr { _code = ae'', _eTy = dstTy }
        CAApp f _ args -> do
            case builtins M.!? f of
                Just (fExecName, argDstTys, rSrcTy) -> do
                    args' <- mapM genVerusCAExpr args
                    args'' <- zipWithM castGRE args' argDstTys
                    let code = [di|#{fExecName}(#{hsep . punctuate comma $ args''})|]
                    return $ GenRustExpr { _code = code, _eTy = rSrcTy }
                Nothing -> do
                    -- Special cases for Owl function calls which aren't regular function calls in Rust
                    case (f, args) of
                        ("true", []) -> return $ GenRustExpr RTBool [di|true|]
                        ("false", []) -> return $ GenRustExpr RTBool [di|false|]
                        ("Some", [x]) -> do
                            x' <- genVerusCAExpr x
                            x'' <- castGRE x' (x ^. tty)
                            return $ GenRustExpr (RTOption (x ^. tty)) [di|Some(#{x''})|]
                        ("None", []) -> return $ GenRustExpr (ae ^. tty) [di|None|]
                        ("length", [x]) -> do
                            x' <- genVerusCAExpr x
                            case x' ^. eTy of
                                RTVec RTU8 -> return $ GenRustExpr RTUsize [di|#{x' ^. code}.len()|]
                                RTRef _ (RTSlice RTU8) -> return $ GenRustExpr RTUsize [di|{ slice_len(#{x' ^. code}) }|]
                                RTOwlBuf _ -> return $ GenRustExpr RTUsize [di|#{x' ^. code}.len()|]
                                -- All lengths are public, so we are allowed to take the len of a SecretBuf
                                RTSecBuf _ -> return $ GenRustExpr RTUsize [di|#{x' ^. code}.len()|]
                                _ -> throwError $ ErrSomethingFailed $ "TODO: length for type: " ++ show (x' ^. eTy)
                        ("andb", [x,y]) -> do
                            x' <- genVerusCAExpr x
                            y' <- genVerusCAExpr y
                            x'' <- castGRE x' RTBool
                            y'' <- castGRE y' RTBool
                            return $ GenRustExpr RTBool [di|#{x''} && #{y''}|]
                        ("andp", [x,y]) -> do
                            -- Propositional `and`, which we just compile to ghost unit
                            return $ GenRustExpr RTVerusGhost [di|owl_ghost_unit()|]
                        ("notb", [x]) -> do
                            x' <- genVerusCAExpr x
                            x'' <- castGRE x' RTBool
                            return $ GenRustExpr RTBool [di|!(#{x''})|]
                        ("eq", [x,y]) -> eqChecker x y
                        ("secret_eq", [x, y, tok]) -> do
                            x' <- genVerusCAExpr x
                            y' <- genVerusCAExpr y
                            tok' <- genVerusCAExpr tok
                            x'' <- castGRE x' (RTRef RShared (RTSecBuf AnyLifetime))
                            y'' <- castGRE y' (RTRef RShared (RTSecBuf AnyLifetime))
                            tok'' <- castGRE tok' (RTVerusTracked RTDeclassifyTok)
                            return $ GenRustExpr RTBool [di|{ SecretBuf::secret_eq(#{x''}, #{y''}, #{tok''}) }|]
                        ("checknonce", [x, y]) -> eqChecker x y
                        ("subrange", [buf, start, end]) -> do
                            buf' <- genVerusCAExpr buf
                            start' <- genVerusCAExpr start
                            end' <- genVerusCAExpr end
                            castStart <- castGRE start' RTUsize
                            castEnd <- castGRE end' RTUsize
                            case buf' ^. eTy of
                                RTOwlBuf _ -> return $ GenRustExpr (ae ^. tty) [di|{ OwlBuf::another_ref(&#{buf' ^. code}).subrange(#{castStart}, #{castEnd}) }|]
                                RTSecBuf _ -> return $ GenRustExpr (ae ^. tty) [di|{ SecretBuf::another_ref(&#{buf' ^. code}).subrange(#{castStart}, #{castEnd}) }|]
                                RTRef _ (RTSlice RTU8) -> return $ GenRustExpr (ae ^. tty) [di|{ slice_subrange(#{buf' ^. code}, #{castStart}, #{castEnd}) }|]
                                t -> throwError $ ErrSomethingFailed $ "TODO: subrange for type: " ++ show t
                        ("buf_declassify", [buf, tok]) -> do
                            buf' <- genVerusCAExpr buf
                            tok' <- genVerusCAExpr tok
                            when (tok' ^. eTy /= RTDeclassifyTok) $
                                throwError $ TypeError $ "got buf_declassify with bad token type " ++ show (owlpretty (tok' ^. eTy))
                            castBuf <- castGRE buf' (RTSecBuf AnyLifetime)
                            castTok <- castGRE tok' (RTVerusTracked RTDeclassifyTok)
                            return $ GenRustExpr (ae ^. tty) [di|{ #{castBuf}.declassify(#{castTok}) }|]
                        (f, [x]) | "?" `isSuffixOf` f -> do
                            -- Special case for enum test functions
                            let f' = init f ++ "_enumtest"
                            x' <- genVerusCAExpr x
                            x'' <- castGRE x' (RTRef RShared (x ^. tty))
                            return $ GenRustExpr (ae ^. tty) [di|#{execName f'}(#{x''})|]
                        _ -> case ae ^. tty of
                                RTStruct n fs | n == execName f -> do
                                    -- Special case for struct constructors
                                    args' <- mapM genVerusCAExpr args
                                    let ftys = map snd fs
                                    args'' <- zipWithM castGRE args' ftys
                                    return $ GenRustExpr (ae ^. tty) [di|#{execName f}(#{hsep . punctuate comma $ args''})|]
                                RTEnum n cs | elem (execName f) (map fst cs) && length args == 1 -> do
                                    -- Special case for enum constructors
                                    let [arg] = args
                                    arg' <- genVerusCAExpr arg
                                    cty <- case lookup (execName f) cs of
                                            Just (Just t) -> return t
                                            _ -> throwError $ ErrSomethingFailed $ "enum constructor case with no type " ++ show (ae^.tty, execName f)
                                    arg'' <- castGRE arg' cty
                                    return $ GenRustExpr (ae ^. tty) [di|#{execName f}(#{arg''})|]
                                _ -> do
                                    args' <- mapM genVerusCAExpr args
                                    args'' <- zipWithM castGRE args' (map (^. tty) args)
                                    return $ GenRustExpr (ae ^. tty) [di|#{execName f}(#{hsep . punctuate comma $ args''})|]
        CAGet n -> do
            let rustN = execName n
            nameTy <- lookupNameBufTy n
            castN <- cast ([di|self.#{rustN}|], nameTy) (ae ^. tty)
            return $ GenRustExpr (ae ^. tty) [di|#{castN}|]
        CAGetEncPK n -> do
            let rustN = execName n
            nameTy <- lookupPkBufTy n
            castN <- cast ([di|self.pk_#{rustN}|], nameTy) (ae ^. tty)
            return $ GenRustExpr (ae ^. tty) [di|#{castN}|]
        CAGetVK n -> do
            let rustN = execName n
            nameTy <- lookupPkBufTy n
            castN <- cast ([di|self.pk_#{rustN}|], nameTy) (ae ^. tty)
            return $ GenRustExpr (ae ^. tty) [di|#{castN}|]
        CAInt fl -> return  $ GenRustExpr (ae ^. tty) $ pretty $ lowerFLen fl
        CACounter ctrname -> do
            let rustCtr = execName ctrname
            castCtr <- cast ([di|mut_state.#{rustCtr}|], RTUsize) (ae ^. tty)
            return $ GenRustExpr (ae ^. tty) [di|#{castCtr}|]
        CAHexConst s -> do
            s' <- hexStringToByteList s
            castX <- ([di|x|], vecU8) `cast` (ae ^. tty)
            return $ GenRustExpr (ae ^. tty) [di|{ let x = mk_vec_u8![#{s'}]; #{castX} }|]
        CASerializeWith (RTStruct n fs) args -> do
            let ftys = map snd fs
            let printComb arg comb = case comb of
                    PCTail -> return [di|Tail|]
                    PCBytes l -> do
                        l' <- concreteLength $ lowerFLen l
                        return [di|Variable(#{l'})|]
                    PCConstBytes l s -> return [di|OwlConstBytes::<#{l}>(#{s})|]
                    PCBuilder -> return [di|BuilderCombinator(#{arg})|]
            let mkCombArg ((arg, comb), fty) = do
                    arg' <- genVerusCAExpr arg
                    let fty' = if comb == PCBuilder then RTUnit else fty
                    arg'' <- if comb == PCBuilder then return $ arg' ^. code else castGRE arg' fty'
                    argForSer <- if comb == PCBuilder || fty' == RTUnit then return [di|()|] else (arg'', fty') `cast` owlBuf
                    viewArg <- if fty == RTUnit then return [di|()|] else do
                        return [di|#{arg' ^. code}.view()|]
                    comb' <- printComb arg'' comb
                    len <- case comb of
                        PCBytes l -> do
                            return [di|#{arg''}.len()|]
                        PCConstBytes l _ -> return [di|#{l}|]
                        PCTail -> return [di|#{arg''}.len()|]
                        PCBuilder -> return [di|#{arg''}.length()|]
                    return (comb', ((argForSer, viewArg), len))
            let acfs = zip args ftys
            (combs, arglens) <- unzip <$> mapM mkCombArg acfs
            let (argsViews, lens) = unzip arglens
            let (args, viewArgs) = unzip argsViews
            let execcomb = mkNestPattern combs
            let execargs = mkNestPattern args
            let specSerInner = [di|serialize_#{specNameOfExecName n}_inner|]
            let specSer = [di|serialize_#{specNameOfExecName n}|]
            let reveals = [di|reveal(#{specSerInner}); reveal(#{specSer});|]
            let specMkStruct = [di|#{unExecName n}(#{hsep . punctuate comma $ viewArgs})|]
            let ser_body = [__di|    
                if no_usize_overflows![ #{(hsep . punctuate comma) lens} ] {
                    let mut ser_buf = vec_u8_of_len(#{(hsep . punctuate (pretty "+")) lens});
                    let exec_comb = #{execcomb};
                    #{reveals}
                    let ser_result = exec_comb.serialize(#{execargs}, &mut ser_buf, 0);
                    if let Ok((num_written)) = ser_result {
                        assert(ser_buf.view() == #{specSer}(#{specMkStruct}));
                        ser_buf
                    } else {
                        // TODO better error name
                        return Err(OwlError::IntegerOverflow);
                    }
                } else {
                    return Err(OwlError::IntegerOverflow);
                }
            |]
            return $ GenRustExpr vecU8 ser_body
        _ -> throwError $ ErrSomethingFailed $ "TODO: genVerusCAExpr: " ++ show (owlpretty ae)
    where
        eqChecker x y = do
            x' <- genVerusCAExpr x
            y' <- genVerusCAExpr y
            let castXTo = castGRE x'
            let castYTo = castGRE y'
            case (x ^. tty, y ^. tty) of
                (RTVec RTU8, RTVec RTU8) -> do
                    x'' <- castXTo u8slice
                    y'' <- castYTo u8slice
                    return $ GenRustExpr RTBool [di|{ slice_eq(#{x''}, #{y''}) }|]
                (RTRef _ (RTSlice RTU8), RTRef _ (RTSlice RTU8)) -> do
                    x'' <- castXTo u8slice
                    y'' <- castYTo u8slice
                    return $ GenRustExpr RTBool [di|{ slice_eq(#{x''}, #{y''}) }|]
                (RTOwlBuf _, RTOwlBuf _) -> do
                    x'' <- castXTo u8slice
                    y'' <- castYTo u8slice
                    return $ GenRustExpr RTBool [di|{ slice_eq(#{x''}, #{y''}) }|]
                _ -> return $ GenRustExpr RTBool [di|#{x' ^. code} == #{y' ^. code}|] -- might not always work

-- Extra info needed just for `genVerusCExpr`
data GenCExprInfo ann = GenCExprInfo {
    -- True if we are extracting the expression `k` in `let x = e in k`, false if we are extracting `e`
    -- We need to track this since at the end of `k`, Rust requires us to return the itree token as well (see CRet case)
    inK :: Bool,
    -- The spec itree type of the current function, which is needed because Rust type inference cannot infer it,
    -- so we need to add `::<specItreeTy>` to the effect calls
    specItreeTy :: Doc ann,
    curLocality :: LocalityName
} deriving (Show)

needsToplevelCast :: VerusTy -> Bool
needsToplevelCast (RTOwlBuf _)  = True
needsToplevelCast (RTSecBuf _)  = True
needsToplevelCast (RTOption (RTOwlBuf _)) = True
needsToplevelCast (RTOption (RTSecBuf _)) = True
needsToplevelCast (RTStruct _ _) = True
needsToplevelCast (RTEnum _ _) = True
needsToplevelCast _ = False

instance OwlPretty VerusTy where
    owlpretty = pretty

genVerusCExpr :: GenCExprInfo ann -> CExpr VerusTy -> EM (GenRustExpr ann)
genVerusCExpr info expr = do
    -- debugPrint $ "genVerusCExpr: "
    -- debugPrint $ show (owlpretty expr)
    case expr ^. tval of
        CSkip -> return $ GenRustExpr RTUnit [di|()|]
        CRet ae -> do
            ae' <- genVerusCAExpr ae
            if inK info then do
                castRes <- castGRE ae' (expr ^. tty)
                return $ GenRustExpr (expr ^. tty) [di|(#{castRes}, Tracked(itree))|]
            else return ae'
        CInput t xek -> do
            let ((x, ev), k) = unsafeUnbind xek
            let rustX = execName . show $ x
            let rustEv = if show ev == "_" then "_" else execName . show $ ev
            let itreeTy = specItreeTy info
            k' <- genVerusCExpr info k
            castTmp <- ([di|tmp_#{rustX}|], vecU8) `cast` t
            return $ GenRustExpr (k' ^. eTy) [__di|
            let (tmp_#{rustX}, #{rustEv}) = { effects.owl_input::<#{itreeTy}>(Tracked(&mut itree)) };
            let #{rustX} = #{castTmp};
            #{k' ^. code}
            |]
        COutput ae dst -> do
            dst' <- case dst of
                Just (EndpointLocality (Locality lname _)) -> do
                    plname <- flattenPath lname
                    return [di|Some(&#{plname}_addr())|]
                Just (Endpoint ev) -> return [di|Some(&#{execName . show $ ev}.as_str())|]
                Nothing -> return [di|None|]
            let myAddr = [di|&#{curLocality info}_addr()|]
            let itreeTy = specItreeTy info
            let retItree = if inK info then [di|((), Tracked(itree))|] else [di||]
            case ae ^. tval of
                CASerializeWith (RTStruct n fs) args -> do
                    -- Special case for fused serialize-output operation
                    let ftys = map snd fs
                    let printComb arg comb = case comb of
                            PCTail -> return [di|Tail|]
                            PCBytes l -> do
                                l' <- concreteLength $ lowerFLen l
                                return [di|Variable(#{l'})|]
                            PCConstBytes l s -> return [di|OwlConstBytes::<#{l}>(#{s})|]
                            PCBuilder -> return [di|BuilderCombinator(#{arg})|]
                    let printCombTy comb = case comb of
                            PCTail -> [di|Tail|]
                            PCBytes l -> [di|Variable|]
                            PCConstBytes l _ -> [di|OwlConstBytes<#{l}>|]
                            PCBuilder -> [di|BuilderCombinator<OwlStAEADBuilder>|]
                    let mkCombArg ((arg, comb), fty) = do
                            arg' <- genVerusCAExpr arg
                            let fty' = if comb == PCBuilder then RTUnit else fty
                            arg'' <- if comb == PCBuilder then return $ arg' ^. code else castGRE arg' fty'
                            argForSer <- if comb == PCBuilder || fty' == RTUnit then return [di|()|] else (arg'', fty') `cast` owlBuf
                            comb' <- printComb arg'' comb
                            len <- case comb of
                                PCBytes l -> do
                                    return [di|#{arg''}.len()|]
                                PCConstBytes l _ -> return [di|#{l}|]
                                PCTail -> return [di|#{arg''}.len()|]
                                PCBuilder -> return [di|#{arg''}.length()|]
                            return (comb', (argForSer, len))
                    let acfs = zip args ftys
                    (combs, arglens) <- unzip <$> mapM mkCombArg acfs
                    let (verusArgs, lens) = unzip arglens
                    let execcomb = mkNestPattern combs
                    let combTy = mkNestPattern $ map (printCombTy . snd) args
                    let execargs = mkNestPattern verusArgs
                    let specSerInner = [di|serialize_#{specNameOfExecName n}_inner|]
                    let specSer = [di|serialize_#{specNameOfExecName n}|]
                    let reveals = [di|reveal(#{specSerInner}); reveal(#{specSer});|]
                    let serout_body = [__di|    
                        let exec_comb = #{execcomb};
                        #{reveals}
                        effects.owl_output_serialize_fused::<#{itreeTy}, OwlBuf<'_>, #{combTy}>(
                            Tracked(&mut itree),
                            exec_comb,
                            #{execargs}, 
                            #{dst'}, 
                            #{myAddr}
                        );
                        #{retItree}
                    |]
                    return $ GenRustExpr RTUnit serout_body
                _ -> do
                    ae' <- genVerusCAExpr ae
                    aeCast <- ae' `castGRE` u8slice
                    return $ GenRustExpr RTUnit [__di|
                    effects.owl_output::<#{itreeTy}>(Tracked(&mut itree), #{aeCast}, #{dst'}, #{myAddr}); 
                    #{retItree}
                    |]
        CSample fl t xk -> do
            let (x, k) = unsafeUnbind xk
            let rustX = execName . show $ x
            let sz = lowerFLen fl
            k' <- genVerusCExpr info k
            let itreeTy = specItreeTy info
            castTmp <- ([di|tmp_#{rustX}|], RTSecBuf AnyLifetime) `cast` t
            return $ GenRustExpr (k' ^. eTy) [__di|
            let tmp_#{rustX} = effects.owl_sample::<#{itreeTy}>(Tracked(&mut itree), #{pretty sz});
            let #{rustX} = #{castTmp};
            #{k' ^. code}
            |]
        CItreeDeclassify _ xk -> do
            let itreeTy = specItreeTy info
            let (x, k) = unsafeUnbind xk
            let rustX = execName . show $ x
            k' <- genVerusCExpr info k
            return $ GenRustExpr (k' ^. eTy) [__di|
            let tracked #{rustX} = consume_itree_declassify::<#{itreeTy}, Endpoint>(&mut itree);
            #{k' ^. code}
            |]
        CLet e oanf xk -> do
            let (x, k) = unsafeUnbind xk
            let rustX = execName . show $ x
            e' <- genVerusCExpr (info { inK = False }) e
            k' <- genVerusCExpr info k
            let needsItreeLhs = case e of
                    Typed _ (CCall _ _ _) -> True
                    _ -> False
            -- Cast here, if necessary
            if e' ^. eTy /= e ^. tty || needsToplevelCast (e' ^. eTy) then do
                castE' <- ([di|tmp_#{rustX}|], e' ^. eTy) `cast` (e ^. tty)
                let lhs = if needsItreeLhs then [di|(tmp_#{rustX}, Tracked(itree))|] else [di|tmp_#{rustX}|]
                rhs <- case e of
                    -- Special case to prevent "use of moved value" errors
                    Typed _ (CRet (Typed _ (CAVar _ _))) | needsToplevelCast (e' ^. eTy) -> castGRE e' (e' ^. eTy)
                    _ -> return $ e' ^. code
                return $ GenRustExpr (k' ^. eTy) [__di|
                let #{lhs} = { #{rhs} };
                let #{rustX} = #{castE'};
                #{k' ^. code}
                |]
            else do
                let lhs = if needsItreeLhs then [di|(#{rustX}, Tracked(itree))|] else [di|#{rustX}|]
                return $ GenRustExpr (k' ^. eTy) [__di|
                let #{lhs} = { #{e' ^. code} };
                #{k' ^. code}
                |]
        CBlock ebody -> do
            ebody' <- genVerusCExpr info ebody
            when (ebody' ^. eTy /= expr ^. tty) $ throwError $ TypeError $ "block has different type than expected: " ++ show (ebody' ^. eTy) ++ " vs " ++ show (expr ^. tty)
            return $ GenRustExpr (expr ^. tty) [__di|
            { 
                #{ebody' ^. code} 
            }
            |]
        CIf ae e1 e2 -> do
            ae' <- genVerusCAExpr ae
            ae'' <- castGRE ae' RTBool
            e1' <- genVerusCExpr info e1
            e2' <- genVerusCExpr info e2
            when (e1' ^. eTy /= e1 ^. tty) $ throwError $ TypeError $ "if true branch has different type than expected: " ++ show (e1' ^. eTy) ++ " vs " ++ show (e1 ^. tty)
            when (e2' ^. eTy /= e2 ^. tty) $ throwError $ TypeError $ "if false branch has different type than expected: " ++ show (e2' ^. eTy) ++ " vs " ++ show (e2 ^. tty)
            ety <- unifyVerusTysUpToSecrecy (e1' ^. eTy) (e2' ^. eTy)
            e1'' <- if e1' ^. eTy /= ety then castGRE e1' ety else return $ e1' ^. code
            e2'' <- if e2' ^. eTy /= ety then castGRE e2' ety else return $ e2' ^. code
            return $ GenRustExpr ety [di|
            if #{ae''} {
                #{e1''}
            } else {
                #{e2''}
            }
            |]
        CCase ae cases -> do
            ae' <- genVerusCAExpr ae
            ae'' <- castGRE ae' (ae ^. tty)
            (aeTyPrefix, translateCaseName) <- case ae ^. tty of
                RTEnum n _ -> return ([di|#{n}::|], execName)
                RTOption _ -> return ([di|Option::|], id)
                t -> throwError $ UndefinedSymbol $ "attempt to case on type " ++ show t
            let genCase (c, o) = do
                    case o of
                        Left k -> do
                            k' <- genVerusCExpr info k
                            let parens = case ae ^. tty of
                                    RTOption _ -> ""
                                    _ -> "()"
                            return ([di|#{aeTyPrefix}#{translateCaseName c}#{parens} =>|],
                                GenRustExpr (k' ^. eTy) [__di|
                                { 
                                    #{k' ^. code} 
                                }
                                |])
                        Right xtk -> do
                            let (x, (t, k)) = unsafeUnbind xtk
                            let rustX = execName . show $ x
                            -- We include the cast operation below in case we decide during 
                            -- type-lowering to  represent the contained type differently 
                            -- in the enum and in the case body (e.g., if the enum contains 
                            -- an owned Vec but the case body should have an OwlBuf)
                            castTmp <- ([di|tmp_#{rustX}|], t) `cast` t
                            k' <- genVerusCExpr info k
                            return ([di|#{aeTyPrefix}#{translateCaseName c}(tmp_#{rustX}) =>|],
                                GenRustExpr (k' ^. eTy) [__di|
                                {
                                    let #{rustX} = #{castTmp}; 
                                    #{k' ^. code} 
                                }
                                |])
            cases' <- mapM genCase cases
            let casesEtys = map ((^. eTy) . snd) cases'
            stmtEty <- foldM unifyVerusTysUpToSecrecy (head casesEtys) (tail casesEtys)
            let castCases (matchArm, c) = do
                    if c ^. eTy /= stmtEty then do
                        cCast <- castGRE c stmtEty
                        return $ [__di| #{matchArm} #{cCast} |]
                    else return $ [__di| #{matchArm} #{c ^. code} |]
            casesCode' <- mapM castCases cases'
            return $ GenRustExpr stmtEty [__di|
            match #{ae''} {
                #{vsep . punctuate comma $ casesCode'}
            }
            |]
        -- special case: comes from type annotation when matching on an authentic option type
        CParse PFromDatatype ae _ (RTOption t') _ xtsk -> do
            let ([(x,s,t)], k) = unsafeUnbind xtsk
            let xsk' = bind (castName x) k
            genVerusCExpr info $ Typed (expr ^. tty) $ CLet (Typed (ae ^. tty) (CRet ae)) Nothing xsk'
        CParse pkind ae extraArgs t maybeOtw xtsk -> do
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
            ae'' <- castGRE ae' (ae ^. tty)
            extraArgs' <- mapM genVerusCAExpr extraArgs
            extraArgs'' <- zipWithM castGRE extraArgs' (map (\x -> if x^.tty == RTDeclassifyTok then RTVerusTracked RTDeclassifyTok else x^.tty) extraArgs)
            k' <- genVerusCExpr info k
            case (pkind, maybeOtw) of
                (PFromBuf, Just otw) -> do
                    otw' <- genVerusCExpr info otw
                    castParsevalTmp <- ([di|parseval_tmp|], ae ^. tty) `cast` RTOwlBuf (Lifetime "_")
                    return $ GenRustExpr (k' ^. eTy) [__di|
                    let parseval_tmp = #{ae''};
                    if let Some(parseval) = parse_#{dstTyName}(#{castParsevalTmp}, #{(hsep . punctuate comma) extraArgs''}) {
                        #{vsep selectors}
                        #{k' ^. code}
                    } else {
                        #{otw' ^. code}
                    }
                    |]
                (PFromSecBuf, Just otw) -> do
                    otw' <- genVerusCExpr info otw
                    castParsevalTmp <- ([di|parseval_tmp|], ae ^. tty) `cast` RTSecBuf (Lifetime "_")
                    return $ GenRustExpr (k' ^. eTy) [__di|
                    let parseval_tmp = #{ae''};
                    if let Some(parseval) = secret_parse_#{dstTyName}(#{castParsevalTmp}, #{(hsep . punctuate comma) extraArgs''}) {
                        #{vsep selectors}
                        #{k' ^. code}
                    } else {
                        #{otw' ^. code}
                    }
                    |]
                (PFromDatatype, _) -> do
                    when (length extraArgs /= 0) $ throwError $ TypeError "parse from datatype with extra args"
                    return $ GenRustExpr (k' ^. eTy) [__di|
                    let parseval = #{ae''};
                    #{vsep selectors}
                    #{k' ^. code}
                    |]
                _ -> throwError $ TypeError "Tried to parse from buf without an otherwise case!"
        CGetCtr ctrname -> do
            let rustCtr = execName ctrname
            return $ GenRustExpr (RTArray RTU8 (CUsizeConst "COUNTER_SIZE")) [di|owl_counter_as_bytes(&mut_state.#{rustCtr})|]
        CIncCtr ctrname -> do
            let rustCtr = [di|mut_state.#{execName ctrname}|]
            let incrExpr = [__di|
            if #{rustCtr} > usize::MAX - 1 {
                return Err(OwlError::IntegerOverflow);
            };
            #{rustCtr} = #{rustCtr} + 1;
            |]
            return $ GenRustExpr RTUnit incrExpr
        CCall f frty args -> do
            args' <- mapM genVerusCAExpr args
            let callMacro = case expr ^. tty of
                    RTOption _ -> "owl_call_ret_option!"
                    RTUnit -> "owl_call_ret_unit!"
                    _ -> "owl_call!"
            argvars <- mapM (fresh . s2n . (++) "tmp_arg" . show) [1..length args]
            let argzip = zip3 args' (map (^. tty) args) argvars
            let genArg (arg, argty, argvar) = do
                    castArg <- arg `castGRE` argty
                    return [di|let #{argvar} = #{castArg};|]
            genArgVars <- mapM genArg argzip
            let execf = execName f
            let specf = f ++ "_spec"
            viewArgs <- mapM (\(_,argty,argvar) -> viewVar (show argvar) argty) argzip
            let specArgs = [di|*self|] : [di|*mut_state|] : viewArgs
            let specCall = [di|#{specf}(#{hsep . punctuate comma $ specArgs})|]
            let execArgs = [di|mut_state|] : map (pretty . show) argvars
            let execCall = [di|self.#{execf}(#{hsep . punctuate comma $ execArgs})|]
            return $ GenRustExpr frty [__di|
            #{vsep genArgVars}
            #{callMacro}(effects, itree, *mut_state, #{specCall}, #{execCall})
            |]
        _ -> throwError $ ErrSomethingFailed $ "TODO: genVerusCExpr: " ++ show (owlpretty expr)


-- Add lifetimes to references, structs, enums, OwlBufs for args/return types
addLifetime :: Lifetime -> VerusTy -> VerusTy
addLifetime lt (RTRef RMut ty) = RTRef (RMutWithLifetime lt) ty
addLifetime lt (RTRef RShared ty) = RTRef (RSharedWithLifetime lt) ty
addLifetime lt (RTStruct s fs) = if structNeedsLifetime s fs then RTWithLifetime (RTStruct s fs) lt else RTStruct s fs
addLifetime lt (RTEnum s cs) = if enumNeedsLifetime s cs then RTWithLifetime (RTEnum s cs) lt else RTEnum s cs
addLifetime lt (RTOwlBuf _) = RTOwlBuf lt
addLifetime lt (RTOption ty) = RTOption (addLifetime lt ty)
addLifetime _ t = t

genVerusDef :: VerusName -> CDef VerusTy -> EM (Doc ann)
genVerusDef lname cdef = do
    let execname = execName $ cdef ^. defName
    debugLog $ "genVerusDef: " ++ cdef ^. defName
    let specname = cdef ^. defName ++ "_spec"
    (defArgs', (rty', body)) <- unbindCDepBind $ cdef ^. defBody
    -- If any of the arguments or return type have a lifetime, we parameterize the whole function with lifetime 'a
    -- and make all arguments and return types have that lifetime
    let lt = Lifetime "a"
    let ltArgs = map (\(n, s, t) -> (n, s, addLifetime lt t)) defArgs'
    let ltRty = addLifetime lt rty'
    let (defArgsLt, rtyLt, needsLt) =
            if ltArgs == defArgs' && ltRty == rty' then (defArgs', rty', False) else (ltArgs, ltRty, True)
    verusArgs <- mapM compileArg defArgsLt
    let specRt = specTyOfExecTySerialized rty'
    let itreeTy = [di|Tracked<ITreeToken<(#{pretty specRt}, state_#{lname}),Endpoint>>|]
    let effectsArg = [di|effects: &mut E|]
    let itreeArg = [di|Tracked(itree): |] <> itreeTy
    let mutStateArg = [di|mut_state: &mut state_#{lname}|]
    let argdefs = hsep . punctuate comma $ [di|&#{if needsLt then pretty lt else pretty ""} self|] : effectsArg : itreeArg : mutStateArg : verusArgs
    let retval = [di|(res: Result<(#{pretty rtyLt}, #{itreeTy}), OwlError>)|]
    specargs <- mapM viewArg defArgs'
    let genInfo = GenCExprInfo { inK = True, specItreeTy = [di|(#{pretty specRt}, state_#{lname})|], curLocality = lname }
    (attr, bodyCode, castResInner) <- case body of
        Just body -> do
            body' <- genVerusCExpr genInfo body
            castResInner <- cast ([di|res_inner|], body' ^. eTy) rty'
            return ([di||], body' ^. code, castResInner)
        Nothing -> return ([di|\#[verifier::external_body]|], [di|unimplemented!(/* implement #{execname} by hand */)|], [di|res_inner|])
    viewRes <- viewVar "(r.0)" rty'
    return [__di|
    #{attr}
    \#[verifier::spinoff_prover]
    pub fn #{execname}<#{if needsLt then (pretty lt <> comma) else pretty ""}E: OwlEffects>(#{argdefs}) -> #{retval}
        requires 
            itree.view() == #{specname}(*self, *old(mut_state), #{hsep . punctuate comma $ specargs}),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in((#{viewRes}, *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (#{pretty rtyLt}, #{itreeTy}) = {
            broadcast use itree_axioms;
            reveal(#{specname});
            #{bodyCode}
        };
        Ok((#{castResInner}, Tracked(itree)))
    }
    |]
    where
        compileArg (cdvar, strname, ty) = do
            return [di|#{prettyArgName $ cdvar}: #{pretty ty}|]
        viewArg (cdvar, strname, ty) = viewVar (execName . show $ cdvar) ty
        prettyArgName = pretty . execName . show

---------------------------------------------------------------------------------------------------------------------------
-- Structs and enums

tyNeedsLifetime :: VerusTy -> Bool
tyNeedsLifetime (RTOwlBuf _) = True
tyNeedsLifetime (RTSecBuf _) = True
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

liftLifetime lt (RTOwlBuf _) = RTOwlBuf lt
liftLifetime lt (RTSecBuf _) = RTSecBuf lt
liftLifetime _ ty = ty

genVerusStruct :: CStruct (Maybe ConstUsize, VerusTy) -> EM (Doc ann)
genVerusStruct (CStruct name fieldsFV isVest isSecretParse isSecretSer) = do
    debugLog $ "genVerusStruct: " ++ name
    let fields = map (\(fname, (formatty, fty)) -> (fname, fty)) fieldsFV
    -- Lift all member fields to have the lifetime annotation of the whole struct
    let needsLifetime = any (tyNeedsLifetime . snd) fields
    let lifetimeConst = "a"
    let lifetimeAnnot = pretty $ if needsLifetime then "<'" ++ lifetimeConst ++ ">" else ""
    let verusFields = fmap (\(fname, fty) -> (fname, execName fname, liftLifetime (Lifetime lifetimeConst) fty)) fields
    let verusFieldsFV = fmap (\(fname, (formatty, fty)) -> (fname, execName fname, formatty, liftLifetime (Lifetime lifetimeConst) fty)) fieldsFV
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
    constructorShortcut <- genConstructorShortcut verusName verusFields lifetimeAnnot
    implStruct <- genImplStruct verusName verusFields lifetimeAnnot
    viewImpl <- genViewImpl verusName specname verusFields emptyLifetimeAnnot
    parsleyWrappers <- genParsleyWrappers verusName specname structTy verusFieldsFV lifetimeConst isVest isSecretParse isSecretSer
    return $ vsep [structDef, constructorShortcut, implStruct, viewImpl, parsleyWrappers]
    where

        genConstructorShortcut :: VerusName -> [(String, VerusName, VerusTy)] -> Doc ann -> EM (Doc ann)
        genConstructorShortcut verusName fields lAnnot = do
            let body = vsep . punctuate comma . fmap (\(_, ename, _) -> [di|#{ename}: arg_#{ename}|]) $ fields
            let args = hsep . punctuate comma . fmap (\(_, ename, fty) -> [di|arg_#{ename}: #{pretty fty}#{extraLt lAnnot fty}|]) $ fields
            let enss = vsep . punctuate comma . fmap (\(_, ename, _) -> [di|res.#{ename}.view() == arg_#{ename}.view()|]) $ fields
            return [__di|
            // Allows us to use function call syntax to construct members of struct types, a la Owl,
            // so we don't have to special-case struct constructors in the compiler
            \#[inline]
            pub fn #{verusName}#{lAnnot}(#{args}) -> (res: #{verusName}#{lAnnot})
                ensures  #{enss}
            {
                #{verusName} { #{body} }
            }
            |]

        genImplStruct :: VerusName -> [(String, VerusName, VerusTy)] -> Doc ann -> EM (Doc ann)
        genImplStruct verusName fields lAnnot = do
            let anotherRefFields = map (\(_, fname, fty) -> case fty of
                        RTWithLifetime (RTStruct t' _) _ -> [di|#{fname}: #{t'}::another_ref(&self.#{fname})|]
                        RTWithLifetime (RTEnum t' _) _ -> [di|#{fname}: #{t'}::another_ref(&self.#{fname})|]
                        (RTStruct t' _) -> [di|#{fname}: #{t'}::another_ref(&self.#{fname})|]
                        (RTEnum t' _) -> [di|#{fname}: #{t'}::another_ref(&self.#{fname})|]
                        RTOwlBuf _ -> [di|#{fname}: OwlBuf::another_ref(&self.#{fname})|]
                        RTSecBuf _ -> [di|#{fname}: SecretBuf::another_ref(&self.#{fname})|]
                        _ -> [di|#{fname}: self.#{fname}|]
                    ) fields
            return [__di|
            impl#{lAnnot} #{verusName}#{lAnnot} {
                pub fn another_ref<'other>(&'other self) -> (result: #{verusName}#{lAnnot})
                    ensures result.view() == self.view(),
                {
                    #{verusName} { 
                        #{vsep . punctuate comma $ anotherRefFields} 
                    }
                }
            }
            |]

        genViewImpl :: VerusName -> String -> [(String, VerusName, VerusTy)] -> Doc ann -> EM (Doc ann)
        genViewImpl verusName specname fields lAnnot = do
            let viewField (fname, ename, fty) = case fty of
                    RTVerusGhost -> [di|#{specName fname}: ghost_unit()|]
                    _ -> [di|#{specName fname}: self.#{ename}.view()|]
            let body = vsep . punctuate [di|,|] . fmap viewField $ fields
            return [__di|
            impl View for #{verusName}#{lAnnot} {
                type V = #{specname};
                open spec fn view(&self) -> #{specname} {
                    #{specname} { 
                        #{body}
                    }
                }
            }
            |]

        genParsleyWrappers :: VerusName -> String -> VerusTy -> [(String, VerusName, Maybe ConstUsize, VerusTy)] -> String -> Bool -> Bool -> Bool -> EM (Doc ann)
        genParsleyWrappers verusName specname structTy fields lifetimeConst True isSecretParse isSecretSer = do
            let specParse = [di|parse_#{specname}|]
            let execParse = [di|parse_#{verusName}|]
            let tupPatFields = mkNestPattern . fmap (\(_, fname, _, _) -> pretty fname) $ fields
            let mkField argty fname fty = do
                    mkf <- case fty of
                            RTOwlBuf _ -> (pretty fname, argty) `cast` fty
                            RTSecBuf _ -> (pretty fname, argty) `cast` fty
                            _ -> return $ pretty fname
                    return [di|#{fname}: #{mkf}|]
            mkStructFields <- hsep . punctuate comma <$> mapM (\(_, fname, _, fty) -> mkField (RTOwlBuf (Lifetime lifetimeConst)) fname fty) fields
            let parse = [__di|
            pub exec fn #{execParse}<'#{lifetimeConst}>(arg: OwlBuf<'#{lifetimeConst}>) -> (res: Option<#{pretty structTy}>) 
                ensures
                    res is Some ==> #{specParse}(arg.view()) is Some,
                    res is None ==> #{specParse}(arg.view()) is None,
                    res matches Some(x) ==> x.view() == #{specParse}(arg.view())->Some_0,
            {
                reveal(#{specParse});
                let exec_comb = exec_combinator_#{verusName}();
                if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
                    let #{tupPatFields} = parsed;
                    Some (#{verusName} { #{mkStructFields} })
                } else {
                    None
                }
            }
            |]
            secretParse <- if isSecretParse then do
                    mkStructFieldsSec <- hsep . punctuate comma <$> mapM (\(_, fname, _, fty) -> mkField (RTSecBuf (Lifetime lifetimeConst)) fname fty) fields
                    return [__di|
                    pub exec fn secret_#{execParse}<'#{lifetimeConst}>(arg: SecretBuf<'#{lifetimeConst}>) -> (res: Option<#{pretty structTy}>) 
                        ensures
                            res is Some ==> #{specParse}(arg.view()) is Some,
                            res is None ==> #{specParse}(arg.view()) is None,
                            res matches Some(x) ==> x.view() == #{specParse}(arg.view())->Some_0,
                    {
                        reveal(#{specParse});
                        let exec_comb = exec_combinator_#{verusName}();
                        if let Ok((_, parsed)) = <_ as Combinator<SecretBuf<'_>, SecretOutputBuf>>::parse(&exec_comb, arg) {
                            let #{tupPatFields} = parsed;
                            Some (#{verusName} { #{mkStructFieldsSec} })
                        } else {
                            None
                        }
                    }
                    |]
                else return [di||]
            let specSer = [di|serialize_#{specname}|]
            let execSer = [di|serialize_#{verusName}|]
            let specSerInner = [di|serialize_#{specname}_inner|]
            let execSerInner = [di|serialize_#{verusName}_inner|]
            let mklen fname szopt fty = case (fty, szopt) of
                    (RTUnit, Just usz) -> return [di|#{pretty usz}|]
                    (RTUnit, Nothing) -> throwError $ ErrSomethingFailed "no size for const ty"
                    _ -> return [di|arg.#{fname}.len()|]
            lens' <- mapM (\(_, fname, szopt, fty) -> mklen fname szopt fty) fields
            let lens = lens' ++ [pretty "0"]
            let innerTyOf fty = case fty of
                    RTUnit -> RTUnit
                    -- if serializing to secret, we upcast the public fields to secret
                    RTOwlBuf l -> if isSecretSer then RTSecBuf l else RTOwlBuf l
                    RTSecBuf l -> RTSecBuf l
                    _ -> u8slice
            fieldsAsInner <- mkNestPattern <$> mapM (\(_, fname, _, fty) -> (pretty ("arg." ++ fname), fty) `cast` innerTyOf fty) fields
            (outTy, obufConstructor, castObuf) <-
                    if isSecretSer then return
                        ( [di|SecretBuf<'#{lifetimeConst}>|]
                        , [di|SecretOutputBuf::new_obuf|]
                        , [di|obuf.into_secret_buf()|]
                        )
                    else do
                        castObuf <- ([di|obuf|], vecU8) `cast` RTOwlBuf (Lifetime lifetimeConst)
                        return  ( [di|OwlBuf<'#{lifetimeConst}>|]
                                , [di|vec_u8_of_len|]
                                , castObuf
                                )

            let ser = [__di|
            pub exec fn #{execSerInner}<'#{lifetimeConst}>(arg: &#{verusName}<'#{lifetimeConst}>) -> (res: Option<#{outTy}>)
                ensures
                    res is Some ==> #{specSerInner}(arg.view()) is Some,
                    res matches Some(x) ==> x.view() == #{specSerInner}(arg.view())->Some_0,
            {
                reveal(#{specSerInner});
                if no_usize_overflows![ #{(hsep . punctuate comma) lens} ] {
                    let exec_comb = exec_combinator_#{verusName}();
                    let mut obuf = #{obufConstructor}(#{(hsep . punctuate (pretty "+")) lens});
                    let ser_result = exec_comb.serialize(#{fieldsAsInner}, &mut obuf, 0);
                    if let Ok((num_written)) = ser_result {
                        assert(obuf.view() == #{specSerInner}(arg.view())->Some_0);
                        Some(#{castObuf})
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            \#[inline]
            pub exec fn #{execSer}<'#{lifetimeConst}>(arg: &#{verusName}<'#{lifetimeConst}>) -> (res: #{outTy})
                ensures  res.view() == #{specSer}(arg.view())
            {
                reveal(#{specSer});
                let res = #{execSerInner}(arg);
                assume(res is Some);
                res.unwrap()
            }
            |]
            return $ vsep [parse, secretParse, ser]
        genParsleyWrappers verusName specname structTy fields lifetimeConst False isSecretParse _ = do
            let specParse = [di|parse_#{specname}|]
            let execParse = [di|parse_#{verusName}|]
            let parse = [__di|
            \#[verifier::external_body]
            pub exec fn #{execParse}<'#{lifetimeConst}>(arg: OwlBuf<'#{lifetimeConst}>) -> (res: Option<#{pretty structTy}>) 
                ensures
                    res is Some ==> #{specParse}(arg.view()) is Some,
                    res is None ==> #{specParse}(arg.view()) is None,
                    res matches Some(x) ==> x.view() == #{specParse}(arg.view())->Some_0,
            {
                unimplemented!()
            }
            |]
            let secretParse = if isSecretParse then
                    [__di|
                    \#[verifier::external_body]
                    pub exec fn secret_#{execParse}<'#{lifetimeConst}>(arg: SecretBuf<'#{lifetimeConst}>) -> (res: Option<#{pretty structTy}>) 
                        ensures
                            res is Some ==> #{specParse}(arg.view()) is Some,
                            res is None ==> #{specParse}(arg.view()) is None,
                            res matches Some(x) ==> x.view() == #{specParse}(arg.view())->Some_0,
                    {
                        unimplemented!()
                    }
                    |]
                else [di||]
            let specSer = [di|serialize_#{specname}|]
            let execSer = [di|serialize_#{verusName}|]
            let specSerInner = [di|serialize_#{specname}_inner|]
            let execSerInner = [di|serialize_#{verusName}_inner|]
            let outTy = if isSecretSer then [di|SecretBuf<'#{lifetimeConst}>|] else [di|OwlBuf<'#{lifetimeConst}>|]
            let ser = [__di|
            \#[verifier::external_body]
            pub exec fn #{execSerInner}<'#{lifetimeConst}>(arg: &#{verusName}) -> (res: Option<#{outTy}>)
                ensures
                    res is Some ==> #{specSerInner}(arg.view()) is Some,
                    res matches Some(x) ==> x.view() == #{specSerInner}(arg.view())->Some_0,
            {
                unimplemented!()
            }
            \#[verifier::external_body]
            pub exec fn #{execSer}<'#{lifetimeConst}>(arg: &#{verusName}) -> (res: #{outTy})
                ensures  res.view() == #{specSer}(arg.view())
            {
                unimplemented!()
            }
            |]
            return $ vsep [parse, secretParse, ser]


genVerusEnum :: CEnum (Maybe ConstUsize, VerusTy) -> EM (Doc ann)
genVerusEnum (CEnum name casesFV isVest execComb isSecret) = do
    debugLog $ "genVerusEnum: " ++ name
    let cases = M.mapWithKey (\fname opt -> case opt of Just (_, rty) -> Just rty; Nothing -> Nothing) casesFV
    -- Lift all member fields to have the lifetime annotation of the whole struct
    let needsLifetime = any tyNeedsLifetime . mapMaybe snd . M.assocs $ cases
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
    use #{verusName}::*;
    |]
    let emptyLifetimeAnnot = pretty $ if needsLifetime then "<'_>" else ""
    implEnum <- genImplEnum verusName verusCases lifetimeAnnot
    viewImpl <- genViewImpl verusName specname verusCases emptyLifetimeAnnot
    parsleyWrappers <- genParsleyWrappers verusName specname enumTy verusCases lifetimeConst execComb isVest isSecret
    enumTests <- mkEnumTests verusName specname verusCases emptyLifetimeAnnot
    return $ (vsep [enumDef, implEnum, viewImpl, enumTests, parsleyWrappers])
    where
        liftLifetime a (Just (RTOwlBuf _)) = Just $ RTOwlBuf (Lifetime a)
        liftLifetime a (Just (RTSecBuf _)) = Just $ RTSecBuf (Lifetime a)
        liftLifetime _ ty = ty

        genImplEnum :: VerusName -> M.Map String (VerusName, Maybe VerusTy) -> Doc ann -> EM (Doc ann)
        genImplEnum verusName cases lAnnot = do
            let anotherRefFields = M.map (\(fname, fty) -> case fty of
                        Just (RTWithLifetime (RTStruct t' _) _) -> [di|#{fname}(x) => #{fname}(#{t'}::another_ref(x))|]
                        Just (RTWithLifetime (RTEnum t' _) _) -> [di|#{fname}(x) => #{fname}(#{t'}::another_ref(x))|]
                        Just (RTStruct t' _) -> [di|#{fname}(x) => #{fname}(#{t'}::another_ref(x))|]
                        Just (RTEnum t' _) -> [di|#{fname}(x) => #{fname}(#{t'}::another_ref(x))|]
                        Just (RTOwlBuf _) -> [di|#{fname}(x) => #{fname}(OwlBuf::another_ref(x))|]
                        Just (RTSecBuf _) -> [di|#{fname}(x) => #{fname}(SecretBuf::another_ref(x))|]
                        Just _ -> [di|#{fname}(x) => #{fname}(x)|]
                        Nothing -> [di|#{fname}() => #{fname}()|]
                    ) cases
            let anotherRefBody = vsep . punctuate comma $ M.elems anotherRefFields
            return [__di|
            impl#{lAnnot} #{verusName}#{lAnnot} {
                pub fn another_ref<'other>(&'other self) -> (result: #{verusName}#{lAnnot})
                    ensures result.view() == self.view(),
                {
                    match self { 
                        #{anotherRefBody} 
                    }
                }
            }
            |]

        viewCase specname fname (ename, Just RTVerusGhost) = [di|#{ename}(v) => #{specname}::#{specName fname}(owl_ghost_unit())|]
        viewCase specname fname (ename, Just fty) = [di|#{ename}(v) => #{specname}::#{specName fname}(v.view())|]
        viewCase specname fname (ename, Nothing) = [di|#{ename}() => #{specname}::#{specName fname}()|]

        genViewImpl :: VerusName -> String -> M.Map String (VerusName, Maybe VerusTy) -> Doc ann -> EM (Doc ann)
        genViewImpl verusName specname cases lAnnot = do
            let body = vsep . punctuate [di|,|] . M.elems . M.mapWithKey (viewCase specname) $ cases
            return [__di|
            impl View for #{verusName}#{lAnnot} {
                type V = #{specname};
                open spec fn view(&self) -> #{specname} {
                    match self { 
                        #{body}
                    }
                }
            }
            |]

        mkEnumTests :: VerusName -> String -> M.Map String (VerusName, Maybe VerusTy) -> Doc ann -> EM (Doc ann)
        mkEnumTests verusName specname cases lAnnot = do
            tests <- mapM mkEnumTest (M.assocs cases)
            return $ vsep tests
            where
                mkEnumTest (cname, (fname, topt)) = do
                    let var = case topt of
                            Just _ -> [di|_|]
                            Nothing -> [di||]
                    return [__di|
                    \#[inline]
                    pub fn #{fname}_enumtest(x: &#{verusName}#{lAnnot}) -> (res:bool)
                        ensures res == #{cname}_enumtest(x.view())
                    {
                        match x {
                            #{verusName}::#{fname}(#{var}) => true,
                            _ => false,
                        }
                    }
                    |]

        genParsleyWrappers :: VerusName -> String -> VerusTy -> M.Map String (VerusName, Maybe VerusTy) -> String -> String -> Bool -> Bool -> EM (Doc ann)
        genParsleyWrappers verusName specname enumTy cases lifetimeConst execComb True isSecret = do
            let specParse = [di|parse_#{specname}|]
            let execParse = [di|parse_#{verusName}|]
            let l = length cases
            let mkParseBranch ((caseName, topt), i) = do
                    let (lhsX, rhsX) = case topt of
                            Just _ -> ([di|(_,x)|], [di|x|])
                            Nothing -> ([di|_|], [di||])
                    lhs <- listIdxToInjPat i l lhsX
                    rhs <- case topt of
                            Just (RTOwlBuf l) -> (rhsX, RTOwlBuf AnyLifetime) `cast` RTOwlBuf l
                            Just (RTSecBuf l) -> (rhsX, RTOwlBuf AnyLifetime) `cast` RTSecBuf l
                            _ -> return rhsX
                    return [__di|
                    #{lhs} => #{verusName}::#{caseName}(#{rhs}),
                    |]
            parseBranches <- mapM mkParseBranch (zip (M.elems cases) [0..])
            let mkParseBranchVec ((caseName, topt), i) = do
                    let (lhsX, rhsX) = case topt of
                            Just _ -> ([di|(_,x)|], [di|x|])
                            Nothing -> ([di|_|], [di||])
                    lhs <- listIdxToInjPat i l lhsX
                    rhs <- case topt of
                            Just (RTOwlBuf l) -> ([di|slice_to_vec(#{rhsX})|], vecU8) `cast` RTOwlBuf l
                            _ -> return rhsX
                    return [di|#{lhs} => #{verusName}::#{caseName}(#{rhs}),|]
            parseBranchesVecs <- mapM mkParseBranchVec (zip (M.elems cases) [0..])
            let parse = [__di|
            pub exec fn #{execParse}<'#{lifetimeConst}>(arg: OwlBuf<'#{lifetimeConst}>) -> (res: Option<#{pretty enumTy}>) 
                ensures
                    res is Some ==> #{specParse}(arg.view()) is Some,
                    res is None ==> #{specParse}(arg.view()) is None,
                    res matches Some(x) ==> x.view() == #{specParse}(arg.view())->Some_0,
            {
                reveal(#{specParse});
                let exec_comb = #{execComb};
                if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
                    let v = match parsed {
                        #{vsep parseBranches}
                    };
                    Some(v)
                } else {
                    None
                }
            }
            |]
            secretParse <- if isSecret then do
                    let parse = [__di|
                    \#[verifier(external_body)] 
                    pub exec fn secret_#{execParse}<'#{lifetimeConst}>(arg: SecretBuf<'#{lifetimeConst}>, Tracked(t): Tracked<DeclassifyingOpToken>) -> (res: Option<#{pretty enumTy}>) 
                        requires t.view() matches DeclassifyingOp::EnumParse(b) && b == arg.view()
                        ensures
                            res is Some ==> #{specParse}(arg.view()) is Some,
                            res is None ==> #{specParse}(arg.view()) is None,
                            res matches Some(x) ==> x.view() == #{specParse}(arg.view())->Some_0,
                    {
                        reveal(#{specParse});
                        unimplemented!()
                    }
                    |]
                    return parse
                else return [di||]
            let specSer = [di|serialize_#{specname}|]
            let execSer = [di|serialize_#{verusName}|]
            let specSerInner = [di|serialize_#{specname}_inner|]
            let execSerInner = [di|serialize_#{verusName}_inner|]
            let mkSerBranch ((caseName, topt), i) = do
                    let (lhsX, lhsXLen,  rhsX) = case topt of
                            Just _ -> ([di|x|], [di|x.len()|], [di|((), x.as_slice())|])
                            Nothing -> ([di||], [di|0|], [di|((), &empty_vec.as_slice())|])
                    rhs <- listIdxToInjResult i l rhsX
                    return [__di|
                    #{verusName}::#{caseName}(#{lhsX}) => {                
                        if no_usize_overflows![ 1, #{lhsXLen} ] {
                            let mut obuf = vec_u8_of_len(1 + #{lhsXLen});
                            let ser_result = exec_comb.serialize(#{rhs}, &mut obuf, 0);
                            if let Ok((num_written)) = ser_result {
                                assert(obuf.view() == #{specSerInner}(arg.view())->Some_0);
                                Some(obuf)
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    },
                    |]
            serBranches <- mapM mkSerBranch (zip (M.elems cases) [0..])
            let ser = [__di|
            \#[verifier(external_body)] 
            pub exec fn #{execSerInner}(arg: &#{verusName}) -> (res: Option<Vec<u8>>)
                ensures
                    res is Some ==> #{specSerInner}(arg.view()) is Some,
                    res is None ==> #{specSerInner}(arg.view()) is None,
                    res matches Some(x) ==> x.view() == #{specSerInner}(arg.view())->Some_0,
            {
                unimplemented!()
            }
            \#[inline]
            pub exec fn #{execSer}(arg: &#{verusName}) -> (res: Vec<u8>)
                ensures  res.view() == #{specSer}(arg.view())
            {
                reveal(#{specSer});
                let res = #{execSerInner}(arg);
                assume(res is Some);
                res.unwrap()
            }
            |]
            return $ vsep [parse, secretParse, ser]
        genParsleyWrappers verusName specname enumTy cases lifetimeConst execComb False _ = do
            let specParse = [di|parse_#{specname}|]
            let execParse = [di|parse_#{verusName}|]
            let parse = [__di|
            \#[verifier::external_body]
            pub exec fn #{execParse}<'#{lifetimeConst}>(arg: OwlBuf<'#{lifetimeConst}>) -> (res: Option<#{pretty enumTy}>) 
                ensures
                    res is Some ==> #{specParse}(arg.view()) is Some,
                    res is None ==> #{specParse}(arg.view()) is None,
                    res matches Some(x) ==> x.view() == #{specParse}(arg.view())->Some_0,
            {
                unimplemented!()
            }
            |]
            secretParse <- if isSecret then do
                    let parse = [__di|
                    \#[verifier(external_body)] 
                    pub exec fn secret_#{execParse}<'#{lifetimeConst}>(arg: SecretBuf<'#{lifetimeConst}>, Tracked(t): Tracked<DeclassifyingOpToken>) -> (res: Option<#{pretty enumTy}>) 
                        requires t.view() matches DeclassifyingOp::EnumParse(b) && b == arg.view()
                        ensures
                            res is Some ==> #{specParse}(arg.view()) is Some,
                            res is None ==> #{specParse}(arg.view()) is None,
                            res matches Some(x) ==> x.view() == #{specParse}(arg.view())->Some_0,
                    {
                        reveal(#{specParse});
                        unimplemented!()
                    }
                    |]
                    return parse
                else return [di||]
            let specSer = [di|serialize_#{specname}|]
            let execSer = [di|serialize_#{verusName}|]
            let specSerInner = [di|serialize_#{specname}_inner|]
            let execSerInner = [di|serialize_#{verusName}_inner|]
            let ser = [__di|
            \#[verifier(external_body)] 
            pub exec fn #{execSerInner}(arg: &#{verusName}) -> (res: Option<Vec<u8>>)
                ensures
                    res is Some ==> #{specSerInner}(arg.view()) is Some,
                    res is None ==> #{specSerInner}(arg.view()) is None,
                    res matches Some(x) ==> x.view() == #{specSerInner}(arg.view())->Some_0,
            {
                unimplemented!()
            }
            \#[verifier(external_body)]
            pub exec fn #{execSer}(arg: &#{verusName}) -> (res: Vec<u8>)
                ensures  res.view() == #{specSer}(arg.view())
            {
                unimplemented!()
            }
            |]
            return $ vsep [parse, secretParse, ser]


genVerusTyDef :: CTyDef (Maybe ConstUsize, VerusTy) -> EM (Doc ann)
genVerusTyDef (CStructDef s) = genVerusStruct s
genVerusTyDef (CEnumDef e) = genVerusEnum e


genVerusTyDefs :: [(String, CTyDef (Maybe ConstUsize, VerusTy))] -> EM (Doc ann)
genVerusTyDefs tydefs = do
    -- debugLog "genVerusTyDefs"
    tyDefs <- mapM (genVerusTyDef . snd) tydefs
    return $ vsep tyDefs


-----------------------------------------------------------------------------
-- Utility functions

castGRE :: GenRustExpr ann -> VerusTy -> EM (Doc ann)
castGRE gre t2 = cast (gre ^. code, gre ^. eTy) t2

-- cast v t1 t2 v returns an expression of type t2 whose contents are v, which is of type t1
cast :: (Doc ann, VerusTy) -> VerusTy -> EM (Doc ann)
cast (v, t1) t2 | t2 == RTRef RShared t1 =
    return [di|&#{v}|]
cast (v, t1) t2 | t2 == RTRef RMut t1 =
    return [di|&mut #{v}|]
cast (v, RTRef RMut t1) (RTRef RShared t2) | t1 == t2 =
    return [di|&#{v}|]
cast (v, RTVec t1) (RTRef b (RTSlice t2)) | t1 == t2 =
    return [di|#{v}.as_slice()|]
cast (v, t1) t2 | t2 == RTVerusTracked t1 =
    return [di|Tracked(#{v})|]
cast (v, RTArray RTU8 _) (RTRef RShared (RTSlice RTU8)) =
    return [di|&#{v}.as_slice()|]
cast (v, RTRef _ (RTSlice RTU8)) (RTArray RTU8 _) =
    return [di|#{v}.try_into()|]
cast (v, RTRef _ (RTSlice RTU8)) (RTOwlBuf _) =
    return [di|OwlBuf::from_slice(&#{v})|]
cast (v, RTVec RTU8) (RTOwlBuf _) =
    return [di|OwlBuf::from_vec(#{v})|]
cast (v, RTVec RTU8) (RTSecBuf _) =
    return [di|OwlBuf::from_vec(#{v}).into_secret()|]
cast (v, RTArray RTU8 _) (RTOwlBuf _) =
    return [di|OwlBuf::from_slice(&#{v})|]
cast (v, RTArray RTU8 _) (RTSecBuf _) =
    return [di|OwlBuf::from_slice(&#{v}).into_secret()|]
cast (v, RTOwlBuf _) (RTRef _ (RTSlice RTU8)) =
    return [di|#{v}.as_slice()|]
cast (v, RTOption (RTVec RTU8)) (RTOption (RTOwlBuf _)) =
    return [di|OwlBuf::from_vec_option(#{v})|]
cast (v, RTStruct t fs) (RTRef RShared (RTSlice RTU8)) = do
    c1 <- cast (v, RTStruct t fs) (RTOwlBuf AnyLifetime)
    cast (c1, vecU8) u8slice
cast (v, RTStruct t fs) (RTOwlBuf l) = do
    return [di|serialize_#{t}(&#{v})|]
cast (v, RTStruct t fs) (RTSecBuf l) = do 
    return [di|serialize_#{t}(&#{v})|]
cast (v, RTEnum t cs) (RTOwlBuf l) = do
    return [di|OwlBuf::from_vec(serialize_#{t}(&#{v}))|]
cast (v, RTEnum t cs) (RTSecBuf l) = do 
    return [di|OwlBuf::from_vec(serialize_#{t}(&#{v})).into_secret()|]
cast (v, RTEnum t cs) (RTVec RTU8) =
    return [di|serialize_#{t}(&#{v})|]
cast (v, RTEnum t cs) (RTRef RShared (RTSlice RTU8)) = do
    c1 <- cast (v, RTEnum t cs) vecU8
    cast (c1, vecU8) u8slice
cast (v, RTEnum t cs) (RTOwlBuf l) = do
    c1 <- cast (v, RTEnum t cs) vecU8
    cast (c1, vecU8) (RTOwlBuf l)
cast (v, RTOwlBuf _) (RTSecBuf _) =
    return [di|SecretBuf::from_buf(#{v}.another_ref())|]
cast (v, RTOwlBuf _) (RTRef RShared (RTSecBuf _)) =
    return [di|&SecretBuf::from_buf(#{v}.another_ref())|]
-- Special case: the `cast` in the compiler approximately corresponds to where we need to call OwlBuf::another_ref
cast (v, RTOwlBuf _) (RTOwlBuf _) =
    return [di|OwlBuf::another_ref(&#{v})|]
cast (v, RTSecBuf _) (RTSecBuf _) =
    return [di|SecretBuf::another_ref(&#{v})|]
cast (v, RTOption (RTOwlBuf _)) (RTOption (RTOwlBuf _)) =
    return [di|OwlBuf::another_ref_option(&#{v})|]
cast (v, RTOption (RTSecBuf _)) (RTOption (RTSecBuf _)) =
    return [di|SecretBuf::another_ref_option(&#{v})|]
cast (v, RTStruct s _) (RTStruct s' _) | s == s' =
    return [di|#{s}::another_ref(&#{v})|]
cast (v, RTEnum e _) (RTEnum e' _) | e == e' =
    return [di|#{e}::another_ref(&#{v})|]
cast (v, RTDummy) t = return v
cast (v, RTOption RTDummy) (RTOption t) = return v
cast (v, RTStAeadBuilder) (RTVec RTU8) = return [di|#{v}.into_fresh_vec()|]
cast (v, RTStAeadBuilder) (RTRef RShared (RTSlice RTU8)) = do
    c1 <- cast (v, RTStAeadBuilder) vecU8
    cast (c1, vecU8) (RTRef RShared (RTSlice RTU8))
cast (v, RTStAeadBuilder) (RTOwlBuf l) = do
    c1 <- cast (v, RTStAeadBuilder) vecU8
    cast (c1, vecU8) (RTOwlBuf l)
cast (v, t1) t2 | t1 == t2 = return v
cast (v, RTEnum e1 cs1) (RTEnum e2 cs2) | e1 == e2 && S.fromList cs1 == S.fromList cs2 = return v
cast (v, _) RTUnit = return [di|()|]
cast (v, t1) t2 = throwError $ CantCastType (show v) (show t1) (show t2)

u8slice :: VerusTy
u8slice = RTRef RShared (RTSlice RTU8)

vecU8 :: VerusTy
vecU8 = RTVec RTU8

secBuf :: VerusTy
secBuf = RTSecBuf AnyLifetime

owlBuf :: VerusTy
owlBuf = RTOwlBuf AnyLifetime

unifyVerusTysUpToSecrecy :: VerusTy -> VerusTy -> EM VerusTy
unifyVerusTysUpToSecrecy RTDummy t2 = return t2
unifyVerusTysUpToSecrecy t1 t2 | t1 == t2 = return t1
unifyVerusTysUpToSecrecy t1 RTDummy = return t1
unifyVerusTysUpToSecrecy (RTOption t1) (RTOption t2) = RTOption <$> unifyVerusTysUpToSecrecy t1 t2
unifyVerusTysUpToSecrecy (RTSecBuf l1) (RTOwlBuf _) = return $ RTSecBuf l1
unifyVerusTysUpToSecrecy (RTOwlBuf _) (RTSecBuf l1) = return $ RTSecBuf l1
unifyVerusTysUpToSecrecy t1 t2 = throwError $ ErrSomethingFailed $ "can't unify Verus types: " ++ (show . pretty $ t1) ++ " and " ++ (show . pretty $ t2)


snOfEn n = if "owl_" `isPrefixOf` n then "owlSpec_" ++ drop 4 n else n

specTyOfExecTySerialized :: VerusTy -> VerusTy
specTyOfExecTySerialized (RTVec t) = RTSeq (specTyOfExecTySerialized t)
specTyOfExecTySerialized (RTOwlBuf _) = RTSeq RTU8
specTyOfExecTySerialized (RTSecBuf _) = RTSeq RTU8
specTyOfExecTySerialized (RTRef _ (RTSlice t)) = RTSeq (specTyOfExecTySerialized t)
specTyOfExecTySerialized (RTArray t _) = RTSeq (specTyOfExecTySerialized t)
specTyOfExecTySerialized (RTOption t) = RTOption (specTyOfExecTySerialized t)
specTyOfExecTySerialized (RTTuple ts) = RTTuple (fmap specTyOfExecTySerialized ts)
specTyOfExecTySerialized (RTStruct n fs) = RTStruct (snOfEn n) (fmap (\(f, t) -> (f, specTyOfExecTySerialized t)) fs)
specTyOfExecTySerialized (RTEnum n cs) = RTEnum (snOfEn n) (fmap (\(c, mt) -> (c, fmap specTyOfExecTySerialized mt)) cs)
specTyOfExecTySerialized (RTWithLifetime t l) = specTyOfExecTySerialized t
specTyOfExecTySerialized t = t 


viewVar :: VerusName -> VerusTy -> EM (Doc ann)
viewVar vname RTUnit = return [di|()|]
viewVar vname (RTNamed _) = return [di|#{vname}.view()|]
viewVar vname (RTStruct _ _) = return [di|#{vname}.view()|]
viewVar vname (RTEnum _ _) = return [di|#{vname}.view()|]
viewVar vname (RTOption (RTNamed _)) = return [di|option_as_seq(view_option(#{vname}))|]
viewVar vname (RTOption _) = return [di|view_option(#{vname})|]
viewVar vname (RTRef _ (RTSlice RTU8)) = return [di|#{vname}.view()|]
viewVar vname (RTVec RTU8) = return [di|#{vname}.view()|]
viewVar vname (RTArray RTU8 _) = return [di|#{vname}.view()|]
viewVar vname (RTOwlBuf _) = return [di|#{vname}.view()|]
viewVar vname (RTSecBuf _) = return [di|#{vname}.view()|]
viewVar vname RTBool = return [di|#{vname}|]
viewVar vname RTUsize = return [di|#{vname}|]
viewVar vname RTVerusGhost = return [di|#{vname}|]
viewVar vname (RTWithLifetime t _) = viewVar vname t
viewVar vname ty = throwError $ ErrSomethingFailed $ "TODO: viewVar: " ++ vname ++ ": " ++ show ty