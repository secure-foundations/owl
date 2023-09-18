module Parse where

import Debug.Trace
import Text.Parsec
import Text.Parsec.Language
import Text.Parsec.Expr
import Data.Default (Default, def)
import qualified Text.Parsec.Token as P
import System.Environment
import Control.Monad.IO.Class
import Control.Lens ((^.))
import qualified Data.Map.Strict as M
import Error.Diagnose.Position
import qualified Data.Functor.Identity as I
import qualified Data.Set as S
import Unbound.Generics.LocallyNameless
import AST

type Parser = ParsecT String () IO 

owlStyle  :: P.GenLanguageDef String st IO
owlStyle   = P.LanguageDef
                { P.commentStart   = "/*"
                , P.commentEnd     = "*/"
                , P.commentLine    = "//"
                , P.nestedComments = True
                , P.identStart     = letter <|> char '_'
                , P.identLetter    = alphaNum <|> oneOf "_'?"
                , P.opStart        = oneOf ":!#$%&*+./<=>?@\\^|-~"
                , P.opLetter       = oneOf ":!#$%&*+./<=>?@\\^|-~"
                , P.reservedNames  = ["adv",  "bool", "Option", "name", "Name", "enckey",  "st_aead", "nonce_pattern", "mackey", "sec", "st_aead_enc", "st_aead_dec", "let", "DH", "nonce", "if", "then", "else", "enum", "Data", "sigkey", "type", "Unit", "Lemma", "random_oracle", "return", "corr", "RO", "debug", "assert",  "assume", "admit", "ensures", "true", "false", "True", "False", "call", "static", "corr_case", "false_elim", "union_case", "exists", "get",  "getpk", "getvk", "pack", "def", "Union", "pkekey", "label", "aexp", "type", "idx", "table", "lookup", "write", "unpack", "to", "include", "maclen",  "begin", "end", "module", "aenc", "adec", "pkenc", "pkdec", "mac", "mac_vrfy", "sign", "vrfy", "prf",  "PRF", "forall", "bv", "pcase", "choose_idx", "crh_lemma", "ro", "is_constant_lemma", "strict", "aad"]
                , P.reservedOpNames= ["(", ")", "->", ":", "=", "==", "!", "<=", "!<=", "!=", "*", "|-", "+x"]
                , P.caseSensitive  = True
                }

lexer = P.makeTokenParser owlStyle
parens      = P.parens lexer
braces      = P.braces lexer
identifier  = P.identifier lexer
whiteSpace  = P.whiteSpace lexer
reserved    = P.reserved lexer
symbol    = P.symbol lexer
colon    = P.colon lexer
comma    = P.comma lexer
dot    = P.dot lexer
semi    = P.semi lexer
commaSep    = P.commaSep lexer
reservedOp = P.reservedOp lexer
natural = P.natural lexer

mkPos :: SourcePos -> SourcePos -> Position
mkPos x y = Position (sourceLine x, sourceColumn x) (sourceLine y, sourceColumn y) (sourceName x)

joinPosition :: Position -> Position -> Position
joinPosition p1 p2 = Position (begin p1) (end p2) (file p1)

prefixPosition :: SourcePos -> Position -> Position
prefixPosition p1 x = Position (sourceLine p1, sourceColumn p1) (end x) (sourceName p1)

postfixPosition :: Position -> SourcePos -> Position
postfixPosition x p = Position (begin x) (sourceLine p, sourceColumn p) (sourceName p)

parensPos :: Parser (Spanned a) -> Parser (Spanned a)
parensPos k = do
    p <- getPosition
    v <- parens k
    p' <- getPosition
    return $ Spanned (ignore $ Position (sourceLine p, sourceColumn p) (sourceLine p', sourceColumn p') (sourceName p)) (v^.val)



parseSpanned :: Parser a -> Parser (Spanned a)
parseSpanned k = do
    p <- getPosition
    v <- k
    p' <- getPosition
    return $ Spanned (ignore $ Position (sourceLine p, sourceColumn p) (sourceLine p', sourceColumn p') (sourceName p)) v

parseNameExp = 
    (parseSpanned $ do
        reserved "PRF"
        symbol "<"
        n <- parseNameExp
        symbol ","
        p <- identifier
        symbol ">"
        return $ PRFName n p)
    <|>
    (parseSpanned $ do
        i <- parsePath
        ps <- parseIdxParams 
        oi <- optionMaybe $ do
            symbol "["
            oas_ <- optionMaybe $ do 
                as <- parseAExpr `sepBy` (symbol ",")
                symbol ";"
                return as
            let as = case oas_ of
                        Nothing -> []
                        Just v -> v
            i <- many1 digit
            symbol "]"
            return $ (as, read i)
        return $ NameConst ps i oi)

parsePath :: Parser Path
parsePath = 
    (try $ do
        x <- identifier
        char '.'
        xs <- identifier `sepBy1` (char '.')
        return $ PUnresolvedPath x xs
    )
    <|>
    (do
        x <- identifier
        return $ PUnresolvedVar x
    )

infixLabel op f assoc = 
    Infix (do
        symbol op
        return (\x y -> mkSpannedWith (joinPosition (unignore $ x^.spanOf) (unignore $ y^.spanOf)) $ f x y)) assoc

parseLabel = buildExpressionParser parseLabelTable parseLabelTerm
parseLabelTable = [ [ infixProp "/\\" LJoin AssocLeft ] ] 
parseLabelTerm = 
        parensPos parseLabel <|> 
      (parseSpanned $ do
          reserved "static";
          return LZero)
      <|>
      (parseSpanned $ do
          reserved "adv";
          return LAdv)
      <|>
      (parseSpanned $ do
          reserved "top";
          return LTop)
      <|> (parseSpanned $ do
          symbol "["
          n <- parseNameExp;
          symbol "]"
          return $ LName n)
      <|> (parseSpanned $ do
          symbol "#"
          n <- parsePath
          symbol "#"
          return $ LConst $ TyLabelVar n)
      <|> (try $ parseSpanned $ do
          symbol "/\\_"
          i <- identifier
          l <- parseLabel
          return $ LRangeIdx $ bind (s2n i) l
          )

alt = (<|>)

parseTy = buildExpressionParser parseTyTable parseTyTerm
parseTyTable = [ [  ] ]
parseTyTerm = 
    parensPos parseTy
    <|>
    (parseSpanned $ do
        reserved "Bool"
        symbol "<"
        l <- parseLabel
        symbol ">"
        return $ TBool l
    )
    <|>
    (parseSpanned $ do 
        reserved "Option"
        t <- parseTy
        return $ TOption t)
    <|>
    (parseSpanned $ do 
        reserved "Union"
        symbol "<"
        t1 <- parseTy
        symbol ","
        t2 <- parseTy
        symbol ">"
        return $ TUnion t1 t2)
    <|>
    (parseSpanned $ do
        reserved "Unit"
        return $ TUnit)
    <|>
    (parseSpanned $ do
        reserved "Lemma"
        symbol "{"
        p <- parseProp
        symbol "}"
        return $ TRefined tUnit "._" $ bind (s2n "._") p)
    <|>
    (parseSpanned $ do
        reserved "Data"
        symbol "<"
        l <- parseLabel
        alt
            (do
                symbol ">"
                alt
                    (try $ do
                        symbol "|"
                        a <- parseAExpr
                        symbol "|"
                        return $ TDataWithLength l a
                    )
                    (return $ TData l l (ignore Nothing))
            )
            (do
                symbol ","
                symbol "|"
                l' <- parseLabel
                symbol "|"
                symbol ">"
                return $ TData l l' (ignore Nothing)
            ) 
    )
    <|>
    (parseSpanned $ do
        reserved "if"
        p <- parseProp
        reserved "then"
        t1 <- parseTy
        reserved "else"
        t2 <- parseTy
        return $ TCase p t1 t2
    )
    <|>
    (parseSpanned $ do
        p <- getPosition
        reserved "sec"
        symbol "("
        ne <- parseNameExp
        symbol ")"
        symbol "?"
        t <- parseTy
        p' <- getPosition
        return $ TCase (mkSpanned $ PNot $ Spanned (ignore $ mkPos p p') $ PFlow (Spanned (_spanOf ne) $ LName ne) advLbl)
                       t
                       (mkSpanned $ TData advLbl advLbl (ignore Nothing))
    )
    <|>
    (parseSpanned $ do
        reserved "Name"
        symbol "("
        n <- parseNameExp
        symbol ")"
        return $ TName n)
    <|>
    (parseSpanned $ do
        reserved "exists"
        i <- identifier
        symbol "."
        t <- parseTy
        return $ TExistsIdx $ bind (s2n i) t 
    )
    <|>
    (try $ parseSpanned $ do
        x <- identifier
        case x of
          "vk" -> do
                 symbol "("
                 n <- parseNameExp
                 symbol ")"
                 return $ TVK n
          "dhpk" -> do
                 symbol "("
                 n <- parseNameExp
                 symbol ")"
                 return $ TDH_PK n
          "encpk" -> do
                 symbol "("
                 n <- parseNameExp
                 symbol ")"
                 return $ TEnc_PK n
          "shared_secret" -> do
                 symbol "("
                 n <- parseNameExp
                 symbol ","
                 m <- parseNameExp
                 symbol ")"
                 return $ TSS n m
          _ -> parserZero
    )
    <|>
    (try $ parseSpanned $ do
        x <- identifier
        symbol ":"
        t <- parseTy
        symbol "{"
        p <- parseProp
        symbol "}"
        return $ TRefined t x $ bind (s2n x) p 
    )
    <|>
    (parseSpanned $ do
        x <- parsePath
        ps' <- optionMaybe parseParams
        let ps = case ps' of
                   Nothing -> []
                   Just xs -> xs
        return $ TConst x ps
    )

  

uniq :: Eq a => [a] -> Bool
uniq [] = True
uniq (x:xs) = not (elem x xs) && uniq xs
  
parseEnum = parseSpanned $ do
        reserved "enum"
        n <- identifier
        is <- parseIdxParamBinds1
        symbol "{"
        xs <- many1 $ do
          symbol "|"
          c <- identifier
          t <- optionMaybe parseTy
          return (c, t)
        symbol "}"
        whiteSpace
        if uniq (map fst xs) then 
            return $ DeclEnum n $ bind is xs
        else fail $ "Duplicate cases in enum " ++ n

parseStruct = parseSpanned $ do
    reserved "struct"
    n <- identifier                                                                  
    is <- parseIdxParamBinds1 
    symbol "{"
    xs <- (do
        s <- identifier
        symbol ":"
        t <- parseTy
        return (s, t)) `sepBy` (symbol ",")
    symbol "}"
    if uniq (map fst xs) then 
        return $ DeclStruct n $ bind is xs
    else fail $ "Duplicate cases in struct " ++ n
        
parseProp :: Parser Prop
parseProp = buildExpressionParser parsePropTable parsePropTerm

parsePropTerm :: Parser Prop
parsePropTerm = 
     parensPos parseProp <|> 
        (parseSpanned $ do
            reserved "True"
            return PTrue)   
        <|>
        (parseSpanned $ do
            reserved "False"
            return PFalse)
        <|>
        (parseSpanned $ do
            reserved "corr"
            symbol "("
            ne <- parseNameExp
            symbol ")"
            return $ PFlow (Spanned (_spanOf ne) $ LName ne) advLbl
        )
        <|>
        (parseSpanned $ do
            p <- getPosition
            reserved "sec"
            symbol "("
            ne <- parseNameExp
            symbol ")"
            p' <- getPosition
            return $ PNot $ Spanned (ignore $ mkPos p p') $ PFlow (Spanned (_spanOf ne) $ LName ne) advLbl
        )
        <|>
        (parseSpanned $ do
            reserved "ro"
            symbol "("
            a <- parseAExpr
            symbol ","
            b <- parseAExpr
            symbol ";"
            oi <- optionMaybe $ many1 digit
            symbol ")"
            let i = case oi of
                      Nothing -> 0
                      Just i -> read i
            return $ PRO a b i
        )
        <|>         
        (parseSpanned $ do
            reserved "let"
            x <- identifier
            symbol "="
            a <- parseAExpr
            reserved "in"
            p <- parseProp
            return $ PLetIn a (bind (s2n x) p)
        )
        <|>
        (try $ parseSpanned $ do
            t <- parseAExpr
            symbol "=="
            t2 <- parseAExpr
            return $ PEq t t2)
        <|>
        (try $ parseSpanned $ do
            pbegin <- getPosition
            t <- parseAExpr
            symbol "!="
            t2 <- parseAExpr
            pend <- getPosition
            return $ PNot $ Spanned (ignore $ mkPos pbegin pend) $ PEq t t2)
        <|>
        (try $ parseSpanned $ do
            t <-  parseIdx
            symbol "=idx"
            t2 <- parseIdx
            return $ PEqIdx t t2)
        <|>
        (try $ parseSpanned $ do
            l1 <- parseLabel
            symbol "<="
            l2 <- parseLabel
            return $ PFlow l1 l2
        )
        <|>
        (try $ parseSpanned $ do
            pbegin <- getPosition
            l1 <- parseLabel
            symbol "!<="
            l2 <- parseLabel
            pend <- getPosition
            return $ PNot $ Spanned (ignore $ mkPos pbegin pend) $ PFlow l1 l2
        )
        <|>
        (parseSpanned $ do
            reserved "happened"
            symbol "("
            s <- parsePath
            inds <- parseIdxParams
            symbol "("
            xs <- (parseAExpr `sepBy` (symbol ","))
            symbol ")"
            symbol ")"
            return $ PHappened s inds xs
        )
        <|>
        (parseSpanned $ do
            q <- parseQuant
            bs <- parseQuantBinders
            symbol "."
            p <- parseProp
            return $ (mkQuant q bs p)^.val
        )
        <|>
        (parseSpanned $ do
            reserved "aad"
            symbol "("
            ne <- parseNameExp
            symbol ")"
            symbol "["
            x <- parseAExpr
            symbol "]"
            return $ PAADOf ne x
            )
        <|>
        (parseSpanned $ try $ do
            p <- parsePath
            is <- parseIdxParams1
            symbol "["
            xs <- (parseAExpr `sepBy` (symbol ","))
            symbol "]"
            return $ PApp p is xs
            )
        <|>
        (parseSpanned $ try $ do
            e <- parseAExpr
            return $ PEq e (builtinFunc "true" []) 
        )

parseQuant = 
    (do
        reserved "forall"
        return $ Forall
    )
    <|>
    (do
        reserved "exists"
        return $ Exists
    )

data BinderType = BTIdx | BTBV
    deriving Eq

parseQuantBinders = 
    (do
        i <- identifier
        symbol ":"
        bt <- alt
            (reserved "idx" >> return BTIdx)
            (reserved "bv" >> return BTBV)
        return (i, bt)) `sepBy1` (symbol ",")

mkQuant :: Quant -> [(String, BinderType)] -> Prop -> Prop
mkQuant q [] p = p
mkQuant q ((i, bt):bs) p = case bt of
    BTIdx -> mkSpanned $ PQuantIdx q $ bind (s2n i) $ mkQuant q bs p
    BTBV -> mkSpanned $ PQuantBV q $ bind (s2n i) $ mkQuant q bs p

mkEForall :: [(String, BinderType)] -> Expr -> Expr
mkEForall [] e = e
mkEForall ((i, bt):bs) k = case bt of
    BTIdx -> mkSpanned $ EForallIdx $ bind (s2n i) $ mkEForall bs k
    BTBV -> mkSpanned $ EForallBV $ bind (s2n i) $ mkEForall bs k


prefixProp op f =
    Prefix (do
        p <- getPosition
        reservedOp op
        return $ \x -> mkSpannedWith (prefixPosition p (unignore $ x^.spanOf)) $ f x
        )

infixProp op f assoc = 
    Infix (do
        symbol op
        return $ \x y -> mkSpannedWith (joinPosition (unignore $ x^.spanOf) (unignore $ y^.spanOf)) (f x y)) assoc 

pIff :: Prop -> Prop -> PropX
pIff p1 p2 = PAnd (mkSpanned $ PImpl p1 p2) (mkSpanned $ PImpl p2 p1)

parsePropTable = [ 
    [ prefixProp "!" PNot ], 
    [ infixProp "/\\" PAnd AssocLeft ],
    [ infixProp "\\/" POr AssocLeft ],
    [ infixProp "==>" PImpl AssocRight ],
    [ infixProp "<==>" pIff AssocNone ]
                 ]

parseNoncePattern = 
    (symbol "*" >> return NPHere)

parseNameType = 
    parensPos parseNameType <|>
    (parseSpanned $ do
        reserved "DH"
        return NT_DH)
    <|>
    (parseSpanned $ do
        reserved "nonce"
        return NT_Nonce)
    <|>
    (parseSpanned $ do
        reserved "sigkey"
        t <- parseTy
        return $ NT_Sig t)
    <|>
    (parseSpanned $ do
        reserved "enckey"
        t <- parseTy
        return $ NT_Enc t)
    <|>
    (parseSpanned $ do
        reserved "st_aead"
        t <- parseTy
        symbol "aad"
        x <- identifier
        symbol "."
        pr <- parseProp
        reserved "nonce"
        p <- parsePath
        reserved "nonce_pattern"
        np <- parseNoncePattern
        return $ NT_StAEAD t (bind (s2n x) pr) p np
    )
    <|>
    (parseSpanned $ do
        reserved "pkekey"
        t <- parseTy
        return $ NT_PKE t)
    <|>
    (parseSpanned $ do
        reserved "mackey"
        t <- parseTy
        return $ NT_MAC t)
    <|>
    (parseSpanned $ do
        reserved "prf"
        symbol "{"
        vals <- (do
            l <- identifier
            symbol ":"
            ae <- parseAExpr
            symbol "->"
            nt <- parseNameType
            return (l, (ae, nt))) `sepBy` (symbol ",")
        symbol "}"
        return $ NT_PRF vals)



parseLocality :: Parser Locality
parseLocality = do
    x <- parsePath
    ys <- optionMaybe $ do
        symbol "<"
        is <- (parseIdx `sepBy` (symbol ","))
        symbol ">"
        return is
    return $ Locality x $ concat ys 

parseNameDecl = 
    parseSpanned $ do
        reserved "name"
        n <- identifier
        inds <- parseIdxParamBinds
        namedecl_body <- parseNameDeclBody
        return $ DeclName n $ bind inds namedecl_body

parseRequires :: Parser (Maybe Prop)
parseRequires = do
    ps <- many $ do
        reserved "requires"
        parseProp
    return $ case ps of
                [] -> Nothing
                _ -> Just $ foldl1 pAnd ps

parseNameDeclBody =
    (do
        symbol ":"
        ((do
            reserved "RO"
            xs_ <- optionMaybe $ do
                symbol "["
                xs <- (identifier `sepBy1` (symbol ","))
                symbol "]"
                return $ map s2n xs
            let xs = case xs_ of
                       Nothing -> []
                       Just v -> v
            ostrict <- optionMaybe $ do
                reserved "strict"
                optionMaybe $ do
                    symbol "{"
                    i <- (many1 digit) `sepBy1` (symbol ",")
                    symbol "}"
                    return $ map read i
            let strictness = case ostrict of
                               Just oi -> ROStrict oi
                               Nothing -> ROUnstrict
            e <- parseAExpr
            symbol "->"
            nts <- parseNameType `sepBy1` (symbol "||")
            oreq <- parseRequires
            let req = case oreq of
                        Nothing -> pTrue
                        Just v -> v
            olem <- optionMaybe $ do
                reserved "uniqueness_by"
                parseExpr
            let lem = case olem of
                        Nothing -> mkSpanned $ ERet $ mkSpanned $ AEApp (topLevelPath "unit") [] []
                        Just l -> l
            return $ DeclRO strictness (bind xs (e, req, nts, lem))
         )
         <|>
         (do
             nt <- parseNameType
             symbol "@"
             nl <- parseLocality `sepBy1` (symbol ",")
             return $ DeclBaseName nt nl)))
    <|>
    (return $ DeclAbstractName)
    
 
parseDecls = 
    many $ 
    parseNameDecl 
    <|>
    parseEnum
    <|>
    parseStruct
    <|>
    (parseSpanned $ do
        reserved "set_option"
        char '\"'
        s1 <- many $ alphaNum <|> oneOf ":_-."
        char '\"'
        whiteSpace
        char '\"'
        s2 <- many $ alphaNum <|> oneOf ":_-."
        char '\"'
        whiteSpace
        return $ DeclSMTOption s1 s2
        )
    <|>
    (parseSpanned $ do
        reserved "include"
        whiteSpace
        char '"'
        s <- many (noneOf "\"")
        char '"'
        whiteSpace
        return $ DeclInclude s
    )
    <|>
    (parseSpanned $ do
        reserved "counter"
        x <- identifier
        inds <- parseIdxParamBinds
        symbol "@"
        l <- parseLocality
        return $ DeclCounter x (bind inds l)
    )
    <|>
    (parseSpanned $ do
        reserved "def"
        n <- identifier
        inds <- parseIdxParamBinds
        parseRegularDef n inds <|> parseHeader n inds
    )
    <|>
    (parseSpanned $ do
        reserved "type"
        n <- identifier
        t <- optionMaybe $ do
            symbol "="
            parseTy
        return $ DeclTy n t
    )
    <|>
    (parseSpanned $ do
        reserved "predicate"
        n <- identifier
        ps <- parseIdxParamBinds1
        symbol "("
        xs <- identifier `sepBy` (symbol ",")
        symbol ")"
        symbol "="
        p <- parseProp
        return $ DeclPredicate n (bind (ps, map s2n xs) p)
    )
    <|>
    (parseSpanned $ do
        reserved "func"
        n <- identifier
        alt
            (do
                reserved "arity"
                whiteSpace
                i <- many1 digit
                whiteSpace
                return $ DeclDetFunc n UninterpFunc (read i))
            (do
                ps <- parseIdxParamBinds
                symbol "("
                xs <- identifier `sepBy` (symbol ",")
                symbol ")"
                symbol "="
                a <- parseAExpr
                return $ DeclFun n (bind (ps, map s2n xs) a))
    )
    <|>
    (parseSpanned $ do
        reserved "corr"
        pb <- parseIdxParamBinds1
        alt
            (try $ do
                symbol "["
                xs <- identifier `sepBy1` (symbol ",")
                symbol "]"
                l1 <- parseLabel
                symbol "==>"
                l2 <- parseLabel
                return $ DeclCorr $ bind (pb, map s2n xs) (l1, l2))
            (do
                l1 <- parseLabel
                symbol "==>"
                l2 <- parseLabel
                return $ DeclCorr $ bind (pb, []) (l1, l2))
    )
    <|>
    (try $ parseSpanned $ do
        reserved "locality"
        nl <- identifier
        symbol "="
        p <- parsePath
        return $ DeclLocality nl (Right p)
    )
    <|>
    (parseSpanned $ do
        reserved "locality"
        nl <- identifier
        oi <- optionMaybe $ do
            symbol ":"
            whiteSpace
            i <- many1 digit
            whiteSpace
            return $ read i
        let i = case oi of
                  Just i -> i
                  Nothing -> 0
        return $ DeclLocality nl (Left i))
    <|>
    (parseSpanned $ do
        reserved "table"
        n <- identifier
        symbol ":"
        t <- parseTy
        symbol "@"
        loc <- parseLocality
        return $ DeclTable n t loc)
    <|>
    (parseSpanned $ do       
        reserved "module"
        imt <- parseIsModType
        n <- identifier
        modArgs <- optionMaybe $ do
            symbol "("
            xs <- (do
                n <- identifier
                symbol ":"
                t <- parseModuleExp ModType $ "SPECOF" ++ n
                return (n, t)
                ) `sepBy1` (symbol ",")
            symbol ")"
            return xs
        omt <- optionMaybe $ do
            symbol ":"
            parseModuleExp ModType $ "TYPEOF" ++ n
        symbol "="
        me <- parseModuleExp imt n
        let (bdy, otype) = mkModuleBinders modArgs me omt 
        return $ DeclModule n imt bdy otype 
    )

parseRegularDef n inds = do
    symbol "("
    args <- (do
        x <- identifier
        symbol ":"
        t <- parseTy
        return $ (s2n x, embed t)
        ) `sepBy` (symbol ",")
    symbol ")"
    symbol "@"
    nl <- parseLocality
    preReq <- parseRequires
    symbol ":"
    tyAnn <- parseTy
    oe <- optionMaybe $ do
        symbol "="
        parseExpr
    return $ DeclDef n (bind inds $ (nl, bind args (preReq, tyAnn, oe)))

parseHeader n inds = do 
    symbol "@"
    nl <- parseLocality
    return $ DeclDefHeader n (bind inds nl)

mkModuleBinders :: Maybe [(String, ModuleExp)] -> ModuleExp -> Maybe ModuleExp -> (ModuleExp, Maybe ModuleExp)
mkModuleBinders Nothing me omt = (me, omt)
mkModuleBinders (Just xs) me omt = 
    (go xs me, fmap (go xs) omt)
        where
            go :: [(String, ModuleExp)] -> ModuleExp -> ModuleExp
            go [] m = m
            go ((x, t) : xs) m = 
                let k = go xs m in
                let p = joinPosition (unignore $ _spanOf t) (unignore $ _spanOf k) in 
                Spanned (ignore p) $ ModuleFun $ bind (s2n x, x, embed t) $ k 


parseIsModType :: Parser IsModuleType
parseIsModType = do
    ot <- optionMaybe $ reserved "type"
    return $ case ot of
                    Just _ -> ModType
                    Nothing -> ModConcrete
    
parseModuleExp :: IsModuleType -> String -> Parser ModuleExp
parseModuleExp imt n = 
    parensPos (parseModuleExp imt n)
    <|>
    (parseSpanned $ do
        symbol "{"
        ds <- parseDecls
        symbol "}"
        return $ ModuleBody imt (bind (s2n $ "%mod_" ++ n) ds) 
    )
    <|>
    (parseSpanned $ do
        reserved "functor"
        symbol "("
        m <- identifier
        symbol ":"
        nt <- parseModuleExp ModType ("TYPEOF" ++ m)
        symbol ")"
        symbol "=>"
        mb <- parseModuleExp imt n
        return $ ModuleFun $ bind (s2n m, m, embed nt) mb
    )
    <|>
    parseAppChain imt n

parseAppChain :: IsModuleType -> String -> Parser ModuleExp
parseAppChain imt n = parseSpanned $ do
    p <- parsePath
    oargs <- optionMaybe $ do
        symbol "("
        xs <- (parsePath `sepBy1` (symbol ","))
        symbol ")"
        return xs
    case oargs of
      Nothing -> return $ ModuleVar p
      Just ps -> return $ mkModuleApp (mkSpanned $ ModuleVar p) ps
  where
      mkModuleApp :: ModuleExp -> [Path] -> ModuleExpX
      mkModuleApp m [] = error "empty mkModuleapp"
      mkModuleApp m [x] = ModuleApp m x
      mkModuleApp m (x : xs) = mkModuleApp (mkSpanned $ ModuleApp m x) xs




parseDebugCommand = 
    (try $ do
        whiteSpace
        char '"'
        cs <- many (noneOf "\"")
        char '"'
        whiteSpace
        return $ DebugPrint cs
    )
    <|>
    (try $ do
        reserved "printTyOf"
        symbol "("
        a <- parseAExpr
        symbol ")"
        return $ DebugPrintTyOf a
    )
    <|>
    (try $ do
        reserved "resolveANF"
        symbol "("
        a <- parseAExpr
        symbol ")"
        return $ DebugResolveANF a
    )
    <|>
    (try $ do
        reserved "printTy"
        symbol "("
        t <- parseTy
        symbol ")"
        return $ DebugPrintTy t
    )
    <|>
    (try $ do
        reserved "printProp"
        symbol "("
        p <- parseProp
        symbol ")"
        return $ DebugPrintProp p
        )
    <|>
    (try $ do
        reserved "printTyContext"
        o <- optionMaybe $ symbol "noanf"
        let b = case o of
                  Nothing -> True
                  Just _ -> False
        return $ DebugPrintTyContext b
    )
    <|>
    (try $ do
        reserved "printModules"
        return $ DebugPrintModules
    )
    <|>
    (try $ do
        reserved "printExpr"
        symbol "("
        e <- parseExpr
        symbol ")"
        return $ DebugPrintExpr e
    )
    <|>
    (try $ do
        reserved "printLabel"
        symbol "("
        l <- parseLabel
        symbol ")"
        return $ DebugPrintLabel l
    )

varNameSuggest :: Expr -> String
varNameSuggest e = 
    let line = fst $ begin $ unignore $ e^.spanOf in
    case e^.val of
      EAssert _ -> "_assert_" ++ show line
      EAssume _ -> "_assume_" ++ show line
      _ -> "_"

parseExpr = buildExpressionParser parseExprTable parseExprTerm
parseExprTable = 
    [ [ Infix (do
    symbol ";" 
    return (\e1 e2 -> mkSpannedWith (joinPosition (unignore $ e1^.spanOf) (unignore $ e2^.spanOf)) $ ELet e1 Nothing Nothing (varNameSuggest e1) (bind (s2n $ varNameSuggest e1) e2))
              )
    AssocLeft ] ]

parseExprBlock :: Parser Expr
parseExprBlock = do
    p <- getPosition
    symbol "{"
    v <- parseExpr
    symbol "}"
    p' <- getPosition
    return $ Spanned (ignore $ Position (sourceLine p, sourceColumn p) (sourceLine p', sourceColumn p') (sourceName p)) $ EBlock v

parseExprTerm = 
    (try $ do -- Short circuit for ()
        p <- getPosition
        char '('
        char ')'
        p' <- getPosition
        whiteSpace
        return $ Spanned (ignore $ mkPos p p') $ ERet $ Spanned (ignore $ mkPos p p') (AEApp (topLevelPath "unit") [] [])
        )
    <|>
    parensPos parseExpr
    <|>
    parseExprBlock 
    <|>
    (parseSpanned $ do
        reserved "input"
        x <- identifier
        oy <- optionMaybe $ do
            symbol ","
            y <- identifier
            return y
        let y = case oy of
                  Nothing -> "_"
                  Just y -> y
        reserved "in"
        e <- parseExpr
        return $ EInput x $ bind (s2n x, s2n y) e
    )
    <|>
    (parseSpanned $ do
        reserved "get_counter"
        p <- parsePath
        ps <- parseIdxParams
        return $ EGetCtr p ps
    )
    <|>
    (parseSpanned $ do
        reserved "inc_counter"
        p <- parsePath
        ps <- parseIdxParams
        return $ EIncCtr p ps
    )
    <|>
    (parseSpanned $ do
        cop <- parseCryptOp
        symbol "("
        as <- parseArgs
        symbol ")"
        return $ ECrypt cop as
    )
    <|>
    (parseSpanned $ do 
        reserved "output" 
        ae <- parseAExpr 
        l <- optionMaybe $ do
            reserved "to"
            x <- parseEndpoint
            return x
        return $ EOutput ae l
    )
    <|>
    (parseSpanned $ do
        reserved "admit"
        return EAdmit
    )
    <|>
    (parseSpanned $ do
        reserved "debug"
        dc <- parseDebugCommand
        return $ EDebug dc
    )
    <|>
    (parseSpanned $ do
        reserved "set_option"
        char '\"'
        s1 <- many $ alphaNum <|> oneOf ":_-."
        char '\"'
        whiteSpace
        char '\"'
        s2 <- many $ alphaNum <|> oneOf ":_-."
        char '\"'
        whiteSpace
        reserved "in"
        e <- parseExpr
        return $ ESetOption s1 s2 e
    )
    <|>
    (parseSpanned $ do
        reserved "union_case"
        x <- identifier
        reservedOp "="
        a <- parseAExpr
        reserved "in"
        e <- parseExpr
        return $ EUnionCase a x $ bind (s2n x) e
    )
    <|>
    (do
        p <- getPosition
        reserved "let"
        xts <- ((do
                x <- identifier
                tyAnn <- optionMaybe $ do
                    symbol ":"
                    parseTy
                return (x, tyAnn))
            `sepBy` (reservedOp ","))
        reservedOp "="
        es <- parseExpr `sepBy` (reservedOp ",")
        reserved "in"
        p' <- getPosition
        e' <- parseExpr
        if length xts /= length es then fail "must have same number of binders and expressions" else
            let f k ((x, tyAnn), e) = Spanned (ignore $ mkPos p p') $ ELet e tyAnn Nothing x $ bind (s2n x) k in
            return $ foldl f e' $ zip xts es
    )
    <|>
    (parseSpanned $ do
        reserved "unpack"
        i <- identifier
        symbol ","
        x <- identifier
        reservedOp "="
        a <- parseAExpr
        reserved "in"
        e <- parseExpr
        return $ EUnpack a $ bind (s2n i, s2n x) e)
    <|>
    (parseSpanned $ do
        reserved "choose_idx"
        i <- identifier
        symbol "|"
        p <- parseProp
        reserved "in"
        k <- parseExpr
        return $ EChooseIdx (bind (s2n i) p) $ bind (s2n i) k)
    <|>
    (parseSpanned $ do
        reserved "call"
        x <- parsePath
        inds <- parseIdxParams
        symbol "("
        args <- parseArgs
        symbol ")"
        return $ ECall x inds args)
    <|>
    (parseSpanned $ do
        reserved "if"
        t <- parseAExpr
        reserved "then"
        e1 <- parseExpr
        reserved "else"
        e2 <- parseExpr
        return $ EIf t e1 e2)
    <|>
    (parseSpanned $ do
        reserved "forall"
        bs <- parseQuantBinders
        symbol "{"
        k <- parseExpr
        symbol "}"
        return $ (mkEForall bs k)^.val
    )
    <|>
    (parseSpanned $ do
        reserved "guard"
        a <- parseAExpr
        reserved "in"
        e <- parseExpr
        return $ EGuard a e
    )
    <|>
    (parseSpanned $ do
        reserved "case"
        x <- parseExpr
        symbol "{"
        xs <- many1 $ do
          symbol "|"
          c <- identifier
          ov <- optionMaybe identifier
          symbol "=>"
          e <- parseExpr
          return (c, case ov of
                       Nothing -> Left e
                       Just x -> Right (ignore x, bind (s2n x) e))
        symbol "}"
        return $ ECase x xs 
    )
    <|>
    (parseSpanned $ do
        reserved "assert"
        p <- parseProp
        return $ EAssert p
        )
    <|>
    (parseSpanned $ do
        reserved "assume"
        p <- parseProp
        return $ EAssume p
        )
    <|>
    (parseSpanned $ do
        reserved "corr_case"
        n <- parseNameExp
        op <- optionMaybe $ do
            reserved "when"
            parseProp
        reserved "in"
        e <- parseExpr
        return $ EPCase (pFlow (nameLbl n) advLbl) op e
        )
    <|>
    (parseSpanned $ do
        reserved "pcase"
        p <- parseProp
        op <- optionMaybe $ do
            reserved "when"
            parseProp
        reserved "in"
        e <- parseExpr
        return $ EPCase p op e
        )
    <|>
    (parseSpanned $ do
        reserved "false_elim"
        reserved "in"
        e <- parseExpr
        return $ EFalseElim e
        )
    <|>
    (parseSpanned $ do
        reserved "lookup"
        symbol "("
        n <- parsePath
        symbol ","
        a <- parseAExpr
        symbol ")"
        return $ ETLookup n a
    )
    <|>
    (parseSpanned $ do
        reserved "write"
        symbol "("
        n <- parsePath
        symbol ","
        a <- parseAExpr
        symbol ","
        a2 <- parseAExpr
        symbol ")"
        return $ ETWrite n a a2
    )
    <|>
    (parseSpanned $ do
        a <- parseAExpr
        return $ ERet a
        )

parseArgs :: Parser [AExpr]
parseArgs = 
    parseAExpr `sepBy` (reservedOp ",")

parseROHint :: Parser (Path, ([Idx], [Idx]), [AExpr])
parseROHint = do
    p <- parsePath
    inds <- parseIdxParams
    xs_ <- optionMaybe $ do
        symbol "["
        as <- parseAExpr `sepBy1` (symbol ",")
        symbol "]"
        return as
    let xs = case xs_ of
               Nothing -> []
               Just v -> v
    return (p, inds, xs)

parseCryptOp :: Parser CryptOp
parseCryptOp = 
    (do
        reserved "hash"
        ohints_idx <- optionMaybe $ do
            symbol "<"
            hs <- parseROHint `sepBy1` (symbol ",")
            idx_ <- optionMaybe $ do
                symbol ";"
                many1 digit
            let idx = case idx_ of
                        Nothing -> 0
                        Just v -> read v
            symbol ">"
            return (hs, idx)
        let (hints, idx) = case ohints_idx of
                             Nothing -> ([], 0)
                             Just v -> v
        return $ CHash hints idx
    )
    <|>
    (do
        reserved "prf"
        symbol "<"
        x <- identifier
        symbol ">"
        return $ CPRF x
    )
    <|>
    (do
        reserved "crh_lemma"
        return $ CLemma $ LemmaCRH 
    )
    <|>
    (do
        reserved "is_constant_lemma"
        return $ CLemma $ LemmaConstant 
    )
    <|>
    (do
        reserved "disjoint_not_eq_lemma"
        return $ CLemma $ LemmaDisjNotEq 
    )
    <|>
    (do
        reserved "cross_dh_lemma"
        symbol "<"
        x <- parseNameExp
        symbol ","
        y <- parseNameExp
        symbol ","
        z <- parseNameExp
        symbol ">"
        return $ CLemma $ LemmaCrossDH x y z
    )
    <|>
    (reserved "aenc" >> return CAEnc)
    <|>
    (reserved "adec" >> return CADec)
    <|>
    (do
        reserved "st_aead_enc"
        symbol "<"
        p <- parsePath
        inds <- parseIdxParams
        symbol ">"
        return $ CEncStAEAD p inds
    )
    <|>
    (reserved "st_aead_dec" >> return CDecStAEAD)
    <|>
    (reserved "pkenc" >> return CPKEnc)
    <|>
    (reserved "pkdec" >> return CPKDec)
    <|>
    (reserved "mac" >> return CMac)
    <|>
    (reserved "mac_vrfy" >> return CMacVrfy)
    <|>
    (reserved "sign" >> return CSign)
    <|>
    (reserved "vrfy" >> return CSigVrfy)

parseParam :: Parser FuncParam
parseParam = 
    (try $ do
        (reserved "label" <|> (symbol "l:" >> return ()) <|> (symbol "lbl:" >> return ()))
        l <- parseLabel
        return $ ParamLbl l)
    <|>
    (try $ do
        (reserved "aexp" <|> (symbol "a:" >> return ()))
        a <- parseAExpr
        return $ ParamAExpr a)
    <|>
    (try $ do
        (reserved "type" <|> (symbol "ty:" >> return ()))
        t <- parseTy
        return $ ParamTy t)
    <|>
    (try $ do
        reserved "idx"
        i <- parseIdx
        return $ ParamIdx i)
    <|>
    (try $ do
        reserved "name"
        i <- parseNameExp
        return $ ParamName i)
    <|>
    (try $ do
        s <- identifier
        return $ ParamStr s)

parseIdx :: Parser Idx
parseIdx = do
    p <- getPosition
    i <- identifier
    p' <- getPosition
    return $ IVar (ignore $ mkPos p p') (s2n i)

parseIdxParams :: Parser ([Idx], [Idx])
parseIdxParams = do
    inds <- optionMaybe $ do
        symbol "<"
        is <- parseIdx `sepBy` symbol ","
        ps <- optionMaybe $ do
            symbol "@"
            parseIdx `sepBy` symbol ","
        symbol ">"
        return (is, concat ps)
    return $ case inds of
               Nothing -> ([], [])
               Just (xs, ys) -> (xs, ys)

parseIdxParams1 :: Parser [Idx]
parseIdxParams1 = do
    inds <- optionMaybe $ do
        symbol "<"
        is <- parseIdx `sepBy` symbol ","
        symbol ">"
        return is
    return $ case inds of
               Nothing -> []
               Just xs -> xs

parseIdxParamsNoAngles :: Parser ([Idx], [Idx])
parseIdxParamsNoAngles = do
    inds <- optionMaybe $ do
        is <- parseIdx `sepBy` symbol ","
        ps <- optionMaybe $ do
            symbol "@"
            parseIdx `sepBy` symbol ","
        return (is, concat ps)
    return $ case inds of
               Nothing -> ([], [])
               Just (xs, ys) -> (xs, ys)

parseIdxParamBinds1 :: Parser [IdxVar]
parseIdxParamBinds1 = do
    inds <- optionMaybe $ do
        symbol "<"
        is <- identifier `sepBy` symbol ","
        symbol ">"
        return $ map s2n is
    return $ case inds of
               Nothing -> []
               Just xs -> xs 

parseIdxParamBinds :: Parser ([IdxVar], [IdxVar])
parseIdxParamBinds = do
    inds <- optionMaybe $ do
        symbol "<"
        is <- identifier `sepBy` symbol ","
        ps <- optionMaybe $ do
            symbol "@"
            identifier `sepBy` symbol ","
        symbol ">"
        return (is, concat ps)
    return $ case inds of
               Nothing -> ([], [])
               Just (xs, ys) -> (map s2n xs, map s2n ys)

parseEndpoint :: Parser Endpoint
parseEndpoint = 
    (do
        reserved "endpoint"
        symbol "("
        l <- parseLocality
        symbol ")"
        return $ EndpointLocality l
    )
    <|>
    (do
        x <- identifier
        return $ Endpoint $ s2n x
    )


parseParams :: Parser [FuncParam]
parseParams = do
    symbol "<"
    ps <- parseParam `sepBy` (symbol ",")
    symbol ">"
    return ps

infixAExpr name fname assoc = 
    Infix (do
        try $ symbol name
        return $ \e1 e2 -> mkSpannedWith (joinPosition (unignore $ e1^.spanOf) (unignore $ e2^.spanOf)) $ AEApp (topLevelPath fname) [] [e1, e2]
          ) assoc


parseAExpr :: Parser AExpr
parseAExpr = buildExpressionParser parseAExprTable parseAExprTerm
parseAExprTable = 
    [ 
        [ infixAExpr "*" "mult" AssocLeft ],
        [ infixAExpr "++" "concat" AssocLeft ],
        [ infixAExpr "&&" "andb" AssocLeft ],
        [ infixAExpr "+" "plus" AssocLeft ]
    ]

parseAExprTerm =           
    (try $ do
        p <- getPosition
        char '('
        char ')'
        p' <- getPosition
        whiteSpace
        return $ Spanned (ignore $ mkPos p p') $ AEApp (topLevelPath $ "unit") [] []
    )
    <|>
    parensPos parseAExpr
    <|>
    (parseSpanned $ do
        reserved "true"
        return $ AEApp (topLevelPath $ "true") [] []
    )
    <|>
    (parseSpanned $ do
        reserved "false"
        return $ AEApp (topLevelPath $ "false") [] []
    )
    <|>
    (parseSpanned $ do
        whiteSpace
        x <- digit
        case x of 
          '0' -> do
              y <- optionMaybe $ try $ digit <|> char 'x'
              whiteSpace
              case y of
                Nothing -> return $ AEInt 0
                Just 'x' -> do
                    z <- many hexDigit
                    whiteSpace
                    return $ AEHex z
                Just y' -> do
                    z <- many1 digit
                    whiteSpace
                    return $ AEInt $ read $ x : y' : z
          _ -> do
                z <- many digit
                whiteSpace
                return $ AEInt $ read $ x : z
    )             
    <|>
    (parseSpanned $ do
        symbol "|"
        x <- many1 (alphaNum <|> oneOf "_'")
        symbol "|"
        return $ AELenConst x
    )
    <|>
    (parseSpanned $ do 
        reserved "preimage"
        symbol "("
        p <- parsePath
        ps <- parseIdxParams
        oargs <- optionMaybe $ do
            symbol "["
            as <- parseAExpr `sepBy1` (symbol ",")
            symbol "]"
            return as
        symbol ")"
        let args = case oargs of
                     Nothing -> []
                     Just as -> as
        return $ AEPreimage p ps args
        )
    <|>
    (parseSpanned $ do 
        reserved "get"
        symbol "("
        ne <- parseNameExp
        symbol ")"
        return $ AEGet ne
        )
    <|>
    (parseSpanned $ do 
        reserved "get_encpk"
        symbol "("
        ne <- parseNameExp
        symbol ")"
        return $ AEGetEncPK ne
        )
    <|>
    (parseSpanned $ do 
        reserved "get_vk"
        symbol "("
        ne <- parseNameExp
        symbol ")"
        return $ AEGetVK ne
        )
    <|>
    (parseSpanned $ do 
        reserved "pack"
        symbol "<"
        i <- parseIdx
        symbol ">"
        symbol "("
        a <- parseAExpr
        symbol ")"
        return $ AEPackIdx i a
        )
    <|>
    (try $ parseSpanned $ do
        x <- parsePath
        op <- optionMaybe parseParams
        symbol "(" 
        args <- parseArgs
        symbol ")"
        let ps = case op of
                   Just ps -> ps
                   Nothing -> []
        return $ AEApp x ps args)
    <|>
    (parseSpanned $ do
        x <- identifier
        return $ AEVar (ignore x) (s2n x))

parseFile :: Parser [Decl]
parseFile = do
    whiteSpace
    ds <- parseDecls
    whiteSpace
    eof
    return ds


-- Parser for Z3 return values

data Z3Result = Z3Result {
    _isUnsat :: Bool,
    _z3Stats :: M.Map String String
                         }

smtIdentifier :: Parser String
smtIdentifier = many1 (alphaNum <|> oneOf "_-.=!")

parseZ3Result :: Parser Z3Result
parseZ3Result = do
    res <- 
        (try $ do
           string "unsat"
           return True)
        <|>
        (do
           string "sat" <|> string "unknown"
           return False)
    whiteSpace
    xs <- parseStatistics
    return $ Z3Result res (M.fromList xs)
    where
        parseStatistics = do
            char '('
            res <- many $ do
                char ':'
                s <- smtIdentifier
                whiteSpace
                t <- smtIdentifier
                whiteSpace
                return (s, t)
            char ')'
            return res



        

