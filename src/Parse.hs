module Parse where

import Debug.Trace
import Numeric
import Data.Char
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
import Pretty

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
                , P.reservedNames  = ["adv",  "ghost", "Ghost", "bool", "Option", "name", "Name",  "SecName", "PubName", "st_aead",  "mackey", "sec", "st_aead_enc", "st_aead_dec", "let", "DH", "nonce", "if", "then", "else", "enum", "Data", "sigkey", "type", "Unit", "Lemma", "random_oracle", "return", "corr", "RO", "debug", "assert",  "assume", "admit", "ensures", "true", "false", "True", "False", "call", "static", "corr_case", "false_elim", "union_case", "exists", "get",  "getpk", "getvk", "pack", "def", "Union", "pkekey", "pke_sk", "pke_pk", "label", "aexp", "type", "idx", "table", "lookup", "write", "unpack", "to", "include", "maclen",  "begin", "end", "module", "aenc", "adec", "pkenc", "pkdec", "mac", "mac_vrfy", "sign", "vrfy", "prf",  "PRF", "forall", "bv", "pcase", "choose_idx", "choose_bv", "crh_lemma", "ro", "is_constant_lemma", "strict", "aad", "Const", "proof", "gkdf"]
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

-- parseKDFSelector :: Parser KDFSelector
-- parseKDFSelector = do
--     i <- many1 digit
--     ps <- parseIdxParams1
--     return (read i, ps)

parseNameExp :: Parser NameExp
parseNameExp = 
     (parseSpanned $ do
         reserved "Extract"
         symbol "<"
         nt <- parseNameType
         symbol ">"
         symbol "("
         a <- parseAExpr
         symbol ","
         b <- parseAExpr
         symbol ")"
         return $ ExtractName a b nt (ignore False)
     )
     <|>
     (parseSpanned $ do
         reserved "Expand"
         symbol "<"
         nks <- parseNameKind `sepBy1` (symbol "||")
         symbol ";"
         j <- many1 digit
         symbol ";"
         nt <- parseNameType
         symbol ">"
         symbol "("
         a <- parseAExpr
         symbol ","
         b <- parseAExpr
         symbol ")"
         return $ ExpandName a b nks (read j) nt (ignore False)
     )
    <|>
    (parseSpanned $ do
        i <- parsePath
        ps <- parseIdxParams 
        oxs <- optionMaybe $ do
                symbol "["
                xs <- parseAExpr `sepBy1` (symbol ",")
                symbol "]"
                return xs
        let xs = case oxs of
                   Just v -> v
                   Nothing -> []
        return $ NameConst ps i xs) 

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
          reserved "ghost";
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
        reserved "Unit"
        return $ TUnit)
    <|>
    (parseSpanned $ do
        reserved "Const"
        symbol "("
        symbol "0"
        symbol "x"
        z <- many hexDigit
        symbol ")"
        return $ THexConst z)
    <|>
    (parseSpanned $ do
        reserved "Lemma"
        symbol "{"
        p <- parseProp
        symbol "}"
        return $ TRefined tUnit "._" $ bind (s2n "._") p)
    <|>
    (parseSpanned $ do
        reserved "Ghost"
        return $ TGhost)
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
    (do
        p <- getPosition
        reserved "SecName"
        symbol "("
        n <- parseNameExp
        symbol ")"
        p' <- getPosition
        let pos = ignore $ Position (sourceLine p, sourceColumn p) (sourceLine p', sourceColumn p') (sourceName p)
        return $ Spanned pos $ TRefined (Spanned pos $ TName n) ("._") $ bind (s2n "._") $ pNot $ pFlow (nameLbl n) advLbl
    )
    <|>
    (do
        p <- getPosition
        reserved "PubName"
        symbol "("
        n <- parseNameExp
        symbol ")"
        p' <- getPosition
        let pos = ignore $ Position (sourceLine p, sourceColumn p) (sourceLine p', sourceColumn p') (sourceName p)
        return $ Spanned pos $ TRefined (Spanned pos $ TName n) ("._") $ bind (s2n "._") $ pFlow (nameLbl n) advLbl
    )
    <|>
    (parseSpanned $ do
        reserved "exists"
        i <- identifier
        symbol "."
        t <- parseTy
        return $ TExistsIdx i $ bind (s2n i) t 
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
    xs_ <- parseDepBind
    let xs = xs_ () 
    symbol "}"
    return $ DeclStruct n $ bind is xs
        
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
        -- <|>
        -- (parseSpanned $ do
        --     reserved "ro"
        --     symbol "("
        --     a <- parseAExpr
        --     symbol ","
        --     b <- parseAExpr
        --     symbol ";"
        --     oi <- optionMaybe $ many1 digit
        --     symbol ")"
        --     let i = case oi of
        --               Nothing -> 0
        --               Just i -> read i
        --     return $ PRO a b i
        -- )
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
            pbegin <- getPosition
            t <- parseIdx
            symbol "!=idx"
            t2 <- parseIdx
            pend <- getPosition
            return $ PNot $ Spanned (ignore $ mkPos pbegin pend) $ PEqIdx t t2)
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
        -- (parseSpanned $ do
        --     reserved "in_odh"
        --     symbol "("
        --     s <- parseAExpr
        --     symbol ","
        --     ikm <- parseAExpr
        --     symbol ","
        --     info <- parseAExpr
        --     symbol ")"
        --     return $ PInODH s ikm info
        --     )
        -- <|>
        (parseSpanned $ do
            reserved "honest_pk_enc"
            symbol "<"
            ne <- parseNameExp
            symbol ">"
            symbol "("
            a <- parseAExpr
            symbol ")"
            return $ PHonestPKEnc ne a
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
    BTIdx -> mkSpanned $ PQuantIdx q (ignore i) $ bind (s2n i) $ mkQuant q bs p
    BTBV -> mkSpanned $ PQuantBV q (ignore i) $ bind (s2n i) $ mkQuant q bs p

mkEForall :: [(String, BinderType)] -> Maybe Prop -> Expr -> Expr
mkEForall [(i, bt)] op k = case bt of
    BTIdx -> mkSpanned $ EForallIdx i $ bind (s2n i) $ (op, k)
    BTBV -> mkSpanned $ EForallBV i $ bind (s2n i) $ (op, k)
mkEForall ((i, bt):bs) op k = case bt of
    BTIdx -> mkSpanned $ EForallIdx i $ bind (s2n i) $ (Nothing, mkEForall bs op k)
    BTBV -> mkSpanned $ EForallBV i $ bind (s2n i) $ (Nothing, mkEForall bs op k)


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


parseNameType = 
    parensPos parseNameType <|>
    (parseSpanned $ do
        reserved "DH"
        return NT_DH)
    <|>
    (parseSpanned $ do
        reserved "nonce"
        olen <- optionMaybe $ try $ do
            symbol "|"
            x <- identifier
            symbol "|"
            return x
        let len = case olen of
                    Just v -> v
                    Nothing -> "nonce"
        return $ NT_Nonce len)
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
        oself <- optionMaybe identifier
        let self = case oself of
                     Nothing -> "%self"
                     Just v -> v
        symbol "."
        pr <- parseProp
        reserved "nonce"
        p <- parsePath
        opat <- optionMaybe $ do
            reserved "pattern"
            y <- identifier
            symbol "."
            a <- parseAExpr
            return $ bind (s2n y) a
        let pat = case opat of
                    Just v -> v
                    Nothing -> bind (s2n "._") $ aeVar' (s2n "._") 
        return $ NT_StAEAD t (bind (s2n x, s2n self) pr) p pat 
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
        reserved "extractkey"
        nt <- parseNameType
        return $ NT_ExtractKey nt)
    <|>
    (parseSpanned $ do
        reserved "expandkey"
        symbol "{"
        x <- identifier
        oy <- optionMaybe identifier
        let y = case oy of
                  Just v -> v
                  Nothing -> "%self"
        symbol "."
        expandCases <- expandCase `sepBy1` (symbol ",")
        symbol "}"
        return $ NT_ExpandKey (bind ((x, s2n x), (y, s2n y)) expandCases)
    )
    <|>
    (parseSpanned $ do
        p <- parsePath
        ps <- parseIdxParams
        oargs <- optionMaybe $ do
            symbol "("
            xs <- parseAExpr `sepBy` (symbol ",")
            symbol ")"
            return xs
        let as = case oargs of
                   Nothing -> []
                   Just v -> v
        return $ NT_App p ps as
    )

parseKDFStrictness = 
    (reserved "strict" >> return KDFStrict)
    <|>
    (reserved "public" >> return KDFPub)


expandCase :: Parser (Bind [(String, DataVar)] (Prop, [(KDFStrictness, NameType)]))
expandCase = do
    oxs <- optionMaybe $ do
        symbol "<"
        xs <- identifier `sepBy1` (symbol ",")
        symbol ">"
        return (map (\x -> (x, s2n x)) xs)
    let xs = case oxs of
               Nothing -> []
               Just vs -> vs
    p <- parseProp
    symbol "->"
    nts <- (do
        ostrict <- optionMaybe $ parseKDFStrictness
        nt <- parseNameType
        let strictness = case ostrict of 
                            Nothing -> KDFNormal
                            Just v -> v
        return (strictness, nt)) `sepBy` (symbol "||")
    return (bind xs (p, nts))

-- parseKDFHint :: Parser (NameExp, Int, Int)
-- parseKDFHint = do 
--     n <- parseNameExp
--     symbol "["
--     i <- many1 digit
--     symbol ","
--     j <- many1 digit
--     symbol "]"
--     return (n, read i, read j)

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
         nt <- parseNameType
         onl <- optionMaybe $ do
             symbol "@"
             parseLocality `sepBy1` (symbol ",")
         let nl = case onl of
                    Nothing -> []
                    Just v -> v
         return $ DeclBaseName nt nl)
    <|>
    (do
        oxs <- optionMaybe $ do
                symbol "["
                xs <- identifier `sepBy1` (symbol ",")
                symbol "]"
                return xs
        let xs = case oxs of
                   Just v -> v
                   Nothing -> []
        symbol "="
        ne2 <- parseNameExp
        return $ DeclAbbrev $ bind (map s2n xs) ne2
    )
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
        reserved "odh"
        n <- identifier
        ps <- parseIdxParamBinds
        symbol ":"
        ne1 <- parseNameExp
        symbol ","
        ne2 <- parseNameExp
        symbol "->"
        nt <- parseNameType
        return $ DeclODH n (bind ps $ (ne1, ne2, nt))
    )
    <|>
    (parseSpanned $ do
        reserved "nametype"
        n <- identifier
        ps <- parseIdxParamBinds
        oxs <- optionMaybe $ do
            symbol "("
            xs <- identifier `sepBy` (symbol ",")
            symbol ")"
            return xs
        let xs = case oxs of
                   Nothing -> []
                   Just v -> map s2n v
        symbol "="
        nt <- parseNameType
        return $ DeclNameType n (bind (ps, xs) nt)
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
    (parseSpanned $ do
        reserved "corr_group"
        pb <- parseIdxParamBinds1
        alt
            (try $ do
                symbol "["
                xs <- identifier `sepBy1` (symbol ",")
                symbol "]"
                ls <- parseLabel `sepBy1` (symbol ",")
                return $ DeclCorrGroup $ bind (pb, map s2n xs) ls)
            (do
                ls <- parseLabel `sepBy1` (symbol ",")
                return $ DeclCorrGroup $ bind (pb, []) ls)
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

parseDepBind :: Alpha a => Parser (a -> DepBind a)
parseDepBind = do
    args <- (do
        x <- identifier
        symbol ":"
        t <- parseTy
        return (s2n x, x, t)
        ) `sepBy` (symbol ",")
    return $ \x -> go args x
        where
            go [] x = DPDone x
            go ((n, s, t):args) x = DPVar t s (bind n $ go args x) 



parseRegularDef n inds = do
    symbol "("
    bndk <- parseDepBind
    symbol ")"
    symbol "@"
    nl <- parseLocality
    preReq <- parseRequires
    symbol ":"
    tyAnn <- parseTy
    oe <- optionMaybe $ do
        symbol "="
        parseExpr
    return $ DeclDef n (bind inds $ (nl, bndk (preReq, tyAnn, oe)))

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


parseAttribute = do
    symbol "#"
    symbol "["
    s <- many $ alphaNum <|> char '_' <|> space
    symbol "]"
    return s

parsePCaseAttribute = do
    o <- optionMaybe parseAttribute
    case o of
      Nothing -> return Nothing
      Just s ->
          case s of
            "assume false" -> return $ Just False
            "assume true" -> return $ Just True
            _ -> fail $ "Unknown attribute for PCase: " ++ s


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
        return $ DebugPrintTyOf (ignore a) a
    )
    <|>
    (try $ do
        reserved "checkStructMatches"
        symbol "(" 
        x <- parsePath
        op <- optionMaybe parseParams
        symbol "(" 
        args <- parseArgs
        symbol ")"
        symbol ")"
        let ps = case op of
                   Just ps -> ps
                   Nothing -> []
        return $ DebugCheckMatchesStruct args x ps
    )
    <|>
    (try $ do
        reserved "hasType"
        symbol "("
        a <- parseAExpr
        symbol ","
        t <- parseTy
        symbol ")"
        return $ DebugHasType (ignore a) a t
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
        reserved "decideProp"
        symbol "("
        p <- parseProp
        symbol ")"
        return $ DebugDecideProp p
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
        reserved "printPathCondition"
        return $ DebugPrintPathCondition
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
    oproof <- optionMaybe $ reserved "proof"
    let proof = case oproof of
                  Just _ -> True
                  Nothing -> False
    symbol "{"
    v <- parseExpr
    symbol "}"
    p' <- getPosition
    return $ Spanned (ignore $ Position (sourceLine p, sourceColumn p) (sourceLine p', sourceColumn p') (sourceName p)) $ EBlock v proof

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
        reserved "kdf"
        symbol "<"
        odhs <- parseODHAnn `sepBy` (symbol ",")
        symbol ";"
        ianns <- (do 
            i <- many1 digit
            iargs <- parseOptionArgs
            return (read i, iargs)
                  ) `sepBy` (symbol ",")
        symbol ";"
        nks <- parseNameKind `sepBy1` (symbol "||")
        symbol ";"
        j <- many1 digit
        symbol ">"
        symbol "("
        as <- parseArgs
        symbol ")"
        case as of
          [a1, a2, a3] -> 
            return $ ELet (mkSpanned $ ECrypt (CExtract odhs) [a1, a2]) Nothing Nothing "%res" $ 
                bind (s2n "%res") $ mkSpanned $ ECrypt (CExpand ianns nks (read j)) [aeVar "%res", a3]
          _ -> fail "kdf: must have three arguments"
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
    (do
        p <- getPosition
        reserved "let"
        alt
            (do
                reserved "ghost"
                x <- identifier 
                reservedOp "="
                a <- parseAExpr 
                reserved "in"
                p' <- getPosition
                e' <- parseExpr
                return $ Spanned (ignore $ mkPos p p') $ ELetGhost a x $ bind (s2n x) e')
            (do
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
                    return $ foldl f e' $ zip xts es))
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
        return $ EUnpack a (i, x) $ bind (s2n i, s2n x) e)
    <|>
    (parseSpanned $ do
        reserved "choose_idx"
        i <- identifier
        symbol "|"
        p <- parseProp
        reserved "in"
        k <- parseExpr
        return $ EChooseIdx i (bind (s2n i) p) $ bind (s2n i) k)
    <|>
    (parseSpanned $ do
        reserved "choose_bv"
        i <- identifier
        symbol "|"
        p <- parseProp
        reserved "in"
        k <- parseExpr
        return $ EChooseBV i (bind (s2n i) p) $ bind (s2n i) k)
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
        reserved "pack"
        symbol "<"
        i <- parseIdx
        symbol ">"
        symbol "("
        a <- parseExpr
        symbol ")"
        return $ EPackIdx i a
        )
    <|>
    (parseSpanned $ do
        reserved "forall"
        bs <- parseQuantBinders
        oAssume <- optionMaybe $ do
            reserved "assuming"
            parseProp
        symbol "{"
        k <- parseExpr
        symbol "}"
        return $ (mkEForall bs oAssume k)^.val
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
        ot <- optionMaybe $ do
            symbol "as"
            parseTy
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
        otk <- case ot of
                 Nothing -> return Nothing
                 Just t -> do 
                     symbol "otherwise"
                     symbol "=>"
                     k <- parseExpr
                     return $ Just (t, k)
        symbol "}"
        return $ ECase x otk xs 
    )
    <|>
    (parseSpanned $ do
        reserved "parse"
        a <- parseAExpr
        reserved "as"
        t <- parseTy
        symbol "("
        xs <- identifier `sepBy1` (symbol ",")
        symbol ")"
        reserved "in"
        k <- parseExpr
        ok <- optionMaybe $ do
            reserved "otherwise"
            parseExpr
        return $ EParse a t ok (bind (map (\x -> (s2n x, ignore x)) xs) k)

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
        attr <- parsePCaseAttribute
        ccase <- alt
                    (do
                        reserved "nameOf"
                        symbol "("
                        a <- parseAExpr
                        symbol ")"
                        return $ Left a
                    )
                    (do
                        n <- parseNameExp
                        return $ Right n
                    )
        op <- optionMaybe $ do
            reserved "when"
            parseProp
        reserved "in"
        e <- parseExpr
        return $ case ccase of
                   Left a -> ECorrCaseNameOf a op e
                   Right n  -> EPCase (pFlow (nameLbl n) advLbl) op attr e
    )
    <|>
    (parseSpanned $ do
        reserved "openTyOf"
        a <- parseAExpr
        reserved "in"
        e <- parseExpr
        return $ EOpenTyOf a e)
    <|>
    (parseSpanned $ do
        reserved "pcase"
        attr <- parsePCaseAttribute
        p <- parseProp
        op <- optionMaybe $ do
            reserved "when"
            parseProp
        reserved "in"
        e <- parseExpr
        return $ EPCase p op attr e
        )
    <|>
    (parseSpanned $ do
        reserved "false_elim"
        op <- optionMaybe $ do
            reserved "when"
            parseProp
        reserved "in"
        e <- parseExpr
        return $ EFalseElim e op
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

parseOptionArgs :: Parser [AExpr]
parseOptionArgs = do
    r <- optionMaybe $ do
        symbol "("
        res <- parseArgs
        symbol ")"
        return res
    case r of
      Nothing -> return []
      Just v -> return v


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

parseODHAnn = do
    s <- identifier
    p <- parseIdxParams
    return (s, p)



parseCryptOp :: Parser CryptOp
parseCryptOp = 
    (do
        reserved "extract"
        o <- optionMaybe $ do
            symbol "<"
            o <- parseODHAnn `sepBy1` (symbol ",")
            symbol ">"
            return o
        let odhs = case o of
                     Nothing -> []
                     Just v -> v
        return $ CExtract odhs 
    )
    <|>
    (do
        reserved "expand"
        symbol "<"
        ianns <- (do 
            i <- many1 digit
            iargs <- parseOptionArgs
            return (read i, iargs)
                  ) `sepBy` (symbol ",")
        symbol ";"
        nks <- parseNameKind `sepBy1` (symbol "||")
        symbol ";"
        j <- many1 digit
        symbol ">"
        return $ CExpand ianns nks (read j))
    <|>
    (do
        reserved "crh_lemma"
        return $ CLemma $ LemmaCRH 
    )
    <|>
    -- (do
    --     reserved "kdf_inj_lemma"
    --     return $ CLemma $ LemmaKDFInj 
    -- )
    -- <|>
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
        symbol ">"
        return $ CLemma $ LemmaCrossDH x 
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
        opat <- optionMaybe $ do
            symbol ","
            reserved "pattern"
            x <- identifier
            symbol "."
            a <- parseAExpr
            return $ bind (s2n x) a
        symbol ">"
        let pat = case opat of
                    Just v -> v
                    Nothing -> bind (s2n "._") $ aeVar' (s2n "._") 
        return $ CEncStAEAD p inds pat
    )
    <|>
    (do
        reserved "st_aead_dec" 
        return $ CDecStAEAD)
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

parseNameKind =
    (reserved "extractkey" >> return NK_ExtractKey)
    <|>
    (reserved "expandkey" >> return NK_ExpandKey)
    <|>
    (reserved "enckey" >> return NK_Enc)
    <|>
    (reserved "mackey" >> return NK_MAC)
    <|>
    (do
        reserved "nonce" 
        olen <- optionMaybe $ try $ do
            symbol "|"
            x <- identifier
            symbol "|"
            return x
        let len = case olen of
                    Just v -> v
                    Nothing -> "nonce"
        return $ NK_Nonce len)

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
        ot <- try $ 
            (reserved "idx" >> return Nothing)
            <|>
            (reserved "session" >> (return $ Just IdxSession))
            <|>
            (reserved "pid" >> (return $ Just IdxPId))
        i <- parseIdx
        return $ ParamIdx i ot)
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
    return $ IVar (ignore $ mkPos p p') (ignore i) (s2n i)

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

prefixAExpr name fname = 
    Prefix (do
        try $ symbol name
        return $ \e -> mkSpannedWith (unignore $ e^.spanOf) $ AEApp (topLevelPath fname) [] [e]
          )


parseAExpr :: Parser AExpr
parseAExpr = buildExpressionParser parseAExprTable parseAExprTerm
parseAExprTable = 
    [ 
        [ infixAExpr "*" "mult" AssocLeft ],
        [ infixAExpr "++" "concat" AssocLeft ],
        [ infixAExpr "&&&" "andp" AssocLeft ],
        [ infixAExpr "&&" "andb" AssocLeft ],
        [ infixAExpr "+" "plus" AssocLeft ],
        [ prefixAExpr "!" "notb" ]
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
        char '\"'
        s <- many $ alphaNum <|> oneOf ":_-. \t"
        char '\"'
        whiteSpace
        return $ AEHex $ concat (map (\i -> showHex (ord i) "") s))
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
        reserved "gextract"
        symbol "("
        a <- parseAExpr
        symbol ","
        b <- parseAExpr
        symbol ")"
        return $ AE_Extract a b
    )
    <|>
    (parseSpanned $ do
        reserved "gexpand"
        symbol "<"
        nks <- parseNameKind `sepBy1` (symbol "||")
        symbol ";"
        j <- many1 digit
        symbol ">"
        symbol "("
        a <- parseAExpr
        symbol ","
        b <- parseAExpr
        symbol ")"
        return $ AE_Expand a b nks (read j) 
        )
    <|>
    (parseSpanned $ do
        reserved "gkdf"
        symbol "<"
        nks <- parseNameKind `sepBy1` (symbol "||")
        symbol ";"
        j <- many1 digit
        symbol ">"
        symbol "("
        a <- parseAExpr
        symbol ","
        b <- parseAExpr
        symbol ","
        c <- parseAExpr
        symbol ")"
        return $ AE_Expand (Spanned (ignore $ joinPosition (unignore $ a^.spanOf) (unignore $ b^.spanOf)) (AE_Extract a b))
                           c
                           nks
                           (read j))
    <|>
    --(parseSpanned $ do 
    --    reserved "preimage"
    --    symbol "("
    --    p <- parsePath
    --    ps <- parseIdxParams
    --    oargs <- optionMaybe $ do
    --        symbol "["
    --        as <- parseAExpr `sepBy1` (symbol ",")
    --        symbol "]"
    --        return as
    --    symbol ")"
    --    let args = case oargs of
    --                 Nothing -> []
    --                 Just as -> as
    --    return $ AEPreimage p ps args
    --    )
    -- <|>
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



        

