module Parse where

import Text.Parsec
import Text.Parsec.String
import Text.Parsec.Language
import Text.Parsec.Expr
import Data.Default (Default, def)
import qualified Text.Parsec.Token as P
import System.Environment
import Control.Lens ((^.))
import qualified Data.Map.Strict as M
import Error.Diagnose.Position
import qualified Data.Functor.Identity as I
import qualified Data.Set as S
import Unbound.Generics.LocallyNameless
import AST

owlStyle  :: P.LanguageDef st
owlStyle   = emptyDef
                { P.commentStart   = "/*"
                , P.commentEnd     = "*/"
                , P.commentLine    = "//"
                , P.nestedComments = True
                , P.identStart     = letter <|> char '_'
                , P.identLetter    = alphaNum <|> oneOf "_'?"
                , P.reservedNames  = ["adv",  "bool", "Option", "name", "Name", "enckey", "mackey", "sec", "let", "DH", "nonce", "samp", "if", "then", "else", "enum", "Data", "sigkey", "type", "Unit", "random_oracle", "return", "corr", "RO", "debug", "assert",  "assume", "admit", "ensures", "true", "false", "True", "False", "call", "static", "corr_case", "false_elim", "union_case", "exists", "get",  "getpk", "getvk", "pack", "def", "Union", "pkekey", "label", "aexp", "type", "idx", "table", "lookup", "write", "unpack", "to", "include", "maclen", "tag", "begin", "end"]
                , P.reservedOpNames= ["(", ")", "->", ":", "=", "!", "~=", "*", "|-", "+x"]
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

beginEndPos :: Parser (Spanned a) -> Parser (Spanned a)
beginEndPos k = do
    p <- getPosition
    reserved "begin"
    v <- k
    reserved "end"
    p' <- getPosition
    return $ Spanned (ignore $ Position (sourceLine p, sourceColumn p) (sourceLine p', sourceColumn p') (sourceName p)) (v^.val)


parseSpanned :: Parser a -> Parser (Spanned a)
parseSpanned k = do
    p <- getPosition
    v <- k
    p' <- getPosition
    return $ Spanned (ignore $ Position (sourceLine p, sourceColumn p) (sourceLine p', sourceColumn p') (sourceName p)) v

parseNameExp =
    parseSpanned $ 
        (do
            reserved "RO"
            symbol "<"
            p <- identifier
            symbol ">"
            return $ ROName p)
        <|>
        (do
            reserved "PRF"
            symbol "<"
            n <- parseNameExp
            symbol ","
            p <- identifier
            symbol ">"
            return $ PRFName n p)
        <|>
        (do
            i <- identifier
            inds <- parseIdxParams
            return $ BaseName inds i
        )

parseLabel = buildExpressionParser parseLabelTable parseLabelTerm
parseLabelTable = [ [ Infix (do
    symbol "/\\" 
    return (\x y -> mkSpannedWith (joinPosition (unignore $ x^.spanOf) (unignore $ y^.spanOf)) $ LJoin x y))
    AssocLeft ] ]
parseLabelTerm = 
        parensPos parseLabel <|> 
      (parseSpanned $ do
          reserved "static";
          return LZero)
      <|>
      (parseSpanned $ do
          reserved "adv";
          return LAdv)
      <|> (parseSpanned $ do
          symbol "["
          n <- parseNameExp;
          symbol "]"
          return $ LName n)
      <|> (parseSpanned $ do
          symbol "#"
          n <- identifier
          symbol "#"
          return $ LVar n)
      <|> (try $ parseSpanned $ do
          symbol "/\\_"
          i <- identifier
          l <- parseLabel
          return $ LRangeIdx $ bind (s2n i) l
          )

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
        reserved "Data"
        symbol "<"
        l <- parseLabel
        o <-
            (try $ do
                symbol ">"
                symbol "|"
                a <- parseAExpr
                symbol "|"
                return $ Right a
            )
            <|>
            (try $ do
                symbol ">"
                return $ Left l
                )
            <|>
            (try $ do
                symbol ","
                symbol "|"
                l' <- parseLabel
                symbol "|"
                symbol ">"
                return $ Left l'
            ) 
        case o of
          Left l' -> return $ TData l l'
          Right a -> return $ TDataWithLength l a
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
                       (mkSpanned $ TData advLbl advLbl)
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
    (parseSpanned $ do
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
          _ -> 
            (do
                symbol ":"
                t <- parseTy
                symbol "{"
                p <- parseProp
                symbol "}"
                return $ TRefined t $ bind (s2n x) p 
            )
            <|>
            (do
                ps' <- optionMaybe parseParams
                let ps = case ps' of
                           Nothing -> []
                           Just xs -> xs
                return $ TVar x ps
            )
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
        (try $ parseSpanned $ do
            t <- parseAExpr
            symbol "="
            t2 <- parseAExpr
            return $ PEq t t2)
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
        (parseSpanned $ do
            reserved "happened"
            symbol "("
            s <- identifier
            inds <- parseIdxParams
            symbol "("
            xs <- (parseAExpr `sepBy` (symbol ","))
            symbol ")"
            symbol ")"
            return $ PHappened s inds xs
        )
        <|>
        (parseSpanned $ try $ do
            e <- parseAExpr
            return $ PEq e (aeApp "TRUE" [] [])
        )



parsePropTable = [ 
    [ Prefix (do
        p <- getPosition
        reservedOp "!" 
        return $ \x -> mkSpannedWith (prefixPosition p (unignore $ x^.spanOf)) $ PNot x) ],
    [ 
     Infix (do
         symbol "/\\"
         return $ \x y -> mkSpannedWith (joinPosition (unignore $ x^.spanOf) (unignore $ y^.spanOf)) (PAnd x y)) AssocLeft, 
     Infix (do
         symbol "||"
         return $ \x y -> mkSpannedWith (joinPosition (unignore $ x^.spanOf) (unignore $ y^.spanOf)) (POr x y)) AssocLeft], 
     [ 
     Infix (do
         p <- getPosition
         symbol "==>"
         return $ \x y -> mkSpannedWith  (joinPosition (unignore $ x^.spanOf) (unignore $ y^.spanOf)) (PImpl x y)) AssocLeft 
     ] ]

parseNameType = 
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
    x <- identifier
    ys <- optionMaybe $ do
        symbol "<"
        is <- (parseIdx `sepBy` (symbol ","))
        symbol ">"
        return is
    return $ Locality x $ concat ys 
 
parseDecls = 
    many $ 
    (parseSpanned $ do
    reserved "name"
    n <- identifier
    inds <- parseIdxParamBinds
    ntnl <- optionMaybe $ do
        symbol ":"
        nt <- parseNameType
        symbol "@"
        nl <- parseLocality `sepBy` (symbol ",")
        return (nt, nl)
    return $ DeclName n (bind inds ntnl)
    )
    <|>
    parseEnum
    <|>
    parseStruct
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
        reserved "def"
        n <- identifier
        inds <- parseIdxParamBinds
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
        preReq <- optionMaybe $ do 
            reserved "requires"
            parseProp
        symbol ":"
        tyAnn <- parseTy
        oe <- optionMaybe $ do
            symbol "="
            parseExpr
        return $ DeclDef n (bind inds $ (nl, bind args (preReq, tyAnn, oe)))
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
        reserved "corr"
        l1 <- parseLabel
        symbol "==>"
        l2 <- parseLabel
        return $ DeclCorr l1 l2
    )
    <|>
    (parseSpanned $ do
        reserved "random_oracle"
        l <- identifier
        symbol ":"
        e <- parseAExpr
        symbol "->"
        nt <- parseNameType
        return $ DeclRandOrcl l [] (e, nt))
    <|>
    (parseSpanned $ do
        reserved "func"
        x <- identifier
        reserved "arity"
        whiteSpace
        i <- many1 digit
        whiteSpace
        return $ DeclDetFunc x UninterpFunc (read i))
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
        return $ DeclLocality nl i)
    <|>
    (parseSpanned $ do
        reserved "table"
        n <- identifier
        symbol ":"
        t <- parseTy
        symbol "@"
        loc <- parseLocality
        return $ DeclTable n t loc)


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
        return $ DebugPrintTyContext
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


parseExpr = buildExpressionParser parseExprTable parseExprTerm
parseExprTable = 
    [ [ Infix (do
    symbol ";" 
    return (\e1 e2 -> mkSpannedWith (joinPosition (unignore $ e1^.spanOf) (unignore $ e2^.spanOf)) $ ELet e1 (Just (Spanned (ignore def) TUnit)) "_" (bind (s2n "_") e2))
              )
    AssocLeft ] ]

parseExprTerm = 
    (try $ do -- Short circuit for ()
        p <- getPosition
        char '('
        char ')'
        p' <- getPosition
        whiteSpace
        return $ Spanned (ignore $ mkPos p p') $ ERet $ Spanned (ignore $ mkPos p p') (AEApp "UNIT" [] [])
        )
    <|>
    parensPos parseExpr
    <|>
    beginEndPos parseExpr
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
        return $ EInput $ bind (s2n x, s2n y) e
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
        reserved "union_case"
        x <- identifier
        reservedOp "="
        a <- parseAExpr
        reserved "in"
        e <- parseExpr
        return $ EUnionCase a $ bind (s2n x) e
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
            let f k ((x, tyAnn), e) = Spanned (ignore $ mkPos p p') $ ELet (head es) tyAnn x $ bind (s2n x) k in
            return $ foldl f e' $ zip xts es
    )
    <|>
    (parseSpanned $ do
        reserved "samp"
        x <- identifier
        symbol "("
        args <- parseArgs
        symbol ")"
        return $ ESamp x args)
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
        reserved "call"
        x <- identifier
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
        reserved "case"
        x <- parseAExpr
        xs <- many1 $ do
          symbol "|"
          c <- identifier
          ov <- optionMaybe identifier
          symbol "=>"
          e <- parseExpr
          return (c, case ov of
                       Nothing -> Left e
                       Just x -> Right (ignore x, bind (s2n x) e))
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
        reserved "in"
        e <- parseExpr
        return $ ECorrCase n e
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
        n <- identifier
        symbol ","
        a <- parseAExpr
        symbol ")"
        return $ ETLookup n a
    )
    <|>
    (parseSpanned $ do
        reserved "write"
        symbol "("
        n <- identifier
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

parseAExpr :: Parser AExpr
parseAExpr = buildExpressionParser parseAExprTable parseAExprTerm
parseAExprTable = 
    [ [ 
    Infix (do
    symbol "+" 
    return (\e1 e2 -> mkSpannedWith (joinPosition (unignore $ e1^.spanOf) (unignore $ e2^.spanOf)) $ AEApp "plus" [] [e1, e2])
              )
    AssocLeft], [
    Infix (do
    symbol "*" 
    return (\e1 e2 -> mkSpannedWith (joinPosition (unignore $ e1^.spanOf) (unignore $ e2^.spanOf)) $ AEApp "mult" [] [e1, e2])
              )
    AssocLeft]
    ,[
    Infix (do
    symbol "&&" 
    return (\e1 e2 -> mkSpannedWith (joinPosition (unignore $ e1^.spanOf) (unignore $ e2^.spanOf)) $ AEApp "andb" [] [e1, e2])
              )
    AssocLeft]
    ]
parseAExprTerm =           
    (try $ do
        p <- getPosition
        char '('
        char ')'
        p' <- getPosition
        whiteSpace
        return $ Spanned (ignore $ mkPos p p') $ AEApp "UNIT" [] []
    )
    <|>
    parensPos parseAExpr
    <|>
    (parseSpanned $ do
        reserved "true"
        return $ AEApp "TRUE" [] []
    )
    <|>
    (parseSpanned $ do
        reserved "false"
        return $ AEApp "FALSE" [] []
    )
    <|>
    (parseSpanned $ do
        symbol "\""
        x <- many $ noneOf "\""
        symbol "\""
        return $ AEString x
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
        whiteSpace
        i <- many1 digit
        whiteSpace
        return $ AEInt (read i)
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
    (parseSpanned $ do { 
    x <- identifier;
    -- todo: accept <i> here?
    ( (do 
        op <- optionMaybe parseParams
        symbol "(" 
        args <- parseArgs
        symbol ")"
        let ps = case op of
                   Just ps -> ps
                   Nothing -> []
        return $ AEApp x ps args)
      <|>
      (return $ AEVar (ignore x) (s2n x))
    )}) 

parseFile :: Parser [Decl]
parseFile = do
    whiteSpace
    ds <- parseDecls
    whiteSpace
    eof
    return ds
