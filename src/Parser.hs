{-# LANGUAGE StrictData #-}

module Parser where

import           Text.Parsec
import           Text.Parsec.String    (Parser             )
import           Text.Parsec.Language  (emptyDef           )
import           Text.Parsec.Expr                          
import qualified Text.Parsec.Token  as  Token              
                                                           
import           Data.List             (intercalate        )
import           Data.Functor          ((<&>        ), ($>))
import           Data.Functor.Identity (Identity           )
import qualified Data.Text           as T                  
                                                           
import           Control.Monad         (when               )

import           Syntax

--------------------------------------------------------------------------------

nasketsDef :: Token.LanguageDef ()
nasketsDef = emptyDef
  { Token.commentStart    = "{-"                                               ,
    Token.commentEnd      = "-}"                                               ,
    Token.commentLine     = "--"                                               ,
    Token.nestedComments  = True                                               ,
    Token.identStart      = letter   <|> char '_'                              ,
    Token.identLetter     = alphaNum <|> char '_' <|> char '\'' <|> oneOf "′″‴",
    Token.opStart         = oneOf ":!#$%&*+./<=>?@\\^|-~[{"                    ,
    Token.opLetter        = oneOf ":>=\\#"                                     ,
    Token.reservedNames   =
      ["module"   , "where"     , "import"  ,
       "Int"      , "Double"    , "String"  ,
       "IO"       , "return"    ,
       "let"      , "in"        ,
       "putStr"   , "getLine"   , "readFile", "writeFile",
       "argCount" , "argAt"     ,
       "substring", "length"    , "trunc"   ,
       "showInt"  , "showDouble",
       "forall"   ],
    Token.reservedOpNames =
      ["::" , "∷"  , ":" ,
       "="  ,
       "->" , "→"  ,
       "Λ"  , "/\\", "\\", "λ",
       "."  ,
       "?"  ,
       ">>" , ">>=", "»" ,
       "|-" , "⊢"  ,
       "==" , "=^" , "=.",
       "["  , "]"  ,
       "{"  , "}"  ,
       "∀"  , 
       "◻"  ,
       "^"  ],
    Token.caseSensitive   = True }

lexer :: Token.TokenParser ()
lexer = Token.makeTokenParser nasketsDef

identifier, stringLiteral :: Parser String

identifier    = Token.identifier    lexer
stringLiteral = Token.stringLiteral lexer

reserved, reservedOp :: String -> Parser ()

reserved   = Token.reserved   lexer
reservedOp = Token.reservedOp lexer

lsym :: String -> Parser String
lsym = Token.symbol lexer

parens, brackets, braces :: Parser a -> Parser a

parens   = Token.parens   lexer
brackets = Token.brackets lexer
braces   = Token.braces   lexer

toPos :: SourcePos -> Pos
toPos sp = Pos (sourceName sp) (sourceLine sp) (sourceColumn sp)

withLoc :: (Pos -> a -> a) -> Parser a -> Parser a
withLoc wrap p = do
   sp <- getPosition
   wrap (toPos sp) <$> p

--------------------------------------------------------------------------------

parseRawK :: Parser RawK
parseRawK = buildExpressionParser table (parens parseRawK <|> (reservedOp "*" >> return RKStar) <|> parseRKForall <|> (RKVar . UName <$> identifier))
  where table = [[Infix (reservedOp "->" >> return RKArr) AssocRight,
                  Infix (reservedOp "→"  >> return RKArr) AssocRight]]

parseRKForall :: Parser RawK
parseRKForall = do
  _            <- reserved "forall" <|> reservedOp "∀"
  binderGroups <- many1 (parens parseGroup <|> parseGroup)
  _            <- reservedOp "."
  body         <- parseRawK
  let flatBinders = concat binderGroups
  return $ foldr (RKForall . LName) body flatBinders
  where parseGroup = do nms <- many1 identifier
                        _   <- optional ((reservedOp "::" <|> reservedOp "∷" <|> reservedOp ":") >> (reservedOp "[]" <|> reservedOp "◻"))
                        return nms

--------------------------------------------------------------------------------

parseRawT :: Parser RawT
parseRawT = withLoc RTLoc $ buildExpressionParser tTable tyApp

tTable :: [[Operator String () Identity RawT]]
tTable =
  [[infixR (reservedOp "->") (RTTApp . RTTApp (RTConst Arr)),
    infixR (reservedOp "→")  (RTTApp . RTTApp (RTConst Arr))]]
  where infixR p f = Infix (try (getPosition <* p) <&> \sp l r -> RTLoc (toPos sp) (f l r)) AssocRight

tyApp :: Parser RawT
tyApp = do
  ty <- tyExp
  fs <- many looseTySuffix
  return $ foldl (\acc f -> f acc) ty fs

looseTySuffix :: Parser (RawT -> RawT)
looseTySuffix =
      try (do pos <- getPosition
              k <- braces parseRawK
              return $ \acc -> RTLoc (toPos pos) (RTKApp acc k))
  <|> try (do pos <- getPosition
              arg <- tyExp
              return $ \acc -> RTLoc (toPos pos) (RTTApp acc arg))

parseRawForall :: Parser RawT
parseRawForall = do
  _            <- reserved "forall" <|> reservedOp "∀"
  binderGroups <- many1 (parens parseGroup <|> parseGroup)
  _            <- reservedOp "."
  body         <- parseRawT
  let flatBinders = concat binderGroups
  return $ foldr (\(n, e) b -> either (\_ -> RTForallK (LName n) b) (\mk -> RTForall (LName n) mk b) e) body flatBinders
  where parseGroup = do nms <- many1 identifier
                        e <- option (Right Nothing) $ try $ do
                               _ <- reservedOp ":" <|> reservedOp "::" <|> reservedOp "∷"
                               (reservedOp "[]" <|> reservedOp "◻") $> Left () <|> (Right . Just) <$> parseRawK
                        return [ (n, e) | n <- nms ]

parseRawTLam :: Parser RawT
parseRawTLam = do
  _            <- reservedOp "\\" <|> reservedOp "λ"
  binderGroups <- many1 (parens parseGroup <|> parseGroup)
  _            <- reservedOp "."
  body         <- parseRawT
  let flatBinders = concat binderGroups
  return $ foldr (\(n, mk) b -> RTTLam (LName n) mk b) body flatBinders
  where parseGroup = do nms <- many1 identifier
                        mk <- optionMaybe ((reservedOp ":" <|> reservedOp "::" <|> reservedOp "∷") >> parseRawK)
                        return [ (n, mk) | n <- nms ]

parseRawTKLam :: Parser RawT
parseRawTKLam = do
  _            <- reservedOp "/\\" <|> reservedOp "Λ"
  binderGroups <- many1 (parens parseGroup <|> parseGroup)
  _            <- reservedOp "."
  body         <- parseRawT
  let flatBinders = concat binderGroups
  return $ foldr (\n b -> RTTKLam (LName n) b) body flatBinders
  where parseGroup = do nms <- many1 identifier
                        _ <- optional ((reservedOp ":" <|> reservedOp "::" <|> reservedOp "∷") >> (reservedOp "[]" <|> reservedOp "◻"))
                        return nms

parseRawTLet :: Parser RawT
parseRawTLet = do
  reserved   "let"
  lnm <- identifier
  mK  <- optionMaybe ((reservedOp ":" <|> reservedOp "::" <|> reservedOp "∷") >> parseRawK)
  reservedOp "="
  ty  <- parseRawT
  reserved   "in"
  ty' <- parseRawT
  return $ RTLet (LName lnm) mK ty ty'

tyExp :: Parser RawT
tyExp = withLoc RTLoc $
      try parseRawForall
  <|> try parseRawTLet
  <|> try (parens (reservedOp "->") >> return (RTConst Arr))
  <|> try (parens (reservedOp "→" ) >> return (RTConst Arr))
  <|> try (parens (pure (RTConst Unit)))
  <|> try (parens parseRawT)
  <|>     (reserved "Int"    >> return (RTConst Int    ))
  <|>     (reserved "Double" >> return (RTConst Double ))
  <|>     (reserved "String" >> return (RTConst String ))
  <|>     (reserved "IO"     >> return (RTConst IO     ))
  <|> try parseRawTKLam
  <|> try parseRawTLam
  <|> try (do pos <- getPosition
              unm <- identifier
              lookAhead (notFollowedBy (try (char '=' >> notFollowedBy (oneOf ":!#$%&*+./<=>?@\\^|-~["))))
              when (sourceColumn pos == 1) $
                lookAhead (notFollowedBy (reservedOp "::" <|> reservedOp "∷" <|> reservedOp ":"))
              return (RTVar (UName unm)))

--------------------------------------------------------------------------------

parseRaw :: Parser Raw
parseRaw = withLoc RLoc $
      try parseRawLet
  <|> try parseRawLam
  <|> try parseRawBigLam
  <|> expOp

expOp :: Parser Raw
expOp = buildExpressionParser expTable expApp

expTable :: [[Operator String () Identity Raw]]
expTable =
  [[prefix (lsym       "-." ) (unOp  ESubD (RLit (LDouble 0.0))) ,
    prefix (reservedOp "-"  ) (unOp  ESub  (RLit (LInt 0     )))],
   [infixL (lsym       "*." ) (binOp EMulD                     ) ,
    infixL (lsym       "/." ) (binOp EDivD                     ) ,
    infixL (reservedOp "*"  ) (binOp EMul                      )],
   [infixL (lsym       "+." ) (binOp EAddD                     ) ,
    infixL (lsym       "-." ) (binOp ESubD                     ) ,
    infixL (reservedOp "+"  ) (binOp EAdd                      ) ,
    infixL (reservedOp "-"  ) (binOp ESub                      )],
   [infixR (reservedOp "^"  ) (binOp EConcat                   )],
   [infixN (lsym       "==" ) (binOp EIntEq                    ) ,
    infixN (lsym       "=^" ) (binOp EStringEq                 ) ,
    infixN (lsym       "=." ) (binOp EDoubleEq                 )],
   [infixL (reservedOp ">>=") RBind                            ]]
  where prefix p f  = Prefix (try (getPosition <* p) <&> \sp e   -> RLoc (toPos sp) (f e))
        infixL p f  = Infix  (try (getPosition <* p) <&> \sp l r -> RLoc (toPos sp) (f l r)) AssocLeft
        infixR p f  = Infix  (try (getPosition <* p) <&> \sp l r -> RLoc (toPos sp) (f l r)) AssocRight
        infixN p f  = Infix  (try (getPosition <* p) <&> \sp l r -> RLoc (toPos sp) (f l r)) AssocNone
        binOp c l r = RApp (RApp (RConst c) l) r
        unOp c z e  = RApp (RApp (RConst c) z) e

expApp :: Parser Raw
expApp = do
  e  <- expTight
  fs <- many looseSuffix
  return $ foldl (\e' f -> f e') e fs

looseSuffix :: Parser (Raw -> Raw)
looseSuffix =
  try (do pos <- getPosition
          arg <- expTight
          return $ \e -> RLoc (toPos pos) (RApp e arg))

expTight :: Parser Raw
expTight = do
  e  <- expPrefix
  fs <- many tightSuffix
  return $ foldl (\e' f -> f e') e fs

tightSuffix :: Parser (Raw -> Raw)
tightSuffix =
      try (do pos <- getPosition
              k <- braces parseRawK
              return $ \e -> RLoc (toPos pos) (RKApp e k))
  <|> try (do pos <- getPosition
              ty  <- brackets parseRawT
              return $ \e -> RLoc (toPos pos) (RTApp e ty))

expPrefix :: Parser Raw
expPrefix =
      try (reserved "return" >> RReturn <$> expApp)
  <|> expAtom

expAtom :: Parser Raw
expAtom = withLoc RLoc $
      try parseRawLet
  <|> try parseRawLam
  <|> try parseRawBigLam
  <|> (reserved "putStr"     >> return (RConst EPutStr    ))
  <|> (reserved "getLine"    >> return (RConst EGetLine   ))
  <|> (reserved "readFile"   >> return (RConst EReadFile  ))
  <|> (reserved "writeFile"  >> return (RConst EWriteFile ))
  <|> (reserved "argCount"   >> return (RConst EArgCount  ))
  <|> (reserved "argAt"      >> return (RConst EArgAt     ))
  <|> (reserved "substring"  >> return (RConst ESubstring ))
  <|> (reserved "length"     >> return (RConst ELength    ))
  <|> (reserved "showInt"    >> return (RConst EShowInt   ))
  <|> (reserved "showDouble" >> return (RConst EShowDouble))
  <|> (reserved "trunc"      >> return (RConst ETrunc     ))
  <|> try (parens (pure (RLit LUnit)))
  <|> try (Token.naturalOrFloat lexer      <&> either (RLit . LInt) (RLit . LDouble))
  <|> try (RLit . LString . T.pack         <$> stringLiteral)
  <|> try (reservedOp "?" >> RHole . HName <$> identifier <*> optionMaybe (try (braces parseRaw)))
  <|> try parseParens
  <|> try (do pos <- getPosition
              unm <- identifier
              lookAhead (notFollowedBy (try (char '=' >> notFollowedBy (oneOf ":!#$%&*+./<=>?@\\^|-~["))))
              when (sourceColumn pos == 1) $
                lookAhead (notFollowedBy (reservedOp "::" <|> reservedOp "∷" <|> reservedOp ":"))
              return (RVar (UName unm)))

parseParens :: Parser Raw
parseParens =
  lsym "(" >> (
        (try (lsym       "+." >> lsym ")") >> return (RConst EAddD    ))
    <|> (try (lsym       "-." >> lsym ")") >> return (RConst ESubD    ))
    <|> (try (lsym       "*." >> lsym ")") >> return (RConst EMulD    ))
    <|> (try (lsym       "/." >> lsym ")") >> return (RConst EDivD    ))
    <|> (try (lsym       "==" >> lsym ")") >> return (RConst EIntEq   ))
    <|> (try (lsym       "=^" >> lsym ")") >> return (RConst EStringEq))
    <|> (try (lsym       "=." >> lsym ")") >> return (RConst EDoubleEq))
    <|> (try (reservedOp "+"  >> lsym ")") >> return (RConst EAdd     ))
    <|> (try (reservedOp "-"  >> lsym ")") >> return (RConst ESub     ))
    <|> (try (reservedOp "*"  >> lsym ")") >> return (RConst EMul     ))
    <|> (try (reservedOp "^"  >> lsym ")") >> return (RConst EConcat  ))
    <|> (parseRaw >>= \e -> (reservedOp ":" >> parseRawT <* lsym ")" <&> RAnn e) <|> (lsym ")" >> return e))
  )

parseRawLet :: Parser Raw
parseRawLet = do
  reserved   "let"
  lnm <- identifier
  mTy <- optionMaybe (reservedOp ":" >> parseRawT)
  reservedOp "="
  e   <- parseRaw
  reserved   "in"
  e'  <- parseRaw
  return $ RLet (LName lnm) mTy e e'

parseRawLam :: Parser Raw
parseRawLam = do
  _            <- reservedOp "λ" <|> reservedOp "\\"
  binderGroups <- many1 (parens parseGroup <|> parseGroup)
  _            <- reservedOp "."
  body         <- parseRaw
  let flatBinders = concat binderGroups
  return $ foldr (\(lnm, mTy) b -> RLam (LName lnm) mTy b) body flatBinders
  where parseGroup = do nms <- many1 identifier
                        mTy <- optionMaybe (reservedOp ":" >> parseRawT)
                        return [ (lnm, mTy) | lnm <- nms ]

parseRawBigLam :: Parser Raw
parseRawBigLam = do
  _            <- reservedOp "/\\" <|> reservedOp "Λ"
  binderGroups <- many1 (parens parseGroup <|> parseGroup)
  _            <- reservedOp "."
  body         <- parseRaw
  let flatBinders = concat binderGroups
  return $ foldr (\(n, e) b -> either (\_ -> RKLam (LName n) b) (\mk -> RTLam (LName n) mk b) e) body flatBinders
  where parseGroup = do nms <- many1 identifier
                        e <- option (Right Nothing) $ try $ do
                               _ <- reservedOp ":" <|> reservedOp "::" <|> reservedOp "∷"
                               (reservedOp "[]" <|> reservedOp "◻") $> Left () <|> (Right . Just) <$> parseRawK
                        return [ (n, e) | n <- nms ]

--------------------------------------------------------------------------------

parseDecl :: Parser RawDecl
parseDecl = withLoc RDLoc $
            try ((reservedOp ">>" <|> reservedOp "»") >> parseRaw  <&> RDeclExc  )
        <|> try ((reservedOp "|-" <|> reservedOp "⊢") >> parseRawT <&> RDeclEvalT)
        <|> do gnm <- identifier
               parseDeclBody gnm

parseDeclBody :: String -> Parser RawDecl
parseDeclBody gnm =
      (do _ <- reservedOp "::" <|> reservedOp "∷"
          (try (reservedOp "[]" <|> reservedOp "◻") >> parseKindRest)
           <|> parseTypeRest)
  <|> (do _ <- reservedOp ":"
          parseFunRest)
  where parseKindRest = do
          gnm' <- identifier
          if gnm == gnm'
            then reservedOp "=" >> parseRawK <&> RDeclKind (GName gnm)
            else fail $ "Kind definition name '" ++ gnm' ++ "' does not match signature name '" ++ gnm ++ "'"
        
        parseTypeRest = do
          k <- parseRawK
          gnm' <- identifier
          if gnm == gnm'
            then reservedOp "=" >> parseRawT <&> RDeclType (GName gnm) k
            else fail $ "Type definition name '" ++ gnm' ++ "' does not match signature name '" ++ gnm ++ "'"
            
        parseFunRest = do
          ty <- parseRawT
          gnm' <- identifier
          if gnm == gnm'
            then reservedOp "=" >> parseRaw <&> RDeclFun (GName gnm) ty
            else fail $ "Function definition name '" ++ gnm' ++ "' does not match signature name '" ++ gnm ++ "'"

parseMNm :: Parser MName
parseMNm = sepBy1 identifier (reservedOp ".") <&> MName . intercalate "."

parseImport :: Parser MName
parseImport = reserved "import" >> parseMNm

parseRawModule :: Parser RawModule
parseRawModule = do
  Token.whiteSpace lexer
  reserved "module"
  mnm <- parseMNm
  reserved "where"
  imports <- many parseImport
  decls   <- many parseDecl
  eof
  return $ RModule mnm imports decls
