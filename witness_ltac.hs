{-# LANGUAGE LambdaCase #-}

import Text.ParserCombinators.Parsec ((<|>), (<?>), many, many1, char, try, parse, sepBy, choice)
import Text.ParserCombinators.Parsec.Char (noneOf)
import Text.ParserCombinators.Parsec.Token (natural, integer, float, whiteSpace, stringLiteral, makeTokenParser)
import Text.ParserCombinators.Parsec.Language (haskellDef)
import System.IO 
import System.Environment
import Control.Monad.Error
import Control.Monad.State

data SExpr = Int Integer
         | Float Double
         | String String
         | Symbol String
         | List [SExpr] deriving (Eq, Show)
 
lexer = makeTokenParser haskellDef
 
tInteger = (natural lexer) >>= (return . Int) <?> "integer"
 
tFloat = (float lexer) >>= (return . Float) <?> "floating point number"
 
tString = (stringLiteral lexer) >>= (return . String) <?> "string"
 
tSymbol = (many1 $ noneOf "()\" \t\n\r") >>= (return . Symbol) <?> "symbol"
 
tAtom = choice [try tFloat, try tInteger, try tSymbol, tString] <?> "atomic expression"
 
tSExpr = do 
    whiteSpace lexer
    expr <- tList <|> tAtom
    whiteSpace lexer
    return expr
    <?> "S-expression"
 
tList = do 
    char '('
    list <- many tSExpr
    char ')'
    return $ List list
    <?> "list"
 
tProg = many tSExpr <?> "program"
 
p ex = case parse tProg "" ex of
              Right x -> putStrLn $  unwords $ map show x
              Left err -> print err

data Trace = Trace {
      name :: String,
      from :: Expr,
      to :: Expr,
      cmds :: [Cmd]
    } deriving (Eq, Show)

data Expr =
  Var String
  | ConstInt Integer
  | Binop Binop Expr Expr
    deriving (Eq, Show)

data Binop = Plus | Minus | Mult | Div
             deriving (Eq, Show)

data Cmd = Rewrite String Expr
         | Fold Expr Expr
         | Lift Expr
         | Beta
           deriving (Eq, Show)

data ExprError =
  ExprError String
  | EmptyListError
  | CompositeError String ExprError
  | MismatchError String String
    deriving (Eq, Show)

instance Error ExprError where
  strMsg s = ExprError s
  
type MayThrow = Either ExprError

getTrace node = enterWith node "trace" $ do
  name <- first >>= lift . getSymbol
  from <- first >>= lift . getFrom
  to <- last_ >>= lift. getTo
  cmds <- every $ lift . getCmd
  return (Trace name from to cmds)

getFrom node =
  enterWith node "from" $ first >>= lift . getExpr <??> "original expression"

getTo node =
  enterWith node "to" $ first >>= lift . getExpr <??> "final expression"
  
getCmd node = enter node $ do
  first >>= lift . getSymbol >>= \case
    "rewrite" -> do
      rule <- first >>= lift . getSymbol <??> "rewrite rule"
      subterm <- first >>= lift . getExpr <??> "rewrite subterm"
      return (Rewrite rule subterm)
    "fold" -> do
      from <- first >>= lift . getExpr <??> "fold from"
      to <- first >>= lift . getExpr <??> "fold to"
      return (Fold from to)
    "lift" -> do
      subterm <- first >>= lift . getExpr
      return (Lift subterm)
    "beta" -> return Beta
                 
getExpr = \case
  Int i -> return (ConstInt i)
  Symbol x -> return (Var x)
  node@(List _) -> enter node $ do
    op <- first >>= lift . getBinop
    a <- first >>= lift . getExpr
    b <- first >>= lift . getExpr
    return (Binop op a b)

getBinop :: SExpr -> MayThrow Binop
getBinop node = 
  getSymbol node >>= \case 
    "+" -> return Plus
    "-" -> return Minus
    "*" -> return Mult
    "/" -> return Div
    op -> throwError (strMsg $ "unknown binary operator" ++ op)

getSymbol :: SExpr -> MayThrow String
getSymbol = \case
  Symbol x -> return x
  node -> throwError $ MismatchError "symbol" (show node)

enter node m = case node of
  List ls -> liftM fst (runStateT m ls)
  _ -> throwError (strMsg "can't enter a non-list node")
    
enterWith node sym m = enter node (first >>= exact (Symbol sym) >> m)

m <??> str = catchError m $ \e -> throwError $ CompositeError ("error in parsing " ++ str) e
  
infixl 1 <??>

exact a b = if a == b then return () else throwError $ MismatchError (show a) (show b)

first = 
  get >>= \case
    x : xs -> put xs >> return x
    _ -> throwError EmptyListError
  
last_ =
  get >>= \case
    [] -> throwError EmptyListError
    ls -> put (removeLast ls) >> return (last ls)

every f = get >>= sequence . (map f)

removeLast ls = take (length ls - 1) ls

main = do
  args <- getArgs
  h <- case args of
         fileName : _ -> openFile fileName ReadMode
         _ -> return stdin
  str <- hGetContents h
  print str
  putStrLn ""
  case parse tProg "" str of
    Right sexprs -> do
      print sexprs
      putStrLn ""
      case sequence (map getTrace sexprs) of
        Right traces -> print traces
        Left err -> print err
    Left err -> print err

-- main = do 
--     let expr = "((data \"quoted data\" 123 4.5)\n  (data (!@# (4.5) \"(more\" \"data)\")))"
--     putStrLn $ "The input:\n" ++ expr ++ "\n"
--     putStr "Parsed as:\n"
--     p expr




-- import Text.ParserCombinators.Parsec

-- traces = many trace
-- trace =
--   do
--     name
--     delimit
--     cmds

-- name =
--   do
--     id
--     try delimit
--     char ':'
--     try delimit

-- id =
--   try (string "ex1")
--   <|> try (string "ex2")
--   <|> string "ex3"
--   <?> "identifier"
    
-- delimit = many1 (space <|> comment)

-- comment =
--   do
--     string "(*"
           



-- csvFile = sepBy line eol
-- line = sepBy cell (char ',')
-- cell = quotedCell <|> many (noneOf ",\n\r")

-- quotedCell = 
--   do
--     char '"'
--     content <- many quotedChar
--     char '"' <?> "quote at end of cell"
--     return content

-- quotedChar =
--   noneOf "\""
--   <|> try (string "\"\"" >> return '"')
  
-- eol =   try (string "\n\r")
--         <|> try (string "\r\n")
--         <|> string "\n"
--         <|> string "\r"
--         <?> "end of line"

-- parseCSV :: String -> Either ParseError [[String]]
-- parseCSV input = parse csvFile "(unknown)" input

-- main =
--   do c <- getContents
--      case parse csvFile "(stdin)" c of
--        Left e -> do putStrLn "Error parsing input:"
--                     print e
--        Right r -> mapM_ print r
