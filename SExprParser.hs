-- S-expression parser
-- Adapted from http://rosettacode.org/wiki/S-Expressions#Haskell

module SExprParser where

import Text.Parsec
import Text.Parsec.Token hiding (integer)
import Text.Parsec.Language
import Control.Applicative hiding ((<|>), many)

data SExpr = Int Integer
         | String String
         | Symbol String
         | List [SExpr] deriving (Eq, Show)

lang = emptyDef {commentLine = ";;"}

lexer = makeTokenParser lang
 
tInteger = integer >>= (return . Int) <?> "integer"

-- the 'integer' parser in Text.Parsec.Token allows whitespace between sign and digits, undesirable here. This is a workaround.
(<:>) a b = (:) <$> a <*> b
number = many1 digit
plus = char '+' *> number
minus = char '-' <:> number
integer = read <$> (plus <|> minus <|> number)

tString = (stringLiteral lexer) >>= (return . String) <?> "string"
 
tSymbol = (many1 $ noneOf "()\" \t\n\r") >>= (return . Symbol) <?> "symbol"
 
tAtom = choice [
  try tInteger,
  try tSymbol,
  tString] <?> "atomic expression"
 
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
 
