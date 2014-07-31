{-# LANGUAGE LambdaCase #-}
module MatchParen where

import Text.Parsec (parse, string, anyChar, choice, try, (<|>), lookAhead, eof)
import Control.Applicative ((<$>), (*>), (<*), (<*>))
import Debug.Trace
import Control.Monad (void)

data Paren = Paren String String [Paren] | NonParen String deriving (Show)

matchParen :: [(String, String)] -> String -> Maybe [Paren]
matchParen ls = post . parse (parens <* eof) ""  where

  parens = nonParen <:> sepEndBy' paren nonParen

  paren = oneOf' . map eachParen $ ls

  eachParen (open, close) = Paren open close <$> (string open *> parens <* string close)

  nonParen = NonParen <$> manyTill anyChar parenMark

  parenMark = oneOf' . map string . concatMap (\(a, b) -> [a, b]) $ ls

post = \case
  Right n -> Just $ trim n
  Left _ -> Nothing

trim = concatMap trimOne

trimOne (NonParen "") = []
trimOne (Paren a b ls) = [Paren a b (trim ls)]
trimOne a = [a]

oneOf' = choice . map try

sepEndBy'1' p sep = do {
  x <- p;
  do {
    y <- sep;
    xs <- sepEndBy' p sep;
    return (x : y : xs) }
  <|> return [x]}

sepEndBy' p sep = sepEndBy'1' p sep <|> return []

(<:>) a b = (:) <$> a <*> b

pretty = pp 0 where
  pp n = unlines . map (pp1 n)
  pp1 n = \case
    NonParen s -> lead n ++ show s
    Paren open close ls -> lead n ++ open ++ "\n" ++ pp (n+1) ls ++ lead n ++ close
  lead n = replicate n '\t'

original = \case
  NonParen s -> s
  Paren open close ls -> open ++ concatMap original ls ++ close

-- main = print $ matchParen [("(", ")")] "a (b (c d) (e f)) (g h) i"
-- main = putStrLn . concatMap original $ matchParen [("(", ")"), ("{", "}")] "a {b (c d) {e f}} (g h) i"
-- main = print $ matchParen [("(", ")")] "()(()) "
-- main = print $ matchParen [("(", ")")] ""

p x = traceShow x x

manyTill p end = scan
  where
    scan  = do{ lookAhead (try $ void end) <|> eof; return [] }
            <|>
            do{ x <- p; xs <- scan; return (x:xs) }
