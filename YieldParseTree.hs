import Control.Applicative((<*))
import Data.List(intercalate)
import Text.Parsec
import Control.Monad.Cont
import Yield(mkgen)

data Tree = Tree { tag :: String, sub :: [Tree] }
instance Show Tree where
  show Tree{tag=t, sub=s} = case s of
    [] -> t
    _ -> t ++ "[" ++ intercalate " " (map show s) ++ "]"

data Event = Start String | Stop Tree deriving Show

pmain yield = spaces >> (ptree <* eof)
  where
    ptree = do
      name <- ptag
      yield (Start name)
      cs <- option [] (between popen pclose (many ptree))
      let tree = Tree name cs
      yield (Stop tree)
      return tree
    ptag = (many1 alphaNum <?> "tagname") <* spaces
    popen = char '[' <* spaces
    pclose = char ']' <* spaces

main :: IO ()
main = runContT cmain return

cmain :: ContT r IO ()
cmain = do
  let s = "f [ x g[a b]" ++ cycle "huge["
  g <- mkgen (\yield _ -> runParserT (pmain (lift . yield)) () "hardcoded" s)
  replicateM_ 30 (g () >>= liftIO . print)
