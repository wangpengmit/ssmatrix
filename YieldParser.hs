import Text.Parsec
import Control.Monad.Cont
import Yield

main :: IO (Either ParseError Int)
main = runContT cmain return

cmain :: ContT r IO (Either ParseError Int)
cmain = do
  s <- liftIO (readFile "/dev/zero")
  g <- mkgen (\yield x -> runParserT (pmain (lift . yield) x) () "/dev/zero" s)
  g True >>= liftIO . print
  g True >>= liftIO . print
  End z <- g False
  return z

pmain yield b = loop b 0 where
  loop False n = return n
  loop True n = do
    c <- anyChar
    b <- yield c
    loop b $! (n+1)
