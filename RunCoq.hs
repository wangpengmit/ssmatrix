{-# LANGUAGE LambdaCase #-}

import System.IO                                             
import System.Process    
import Debug.Trace
import System.IO.Error
import Control.Concurrent
import Data.List
import Text.Parsec (runParserT, many, try, string, (<|>), letter, anyChar, alphaNum, oneOf)
import Control.Monad.Cont
import Yield
import Control.Applicative ((<$>), (<*>), pure)

main = do
  let input = getInput
  -- let input = getInput2
  promptStream input
  
promptStream k = do                                                    
    (toCoq, fromCoq, fromCoqErr, handleCoq) <- runInteractiveCommand "coqtop 2>&1"
    -- (toCoq, fromCoq, fromCoqErr, handleCoq) <- runInteractiveCommand "coqtop -emacs 2>&1"
    mapM_ (flip hSetBinaryMode True) [toCoq, fromCoqErr, fromCoq]             
    -- hSetBuffering fromCoqErr NoBuffering
    hSetBuffering toCoq NoBuffering
    -- hSetBuffering fromCoq NoBuffering
    -- hSetBuffering stdout NoBuffering
    strFromCoq <- hGetContents fromCoq
    flip runContT return $ do
      g <- mkgen (\yield _ -> runParserT (promptParser (lift . yield)) () "strFromCoq" strFromCoq)
      let waitPrompt onNonPrompt onPrompt = do
            g () >>= \case
              More (Left c) -> do
                onNonPrompt c
                (np, p) <- waitPrompt onNonPrompt onPrompt
                return (c : np, p)
              More (Right s) -> do
                onPrompt s
                return ("", s)
              _ -> return ("", "")
      k toCoq waitPrompt

getInput
  :: (Monad (t1 IO), Monad (t2 IO), MonadTrans t1, MonadTrans t,
      MonadTrans t2) =>
     Handle
     -> ((Char -> t2 IO ()) -> (String -> t IO ()) -> t1 IO b)
     -> t1 IO ()
getInput toCoq waitPrompt = do    
    input <- lift $ getContents
    input <- return $ lines input
    input <- return $ flip mapM_ input
    waitPrompt noop (lift . putStr)
    input $ \ln -> do
      mapM_ (lift . flip hPutStrLn ln) [stdout, toCoq] 
      waitPrompt (lift . putStr . pure) (\_ -> lift $ putStr "Coq > ")

noop x = return ()

getInput2 toCoq waitPrompt = do
  lift $ putStrLn "Before"
  waitPrompt noop noop
  lift $ putStr "Coq > "
  mapM_ (lift . flip hPutStrLn "About nat.") [stdout, toCoq] 
  waitPrompt (lift . putStr . pure) noop
  lift $ putStrLn "Middle"
  lift $ putStr "Coq > "
  mapM_ (lift . flip hPutStrLn "About bool.") [stdout, toCoq] 
  waitPrompt (lift . putStr . pure) noop
  lift $ putStrLn "After"

promptParser yield = many $ try onPrompt <|> onNonprompt
  where
    onPrompt = do
      s <- prompt
      yield $ Right s
      return ()
    prompt = word <++> string " < "
    -- prompt = string "<prompt>" <++> word <++> string " < " <++> word <++> string " |" <++> option "" word <++> string "| " <++> word <++> string " < </prompt>"
    onNonprompt = do
      c <- anyChar
      yield $ Left c
      return ()
    word = letter <:> (many $ alphaNum <|> oneOf "_'")

(<++>) a b = (++) <$> a <*> b
(<:>) a b = (:) <$> a <*> b

p x = traceShow x x

pf f x = traceShow (f x) x

