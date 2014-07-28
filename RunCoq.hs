{-# LANGUAGE LambdaCase #-}

import Control.Applicative                                   
import System.IO                                             
import System.Process    
import Debug.Trace
import System.IO.Error
import Control.Concurrent
import Data.List

main = do                                                    
    (inn, out, err, idd) <- runInteractiveCommand "coqtop"    
    mapM_ (flip hSetBinaryMode False) [inn, err, out]             
    hSetBuffering inn NoBuffering
    hSetBuffering err LineBuffering
    hSetBuffering out LineBuffering
    forkIO $ parseUntilPrompt "stdin" out >> return ()
    forkIO $ hPutStrLn inn "Require Import matrix."
    waitPrompt err
    putStrLn "input"
    forkIO $ hPutStrLn inn "About bool."
    waitPrompt err
    putStrLn "input"
    forkIO $ hPutStrLn inn "Quit."
    waitPrompt err

waitPrompt h = do
  ln <- hGetLine h
  putStrLn $ "stderr: " ++ ln
  if isPrefixOf "Coq <" ln then do
    return ln
  else
    waitPrompt h

parseUntilPrompt src out = do
  tryIOError (hGetLine out) >>= \case
    Left e ->
        if isEOFError e
           then return []
           else ioError e
    Right latest -> do
        putStrLn $ src ++ ": " ++ latest
        (:) <$> return latest <*> parseUntilPrompt src out

p x = traceShow x x

pf f x = traceShow (f x) x

