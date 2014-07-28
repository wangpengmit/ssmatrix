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
    forkIO $ getResp out >> return ()
    waitPrompt err >>= putStr
    mapM_ ($ "Require Import matrix.") [putStrLn, (input inn)] 
    waitPrompt err >>= putStr
    mapM_ ($ "About bool.") [putStrLn, (input inn)] 
    waitPrompt err >>= putStr
    mapM_ ($ "Quit.") [(input inn)] 

waitPrompt h = hGetUntil h "Coq < "

input inn str = (forkIO $ hPutStrLn inn str) >> return ()

getResp out = hGetLine out >>= putStrLn >> getResp out

hGetUntil h str = 
  if null str then
    return ""
  else
    do
      c <- hGetChar h
      let str' = if c == head str then tail str else str
      (c :) <$> hGetUntil h str'
    
p x = traceShow x x

pf f x = traceShow (f x) x

