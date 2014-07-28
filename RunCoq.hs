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
    hSetBuffering stdout NoBuffering
    hSetBuffering err NoBuffering
    hSetBuffering out NoBuffering
    forkIO $ getResp out
    waitPrompt err
    str <- getContents
    flip mapM_ (lines str) $ \ln -> do
      mapM_ (flip hPutStrLn ln) [stdout, inn] 
      waitPrompt err

waitPrompt h = hGetUntil h " < " >> putStr "Coq < "

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

