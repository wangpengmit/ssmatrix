{-# LANGUAGE LambdaCase #-}

import System.IO                                             
import System.Process    
import Debug.Trace
import System.IO.Error
import Control.Concurrent
import Data.List
import Text.Parsec
import Control.Monad.Cont
import Yield
import Control.Applicative ((<$>), (<*>))

main = do                                                    
    (inn, out, err, idd) <- runInteractiveCommand "coqtop 1>&2"
    -- (inn, out, err, idd) <- runInteractiveCommand "coqtop -emacs 1>&2"
    mapM_ (flip hSetBinaryMode True) [inn, err, out]             
    -- hSetBuffering err NoBuffering
    hSetBuffering inn NoBuffering
    -- hSetBuffering out NoBuffering
    -- hSetBuffering stdout NoBuffering
    forkIO $ getResp out
    strErr <- hGetContents err
    -- strErr <- return $ map (\x -> p x) $ strErr
    strStdin <- getContents
    -- strStdin <- return $ "About nat. \n(*\nAbout bool.\n"
    flip runContT return $ do
      g <- mkgen (\yield _ -> runParserT (pmain (lift . yield)) () "" strErr)
      let waitPrompt = do
            g () >>= \case
              More (Left c) -> do
                liftIO $ putStr $ [c]
                waitPrompt
              More (Right s) -> do
                liftIO $ putStr s
              _ -> return ()
      waitPrompt
      strStdin <- return $ lines strStdin
      -- strStdin <- return $ filter (\x -> not $ null x) strStdin
      flip mapM_ strStdin $ \ln -> do
        -- liftIO $ putStrLn $ "Sending: " ++ ln
        -- liftIO $ threadDelay 1000000
        mapM_ (liftIO . flip hPutStrLn ln) [stdout, inn] 
        -- liftIO $ putStrLn $ "Sent: " ++ ln
        waitPrompt
        -- liftIO $ putStr $ "[prompt got]"

pmain yield = many $ try onPrompt <|> onNonprompt
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
    word = letter <:> (many $ alphaNum <|> oneOf "_")

(<++>) a b = (++) <$> a <*> b
(<:>) a b = (:) <$> a <*> b

getResp out = hGetLine out >>= putStrLn >> getResp out

p x = traceShow x x

pf f x = traceShow (f x) x

