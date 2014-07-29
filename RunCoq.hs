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
import Util

main = do
  getPromptStream getInput3
  
getPromptStream k = do                                                    
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
  waitPrompt (lift . putStr . pure) (lift . putStr)
  input $ \ln -> do
    mapM_ (lift . flip hPutStrLn ln) [stdout, toCoq] 
    waitPrompt (lift . putStr . pure) (lift . putStr) -- (\_ -> lift $ putStr "Coq > ")

noop x = return ()

getInput2
  :: (Monad (t IO), Monad (t2 IO), Monad m, MonadTrans t,
      MonadTrans t2) =>
     Handle -> ((Char -> t2 IO ()) -> (t1 -> m ()) -> t IO a) -> t IO ()
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

getInput3 toCoq waitPrompt = do
  waitPrompt noop noop
  input <- lift $ getContents
  input <- return $ lines input
  flip runStateT noCoq $ mapM_ process input
  where
    process ln = do
      st <- get
      if notCoqMode st then do
        lift $ putStrLn ln
        put $ transit st ln
      else do
        put $ transit st ln
        st <- get
        if notCoqMode st then
          lift $ putStrLn ln
        else do
          if isShowCmd st then do
            lift $ putStr "Coq > "
            lift $ putStrLn ln
          else
            return ()
          lift $ hPutStrLn toCoq ln
          if isShowResp st then
            waitPrompt (lift . putStr . pure) noop
          else
            waitPrompt noop noop

transit NoCoq ln | beginCoq ln = Coq
                 | beginCoqCmd ln = CoqCmd
                 | beginCoqCmdResp ln = CoqCmdResp
transit Coq ln | endCoq ln = NoCoq
transit CoqCmd ln | endCoqCmd ln = NoCoq
transit CoqCmdResp ln | endCoqCmdResp ln = NoCoq

                                        

  --     On -> onCoqRegion b
  --     _ -> mapM_ (lift . putStrLn) b
  --   onCoqRegion = mapM_ $ \ln -> do
  --     lift $ putStr "Coq > "
  --     mapM_ (lift . flip hPutStrLn ln) [stdout, toCoq] 
  --     waitPrompt (lift . putStr . pure) noop

  
  -- mapM_ processRegion . coqRegions $ input
  -- where
  --   processRegion (r, b) = case r of
  --     On -> onCoqRegion b
  --     _ -> mapM_ (lift . putStrLn) b
  --   onCoqRegion = mapM_ $ \ln -> do
  --     lift $ putStr "Coq > "
  --     mapM_ (lift . flip hPutStrLn ln) [stdout, toCoq] 
  --     waitPrompt (lift . putStr . pure) noop

coqRegions = partitionByBeginEnd beginCoq endCoq

beginCoq s = isInfixOf "\\begin{coq_example}" s || isInfixOf "\\begin{coq_eval}" s

endCoq s = isInfixOf "\\end{coq_example}" s || isInfixOf "\\end{coq_eval}" s

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

