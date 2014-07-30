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
import Control.Monad.State (runStateT, get, put)
import System.Console.GetOpt
import System.Exit
import System.Environment (getArgs)
import Data.String.Utils (strip)
import Control.Monad.Trans.Maybe (runMaybeT)

main = do
  (options, fs) <- getArgs >>= parseOpt
  let fin = if length fs >= 1 then fs !! 0 else "-"
  let fout = if length fs >= 2 then fs !! 1 else "-"
  hIn <- if fin /= "-" then openFile fin ReadMode else return stdin
  hOut <- if fout /= "-" then openFile fout WriteMode else return stdout
  if elem Interactive options then
    void $ getPromptStream $ interactive $ elem Echo options
  else do
    let config = if elem Tex options || isSuffixOf ".tex" fin then texRegionConfig else vRegionConfig
    void $ getPromptStream $ regionSub hIn hOut config $ elem Verbose options && fout /= "-"
  hClose hIn
  hClose hOut
  
interactive isEcho (toCoq, waitPrompt) = do    
  liftIO $ hSetBuffering stdout NoBuffering
  waitPrompt (liftIO . putStr . pure) (liftIO . putStr)
  input <- liftIO $ getContents
  input <- return $ lines input
  input <- return $ runMaybeT . flip mapM_ input
  input $ \ln -> do
    if isEcho then
      liftIO $ putStrLn ln
    else
      return ()
    liftIO $ hPutStrLn toCoq ln
    if strip ln == "Quit." then
      fail ""
    else
      void $ lift $ waitPrompt (liftIO . putStr . pure) (liftIO . putStr)

regionSub hIn hOut regionCfg isVerbose (toCoq, waitPrompt) = do
  waitPrompt noop noop
  input <- liftIO $ hGetContents hIn
  input <- return $ lines input
  flip runStateT (initCoqState regionCfg) $ mapM_ process input
  where
    process ln = do
      st <- get
      if not $ isCoqMode regionCfg st then do
        liftIO $ hPutStrLn hOut $ translateNonCoq regionCfg ln
        put $ transit regionCfg st ln
      else do
        put $ transit regionCfg st ln
        st <- get
        if not $ isCoqMode regionCfg st then
          liftIO $ hPutStrLn hOut $ translateNonCoq regionCfg ln
        else do
          if isShowCmd regionCfg st then do
            let hOuts = if isVerbose then [stdout, hOut] else [hOut]
            liftIO $ hPutStr hOut "Coq < "
            liftIO $ multi hPutStrLn hOuts ln
          else
            return ()
          liftIO $ hPutStrLn toCoq ln
          if isShowResp regionCfg st then
            void $ lift $ waitPrompt (liftIO . hPutStr hOut . pure) noop
          else
            void $ lift $ waitPrompt noop noop

data CoqState = NoCoq | Coq | CoqCmd | CoqCmdResp deriving (Eq)

data RegionConfig = RegionConfig {
  initCoqState :: CoqState,
  isCoqMode :: CoqState -> Bool,
  isShowCmd :: CoqState -> Bool,
  isShowResp :: CoqState -> Bool,
  transit :: CoqState -> String -> CoqState,
  translateNonCoq :: String -> String
  }

-- Region configuration for .tex files
texRegionConfig = RegionConfig {
  initCoqState = NoCoq,
  isCoqMode = (/= NoCoq),
  isShowCmd = (== CoqCmd) <||> (== CoqCmdResp),
  isShowResp = (== CoqCmdResp),
  transit = texTransit,
  translateNonCoq = texTranslateNonCoq
}

-- Region configuration for .v files, which trivially treats the whole file as a region
vRegionConfig = RegionConfig {
  initCoqState = CoqCmdResp,
  isCoqMode = \_ -> True,
  isShowCmd = \_ -> True,
  isShowResp = \_ -> True,
  transit = \_ -> \_ -> CoqCmdResp,
  translateNonCoq = id
  }
                
texTransit NoCoq ln | beginCoq ln = Coq
               | beginCoqCmd ln = CoqCmd
               | beginCoqCmdResp ln = CoqCmdResp
texTransit Coq ln | endCoq ln = NoCoq
texTransit CoqCmd ln | endCoqCmd ln = NoCoq
texTransit CoqCmdResp ln | endCoqCmdResp ln = NoCoq
texTransit st _ = st

texTranslateNonCoq ln =
  if beginCoq ln || beginCoqCmd ln || beginCoqCmdResp ln then
    "\\begin{coq_output}"
  else if endCoq ln || endCoqCmd ln || endCoqCmdResp ln then
         "\\end{coq_output}"
       else
         ln
         
beginCoq = isInfixOf "\\begin{coq_eval}"
beginCoqCmd = isInfixOf "\\begin{coq_example*}"
beginCoqCmdResp = isInfixOf "\\begin{coq_example}"
endCoq = isInfixOf "\\end{coq_eval}"
endCoqCmd = isInfixOf "\\end{coq_example*}"
endCoqCmdResp = isInfixOf "\\end{coq_example}"

-- k : continuation
getPromptStream k = do                                                    
    (toCoq, fromCoq, _, handleCoq) <- runInteractiveCommand "coqtop 2>&1"
    -- (toCoq, fromCoq, _, handleCoq) <- runInteractiveCommand "coqtop -emacs 2>&1"
    mapM_ (flip hSetBinaryMode True) [toCoq, fromCoq]             
    hSetBuffering toCoq NoBuffering
    strFromCoq <- hGetContents fromCoq
    flip runContT return $ do
      g <- mkgen (\yield _ -> runParserT (promptParser (lift . yield)) () "strFromCoq" strFromCoq)
      let waitPrompt onNonPrompt onPrompt = do
            g () >>= \case
              More (Left c) -> do
                onNonPrompt c
                waitPrompt onNonPrompt onPrompt
              More (Right s) -> do
                void $ onPrompt s
              _ -> return ()
      k (toCoq, waitPrompt)

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

-- commandline interface

data Flag = Help | Interactive | Echo | Tex | Verbose
            deriving (Eq)
                   
flags = [
 Option ['i'] ["interact"] (NoArg Interactive) "Run interactive mode",
 Option ['e'] ["echo"] (NoArg Echo) "Echo command in interactive mode",
 Option ['v'] ["verbose"] (NoArg Verbose) "Verbose mode, print more information",
 Option ['t'] ["tex"] (NoArg Tex) "Run Coq in regions delimited by \\begin{coq_example}, \\begin{coq_example*} or \\begin{coq_eval} (and corresponding \\end{...} tags), and replace them with Coq responses surrounded by \\begin{coq_output} and \\end{coq_output}. This mode will be automatically chosen if the input file name ends with .tex",
 Option ['h'] ["help"] (NoArg Help) "Print this help message"
 ]

parseOpt argv = case getOpt Permute flags argv of
  (args, files, []) -> do
    if Help `elem` args then do
      hPutStrLn stderr usage
      exitWith ExitSuccess
    else return (args, files)
  (_,_,errs) -> do
    hPutStrLn stderr (concat errs ++ usage)
    exitWith (ExitFailure 1)

usage = usageInfo "Usage: PostCoqTex [-h] [input file] [output file]\nInput (output) file name can be -, indicating stdin (stdout)" flags

-- utilitites

(<++>) a b = (++) <$> a <*> b
(<:>) a b = (:) <$> a <*> b

(<||>) a b = \x -> a x || b x

noop x = return ()

multi f ls x = sequence_ $ map ($ x) $ map f ls

p x = traceShow x x

pf f x = traceShow (f x) x

