{-# LANGUAGE LambdaCase #-}

import System.IO                                             
import System.Process    
import Debug.Trace
import System.IO.Error
import Data.List
import Text.Parsec (runParserT, many, try, string, (<|>), letter, anyChar, alphaNum, oneOf)
import Control.Monad.Cont
import Yield
import Control.Applicative ((<$>), (<*>), pure)
import Control.Monad.State
import System.Console.GetOpt
import System.Exit
import System.Environment (getArgs)
import Data.String.Utils (strip)
import Control.Monad.Trans.Maybe
import Data.Maybe (fromMaybe, isNothing)

main = do
  (options, fs) <- getArgs >>= parseOpt
  let fin = if length fs >= 1 then fs !! 0 else "-"
  let fout = if length fs >= 2 then fs !! 1 else "-"
  hIn <- if fin /= "-" then openFile fin ReadMode else return stdin
  hOut <- if fout /= "-" then openFile fout WriteMode else return stdout
  cmain <- return $
    if elem Interactive options then
      interactive $ elem Echo options
    else
      let config = if elem Tex options || isSuffixOf ".tex" fin then texRegionConfig else vRegionConfig in
      regionSub hIn hOut config $ elem Verbose options && fout /= "-"
  flip runContT return $ (lift $ getPromptGenerator) >>= cmain
  hClose hIn
  hClose hOut

-- g : prompt generator
interactive isEcho (toCoq, g) = void $ runMaybeT $ do    
  liftIO $ hSetBuffering stdout NoBuffering
  (MaybeT $ waitPrompt g (liftIO . putStr . pure)) >>= liftIO . putStr
  input <- liftIO $ getContents
  flip mapM_ (lines input) $ \ln -> do
    when isEcho $ liftIO $ putStrLn ln
    liftIO $ hPutStrLn toCoq ln
    if strip ln == "Quit." then
      fail ""
    else do
      (MaybeT $ waitPrompt g (liftIO . putStr . pure)) >>= liftIO . putStr

regionSub hIn hOut regionCfg isVerbose (toCoq, g) = void $ flip runStateT (initCoqState regionCfg, True) $ do
  (lift $ waitPrompt g noop) >>= checkCoqLiveness
  input <- liftIO $ hGetContents hIn
  input <- return $ lines input
  mapM_ process input
  where
    process ln = do
      st <- getState
      if not $ isCoqMode regionCfg st then do
        liftIO $ hPutStrLn hOut $ translateNonCoq regionCfg ln
        putState $ transit regionCfg st ln
      else do
        putState $ transit regionCfg st ln
        st <- getState
        if not $ isCoqMode regionCfg st then
          liftIO $ hPutStrLn hOut $ translateNonCoq regionCfg ln
        else do
          whenM isAlive $ do
            when (isShowCmd regionCfg st) $ do
              let hOuts = if isVerbose then [stdout, hOut] else [hOut]
              liftIO $ hPutStr hOut "Coq < "
              liftIO $ multi hPutStrLn hOuts ln
            liftIO $ hPutStrLn toCoq ln
            onNonPrompt <- return $ if isShowResp regionCfg st then
              liftIO . hPutStr hOut . pure
            else
              noop
            (lift $ waitPrompt g onNonPrompt) >>= checkCoqLiveness
    checkCoqLiveness = whenF isNothing $ do
      putSnd False
      liftIO $ hPutStrLn stderr "Coq quitted."
    isAlive = snd <$> get
    getState = fst <$> get
    putState st = putFst st

whenM m a = m >>= flip when a

whenF f a x = when (f x) a

putFst v = modify $ \(_, b) -> (v, b)

putSnd v = modify $ \(a, _) -> (a, v)

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
  transit = \_ _ -> CoqCmdResp,
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

getPromptGenerator = do                                                    
    (toCoq, fromCoq, _, handleCoq) <- liftIO $ runInteractiveCommand "coqtop 2>&1"
    -- (toCoq, fromCoq, _, handleCoq) <- liftIO $ runInteractiveCommand "coqtop -emacs 2>&1"
    mapM_ (liftIO . flip hSetBinaryMode True) [toCoq, fromCoq]             
    liftIO $ hSetBuffering toCoq NoBuffering
    strFromCoq <- liftIO $ hGetContents fromCoq
    g <- mkgen (\yield _ -> runParserT (promptGenerator (lift . yield)) () "strFromCoq" strFromCoq)
    return (toCoq, g)

promptGenerator yield = many $ try onPrompt <|> onNonprompt
  where
    onPrompt = do
      s <- prompt
      yield $ Right s
    prompt = word <++> string " < "
    -- prompt = string "<prompt>" <++> word <++> string " < " <++> word <++> string " |" <++> option "" word <++> string "| " <++> word <++> string " < </prompt>"
    onNonprompt = do
      c <- anyChar
      yield $ Left c
    word = letter <:> (many $ alphaNum <|> oneOf "_'")

waitPrompt g onNonPrompt = 
  g () >>= \case
    More (Left c) -> onNonPrompt c >> waitPrompt g onNonPrompt
    More (Right s) -> return $ Just s
    _ -> return Nothing

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

