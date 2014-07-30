{-# LANGUAGE LambdaCase, FlexibleInstances, MultiParamTypeClasses, FlexibleContexts #-}
import System.IO 
import System.Environment (getArgs)
import System.Exit
import System.Console.GetOpt
import Data.List
import Data.Maybe
import Data.Char (chr)
import Debug.Trace (traceShow)
import Numeric (readOct)
import Text.Printf (printf)
import Data.String.Utils (strip, replace)
import Text.Regex.PCRE
import Data.Array (elems)
import Control.Monad ((>=>))
import Control.Monad.Writer (runWriter, tell)
import Control.Monad.State (runStateT, get, put, modify)
import Control.Monad.Identity (runIdentity)
import Data.Foldable (asum)
import Data.Monoid
import Util
import System.IO.Error (tryIOError)

main = do
  (options, fs) <- getArgs >>= parseOpt
  let fin = if length fs >= 1 then fs !! 0 else "-"
  let fout = if length fs >= 2 then fs !! 1 else "-"
  hIn <- if fin /= "-" then openFile fin ReadMode else return stdin
  hOut <- if fout /= "-" then openFile fout WriteMode else return stdout
  str <- hGetContents hIn
  str <- doIncludes str
  -- putStrLn str
  str <- return $ process $ str
  hPutStr hOut str
  hClose hIn
  hClose hOut

doIncludes = subM "\\\\coq_output{(.*?)}" $ \(_ : filename : _) -> do
  (tryIOError $ readFile filename) >>= \case
    Left _ -> return $ "Can read file: " ++ filename
    Right s -> return $ beginCoqOutputStr ++ "\n" ++ s ++ "\n" ++ endCoqOutputStr ++ "\n"

data St = St {
  lemma :: Lemma,
  subgoal :: Equation,
  rules :: [(String, String)]
  }

data Lemma = Lemma {
  name :: String,
  equation :: Equation
  } deriving (Show)

data Equation = Equation {
  lhs :: String,
  rhs :: String
} deriving (Show)
  
process = unlines . getOutput . run initState . mapM_ processRegion . coqRegions . map strip . lines

initState = St {
  lemma = Lemma "*no-name*" (Equation "*no-from*" "*no-to*"),
  subgoal = (Equation "*no-lhs*" "*no-rhs*"),
  rules = []
  }

run s = runWriter . flip runStateT s

getOutput = snd

-- Coq regions

coqRegions = partitionByBeginEnd beginCoq endCoq

beginCoq = isInfixOf beginCoqOutputStr

beginCoqOutputStr = "\\begin{coq_output}"

endCoq = isInfixOf endCoqOutputStr

endCoqOutputStr = "\\end{coq_output}"

processRegion (r, b) = case r of
  On -> onCoqRegion b
  Off -> tell b
  _ -> return ()

onCoqRegion = mapM_ onConversation . conversations

conversations = itemizeBeginOn . partitionByBegin beginCmd

beginCmd = isPrefixOf cmdPrefix . strip

cmdPrefix = "Coq < "

onConversation (cmds, resp) = do
  onCmds cmds
  onResp resp
  
onCmds = mapM_ runCmd . getCmds . map (sub cmdPrefix "")

data Cmd = LemmaCmd Lemma | InCommentCmd ([InCommentOpts], String) deriving (Show)

getCmds = mapMaybe getCmd

getCmd = choice [
  getLemmaCmd,
  getInCommentCmd
  ]

getLemmaCmd s = do
  s <- return $ removeForall s
  _ : name : lhs : rhs : _ <- s =~~ "\\b(?:Lemma|Theorem)\\s+([^\\s:]+)[^:]*:(.*)=(.*)\\."
  return $ LemmaCmd $ Lemma name $ Equation lhs rhs

getInCommentCmd s = do
  _ : opts : c : _ <- s =~~ "\\(\\*(![-n]*)(.*?)\\*\\)"
  return $ InCommentCmd (parseInCommentOpts opts, c)

parseInCommentOpts s = concat [
  if elem '-' s then [NoPrint] else [],
  if elem 'n' s then [NoSub] else []
  ]

data InCommentOpts = NoPrint | NoSub deriving (Eq, Show)

runCmd c = case c of
  LemmaCmd c -> runLemmaCmd c
  InCommentCmd c -> runInCommentCmd c

runLemmaCmd c = modify $ \x -> x {lemma = c}

runInCommentCmd (opts, s) = do
  -- run builtin \coqXXX commands
  s <- chainM texCmds s
  if not $ elem NoPrint opts then do
    s <- if not $ elem NoSub opts then
           do
             -- string substitution using rules registered on-the-fly
             St {rules = rules} <- get
             return . chain (map (uncurry sub) rules) $ s
         else
             return s
    tell . singleton $ s
  else
    return ()

texCmds = [
  -- \coqadd{}{}
  texAddRule,
  -- \coqvar{}
  texVar
  ]

texAddRule = subM "\\\\coqadd{(.*)}{(.*)}" $ 
  \(_ : p : s : _) -> do
    addRule p s
    return ""

addRule a b = do
  st <- get
  put st{ rules = rules st ++ [(a, b)] }

-- replace \coqvar{...} with corresponding value according to vars
texVar = chainM $ map (uncurry subVar) vars

vars = [
  ("name", name . lemma),
  ("from", lhs . equation . lemma),
  ("to", rhs . equation . lemma),
  ("lhs", lhs . subgoal),
  ("rhs", rhs . subgoal)
  ]

subVar name f = subM (varTag name) $ \ _ -> get >>= return . f

varTag name =  printf "\\\\coqvar{%s}" name

-- process coqtop responses
-- currently only process the first subgoal

onResp =  onSubgoal . fromMaybe "" . listToMaybe . subgoals

subgoals = map unwords . filterByEqFst On . partitionByBegin beginSubgoal

beginSubgoal = isInfixOf "=========="

onSubgoal s = 
  case s =~ "(.*)=(.*)" of
    _ : lhs : rhs : _ ->
      modify $ \x -> x {subgoal = Equation lhs rhs}
    _ -> return ()

-- text processors

untex = unescape . unchar . untilde . untag "medskip" . uncommand "texttt" . uneol . strip

unescape = unescapes "{}_$&" . sub "{<}" "<"

unescapes = chain . map unescapeC
  
unescapeC c = sub ("\\\\\\" ++ [c]) [c]

unchar = subF "{\\\\char'(\\d+)}" $ \(_ : s : _) -> singleton . chr . oct $ s

uncommand name = sub ("\\\\" ++ name ++ "{(.*)}") "\\1"

untag name = sub ("\\\\" ++ name) ""

untilde = sub "~" " "

uneol = sub "\\\\\\\\$" ""

removeForall = sub "forall[^,]*," ""

-- commandline interface

data Flag = Help 
            deriving (Eq)
                   
flags = [
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

-- utilities

-- regex utilities

-- subsitute all occurances of regex
subM :: Monad m => String -> ([String] -> m String) -> String -> m String
subM regex func str =
  fromMaybe (return str) $ do
    (before, matched, after, groups) <- str =~~~ regex
    return $ do
      s <- func (matched : groups)
      k <- if length after < length str then -- avoid infinite loop
             subM regex func after
           else return str
      return $ before ++ s ++ k

subF r f = runIdentity . subM r (return . f)

sub r s = subF r (fromStr s)

fromStr s = fst . foldl f (s, 0) where
  f (s, i) group = (replace ("\\" ++ show i) group s, i + 1)

-- a safer version of =~~, where compile error of regex won't crash the execution
(=~~~) :: (RegexMaker Regex CompOption ExecOption source,RegexContext Regex source1 target,Monad m)
      => source1 -> source -> m target

(=~~~) x r = let makeM :: (RegexMaker Regex CompOption ExecOption a, Monad m) => a -> m Regex
                 makeM = makeRegexM
             in do
               r <- makeM r
               matchM r x

-- s =~ r :: [String] will return the first match and its subgroups
instance (RegexLike a b) => RegexContext a b [b] where 
  match r s = maybe [] id (matchM r s)
  matchM = actOn (\(_,ma,_) -> map fst $ elems ma)

-- regexFailed and actOn are copied from Text.Regex.Base.Context
regexFailed :: (Monad m) => m b
regexFailed =  fail $ "regex failed to match"

actOn f r s = case matchOnceText r s of
    Nothing -> regexFailed
    Just preMApost -> return (f preMApost)

-- miscellaneous

unique :: Eq a => [a] -> [a]
unique = map head . group

removeEmptyLines = filter (\l -> strip l /= "")

trim = removeEmptyLines . map strip

singleton a = [a]

oct s = case readOct s of
  (i, _) : _ -> i
  _ -> 0

oneIsInfixOf ls s = any (flip isInfixOf s) ls

-- returns the result of the first function in fs to succeed
choice fs x = asum $  map ($ x) fs

-- chain [f, g, h, ...] = ... . h . g . f
chain = appEndo . mconcat . map Endo . reverse

-- chain [f, g, h, ...] = f >=> g >=> h >=> ...
chainM = appEndoM . mconcat . map EndoM

newtype EndoM m a = EndoM { appEndoM :: a -> m a}

instance Monad m => Monoid (EndoM m a) where
  mempty = EndoM return
  EndoM f `mappend` EndoM g = EndoM (f >=> g)

-- p x = traceShow x x

-- pf f x = traceShow (f x) x

