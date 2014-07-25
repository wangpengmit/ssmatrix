{-# LANGUAGE LambdaCase, FlexibleInstances, MultiParamTypeClasses #-}
import System.IO 
import System.Environment
import System.Exit
import System.Console.GetOpt
import Data.List
import Data.Maybe
import Data.Char
import Debug.Trace
import Numeric
import Text.Printf
import Data.String.Utils
import Text.Regex.PCRE
import Data.Array

main = do
  (options, fs) <- getArgs >>= parseOpt
  fin <- if length fs >= 1 then openFile (fs !! 0) ReadMode else return stdin
  fout <- if length fs >= 2 then openFile (fs !! 1) WriteMode else return stdout
  str <- hGetContents fin
  str <- return $ process str
  hPutStr fout str
  hClose fin
  hClose fout

process :: String -> String
process = unlines . getOutput . run initState . mapM_ processRegion . coqRegions . map strip . lines

-- Coq regions

coqRegions = regions beginCoq endCoq

beginCoq = isInfixOf "\\begin{flushleft}"

endCoq = isInfixOf "\\end{flushleft}"

processRegion (r, b) = case r of
  On -> onCoqRegion . map untex $ b
  Off -> tell b
  _ -> return ()

onCoqRegion = mapM_ onCmd . cmds

cmds = groupSections . sections beginCmd

beginCmd = isPrefixOf cmdPrefix

cmdPrefix = "Coq < "

onCmd (cmds, resp) = do
  mapM_ runCmd . getCmds . map (sub cmdPrefix "") $ cmds
  mapM_ onSubGoal . subGoals $ resp

data Cmd = Lemma (String, String, String) | Tex String

getCmds = mapMaybe getCmd

getCmd = msum [
  getLemma,
  getTex
  ]
         
getLemma s = do
  s <- return $ removeForall s
  _ : name : lhs : rhs : _ <- s =~~ "\\s(?:Lemma|Theorem)\\s([^\\s:]+)[^:]*:(.*)=(.*)"
  return $ Lemma (name, lhs, rhs)

getTex s = do
  _ : c : _ <- s = ~~ "\\(\\*!(.*?)\\*\\)"
  return $ Tex c

runCmd = \case
  Lemma c -> runLemma c,
  Tex c -> runTex c

runLemma c = modify $ \x -> x {lemma := c}

runTex s = do
  s <- mconcat texCmds s
  {rules := rules} <- get
  tell . mconcat . map (uncurry sub) rules $ s

texCmds = [
  texAddRule
  ]

texAddRule = subM "\\\\coqadd{(.*)}{(.*)}" $ 
  \(_ : pattern : replacement : _) -> do
    addRule pattern replacement
    return ""

addRule a b = do
  st <- get
  put st{rules := (a, b) : rules st}
  
  concat . map printLemma . mapMaybe parseLemma . mergeRegion Begin On . lemmas

subGoals = map tail . sections beginGoal

beginGoal = isInfixOf "=========="

onSubGoal s =
  _ : lhs : rhs : _ <- s =~~ "(.*)=(.*)"
  modify $ \x -> x {subgoal := (lhs, rhs)}

untex = unescape . unchar . untilde . uncommand' "medskip" . uncommand "texttt" . uneol . strip

removeForall = sub "forall[^,]*," ""

unescape = unescapeC '_' . unescapeC '$'

unescapeC c = sub ("\\\\\\" ++ [c]) [c]

unchar = subF "{\\\\char'(\\d+)}" $ \(_ : s : _) -> singleton . chr . oct $ s

uncommand name = sub ("\\\\" ++ name ++ "{(.*)}") "\\1"

uncommand' name = sub ("\\\\" ++ name) ""

untilde = sub "~" " "

uneol = sub "\\\\\\\\$" ""

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

usage = usageInfo "Usage: PostCoqTex [-h] [input file] [output file]" flags

-- utilities

-- regex utilities

subF regex func str =
  case str =~ regex of
    (before, matched, after, groups) | not $ null matched ->
      before ++ func (matched : groups) ++ (subF regex func after)
    _ -> str

subF regex func str =
  case str =~ regex of
    (before, matched, after, groups) | not $ null matched -> do
      s <- func (matched : groups)
      k <- subF regex func after
      return $ before ++ s ++ k
    _ -> return str

sub r s = subF r (fromStr s)

fromStr s = fst . foldl f (s, 0) where
  f (s, i) group = (replace ("\\" ++ show i) group s, i + 1)

instance (RegexLike a b) => RegexContext a b [b] where 
  match r s = maybe [] id (matchM r s)
  matchM = actOn (\(_,ma,_) -> map fst $ elems ma)

-- regexFailed and actOn are copied from Text.Regex.Base.Context
regexFailed :: (Monad m) => m b
regexFailed =  fail $ "regex failed to match"

actOn :: (RegexLike r s,Monad m) => ((s,MatchText s,s)->t) -> r -> s -> m t
actOn f r s = case matchOnceText r s of
    Nothing -> regexFailed
    Just preMApost -> return (f preMApost)

-- non-embedding regions with explicit begin and end mark
    
data Region = On | Off | Begin | End
              deriving (Eq)

regions begin end = groupRegion . reverse . snd. foldl f (False, []) where
  f (False, acc) x = if begin x then (True, (Begin, x) : acc) else (False, (Off, x) : acc)
  f (True, acc) x = if end x then (False, (End, x) : acc) else (True, (On, x) : acc)

groupRegion = map liftFst . groupBy eqFst

mergeRegion a b = mapRegion concat . groupRegion . map f where
  f (r, x) = (if r == a then b else r, x)

mapRegion f = map (\(r, x) -> (r, f x))

liftFst x@((r,_) : _) = (r, map snd x)

eqFst a b = fst a == fst b

-- miscellaneous

p x = traceShow x x

unique :: Eq a => [a] -> [a]
unique = map head . group

removeEmptyLines = filter (\l -> strip l /= "")

trim = removeEmptyLines . map strip

singleton a = [a]

oct s = case readOct s of
  (i, _) : _ -> i
  _ -> 0

oneIsInfixOf ls s = any (\x -> isInfixOf x s) ls

-- instance Monad m => Monoid (a -> m a) where
--   mempty = return
--   mappend = (>=>)
  
sections = foldl f (False, []) where
  f = \case
    (False, a)
