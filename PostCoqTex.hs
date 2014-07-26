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
import Control.Monad.Writer
import Control.Monad.Trans.State

main = do
  (options, fs) <- getArgs >>= parseOpt
  fin <- if length fs >= 1 then openFile (fs !! 0) ReadMode else return stdin
  fout <- if length fs >= 2 then openFile (fs !! 1) WriteMode else return stdout
  str <- hGetContents fin
  str <- return $ process str
  hPutStr fout str
  hClose fin
  hClose fout

data St = St {
  lemma :: Lemma,
  subgoal :: Equation,
  rules :: [(String, String)]
  }

data Lemma = Lemma {
  name :: String,
  equation :: Equation
  }

data Equation = Equation {
  lhs :: String,
  rhs :: String
}
  
process :: String -> String
process = unlines . getOutput . flip run initState . mapM_ processRegion . coqRegions . map strip . lines

initState = St {
  lemma = Lemma "" (Equation "" ""),
  subgoal = (Equation "" ""),
  rules = []
  }

run m s = runWriter $ runStateT m s

getOutput = snd

-- Coq regions

coqRegions = partitionByBeginEnd beginCoq endCoq

beginCoq = isInfixOf "\\begin{flushleft}"

endCoq = isInfixOf "\\end{flushleft}"

processRegion (r, b) = case r of
  On -> onCoqRegion . map untex $ b
  Off -> tell b
  _ -> return ()

onCoqRegion = mapM_ onConversation . conversations

conversations = itemizeBeginOn . concatByFst. partitionByBegin beginCmd

beginCmd = isPrefixOf cmdPrefix

cmdPrefix = "Coq < "

onConversation (cmds, resp) = do
  onCmds cmds
  onResp resp
  
onCmds = mapM_ runCmd . getCmds . map (sub cmdPrefix "")

data Cmd = CmdLemma Lemma | CmdTex String

getCmds = mapMaybe getCmd

getCmd = msum [
  getLemma,
  getTex
  ]
         
getLemma s = do
  s <- return $ removeForall s
  _ : name : lhs : rhs : _ <- s =~~ "\\s(?:Lemma|Theorem)\\s([^\\s:]+)[^:]*:(.*)=(.*)"
  return $ CmdLemma $ Lemma name $ Equation lhs rhs

getTex s = do
  _ : c : _ <- s =~~ "\\(\\*!(.*?)\\*\\)"
  return $ CmdTex c

runCmd = \case
  CmdLemma c -> runLemma c
  CmdTex c -> runTex c

runLemma c = modify $ \x -> x {lemma = c}

runTex s = do
  s <- mconcat texCmds s
  St {rules = rules} <- get
  tell . mconcat . map (uncurry sub) rules $ s

texCmds = [
  texAddRule,
  texVar
  ]

texAddRule = subM "\\\\coqadd{(.*)}{(.*)}" $ 
  \(_ : pattern : replacement : _) -> do
    addRule pattern replacement
    return ""

addRule a b = do
  st <- get
  put st{rules = (a, b) : rules st}
  
texVar = mconcat . map (uncurry subVar) vars

subVar name f = subM (printf "\\\\coqvar{%s}" name) $ get >>= return . f
  
vars = [
  ("name", name . lemma),
  ("begin", lhs . equation . lemma),
  ("end", lhs . equation . lemma),
  ("lhs", lhs . subgoal),
  ("rhs", rhs . subgoal)
  ]

-- currently only process the first subgoal

onResp =  onSubgoal . fromMaybe [] . listToMaybe . subgoals

subgoals = filterByEqFst On . partitionByBegin beginGoal

beginGoal = isInfixOf "=========="

onSubgoal s = do
  _ : lhs : rhs : _ <- s =~~ "(.*)=(.*)"
  modify $ \x -> x {subgoal = Equation lhs rhs}

-- text processors

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

subM regex func str =
  case str =~ regex of
    (before, matched, after, groups) | not $ null matched -> do
      s <- func (matched : groups)
      k <- subM regex func after
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

-- non-embedding regions with begin and/or end mark
    
data Region = On | Off | Begin | End
            deriving (Eq)

partitionByBeginEnd begin end = groupLiftByFst . reverse . snd. foldl f (False, []) where
  f (False, acc) x = if begin x then (True, (Begin, x) : acc) else (False, (Off, x) : acc)
  f (True, acc) x = if end x then (False, (End, x) : acc) else (True, (On, x) : acc)

partitionByBegin begin = foldl f (False, []) where
  f (False, acc) x = if begin x then (True, (Begin, x) : acc) else (False, (Off, x) : acc)
  f (True, acc) x = (True, if begin x then Begin else On : acc)

itemizeBeginOn = final . foldl f (Nothing, []) . filterByNeFst Off where
  f (cur, acc) (Begin, x) = (Just (x, mempty), case cur of {Just cur -> cur : acc ;  _ -> acc})
  f (Just (a, _), acc) (On, x) = (Just (a, x), acc)
  f a _ = a
  final (Just cur, acc) = cur : acc
  final (_, acc) = acc

groupByFst = groupBy eqFst

groupLiftByFst = map liftFst . groupByFst

concatByFst = mapSnd concat . groupLiftByFst

combineByFst a b = concatByFst . map f where
  f (r, x) = (if r == a then b else r, x)

mapSnd f = map (\(r, x) -> (r, f x))

filterByEqFst a = map snd . filter (\x -> fst x == a)

filterByNeFst a = map snd . filter (\x -> fst x /= a)

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
