{-# LANGUAGE LambdaCase, FlexibleInstances, MultiParamTypeClasses, FlexibleContexts, UndecidableInstances, FunctionalDependencies, Rank2Types #-}
import System.IO 
import System.Environment (getArgs)
import System.Exit
import System.Console.GetOpt
import Data.List
import Data.Maybe
import Data.Char (chr)
-- import Debug.Trace (traceShow)
import Numeric (readOct)
import Text.Printf (printf)
import Data.String.Utils (strip, replace)
import Text.Regex.PCRE
import Data.Array (elems)
import Control.Monad ((>=>), when, (<=<), liftM)
import Control.Monad.Writer (runWriter, tell, Writer, MonadWriter)
import Control.Monad.State (runStateT, modify, runState, State, StateT, MonadState, put)
import qualified Control.Monad.State (get)
import Control.Monad.Identity (runIdentity)
import Data.Foldable (asum)
import Data.Monoid
import System.IO.Error (tryIOError)
import Data.Function (on)
import MatchParen (matchParen, original, Paren(..))
import Control.Monad.Error (ErrorT, runErrorT)
import Control.Monad.Identity (Identity)
import Tag (TWriterT, TWriter, ttell, Contains, runTWriter, runTWriterT)

main = do
  (options, fs) <- getArgs >>= parseOpt
  let fin = if length fs >= 1 then fs !! 0 else "-"
  let fout = if length fs >= 2 then fs !! 1 else "-"
  hIn <- if fin /= "-" then openFile fin ReadMode else return stdin
  hOut <- if fout /= "-" then openFile fout WriteMode else return stdout
  str <- hGetContents hIn
  str <- doIncludes str
  (str, err) <- return $ process $ str
  hPutStr hOut str
  hPutStr stderr err
  hClose hIn
  hClose hOut

doIncludes = subM "\\\\coqOutput{(.*?)}" $ \(_ : filename : _) -> do
  (tryIOError $ readFile filename) >>= \case
    Left _ -> return $ "Can read file: " ++ filename
    Right s -> return $ beginCoqOutputStr ++ "\n" ++ s ++ "\n" ++ endCoqOutputStr ++ "\n"

process = run initState . mapM_ processRegion . coqRegions . map strip . lines

coqRegions = partitionByBeginEnd beginCoq endCoq

beginCoq = isInfixOf beginCoqOutputStr

beginCoqOutputStr = "\\begin{coq_output}"

endCoq = isInfixOf endCoqOutputStr

endCoqOutputStr = "\\end{coq_output}"

processRegion (r, b) = case r of
  On -> onCoqRegion b
  Off -> tellOut b
  _ -> return ()

run :: St -> M a -> (String, String)
run s = (unlines >< unlines) . getOutput . runM s

runM s = flip runState s . runTWriterT . runTWriterT

getOutput = (snd . fst |><| snd) . fst

type M = TWriterT Out [String] (TWriterT Err [String] (State St ))

data St = St {
  lemma :: Lemma,
  subgoal :: Equation,
  rules :: [(Regex, String)]
  }

data Lemma = Lemma {
  name :: String,
  equation :: Equation
  } deriving (Show)

data Equation = Equation {
  lhs :: String,
  rhs :: String
} deriving (Show)
  
type CanWriteTo t w m a =  (Monad m, Contains m t n, MonadWriter w n) => a

tellOut :: CanWriteTo Out w m (w -> m ())
tellOut = ttell Out

tellErr :: CanWriteTo Err w m (w -> m ())
tellErr = ttell Err

data Out = Out
data Err = Err

initState = St {
  lemma = Lemma "*no-name*" (Equation "*no-from*" "*no-to*"),
  subgoal = (Equation "*no-lhs*" "*no-rhs*"),
  rules = []
  }

onCoqRegion = mapM_ onConversation . conversations

conversations = itemizeBeginOn . partitionByBegin beginCmd

beginCmd = isPrefixOf cmdPrefix . strip

cmdPrefix = "Coq < "

onConversation (cmds, resp) = do
  onCmds cmds
  onResp resp
  
onCmds = mapM_ runCmd <=< getCmds . map (sub cmdPrefix "")

data Cmd = LemmaCmd Lemma | InCommentCmd ([InCommentOpts], String) deriving (Show)

-- getCmds will only have the side-effect of generating error messages, not generating output
getCmds :: CanWriteTo Err [String] m ([String] -> m [Cmd])
getCmds = return . mapMaybe getCmd . concatMap onSplit <=< splitByComment . unwords

onSplit = \case
  Left s -> breakCoqCommands s
  Right s -> [s]

splitByComment s = post . matchParen [("(*", "*)")] $ s where
  post = \case
    Left e -> tellErr [format "Warning: error in parsing comments: {0}\nin: {1}" [show e, s]] >> return [Left $ s]
    Right ls -> return $ map tag ls
  tag a = let s = original a in case a of
    NonParen _ -> Left s
    Paren _ _ _ -> Right s 

breakCoqCommands = lines . sub "\\.\\s" ".\n" . unwords . lines

getCmd = choice [
  getLemmaCmd,
  getInCommentCmd
  ]

getLemmaCmd s = do
  s <- return $ removeForall s
  _ : name : lhs : rhs : _ <- s =~~ "\\b(?:Lemma|Theorem)\\s+([^\\s:]+)[^:]*:(.*)=(.*)\\.(?:\\s|$)"
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
  when (not $ elem NoPrint opts) $ printComment (not $ elem NoSub opts) s

printComment :: ReadOnly St m => CanWriteTo Out [String] m (Bool -> String -> m ())
printComment isSub s = do
  s <- if isSub then do
         -- string substitution using rules registered on-the-fly
         rules <- getRules
         return . chain (map (uncurry subC) rules) $ s
       else
         return s
  s <- return $ texLocalSub s
  tellOut . singleton $ s

texLocalSub = until (\s -> s =~ localSubPattern == False) $ subF localSubPattern $ \(_ : r : s : body : _) -> sub r s body

localSubPattern = format "\\\\coqLocalSub{0}(.*)" [subPattern]

texCmds = [
  -- \coqAddRule{}{}
  texAddRule,
  -- \coqVar{}
  texVar
  ]

texAddRule = subM (format "\\\\coqAddRule{0}" [subPattern]) $ 
  \(_ : ptrn : s : _) -> do
    case runEitherE $ makeRegexM ptrn of
      Right re -> do
        addRule re s
      Left e ->
        tellErr [format "Warning: error in regex {0} : {1}" [ptrn, e]]
    return ""

subPattern = format "/({0})/({0})/" [subPatternContent]

subPatternContent = "(?:[^/]|\\/)*?"

getRules :: ReadOnly St m => m [(Regex, String)]
getRules = do
  St {rules = rules} <- get
  return rules
  
addRule a b = do
  st <- get
  put st{ rules = rules st ++ [(a, b)] }

-- replace \coqVar{...} with corresponding value according to vars
texVar :: ReadOnly St m => String -> m String
texVar = chainM $ map (uncurry subVar) vars

vars = [
  ("name", name . lemma),
  ("from", lhs . equation . lemma),
  ("to", rhs . equation . lemma),
  ("lhs", lhs . subgoal),
  ("rhs", rhs . subgoal)
  ]

subVar :: ReadOnly St m => String -> (St -> String) -> String -> m String
subVar name f = subM (varTag name) $ \ _ -> get >>= return . f

varTag name =  printf "\\\\coqVar{%s}" name

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
{- name conventions:
   C : using the compiled version of the regex
   M : with monads
   F : with functions
-}
matchAllCM :: Monad m => Regex -> ((String , String , String, [String]) -> m String) -> String -> m String
matchAllCM regex func str =
  fromMaybe (return str) $ do
    (before, matched, after, groups) <- matchM regex str
    return $ do
      s <- func (before, matched, after, groups)
      k <- if length after < length str then -- avoid infinite loop
             matchAllCM regex func after
           else return str
      return $ s ++ k

subCM r f = matchAllCM r (\(before, matched, _, groups) -> (before ++) <$$> f (matched : groups))

subCF r f = runIdentity . subCM r (return . f)

subC r s = subCF r (fromStr s)

matchAllM :: Monad m => String -> ((String , String , String, [String]) -> m String) -> String -> m String
matchAllM regex func str = do
  regex <- makeRegexM regex
  matchAllCM regex func str

splitBy r s = let (remain, ls) = runState m [] in reverse (Left remain : ls)
  where
    m = flip (matchAllM r) s $ \(before, matched, _, _) -> do
      modify $ (Left before :)
      modify $ (Right matched :)
      return ""

subM r f = matchAllM r (\(before, matched, _, groups) -> (before ++) <$$> f (matched : groups))

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

-- non-embedding regions with begin and/or end marks
    
data Region = On | Off | Begin | End
            deriving (Eq, Show)

-- partition with explicit begin and end marks
partitionByBeginEnd begin end = groupLiftByFst . reverse . snd. foldl f (False, []) where
  f (False, acc) x = if begin x then (True, (Begin, x) : acc) else (False, (Off, x) : acc)
  f (True, acc) x = if end x then (False, (End, x) : acc) else (True, (On, x) : acc)

-- partition with only begin marks
partitionByBegin begin = groupLiftByFst . reverse . snd . foldl f (False, []) where
  f (False, acc) x = if begin x then (True, (Begin, x) : acc) else (False, (Off, x) : acc)
  f (True, acc) x = (True, (if begin x then Begin else On, x) : acc)

-- convert a sequence of [(Off, _), (Begin, x1), (On, y1), (Begin, x2), (On, y2), ...] to [(x1,y1), (x2, y2), ...]
itemizeBeginOn :: Monoid a => [(Region, a)] -> [(a, a)]
itemizeBeginOn = reverse . final . foldl f (Nothing, []) . filterByNeFst Off where
  f (cur, acc) (Begin, x) = (Just (x, mempty), case cur of {Just cur -> cur : acc ;  _ -> acc})
  f (Just (a, _), acc) (On, x) = (Just (a, x), acc)
  f a _ = a
  final (Just cur, acc) = cur : acc
  final (_, acc) = acc

groupByFst = groupBy eqFst

groupLiftByFst = map liftFst . groupByFst

concatByFst = (map . mapSnd) concat . groupLiftByFst

combineByFst a b = concatByFst . (map . mapFst) (change a b)

filterByEqFst a = map snd . filter (\x -> fst x == a)

filterByNeFst a = filter (\x -> fst x /= a)

liftFst x@((r,_) : _) = (r, map snd x)

mapFst f (a, b) = (f a, b)

mapSnd f (a, b) = (a, f b)

eqFst = (==) `on` fst

change a b x = if x == a then b else x

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
chainM :: Monad m => [a -> m a] -> a -> m a
chainM = appEndoM . mconcat . map EndoM

newtype EndoM m a = EndoM { appEndoM :: a -> m a}

instance Monad m => Monoid (EndoM m a) where
  mempty = EndoM return
  EndoM f `mappend` EndoM g = EndoM (f >=> g)

format a b = doFormat a (0::Int,b)
    where
    doFormat a (_,[]) = a
    doFormat a (n,(b:bs)) = replace (old n) b a `doFormat` (n+1,bs)
    old n = "{" ++ show n ++ "}"

-- a Monad instance for Either where fail = Left
type EitherE e = ErrorT e Identity

runEitherE = runIdentity . runErrorT

f >< g = \(a, b) -> (f a, g b)
fork a = (a, a)
f |><| g = (f >< g) . fork
infixr 8 |><|

f <$$> m = liftM f m

class Monad m => ReadOnly s m | m -> s where
  get :: m s

instance MonadState s m => ReadOnly s m where
  get = Control.Monad.State.get
  
-- p x = traceShow x x

-- pf f x = traceShow (f x) x
