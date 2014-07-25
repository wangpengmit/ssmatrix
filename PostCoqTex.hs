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

process = unlines . concatMap processBlock . coqBlocks . map strip . lines

coqBlocks = regions beginBlock endBlock

beginBlock = isInfixOf "\\begin{flushleft}"

endBlock = isInfixOf "\\end{flushleft}"

processBlock = \case
  (On, b) -> concat . map printLemma . mapMaybe parseLemma . mergeRegion Begin On . lemmas $ b
  (_, b) -> b

lemmas = regions beginLemma endLemma

beginLemma = oneIsInfixOf ["~Lemma~", "~Theorem~"]

endLemma = isInfixOf "~Qed."

printLemma (name, formulas) = printf "%s:" name : formulas

parseLemma = \case
  (On, b) -> 
      let (name, lhs, rhs) = getLemma b in
      let steps = map processGoal . goals $ b in
      let formulas = unique . trim $ lhs : steps ++ [rhs] in
      Just (name, formulas)
  _ -> Nothing

getLemma = getLemmaParts . untex . takeWhile (isInfixOf "Coq~{<}~")

getLemmaParts :: String -> (String, String, String)
getLemmaParts s = fromMaybe ("", "", "") $ do
  s <- return $ removeForall s
  _ : name : lhs : rhs : _ <- s =~~ "\\s(?:Lemma|Theorem)\\s([^\\s:]+)[^:]*:(.*)=(.*)"
  return (name, lhs, rhs)

removeForall = sub "forall[^,]*," ""

goals = regions beginGoal endGoal

beginGoal = isInfixOf "=========="

endGoal = isInfixOf "\\medskip"

processGoal = \case
  (On, b) -> lhs . untex $ b
  _ -> ""

untex = unescape . unchar . unwords . map (strip . untilde . uncommand "texttt" . uneol)

lhs s = fromMaybe "" $ s =~~ "(.*)=" >>= return . (!! 1)

unescape = unescapeC '_' . unescapeC '$'

unescapeC c = sub ("\\\\\\" ++ [c]) [c]

unchar = subF "{\\\\char'(\\d+)}" $ \(_ : s : _) -> singleton . chr . oct $ s

uncommand name = sub ("^\\\\" ++ name ++ "{(.*)}$") "\\1"

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

singleton a = [a]

oct s = case readOct s of
  (i, _) : _ -> i
  _ -> 0

subF regex func str =
  case str =~ regex of
    (before, matched, after, groups) | not $ null matched ->
      before ++ func (matched : groups) ++ (subF regex func after)
    _ -> str

sub r s = subF r (fromStr s)

fromStr s = fst . foldl f (s, 0) where
  f (s, i) group = (replace ("\\" ++ show i) group s, i + 1)

oneIsInfixOf ls s = any (\x -> isInfixOf x s) ls

regions begin end = groupRegion . reverse . snd. foldl f (False, []) where
  f (False, acc) x = if begin x then (True, (Begin, x) : acc) else (False, (Off, x) : acc)
  f (True, acc) x = if end x then (False, (End, x) : acc) else (True, (On, x) : acc)

data Region = On | Off | Begin | End
              deriving (Eq)

groupRegion = map liftFst . groupBy eqFst

liftFst x@((r,_) : _) = (r, map snd x)

eqFst a b = fst a == fst b

p x = traceShow x x

unique :: Eq a => [a] -> [a]
unique = map head . group

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
    
removeEmptyLines = filter (\l -> strip l /= "")

trim = removeEmptyLines . map strip

mergeRegion a b = mapRegion concat . groupRegion . map f where
  f (r, x) = (if r == a then b else r, x)

mapRegion f = map (\(r, x) -> (r, f x))

