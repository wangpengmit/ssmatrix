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
  (On, b) -> concat . map processLemma . lemmas $ b
  (_, b) -> b

lemmas = regions beginLemma endLemma

beginLemma = oneIsInfixOf ["~Lemma~", "~Theorem~"]

oneIsInfixOf ls s = any (\x -> isInfixOf x s) ls

endLemma = isInfixOf "~Qed."

processLemma = \case
  (On, b) -> unique . concat . map processGoal . goals $ b
  (Begin, s : _) -> [printf "%s:" . getLemmaName $ s]
  _ -> []

getLemmaName s = case s =~ "~(?:Lemma|Theorem)~([^~:]+)~" :: (String, String, String, [String]) of
  (_, _, _, name : _) -> name


-- instance (RegexLike a b) => RegexContext a b [b] where 
--   match r s = maybe [] id (matchM r s)
--   matchM = actOn (\(_,ma,_) -> map fst $ elems ma)
           
goals = regions beginGoal endGoal

beginGoal = isInfixOf "=========="

endGoal = isInfixOf "\\medskip"

processGoal = \case
  (On, b) -> map (unchar . untilde . uncommand "texttt" . uneol) b
  _ -> []

unchar = subF "{\\\\char'([^}]+)}" $ \(_ : s : _) -> singleton . chr . oct $ s

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

uncommand name = sub ("^\\\\" ++ name ++ "{(.*)}$") "\\1"

untilde = sub "~" " "

uneol = sub "\\\\\\\\$" ""

get2_4 t = let (_, x, _, _) = t in x

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

