{-# LANGUAGE LambdaCase #-}
import System.IO 
import System.Environment
import System.Exit
import System.Console.GetOpt
import Data.List
import Data.Text (pack, unpack, strip)
import Text.Regex
import Debug.Trace

process = unlines . concatMap processBlock . coqBlocks . map strip' . lines

p x = traceShow x x

strip' = unpack . strip . pack

coqBlocks = region beginBlock endBlock

beginBlock = isInfixOf "\\begin{flushleft}"

endBlock = isInfixOf "\\end{flushleft}"

processBlock = \case
  (On, b) -> concatMap processGoal . goals $ b
  (_, b) -> b

goals = region beginGoal endGoal

beginGoal = isInfixOf "=========="

endGoal = isInfixOf "\\medskip"

processGoal (On, b) = b
processGoal _ = []

region begin end = groupRegion . reverse . foldl f (False, []) where
  f (False, acc) x = if begin x then (True, (Begin, x) : acc) else (False, (Off, x) : acc)
  f (True, acc) x = if end x then (False, (End x) : acc) else (True, (On, x) : acc)

data Region = On | Off | Begin | End

groupRegion = map liftRegion . groupBy eqFst

liftRegion x@((r,_) : _) = (r, map snd x)

eqFst a b = fst a == fst b


main = do
  (options, fs) <- getArgs >>= parseOpt
  fin <- if length fs >= 1 then openFile (fs !! 0) ReadMode else return stdin
  fout <- if length fs >= 2 then openFile (fs !! 1) WriteMode else return stdout
  str <- hGetContents fin
  hPutStr fout (process str)
  hClose fin
  hClose fout

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

