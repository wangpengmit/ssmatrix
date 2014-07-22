{-# LANGUAGE LambdaCase #-}
import System.IO 
import System.Environment
import System.Exit
import Control.Monad.Error
import Control.Monad.State
import Data.List
import Text.Parsec
import Text.Printf
import System.Console.GetOpt

import SExprParser

data Trace = Trace {
      name :: String,
      from :: Expr,
      to :: Expr,
      trans :: [Trans]
    } deriving (Eq, Show)

data Expr =
  Var String
  | ConstInt Integer
  | Binop Binop Expr Expr
    deriving (Eq, Show)

data Binop = Plus | Minus | Mult | Div | Exp
             deriving (Eq, Show)

data Trans = Rewrite String Expr
         | Fold Expr Expr
         | Lift Expr
         | Beta
           deriving (Eq, Show)

data ExprError =
  ExprError String
  | EmptyListError
  | CompositeError String ExprError
  | MismatchError String String
    deriving (Eq, Show)

instance Error ExprError where
  strMsg s = ExprError s
  
type MayThrow = Either ExprError

getTrace node = do
  name <- child node "name" >>= getName <??> "name"
  from <- child node "from" >>= getFrom <??> "from"
  to <- child node "to" >>= getTo <??> "to"
  trans <- child node "trans" >>= getTransPath <??> "trans"
  return (Trace name from to trans)

getName node =
  enterWith node "name" $ first >>= lift. getSymbol <??> "name string"
  
getFrom node =
  enterWith node "from" $ first >>= lift . getExpr <??> "original expression"

getTo node =
  enterWith node "to" $ first >>= lift . getExpr <??> "final expression"

getTransPath node =
  enterWith node "trans" $ every $ lift . getTrans

getTrans node = enter node $ do
  first >>= lift . getSymbol >>= \case
    "rewrite" -> do
      rule <- first >>= lift . getSymbol <??> "rewrite rule"
      subterm <- first >>= lift . getExpr <??> "rewrite subterm"
      return (Rewrite rule subterm)
    "fold" -> do
      from <- first >>= lift . getExpr <??> "fold from"
      to <- first >>= lift . getExpr <??> "fold to"
      return (Fold from to)
    "lift" -> do
      subterm <- first >>= lift . getExpr
      return (Lift subterm)
    "beta" -> return Beta
                 
getExpr = \case
  Int i -> return (ConstInt i)
  Symbol x -> return (Var x)
  node@(List _) -> enter node $ do
    op <- first >>= lift . getBinop
    a <- first >>= lift . getExpr
    b <- first >>= lift . getExpr
    return (Binop op a b)

getBinop node = 
  getSymbol node >>= \case 
    "+" -> return Plus
    "-" -> return Minus
    "*" -> return Mult
    "/" -> return Div
    "^" -> return Exp
    op -> throwError (strMsg $ "unknown binary operator" ++ op)

getSymbol = \case
  Symbol x -> return x
  node -> throwError $ MismatchError "symbol" (show node)

child node child_name = case node of
  List (_ : children) -> case find p children of
    Just n -> return n
    _ -> throw
    where p = \case
               Symbol sym | sym == child_name -> True
               List (Symbol sym : _) | sym == child_name -> True
               _ -> False
  _ -> throw
  where throw = throwError $ strMsg $ "can't find child " ++ child_name ++ " in " ++ show node
  
enter node m = 
    liftM fst (runStateT m ls)
    where ls = case node of
               List l -> l
               x -> [x]
    
enterWith node sym m = enter node (first >>= exact (Symbol sym) >> m)

m <??> str = catchError m $ \e -> throwError $ CompositeError ("error in parsing " ++ str) e
  
infixl 1 <??>

exact a b = if a == b then return () else throwError $ MismatchError (show a) (show b)

first = 
  get >>= \case
    x : xs -> put xs >> return x
    _ -> throwError EmptyListError

every f = do
  ls <- get
  put []
  sequence (map f ls)

removeLast ls = take (length ls - 1) ls

ltacAll traces = unlines $ prelude : map ltacTrace traces

prelude = unlines [
           "Set Implicit Arguments.",
           "Unset Strict Implicit.",
           "Unset Printing Implicit Defensive.",
           "",
           "Require Import prelude.",
           "Import prelude.Exports."]

ltacTrace trace = printf "Section %s.\n\nVariables %s : int.\n\nLemma %s : %s = %s.\nProof.\n%sQed.\n\nEnd %s.\n" (name trace) (unwords $ freeVars (from trace) `union` freeVars (to trace)) (name trace) (ltacExpr $ from trace) (ltacExpr $ to trace) (ltacTransPath $ trans trace) (name trace)

ltacTransPath path = unlines . map ("  " ++) $ (map ltacTrans path) ++ ["by []."]

ltacTrans = \case
  Rewrite rule subterm -> 
      let (d, n) = if isPrefixOf "-" rule then ("-", tail rule) else ("", rule) in
      printf "rewrite %s[%s]%s." d (ltacExpr subterm) n
  Fold from to -> printf "rewrite -[%s]/%s." (ltacExpr from) (ltacExpr to)
  Lift subterm -> printf "pattern_set %s." (ltacExpr subterm)
  Beta -> printf "red."

ltacExpr = \case
  Var x -> x
  ConstInt n -> "$" ++ show n
  Binop op a b -> printf "(%s %s %s)" (ltacExpr a) (ltacBinop op) (ltacExpr b)

ltacBinop = \case
  Plus -> "+"
  Minus -> "-"
  Mult -> "*"
  Div -> "/"
  Exp -> "^"

freeVars = \case
  Var x -> [x]
  ConstInt _ -> []
  Binop _ a b -> union (freeVars a) (freeVars b)

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

usage = usageInfo "Usage: WitnessToLtac [-h] [input file] [output file]" flags

main = do
  (options, fs) <- getArgs >>= parseOpt
  fin <- if length fs >= 1 then openFile (fs !! 0) ReadMode else return stdin
  fout <- if length fs >= 2 then openFile (fs !! 1) WriteMode else return stdout
  str <- hGetContents fin
  -- hPrint stderr str
  -- hPutStrLn stderr ""
  case parse tProg "" str of
    Right sexprs -> do
      -- hPrint stderr sexprs
      -- hPutStrLn stderr ""
      case sequence (map getTrace sexprs) of
        Right traces -> do
          -- hPrint stderr traces
          -- hPutStrLn stderr ""
          hPutStrLn fout $ ltacAll traces
        Left err -> print err
    Left err -> print err
  hClose fin
  hClose fout
