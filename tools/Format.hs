module Format where

import Data.String.Utils (replace)

format a b = doFormat a (0::Int,b)
    where
    doFormat a (_,[]) = a
    doFormat a (n,(b:bs)) = replace (old n) b a `doFormat` (n+1,bs)
    old n = "{" ++ show n ++ "}"

