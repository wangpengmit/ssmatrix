module Util where

import Data.Monoid
import Data.List
import Data.Function (on)

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

