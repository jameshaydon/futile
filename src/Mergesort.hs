-- | Where I try to program mergesort using only recursion schemes.
module Mergesort where

import Data.Functor.Foldable
import Data.Fix hiding (hylo)

-- * First we need to merge sorted lists.

data MergeSortedF a r
  = Done [a]
  | ChoseLeast a r
  deriving stock (Functor)

merge :: (Ord a) => ([a], [a]) -> [a]
merge = hylo rebuild choose
  where
    choose :: (Ord a) => ([a], [a]) -> MergeSortedF a ([a], [a])
    choose ([], r) = Done r
    choose (l, []) = Done l
    choose (x:xs, y:ys) =
      if x <= y
        then ChoseLeast x (xs, y:ys)
        else ChoseLeast y (x:xs, ys)

    rebuild :: MergeSortedF a [a] -> [a]
    rebuild = \case
      Done xs -> xs
      ChoseLeast x xs -> x:xs

-- * Then we implement mergesort.

data TreeF a r = Empty | Leaf a | Node r r
  deriving stock (Functor)

type Tree a = Fix (TreeF a)

split :: [a] -> TreeF a [a]
split [] = Empty
split [x] = Leaf x
split xs = Node l r
  where
    (l, r) = splitAt (length xs `div` 2) xs

combine :: (Ord a) => TreeF a [a] -> [a]
combine Empty = []
combine (Leaf x) = [x]
combine (Node l r) = merge (l, r)

mergeSort :: (Ord a) => [a] -> [a]
mergeSort = hylo combine split
