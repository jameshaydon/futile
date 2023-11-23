-- | Where I try to program mergesort using only recursion schemes.
module Mergesort where

import Generic.Data
import Generic.Data.Orphans ()
import Data.Functor.Foldable
import Data.Fix hiding (hylo)
import Data.Functor.Classes (Show1)

-- First we need to merge sorted lists.

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

-- We need to be able to split lists in two halves

data HalvesF a r = HalvesDone [a] [a] | Distribute a a r
  deriving stock (Functor)

halves :: [a] -> ([a],[a])
halves = hylo distr takeTwo
  where
    distr :: HalvesF a ([a], [a]) -> ([a], [a])
    distr (HalvesDone l r) = (l, r)
    distr (Distribute x y (l, r)) = (x:l, y:r)
    takeTwo :: [a] -> HalvesF a [a]
    takeTwo [] = HalvesDone [] []
    takeTwo [x] = HalvesDone [x] []
    takeTwo (x:y:xs) = Distribute x y xs

-- And finally we can implement mergesort

data TreeF a r = Empty | Leaf a | Node r r
  deriving stock (Functor, Generic, Generic1)
  deriving (Show1) via (Generically1 (TreeF a))

type Tree a = Fix (TreeF a)

mergeSort :: (Ord a) => [a] -> [a]
mergeSort = hylo combine split
  where
    combine :: (Ord a) => TreeF a [a] -> [a]
    combine Empty = []
    combine (Leaf x) = [x]
    combine (Node l r) = merge (l, r)

    split :: [a] -> TreeF a [a]
    split [] = Empty
    split [x] = Leaf x
    split xs = Node l r
      where
        (l, r) = halves xs
