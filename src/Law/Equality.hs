-- | Uber naive equality saturation.
module Law.Equality where

import Control.Lens
import Data.Set qualified as Set

class Normalize t where
  norm :: t -> t

onOne :: (Plated t, Normalize t) => (t -> [t]) -> t -> [t]
onOne rw x = x : [norm (replace sub') | Context replace sub <- contexts x, sub' <- rw sub]

satOnce :: (Plated t, Ord t, Normalize t) => (t -> [t]) -> Set t -> Set t
satOnce rw es = Set.fromList (Set.toList es >>= onOne rw)

satOnce' :: (Plated t, Ord t, Normalize t) => (t -> [t]) -> (Bool, Set t) -> (Bool, Set t)
satOnce' _ (True, es) = (True, es)
satOnce' rw (False, es) = let es' = satOnce rw es in (Set.size es == Set.size es', es')

satMany :: (Plated t, Ord t, Normalize t) => Int -> (t -> [t]) -> Set t -> Set t
satMany n _ es | n <= 0 = es
satMany n rw es =
  let next = satOnce rw es
   in if Set.size es == Set.size next
        then es
        else satMany (n - 1) rw (satOnce rw es)

data EqRes = Equal | NonEqual | Unknown
  deriving stock (Eq, Show)

eq :: (Plated t, Ord t, Normalize t) => Int -> (t -> [t]) -> t -> t -> EqRes
eq _ _ x y | x == y = Equal
eq n rw x y = go n (False, Set.singleton x) (False, Set.singleton y)
  where
    go i a@(satX, xs) b@(satY, ys) =
      case decide of
        Unknown | i >= 1 -> go (i - 1) (satOnce' rw a) (satOnce' rw b)
        _ -> decide
      where
        disj = Set.disjoint xs ys
        sat = satX && satY
        decide =
          if
            | disj && sat -> NonEqual
            | disj -> Unknown
            | otherwise -> Equal
