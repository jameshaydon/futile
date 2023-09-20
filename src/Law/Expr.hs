{-# LANGUAGE MonoLocalBinds #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Law.Expr where

import Control.Lens
import Data.Fix
import Data.Functor.Classes (Eq1 (..), Ord1 (..), Show1 (..))
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Generic.Data (Generic1, Generically1 (..))
import Generic.Data.Orphans ()
import Law.Core
import Law.Equality

type Mapping a b = [(a, b)]

data Niche a = a :-> a

data ArF ar
  = Named Name
  | Comp [ar]
  | Proj Sign Lbl
  | Cone Sign (Map Lbl ar)
  | Distr Lbl
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable, Generic, Generic1)
  deriving (Eq1, Ord1, Show1) via (Generically1 ArF)

type Ar = Fix ArF

instance (Traversable f) => Plated (Fix f) where
  plate f (Fix fx) = Fix <$> traverse f fx

cost :: ArF Int -> Int
cost = \case
  Named {} -> 1
  Comp fs -> sum fs
  Proj {} -> 1
  Cone _ cs -> 1 + sum (toList cs)
  Distr {} -> 1

normalizeOnce :: Ar -> Ar
normalizeOnce (Fix (Comp fs)) = case flatten fs of
  [f] -> f
  fs' -> Fix (Comp fs')
  where
    flatten [] = []
    flatten (Fix (Comp gs) : rest) = flatten (gs ++ rest)
    flatten (f : rest) = f : flatten rest
normalizeOnce f = f

normalize :: Int -> Ar -> Ar
normalize n x
  | n <= 0 = x
  | otherwise =
      let x' = transform normalizeOnce x
       in if x == x'
            then x
            else normalize (n - 1) x'

instance Normalize Ar where
  norm = normalize 100

catrw :: Ar -> [Ar]
catrw e =
  norm
    <$> compPairRW coneComp e
      ++ compPairRW coneProj e
      ++ compTripRW distrCase e
      ++ ( case e of
             Fix (Named "plus") -> [plus]
             _ -> []
         )
  where
    compPairRW :: (Ar -> Ar -> [Ar]) -> Ar -> [Ar]
    compPairRW f (Fix (Comp fs)) =
      Fix . Comp
        <$> [ before ++ [fab] ++ after
              | (before, (a, b), after) <- doubles fs,
                fab <- f a b
            ]
    compPairRW _ _ = []

    compTripRW :: (Ar -> Ar -> Ar -> [Ar]) -> Ar -> [Ar]
    compTripRW f (Fix (Comp fs)) =
      Fix . Comp
        <$> [ before ++ [fab] ++ after
              | (before, (a, b, c), after) <- triples fs,
                fab <- f a b c
            ]
    compTripRW _ _ = []

    coneComp :: Ar -> Ar -> [Ar]
    coneComp f (Fix (Cone Pos cs)) = [Fix (Cone Pos ((\g -> Fix (Comp [f, g])) <$> cs))]
    coneComp _ _ = []

    coneProj :: Ar -> Ar -> [Ar]
    coneProj (Fix (Cone Pos cs)) (Fix (Proj Pos lbl)) = maybe [] pure (Map.lookup lbl cs)
    coneProj _ _ = []

    distrCase :: Ar -> Ar -> Ar -> [Ar]
    distrCase (Fix (Cone Pos cs)) (Fix (Distr lbl)) (Fix (Cone Neg cases)) = case Map.lookup lbl cs of
      Nothing -> []
      Just c -> case c of
        Fix (Proj Neg con) -> case Map.lookup con cases of
          Nothing -> []
          Just theCase ->
            [ Fix
                ( Comp
                    [ Fix (Cone Pos (Map.insert lbl (Fix (Comp [])) cs)),
                      theCase
                    ]
                )
            ]
        Fix (Comp fs) -> case splitLast fs of -- TODO: use more efficient function
          Just (before, Fix (Proj Neg con)) -> case Map.lookup con cases of
            Nothing -> []
            Just theCase ->
              [ Fix
                  ( Comp
                      [ Fix (Cone Pos (Map.insert lbl (Fix (Comp before)) cs)),
                        theCase
                      ]
                  )
              ]
          _ -> []
        _ -> []
    distrCase _ _ _ = []

doubles :: [a] -> [([a], (a, a), [a])]
doubles (x : y : rest) = ([], (x, y), rest) : [(x : a, b, c) | (a, b, c) <- doubles (y : rest)]
doubles _ = []

triples :: [a] -> [([a], (a, a, a), [a])]
triples (x : y : z : rest) = ([], (x, y, z), rest) : [(x : a, b, c) | (a, b, c) <- triples (y : z : rest)]
triples _ = []

splitLast :: [a] -> Maybe ([a], a)
splitLast [] = Nothing
splitLast [x] = Just ([], x)
splitLast (x : rest) = do
  (prefix, y) <- splitLast rest
  pure (x : prefix, y)

example :: Ar
example =
  comp
    (cone [("x", cid), ("y", exampleComp)])
    (proj "x")

exampleComp :: Ar
exampleComp =
  comp
    (comp (named "f") (named "g"))
    (named "h")

exampleComp' :: Ar
exampleComp' =
  comp
    (comp (named "f") (comp (named "g") cid))
    (named "h")

plusAssoc :: EqRes
plusAssoc = eq 12 catrw ff gg

zero :: Ar
zero = cone [] .+ coproj "zero"

zeroPlusZero :: Ar
zeroPlusZero =
  zero
    .+ cone
      [ ("a", cid),
        ("b", zero)
      ]
    .+ named "plus"

checkEq :: Ar -> Ar -> EqRes
checkEq a b = eq 14 catrw (norm a) (norm b)

zeroRightNeutralBase :: EqRes
zeroRightNeutralBase =
  checkEq zeroPlusZero zero

expand :: Int -> Ar -> [Ar]
expand n = Set.toList . satMany n catrw . Set.singleton . norm

cid :: Ar
cid = Fix (Comp [])

comp :: Ar -> Ar -> Ar
comp f g = Fix (Comp [f, g])

cone :: [(Lbl, Ar)] -> Ar
cone cs = Fix (Cone Pos (Map.fromList cs))

cocone :: [(Lbl, Ar)] -> Ar
cocone cs = Fix (Cone Neg (Map.fromList cs))

infixr 9 .+

(.+) :: Ar -> Ar -> Ar
(.+) = comp

named :: Name -> Ar
named n = Fix (Named n)

proj :: Lbl -> Ar
proj n = Fix (Proj Pos n)

coproj :: Lbl -> Ar
coproj n = Fix (Proj Neg n)

distr :: Lbl -> Ar
distr n = Fix (Distr n)

plus :: Ar
plus =
  distr "a"
    .+ cocone
      [ ("zero", proj "b"),
        ("succ", named "plus" .+ coproj "succ")
      ]

f1 :: Ar
f1 =
  cone
    [ ("xy", cone [("a", proj "x"), ("b", proj "y")] .+ named "plus"),
      ("z", proj "z")
    ]

f2 :: Ar
f2 =
  cone
    [ ("a", proj "xy"),
      ("b", proj "z")
    ]
    .+ named "plus"

ff :: Ar
ff = f1 .+ f2

g1 :: Ar
g1 =
  cone
    [ ("x", proj "x"),
      ( "yz",
        cone [("a", proj "y"), ("b", proj "z")]
          .+ named "plus"
      )
    ]

g2 :: Ar
g2 =
  cone
    [ ("a", proj "x"),
      ("b", proj "yz")
    ]
    .+ named "plus"

gg :: Ar
gg = g1 .+ g2
