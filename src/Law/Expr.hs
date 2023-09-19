{-# LANGUAGE MonoLocalBinds #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Law.Expr where

import Control.Lens
import Data.Fix
import Data.Functor.Classes (Eq1 (..), Ord1 (..), Show1 (..))
import Data.Map.Strict qualified as Map
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

-- catrewrites :: [Rewrite () ArF]
-- catrewrites =
--   [ -- identity
--     pat (Comp "f" (pat Id)) := "f",
--     pat (Comp (pat Id) "f") := "f",
--     -- associcativity
--     pat (Comp (pat (Comp "f" "g")) "h") := pat (Comp "f" (pat (Comp "g" "h"))),
--     pat (Comp "f" (pat (Comp "g" "h"))) := pat (Comp (pat (Comp "f" "g")) "h"),
--     -- Commutativity of cone compo
--     pat (ConeComp "x" "y") := pat (ConeComp "y" "x"),
--     -- Associativity of cone comp
--     pat (ConeComp (pat (ConeComp "f" "g")) "h") := pat (ConeComp "f" (pat (ConeComp "g" "h"))),
--     pat (ConeComp "f" (pat (ConeComp "g" "h"))) := pat (ConeComp (pat (ConeComp "f" "g")) "h"),
--     --
--     pat
--       ( Comp
--           (pat (ConePart Pos "lbl" "f"))
--           (pat (Proj Pos "lbl"))
--       )
--       := "f",
--     pat
--       ( Comp
--           (pat (ConeComp "extra" (pat (ConePart Pos "lbl" "f"))))
--           (pat (Proj Pos "lbl"))
--       )
--       := "f"
--   ]
--     ++ emptyConeComponent
--   where
--     emptyConeComponent =
--       [ r
--         | sig <- [Pos, Neg],
--           let x = pat (ConePart sig "name" "f"),
--           let e = pat (EmptyCone sig),
--           r <-
--             [ pat (ConeComp e x) := x,
--               pat (ConeComp x e) := x
--             ]
--       ]

--

catrw :: Ar -> [Ar]
catrw = \case
  -- Assoc
  Fix (Comp fs) ->
    [ Fix (Comp (flattenComps fs)),
      Fix (Comp (coneComp fs)),
      Fix (Comp (coneProj fs))
    ]
  -- Names
  Fix (Named "plus") -> [plus]
  _ -> []
  where
    flattenComps :: [Ar] -> [Ar]
    flattenComps [] = []
    flattenComps (Fix (Comp gs) : rest) = gs ++ flattenComps rest
    flattenComps (f : rest) = f : flattenComps rest

    coneComp :: [Ar] -> [Ar]
    coneComp [] = []
    coneComp [c] = [c]
    coneComp (f : Fix (Cone Pos cs) : rest) =
      coneComp (Fix (Cone Pos ((\g -> Fix (Comp [f, g])) <$> cs)) : rest)
    coneComp (f : rest) = f : coneComp rest

    coneProj :: [Ar] -> [Ar]
    coneProj [] = []
    coneProj [c] = [c]
    coneProj (a@(Fix (Cone Pos cs)) : b@(Fix (Proj Pos lbl)) : rest) = case Map.lookup lbl cs of
      Nothing -> a : b : coneProj rest
      Just c -> c : coneProj rest
    coneProj (r:rest) = r : coneProj rest

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

foo :: EqRes
foo = eq 5 catrw ff gg -- exampleComp exampleComp'

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
        ( "succ",
          ( cone
              [ ("a", proj "a"),
                ("b", proj "b")
              ]
              .+ named "plus"
              .+ coproj "succ"
          )
        )
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
