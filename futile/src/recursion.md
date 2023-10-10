# Recursion

In this note I explore doing recursion only via the `F`-algebra approach.

## Naturals

The initial F-algebra approach to to defining the natural numbers:
```
F(X) := 1 + X
```
where `1` is the _unit_ object. How can we define this in Futile?
```futile
// This is a definition (of a functor) inside the category of categories
// The source/target is unspecified, or "polymorphic"
F :=
  colim{ zero = lim{}, succ = . }
```
And we can then obtain the natural numbers as:
```futile
Nat := Fix(F)
```
using some special operation `Fix` which takes fixed points of functors.
Which means that `Nat` is an object such that `wrap : F(Nat) -> Nat` and `unwrap : Nat -> F(Nat)` are inverse to one another.
```
wrap   : colim{ zero = lim{}, succ = Nat } -> Nat
unwrap : Nat -> colim{ zero = lim{}, succ = Nat }
```
After this we can then define arrows operating on `Nat`:
```
zero : lim{} -> Nat
zero := zero. wrap

inc : Nat -> Nat
inc = succ. wrap

plus : (Nat, Nat) -> Nat
plus =
  (.1 unwrap, .2)
  @1
  cocone{
    zero = .2,
    succ = plus inc
  }
```

_Question:_ How does the recursion on `plus` work here?

_Question:_ The wrapping/unwrapping is annoying, can it be avoided?

_Remark:_ There is something a bit unnatural about `Fix` returning an object of
the category, rather than a functor (which would have codomain the unit
category).

The recursion can be replaced by using the catamorphism of the initial algebra.
The catamorphism we want in this case is one on `Nat` itself:
```futile
alg : F(Nat) -> Nat
alg :=
  cocone{
    zero = PLUS_SECOND_ARG,
    succ = succ.
  }
```
At this point there are two options. You can either take the _T. Hagino_ definition, which involves defining `Nat -> (Nat => Nat)` instead, and then transforming back, but it looks super ugly. Or you can _M. Hesegawa_'s κ-calculus and do:
```
plus := \κ x -> cata(cocon{zero = x, succ.})
```

But I would rather avoid binding forms if possible.

**Notation:** From now one we allow writing `f + g` instead of `(f, g) plus`.

## Mutual recursion

What about mutual recursion?

When performing mutual recursion in values, one can avoid it by only defining
one thing that is a product thing. For example for defining `even : Nat -> Nat`
and `odd : Nat -> Nat` one can instead define `evenOdd : Nat -> (Nat, Nat)`, and
then `even := evenOdd .1` and `odd := evenOdd .2`.

Can we do the same sort of trick for defining mutually recursive types? We can't
define one type for which we can get other types "by projection". We can however
define an object in a product category.

We consider for example defining trees and forests at the same time, in Haskell:
```haskell
-- A tree of Int:
data Tree
  = TreeEmpty
  | Node Int Forest
  
-- A forest of Int:
data Forest
  = ForestEmpty
  | Forest Tree Forest
```

Well, now we want to define two types at once, so we instead look at
endofunctors of `lim{ tree = C, forest = C}`, for some (polymorphic) category
`C`. This is a limit in the category of categories. We can define an endomorphism of this:

```futile
TreeForestF :=
  cone{
    tree =
      colim{
        empty = lim{},
        node = lim{
                 value    = Int,
                 children = .forest 
               }
      },
    forest =
      colim{
        empty = lim{},
        cons  = lim{
                  child = .tree,
                  tail = .forest 
                } 
             
      }
  }
```

Again we can `Fix`:
```
TreeForest := Fix(TreeForestF)
```

So now `TreeForest` is an object of `lim{ tree = C, forest = C}` such that:
```
wrap/unwrap : TreeForestF(TreeForest) <-> TreeForest
```

We can define
```
Tree   := .tree(TreeForest)
Forest := .forest(TreeForest)
```

As long as we assume we can "apply" all these things. Better might be for `Fix` to return a functor:

```
Fix(TreeForestF) : {} -> lim{ tree = C, forest = C}
```

So that `Fix(TreeForestF) .tree` and `Fix(TreeForestF) .forest` are now
definable using arrow composition syntax. But now if you want to _use_ these definitions _inside_ `C`, you need to apply it to `{}`:

```
Tree   := (Fix(TreeForestF) .tree  )({})
Forest := (Fix(TreeForestF) .forest)({})
```

Maybe there would be some way to automatically convert between things of type
`{} -> A` and things of type `A`.

## Functors

How does this mix with functors?

Let's take `List` as an example, this type is a functor for the elements, but is also recursive. We define `ListF` as a functor
```
ListF : lim{ elem = C, rec = C } -> C
ListF :=
  colim{
    empty = lim{},
    cons  = lim{
              head = .elem,
              tail = .rec
    }
  }
```

Now we want to call `Fix`, but, we only want to `Fix` on one dimension of the
limit category, so we need something more general. This is a bit like a trace operator. This would be something like:

```
F : lim{ loop = C, in = A } -> lim{ loop = C, out = B }
Trace(F) : A -> B
```

If we take the special case:
```
F : lim{ loop = C, in = lim{} } -> lim{ loop = C, out = C }
```
then
```
Trace(F) : lim{} -> C
```

More generally if we take:
```
F : lim{ loop = C, in = A } -> lim{ loop = C, out = C }
```

then
```
Trace(F) : A -> C
```

Let's define `Fix` to be the same as `Trace` but always operating on `loop` and `out` being the same, so that you don't need to specify both of them, in other words:
```
Fix(F) = Trace(F cone{ loop = ., out = .})
```

So now, back to lists. We define lists as:
```
ListF : lim{ loop = C, in = C } -> C
ListF :=
  colim{
    empty = lim{},
    cons  = lim{
              head = .in,
              tail = .loop
    }
  }

List : C -> C
List := Fix(ListF)
```

How do we _use_ this definition? For example, how do we sum a list of `Nat`?

```
sum : Nat List -> Nat
sum := ...?
```

Recall that we have decided to make `Nat` a functor `{} -> C`, therefore we can "apply" the functor `List : C -> C` to `Nat : {} -> C` simply by composition: `Nat List : {} -> C`. So now when we write `Nat List -> Nat`, we are referring to a natural transformation between functors `{} -> C`.

It's interesting that this makes type-application look like ML/OCaml.

Let's first try a naive definition.

```
sum : Nat List -> Nat
sum :=
  unwrap
  cocone{
    empty = zero,
    cons  = .head + .tail sum
  }
```

(Again, the question remains of the formal semantics of these sorts of equations that refer to themselves.)

But in this case we can use the catamorphism directly. In this case we want to
use an algebra on `Nat` for the case when the element type (the `.in` component
in this case) is also `Nat`:
```
// recall:
ListF : lim{ loop = C, in = C } -> C

// so:
cone{ loop = . , in = cone{} Nat } ListF : C -> C

NatListF := cone{ loop = . , in = cone{} Nat } ListF
```

So we want an algebra of this with carrier `Nat : {} -> C`, that is, a natural transformation
```
Nat NatListF -> Nat
```

To see how the typing works here, we can simplify this composition of functors:
```
  Nat NatListF
=
  Nat cone{ loop = . , in = Nat } ListF
=
  cone{ loop = Nat , in = Nat } ListF
=
  cone{ loop = Nat , in = Nat }
  colim{
      empty = lim{},
      cons  = lim{
                head = .in,
                tail = .loop
      }
    }
=
  colim{
      empty = lim{},
      cons  = lim{
                head = Nat,
                tail = Nat
      }
    }
```

So:

```
sum_alg : Nat NatListF -> Nat
sum_alg :=
  cocone{
    empty = zero,
    cons  = .head + .tail
  }

sum : Nat List -> Nat
sum := cata(sum_alg)
```
