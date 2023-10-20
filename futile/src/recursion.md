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

## Lists

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
  Nat cone{ loop = . , in = cone{} Nat } ListF
=
  cone{ loop = Nat , in = Nat cone{} Nat } ListF
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

## Recursive functions

Not all recursive functions are "structural", that is, expressed as a
catamorphism. So we also want to define general recursive functions.

Let's look at very simple example, a recursively defined morphism `f : Nat ->
Nat` that always returns zero:

```futile
dec : Nat -> Nat
dec = unwrap cocone{ zero = cone{} zero. wrap, succ = }

f : Nat -> Nat
f = dec f
```

First let's try to prove that this is equal to `cone{} zero`:

```
  zero f 
= zero dec f
= zero unwrap cocone{ zero = cone{} zero. wrap, succ = }
= zero. wrap unwrap cocone{ zero = cone{} zero. wrap, succ = }
= zero. cocone{ zero = cone{} zero. wrap, succ = }
= cone{} zero. wrap
```

and

```
  zero cone{} zero
= cone{} zero
= cone{} zero. wrap
```

hence `zero f = zero cone{} zero`

And:

```
  inc f 
= succ. wrap f
= succ. wrap dec f
= succ. wrap unwrap cocone{ zero = cone{} zero. wrap, succ = } f
= succ. cocone{ zero = cone{} zero. wrap, succ = } f
= f
= cone{} zero
```

(_TODO:_ The last equality in this chain uses the property we are trying to
prove. Make explicit why this is OK.)

and

```
  inc cone{} zero
= cone{} zero
```

hence `inc f = inc cone{} zero`.

Then (using that `zero` and `inc` "cover" `Nat`), we conclude that `f = cone{}
zero`.

_TODO:_ improve this proof, going from the explicit coproduct instead.

This proves that, if there is a morphism `f` that has the property `f = dec f`,
then it is equal to `cone{} zero`.

_How to interpret this morphism into a category?_

Up till now we have been assuming the following interpretation model:
- Interpret some base morphisms.
- Know how to interpret combinators of morphisms if you know the interpretation of the morphisms. E.g., `I(f g) = I(f) I(g)`, and same for cones, cocones, etc.

In other words, an interpretation was simply a functor, from the free category of the syntax, to the target category. A functor that preserves (co)limits, etc.

How can we _functor_ `f`?

```
I(f) = I(dec f) = I(dec) I(f)
```

We know how to interpret `dec`, so the question is, can we solve the equation:
```
x = I(dec) x
```
in the target category?

If we unroll the definition, we see that we are trying to define `f` as:
```
dec dec dec dec dec dec ...
```
but most categories don't permit infinite compositions. Another way of looking at it is that we are defining an infinite sequence:
```
undefined
dec undefined
dec dec undefined
dec dec dec undefined
dec dec dec dec undefined
dec dec dec dec dec undefined
dec dec dec dec dec dec undefined
dec dec dec dec dec dec dec undefined
dec dec dec dec dec dec dec dec undefined
...
```

which, for all (finite) inputs of type `Nat`, one of these will return a defined
value. So, if you have an order on the morphisms, you can ask for the limit of
this sequence.

Note that we could have defined `f` as:
```
f : Nat -> Nat
f = f dec
```

Is this the same?

If we take the "infinite expansion" point of view, it is the same, it is an infinite composition of `dec` with itself. But, the expansion is to the left:
```
... dec dec dec dec dec
```

Computationally this is very different: given an argument, we don't have a finite known prefix with which to start processing it.

_Is it always a (limit of a) sequence of morphisms?_

In _single recursion_ this is obviously the case. But even in multiple recursion, you can always expand _all_ instances of the recursive morphism, to get a sequence of increasingly precise morphisms.

---

_Something something "knot tying":_ The way recursion works in functional
programming languages like OCaml is that it first creates a pointer for the
function that is defined to be `null`. Then it creates the closure object, with
references to this null pointer, and finally it sets the pointer to that closure
object. This sort of manipulation doesn't really look like what the "take a
limit" procedure.


_Something something "lazy":_ What enables the solution to exist is a certain
laziness. Even in strict languages like OCaml, it's the fact that closures are
values that just sit there and don't _do_ anything until they are invoked. So,
they can be defined (as a null pointer) before they exhibit any bad behaviour,
and can resolve any required "infinite" behaviour dynamically, at runtime.

---

## The functor approach?

One way to do it, possibly, is to define some sort of functor.

We consider a category generated by some minimal set of objects we need to make things typecheck. And then we consider an endofunctor of this category which encodes the equation above. The idea is to then define `f` as some sort of fixed point interpretation of this category into your target category.

If we want to define a recursive `f` in `C`, we want some `D` such that `D -> C` to correspond to "possible definitions of `f` in `C`". Then, we want a process which, given `D -> C` produces a "better" `D -> C`.

```
(D => C) -> (D => C)
--------------------
(D => C) × D -> C
```

We could hope it be specified by some `F : D -> D`, so that if `D -> C` is some approximation, then `D -> D -> C` is the refinement.

In the example of `f` above, we are looking for some category `D` which has an abstract morphism `f` and an abstract morphism `dec`, and then we define a functor `F` that sends:

```
f ~> dec f
```

Then if we consider an approximation `A0 : D -> C` that sends `dec ~> dec` and `f ~> undefined`, then `F A0` sends:
```
dec ~> dec   ~> dec
f   ~> dec f ~> dec undefined
```

and `F F A0` sends:
```
    F        F            A0
dec ~> dec   ~> dec       ~> dec
f   ~> dec f ~> dec dec f ~> dec dec undefined
```

so precomposing with `F` gets us a chain of increasingly accurate moprhisms. 

From now on lets call `f` "countdown" instead.

In this case the category `D` is quite simple:
```futile
def category Countdown := {
  gen             *
  gen dec       : * -> *
  gen countdown : * -> *
}
```

We can define the following functor `Countdown -> Countdown`:
```
{ dec = dec, countdown = dec countdown }
```
Then, given some category `C` where we have defined `Nat` and `dec : Nat -> Nat`, we can define a functor `Countdown -> C`:
```
{ * = Nat, dec = dec, countdown = undefined }
```
Note, as in [macros](macros.md), that with inference this would hopefully be reduced to:
```
{ dec = dec, countdown = undefined }
```
We are then searching for the recursive fixed point for this, say:
```futile
rec
  { dec = dec, countdown = dec countdown }
  { dec = dec, countdown = undefined }
: Countdown -> C
```
for which we want to extract `countdown`, so:
```
interpret
  countdown
over rec
  { dec = dec, countdown = dec countdown }
  { dec = dec, countdown = undefined }
```

If we want to prove some property `P` about `countdown` then we have to do the following:
- Prove `P` for `{ dec = dec, countdown = undefined }`
- Prove that if `P` holds for `F` then it holds for `{ dec = dec, countdown = dec countdown } F`.

## Equality as moprhisms

Equality proofs are 2 morphisms. They can use colimit and limit constructions. Thus, you can prove equality from a coproduct by proving equality kn each summand. You can prove equality by proving equality for each projection, for morphosms to a product. Proofs have to terminate or they are meaningless, so they cannot be defined by recursion. Thus, for proofs about equality from recursive types, better to use the cata.

---

Wait, is it even `f = dec f` that we want? This is actually just a diverging function. What we want is:
```futile
f : Nat -> Nat
f =
  unwrap
  cocone{
    zero = zero. wrap,
    succ = f
  }
```

In this case for the functor approach we need a category which has:
- limits and cones
- colimits and cocones
- wrap/unwrap for the recursive `Nat` type.

Let's try to prove that if we take the fixed point, then
```
f == cone{} zero. wrap
```
We prove this by defining the equality as a 2-morphism:
```
f -> cone{} zero. wrap : Nat -> Nat
```
First we will precompose with `wrap`:
```
wrap f -> wrap cone{} zero. wrap : colim{ zero = lim{}, Nat } -> Nat
```
Because `wrap` is an iso, this will give us the required equality.
Because the source here is a colimit, we can define such a 2-morphism via lifting a cocone:
```
lift_cocone{ zero = ?zero_case , succ = ?succ_case }
```
where:
```
zero_case : zero. wrap f -> zero. wrap cone{} zero. wrap : lim{} -> Nat
succ_case : succ. wrap f -> succ. wrap cone{} zero. wrap : Nat   -> Nat
```

- Let's start with `zero_case`:
  ```
  zero. wrap f -> zero. wrap
  ```
  since we can simplify `zero. wrap cone{} zero. wrap` to `zero. wrap`.
  We expand `f`:
  ```
  zero. wrap unwrap
  cocone{
    zero = zero. wrap,
    succ = f
  }
  ->
  zero.
  cocone{
    zero = zero. wrap,
    succ = f
  }
  ->
  zero. wrap
  ```
  Done.
- Let's now do the `succ_case`:
  ```
  succ. wrap f -> succ. wrap cone{} zero. wrap
  ```
  Again we can simplfy:
  ```
  succ. wrap f -> cone{} zero. wrap
  ```
  We unwrap `f`:
  ```
  succ. wrap f
  ->
  succ. wrap
  unwrap
  cocone{
    zero = zero. wrap,
    succ = f
  }
  ->
  succ.
  cocone{
    zero = zero. wrap,
    succ = f
  }
  ->
  f
  -> [HERE WE ARE USING RECURSIVE EQUALITY]
  cone{} zero. wrap
  ```
  Done.

So, we get through, but we use the property itself, this is a cyclic proof.

Is the cyclic proof valid?

Reformulating as a fixed point induction doesn't work, because the base case is:
```
undefined -> cone{} zero. wrap
```
and these don't look equal, the LHS is totally undefined, the one of the right is totally defined.

But that's if we only consider 2-morphisms are equality. What if we consider them to be inclusion of partial functions? So, in the domain, for `f,g: a -> b`, `f -> g` means that, for all `x`, `f(x) <= g(x)` inside `1 + b`, which means, `f(x) undefined` and `g(x)` anything, or `f(x) defined` and `g(x) defined` and `g(x) == f(x)`.

Then can we do the fixed point induction? The property `P` we want to prove is:
```
f -> cone{} zero. wrap
```

- `undefined <= cone{} zero. wrap` ✓
- Assume `g <= cone{} zero. wrap` for some `g` then we want to prove that:
  ```
  unwrap
  cocone{
    zero = zero. wrap,
    succ = g
  }
  <=
  cone{} zero. wrap
  ```
  To proceed by cases we need to precompose with `wrap`. But then we'd need to know that: `wrap u <= wrap v` implies `u <= v`. For this we'd need to use that `wrap`/`unwrap` are _total_? Anyways, let's assume this is all okay, so we want to prove:
  ```
  cocone{
    zero = zero. wrap,
    succ = g
  }
  <=
  wrap cone{} zero. wrap
  ```
  and now we can proceed by cases.
  
  - We have the zero case:
    ```
    zero.
    cocone{
      zero = zero. wrap,
      succ = g
    }
    <=
    zero. wrap
    <=
    cone{} zero. wrap
    ```
  - And the `succ` case:
    ```
    succ.
    cocone{
      zero = zero. wrap,
      succ = g
    }
    <=
    g
    <=
    cone{} zero. wrap
    ```
    ✓

What have we proved?
```
f <= cone{} zero. wrap
```
That is, _in as far as `f` is even defined_, it is equal to the constantly zero function.

Proving that `f` is total, is another matter.

## Hylomorphisms and other recursion schemes

Another approach the language could take is to not allow definitions by general recursion. Instead, you must use specific recursion schemes, and conditions which ensure that they are well defined (terminate).
- Catamorphisms always terminate
- Hylomorphisms need the co-algebra to be _recursive_.

Let's look at `mergesort`.

The functor is:
```haskell
data TreeF a r = Empty | Leaf a | Node r r 
```

The algebra part:
```haskell
combine Empty = []
combine (Leaf x) = [x]
combine (Node l r) = merge l r
```

The coalgebra part:
```haskell
split []  = Empty
split [x] = Leaf x
split xs  = Node l r where
  (l, r) = splitAt (length xs `div` 2) xs
```
Is this coalgebra recursive? This would mean that for any algebra `TreeF a x -> x`, then is a unique coalgebra-to-algebra morphism `[a] -> x`. _On Well-Founded and Recursive Coalgebras_ paper gives the condition:

Existence of a homomorphism of `split` to `(μ (TreeF a), μ (TreeF a) -> TreeF a (μ (TreeF a)))`. This means, a morphism:
```
f : [a] -> μ (TreeF a)
```
such that DIAG.

What is `μ (TreeF a)`? It is (isomorphic to):
```
data Tree a = Empty | Leaf a | Node (Tree a) (Tree a) 
```
So it is binary trees (that can be empty) with `a` at the leaves. So in this case:
```haskell
f :: [a] -> Tree a
f []  = Empty
f [x] = Leaf x
f xs  = Node (f l) (f r)
  where
    (l, r) = split xs
```
Is `f : [a] -> Tree a` a homomorphism from `split`?
```
[a] --split--> TreeF a [a]
 |              |
 f              TreeF(f)
 |              |
 v              v
 Tree a -----> TreeF a (Tree a)
```
yes.

Note that this `f` is _not_ the anamorphism for `split`, which target `ν (TreeF a)` (nu). So we have to understand `data Tree` as the _finite_ haskell trees.

Can we define `f` via a cata?

Here is an alternative. We define tilted trees:
```haskell
data TiltedF a r
  = Empty
  | Leaf a
  | TiltLeft  r r
  | TiltRight r r
```
then, given a tilted tree, we can insert a new element into it:
```haskell
insert :: a -> Tilted a -> Tilted a
insert x Empty = Leaf x
insert x (Leaf y) = TiltLeft (Leaf x) (Leaf y)
insert x (TiltLeft  left right) = TiltRight (insert x left) right
insert x (TiltRight left right) = TiltLeft  left            (insert x right)
```

`foldr insert Empty xs` then turns a list into a tilted tree. This is total as long as `insert` is. But `insert` is a cata? I.e. it is defined by an algebra on `(Maybe a -> Tilted a)`:
```haskell
alg :: TiltedF a (Maybe a -> Tilted a) -> (Maybe a -> Tilted a)
alg t Nothing = t
alg Empty (Just x) = Leaf x
alg (Leaf y) (Just x) = TiltLeft (Leaf x) (Leaf y)
alg (TiltLeft  left right) (Just x) = TiltRight (left (Just x)) (right Nothing)
alg (TiltRight left right) (Just x) = TiltLeft  (left Nothing)  (right (Just x))
```
Can we define:
```haskell
foo :: [a] -> TiltedF a [a]
foo [] = Empty
foo [x] = Leaf x
foo xs =
    if even (length xs)
      then TiltLeft l r
      else TiltRight l r
  where
    (l, r) = split xs
```
This doesn't correspond to how we split it before.

See [Mergesort](mergesort.md) chapter.

## References

- [A Practical Fixed Point
Combinator for Type Theory](https://www.chargueraud.org/research/2009/fixwf/fixwf.pdf)
- How to prove that merge-sort terminates: https://softwarefoundations.cis.upenn.edu/current/vfa-current/Merge.html
- https://hackage.haskell.org/package/recursion-schemes-5.2.2.5
