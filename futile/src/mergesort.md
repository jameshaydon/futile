# Mergesort

## List reminder

```futile
// a bifunctor
def ListF :=
  colim{
    empty = lim{},
    cons  = lim{ hd = .elem, tl = .rec }
  }

// a functor
def List := Fix(ListF)

def empty : {} -> List :=
  empty. wrap

def cons : { hd = , tl = List } -> List :=
  cons. wrap

def single : -> List :=
  { hd = , tl = empty } cons
```

## Split a list in two

```futile
def Pair := lim( , )

def Distr :=
  colim{ done  = .elem List Pair
         distr = lim{ x = .elem, y = .elem, rest = .rec } 
  }

def halve : List -> List Pair := hylo distr poptwo

def distr : { elem = , rec = List LeftRight } Distr -> List Pair :=
  [ done  = ,
    distr = ( .x :: .rest.l, .y :: .rest.r ) ]

def poptwo : List -> {elem = , rec = List} Distr :=
  unwrap
  [ empty = (empty, empty) done.,
    cons  = .tl(unwrap) @tl
            [ empty = (.hd single, empty) done.,
              cons  = { x    = .hd,
                        y    = .tl.hd,
                        rest = .tl.tl } distr.
            ]
  ]
```

Note we use:
```
x :: xs
```
as notation for `{ hd = x, tl = xs } cons`.

## Merge two sorted lists

Here we specialise to `Nat` lists until we figure out how to handle the `Ord` typeclass.
```futile
def Merge := 
  colim{ done = Nat List,
         cons = lim{ hd = Nat List,
                     tl = }}

def rebuild : Nat List Merge -> Nat List
  := [ done = , cons = cons ]

def choose : Nat List Pair -> Nat List Pair Merge :=
  .1(unwrap) .2(unwrap) @1
  [ empty = .2 cons done.,
    cons  = @2
            [ empty = .1 cons done.,
              cons  = ( if .1.hd < .2.hd
                        then { hd = .1.hs, tl = (.1.tl, .2 cons )}
                        else { hd = .2.hs, tl = (.1 cons, .2.tl )}
                      ) cons.
            ]
  ]
```

## Finally mergesort

```futile
// a bifunctor
def TreeF :=
  [ empty  = {},
    single = .elem,
    merge  = .rec Pair ]
```
We want to define `mergesort` as a hylo, so we have to give an algebra and a co-algebra for `TreeF`.

```futile
def combine : { elem = , rec = List } TreeF -> List :=
  [ empty  = empty,
    single = single,
    split  = merge ] // note here we are ignoring the `Ord` problem.

def split : List -> {elem = , rec = List } TreeF :=
  { l = , l_ = unwrap }
  @l_
  [ empty = {} empty.,
    cons  = { x = .l_.hd, xs = .l_ .tl unwrap, l }
            @xs
            [ empty = .x single.,
              cons  = .l halve merge. ]
  ]
  
def sort : List -> List := hylo combine split
```

## Orders

How to deal with orders? Can we define a category of orders? A category has orders for all objects if there is a natural transformation from
```
A |-> lim(A, A)
```
to
```
A |-> Bool = [ true = {}, false = {} ]
```

We defined
```
def sort : List -> List
```
as a natural transformation between `List` and itself.



---

## Old stuff (don't read)

### Algebra

```futile
// This algebra is polymorphic, so it's also a natural transformation.
// List : C -> C
// { elem = , rec = List } : C -> { elem = C, rec = C }
// TreeF : { elem = C, rec = C } -> C
// { elem =  , rec = List } TreeF : C -> C
def alg : { elem = , rec = List } TreeF -> List := cocone{
  empty = emptyList,
  leaf  = singletonList,
  node  = mergeSortedLists 
}
```

where

```futile
// make an empty list
def emptyList : lim{} -> List
  := empty. wrap

// make a list with one element
def singletonList : . -> List
  := cone{ head = . , tail = cone{} emptyList } cons. wrap

def mergeSortedLists : lim{ left = List, right = List } -> List
  := ?
```

_TODO:_ how do we specify the `Ord` constraint? Or, how do we do all this assuming some `compare` param.

For now let's specialise to `Nat`:
```futile
def mergeSortedLists : Nat lim{ left = List, right = List } -> Nat List
  := ?
```

In haskell I think it is a hylo as:

```haskell
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
        then ChoseLeast x (  xs, y:ys)
        else ChoseLeast y (x:xs,   ys)

    rebuild :: MergeSortedF a [a] -> [a]
    rebuild = \case
      Done xs -> xs
      ChoseLeast x xs -> x:xs
```

In Futile:
```futile
def merge := hylo rebuild choose

def rebuild := cocone{ done = , cons = cons }

def MergeSortedF := 
  colim{ done = Nat List,
         cons = lim{ hd = .elem List,
                     tl = .rec }}

def LeftRight := lim{ left = List, right = List }

// polymorphic version would be:
// LeftRight -> { elem = , rec = LeftRight } MergeSortedF
def choose :
  Nat LeftRight -> { elem = Nat, rec = Nat LeftRight } MergeSortedF
  :=
  cone{ leftu  = .left  unwrap,
        rightu = .right unwrap,
        left, right
  }
  @leftu
  cocone{
    empty = .right done.,
    cons  = @rightu
            cocone{
              empty = .right done.,
              cons  = pickLeast cons.
            }
  }

def pickLeast :=
  (if   .leftu.head <= .rightu.head
   then cone{ least = .leftu,  left = .leftu.tail, right }
   else cone{ least = .rightu, left = .left, right = .rightu.tail })
  cone{ head = .least.head, tail = cone{left, right} }

// reminder:
def cons := cons. wrap
```

Can we write this to be closer to the Haskell? We can use positional records instead of "left"/"right", and use a similar naming scheme:
```futile
def merge := hylo rebuild choose

def rebuild := cocone{ done = , cons = cons }

def choose : Nat lim(List, List) -> Nat List :=
  cone{ l = .1, l_ = .1 unwrap, r = .2, r_ = .2 unwrap }
  @l_
  cocone{
    empty = .r done.,
    cons  = @r_
            cocone{
              empty = .l done.,
              cons  = pickLeast cons.
            }
  }

def pickLeast :=
  cone{
    x   = .l_.head,
    xs  = .l_.tail,
    xxs = .l,
    y   = .r_.head,
    ys  = .r_.tail,
    yys = .r
  }
  (if   .x <= .y
   then cone{ head = .x, tail = cone(.xs , .yys) }
   else cone{ head = .y, tail = cone(.xxs,  .ys) })
```

Note that "bindings" need to be defined by projection, rather than by "pattern-matching" or "destructuring". Mainly we'd like to bind `x` and `xs` in one go somehow from `l_`. Say:
```futile
cone{
  { head = x, tail = xs } = .l_,
  { head = y, tail = ys } = .r_
}
```

What is the meaning? Well, let's assume there is a flattening operation `/\` (from dhall), then you can:
```futile
.l_ cone{ x = .head, xs = .tail } /\ .r_ cone{ y = .head, ys = .tail }
```
Not a huge leap to:
```futile
cone{
  .l_ { x = .head, xs = .tail },
  .r_ { y = .head, ys = .tail }
}
```

---

The above patterns are basically for handling "nested products", because we are dealing with a product with a component `l_` which itself points to a product, and we want to explode that out into a flattened product.

What about coproducts? E.g. if we have
```futile
colim{ a = colim{u = ?, v = ?}, b = ? } --> ?
```
Then we might define a morphism as:
```futile
cocone{
  a = cocone{
    u = ?,
    v = ?
  },
  b = ?
}
```
but what about
```futile
cocone{
  a u = ?,
  b v = ?,
  b   = ?
}
```

---

There is another way to define `choose` maybe:
(for now, let's elide the `unwrap` calls:)
```futile
def choose : Nat lim{ left = List, right = List } -> Nat List :=
  @{left,right} // distribute on several sum components of a product
  cocone{
    empty.empty = cone{} empty done.,
    empty.cons  = .r cons done.,
    cons.empty  = .l cons done.,
    cons.cons   = pickLeast cons.
  }
```
this has effectively split up the analysis into 4 cases.

```futile
def choose :
  Nat LeftRight -> { elem = Nat, rec = Nat LeftRight } MergeSortedF
  :=
  .l(unwrap) .r(unwrap) @l
  [ empty = .r cons done.,
    cons  = @r
            [ empty = .l cons done.,
              cons  = ( if .l.hd < .r.hd
                        then { hd = .l.hs, tl = {l = .l.tl, r = .r cons }}
                        else { hd = .r.hs, tl = {l = .l cons, r = .r.tl }}
                      ) cons.
            ]
  ]
```

---

## Coalgebra

This is the function which splits a list. How de we define this with a cata? We want to use an accumator (a pair of lists) and add elements to the left or right one in alternation:
```futile
TreeF = colim{
    empty  = lim{},
    single = Nat,
    split  = lim{ l = , r = }
  }

def split : Nat List -> Nat List TreeF 
:=
  unwrap
  [ empty = empty.,
    cons  = @tl
            [ empty = .hd single.,
              cons  = 
            ]
  ]
  
```
we could have not swapped them and used a bool instead:
```futile
cocone{
  empty = cone{ left = emptyList, right = emptyList, which = true },
  cons  = @.tail.which
          cocone{
            true  = ?, // add to the left side
            flase = ?  // add to the right side
          }
}
```

_TODO:_ note this distributes on a nested product. We haven't defined this formally.


