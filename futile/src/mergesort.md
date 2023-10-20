# Mergesort

```futile
// a bifunctor
def ListF :=
  colim{
    empty = lim{},
    cons  = lim{ head = .elem, tail = .rec }
  }

// a functor
def List := Fix(ListF)

// a bifunctor
def TreeF :=
  colim{
    empty = lim{},
    leaf  = .elem,
    node  = lim{ left = .rec, right .rec } 
  }

// a functor
def Tree := Fix(TreeF)
```
We want to define `mergesort` as a hylo, so we have to give an algebra and a co-algebra for `TreeF`.

Algebra:
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

def choose : Nat lim{ left = List, right = List } -> Nat List :=
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

Note that "bindings" need to be defined by projection, rather than by "pattern-matching" or "destructuring". Mainly we'd like to bind `x` and `xs` in one go somehow, from `l_`. Say:
```futile
cone{
  { head = x, tail = xs } = .l_,
  { head = y, tail = ys } = .r_
}
```
if we had used tuples in the definition of `List`:
```futile
cone{
  (x, xs) = .l_,
  (y, ys) = .r_
}
```
the idea here is that if the LHS of an `=` is not a label, then it must be a pattern.
```futile
cone{
  x :< xs = .l_,
  y :< ys = .r_,
  // ...
}
```

This means you've defined some sort of "pattern" `:<`:
```futile
head :< tail
```

Coalgebra:
This is the function which splits a list. How de we define this with a cata? We want to use an accumator (a pair of lists) and add elements to the left or right one in alternation:
```futile
cocone{
  empty = cone{ left = emptyList, right = emptyList },
  cons  = cone{ left  = { head = .head, tail = .tail.right } cons,
                right = .tail.left }
}
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
