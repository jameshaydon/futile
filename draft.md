# Lawvere-lang 2

A small text explaining the new features.

The toplevel is about defining objects in the category of categories, `CAT`.
Let's see an example:

```
Bool : forall C. (Colim C, Lim C) => C[ Bool, not : Bool -> Bool ] -> C
  := { Bool
         = colim{ true = lim{}, false = lim{} } ,
       not : Bool -> Bool
         = cocone{ true = false., false = true. }
     }
```

Let's dissect this step by step:

```
Bool : forall C. (Colim C, Lim C) => C[ Bool, not : Bool -> Bool ] -> C
```
This says: we will define a thing called `Bool`, followed by a signature.
The signature starts with `forall C`, so this means "for all categories `C`".
Then comes `(Colim C, Lim C) =>`, this means we require `C` has colimits and limits.

Since the toplevel is `CAT`, `C[ Bool, not : Bool -> Bool ] -> C` is a _functor_
between two categories: `C[ Bool, not : Bool -> Bool ]` and `C`.

- `C[ Bool, not : Bool -> Bool ]` is the free extension of `C` by the quiver
  `(Bool, not : Bool -> Bool)`. This is the category obstained from `C` by
  freely adjoining an object `Bool` and an arrow `not : Bool -> Bool`.
- `C` is just `C`

Then comes `:=`, which means "is defined as".

Then comes: 
```
{ Bool
    = colim{ true = lim{}, false = lim{} } ,
  not : Bool -> Bool
    = cocone{ true = false., false = true. }
}
```

Whenever `Q` is a quiver, and `C` is a category, then this notation between
curly braces can be used to defined a functor `C[Q] -> T`, to some category `T`.
Inside the curly braces should be the same objects/morphisms as in the quiver,
paired with what they are mapped to under the functor. So
```
{ Bool
    = colim{ true = lim{}, false = lim{} } ,
  not : Bool -> Bool
    = cocone{ true = false., false = true. }
}
```

maps `Bool` in `C[ Bool, not : Bool -> Bool ]` to `colim{ true = lim{}, false =
lim{} }`, and similarly for `not`.

`colim{ true = lim{}, false = lim{}}` is an object of `C`, defined as a colimit.

To define a colimit, we need to define a functor into `C` that we take the
colimit of. In this case we will use a functor from a quiver consisting
of two objects called `true` and `false`, and use the same notation:

```
{ true = lim{}, false = lim{}}
```
sends the object `true` to `lim{}`, and the object `false` to `lim{}`.

`lim{}` is a limit, taken in `C`, from the empty quiver.

As for `not`, this is sent to a morphism of `C`:

```
cocone{ true = false., false = true. }
```

This morphism is a morphism from a colimit defined as a cocone. A cocone is
specified by providing all the components of the cocone.

The components in this case are `false.` and `true.`, this is notation for
coprojections. Whenever you have a colimit over a discrete diagram with an
object called `a`, then `a.` denotes the coprojection for the `a` component.

fortunately, `lawvere` infers much of this for us. Because we use limits and
colimits in `C`, the constraints `(Colim C, Lim C)` are inferred. Furthermore,
the notation
```
{ Bool
    = colim{ true = lim{}, false = lim{} },
  not : Bool -> Bool
    = cocone{ true = false., false = true. }
}
```

implies a functor from a a free category generated an object symbol `Bool`, and
a morphism symbol `not : Bool -> Bool`. So we can just write:

```
Bool :=
  { Bool
      = colim{ true = lim{}, false = lim{} } ,
    not : Bool -> Bool
      = cocone{ true = false., false = true. }
  }
```

In fact, `lawvere` infers something more general for this definition:

- Since it is a definition of the form `{ ... }`, this is a functor between two
  categories `X` and `D`, that will be defined on some formal symbols of `X`.
- Since it is of the form `{ Bool = _, not = _ }`, the category `C` much have a
  formal object symbol `Bool` and a formal arrow symbol `not : Bool -> Bool`.
- Since that is all that defines the functor, the rest must be implicit. That
  is, `X` must be of the form `C[Bool, not : Bool -> Bool]`, where `C` is a
  category such that there is a canonical functor `C -> D`.
- `D` must have limits and colimits.

This signature would be written:
```
forall C. forall D. (Colim D, Lim D, Can C D) => C[Bool, not : Bool -> Bool] -> D
```

We might then want to prove some fact, for example that `not not = .`, that is,
`not` composed with itself is the identity. To do this we would add this:

```
Bool :=
  { Bool
      = colim{ true = lim{}, false = lim{} } ,
    not : Bool -> Bool
      = cocone{ true = false., false = true. },
    not_involution : not not -> id
      = PROOF
  }
```

This is now adding a new formal symbol `not_involution`, an arrow (at this level
and equality) between `not not` and `id` in the source category. For the functor
to make sense, we must therefore prove this equality in the target category,
this is what `PROOF` is. We will discuss syntax for proofs later.

## Maybe

Needs to depend on an element type.

```
sketch Maybe :=
  { }
```

## Naturals

Needs recursion.

```
sketch NatSketch :=
  { Nat,
    plus  : (Nat, Nat) -> Nat,
    times : (Nat, Nat) -> Nat
  }
```

```
functor Nat : F(NatSketch) -> F(NatSketch) :=
  { Nat   = colim{ zero = lim{}, succ = Nat },
    plus  = @1 cocone{ zero = .2, succ = plus succ. },
    times = ...
  }
```

If we want to instantiate this into some known category, say `Set`, then we need
`Set` to have some properties:
- needs limits and colimits
- needs to have recursive definitions of object/morphisms, that is, we should be
  able to "solve" the above endofunctor for a least fixed point.

```
fix(Nat) : F(NatSketch) -> Set
```

## Lists

This needs a lot of language features:
- Needs recursion.
- Needs to depend on an element type.
- Needs to depend on `Maybe` (for `headMay`).
- Needs "higher order macros" (for `map`, `filter`).
- Needs to depend on `Bool` (for `filter`).

```
sketch ListSk = {
  import Elem;
  import Nat;
  List;
  length: List -> Nat;
  concat: lim{ x = List, y = List } -> List;
}

functor List : F(ListSk) -> F(ListSk) over Elem :=
  { List = colim{ empty = lim{}, cons = lim{ head = Elem, tail = List } },
    length = cocone{ empty = zero., cons = .tail length succ. },
    concat = ...
  }

// if we want to get some list type in set immediately
functor SetListInt = fix List over { Elem = Int }

// but really we'd just keep programming some other module
{
  import Nat;
  import List as NatList over { Elem = Nat };
  NatList
}
```

### Map

```
sketch MapInput :=
  { import List as A;
    import List as B;
    f : A.Elem -> B.Elem;
  }

sketch MapOutput :=
  { import MapInput;
    out : A.List -> B.List
  }
  
functor Map : MapOutput -> MapOutput :=
  { over MapInput;
    out : A.List -> B.List
      = cocone { empty = empty.,
                 cons  = { head = .head f, tail = out } cons. }
  }
```

Then, when programming in some category `C` and we want to map over a list, then
that means we have enough to specify a functor:

```
MapInput -> C
```

except we can't, because that would involve specifying `out`, which is what we
are trying to get in the first place. This is a _recursive_ definition.

```
fix Map over { f = <<<complex expression>>> }
```

Do we need to import `List` into `MapInput`?

We could do something like this:

```
sketch MapInput :=
  { import Elem as A;
    import Elem as B;
    f : A.Elem -> B.Elem;
  }

sketch MapOutput :=
  { import MapInput;
    import List as A;
    import List as B;
    out : A.List -> B.List
  }
  
functor Map : MapOutput -> MapOutput :=
  { over MapInput;
    over A;
    over B;
    out : A.List -> B.List
      = cocone { empty = empty.,
                 cons  = { head = .head f, tail = out } cons. }
  }
```

But note here that there is a conflict in the lines:
```
import MapInput;
import List as A;
import List as B;
```
since `MapInput` imports `Elem as A`, and so does `List as A`. Of course we _want_ this conflict.

```
sketch MapInput :=
  { import Elem as A;
    import Elem as B;
    f : A.Elem -> B.Elem;
  }

sketch MapOutput :=
  { import MapInput;
    import List as A extending MapInput.A;
    import List as B extending MapInput.B;
    out : A.List -> B.List
  }
  
functor Map : MapOutput -> MapOutput :=
  { over MapInput;
    over A;
    over B;
    out : A.List -> B.List
      = cocone { empty = empty.,
                 cons  = { head = .head f, tail = out } cons. }
  }
```

What we are really doing is a colimit of sketches:

We assume we already have the `Elem` sketch and the `List` sketch, along with `ListOf : Elem -> List` inclusion of sketches. And that we have already defined `MapIn` sketch, along with the inclusions of sketches `MapInA : Elem -> MapIn`, `MapInB : Elem -> MapIn`

Then `MapOut` is:

```
MapOut :=
  colim{
    In = MapIn,
    ListA = List,
    ListB = List,
    ElemA = Elem,
    ElemB = Elem,
    ListOfA : ElemA -> ListA = ListOf,
    ListOfB : ElemB -> ListB = ListOf,
    InA : ElemA -> In = MapInA,
    InB : ElemB -> In = MapInB
  }
```

This is too tedious. So let's use the other notation, and start from the
beginning:

```
sketch Elem = { Elem }

sketch List = {
  import Elem as Elem;
  List;
  length : List -> Nat;
  concat : lim{ a = List, b = List } -> List;
  cons :   lim{ x = Elem, l = List } -> List;
}

can : Elem -> List

sketch MapIn = {
  import Elem as Src;
  import Elem as Tgt;
  func : Src.Elem -> Tgt.Elem
}

Src : Elem -> MapIn
Tgt : Elem -> MapIn

sketch MapOut = {
  import List as ListSrc;
  import List as ListTgt;
  import MapIn as In;
  
  Src In == Elem ListSrc;
  Tgt In == Elem ListTgt;
}

      Elem       ListSrc
Elem ----> List ------> MapOut
  |
  | Src
  v          In
MapIn ----------------> MapOut
  ^
  | Tgt
  |
Elem ----> List ------> MapOut
      Elem       ListSrc
```

```
map = module {
  use Elem as Src;
  use Elem as Tgt;
  func : Src.Elem -> Tgt.Elem;
  map = 
}
```



```
double : Th{ B, out : B -> B } -> Th{ A, f : A -> A }
double = { B = A, out = f f }

// Then when programming in some category C, for which E is an expression for a morphism
// { f = E } is a functor Th{A, f : A -> A } -> C
// double { f = E } is a functor Th{ B, out : B -> B } -> C
// #double { f = E } is a morphism of C

double { f = E } is a functor Th{ B, out : B -> B } -> C
```


```
nat : Th(NatSk) -> Th(NatSk)
nat =
  { Nat  = colim{ zero = lim{},
                  succ = Nat
                },
    plus : (Nat, Nat) -> Nat =
      @1 cocon{ zero = .2, succ = plus succ. },
    plusAssoc : cone(.1, (.2, .3) plus) plus = cone((.1, .2) plus, .3) = AUTO
  }
```

```
list : Th(ListSk) -> Th(ListElemSk)
list = {
  import nat,
  List = colim{ empty = lim{}, cons = {head = Elem, tail = List } },
  length = ...
}
```

```
foo = {
  import nat;
  import list;
  // List = colim{ empty = lim{}, cons = { head = Elem, tail = List }};
  Elem = Nat;
  foo = #map { f = <...> }
}
```

```
zeroRightNeutral

( . , cone{} zero. ) plus = .   ?

assuming: ( . , cone{} zero. ) plus = .
prove:    ( . , cone{} zero. ) @1 cocone{ zero = .2, succ = plus succ. } = .

therese are morphisms Nat -> Nat

prove by precom with zero. and succ.
zero. : lim{} -> Nat

zero.:

zero. ( . , cone{} zero. ) @1 cocone{ zero = .2, succ = plus succ. }
=
( zero. , zero. cone{} zero. ) @1 cocone{ zero = .2, succ = plus succ. }
=
( zero. , zero. cone{} zero. ) @1 cocone{ zero = .2, succ = plus succ. }
=
(  , zero. cone{} zero. ) .2
=
zero. cone{} zero.
=
cone{} zero.
=
zero.

precomp with succ.:

succ. ( . , cone{} zero. ) @1 cocone{ zero = .2, succ = plus succ. }
=
( succ. , succ. cone{} zero. ) @1 cocone{ zero = .2, succ = plus succ. }
=
( . , succ. cone{} zero. ) plus succ.
=
( . , cone{} zero. ) plus succ.
=
( . , cone{} zero. ) plus succ.
=
succ.
```

```
( . , cone{} zero. ) plusSOURCE = .

transform:

( . , cone{} zero. ) @1 cocone{ zero = .2, succ = plusTARGET succ. } = .
```

## Again again

```
sketch Nat := { 
  Nat,
  plus: (Nat, Nat) -> Nat,
  succ: Nat -> Nat,
  pred: Nat -> colim{ ... },
  assoc: ff == gg : (Nat, Nat, Nat) -> (Nat, Nat, Nat)
}

interp NatI of Nat :=
  {  Nat = colim{},
     plus = ...
  }
  
List := sketch { Elem, List, concat: (List, List) -> List }

ListI := interp of List
  require Nat;
  {
  }
```

```
DoubleSketch :=
  sketch {
    extends NatSketch;
    double : Nat -> Nat
  }

Double :=
  rec interp of DoubleSketch
  { double = pred cocone{ zero = zero, succ = double succ succ } }
```

because `DoubleSketch` _extends_ `NatSketch`, any interpretation of
`DoubleSketch` is assumed to take place in a category where `NatSketch` has
already been interpreted. Note that we don't care _how_ is is interpreted, all
that it requires is the _interface_ described by the sketch.

```
ElemT := theory { Elem }

ListT :=
  theory {
    extends Nat;
    extends Elem;
    List,
    length: List -> Nat,
    concat: (List, List) -> List
  }

List := rec interp ListT
  { List = colim{ empty = lim{},
                  cons = lim{ head = Elem, tail = List } },
    length = ...,
    concat = ...
  }
```

Here we want to talk about a situation which involves lists of natural numbers:
```
ListNatT :=
  theory {
    extends NatSketch;
    extends Elem;
    extends ListSketch;
    sum: List -> List
  }
```

Again since it extends the previous theories, any interpretation will already
have those theories interpreted. But, what about the `Elem` theory? In this case
we don't want to assume _any_ interpretation, we want to assume one where it
coincides with that of `Nat`.
