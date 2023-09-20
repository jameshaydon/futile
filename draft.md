# Lawvere-lang 2

A small text explaining the new features.

The toplevel is about defining objects in the category of categories, `CAT`.
Let's see an example:

```
Bool : forall C. (Colim C, Lim C) => C[ Bool, not : Bool -> Bool ] -> C
  := { Bool = colim{ true = lim{}, false = lim{} } ,
       not  = cocone{ true = false., false = true. }
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
{ Bool = colim{ true = lim{}, false = lim{} } ,
  not  = cocone{ true = false., false = true. }
}
```

Whenever `Q` is a quiver, and `C` is a category, then this notation between
curly braces can be used to defined a functor `C[Q] -> T`, to some category `T`.
Inside the curly braces should be the same objects/morphisms as in the quiver,
paired with what they are mapped to under the functor. So
```
{ Bool = colim{ true = lim{}, false = lim{} } ,
  not  = cocone{ true = false., false = true. }
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
{ Bool = colim{ true = lim{}, false = lim{} } ,
  not  = cocone{ true = false., false = true. }
}
```

implies a functor from a a free category generated an object symbol `Bool`, and
a morphism symbol `not : Bool -> Bool`. So we can just write:

```
Bool :=
  { Bool = colim{ true = lim{}, false = lim{} } ,
    not  = cocone{ true = false., false = true. }
  }
```

In fact, `lawvere` infers something more general for this definition:

- Since it is a definition of the form `{ ... }`, this is a
  functor between two categories `X` and `D`.
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
