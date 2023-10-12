# Random

Can you write a "macro" to "run a function twice"?:
```
macro dup(f) = f f
```

Can we define `𝐁Nat`? Can we define `𝐁Rel`? Can we define functors from these categories?

These questions are related.

And, can we functor from these categories? If we could, then we could define `4`
for example (as a morphism), and then we could get `f f f f` for any `f` in any
morphism by functoring from `𝐁Nat`.

```futile
def category Loop := {
  gen *
  gen one : * -> *
  two     : * -> * := one one
  three   : * -> * := two one
  four    : * -> * := three one
}
```

or with more inference:

```futile
def category Loop := {
  gen *
  gen one : * -> *
  two   := one one
  three := two one
  four  := three one
}
```

Then, when programming in some category `C`, one where we have defined `Nat` and
`inc` say, we should be able to define a functor from `Loop`, anonymously:

```
{ * = Nat, one = inc }
```

You only need to define the functor on the generators.
Note that this notation is consistent with the notation we have already been using for limits and colimits:
```futile
lim{ x = Nat, y = Nat }
colim{ empty = lim{}, cons = lim{ head = Nat, tail = List } }
```

These are defining functors, e.g. `{ x = Nat, y = Nat }` (from a discrete category with two generator objects `x` and `y`), and then applying the special operator `lim` or `colim`.

With more inference it can even be:
```
{ one = inc }
```
because it knows that `inc : Nat -> Nat`, so it can infer from this that `*` maps to `Nat`.

So `{ one = inc }` is a functor `Loop -> C`, and now we wish to extract the image of `two`. Applicative syntax:
```
{ one = inc }(two)
```
(seems ugly.)

or we could consider the universal floating arrow `A`, so that we get a functor
`two : A -> Loop`, and then
```
two { one = inc } : A -> C
```
picks out `inc inc` in `C`. There might be some syntax for coercion between `A -> C` are arrows of `C`, something like:
```futile
def plus2 : Nat -> Nat :=
  #(two { one = inc })
```

Or maybe we just have functor application:
```futile
def plus2 : Nat -> Nat :=
  two where { one = inc }
```
or some notation:

```
{ one = inc }(two)
two over { one = inc }
two for { one = inc }
two given { one = inc }
two using { one = inc }
two with { one = inc }
{ one = inc } on two
two using { one = inc }
{ one = inc } @ two
[[ two | one = inc ]]
{two | one = inc}
{| two | one = inc |}
apply { one = inc } two
```

point is, applying a functor should have good notation.
