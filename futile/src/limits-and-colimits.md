# Limits and Colimits

This is about limits and colimits.

Before I was writing cones and cocones like this:
```futile
cone{ x = inc, y = inc }
cocone{ x = inc, y = inc }
```

But now I think maybe I could write them like this:
```
{ _ .x = inc,
  _ .y = inc }
{ x. _ = inc,
  y. _ = inc }
```
This makes it clear what the equations are, the unknown variable is `_`, and it has scope delimited by the curly braces.

Limits were specified like this:
```
lim{ x = Real, y = Real }
```
One of the ideas here was that `{ x = ?, y = ? }` notation in general was used for _functors_ from freely generated categories, and so in general one could put on the LHS of `=` any generator of that category.

When looking at recursive datatypes, it seemed that it was advantageous to consider objects as functors from the terminal category. Then `lim{ x = A, y = B }` is interpreted as the functor, with the same source as `A` and `B`, which computes the product of the functors `A` and `B`. When the target category is complete, this is the pointwise product.

Then suppose you are defining a morphism `X -> lim{ x = A, y = B }`. Then this is the same as asking for two natural transformations:
- `x : X -> A`
- `y : X -> B`

or a natural transformation
```futile
cone{} X -> {x = A, y = B }
```



---

One thing that would be nice is nice notation for component-wise mapping.

At the moment if you have
```
T := lim{ a = Nat, b = Nat}
```
and you want to define
```
T -> T
```
which increments both components then you have to write:
```
cone{ a = .a inc, b = .b inc }
```
with the other notation this is:
```
{ _ .a = .a inc, _ .b = .b inc }
```

Each label should define a map, so for example:
```
f : A -> B
.foo(f) : lim{ foo = A, bar = X } -> lim{ foo = B, bar = X }
```

Similarly for coproducts.

What about a fibre-product?
```
X := lim{ a = A, b = B, c = C, f:a->b = f, g:b->c = g }
```

In this case if you have a primed version `X'` and
```
aMap : A -> A'
bMap : B -> B'
cMap : C -> C'
```
then for this to define `X -> X'` you need:
```
.a aMap : X -> A'
.b bMap : X -> B'
.c cMap : X -> C'
```
such that
```
.a aMap f' = .c cMap
.b bMap g' = .c cMap
```
If
```
aMap f' = f cMap
bMap g' = g cMap
```
then:
```
  .a aMap f'
= .a f cMap
= .b g cMap
= .b bMap g'
```

So in conclusion, we note that you get `X -> X` if you can define `aMap` and `bMap` such that
```
aMap f' = f cMap
bMap g' = g cMap
```
In particular, if `bMap` and `cMap` are identities then `g' = g` and you need
```
aMap f' = f
```
Therefore for `.a(aMap) : X -> X'` to be valid, you must check:
```
aMap f' = f
```

## Cones

It seems like it would be really nice to use `{ .. }` instead of `cone{ .. }` in the terms. A cone is a morphism to a limit.

## Cocones

Note that whenever we have any morphisms `c : X -> colim{ a = A, b = B}` then we can define a morphism
```futile
case c : X -> colim{ a = X, b = X }
```
by:
```futile
cone{ of = c, env = } @of cocone{ a = .env, b = .env }
```

That way you can define morphism like:
```futile
(case c)
cocone{ a = ?, b = ? }
```

In particular, when looking at `Bool`:
```futile
(case c) cocone{ true = ?, false = ? }
```

Note that this isn't useful when you need the payload of the summand, since that information is thrown away.

So, we can specify a component label for storing the payload. This _only works when `X` is a limit_. So for example, if `T = lim{x = X, y = Y}` and `c : T -> colim{ a = A, b = B}`, then
``` futile
case c as foo
  : T
    ->
    colim{ a = lim{ x = X, y = Y, foo = A },
           b = lim{ x = X, y = Y, foo = B } }
```
and so can be used like this:
```futile
(case c as foo)
cocone{
  a = ?,
  b = ?
}
```
`case c as foo` is defines as:
```futile
cone{ foo = c,
      env = }
@foo
cocone{ a = .env /\ cone{ foo = .foo },
        b = .env /\ cone{ foo = .foo } }
```

For example:
```futile
plus : lim{ a = Nat, b = Nat } -> Nat :=
  (case unwrap .a as aprev)
  cocone{
    zero = .b
    succ = cone{ a = .aprev, b = .b} plus succ. wrap
  }
```
We could instead do:
```futile
plus : lim{ a = Nat, b = Nat } -> Nat :=
  (case unwrap .a as a)
  cocone{
    zero = .b
    succ = plus succ. wrap
  }
```
Note that this is specifying a label that is _already in the limit_, hence this is a form of shadowing, and hence we should think about if this should be allowed (and the definition uses `/\`, which also could allow or not allow this).

Can this be iterated?
```
(case
  .left  unwrap as leftu
  .right unwrap as rightu)
```
this will 
