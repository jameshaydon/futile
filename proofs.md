# Proofs

Here we are talking about proving equality of arrows.

- Most of the steps of a proof will just involve searching for equality between
  two terms.
- We do this mostly just by applying many re-writes.
- When doing this inside a module, a name can be re-written by its definition.
- When doing this inside a _recursive_ module, then names will be replaced by
  definitions, and upon doing so, the names _within_ will become "active". This
  means that theorems (including the one you are currently trying to prove) can
  apply to them.

## rewrites

Standard stuff from category theory.

Distribution re-write:

When you have a situation like:

```
{ lbl = F con., ... } @lbl [ con = G, ... ]
```

Then this can be re-written to:

```
{ lbl = F, ... } G
```

## Proving equality of terms from a coproduct

Then you must prove after pre-composition with all the injections.

## Proving equality of terms to a product

Then you must prove after post-composition with all the projections.
