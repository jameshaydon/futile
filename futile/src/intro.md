# Goals

_Futile_ is a functional programming language which aims to fully embrace the
pointfree programming style. The language is still in development. The current journey is at an odd stage:
- At the moment `futile` has no λs:
  - By lambdas not being available while I am designing it, it forces the language develop good pointfree ergonomics.
  - Not supporting lambdas makes programming other features much faster during
    this prototyping stage.
- I am not developing the type-system at the moment. The previous incarnation ([lawvere-lang](https://github.com/jameshaydon/lawvere "GitHub")) had a type system. In this iteration I have decided that I want to explore the term level thoroughly first, before deciding what's best for the type system.
- I am developing the proof system for proving equality of terms.

## Things I like from other languages

### OCaml

- Functors: https://dev.realworldocaml.org/functors.html
- First class modules https://dev.realworldocaml.org/first-class-modules.html
- 1ML: https://people.mpi-sws.org/~rossberg/1m/l and https://www.cambridge.org/core/services/aop-cambridge-core/content/view/47B10882829E4B32F98FBA93B28CEF30/S0956796818000205a.pdf/1ml-core-and-modules-united.pdf

### Dhall

- Dhall just has expressions for everything. A "package" or "module" is simply an expression that (usually) returns a record of all the things "exported" by that package.
- Dhall uses a lot of records, and has operators to make things nice. We should have the same operators probably.

### Morte et al

### Koka

Modules use `/` instead of `.`, like unix filesystem.

### Unison

### Erlang / Elixir

### Agda

### Frank

### Other materials

- An interesting blog post about design choices in Rust: https://graydon2.dreamwidth.org/307291.html

## Booleans

Here is the definition of `not`:
```futile
def not := [ true = false., false = true. ]
```

We can test this out at the REPL:
```
> false. not
true.
> true. not
false.
```

We notice that `not not` behaves the same as the identity function:
```
> true. not not
true.
> false. not not
false.
```

Futile can prove that `not not` is the same as the identity function:
```futile
prop not not == .
```

## Natural numbers

```futile
// Defines addition
def plus := @1 [ zero = .2, succ = plus succ. ]
```

This is a recursive definition. So we need to make into a module:
```futile
{
  plus = @1 [ zero = .2, succ = plus succ. ]
}
```

## Mapping over lists

```futile
// A module is a list of definitions.
// The module might depend on other arrows which aren't specified yet, in this case `trans`.
// In terms of types, this corresponds to a functor from freely generated categories.
map := {{
  out =
    [ empty = empty.,
      cons  = { head = .head trans, tail = .tail out } cons. ]
}}

// If you write down a module in a term, then the _target_ of that functor is the current category being programmed in.
def zim :=
  {1, 2, 3, 4}
  ({ trans = inc inc } map)/out
```



