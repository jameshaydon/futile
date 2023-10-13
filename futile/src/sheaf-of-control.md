# Sheaf of control

We define the following:
- A _network structure_ is a finite category `N` that is a _site_, that is, is equipped with a _coverage_.
- A _geometry_ for the network structure is a morphism of sites `G : N -> A`, where `A` is some "geometric" category. We will always use some sub-category of the category of opens in `R^n` for some `n`.
- A _static_ is a `S : Sh(N)` (a sheaf on the site `N`).

Given the above, a _map_ is:
- A sheaf `M : PSh(N)`
- A morphism of sheaves `M -> S`

A _point_ `x` (of the map `M`) is:
- for each `n : N`, a subset `x(n)` of `M(n)`
- a function `loc(n) : x(n) -> G(n)`
- such that, if `i : n -> m` in `N`, then:
```
x(n) == (G(i) ⚬ loc(n))⁻¹( loc(m)(x(m)) )
```

Given some object `a : A`, let `Dyn(a)` refer to the possible dynamics.

A _local controller_ is a morphism of sheaves `S -> Dyn ⚬ G`.

So this assigns, for each `n : N` of the network structure, a function `S(n) -> Dyn(G(n))`, in other words, a dynamics that is parametrised by a static structure on `n`.

A _gobal controller_ is a morphism of sheaves `M × S -> Dyn ⚬ G`, so a function `M(n) × S(n) -> Dyn(G(n))` for all `n`, this is a dynamics that is parametrised not only on the obstacles, but also on the instance of the road segment `n`.

_Note:_ These definitions are really just about specifying dynamics, controllers can be more general, for example they can stop given some condition and then use a different dynamics, etc. TODO: generalise to more general controllers.
 
**Theorem:** (Example): _Consider a global controller `Glob` and a local controller `Loc`. Consider a local precondition `P` (defined much like a local controller). We can build a global simplex controller `Simplex(Glob, P, Loc)`. If `Loc` is locally safe given it is engaged when `P`, then `Simplex(Glob, P, Loc)` is globally safe._

---

Example:

Site `N`:
- objects are named `Big`, `Med` and `Small`.
- morphisms:
  ```
  left   : Med -> Big
  right  : Med -> Big
  sleft  : Small -> Med
  sright : Small -> Med
  small  : Small -> Big
  ```
  and all the identities and compositions of these such that `small = sleft right = sright left`. 
- coverages:
  - `left` and `right` is a coverage for `Big` (you can add `small`)
  - `sleft` and `sright` is a coverage for `Med`
  - `id` is a coverage for `Small`

`G` interprets these as segments of straightline roads, driving is imagines as left-to-right direction:
- `G(Big)` is some open rectangular area of R^2 of width 5 and length 50.
- `G(Med)` is some open rectangular area of R^2 of width 5 and length 40.
- `G(Small)` is some open rectangular area of R^2 of width 5 and length 20.

`S` adds obstacles to the roads:
- `S(Big)` is a finite set of points in `G(Big)`
- ...

The definitions specialise:
- _map:_ road network obtained by glueing straight line roads together. Each segment has a set of obstacle points.
- _local controller:_ a controller for each **sort** of road segment, that is aware of the obstacles on that road segment.
- _global controller:_ a controller for _each_ road segment, that is aware of the obstacles.

Then we can define a local controller which:
- keep on the road (doesn't hit the sides)
- comes to a stop
- doesn't hit obstacles

We can then consider an arbitrary global controller that satisfies some minimum conditions, and consider the simplex. Then we can prove that the simplex is safe. The cool think here is that the local controller: _doesn't know about the full map_.
