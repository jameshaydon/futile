# Cyber Physical systems

An attempt at parallel programs of cyber-physical systems.

We'll say a type `T` is _physical_ if it is isomorphic to `R^n` for some `n`. We could make this more general (e.g. like a differentiable manifold). Such a type has a corresponding type `Dyn(T)` of _dynamics_ on `T`.

Given a physical type `T`, we let `Open(T)` be the _open conditions_ on `T`.

An _open system_ is:
- a _physical state_ type `P` (which is a physical type),
- a _cyber state_ type `C`,
- an _interface_, comprised of
  - `I` (physical), the _input_,
  - `O` (physical), the _output_,
  - `out : C -> (P -> O)`, the _output interface_, such that `out(c)` is continuous for all `c`.',
- a _dynamics_, an element of `I × C -> Dyn(P)`,
- _output events_ type `E`,
- _input events_ type `R`,
- a _program_, which is:
  - `wait(cond)` where `cond` is a disjunction of:
    - input events, or
    - `C -> Open(I × P)`
  - `upd(f)`, where `f : I × P × C -> C`
  - `emit(e)`, where `e` is an output event,
  - `p; q`, sequencing of two programs `p` and `q`,
  - `if cond then p else q`, where `p` and `q` are programs, and `cond : I × P × C -> Bool`.

Several open systems can be put into parallel composition to create a new open system via a _wiring_. We'll just do parallel composition of two systems, the general case is similar. Given two systems `A` and `B`, the wiring consists of functions:
- `I × O_A -> I_B` mapping general inputs and outputs of `A` into `B`'s inputs,
- `I × O_B -> I_A` mapping general inputs and outputs of `B` into `A`'s inputs,
- `O_A × O_B × O` mapping `A`'s and `B`'s outputs to the general outputs.
