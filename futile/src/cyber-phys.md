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
  - `upd(f)`, where `f : I × P × C × [0,1] -> C`, the `[0,1]` param is a source of randomness,
  - `emit(e)`, where `e` is an output event,
  - `p; q`, sequencing of two programs `p` and `q`,
  - `if cond then p else q`, where `p` and `q` are programs, and `cond : I × P × C -> Bool`.

Remarks:
- Programs can be recursive.
- There is no termination of systems. Termination is always externally controlled.
- Systems can exhibit Zeno behaviour.

Several open systems can be put into parallel composition to create a new open system via a _wiring_. We'll just do parallel composition of two systems, the general case is similar. Given two systems `A` and `B`, the wiring consists of functions:
- `I × O_A -> I_B` mapping general inputs and outputs of `A` into `B`'s inputs,
- `I × O_B -> I_A` mapping general inputs and outputs of `B` into `A`'s inputs,
- `O_A × O_B × O` mapping `A`'s and `B`'s outputs to the general outputs.


## RSS example

In the case of RSS single-lane-follow, the programs are:
```
constant ρ;

type Car = { x: R, v: R };

type CarControl = { a_lower: R, a_upper: R };

prog resp =
  wait d > dRSS + ε;
  upd  ρ * rand;
  wait state > 0;
  emit Trigger;
  wait dist < dRSS + 2ε;
  emit Untrigger;
  resp;
 where
  d    = abs(in.pov.x - in.sv.x)
  dRSS = rssDistance(in.pov.v, in.sv.v)

sys Resp =
  { phys   = R,
    cyber  = R,
    in     = { sv: Car, pov: Car },
    out    = Unit,
    outMap = unit,
    prog   = resp,
    dyn    = 1
  }

prog sv =
  wait Trigger;
  upd { a_lower = a_min, a_upper = a_min };
  wait Untrigger || state.v > 0;
  if state.v <= 0 
    then upd { a_lower = 0, a_upper = 0 };
         wait Untrigger;
         sv
    else sv

sys SV =
  { phys   = Car,
    cyber  = CarControl,
    in     = Unit,
    out    = Car,
    outMap = phys,
    prog   = sv,
    dyn    = { x = v, v in [cyber.a_lower, cyber.a_upper] }
  }

// TODO: this program doesn't guarantee min/max speeds for POV.
pov = wait true;

sys POV =
  { phys   = Car,
    cyber  = CarControl,
    in     = Unit,
    out    = Car,
    outMap = phys,
    prog   = pov,
    dyn    = { x = v, v in [cyber.a_lower, cyber.a_upper] }
  }

sys SingleLaneFollow =
  parallel{
    in  = Unit,
    out = Unit,
    components = {
      sv =
        { component = SV,
          input = unit
        },
      pov =
        { component = POV,
          input = unit,
        },
      resp =
        { component = Resp,
          input = { sv = sv.out,
                    pov = pov.out }
        }
    },
    outMap = unit
  }
```
