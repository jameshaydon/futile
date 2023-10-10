# Draft 2

```
sketch Nat = {};

sketch Elem = { Elem }

sketch List = {
  include Elem;
  List,
  length : Elem -> Nat
}
```

```
length = 
```

I think it is best to use a colimit approach for combining theories/sketches, as
in the Barr Wells book. However, i still think we need the
"interpretation/algebra" for the recursive functions?

---

```
BoolS := sketch { Bool, not }

Bool := interp BoolS {
  Bool = ..
  not = ..
} 

NatS := sketch { Nat, plus }

NatI := rec interp NatS {
  Nat = colim{..},
  plus = ..
}

Elem := sketch { Elem }

ListS := sketch
  { use Elem;
    List,
    concat : (List, List) -> List,
    unwrap : List -> colim{ empty = lim{}, cons = lim{ head = Elem, tail = List} }
  }

ListI : Th(List) -> Th(Elem)
ListI = 
  { Elem = Elem
    List = colim{..},
    concat = @1 cocone{..} }

ProgS :=
  sketch {
    use Bool = BoolS;
    use ElemInt = Elem;
    use ListInt = ListS;
    use Nat = NatS;
    use ElemInt -> ListInt = Elem;
    use ElemInt -> Nat     = { Elem = Nat };
    sum : ListInt.List -> Nat.Nat
  }

Main = interp ProgS {
  sum = unwrap cocone{ empty = zero.,
                       cons  = (.head, .tail sum) plus }
}

MapIn = sketch { A, B, f : A -> B }

MapOut = sketch{
  use ListA = ListS;
  use A = Elem;
  use ListB = ListS;
  use B = Elem;
  use MapIn = MapIn;
  use A -> ListA = Elem;
  use B -> ListB = Elem;
  use A -> MapIn = { Elem = A };
  use B -> MapIn = { Elem = B };
  map : ListA.List -> ListB.List
}

Th(MapOut) -> Th(MapIn)

{ use list { Elem = A } on ListA;
  use list { Elem = B } on ListB;
  use { Elem = A } on A;
  use { Elem = B } on B;
  use . on MapIn;
  map = unwrap cocone{ ... }
}
```

