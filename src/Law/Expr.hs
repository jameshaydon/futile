module Law.Expr () where

import Law.Core

type Mapping a b = [(a, b)]

data Niche a = a :-> a

data Sketch ob ar pf = Sketch
  { obs :: Mapping Lbl ob,
    ars :: Mapping (Lbl, Niche Lbl) ar,
    pfs :: Mapping ([Lbl], [Lbl]) pf
  }

data Ar
  = Named Name
  | Comp [Ar]
  | Proj Sign Lbl
  | Cone Sign [(Lbl, Ar)]
  deriving stock (Eq, Ord, Show)

newtype Ob
  = ObNamed Name
  | ObLim Lim

data Lim = Lim
  { sign :: Sign,
    obs :: [(Lbl, Ob)],
    ars :: [(Lbl, Lbl, Lbl, Ar)]
  }

data Quiv = Quiv
  { obs :: [Name],
    ars :: [(Name, Name, Name)]
  }

data FinFunc = FinFunc
  { obs :: [(Name, Ob)],
    ars :: [(Name, Ar)]
  }

loop :: Quiv
loop =
  Quiv
    { obs = ["*"],
      ars = [("*", "endo", "*")]
    }

twice :: FinFunc
twice =
  FinFunc
    { obs = [("*", ObNamed "*")],
      ars = [("endo", Comp [Named "endo", Named "endo"])]
    }
