module Law.Check where

import Law.Expr

data Err = Err

type Check = Either Err

checkModule :: Module -> Check ()
checkModule mod = traverse_ checkDef mod
  where
    checkDef :: Def -> Check ()
    checkDef (DefOb name o) = _
    checkDef (DefOb )
