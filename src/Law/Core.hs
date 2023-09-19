module Law.Core where

type Name = Text

data Sign = Neg | Pos
  deriving stock (Eq, Ord, Show)

data Lbl = LblPos Int | LblName Name
  deriving stock (Eq, Ord, Show)

instance IsString Lbl where
  fromString = LblName . toText
