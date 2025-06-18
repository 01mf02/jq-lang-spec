module Def where

data Option a = None | Some(a)
  deriving (Read, Show)

toMaybe :: Option a -> Maybe a
toMaybe None = Nothing
toMaybe (Some(x)) = Just x

data StrPart tm = Str(String) | Term(tm) | Char(Char)
  deriving (Read, Show)

data Pattern tm = Var(String) | Arr([Pattern tm]) | Obj([(tm, Pattern tm)])
  deriving (Read, Show)

data Path f = Path([(Part f, Opt)])
  deriving (Read, Show)

data Part i = Index(i) | Range(Option i, Option i)
  deriving (Read, Show)

data Opt = Optional | Essential
  deriving (Read, Show)
