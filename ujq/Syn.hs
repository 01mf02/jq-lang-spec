module Syn where

import qualified Def
import Def (Option(None, Some))

data Term =
    Id
  | Recurse
  | Num String
  | Str(Option String, [StrPart])
  | Arr(Option Term)
  | Obj([(Term, Option Term)])
  | Neg(Term)
  | Pipe(Term, Option Pattern, Term)
  | BinOp(Term, BinaryOp, Term)
  | Label(String, Term)
  | Break(String)
  | Fold(String, Term, Pattern, [Term])
  | TryCatch(Term, Option Term)
  | IfThenElse([(Term, Term)], Option Term)
  | Def([(String, [String], Term)], Term)
  | Call(String, [Term])
  | Var(String)
  | Path(Term, Def.Path Term)
  deriving (Read, Show)

true, false, bool :: Term
true  = BinOp(Arr(None), Cmp(Eq), Arr(None))
false = BinOp(Arr(None), Cmp(Ne), Arr(None))
bool = IfThenElse([(Id, true)], Some(false))

type StrPart = Def.StrPart Term
type Pattern = Def.Pattern Term

data BinaryOp =
    Comma
  | Alt
  | Or
  | And
  | Assign
  | Update
  | UpdateAlt
  | UpdateMath(MathOp)
  | Math(MathOp)
  | Cmp(BoolOp)
  deriving (Read, Show)
 
data MathOp = Add | Sub | Mul | Div | Rem
  deriving (Read, Show)

data BoolOp = Eq | Ne | Lt | Le | Gt | Ge
  deriving (Read, Show)

boolOp :: Ord a => BoolOp -> a -> a -> Bool
boolOp op = case op of
  Eq -> (==)
  Ne -> (/=)
  Lt -> (<)
  Le -> (<=)
  Gt -> (>)
  Ge -> (>=)
