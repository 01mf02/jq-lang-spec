module Val where

import qualified Data.Map as Map
import qualified Data.Sequence as Seq
import Text.Read (readMaybe)

data Val = Null
  | Bool Bool
  | Num Float
  | Str String
  | Arr (Seq.Seq Val)
  | Obj (Map.Map Val Val)
  deriving (Show, Eq, Ord)

data Exn v = Error v | Break Int
  deriving Show
type ValueR v = Either (Exn v) v

ok :: v -> ValueR v
ok = Right

err :: Value v => String -> ValueR v
err = Left . Error . fromStr

class (Eq a, Ord a) => Value a where
  toBool :: a -> Bool
  fromBool :: Bool -> a
  fromNum :: String -> a
  fromStr :: String -> a

  arr :: [ValueR a] -> ValueR a
  obj0 :: a
  obj1 :: a -> a -> ValueR a

  add :: a -> a -> ValueR a
  sub :: a -> a -> ValueR a
  mul :: a -> a -> ValueR a
  div :: a -> a -> ValueR a
  rem :: a -> a -> ValueR a
  neg :: a -> ValueR a

instance Value Val where
  arr = fmap (Arr . Seq.fromList) . sequence
  obj0 = Val.Obj $ Map.empty
  obj1 k v = ok $ Val.Obj $ Map.singleton k v
  toBool v = case v of {Null -> False; Bool b -> b; _ -> True}
  fromBool = Bool
  fromNum n = Num $ read n
  fromStr = Str

  add Null v = ok v
  add v Null = ok v
  add (Num x) (Num y) = ok $ Num $ x + y
  add (Str x) (Str y) = ok $ Str $ x <> y
  add (Arr x) (Arr y) = ok $ Arr $ x <> y
  add (Obj x) (Obj y) = ok $ Obj $ y <> x
  add x y = err $ "could not add " ++ show x ++ " and " ++ show y

  neg (Num n) = ok $ Num $ -n
  neg v = err $ "could not negate " ++ show v
