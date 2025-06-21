module Val where

import qualified Data.Map as Map
import qualified Data.Sequence as Seq
import Data.Foldable (toList)
--import Text.Read (readMaybe)

import Def (Opt(Optional, Essential))

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

data Index i = Index i | Range (Maybe i) (Maybe i)
  deriving Show

instance Functor Index where
  fmap f (Index i)   = Index (f i)
  fmap f (Range l h) = Range (fmap f l) (fmap f h)

class (Eq a, Ord a, Show a) => Value a where
  toBool :: a -> Bool
  fromBool :: Bool -> a
  fromNum :: String -> a
  fromStr :: String -> a

  arr :: [ValueR a] -> ValueR a
  obj0 :: a
  obj1 :: a -> a -> ValueR a

  index :: a -> Index a -> Opt -> [ValueR a]

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

  index (Arr a) (Range Nothing Nothing) _ = fmap ok $ toList a
  index (Arr a) (Index (Num i)) _ = [ok $ maybe Null id $ Seq.lookup (round i) a]
  index (Obj o) (Index i) _ = [ok $ maybe Null id $ Map.lookup i o]
  index v i Essential = [err $ "could not index " ++ show v ++ " with " ++ show i]
  index _ _ Optional = []

  add Null v = ok v
  add v Null = ok v
  add (Num x) (Num y) = ok $ Num $ x + y
  add (Str x) (Str y) = ok $ Str $ x <> y
  add (Arr x) (Arr y) = ok $ Arr $ x <> y
  add (Obj x) (Obj y) = ok $ Obj $ y <> x
  add x y = err $ "could not add " ++ show x ++ " and " ++ show y

  neg (Num n) = ok $ Num $ -n
  neg v = err $ "could not negate " ++ show v
