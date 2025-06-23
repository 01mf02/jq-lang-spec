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

data ValP v = ValP {
  val :: v,
  path :: Maybe [v]
} deriving Show

newVal :: v -> ValP v
newVal val = ValP {val, path = Nothing}

type ValueR v = Either (Exn v) v
type ValPE v = Either (Exn v) (ValP v)

ok :: v -> Either e v
ok = Right

err :: Value v => String -> Either (Exn v) v'
err = Left . Error . fromStr

data Index i = Index i | Range (Maybe i) (Maybe i)
  deriving Show

instance Functor Index where
  fmap f (Index i)   = Index (f i)
  fmap f (Range l h) = Range (fmap f l) (fmap f h)

class (Eq a, Ord a, Show a) => Value a where
  toBool :: a -> Bool
  fromBool :: Bool -> a
  fromInt :: Int -> a
  fromNum :: String -> a
  fromStr :: String -> a

  arr :: [ValueR a] -> ValueR a
  obj0 :: a
  obj1 :: a -> a -> ValueR a

  idx :: ValP a -> Index a -> Opt -> [ValPE a]
  upd :: a -> a -> (a -> [ValueR a]) -> ValueR a

  add :: a -> a -> ValueR a
  sub :: a -> a -> ValueR a
  mul :: a -> a -> ValueR a
  div :: a -> a -> ValueR a
  rem :: a -> a -> ValueR a
  neg :: a -> ValueR a

instance Value Val where
  arr = fmap (Arr . Seq.fromList) . sequence
  obj0 = Val.Obj Map.empty
  obj1 k v = ok $ Val.Obj $ Map.singleton k v
  toBool v = case v of {Null -> False; Bool b -> b; _ -> True}
  fromBool = Bool
  fromInt = Num . fromIntegral
  fromNum = Num . read
  fromStr = Str

  idx (ValP {val, path}) index opt = case (val, index, opt) of
    (Arr a, Range Nothing Nothing, _) -> zipWith (\i val -> ok $ ValP {path = (fromInt i :) <$> path, val}) [0..] $ toList a
    (Arr a, Index (Num i), _) -> [ok $ ValP {path = (Num i :) <$> path, val = maybe Null id $ Seq.lookup (round i) a}]
    (Obj o, Index i, _) -> [ok $ ValP {path = (i:) <$> path, val = maybe Null id $ Map.lookup i o}]
    (v, i, Essential) -> [err $ "could not index " ++ show v ++ " with " ++ show i]
    (_, _, Optional) -> []

  upd (Arr a) (Num i) f = case Seq.lookup (round i) a of
    Nothing -> ok (Arr a)
    Just x -> case f x of
      hd : _ -> hd >>= \y -> ok $ Arr $ Seq.update (round i) y a
      [] -> ok $ Arr $ Seq.deleteAt (round i) a
  upd (Obj o) k f = case Map.lookup k o of
    Nothing -> ok (Obj o)
    Just x -> case f x of
      hd : _ -> hd >>= \y -> ok $ Obj $ Map.update (const $ Just y) k o
      [] -> ok $ Obj $ Map.update (const Nothing) k o
  upd v i _ = err $ "could not update " ++ show v ++ " at " ++ show i

  add Null v = ok v
  add v Null = ok v
  add (Num x) (Num y) = ok $ Num $ x + y
  add (Str x) (Str y) = ok $ Str $ x <> y
  add (Arr x) (Arr y) = ok $ Arr $ x <> y
  add (Obj x) (Obj y) = ok $ Obj $ y <> x
  add x y = err $ "could not add " ++ show x ++ " and " ++ show y

  neg (Num n) = ok $ Num $ -n
  neg v = err $ "could not negate " ++ show v
