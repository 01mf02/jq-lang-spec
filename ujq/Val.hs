module Val where

import qualified Data.Map as Map
import qualified Data.Sequence as Seq
import qualified Data.List as List
import Data.Foldable (toList)
--import Text.Read (readMaybe)

import Def (Opt(Optional, Essential))

data Val =
    Null
  | Bool Bool
  | Num Float
  | Str String
  | Arr (Seq.Seq Val)
  | Obj (Map.Map Val Val)
  deriving (Eq, Ord)

instance Show Val where
  show Null = "null"
  show (Bool False) = "false"
  show (Bool True ) = "true"
  show (Num n) | n == fromInteger (round n) = show $ round n
  show (Num n) = show n
  show (Str s) = show s
  show (Arr a) = "[" ++ (List.intercalate "," $ map show $ toList a) ++ "]"
  show (Obj o) = "{" ++ (List.intercalate "," $ map (\(k, v) -> show k ++ ":" ++ show v) $ Map.toList o) ++ "}"

data Exn v = Error v | Break Int
  deriving Show

data ValP v = ValP {
  val :: v,
  path :: Maybe [v]
} deriving Show

newVal :: v -> ValP v
newVal val = ValP {val, path = Nothing}

type ValR v = Either (Exn v) v
type ValPR v = Either (Exn v) (ValP v)

ok :: v -> Either e v
ok = Right

err :: Value v => String -> Either (Exn v) v'
err = Left . Error . fromStr

data Index i = Index i | Range (Maybe i) (Maybe i)
  deriving Show

instance Foldable Index where
  foldMap f (Index i)   = f i
  foldMap f (Range l h) = foldMap f l <> foldMap f h

instance Functor Index where
  fmap f (Index i)   = Index (f i)
  fmap f (Range l h) = Range (fmap f l) (fmap f h)

class (Eq a, Ord a, Show a) => Value a where
  toBool :: a -> Bool
  fromBool :: Bool -> a
  fromInt :: Int -> a
  fromNum :: String -> a
  fromStr :: String -> a

  arr :: [ValR a] -> ValR a
  obj0 :: a
  obj1 :: a -> a -> ValR a

  idx :: ValP a -> Index a -> Opt -> [ValPR a]
  upd ::      a -> Index a -> Opt -> (a -> [ValR a]) -> ValR a

  add :: a -> a -> ValR a
  sub :: a -> a -> ValR a
  mul :: a -> a -> ValR a
  div :: a -> a -> ValR a
  rem :: a -> a -> ValR a
  neg :: a -> ValR a

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
    (Obj o, Range Nothing Nothing, _) -> map (\(k, val) -> ok $ ValP {path = (k:) <$> path, val}) $ Map.toList o
    (Obj o, Index i, _) -> [ok $ ValP {path = (i:) <$> path, val = maybe Null id $ Map.lookup i o}]
    (v, i, Essential) -> [err $ "could not index " ++ show v ++ " with " ++ show i]
    (_, _, Optional) -> []

  upd (Arr a) (Index (Num i)) opt f = case Seq.lookup (round i) a of
    Nothing -> case opt of
      Optional -> ok (Arr a)
      Essential -> error "todo"
    Just x -> case f x of
      hd : _ -> hd >>= \y -> ok $ Arr $ Seq.update (round i) y a
      [] -> ok $ Arr $ Seq.deleteAt (round i) a
  upd (Arr a) (Range Nothing Nothing) _ f = arr $ toList a >>= f
  upd (Obj o) (Index k) _ f = case Map.lookup k o of
    Nothing -> ok (Obj o)
    Just x -> case f x of
      hd : _ -> hd >>= \y -> ok $ Obj $ Map.update (const $ Just y) k o
      [] -> ok $ Obj $ Map.update (const Nothing) k o
  upd (Obj o) (Range Nothing Nothing) _ f =
    fmap (Obj . Map.fromList) $ sequence $
    concatMap (\(k, v) -> map(fmap ((k,))) $ take 1 $ f v) $
    Map.toList o
  upd v i _ _ = err $ "could not update " ++ show v ++ " at " ++ show i

  add Null v = ok v
  add v Null = ok v
  add (Num x) (Num y) = ok $ Num $ x + y
  add (Str x) (Str y) = ok $ Str $ x <> y
  add (Arr x) (Arr y) = ok $ Arr $ x <> y
  add (Obj x) (Obj y) = ok $ Obj $ y <> x
  add x y = err $ "could not add " ++ show x ++ " and " ++ show y

  mul (Num x) (Num y) = ok $ Num $ x * y
  mul (Num x) (Str y) = ok $ Str $ mconcat $ replicate (floor x) y
  mul (Str x) (Num y) = mul (Num y) (Str x)
  mul x y = err $ "could not multiply " ++ show x ++ " and " ++ show y

  sub (Num x) (Num y) = ok $ Num $ x - y
  sub x y = err $ "could not subtract " ++ show x ++ " and " ++ show y

  div (Num x) (Num y) = ok $ Num $ x / y
  div x y = err $ "could not divide " ++ show x ++ " and " ++ show y

  rem (Num x) (Num y) = ok $ Num $ fromIntegral $ (floor x) `Prelude.rem` (floor y)
  rem x y = err $ "could not calculate remainder of " ++ show x ++ " and " ++ show y

  neg (Num n) = ok $ Num $ -n
  neg v = err $ "could not negate " ++ show v
