module Eval where

import qualified Data.Map as Map
import Data.Map ((!))

import qualified Syn
import qualified Def
import qualified Val
import Val (ValueR, Value, ok)
import IR

type Arg = String

data Ctx v = Ctx {
  vars :: Map.Map Var v,
  funs :: Map.Map (String, Int) (Maybe [Arg], Filter, Ctx v),
  lbls :: Map.Map String Int
} deriving Show

mathOp :: Value a => Syn.MathOp -> a -> a -> ValueR a
mathOp op = case op of
  Syn.Add -> Val.add
  Syn.Sub -> Val.sub
  Syn.Mul -> Val.mul
  Syn.Div -> Val.div
  Syn.Rem -> Val.rem

app :: (x -> [Either e y]) -> [Either e x] -> [Either e y]
app f = mconcat . map (\r -> case r of {Left e -> [Left e]; Right y -> f y})

tryCatch :: (v -> [ValueR v]) -> [ValueR v] -> [ValueR v]
tryCatch catch l = case l of
  [] -> []
  Left (Val.Error e) : _ -> catch e
  y : tl -> y : tryCatch catch tl

label :: Int -> [ValueR v] -> [ValueR v]
label lbl = takeWhile $ \r -> case r of
  Left (Val.Break lbl') | lbl == lbl' -> False
  _ -> True

fold :: (x -> y -> [Either e y]) -> (x -> y -> [Either e y]) -> (y -> [Either e y]) -> [Either e x] -> y -> [Either e y]
fold f g n xs acc = case xs of
  [] -> n acc
  Right x : tl -> app (\y -> g x y ++ fold f g n tl y) $ f x acc
  Left e : _ -> [Left e]

reduce :: (x -> y -> [Either e y]) -> [Either e x] -> y -> [Either e y]
reduce update = fold update (\_x _y -> []) (\y -> [Right y])

foreach :: (x -> y -> [Either e y]) -> (x -> y -> [Either e y]) -> [Either e x] -> y -> [Either e y]
foreach update init = fold update init (\_y -> [])

bind :: Var -> v -> Ctx v -> Ctx v
bind x v c@Ctx{vars} = c {vars = Map.insert x v vars}

recurse :: Value v => v -> [ValueR v]
recurse v = [ok v] ++ app recurse (Val.index v (Val.Range Nothing Nothing) Def.Optional)

run :: Value v => Filter -> Ctx v -> v -> [ValueR v]
run f' c@Ctx{vars, lbls} v = case f' of
  Id -> [ok v]
  Recurse -> recurse v
  ToString -> [ok $ Val.fromStr $ show v]
  Num n -> [ok $ Val.fromNum n]
  Str s -> [ok $ Val.fromStr s]
  Neg x -> [Val.neg (vars ! x)]
  BoolOp lx op rx -> [ok $ Val.fromBool $ Syn.boolOp op (vars ! lx) (vars ! rx)]
  MathOp lx op rx -> [mathOp op (vars ! lx) (vars ! rx)]
  Arr0 -> [Val.arr []]
  Obj0 -> [ok $ Val.obj0]
  ArrN f -> [Val.arr $ run f c v]
  Obj1 kx vx -> [Val.obj1 (vars ! kx) (vars ! vx)]
  Concat f g -> run f c v ++ run g c v
  Compose f g -> app (\y -> run g c y) $ run f c v
  Bind f x g -> app (\y -> run g (bind x y c) v) $ run f c v
  Alt f g -> case filter (either (const True) Val.toBool) (run f c v) of {[] -> run g c v; l -> l}
  Var x -> [ok $ vars ! x]
  TryCatch f g -> tryCatch (\e -> run g c e) $ run f c v
  Label l f -> let li = Map.size lbls in label li $ run f (c {lbls = Map.insert l li lbls}) v
  Break l -> [Left $ Val.Break (lbls ! l)]
  Ite x f g -> run (if Val.toBool $ vars ! x then f else g) c v
  Reduce fx x f -> reduce (\xv -> run f (bind x xv c)) (run fx c v) v
  Foreach fx x f g -> foreach (\xv -> run f (bind x xv c)) (\xv -> run g (bind x xv c)) (run fx c v) v
  Path part opt -> Val.index v (fmap ((!) vars) part) opt
  Def f_name arg_names rhs g ->
    let add = Map.insert (f_name, length arg_names) (Just arg_names, rhs, c) in
    run g (c {funs = add $ funs c}) v
  App f_name args ->
    let sig = (f_name, length args) in
    let fun@(arg_names, rhs, c') = funs c ! sig in
    let funs' = maybe [] (\names -> (sig, fun) : zipWith (\name arg -> ((name, 0), (Nothing, arg, c))) names args) arg_names in
    run rhs (c' {funs = Map.fromList funs' `Map.union` funs c'}) v
