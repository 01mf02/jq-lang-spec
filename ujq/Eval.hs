module Eval where

import qualified Data.Map as Map
import Data.Map ((!))

import qualified Syn
import qualified Def
import qualified Val
import Val (ValueR, ValP(..), ValPE, Value, ok, newVal)
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

tryCatch :: (ValP v -> [ValPE v]) -> [ValPE v] -> [ValPE v]
tryCatch catch l = case l of
  [] -> []
  Left (Val.Error e) : _ -> catch $ newVal e
  y : tl -> y : tryCatch catch tl

label :: Int -> [ValPE v] -> [ValPE v]
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

recurse :: Value v => ValP v -> [ValPE v]
recurse vp = [ok vp] ++ app recurse (Val.idx vp (Val.Range Nothing Nothing) Def.Optional)

updatePath :: Value v => (v -> [ValueR v]) -> [v] -> v -> [ValueR v]
updatePath f [] v = f v
updatePath f (hd:tl) v = [Val.upd v hd (\x -> updatePath f tl x)]

updatePaths :: Value v => (v -> [ValueR v]) -> [ValPE v] -> v -> [ValueR v]
updatePaths _ [] v = [ok v]
updatePaths f (hd : tl) v = case hd of
  Right (ValP {path = Just p}) -> app (updatePaths f tl) (updatePath f (reverse p) v)
  Right (ValP {path = Nothing, val}) -> [Val.err $ "invalid path expression with result " ++ show val]
  Left e -> [Left e]

run :: Value v => Filter -> Ctx v -> ValP v -> [ValPE v]
run f c@Ctx{vars, lbls} vp@Val.ValP{val = v} = case f of
  Id -> [ok vp]
  Recurse -> recurse vp
  ToString -> [ok $ newVal $ Val.fromStr $ show v]
  Num n -> [ok $ newVal $ Val.fromNum n]
  Str s -> [ok $ newVal $ Val.fromStr s]
  Neg x -> [fmap newVal $ Val.neg (vars ! x)]
  BoolOp lx op rx -> [ok $ newVal $ Val.fromBool $ Syn.boolOp op (vars ! lx) (vars ! rx)]
  MathOp lx op rx -> [fmap newVal $ mathOp op (vars ! lx) (vars ! rx)]
  Arr0 -> [fmap newVal $ Val.arr []]
  Obj0 -> [ok $ newVal $ Val.obj0]
  ArrN f -> [fmap newVal $ Val.arr $ map (fmap val) $ run f c vp]
  Obj1 kx vx -> [fmap newVal $ Val.obj1 (vars ! kx) (vars ! vx)]
  Concat f g -> run f c vp ++ run g c vp
  Compose f g -> app (\y -> run g c y) $ run f c vp
  Bind f x g -> app (\y -> run g (bind x (val y) c) vp) $ run f c vp
  Alt f g -> case filter (either (const True) (Val.toBool . val)) (run f c vp) of {[] -> run g c vp; l -> l}
  Var x -> [ok $ newVal $ vars ! x]
  TryCatch f g -> tryCatch (run g c) $ run f c vp
  Label l f -> let li = Map.size lbls in label li $ run f (c {lbls = Map.insert l li lbls}) vp
  Break l -> [Left $ Val.Break (lbls ! l)]
  Ite x f g -> run (if Val.toBool $ vars ! x then f else g) c vp
  Reduce fx x f -> reduce (\xv -> run f (bind x (val xv) c)) (run fx c vp) vp
  Foreach fx x f g -> foreach (\xv -> run f (bind x (val xv) c)) (\xv -> run g (bind x (val xv) c)) (run fx c vp) vp
  Path part opt -> Val.idx vp (fmap ((!) vars) part) opt
  Update f g ->
    let paths = run f c (ValP {val = v, path = Just []}) in
    map (fmap newVal) $ updatePaths (map (fmap val) . run g c . newVal) paths v
  Def f_name arg_names rhs g ->
    let add = Map.insert (f_name, length arg_names) (Just arg_names, rhs, c) in
    run g (c {funs = add $ funs c}) vp
  App f_name args ->
    let sig = (f_name, length args) in
    let fun@(arg_names, rhs, c') = funs c ! sig in
    let funs' = maybe [] (\names -> (sig, fun) : zipWith (\name arg -> ((name, 0), (Nothing, arg, c))) names args) arg_names in
    run rhs (c' {funs = Map.fromList funs' `Map.union` funs c'}) vp
