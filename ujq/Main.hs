import qualified Data.Map as Map
import Data.Map ((!))
--import Debug.Trace

import qualified Syn
import qualified Def
import Def (Option(None, Some), toMaybe)
import qualified Val
import Val (ValueR, Value, ok)

type Var = String
type Arg = String

data Filter = Id
  | Recurse
  | ToString
  | Num String
  | Str String
  | Arr0
  | Obj0
  | ArrN Filter
  | Obj1 Var Var
  | Neg Var
  | BoolOp Var Syn.BoolOp Var
  | MathOp Var Syn.MathOp Var
  | Concat Filter Filter
  | Compose Filter Filter
  | Bind Filter Var Filter
  | Label String Filter
  | Break String
  | Var Var
  | Ite Var Filter Filter
  | TryCatch Filter Filter
  | Reduce Filter Var Filter
  | Foreach Filter Var Filter Filter
  | Def String [String] Filter Filter
  | App String [Filter]
  deriving Show

freshBin :: Int -> Syn.Term -> Syn.Term -> (Var -> Var -> Filter) -> Filter
freshBin vs l r f =
  let (lx, rx) = (show vs, show $ vs + 1) in
  Bind (compile vs l) lx $ Bind (compile (vs + 1) r) rx $ f lx rx

fresh :: Int -> Syn.Term -> (Var -> Int -> Filter) -> Filter
fresh vs tm f = let x = show vs in Bind (compile vs tm) x $ f x (vs + 1)

compile :: Int -> Syn.Term -> Filter
compile vs f' = case f' of
  Syn.Id -> Id
  Syn.Recurse -> Recurse
  Syn.Num n -> Num n
  Syn.Str(None, [Def.Str s]) -> Str s
  Syn.Arr(None) -> Arr0
  Syn.Arr(Some(a)) -> ArrN (compile vs a)
  Syn.Obj([]) -> Obj0
  Syn.Obj([(k, Some(v))]) -> freshBin vs k v Obj1
  Syn.Var(x) -> Var(x)
  Syn.Neg(f) -> let x = show vs in Bind (compile vs f) x $ Neg x
  Syn.BinOp(l, Syn.Comma, r) -> Concat (compile vs l) (compile vs r)
  Syn.BinOp(l, Syn.Cmp (op), r) -> freshBin vs l r (\l r -> BoolOp l op r)
  Syn.BinOp(l, Syn.Math(op), r) -> freshBin vs l r (\l r -> MathOp l op r)
  Syn.Pipe(l, None, r) -> Compose (compile vs l) (compile vs r)
  Syn.Pipe(l, Some(Def.Var(v)), r) -> Bind (compile vs l) v (compile vs r)
  Syn.IfThenElse((if_, then_) : tl, else_) -> fresh vs if_ $
    \x vs -> Ite x (compile vs then_) (compile vs $ Syn.IfThenElse(tl, else_))
  Syn.IfThenElse([], else_) -> maybe Id (compile vs) $ toMaybe else_
  Syn.TryCatch(try, Some(catch)) -> TryCatch (compile vs try) (compile vs catch)
  Syn.Label(l, f) -> Label l (compile vs f)
  Syn.Break(l) -> Break l
  Syn.Fold("reduce", xs, Def.Var(x), [init, update]) -> fresh vs Syn.Id $
    \x' vs -> Compose (compile vs init) $
      Reduce  (Var x' `Compose` compile vs xs) x (compile vs update)
  Syn.Fold("foreach", xs, Def.Var(x), [init, update, project]) -> fresh vs Syn.Id $
    \x' vs -> Compose (compile vs init) $
      Foreach (Var x' `Compose` compile vs xs) x (compile vs update) (compile vs project)
  Syn.Fold("foreach", xs, x, [init, update]) -> compile vs $
    Syn.Fold("foreach", xs, x, [init, update, Syn.Id])
  Syn.Def(defs, t) -> foldr (\ (name, args, rhs) -> Def name args (compile vs rhs)) (compile vs t) defs
  Syn.Call(name, args) -> App name (map (compile vs) args)

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

run :: Value v => Filter -> Ctx v -> v -> [ValueR v]
run f' c@Ctx{vars, lbls} v = case f' of
  Id -> [ok v]
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
  Var x -> [ok $ vars ! x]
  TryCatch f g -> tryCatch (\e -> run g c e) $ run f c v
  Label l f -> let li = Map.size lbls in label li $ run f (c {lbls = Map.insert l li lbls}) v
  Break l -> [Left $ Val.Break (lbls ! l)]
  Ite x f g -> run (if Val.toBool $ vars ! x then f else g) c v
  Reduce fx x f -> reduce (\xv -> run f (bind x xv c)) (run fx c v) v
  Foreach fx x f g -> foreach (\xv -> run f (bind x xv c)) (\xv -> run g (bind x xv c)) (run fx c v) v
  Def f_name arg_names rhs g ->
    let add = Map.insert (f_name, length arg_names) (Just arg_names, rhs, c) in
    run g (c {funs = add $ funs c}) v
  App f_name args ->
    let sig = (f_name, length args) in
    let fun@(arg_names, rhs, c') = funs c ! sig in
    let funs' = maybe [] (\names -> (sig, fun) : zipWith (\name arg -> ((name, 0), (Nothing, arg, c))) names args) arg_names in
    run rhs (c' {funs = Map.fromList funs' `Map.union` funs c'}) v

main :: IO ()
main = do
  stdin <- getContents
  print stdin
  let tm = read stdin :: Syn.Term
  print tm
  let f = compile 0 tm
  let c = Ctx {vars = Map.empty, funs = Map.empty, lbls = Map.empty} 
  let v = Val.Null
  print f
  print $ run f c v
