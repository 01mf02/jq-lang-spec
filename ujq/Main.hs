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
  | Alt Filter Filter
  | Update Filter Filter
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
  | Path (Val.Index Var) Def.Opt
  deriving Show

freshBin :: Int -> Syn.Term -> Syn.Term -> (Var -> Var -> Filter) -> Filter
freshBin vs l r f = fresh vs l $ \ lx vs -> fresh vs r $ \rx _vs -> f lx rx

fresh :: Int -> Syn.Term -> (Var -> Int -> Filter) -> Filter
fresh vs tm f = let x = show vs in Bind (compile vs tm) x $ f x (vs + 1)

compilePath :: Var -> Int -> (Def.Part Syn.Term, Def.Opt) -> Filter
compilePath x vs (part, opt) = case part of
  Def.Index(i) -> fresh vs (app i) $ \i _vs -> Path (Val.Index i) opt
  Def.Range(l, r) -> case (app <$> toMaybe l, app <$> toMaybe r) of
    (Nothing, Nothing) -> range Nothing Nothing
    (Just l, Nothing) -> fresh vs l $ \l _vs -> range (Just l) Nothing
    (Nothing, Just r) -> fresh vs r $ \r _vs -> range Nothing (Just r)
    (Just l, Just r) -> fresh vs l $ \l vs -> fresh vs r $ \r _vs -> range (Just l) (Just r)
  where
    app tm = Syn.Pipe(Syn.Var(x), None, tm)
    range l r = Path (Val.Range l r) opt

compile :: Int -> Syn.Term -> Filter
compile vs f' = case f' of
  Syn.Id -> Id
  Syn.Recurse -> Recurse
  Syn.Num n -> Num n
  Syn.Str(_, []) -> Str ""
  Syn.Str(_, [Def.Str s]) -> Str s
  Syn.Str(_, [Def.Char c]) -> Str [c]
  Syn.Str(f, [Def.Term t]) -> Compose (compile vs t) (maybe ToString (\f -> App f []) $ toMaybe f)
  Syn.Str(f, hd : tl) -> compile vs $ Syn.BinOp(Syn.Str(f, [hd]), Syn.Math(Syn.Add), Syn.Str(f, tl))
  Syn.Arr(None) -> Arr0
  Syn.Arr(Some(a)) -> ArrN (compile vs a)
  Syn.Obj([]) -> Obj0
  Syn.Obj([(k, v)]) ->
    let index i = Syn.Path(Syn.Id, Def.Path([(Def.Index i, Def.Essential)])) in
    freshBin vs k (case v of {Some(v) -> v; None -> index k}) Obj1
  Syn.Obj(kv : tl) -> compile vs $ Syn.BinOp(Syn.Obj([kv]), Syn.Math(Syn.Add), Syn.Obj(tl))
  Syn.Var(x) -> Var(x)
  Syn.Neg(f) -> let x = show vs in Bind (compile vs f) x $ Neg x
  Syn.BinOp(l, Syn.Comma, r) -> Concat (compile vs l) (compile vs r)
  Syn.BinOp(l, Syn.Alt, r) -> Alt (compile vs l) (compile vs r)
  Syn.BinOp(l, Syn.And, r) -> compile vs $ Syn.IfThenElse([(l, Syn.Pipe(r, None, Syn.bool))], Some(Syn.false))
  Syn.BinOp(l, Syn.Or,  r) -> compile vs $ Syn.IfThenElse([(l, Syn.true)], Some(Syn.Pipe(r, None, Syn.bool)))
  Syn.BinOp(l, Syn.Cmp (op), r) -> freshBin vs l r (\l r -> BoolOp l op r)
  Syn.BinOp(l, Syn.Math(op), r) -> freshBin vs l r (\l r -> MathOp l op r)
  -- f |= g
  Syn.BinOp(f, Syn.Update, g) -> Update (compile vs f) (compile vs g)
  -- f = g
  Syn.BinOp(f, Syn.Assign, g) -> fresh vs g $ \x' vs -> compile vs $
    Syn.BinOp(f, Syn.Update, Syn.Var(x'))
  -- f += g, f -= g, ...
  Syn.BinOp(f, Syn.UpdateMath(op), g) -> fresh vs g $ \x' vs -> compile vs $
    Syn.BinOp(f, Syn.Update, Syn.BinOp(Syn.Id, Syn.Math(op), Syn.Var(x')))
  -- f //= g
  Syn.BinOp(f, Syn.UpdateAlt, g) -> compile vs $ Syn.BinOp(f, Syn.Update, Syn.BinOp(Syn.Id, Syn.Alt, g))
  Syn.Pipe(l, None, r) -> Compose (compile vs l) (compile vs r)
  Syn.Pipe(l, Some(Def.Var(v)), r) -> Bind (compile vs l) v (compile vs r)
  -- $x as [p1, ..., pn] | g
  Syn.Pipe(Syn.Var(x), Some(Def.Arr(p)), g) -> compile vs $
    Syn.Pipe(Syn.Var(x), Some(Def.Obj(zipWith (\i pi -> (Syn.Num(show i), pi)) [0..] p)), g)
  -- $x as {f1: p1, ...tl} | g
  Syn.Pipe(Syn.Var(x), Some(Def.Obj((f1, p1) : tl)), g) ->
    fresh vs (Syn.Path(Syn.Var(x), Def.Path([(Def.Index(f1), Def.Essential)]))) $
    \x' vs -> compile vs $ Syn.Pipe(Syn.Var(x'), Some(p1), Syn.Pipe(Syn.Var(x), Some(Def.Obj(tl)), g))
  -- $x as {} | g
  Syn.Pipe(Syn.Var(_), Some(Def.Obj([])), g) -> compile vs g
  -- f as p | g
  Syn.Pipe(f, p@(Some(_)), g) -> fresh vs f $ \x' vs -> compile vs $ Syn.Pipe(Syn.Var(x'), p, g)
  Syn.IfThenElse((if_, then_) : tl, else_) -> fresh vs if_ $
    \x vs -> Ite x (compile vs then_) (compile vs $ Syn.IfThenElse(tl, else_))
  Syn.IfThenElse([], else_) -> maybe Id (compile vs) $ toMaybe else_
  -- try f catch g
  Syn.TryCatch(f, g) -> TryCatch (compile vs f) $ maybe empty (compile vs) $ toMaybe g where
    -- [][] as $x | .
    empty = Bind (Arr0 `Compose` Path (Val.Range Nothing Nothing) Def.Essential) "" Id
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
  Syn.Path(head, Def.Path(path)) -> fresh vs Syn.Id $
    \x' vs -> foldl (\acc -> Compose acc . compilePath x' vs) (compile vs head) path
  Syn.Def(defs, t) -> foldr (\ (name, args, rhs) -> Def name args (compile vs rhs)) (compile vs t) defs
  Syn.Call(name, args) -> App name $ map (compile vs) args

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
