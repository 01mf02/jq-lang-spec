module IR where

import qualified Syn
import qualified Def
import Def (Option(None, Some), toMaybe)
import qualified Val

type Var = String

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
  -- {}
  Syn.Obj([]) -> Obj0
  -- {k: v}
  Syn.Obj([(k, v)]) ->
    let index i = Syn.Path(Syn.Id, Def.Path([(Def.Index i, Def.Essential)])) in
    freshBin vs k (case v of {Some(v) -> v; None -> index k}) Obj1
  Syn.Obj(kv : tl) -> compile vs $ Syn.BinOp(Syn.Obj([kv]), Syn.Math(Syn.Add), Syn.Obj(tl))
  -- $x
  Syn.Var(x) -> Var(x)
  -- -f
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
  Syn.Fold(typ, fx, p, init : tl) | not $ Def.isVarPattern p ->
    let pvs = Def.patternVars p in
    let serPat = case map Syn.Var pvs of {[] -> None; hd : tl -> Some $ foldl (\acc x -> Syn.BinOp(acc, Syn.Comma, x)) hd tl} in
    let deserTm = Def.Arr(map Def.Var pvs) in
    let x' = show vs in
    let ser tm = Syn.Pipe(tm, Some(p), Syn.Arr(serPat)) in
    let deser tm = Syn.Pipe(Syn.Var(x'), Some(deserTm), tm) in
    compile (vs + 1) $ Syn.Fold(typ, ser fx, Def.Var(x'), init : map deser tl)
  Syn.Fold(_, _, _, _) -> error "unknown folding operation"
  Syn.Path(head, Def.Path(path)) -> fresh vs Syn.Id $
    \x' vs -> foldl (\acc -> Compose acc . compilePath x' vs) (compile vs head) path
  Syn.Def(defs, t) -> foldr (\ (name, args, rhs) -> Def name args (compile vs rhs)) (compile vs t) defs
  Syn.Call(name, args) -> App name $ map (compile vs) args
