module Eval where

import qualified Data.Map as Map
import Data.Map ((!))

import qualified Syn
import qualified Def
import qualified Val
import Val (ValueR, ValP(..), ValPE, Value, ok, err, newVal)
import IR

type Arg = String

-- Named filter, such as `length`, `x`, or `has($k)`
data Named v =
    -- filter argument, such as `x` on the RHS of `def f(x): x`
    Arg Filter (Ctx v)
    -- defined filter, such as `f(0)` in `def f(x): ...; f(0)`
  | Def [Arg] Filter (Ctx v)
    -- builtin function, such as `length`
  | Fun (Builtin v)

type Builtin v = [Filter] -> Ctx v -> ValP v -> [ValPE v]

data Ctx v = Ctx {
  vars :: Map.Map Var v,
  funs :: Map.Map (String, Int) (Named v),
  lbls :: Map.Map String Int
}

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

{-
updatePath :: Value v => (v -> [ValueR v]) -> [v] -> v -> [ValueR v]
updatePath f [] v = f v
updatePath f (hd:tl) v = [Val.upd v hd (\x -> updatePath f tl x)]

updatePaths :: Value v => (v -> [ValueR v]) -> [ValPE v] -> v -> [ValueR v]
updatePaths _ [] v = [ok v]
updatePaths f (hd : tl) v = case hd of
  Right (ValP {path = Just p}) -> app (updatePaths f tl) (updatePath f (reverse p) v)
  Right (ValP {path = Nothing, val}) -> [Val.err $ "invalid path expression with result " ++ show val]
  Left e -> [Left e]
-}

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
  IR.Var x -> [ok $ newVal $ vars ! x]
  TryCatch f g -> tryCatch (run g c) $ run f c vp
  Label l f -> let li = Map.size lbls in label li $ run f (c {lbls = Map.insert l li lbls}) vp
  Break l -> [Left $ Val.Break (lbls ! l)]
  Ite x f g -> run (if Val.toBool $ vars ! x then f else g) c vp
  Reduce fx x f -> reduce (\xv -> run f (bind x (val xv) c)) (run fx c vp) vp
  Foreach fx x f g -> foreach (\xv -> run f (bind x (val xv) c)) (\xv -> run g (bind x (val xv) c)) (run fx c vp) vp
  Path part opt -> Val.idx vp (fmap ((!) vars) part) opt
  Update f g -> map (fmap newVal) $ upd f c (map (fmap val) . run g c . newVal) v
    --let paths = run f c (ValP {val = v, path = Just []}) in
    --map (fmap newVal) $ updatePaths (map (fmap val) . run g c . newVal) paths v
  IR.Def f_name arg_names rhs g ->
    let add = Map.insert (f_name, length arg_names) (Eval.Def arg_names rhs c) in
    run g (c {funs = add $ funs c}) vp
  App f_name args -> case maybe err id $ Map.lookup sig $ funs c of
    Fun f -> f args c vp
    Arg rhs c' -> run rhs c' vp
    fun@(Eval.Def arg_names rhs c') ->
      let funs' = (sig, fun) : zipWith (\name arg -> ((name, 0), (Arg arg c))) arg_names args in
      run rhs (c' {funs = Map.fromList funs' `Map.union` funs c'}) vp
    where
     sig = (f_name, length args)
     err = error $ "undefined function: " ++ f_name ++ "/" ++ show (length args)

upd :: Value v => Filter -> Ctx v -> (v -> [ValueR v]) -> v -> [ValueR v]
upd phi c@Ctx{vars, lbls} sigma v = case phi of
  Id -> sigma v
  Compose f g -> upd f c (upd g c sigma) v
  Concat f g -> app (upd g c sigma) $ upd f c sigma v
  Bind f x g -> reduce (\y -> upd g (bind x (val y) c) sigma) (run f c (newVal v)) v
  Break l -> [Left $ Val.Break (lbls ! l)]
  Ite x f g -> upd (if Val.toBool $ vars ! x then f else g) c sigma v
  Path part opt -> [Val.upd v (fmap ((!) vars) part) opt sigma]
  IR.Def f_name arg_names rhs g ->
    let add = Map.insert (f_name, length arg_names) (Eval.Def arg_names rhs c) in
    upd g (c {funs = add $ funs c}) sigma v
  App f_name args -> case maybe err id $ Map.lookup sig $ funs c of
    Fun f -> error $ "todo"
    Arg rhs c' -> upd rhs c' sigma v
    -- TODO: deduplicate with `run`
    fun@(Eval.Def arg_names rhs c') ->
      let funs' = (sig, fun) : zipWith (\name arg -> ((name, 0), (Arg arg c))) arg_names args in
      upd rhs (c' {funs = Map.fromList funs' `Map.union` funs c'}) sigma v
    where
     sig = (f_name, length args)
     err = error $ "undefined function: " ++ f_name ++ "/" ++ show (length args)
  _ -> error "todo"

builtins :: Value v => Map.Map (String, Int) (Named v)
builtins = Map.fromList $ map (\ (sig, f) -> (sig, Fun f)) $
  [ (("path", 1), \args c vp -> map getPath $ run (args !! 0) c (ValP {val = val vp, path = Just []}))
  ]

getPath :: Value v => ValPE v -> ValPE v
getPath vpe =
  vpe >>= maybe (err "cannot determine path") ok . path >>= Val.arr . map ok >>= return . newVal
