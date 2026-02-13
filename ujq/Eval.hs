module Eval where

import qualified Data.Map as Map
import Data.Map ((!))

import qualified Syn
import qualified Val
import Val (ValR, ValP(..), ValPR, Value, ok, err, newVal)
import IR (Filter(..))
import qualified IR

type Arg = String

-- Named filter, such as `length`, `x`, or `has($k)`
data Named v =
    -- filter argument, such as `x` on the RHS of `def f(x): x`
    Arg Filter (Ctx v)
    -- defined filter, such as `f(0)` in `def f(x): ...; f(0)`
  | Def [Arg] Filter (Ctx v)
    -- builtin function, such as `length`
  | Fun (Builtin v)

type Builtin v = [Filter] -> Ctx v -> ValP v -> [ValPR v]

data Ctx v = Ctx {
  vars :: Map.Map IR.Var v,
  funs :: Map.Map (String, Int) (Named v),
  lbls :: Map.Map String Int
}

toIRCtx :: Ctx v -> IR.Ctx
toIRCtx (Ctx {vars, funs, lbls}) = IR.Ctx {
  IR.vars = Map.keysSet vars,
  IR.funs = Map.keysSet funs,
  IR.lbls = Map.keysSet lbls
}

mathOp :: Value a => Syn.MathOp -> a -> a -> ValR a
mathOp op = case op of
  Syn.Add -> Val.add
  Syn.Sub -> Val.sub
  Syn.Mul -> Val.mul
  Syn.Div -> Val.div
  Syn.Rem -> Val.rem

app :: (x -> [Either e y]) -> [Either e x] -> [Either e y]
app f = mconcat . map (\r -> case r of {Left e -> [Left e]; Right y -> f y})

bind = flip app

tryCatch :: (ValP v -> [ValPR v]) -> [ValPR v] -> [ValPR v]
tryCatch catch l = case l of
  [] -> []
  Left (Val.Error e) : _ -> catch $ newVal e
  y : tl -> y : tryCatch catch tl

label :: Int -> [ValPR v] -> [ValPR v]
label lbl = takeWhile $ \r -> case r of
  Left (Val.Break lbl') | lbl == lbl' -> False
  _ -> True

trues :: Value v => [ValPR v] -> [ValPR v]
trues = filter (either (const True) (Val.toBool . val))

fold :: (x -> y -> [Either e y]) -> (x -> y -> [Either e y]) -> (y -> [Either e y]) -> [Either e x] -> y -> [Either e y]
fold f g n xs acc = case xs of
  [] -> n acc
  Right x : tl -> f x acc `bind` (\y -> g x y ++ fold f g n tl y)
  Left e : _ -> [Left e]

type Update e x y = x -> (y -> [Either e y]) -> y -> [Either e y]

foldUpd :: Update e x y -> (x -> y -> [Either e y]) -> (y -> [Either e y]) -> [Either e x] -> y -> [Either e y]
foldUpd f g n l v = case l of
  [] -> n v
  Right h : t -> f h (\x -> app (foldUpd f g n t) (g h x)) v
  Left e : _ -> [Left e]

reduceUpd :: Update e x y -> (y -> [Either e y]) -> [Either e x] -> y -> [Either e y]
reduceUpd f sigma = foldUpd f (\h v -> [ok v]) sigma

foreachUpd :: Update e x y -> Update e x y -> (y -> [Either e y]) -> [Either e x] -> y -> [Either e y]
foreachUpd f g sigma = foldUpd f (\h v -> g h sigma v) (\v -> [ok v])

reduce :: (x -> y -> [Either e y]) -> [Either e x] -> y -> [Either e y]
reduce update = fold update (\_x _y -> []) (\y -> [Right y])

foreach :: (x -> y -> [Either e y]) -> (x -> y -> [Either e y]) -> [Either e x] -> y -> [Either e y]
foreach update init = fold update init (\_y -> [])

-- Bind a variable to a value.
bindVar :: IR.Var -> v -> Ctx v -> Ctx v
bindVar x v c@Ctx{vars} = c {vars = Map.insert x v vars}

-- Bind a definition in a context.
bindDef :: String -> [Arg] -> Filter -> Ctx v -> Ctx v
bindDef f_name arg_names rhs c@Ctx{funs} =
  c {funs = Map.insert (f_name, length arg_names) (Eval.Def arg_names rhs c) funs}

-- Retrieve either the builtin function or the filter corresponding to a named function call.
getNamed :: String -> [Filter] -> Ctx v -> Either (Builtin v) (Filter, Ctx v)
getNamed f_name args c = case maybe err id $ Map.lookup sig $ funs c of
  Fun f -> Left f
  Arg rhs c' -> Right (rhs, c')
  fun@(Eval.Def arg_names rhs c') ->
    let funs' = (sig, fun) : zipWith (\name arg -> ((name, 0), (Arg arg c))) arg_names args in
    Right (rhs, c' {funs = Map.fromList funs' `Map.union` funs c'})
  where
    sig = (f_name, length args)
    err = error $ "undefined function: " ++ f_name ++ "/" ++ show (length args)

run :: Value v => Filter -> Ctx v -> ValP v -> [ValPR v]
run f c@Ctx{vars, lbls} vp@ValP{val = v} = case f of
  Id -> [ok vp]
  Recurse -> run IR.recRun c vp
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
  Compose f g -> run f c vp `bind` run g c
  Bind f x g -> run f c vp `bind` (\y -> run g (bindVar x (val y) c) vp)
  Alt f g -> case trues $ run f c vp of {[] -> run g c vp; l -> l}
  Var x -> [ok $ newVal $ vars ! x]
  TryCatch f g -> tryCatch (run g c) $ run f c vp
  Label l f -> let li = Map.size lbls in label li $ run f (c {lbls = Map.insert l li lbls}) vp
  Break l -> [Left $ Val.Break (lbls ! l)]
  Ite x f g -> run (if Val.toBool $ vars ! x then f else g) c vp
  Reduce fx x f -> reduce (\xv -> run f (bindVar x (val xv) c)) (run fx c vp) vp
  Foreach fx x f g -> foreach (\xv -> run f (bindVar x (val xv) c)) (\xv -> run g (bindVar x (val xv) c)) (run fx c vp) vp
  Path part opt -> Val.idx vp (fmap ((!) vars) part) opt
  Update f g -> map (fmap newVal) $ upd f c (map (fmap val) . run g c . newVal) v
  IR.Def f_name arg_names rhs g -> run g (bindDef f_name arg_names rhs c) vp
  App f_name args -> case getNamed f_name args c of
    Left f -> f args c vp
    Right (rhs, c) -> run rhs c vp

upd :: Value v => Filter -> Ctx v -> (v -> [ValR v]) -> v -> [ValR v]
upd phi c@Ctx{vars, lbls} sigma v = case phi of
  Id -> sigma v
  Recurse -> upd IR.recUpd c sigma v
  Compose f g -> upd f c (upd g c sigma) v
  Concat f g -> upd f c sigma v `bind` upd g c sigma
  Alt f g -> upd (case trues $ run f c $ newVal v of {[] -> g; _ -> f}) c sigma v
  Path part opt -> [Val.upd v (fmap ((!) vars) part) opt sigma]
  Bind f x g -> reduce (\y -> upd g (bindVar x (val y) c) sigma) (run f c $ newVal v) v
  Ite x f g -> upd (if Val.toBool $ vars ! x then f else g) c sigma v
  Break l -> [Left $ Val.Break (lbls ! l)]
  Reduce fx x f -> reduceUpd (\xv -> upd f (bindVar x xv c)) sigma (map (fmap val) $ run fx c $ newVal v) v
  Foreach fx x f g -> foreachUpd (\xv -> upd f (bindVar x xv c)) (\xv -> upd g (bindVar x xv c)) sigma (map (fmap val) $ run fx c $ newVal v) v
  IR.Def f_name arg_names rhs g -> upd g (bindDef f_name arg_names rhs c) sigma v
  App f_name args -> case getNamed f_name args c of
    Left f -> error $ "todo"
    Right (rhs, c) -> upd rhs c sigma v
  _ -> error "todo"

-- Builtin functions.
builtins :: Value v => Map.Map (String, Int) (Named v)
builtins = Map.fromList $ map (\ (sig, f) -> (sig, Fun f)) $
  [ (("path", 1), \args c vp -> map getPath $ run (args !! 0) c (ValP {val = val vp, path = Just []}))
  ]

getPath :: Value v => ValPR v -> ValPR v
getPath vpe =
  vpe >>= maybe (err "cannot determine path") ok . path >>= Val.arr . map ok >>= return . newVal
