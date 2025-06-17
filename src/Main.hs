import qualified Data.Map as Map
import qualified Data.Sequence as Seq
import Data.List (intercalate)
import Data.Char (isSpace, isAlpha, isAlphaNum)
import Debug.Trace

import qualified Syn
import qualified Def
import Def (Option(None, Some))

data Val = Null | Bool Bool | Int Int | Float Float | Str String
  | Arr (Seq.Seq Val) | Obj (Map.Map Val Val)
  deriving (Show, Eq, Ord)

type Var = String
type Arg = String

compile f' = case f' of
  Syn.Id -> Id
  Syn.Recurse -> Recurse
  Syn.Arr(Def.None) -> Arr0
  Syn.Arr(Def.Some(a)) -> ArrN (compile a)
  Syn.Obj([]) -> Obj0
  Syn.Var(x) -> Variable(x)
  Syn.BinOp(l, Syn.Comma, r) -> Concat (compile l) (compile r)
  Syn.Pipe(l, None, r) -> Compose (compile l) (compile r)
  Syn.Def([(name, args, rhs)], t) -> Def name args (compile rhs) (compile t)
  Syn.Call(name, args) -> App name (map compile args)

data Filter = Id | Recurse | Arr0 | Obj0 | ArrN Filter | Obj1 Var Var
  | BoolOp Var Syn.BoolOp Var
  | Concat Filter Filter | Compose Filter Filter
  | Bind Filter Var Filter | Variable Var
  | Ite Var Filter Filter
  | TryCatch Filter Filter
  | Def String [String] Filter Filter
  | App String [Filter]

showArgs :: [String] -> String
showArgs l = case l of {[] -> ""; _ -> "(" ++ intercalate "; " l ++ ")"}

instance Show Filter where
  show f' = case f' of
    Id -> "."
    Arr0 -> "[]"
    Obj0 -> "{}"
    ArrN f -> "[" ++ show f ++ "]"
    Concat f g -> "(" ++ show f ++ ", " ++ show g ++ ")"
    Compose f g -> "(" ++ show f ++ " | " ++ show g ++ ")"
    Variable v -> v
    Ite v f g -> "if " ++ v ++ " then " ++ show f ++ " else " ++ show g ++ "end"
    Def name args rhs g -> "def " ++ name ++ showArgs args ++ ": " ++ show rhs ++ "; " ++ show g
    App f args -> f ++ showArgs (map show args)

type ValR = Either Exn Val

data Ctx = Ctx {
  vars :: Map.Map Var Val,
  funs :: Map.Map (String, Int) (Maybe [Arg], Filter, Ctx),
  lbls :: Map.Map String Int
} deriving Show

data Exn = Error Val | Break Int deriving Show

arr :: [ValR] -> ValR
arr = fmap (Arr . Seq.fromList) . sequence

bool :: Val -> Bool
bool Null = False
bool (Bool False) = False
bool _ = True

ok :: Val -> ValR
ok = Right

app :: (Val -> [ValR]) -> [ValR] -> [ValR]
app f = mconcat . map (\r -> case r of {Left _ -> [r]; Right y -> f y})

tryCatch :: (Val -> [ValR]) -> [ValR] -> [ValR]
tryCatch catch l = case l of
  [] -> []
  Left (Error e) : _ -> catch e
  y : tl -> y : tryCatch catch tl

strip :: String -> [String] -> ((), [String])
strip = error "a"

type Parser a = ([String] -> (a, [String]))

infixr <&>
(<&>) :: Parser a -> Parser b -> Parser (a, b)
(<&>) pl pr = \input ->
  let (l, l_rest) = pl input in
  let (r, r_rest) = pr l_rest in
  ((l, r), r_rest)

(<&) :: Parser a -> Parser b -> Parser a
(<&) pl pr = \input -> let ((l, r), rest) = (pl <&> pr) input in (l, rest)

(&>) :: Parser a -> Parser b -> Parser b
(&>) pl pr = \input -> let ((l, r), rest) = (pl <&> pr) input in (r, rest)

parseVar :: Parser Var
parseVar = error "a"

lexer :: String -> [String]
lexer s = case dropWhile isSpace s of
  '$' : tl -> let (v, rest) = span isAlphaNum tl in ('$' : v) : lexer rest
  c : tl | isAlpha c -> let (v, rest) = span isAlphaNum tl in (c : v) : lexer rest
  '"' : tl -> error "a"
  

parse :: Parser Filter
parse ss = case ss of
  "." : tl -> (Id, tl)
  ".." : tl -> (Recurse, tl)
  v@('$':_) : tl -> (Variable v, tl)
  "[" : tl ->
     let (f, ftl) = parse tl in
     let "]" : close = ftl in
     (ArrN f, close)
  "try" : tl ->
    let ((try, catch), rest) = (parse <&> (strip "catch" &> parse)) tl in
    (TryCatch try catch, rest)
  "if": tl ->
    let p = parseVar <&> (strip "then" &> (parse <&> (strip "else" &> (parse <& strip "end")))) in
    let ((if_, (then_, else_)), rest) = p tl in
    (Ite if_ then_ else_, rest)
  "(" : lx@('$':_) : op : rx@('$':_) : ")" : tl | op `elem` ["==", "!=", "<", ">", "<=", ">="] ->
    error "a"
  _ -> error "a"

run :: Filter -> Ctx -> Val -> [ValR]
run f' c@Ctx{vars} v = case f' of
  Id -> [ok v]
  BoolOp lx op rx -> [ok $ Bool $ Syn.boolOp op (vars Map.! lx) (vars Map.! rx)]
  Arr0 -> [ok $ Arr $ Seq.empty]
  Obj0 -> [ok $ Obj $ Map.empty]
  ArrN f -> [arr $ run f c v]
  Obj1 kx vx -> [ok $ Obj $ Map.singleton (vars Map.! kx) (vars Map.! vx)]
  Concat f g -> run f c v ++ run g c v
  Compose f g -> (\y -> run g c y) `app` run f c v
  Bind f x g -> (\y -> run g (c {vars = Map.insert x y vars}) v) `app` run f c v
  Variable x -> [ok $ vars Map.! x]
  TryCatch f g -> tryCatch (\e -> run g c e) $ run f c v
  Ite x f g -> run (if bool $ vars Map.! x then f else g) c v
  Def f_name arg_names rhs g ->
    let add = Map.insert (f_name, length arg_names) (Just arg_names, rhs, c) in
    run g (c {funs = add $ funs c}) v
  App f_name args ->
    let sig = (f_name, length args) in
    let fun@(arg_names, rhs, c') = funs c Map.! sig in
    let funs' = maybe [] (\names -> (sig, fun) : zipWith (\name arg -> ((name, 0), (Nothing, arg, c))) names args) arg_names in
    run rhs (c' {funs = Map.fromList funs' `Map.union` funs c'}) v

main :: IO ()
main = do
  bla <- getContents
  print bla
  let tm = read bla :: Syn.Term
  print tm
  let filter = compile tm
{-
  let call f = App f []
  let def f = Def f []
  let f = Def "f" ["g"] (def "rec" (call "g" `Concat` call "rec") $ call "rec") $ App "f" [Id]
  --let f = Def "f" ["g"] (call "g" `Concat` App "f" [call "g"]) $ App "f" [Id]
  --let f = Bind Id "$x" $ Obj1 "$x" "$x"
-}

  let c = Ctx {vars = Map.empty, funs = Map.empty, lbls = Map.empty} 
  let v = Null
  print $ run filter c v
  return ()
