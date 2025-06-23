import qualified Data.Map as Map
import qualified Val
import qualified IR
import Eval (Ctx(..), run)

main :: IO ()
main = do
  stdin <- getContents
  print stdin
  let tm = read stdin
  print tm
  let f = IR.compile 0 tm
  let c = Eval.Ctx {vars = Map.empty, funs = Map.empty, lbls = Map.empty}
  let v = Val.Null
  print f
  print $ Eval.run f c v
