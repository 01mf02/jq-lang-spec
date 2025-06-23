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
  let c = Ctx {vars = Map.empty, funs = Map.empty, lbls = Map.empty}
  let v = Val.newVal Val.Null
  print f
  print $ map (fmap Val.val) $ run f c v
