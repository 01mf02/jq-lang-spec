import qualified Data.Map as Map
import qualified Val
import qualified IR
import Eval (Ctx(..), run, builtins)
import Control.Monad (when)
import System.Exit (exitFailure)

main :: IO ()
main = do
  stdin <- getContents
  --print stdin
  let tm = read stdin
  --print tm
  let f = IR.compile 0 tm

  when (not $ IR.wf f IR.emptyCtx) $ do
    putStrLn $ "Filter is not well-formed (unknown function or variable)"
    exitFailure

  let c = Ctx {vars = Map.empty, funs = builtins, lbls = Map.empty}
  let v = Val.newVal Val.Null
  --print f
  err <- printUntilError $ map (fmap Val.val) $ run f c v
  maybe (return ()) (\e -> (print $ "Error: " ++ show e) >> exitFailure) err

printUntilError :: Show x => [Either e x] -> IO (Maybe e)
printUntilError [] = return Nothing
printUntilError (y:ys) =
  case y of
    Right x -> print x >> printUntilError ys
    Left e -> return (Just e)
