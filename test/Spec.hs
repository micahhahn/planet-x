import Test.Tasty
import Test.Tasty.HUnit

import qualified Lib
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

main :: IO ()
main = defaultMain tests

tests = testGroup "Tests" [test1]

vs = [(Lib.xs !! 0, True), (Lib.xs !! 1, False), (Lib.xs !! 2, True), (Lib.xs !! 3, False), (Lib.xs !! 4, False)]
x = Lib.evalT (Lib.kFunEQ (take 5 Lib.xs) 2) (Map.fromList vs)
test1 = testCase "Choose 5" $ x @?= True