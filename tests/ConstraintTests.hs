module Main ( main ) where

import Data.List ( sort )
import Test.Framework ( defaultMain, testGroup, Test )
import Test.Framework.Providers.HUnit
import Test.HUnit hiding ( Test )

import Constraints.Set.Solver

tests :: [Test]
tests = [
  testGroup "Simple" [
     testCase "tc1" tc1,
     testCase "tc2" tc2
     ]
  ]

tc1 :: Assertion
tc1 =
  assertEqual "tc1" [5,6] (sort sol)
  where
    Just solved = solveSystem cs
    Just sol = leastSolution solved "a"
    cs = constraintSystem [ atom 5 <=! setVariable "a", atom 6 <=! setVariable "a" ]

tc2 :: Assertion
tc2 =
  assertEqual "tc2" [5] (sort sol)
  where
    Just solved = solveSystem cs
    Just sol = leastSolution solved "a"
    cs = constraintSystem [ atom 5 <=! setVariable "a", atom 6 <=! setVariable "b" ]


main :: IO ()
main = defaultMain tests
