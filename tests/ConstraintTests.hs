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
     testCase "tc2" tc2,
     testCase "tc3" tc3,
     testCase "tc4" tc4,
     testCase "tc5" tc5,
     testCase "tc6" tc6
     ]
  ]

tc1 :: Assertion
tc1 =
  assertEqual "tc1" [5,6 :: Int] (sort sol)
  where
    Just solved = solveSystem cs
    Just sol = leastSolution solved "a"
    cs = constraintSystem [ atom 5 <=! setVariable "a", atom 6 <=! setVariable "a" ]

tc2 :: Assertion
tc2 =
  assertEqual "tc2" [5 :: Int] (sort sol)
  where
    Just solved = solveSystem cs
    Just sol = leastSolution solved "a"
    cs = constraintSystem [ atom 5 <=! setVariable "a", atom 6 <=! setVariable "b" ]

tc3 :: Assertion
tc3 =
  assertEqual "tc3" [5, 6 :: Int] (sort sol)
  where
    Just solved = solveSystem cs
    Just sol = leastSolution solved "a"
    cs = constraintSystem [ atom 5 <=! setVariable "b"
                          , atom 6 <=! setVariable "b"
                          , setVariable "b" <=! setVariable "a"
                          ]

tc4 :: Assertion
tc4 =
  assertEqual "tc4" [0..20 :: Int] (sort sol)
  where
    Just solved = solveSystem cs
    Just sol = leastSolution solved "a"
    cs = constraintSystem $ map ((<=! setVariable "a") . atom) [0..20]

-- From the FFSA98 paper
tc5 :: Assertion
tc5 =
  assertEqual "tc5" [0..40 :: Int] (sort sol)
  where
    Just solved = solveSystem cs
    Just sol = leastSolution solved "R1"
    cs = constraintSystem $ concat [
      [setVariable "Z" <=! setVariable "R1"
      , setVariable "Z" <=! setVariable "R2"
      , setVariable "Y1" <=! setVariable "Z"
      , setVariable "Y2" <=! setVariable "Z"
      , setVariable "X" <=! setVariable "Y1"
      , setVariable "X" <=! setVariable "Y2"
      , setVariable "L1" <=! setVariable "X"
      , setVariable "L2" <=! setVariable "X"
      ],
      map ((<=! setVariable "L1") . atom) [0..20],
      map ((<=! setVariable "L2") . atom) [20..40]
      ]

-- Test a simple cycle
tc6 :: Assertion
tc6 =
  assertEqual "tc6" [5, 6, 7, 8 :: Int] (sort sol)
  where
    Just solved = solveSystem cs
    Just sol = leastSolution solved "a"
    cs = constraintSystem [ atom 5 <=! setVariable "b"
                          , atom 6 <=! setVariable "b"
                          , atom 7 <=! setVariable "a"
                          , atom 8 <=! setVariable "a"
                          , setVariable "b" <=! setVariable "a"
                          , setVariable "a" <=! setVariable "b"
                          ]




main :: IO ()
main = defaultMain tests
