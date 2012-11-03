module Main ( main ) where

import Control.Exception
import Data.List ( permutations, sort )
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
     testCase "tc6" tc6,
     testCase "tc7" tc7,
     testCase "tc8" tc8,
     testCase "tc9" tc9,
     testCase "tc10" tc10,
     testCase "tc11" tc11
     ],
  testGroup "PointsTo" [
    testCase "pt1" pt1,
    testCase "pt2" pt2
    ]
  ]

tc1 :: Assertion
tc1 = solveFor "tc1" "a" [5,6] is
  where
    is = [ atom 5 <=! setVariable "a", atom 6 <=! setVariable "a" ]

tc2 :: Assertion
tc2 = solveFor "tc2" "a" [5] is
  where
    is = [ atom 5 <=! setVariable "a", atom 6 <=! setVariable "b" ]

tc3 :: Assertion
tc3 = solveFor "tc3" "a" [5,6] is
  where
    is = [ atom 5 <=! setVariable "b"
         , atom 6 <=! setVariable "b"
         , setVariable "b" <=! setVariable "a"
         ]

tc4 :: Assertion
tc4 = solveFor "tc4" "a" [0..20] is
  where
    is = map ((<=! setVariable "a") . atom) [0..20]

-- | From the FFSA98 paper
tc5 :: Assertion
tc5 = mapM_ (solveFor "tc5" "R1" [0..40]) $ take 1000 $ permutations is
  where
    is = concat [
      [ setVariable "Z" <=! setVariable "R1"
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

-- | Test a simple cycle
tc6 :: Assertion
tc6 = mapM_ (solveFor "tc6" "a" [5,6,7,8]) $ take 1000 $ permutations is
  where
    is = [ atom 5 <=! setVariable "b"
         , atom 6 <=! setVariable "b"
         , atom 7 <=! setVariable "a"
         , atom 8 <=! setVariable "a"
         , setVariable "b" <=! setVariable "a"
         , setVariable "a" <=! setVariable "b"
         ]

-- | Test a longer cycle
tc7 :: Assertion
tc7 = mapM_ (solveFor "tc7" "f" [5,6,7,8]) $ take 1000 $ permutations is
  where
    is = [ atom 5 <=! setVariable "b"
         , atom 6 <=! setVariable "b"
         , atom 7 <=! setVariable "a"
         , atom 8 <=! setVariable "a"
         , setVariable "b" <=! setVariable "a"
         , setVariable "c" <=! setVariable "b"
         , setVariable "d" <=! setVariable "c"
         , setVariable "e" <=! setVariable "d"
         , setVariable "f" <=! setVariable "e"
         , setVariable "g" <=! setVariable "f"
         , setVariable "a" <=! setVariable "g"
         ]


tc8 :: Assertion
tc8 = mapM_ (solveFor "tc8" "zz" []) $ take 1000 $ permutations is
  where
    is = [ atom 5 <=! setVariable "b"
         , atom 6 <=! setVariable "b"
         , atom 7 <=! setVariable "a"
         , atom 8 <=! setVariable "a"
         , setVariable "b" <=! setVariable "a"
         , setVariable "c" <=! setVariable "b"
         , setVariable "d" <=! setVariable "c"
         , setVariable "e" <=! setVariable "d"
         , setVariable "f" <=! setVariable "e"
         , setVariable "g" <=! setVariable "f"
         , setVariable "a" <=! setVariable "g"
         , setVariable "z" <=! setVariable "f"
         , setVariable "zz" <=! setVariable "z"
         ]

tc9 :: Assertion
tc9 =
  mapM_ (solveFor "tc9" "zz" [11]) $ take 1000 $ permutations is
  where
    is = [ atom 5 <=! setVariable "b"
         , atom 6 <=! setVariable "b"
         , atom 7 <=! setVariable "a"
         , atom 8 <=! setVariable "a"
         , setVariable "b" <=! setVariable "a"
         , setVariable "c" <=! setVariable "b"
         , setVariable "d" <=! setVariable "c"
         , setVariable "e" <=! setVariable "d"
         , setVariable "f" <=! setVariable "e"
         , setVariable "g" <=! setVariable "f"
         , setVariable "a" <=! setVariable "g"
         , setVariable "z" <=! setVariable "f"
         , setVariable "zz" <=! setVariable "z"
         , atom 11 <=! setVariable "zz"
         ]

tc10 :: Assertion
tc10 =
  mapM_ (solveFor "tc10" "c" [5,6,7,8,11]) $ take 1000 $ permutations is
  where
    is = [ atom 5 <=! setVariable "b"
         , atom 6 <=! setVariable "b"
         , atom 7 <=! setVariable "a"
         , atom 8 <=! setVariable "a"
         , setVariable "b" <=! setVariable "a"
         , setVariable "c" <=! setVariable "b"
         , setVariable "d" <=! setVariable "c"
         , setVariable "e" <=! setVariable "d"
         , setVariable "f" <=! setVariable "e"
         , setVariable "g" <=! setVariable "f"
         , setVariable "a" <=! setVariable "g"
         , setVariable "z" <=! setVariable "f"
         , setVariable "zz" <=! setVariable "z"
         , atom 11 <=! setVariable "zz"
         ]

-- | There are no solutions to this type of constraint (A ⊆ c) when c is
-- a nullary constructor (a constant term).  It can have solutions
-- when c has arguments.
tc11 :: Assertion
tc11 = solveFor "tc11" "a" [] is
  where
    is = [ setVariable "a" <=! atom 5 ]

solveFor :: String -> String -> [Int] -> [Inclusion String Int] -> Assertion
solveFor name var expected is =
  assertEqual name (sort (map toSetExp expected)) (sort sol)
  where
    Just solved = solveSystem is
    Just sol = leastSolution solved var

toSetExp :: Int -> SetExpression v Int
toSetExp i = term i [] []

-- | Points-to example from the paper, a = &b;
pt1 :: Assertion
pt1 = assertEqual "pt1" [loc "b"] sol
  where
    sol = either throwErr id $ do
      s <- solveSystem is
      leastSolution s "Xa"
    ref = term "ref" [Covariant, Covariant, Contravariant]
    loc name = ref [atom name, setVariable ("X"++name), setVariable ("X"++name)]
    is = [ loc "a" <=! ref [ universalSet, universalSet, setVariable "T1" ]
         , ref [ emptySet, loc "b", emptySet ] <=! ref [ universalSet, setVariable "T2", emptySet ]
         , setVariable "T2" <=! setVariable "T1"
         ]


-- | A simple example (with LLVM bitcode)
-- > int * p1, *p2;
-- > int ** pp;
-- > int x,y,z;
-- >
-- > p1 = &x;
-- > p2 = &y;
-- > pp = &p2;
-- > *pp = p1;
-- > *pp = &z;
--
-- > store i32* @x, i32** @p1, align 4
-- > store i32* @y, i32** @p2, align 4
-- > store i32** @p2, i32*** @pp, align 4
-- > %1 = load i32** @p1, align 4
-- > %2 = load i32*** @pp, align 4
-- > store i32* %1, i32** %2, align 4
-- > %3 = load i32*** @pp, align 4
-- > store i32* @z, i32** %3, align 4
pt2 :: Assertion
pt2 = assertEqual "pt2" (sort [loc "x", loc "z"]) (sort sol)
  where
    sol = either throwErr id $ do
      s <- solveSystem is
      leastSolution s "Xp1"
    ref = term "ref" [Covariant, Covariant, Contravariant]
    loc name = ref [atom name, setVariable ("X"++name), setVariable ("X"++name)]

    xloc = loc "x"
    yloc = loc "y"
    zloc = loc "z"
    p1loc = loc "p1"
    p2loc = loc "p2"
    pploc = loc "pp"
    -- First, p1 = &x
    is = [ loc "p1" <=! ref [ universalSet, universalSet, setVariable "T1" ]
         , ref [ emptySet, loc "x", emptySet ] <=! ref [ universalSet, setVariable "T2", emptySet ]
         , setVariable "T2" <=! setVariable "T1"
           -- now p2 = &y
         , loc "p2" <=! ref [ universalSet, universalSet, setVariable "T3" ]
         , ref [ emptySet, loc "y", emptySet ] <=! ref [universalSet, setVariable "T4", emptySet ]
         , setVariable "T4" <=! setVariable "T3"
           -- now pp = &p2;
         , loc "pp" <=! ref [ universalSet, universalSet, setVariable "T5" ]
         , ref [ emptySet, loc "p2", emptySet ] <=! ref [universalSet, setVariable "T6", emptySet ]
         , setVariable "T6" <=! setVariable "T5"
           -- now pp = &p1;
         , loc "pp" <=! ref [ universalSet, universalSet, setVariable "T7" ]
         , ref [ emptySet, loc "p1", emptySet ] <=! ref [universalSet, setVariable "T8", emptySet ]
         , setVariable "T8" <=! setVariable "T7"
           -- *pp (saved as T9)
         , loc "pp" <=! ref [ universalSet, setVariable "T9", emptySet ]
           -- *pp = &z;
         , setVariable "T9" <=! ref [ universalSet, universalSet, setVariable "TT" ]
         , ref [ emptySet, loc "z", emptySet ] <=! ref [universalSet, setVariable "T10", emptySet ]
         , setVariable "T10" <=! setVariable "TT"
         ]

-- What if we take the above and add *pp = &zz; (make sure to just
-- re-use T9).  Another important case, what about *pq = *pp;

throwErr :: ConstraintError String String -> [SetExpression String String]
throwErr = throw

main :: IO ()
main = defaultMain tests
