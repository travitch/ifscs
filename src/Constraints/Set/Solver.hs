-- | This is an implementation of a set (inclusion) constraint solver.
--
-- Set constraints, also known as inclusion constraints, are a
-- convenient, expressive, and efficient way to solve graph
-- reachability problems.  A constraint system consists of set
-- variables and constructed terms representing atomic literals and
-- compound terms in the domain.  Terms and atomic literals are
-- /included/ in sets by inclusion constraints, and inclusion
-- relationships are established between set variables.
--
-- For example, consider the following constraint system:
--
-- > 5 ⊆ S[B]
-- > 6 ⊆ S[B]
-- > S[B] ⊆ S[A]
--
-- This says that 5 and 6 (atomic literals) are included in the set
-- represented by set variable B.  It also says that set B is a subset
-- of set A.  Thus, the least solution to this system is:
--
-- > S[B] = { 5, 6 }
-- > S[A] = { 5, 6 }
--
-- This example can be solved with this library with the following
-- code:
--
-- > let constraints = [ atom 6 <=! setVariable "b"
-- >                   , atom 5 <=! setVariable "b"
-- >                   , setVariable "b" <=! setVariable "a"
-- >                   ]
-- >     Just solved = solveSystem constraints
-- >     Just solutionA = leastSolution solved "a"
--
-- which gives the answer: [ ConstructedTerm 5 [], ConstructedTerm 6
-- [] ] corresponding to two atoms: 5 and 6.  The 'solveSystem' and
-- 'leastSolution' functions report errors using the 'Failure'
-- abstraction from the failure package.  This abstraction lets
-- callers receive errors in the format they prefer.  This example
-- discards errors by treating them as Maybe values.  Errors can be
-- observed purely using the Either instance of Failure or impurely in
-- the IO monad using the IO instance.
--
-- The implementation is based on the set constraint formulation
-- described in the FFSA98 paper in PLDI'98:
-- <http://dx.doi.org/10.1145/277650.277667>.  Also available at
--
-- <http://theory.stanford.edu/~aiken/publications/papers/pldi98b.ps>
--
-- This formulation is notable for representing the constraint graph
-- in /inductive/ form.  Briefly, inductive form assigns an ordering
-- to the set variables in the graph and uses this ordering to reduce
-- the amount of work required to saturate the graph.  The reduction
-- implies a tradeoff: not all solutions are immediately manifest in
-- the solved constraint graph.  Instead, a DFS is required to extract
-- each solution.
module Constraints.Set.Solver (
  -- * Constructors
  emptySet,
  universalSet,
  setVariable,
  term,
  atom,
  (<=!),
  -- * Interface
  solveSystem,
  leastSolution,
  -- * Types
  ConstraintError(..),
  Variance(..),
  Inclusion,
  SetExpression(..),
  SolvedSystem
  ) where

import Constraints.Set.Implementation
