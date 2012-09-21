module Constraints.Set.Solver (
  -- * Types
  ConstraintError(..),
  Variance(..),
  Inclusion,
  SetExpression(..),
  ConstraintSystem,
  SolvedSystem,
  -- * Constructors
  emptySet,
  universalSet,
  setVariable,
  atom,
  term,
  (<=!),
  constraintSystem,
  -- * Interface
  solveSystem,
  leastSolution
  ) where

import Constraints.Set.Implementation
