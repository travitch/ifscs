{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, DeriveDataTypeable #-}
{-# LANGUAGE BangPatterns #-}
module Constraints.Set.Implementation (
  ConstraintError(..),
  Variance(..),
  Inclusion,
  SetExpression(..),
  ConstraintSystem,
  SolvedSystem,
  emptySet,
  universalSet,
  setVariable,
  atom,
  term,
  (<=!),
  constraintSystem,
  solveSystem,
  leastSolution,
  -- * Debugging
  ConstraintEdge(..),
  solvedSystemGraphElems
  ) where

import Control.Exception
import Control.Failure
import Control.Monad.State.Strict
import qualified Data.Foldable as F
import Data.Graph.Interface
import Data.Graph.LazyHAMT
import Data.Graph.Algorithms.Matching.DFS
import Data.List ( intercalate )
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Maybe ( catMaybes )
import Data.Monoid
import Data.Set ( Set )
import qualified Data.Set as S
import Data.Typeable
import Data.Vector.Persistent ( Vector )
import qualified Data.Vector.Persistent as V

-- 1) Take the list of initial constraints and simplify them using the
-- rewrite rules.  Once they are solved, all constraints are in
-- *atomic form*.
--
-- One approach is to fold over the list of constraints and simplify
-- each one until it is in atomic form (simplification can produce
-- multiple constraints).  Once at atomic form, add the constraint to
-- a set.

-- 2) Use the atomic constraints to build the closure graph.

emptySet :: SetExpression v c
emptySet = EmptySet

universalSet :: SetExpression v c
universalSet = UniversalSet

setVariable :: v -> SetExpression v c
setVariable = SetVariable

-- | Atomic terms have a label and arity zero.
atom :: c -> SetExpression v c
atom conLabel = ConstructedTerm conLabel [] []

-- | This returns a function to create terms from lists of
-- SetExpressions.  It is meant to be partially applied so that as
-- many terms as possible can share the same reference to a label and
-- signature.
term :: c -> [Variance] -> ([SetExpression v c] -> SetExpression v c)
term = ConstructedTerm

(<=!) :: SetExpression v c -> SetExpression v c -> Inclusion v c
(<=!) = (:<=)

constraintSystem :: [Inclusion v c] -> ConstraintSystem v c
constraintSystem = ConstraintSystem

data Variance = Covariant | Contravariant
              deriving (Eq, Ord, Show)

data SetExpression v c = EmptySet
                       | UniversalSet
                       | SetVariable v
                       | ConstructedTerm c [Variance] [SetExpression v c]
                       deriving (Eq, Ord)

instance (Show v, Show c) => Show (SetExpression v c) where
  show EmptySet = "∅"
  show UniversalSet = "U"
  show (SetVariable v) = show v
  show (ConstructedTerm c _ es) =
    concat [ show c, "("
           , intercalate ", " (map show es)
           , ")"
           ]

-- | An inclusion is a constraint of the form se1 ⊆ se2
data Inclusion v c = (SetExpression v c) :<= (SetExpression v c)
                                 deriving (Eq, Ord)

instance (Show v, Show c) => Show (Inclusion v c) where
  show (lhs :<= rhs) = concat [ show lhs, " ⊆ ", show rhs ]

-- | A constraint system is a set of constraints in DNF.  The
-- disjuncts are implicit.
data ConstraintSystem v c = ConstraintSystem [Inclusion v c]
                          deriving (Eq, Ord, Show)

data ConstraintError v c = NoSolution (Inclusion v c)
                         | NoVariableLabel v
                         deriving (Eq, Ord, Show, Typeable)

instance (Typeable v, Typeable c, Show v, Show c) => Exception (ConstraintError v c)

-- | Simplify one set expression.
simplifyInclusion :: (Failure (ConstraintError v c) m, Eq v, Eq c)
                     => [Inclusion v c]
                     -> Inclusion v c
                     -> m [Inclusion v c]
simplifyInclusion acc i =
  case i of
    -- Eliminate constraints of the form A ⊆ A
    SetVariable v1 :<= SetVariable v2 ->
      if v1 == v2 then return acc else return (i : acc)
    UniversalSet :<= EmptySet ->
      failure (NoSolution i)
    ConstructedTerm c1 s1 ses1 :<= ConstructedTerm c2 s2 ses2 ->
      let sigLen = length s1
          triples = zip3 s1 ses1 ses2
      in case c1 == c2 && s1 == s2 && sigLen == length ses1 && sigLen == length ses2 of
        False -> failure (NoSolution i)
        True -> foldM simplifyWithVariance acc triples
    UniversalSet :<= ConstructedTerm _ _ _ -> failure (NoSolution i)
    ConstructedTerm _ _ _ :<= EmptySet -> failure (NoSolution i)
    -- Eliminate constraints of the form A ⊆ 1
    _ :<= UniversalSet -> return acc
    -- 0 ⊆ A
    EmptySet :<= _ -> return acc
    -- Keep anything else (atomic forms)
    _ -> return (i : acc)

simplifyWithVariance :: (Failure (ConstraintError v c) m, Eq v, Eq c)
                        => [Inclusion v c]
                        -> (Variance, SetExpression v c, SetExpression v c)
                        -> m [Inclusion v c]
simplifyWithVariance acc (Covariant, se1, se2) =
  simplifyInclusion acc (se1 :<= se2)
simplifyWithVariance acc (Contravariant, se1, se2) =
  simplifyInclusion acc (se2 :<= se1)

simplifySystem :: (Failure (ConstraintError v c) m, Eq v, Eq c)
                  => ConstraintSystem v c
                  -> m (ConstraintSystem v c)
simplifySystem (ConstraintSystem is) = do
  is' <- foldM simplifyInclusion [] is
  return $! ConstraintSystem is'

data ConstraintEdge = Succ | Pred
                    deriving (Eq, Ord, Show)

type IFGraph = Gr () ConstraintEdge

data SolvedSystem v c = SolvedSystem { systemIFGraph :: IFGraph
                                     , systemSetToIdMap :: Map (SetExpression v c) Int
                                     , systemIdToSetMap :: Vector (SetExpression v c)
                                     }


-- | Compute the least solution for the given variable
--
-- LS(y) = All source nodes with a predecessor edge to y, plus LS(x)
-- for all x where x has a predecessor edge to y.
leastSolution :: forall c m v . (Failure (ConstraintError v c) m, Ord v, Ord c)
                 => SolvedSystem v c
                 -> v
                 -> m [SetExpression v c]
leastSolution (SolvedSystem g0 m v) varLabel = do
  case M.lookup (SetVariable varLabel) m of
    Nothing -> failure ex
    Just nid -> return $ catMaybes $ xdfsWith pre' addTerm [nid] g0
  where
    ex :: ConstraintError v c
    ex = NoVariableLabel varLabel

    -- We only want to add ConstructedTerms to the output list
    addTerm :: Context IFGraph -> Maybe (SetExpression v c)
    addTerm (Context _ (LNode nid _) _) = do
      se <- V.index v nid
      case se of
        ConstructedTerm _ _ _ -> return se
        _ -> Nothing

solveSystem :: (Failure (ConstraintError v c) m, Eq c, Eq v, Ord c, Ord v)
               => ConstraintSystem v c
               -> m (SolvedSystem v c)
solveSystem s = do
  s' <- simplifySystem s
  return $! constraintsToIFGraph s'

constraintsToIFGraph :: (Ord v, Ord c) => ConstraintSystem v c -> SolvedSystem v c
constraintsToIFGraph (ConstraintSystem is) =
  SolvedSystem { systemIFGraph = g
               , systemSetToIdMap = m
               , systemIdToSetMap = v
               }
  where
    -- The initial graph has all of the nodes we need; after that we
    -- just need to saturate the edges through transitive closure
    (g, (m, v)) = runState (buildInitialGraph is >>= saturateGraph) (mempty, mempty)

type BuilderMonad v c = State (Map (SetExpression v c) Int, Vector (SetExpression v c))

-- | Build an initial IF constraint graph that contains all of the
-- vertices and the edges induced by the initial simplified constraint
-- system.
buildInitialGraph :: (Ord v, Ord c) => [Inclusion v c] -> BuilderMonad v c IFGraph
buildInitialGraph is = do
  res <- foldM addInclusion (empty, mempty) is
  return (fst res)

-- | Adds an inclusion to the constraint graph (adding vertices if
-- necessary).  Returns the set of nodes that are affected (and will
-- need more transitive edges).
addInclusion :: (Eq c, Ord v, Ord c)
                => (IFGraph, Set Int)
                -> Inclusion v c
                -> BuilderMonad v c (IFGraph, Set Int)
addInclusion acc i =
  case i of
    -- This is the key to an inductive form graph (rather than
    -- standard form)
    e1@(SetVariable v1) :<= e2@(SetVariable v2) ->
      case compare v1 v2 of
        EQ -> error "Constraints.Set.Solver.addInclusion: invalid A ⊆ A constraint"
        LT -> addEdge acc Pred e1 e2
        GT -> addEdge acc Succ e1 e2
    e1@(ConstructedTerm _ _ _) :<= e2@(SetVariable _) -> addEdge acc Pred e1 e2
    e1@(SetVariable _) :<= e2@(ConstructedTerm _ _ _) -> addEdge acc Succ e1 e2
    _ -> error "Constraints.Set.Solver.addInclusion: unexpected expression"

-- | Add an edge in the constraint graph between the two expressions
-- with the given label.  Adds nodes for the expressions if necessary.
--
-- FIXME: Instead of just returning a simple set here, we can return a
-- set of pairs (edges) that we know will need to be added.  Adding
-- those edges would then add more, &c.  This would save asymptotic
-- work when re-visiting the source nodes (already visited nodes can
-- be ignored).
addEdge :: (Eq v, Eq c, Ord v, Ord c)
           => (IFGraph, Set Int)
           -> ConstraintEdge
           -> SetExpression v c
           -> SetExpression v c
           -> BuilderMonad v c (IFGraph, Set Int)
addEdge (!g0, !affected) etype e1 e2 = do
  (eid1, g1) <- getEID e1 g0
  (eid2, g2) <- getEID e2 g1
  let edge = LEdge (Edge eid1 eid2) etype
      !g3 = insEdge edge g2

  -- If the edge we added is a predecessor edge, eid1 needs to be
  -- scanned again later because new successors to eid2 might be
  -- reachable.
  --
  -- Otherwise, all predecessors to eid1 (with Pred edge labels) need
  -- to be scanned later.
  case etype of
    Pred -> return $ (g3, S.insert eid1 affected)
    Succ -> return $ (g3, foldr addPredPred affected $ lpre g3 eid1)
  where
    addPredPred (_, Succ) !s = s
    addPredPred (pid, Pred) !s = S.insert pid s

-- | Get the ID for the expression node.  Inserts a new node into the
-- graph if needed.
getEID :: (Ord v, Ord c)
          => SetExpression v c
          -> IFGraph
          -> BuilderMonad v c (Int, IFGraph)
getEID e g = do
  (m, v) <- get
  case M.lookup e m of
    Just i -> return (i, g)
    Nothing -> do
      let eid = V.length v
          !v' = V.snoc v e
          !m' = M.insert e eid m
          !g' = insNode (LNode eid ()) g
      put (m', v')
      return (eid, g')

-- | For each node L in the graph, follow its predecessor edges to
-- obtain set X.  For each ndoe in X, follow its successor edges
-- giving a list of R.  Generate L ⊆ R and simplify it with
-- 'simplifyInclusion'.  These are new edges (collect them all in a
-- set, discarding existing edges).
--
-- After a pass, insert all of the new edges
--
-- Repeat until no new edges are found.
--
-- An easy optimization is to base the next iteration only on the
-- newly-added edges (since any additions in the next iteration must
-- be due to those new edges).  It would require searching forward
-- (for pred edges) and backward (for succ edges).
--
-- Also perform online cycle detection per FFSA98
--
-- This function can fail if a constraint generated by the saturation
-- implies that no solution is possible.  I think that probably
-- shouldn't ever happen but I have no proof.
saturateGraph :: (Eq v, Eq c, Ord v, Ord c)
                 => IFGraph
                 -> BuilderMonad v c IFGraph
saturateGraph g0 = closureEdges (S.fromList (nodes g0)) g0
  where
    simplify v e (l, r) =
      let incl = V.unsafeIndex v l :<= V.unsafeIndex v r
          Just incl' = simplifyInclusion e incl
      in incl'
    closureEdges ns g
      | S.null ns = return g
      | otherwise = do
        (_, v) <- get
        let nextEdges = F.foldl' (findEdge g) mempty ns
            inclusions = F.foldl' (simplify v) [] nextEdges
        case null inclusions of
          True -> return g
          False -> do
            (g', affectedNodes) <- foldM addInclusion (g, mempty) inclusions
--                affectedNodes = S.fromList (nodes g)
            closureEdges affectedNodes g'

    findEdge g s l =
      let xs = filter isPred $ lsuc g l
          rs = filter isSucc $ concatMap (lsuc g . fst) xs
      in foldr (toNewInclusion g l . fst) s rs

    toNewInclusion g l r !s =
      case edgeExists g (Edge l r) of
        Just _ -> s
        Nothing -> S.insert (l, r) s

isPred :: (Node IFGraph, EdgeLabel IFGraph) -> Bool
isPred = (==Pred) . snd

isSucc :: (Node IFGraph, EdgeLabel IFGraph) -> Bool
isSucc = (==Succ) . snd


solvedSystemGraphElems :: (Eq v, Eq c) => SolvedSystem v c -> ([(Int, SetExpression v c)], [(Int, Int, ConstraintEdge)])
solvedSystemGraphElems (SolvedSystem g _ v) = (ns, es)
  where
    ns = map (\(LNode nid _) -> (nid, V.unsafeIndex v nid)) $ labNodes g
    es = map (\(LEdge (Edge s d) l) -> (s, d, l)) $ labEdges g