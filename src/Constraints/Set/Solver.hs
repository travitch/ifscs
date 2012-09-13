{-# LANGUAGE FlexibleContexts, ScopedTypeVariables #-}
module Constraints.Set.Solver (
  ConstraintError(..),
  Inclusion,
  SetExpression,
  ConstraintSystem,
  SolvedSystem,
  emptySet,
  universalSet,
  setVariable,
  atom,
  (<=!),
  constraintSystem,
  solveSystem,
  leastSolution
  ) where

import Control.Failure
import Control.Monad.State.Strict
import qualified Data.Foldable as F
import Data.Graph.Interface
import Data.Graph.LazyHAMT
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Maybe ( mapMaybe )
import Data.Monoid
import Data.Set ( Set )
import qualified Data.Set as S
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

atom :: c -> SetExpression v c
atom = Term

(<=!) :: SetExpression v c -> SetExpression v c -> Inclusion v c
(<=!) = (:<=)

constraintSystem :: [Inclusion v c] -> ConstraintSystem v c
constraintSystem = ConstraintSystem

data SetExpression v c = EmptySet
                       | UniversalSet
                       | SetVariable v
                       | Term c
                         -- ^ A shorthand for a nullary constructed
                         -- term for testing and development.  Replace
                         -- with ConstructedTerm later.

                         -- | ConstructedTerm conLabel [SetExpression] Signature
                       deriving (Eq, Ord, Show)

data Inclusion v c = (SetExpression v c) :<= (SetExpression v c)
                                 deriving (Eq, Ord, Show)

-- | A constraint system is a set of constraints in DNF.  The
-- disjuncts are implicit.
data ConstraintSystem v c = ConstraintSystem [Inclusion v c]
                          deriving (Eq, Ord, Show)

data ConstraintError v c = NoSolution (Inclusion v c)
                         | NoVariableLabel v
                         deriving (Eq, Ord, Show)

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
    Term t1 :<= Term t2 ->
      if t1 == t2 then return acc else failure (NoSolution i)
    UniversalSet :<= Term _ -> failure (NoSolution i)
    Term _ :<= EmptySet -> failure (NoSolution i)
    -- Eliminate constraints of the form A ⊆ 1
    _ :<= UniversalSet -> return acc
    -- 0 ⊆ A
    EmptySet :<= _ -> return acc
    -- Keep anything else (atomic forms)
    _ -> return (i : acc)

simplifySystem :: (Failure (ConstraintError v c) m, Eq v, Eq c)
                  => ConstraintSystem v c
                  -> m (ConstraintSystem v c)
simplifySystem (ConstraintSystem is) = do
  is' <- foldM simplifyInclusion [] is
  return $! ConstraintSystem is'

data ConstraintEdge = Succ | Pred
                    deriving (Eq, Ord, Show)

type IFGraph v c = Gr (SetExpression v c) ConstraintEdge

data SolvedSystem v c = SolvedSystem { systemIFGraph :: IFGraph v c
                                     , systemSetToIdMap :: Map (SetExpression v c) Int
                                     , systemIdToSetMap :: Vector (SetExpression v c)
                                     }

-- | Compute the least solution for the given variable
--
-- LS(y) = All source nodes with a predecessor edge to y, plus LS(x)
-- for all x where x has a predecessor edge to y.
leastSolution :: forall c m v . (Failure (ConstraintError v c) m, Ord v, Ord c) => SolvedSystem v c -> v -> m [c]
leastSolution (SolvedSystem g m _) varLabel = do
  case M.lookup (SetVariable varLabel) m of
    Nothing -> failure ex
    Just nid -> return $ S.toList $ snd $ go nid (mempty, mempty)
  where
    ex :: ConstraintError v c
    ex = NoVariableLabel varLabel
    -- For the given nid, add all of the predecessor terms (with a
    -- pred edge label) to the result set.  Recursively invoke go on
    -- any predecessors (With pred edge labels) that are variables.
    go :: Int -> (Set Int, Set c) -> (Set Int, Set c)
    go nid acc@(visited, res)
      | nid `S.member` visited = acc
      | otherwise =
        let visited' = S.insert nid visited
            Just (Context ps _ _) = context g nid
            res' = foldr addTermPred res ps
            predVars = mapMaybe toPredVarId ps
        in foldr go (visited', res') predVars
    addTermPred :: (Int, ConstraintEdge) -> Set c -> Set c
    addTermPred (_, Succ) acc = acc
    addTermPred (nid, Pred) acc =
      case context g nid of
        Just (Context _ (LNode _ (Term t)) _) -> S.insert t acc
        _ -> acc
    toPredVarId :: (Int, ConstraintEdge) -> Maybe Int
    toPredVarId (_, Succ) = Nothing
    toPredVarId (nid, Pred) =
      case context g nid of
        Just (Context _ (LNode _ (SetVariable _)) _) -> Just nid
        _ -> Nothing

solveSystem :: (Failure (ConstraintError v c) m, Eq c, Eq v, Ord c, Ord v)
               => ConstraintSystem v c
               -> m (SolvedSystem v c)
solveSystem s = do
  s' <- simplifySystem s
  return $! constraintsToIFGraph s'

constraintsToIFGraph :: (Ord v, Ord c) => ConstraintSystem v c -> SolvedSystem v c
constraintsToIFGraph (ConstraintSystem is) =
  SolvedSystem { systemIFGraph = saturateGraph m v g0
               , systemSetToIdMap = m
               , systemIdToSetMap = v
               }
  where
    -- The initial graph has all of the nodes we need; after that we
    -- just need to saturate the edges through transitive closure
    (g0, m, v) = execState (buildInitialGraph is) (empty, mempty, mempty)

type BuilderMonad v c = State (IFGraph v c, Map (SetExpression v c) Int, Vector (SetExpression v c))

-- | Build an initial IF constraint graph that contains all of the
-- vertices and the edges induced by the initial simplified constraint
-- system.
buildInitialGraph :: (Ord v, Ord c) => [Inclusion v c] -> BuilderMonad v c ()
buildInitialGraph = mapM_ addInclusion

addInclusion :: (Eq c, Ord v, Ord c) => Inclusion v c -> BuilderMonad v c ()
addInclusion i =
  case i of
    -- This is the key to an inductive form graph (rather than
    -- standard form)
    e1@(SetVariable v1) :<= e2@(SetVariable v2) ->
      case compare v1 v2 of
        EQ -> error "Constraints.Set.Solver.addInclusion: invalid A ⊆ A constraint"
        LT -> addEdge Pred e1 e2
        GT -> addEdge Succ e1 e2
    e1@(Term _) :<= e2@(SetVariable _) -> addEdge Pred e1 e2
    e1@(SetVariable _) :<= e2@(Term _) -> addEdge Succ e1 e2
    _ -> error "Constraints.Set.Solver.addInclusion: unexpected expression"

-- | Add an edge in the constraint graph between the two expressions
-- with the given label.  Adds nodes for the expressions if necessary.
addEdge :: (Eq v, Eq c, Ord v, Ord c)
           => ConstraintEdge
           -> SetExpression v c
           -> SetExpression v c
           -> BuilderMonad v c ()
addEdge etype e1 e2 = do
  eid1 <- getEID e1
  eid2 <- getEID e2
  let edge = LEdge (Edge eid1 eid2) etype
  (g, m, v) <- get
  let g' = insEdge edge g
  put (g', m, v)

-- | Get the ID for the expression node.  Inserts a new node into the
-- graph if needed.
getEID :: (Ord v, Ord c) => SetExpression v c -> BuilderMonad v c Int
getEID e = do
  (g, m, v) <- get
  case M.lookup e m of
    Just i -> return i
    Nothing -> do
      let eid = V.length v
          v' = V.snoc v e
          m' = M.insert e eid m
          g' = insNode (LNode eid e) g
      put (g', m', v')
      return eid

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
                 => Map (SetExpression v c) Int
                 -> Vector (SetExpression v c)
                 -> IFGraph v c
                 -> IFGraph v c
saturateGraph m v g0 = closureEdges (S.fromList (nodes g0)) g0
  where
    simplify e a =
      let Just a' = simplifyInclusion e a
      in a'
    closureEdges ns g
      | S.null ns = g
      | otherwise =
        let nextEdges = F.foldl' (findEdge g) mempty ns
            inclusions = F.foldl' simplify [] nextEdges
        in case null inclusions of
          True -> g
          False ->
            let g' = foldr addToGraph g inclusions
                affectedNodes = S.fromList (nodes g)
            in closureEdges affectedNodes g'

    -- During optimization, modify this to compute affected nodes on
    -- the fly
    addToGraph i g =
      let (g', _, _) = execState (addInclusion i) (g, m, v)
      in g'

    findEdge g s l =
      let xs = filter isPred $ lsuc g l
          rs = filter isSucc $ concatMap (lsuc g . fst) xs
      in foldr (toNewInclusion g l . fst) s rs

    toNewInclusion g l r s =
      case edgeExists g (Edge l r) of
        Just _ -> s
        Nothing -> S.insert (V.unsafeIndex v l :<= V.unsafeIndex v r) s

isPred :: (Node (IFGraph v s), EdgeLabel (IFGraph v s)) -> Bool
isPred = (==Pred) . snd

isSucc :: (Node (IFGraph v s), EdgeLabel (IFGraph v s)) -> Bool
isSucc = (==Succ) . snd
