{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE BangPatterns #-}
module Constraints.Set.Implementation (
  ConstraintError(..),
  Variance(..),
  Inclusion,
  SetExpression(..),
  SolvedSystem,
  emptySet,
  universalSet,
  setVariable,
  atom,
  term,
  (<=!),
  solveSystem,
  leastSolution
  ) where

import Control.Exception
import Control.Failure
import qualified Data.Foldable as F
import Data.Function ( on )
import qualified Data.List as L
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Maybe ( fromMaybe )
import Data.Monoid
import Data.Set ( Set )
import qualified Data.Set as S
import Data.Typeable

type Worklist v c = Set (PredSegment v c)

-- | The type used to represent that inductive form constraint graph
-- during saturation.  This form is more efficient to saturate.
type IFGraph v c = Map (SetExpression v c) (Edges v c)

data Edges v c = Edges { predecessors :: Set (SetExpression v c)
                       , successors :: Set (SetExpression v c)
                       }
               deriving (Eq, Ord)

-- | The solved constraint system
data SolvedSystem v c =
  SolvedSystem { systemIFGraph :: IFGraph v c  }

instance (Eq v, Eq c) => Eq (SolvedSystem v c) where
  (==) = (==) `on` systemIFGraph


-- | A type describing an edge added in one iteration of the
-- transitive closure.  These let us know which nodes need to be
-- revisited in the next iteration (and in which direction -
-- predecessor or successor)
data PredSegment v c = PSPred (SetExpression v c) (SetExpression v c)
                     | PSSucc (SetExpression v c) (SetExpression v c)
                     deriving (Eq, Ord)

-- | Create a set expression representing the empty set
emptySet :: SetExpression v c
emptySet = EmptySet

-- | Create a set expression representing the universal set
universalSet :: SetExpression v c
universalSet = UniversalSet

-- | Create a new set variable with the given label
setVariable :: (Ord v) => v -> SetExpression v c
setVariable = SetVariable

-- | Atomic terms have a label and arity zero.  This is a shortcut for
--
-- > term conLabel [] []
atom :: (Ord c) => c -> SetExpression v c
atom conLabel = ConstructedTerm conLabel [] []

-- | This returns a function to create terms from lists of
-- SetExpressions.  It is meant to be partially applied so that as
-- many terms as possible can share the same reference to a label and
-- signature.
--
-- The list of variances specifies the variance (Covariant or
-- Contravariant) for each argument of the term.  A mismatch in the
-- length of the variance descriptor and the arguments to the term
-- will result in a run-time error.
term :: (Ord v, Ord c) => c -> [Variance] -> ([SetExpression v c] -> SetExpression v c)
term = ConstructedTerm

-- | Construct an inclusion relation between two set expressions.
--
-- This is equivalent to @se1 ⊆ se2@.
(<=!) :: (Ord c, Ord v) => SetExpression v c -> SetExpression v c -> Inclusion v c
(<=!) = Inclusion

-- | Tags to mark term arguments as covariant or contravariant.
data Variance = Covariant | Contravariant
              deriving (Eq, Ord, Show)

-- | Expressions in the language of set constraints.
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
           , L.intercalate ", " (map show es)
           , ")"
           ]

-- | An inclusion is a constraint of the form @se1 ⊆ se2@
data Inclusion v c =
  Inclusion (SetExpression v c) (SetExpression v c)
  deriving (Eq, Ord)



instance (Show v, Show c) => Show (Inclusion v c) where
  show (Inclusion lhs rhs) = concat [ show lhs, " ⊆ ", show rhs ]

-- | The types of errors that can be encountered during constraint
-- resolution
data ConstraintError v c = NoSolution (Inclusion v c) -- ^ The system has no solution because of the given inclusion constraint
                         | NoVariableLabel v -- ^ When searching for a solution, the requested variable was not present in the constraint graph
                         deriving (Eq, Ord, Show, Typeable)

instance (Typeable v, Typeable c, Show v, Show c) => Exception (ConstraintError v c)

-- | Simplify one set expression.  The expression may be eliminated,
-- passed through unchanged, or split into multiple new expressions.
simplifyInclusion :: (Ord c, Ord v, Eq v, Eq c)
                     => Inclusion v c -- ^ The inclusion to be simplified
                     -> [Inclusion v c]
simplifyInclusion i =
  case i of
    -- Eliminate constraints of the form A ⊆ A
    Inclusion (SetVariable v1) (SetVariable v2) ->
      if v1 == v2 then [] else [i]
    Inclusion UniversalSet EmptySet ->
      error "Malformed constraint univ < emptyset"
    Inclusion (ConstructedTerm c1 s1 ses1) (ConstructedTerm c2 s2 ses2) ->
      let sigLen = length s1
          triples = zip3 s1 ses1 ses2
      in case c1 == c2 && s1 == s2 && sigLen == length ses1 && sigLen == length ses2 of
        False -> error "Malformed constraint cterm mismatch"
        True -> concatMap simplifyWithVariance triples
    Inclusion UniversalSet (ConstructedTerm _ _ _) ->
      error "Malformed constraint univ < cterm"
    Inclusion (ConstructedTerm _ _ _) EmptySet ->
      error "Malformed constraint cterm < emptyset"
    -- Eliminate constraints of the form A ⊆ 1
    Inclusion _ UniversalSet -> []
    -- 0 ⊆ A
    Inclusion EmptySet _ -> []
    -- Keep anything else (atomic forms)
    _ -> [i]

-- | Simplifies an inclusion taking variance into account; this is a
-- helper for 'simplifyInclusion' that deals with the variance of
-- constructed terms.  The key here is that contravariant inclusions
-- are /flipped/.
simplifyWithVariance :: (Ord c, Ord v, Eq v, Eq c)
                        => (Variance, SetExpression v c, SetExpression v c)
                        -> [Inclusion v c]
simplifyWithVariance (Covariant, se1, se2) =
  simplifyInclusion (Inclusion se1 se2)
simplifyWithVariance (Contravariant, se1, se2) =
  simplifyInclusion (Inclusion se2 se1)

-- | Simplify all of the inclusions in the initial constraint system.
simplifySystem :: (Ord c, Ord v, Eq v, Eq c)
                  => [Inclusion v c]
                  -> [Inclusion v c]
simplifySystem = concatMap simplifyInclusion

dfs :: (Ord c, Ord v) => IFGraph v c -> SetExpression v c -> Set (SetExpression v c)
dfs g = go mempty
  where
    go !visited v
      | S.member v visited = visited
      | otherwise =
          case M.lookup v g of
            Nothing -> visited
            Just Edges { predecessors = ps } ->
              F.foldl' go (S.union ps visited) ps

-- | Compute the least solution for the given variable.  This can fail
-- if the requested variable is not present in the constraint system
-- (see 'ConstraintError').
--
-- LS(y) = All source nodes with a predecessor edge to y, plus LS(x)
-- for all x where x has a predecessor edge to y.
leastSolution :: (Failure (ConstraintError v c) m, Ord v, Ord c)
                 => SolvedSystem v c
                 -> v
                 -> m [SetExpression v c]
leastSolution (SolvedSystem g0) varLabel = do
  let reached = dfs g0 (SetVariable varLabel)
  return $ F.foldr addTerm [] reached
  where
    -- ex :: ConstraintError v c
    -- ex = NoVariableLabel varLabel

    addTerm v acc =
      case v of
        ConstructedTerm _ _ _ -> v : acc
        _ -> acc

-- | Simplify and solve the system of set constraints
solveSystem :: (Failure (ConstraintError v c) m, Eq c, Eq v, Ord c, Ord v)
               => [Inclusion v c]
               -> m (SolvedSystem v c)
solveSystem = return . constraintsToIFGraph . simplifySystem

-- | The real worker to solve the system and convert from an IFGraph
-- to a SolvedGraph.
constraintsToIFGraph :: (Ord v, Ord c) => [Inclusion v c] -> SolvedSystem v c
constraintsToIFGraph is =
  SolvedSystem { systemIFGraph = saturateGraph g0 wl }
  where
    (g0, wl) = buildInitialGraph is

-- | Build an initial IF constraint graph that contains all of the
-- vertices and the edges induced by the initial simplified constraint
-- system.
buildInitialGraph :: (Ord v, Ord c)
                     => [Inclusion v c]
                     -> (IFGraph v c, Worklist v c)
buildInitialGraph is = L.foldl' addInclusion (mempty, mempty) is

-- | Adds an inclusion to the constraint graph (adding vertices if
-- necessary).  Returns the set of nodes that are affected (and will
-- need more transitive edges).
addInclusion :: (Eq c, Ord v, Ord c)
                => (IFGraph v c, Worklist v c)
                -> Inclusion v c
                -> (IFGraph v c, Worklist v c)
addInclusion acc i =
  case i of
    -- This is the key to an inductive form graph (rather than
    -- standard form)
    Inclusion e1@(SetVariable v1) e2@(SetVariable v2)
      | v1 < v2 -> addSuccEdge acc e1 e2
      | otherwise -> addPredEdge acc e1 e2
    Inclusion e1@(ConstructedTerm _ _ _) e2@(SetVariable _) ->
      addPredEdge acc e1 e2
    Inclusion e1@(SetVariable _) e2@(ConstructedTerm _ _ _) ->
      addSuccEdge acc e1 e2
    _ -> error "Constraints.Set.Solver.addInclusion: unexpected expression"

-- | Add a predecessor edge (l is a predecessor of r)
addPredEdge :: (Ord c, Ord v)
               => (IFGraph v c, Worklist v c)
               -> SetExpression v c
               -> SetExpression v c
               -> (IFGraph v c, Worklist v c)
addPredEdge acc@(!g, !work) l r =
  case M.lookup r g of
    Nothing ->
      let es = Edges { predecessors = S.singleton l, successors = S.empty }
      in (M.insert r es g, S.insert (PSPred l r) work)
    Just es
      | S.member l (predecessors es) -> acc
      | otherwise ->
        let es' = es { predecessors = S.insert l (predecessors es) }
        in (M.insert r es' g, S.insert (PSPred l r) work)

addSuccEdge :: (Ord c, Ord v)
               => (IFGraph v c, Worklist v c)
               -> SetExpression v c
               -> SetExpression v c
               -> (IFGraph v c, Worklist v c)
addSuccEdge acc@(!g, !work) l r =
  case M.lookup l g of
    Nothing ->
      let es = Edges { predecessors = S.empty, successors = S.singleton r }
      in (M.insert l es g, S.insert (PSSucc l r) work)
    Just es
      | S.member r (successors es) -> acc
      | otherwise ->
        let es' = es { successors = S.insert r (successors es) }
        in (M.insert l es' g, S.insert (PSSucc l r) work)

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
saturateGraph :: (Ord v, Ord c, Eq c)
                 => IFGraph v c
                 -> Worklist v c
                 -> IFGraph v c
saturateGraph g0 wl0 =
  let (g1, wl1) = F.foldl' addNewEdges (g0, mempty) wl0
  in if S.null wl1 then g1 else saturateGraph g1 wl1

addNewEdges :: (Ord v, Ord c)
               => (IFGraph v c, Worklist v c)
               -> PredSegment v c
               -> (IFGraph v c, Worklist v c)
addNewEdges acc@(!g0, _) (PSPred l r) = fromMaybe acc $ do
  Edges { successors = ss } <- M.lookup r g0
  return $ F.foldl' (addNewInclusions l) acc ss
  where
    addNewInclusions lhs a rhs =
      F.foldl' addInclusion a $ simplifyInclusion (Inclusion lhs rhs)
addNewEdges acc@(!g0, _) (PSSucc l r) = fromMaybe acc $ do
  Edges { predecessors = ps } <- M.lookup l g0
  return $ F.foldl' (addNewInclusions r) acc ps
  where
    addNewInclusions rhs a lhs =
      F.foldl' addInclusion a $ simplifyInclusion (Inclusion lhs rhs)


-- Cycle detection

{-

-- Track both a visited set and a "the nodes on the cycle" set
checkChain :: Bool -> ConstraintEdge -> IFGraph -> Int -> Int -> Maybe IntSet
checkChain False _ _ _ _ = Nothing
checkChain True tgt g from to = do
  chain <- snd $ checkChainWorker (mempty, Nothing) tgt g from to
  return $ IS.insert from chain

-- Only checkChainWorker adds things to the visited set
checkChainWorker :: (IntSet, Maybe IntSet) -> ConstraintEdge -> IFGraph -> Int -> Int -> (IntSet, Maybe IntSet)
checkChainWorker (visited, chain) tgt g from to
  | from == to = (visited, Just (IS.singleton to))
  | otherwise =
    let visited' = IS.insert from visited
    in G.foldPre (checkChainEdges tgt g to) (visited', chain) g from

-- Once we have a branch of the DFS that succeeds, just keep that
-- value.  This manages augmenting the set of nodes on the chain
checkChainEdges :: ConstraintEdge
                   -> IFGraph
                   -> Int
                   -> Int
                   -> ConstraintEdge
                   -> (IntSet, Maybe IntSet)
                   -> (IntSet, Maybe IntSet)
checkChainEdges _ _ _ _ _ acc@(_, Just _) = acc
checkChainEdges tgt g to v lbl acc@(visited, Nothing)
  | tgt /= lbl = acc
  | IS.member v visited = acc
  | otherwise =
    -- If there was no hit on this branch, just return the accumulator
    -- from the recursive call (which has an updated visited set)
    case checkChainWorker acc tgt g v to of
      acc'@(_, Nothing) -> acc'
      (visited', Just chain) -> (visited', Just (IS.insert v chain))

-- | Ask if we should bother to check for cycles this iteration
checkCycles :: BuilderMonad v c Bool
checkCycles = do
  BuilderState _ _ cnt <- get
  case cnt of
    Nothing -> return True
    Just c -> return $ c <= 1000

-- FIXME: Maybe try to mark nodes as "exhausted" after they can't induce
-- any new edges?
--
-- Also, perhaps use bitmasks instead of sets for something?

-- | Try to detect cycles as in FFSA98.  Note that this is currently
-- broken somehow.  It detects cycles just fine, but removing them
-- seems to damage the constraint graph somehow making the solving
-- phase much slower.
tryCycleDetection :: (Ord c, Ord v) => Bool -> IFGraph
                     -> Worklist -> ConstraintEdge
                     -> Int -> Int -> BuilderMonad v c (IFGraph, Worklist)
tryCycleDetection _ g2 affected Succ eid1 eid2 = simpleAddEdge g2 affected Succ eid1 eid2
tryCycleDetection removeCycles g2 affected etype eid1 eid2 =
  case checkChain removeCycles (otherLabel etype) g2 eid1 eid2 of
    Just chain | not (IS.null chain) -> do
      -- Make all of the nodes in the cycle refer to the min element
      -- (the reference bit is taken care of in the node lookup and in
      -- the result lookup).
      --
      -- For each of the nodes in @rest@, repoint their incoming and
      -- outgoing edges.
      BuilderState m v c <- get
      -- Find all of the edges from any node pointing to a node in
      -- @rest@.  Also find all edges from @rest@ out into the rest of
      -- the graph.  Then resolve those back to inclusions using @v@
      -- and call addInclusion over these new inclusions (after
      -- blowing away the old ones)
      let (representative, rest) = IS.deleteFindMin chain
          thisExp = V.unsafeIndex v representative
          newIncoming = IS.foldr' (srcsOf g2 v chain thisExp) [] rest
          newInclusions = IS.foldr' (destsOf g2 v chain thisExp) newIncoming rest
          g3 = IS.foldr' G.removeVertex g2 rest
          m' = IS.foldr' (replaceWith v representative) m rest
      put $! BuilderState m' v (fmap (+1) c)
      foldM (addInclusion False) (g3, affected) newInclusions --  `debug`
        -- ("Removing " ++ show (IS.size chain) ++ " cycle (" ++ show eid1 ++
        --  " to " ++ show eid2 ++ "). " ++ show (CG.numNodes g3) ++
        --  " nodes left in the graph.")
      -- Nothing was affected because we didn't add any edges
    _ -> simpleAddEdge g2 affected etype eid1 eid2
  where
    otherLabel Succ = Pred
    otherLabel Pred = Succ

srcsOf :: IFGraph -> Vector (SetExpression v c) -> IntSet
          -> SetExpression v c -> Int -> [Inclusion v c]
          -> [Inclusion v c]
srcsOf g v chain newDst oldId acc =
  G.foldPre (\srcId _ a ->
              case IS.member srcId chain of
                True -> a
                False -> (V.unsafeIndex v srcId :<= newDst) : a) acc g oldId

destsOf :: IFGraph -> Vector (SetExpression v c) -> IntSet
          -> SetExpression v c -> Int -> [Inclusion v c]
          -> [Inclusion v c]
destsOf g v chain newSrc oldId acc =
  G.foldSuc (\dstId _ a ->
              case IS.member dstId chain of
                True -> a
                False -> (newSrc :<= V.unsafeIndex v dstId) : a) acc g oldId

-- | Change the ID of the node with ID @i@ to @repr@
replaceWith :: (Ord k) => Vector k -> a -> Int -> Map k a -> Map k a
replaceWith v repr i m =
  case M.lookup se m of
    Nothing -> m
    Just _ -> M.insert se repr m
  where
    se = V.unsafeIndex v i

-}
