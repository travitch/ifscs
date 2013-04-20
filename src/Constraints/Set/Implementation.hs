{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, DeriveDataTypeable #-}
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
  leastSolution,
  -- * Debugging
  ConstraintEdge(..),
  solvedSystemGraphElems
  ) where

import Control.DeepSeq
import Control.Exception
import Control.Failure
import Control.Monad.State.Strict
import qualified Data.Graph.Interface as G
import Data.Graph.MutableDigraph
import Data.Graph.Algorithms.DFS
import Data.Hashable
import Data.List ( intercalate )
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Maybe ( catMaybes, mapMaybe )
import Data.Monoid
import Data.HashSet ( HashSet )
import qualified Data.HashSet as HS
import Data.Typeable
import Data.Vector.Persistent ( Vector )
import qualified Data.Vector.Persistent as V

import Constraints.Set.MapReduce


type Worklist = HashSet PredSegment

data ConstraintEdge = Succ | Pred
                    deriving (Eq, Ord, Show)

-- | Create a set expression representing the empty set
emptySet :: SetExpression v c
emptySet = EmptySet

-- | Create a set expression representing the universal set
universalSet :: SetExpression v c
universalSet = UniversalSet

-- | Create a new set variable with the given label
setVariable :: v -> SetExpression v c
setVariable = SetVariable

-- | Atomic terms have a label and arity zero.  This is a shortcut for
--
-- > term conLabel [] []
atom :: c -> SetExpression v c
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
term :: c -> [Variance] -> ([SetExpression v c] -> SetExpression v c)
term = ConstructedTerm

-- | Construct an inclusion relation between two set expressions.
--
-- This is equivalent to @se1 ⊆ se2@.
(<=!) :: SetExpression v c -> SetExpression v c -> Inclusion v c
(<=!) = (:<=)

-- | Tags to mark term arguments as covariant or contravariant.
data Variance = Covariant | Contravariant
              deriving (Eq, Ord, Show)

-- | Expressions in the language of set constraints.
data SetExpression v c = EmptySet
                       | UniversalSet
                       | SetVariable v
                       | ConstructedTerm c [Variance] [SetExpression v c]
                       deriving (Eq, Ord)

-- Fake instance because we never create new SetExpressions during
-- saturation.
instance NFData (SetExpression v c) where
  rnf _ = ()

instance NFData (Inclusion v c) where
  rnf (_ :<= _) = ()

instance (Show v, Show c) => Show (SetExpression v c) where
  show EmptySet = "∅"
  show UniversalSet = "U"
  show (SetVariable v) = show v
  show (ConstructedTerm c _ es) =
    concat [ show c, "("
           , intercalate ", " (map show es)
           , ")"
           ]

-- | An inclusion is a constraint of the form @se1 ⊆ se2@
data Inclusion v c = (SetExpression v c) :<= (SetExpression v c)
                   deriving (Eq, Ord)

instance (Show v, Show c) => Show (Inclusion v c) where
  show (lhs :<= rhs) = concat [ show lhs, " ⊆ ", show rhs ]

-- | The types of errors that can be encountered during constraint
-- resolution
data ConstraintError v c = NoSolution (Inclusion v c) -- ^ The system has no solution because of the given inclusion constraint
                         | NoVariableLabel v -- ^ When searching for a solution, the requested variable was not present in the constraint graph
                         deriving (Eq, Ord, Show, Typeable)

instance (Typeable v, Typeable c, Show v, Show c) => Exception (ConstraintError v c)

-- | Simplify one set expression.  The expression may be eliminated,
-- passed through unchanged, or split into multiple new expressions.
simplifyInclusion :: (Failure (ConstraintError v c) m, Eq v, Eq c)
                     => [Inclusion v c] -- ^ An accumulator list
                     -> Inclusion v c -- ^ The inclusion to be simplified
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

-- | Simplifies an inclusion taking variance into account; this is a
-- helper for 'simplifyInclusion' that deals with the variance of
-- constructed terms.  The key here is that contravariant inclusions
-- are /flipped/.
simplifyWithVariance :: (Failure (ConstraintError v c) m, Eq v, Eq c)
                        => [Inclusion v c]
                        -> (Variance, SetExpression v c, SetExpression v c)
                        -> m [Inclusion v c]
simplifyWithVariance acc (Covariant, se1, se2) =
  simplifyInclusion acc (se1 :<= se2)
simplifyWithVariance acc (Contravariant, se1, se2) =
  simplifyInclusion acc (se2 :<= se1)

-- | Simplify all of the inclusions in the initial constraint system.
simplifySystem :: (Failure (ConstraintError v c) m, Eq v, Eq c)
                  => [Inclusion v c]
                  -> m [Inclusion v c]
simplifySystem = foldM simplifyInclusion []

-- | The type used to represent that inductive form constraint graph
-- during saturation.  This form is more efficient to saturate.
type IFGraph = DenseDigraph () ConstraintEdge

-- | The type representing the inductive constraint graph after it has
-- been saturated.  This change in representations is used to make DFS
-- queries easier.
type SolvedGraph = DenseDigraph () ConstraintEdge

-- | The solved constraint system
data SolvedSystem v c =
  SolvedSystem { systemIFGraph :: SolvedGraph
               , systemSetToIdMap :: Map (SetExpression v c) Int
               , systemIdToSetMap :: Vector (SetExpression v c)
               }

instance (Eq v, Eq c) => Eq (SolvedSystem v c) where
  (SolvedSystem g1 m1 v1) == (SolvedSystem g2 m2 v2) =
    m1 == m2 && v1 == v2 && g1 == g2

-- | Compute the least solution for the given variable.  This can fail
-- if the requested variable is not present in the constraint system
-- (see 'ConstraintError').
--
-- LS(y) = All source nodes with a predecessor edge to y, plus LS(x)
-- for all x where x has a predecessor edge to y.
leastSolution :: forall c m v . (Failure (ConstraintError v c) m, Ord v, Ord c)
                 => SolvedSystem v c
                 -> v
                 -> m [SetExpression v c]
leastSolution (SolvedSystem g0 m v) varLabel = do
  case M.lookup (SetVariable varLabel) m of
    Nothing -> failure ex -- FIXME reverse all of the edges and use a
                          -- simpler graph structure
    Just nid -> return $ catMaybes $ xdfsWith G.pre' addTerm [nid] g0
  where
    ex :: ConstraintError v c
    ex = NoVariableLabel varLabel

    -- We only want to add ConstructedTerms to the output list
    addTerm :: G.Context SolvedGraph -> Maybe (SetExpression v c)
    addTerm (G.Context _ nid _ _) = do
      se <- V.index v nid
      case se of
        ConstructedTerm _ _ _ -> return se
        _ -> Nothing

-- | Simplify and solve the system of set constraints
solveSystem :: (Failure (ConstraintError v c) m, Eq c, Eq v, Ord c, Ord v)
               => [Inclusion v c]
               -> m (SolvedSystem v c)
solveSystem s = do
  s' <- simplifySystem s
  return $! constraintsToIFGraph s'

-- | The real worker to solve the system and convert from an IFGraph
-- to a SolvedGraph.
constraintsToIFGraph :: (Ord v, Ord c) => [Inclusion v c] -> SolvedSystem v c
constraintsToIFGraph is =
  SolvedSystem { systemIFGraph = G.mkGraph ns es
               , systemSetToIdMap = m
               , systemIdToSetMap = v
               }
  where
    s0 = BuilderState { exprIdMap = mempty
                      , idExprMap = mempty
                      , lruCache = Nothing -- LRU.newLRU (Just 10000)
                      }
    -- The initial graph has all of the nodes we need; after that we
    -- just need to saturate the edges through transitive closure
    (g, bs) = runState act s0
    act = do
      theGraph <- buildInitialGraph is
      BuilderState m0 v0 _ <- get
      put $ BuilderState m0 v0 (Just 0)
      saturateGraph theGraph
    BuilderState m v _ = bs
    ns = map (\nid -> (nid, ())) $ G.vertices g
    es = map (\(G.Edge s d l) -> (G.Edge s d l)) $ G.edges g

-- | Metadata used to construct the constraint graph from the initial
-- inclusion constraints.  This maps set expressions to unique Int
-- identifiers, which are faster to reference during saturation.  The
-- expressions themselves don't matter during saturation.
data BuilderState v c = BuilderState { exprIdMap :: Map (SetExpression v c) Int
                                     , idExprMap :: Vector (SetExpression v c)
                                     , lruCache :: Maybe Int -- LRU.LRU Int ()
                                     }

-- | The monadic environment in which the constraint graph is built
-- and solved.
-- type BuilderMonad v c = State (BuilderState v c)
type BuilderMonad v c = State (BuilderState v c)

-- | Build an initial IF constraint graph that contains all of the
-- vertices and the edges induced by the initial simplified constraint
-- system.
buildInitialGraph :: (Ord v, Ord c) => [Inclusion v c] -> BuilderMonad v c IFGraph
buildInitialGraph is = do
  res <- foldM (addInclusion True) (G.empty, mempty) is
  return (fst res)

-- | This is just a strict (and unboxed) pair representing an edge
-- being added to the worklist because it will be the base of a new
-- closure edge.
data PredSegment = PS {-# UNPACK #-} !Int {-# UNPACK #-} !Int
                 deriving (Eq, Ord)

instance Hashable PredSegment where
  hashWithSalt s (PS l r) =
    s `hashWithSalt` l `hashWithSalt` r

-- | Adds an inclusion to the constraint graph (adding vertices if
-- necessary).  Returns the set of nodes that are affected (and will
-- need more transitive edges).
addInclusion :: (Eq c, Ord v, Ord c)
                => Bool
                -> (IFGraph, Worklist)
                -> Inclusion v c
                -> BuilderMonad v c (IFGraph, Worklist)
addInclusion removeCycles acc i =
  case i of
    -- This is the key to an inductive form graph (rather than
    -- standard form)
    e1@(SetVariable v1) :<= e2@(SetVariable v2) ->
      case compare v1 v2 of
        EQ -> error "Constraints.Set.Solver.addInclusion: invalid A ⊆ A constraint"
        GT -> addEdge removeCycles acc Pred e1 e2
        LT -> addEdge removeCycles acc Succ e1 e2
    e1@(ConstructedTerm _ _ _) :<= e2@(SetVariable _) ->
      addEdge removeCycles acc Pred e1 e2
    e1@(SetVariable _) :<= e2@(ConstructedTerm _ _ _) ->
      addEdge removeCycles acc Succ e1 e2
    _ -> error "Constraints.Set.Solver.addInclusion: unexpected expression"


-- | Add an edge in the constraint graph between the two expressions
-- with the given label.  Adds nodes for the expressions if necessary.
addEdge :: (Eq v, Eq c, Ord v, Ord c)
           => Bool
           -> (IFGraph, Worklist)
           -> ConstraintEdge
           -> SetExpression v c
           -> SetExpression v c
           -> BuilderMonad v c (IFGraph, Worklist)
addEdge {-removeCycles-}_ acc@(!g0, !affected) etype e1 e2 = do
  (eid1, g1) <- getEID e1 g0
  (eid2, g2) <- getEID e2 g1
  case eid1 == eid2 || G.edgeExists g2 eid1 eid2 of
    True -> return acc
    False -> simpleAddEdge g2 affected etype eid1 eid2
--
--       do
--       -- b <- checkCycles
--       -- case b && removeCycles of
--       case False of
--         True -> tryCycleDetection removeCycles g2 affected etype eid1 eid2
--         False ->

-- | Add an edge without trying to detect new cycles
simpleAddEdge :: IFGraph -> Worklist -> ConstraintEdge -> Int -> Int -> BuilderMonad v c (IFGraph, Worklist)
simpleAddEdge g2 affected etype eid1 eid2 =
  case etype of
    Pred -> return (g3, HS.insert (PS eid1 eid2) affected)
    Succ -> return (g3, G.foldPre (addPredPred eid1) affected g3 eid1)
  where
    Just g3 = G.insertEdge eid1 eid2 etype g2
    addPredPred _ _ Succ acc = acc
    addPredPred eid pid Pred acc =
      HS.insert (PS pid eid) acc



-- | Get the ID for the expression node.  Inserts a new node into the
-- graph if needed.
getEID :: (Ord v, Ord c)
          => SetExpression v c
          -> IFGraph
          -> BuilderMonad v c (Int, IFGraph)
getEID e g = do
  BuilderState m v c <- get
  case M.lookup e m of
    -- Even if we find the ID for the expression, we have to check to
    -- see if the node has been renamed due to cycle elimination
    Just i -> return (i, g)
    Nothing -> do
      let eid = V.length v
          !v' = V.snoc v e
          !m' = M.insert e eid m
          !g' = G.insertVertex eid () g
      put $! BuilderState m' v' c
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
saturateGraph g0 = closureEdges es0 g0
  where
    -- Initialize the saturation worklist with all of the predecessor
    -- edges in the initial graph
    es0 = HS.fromList $ mapMaybe predToPredSeg $ G.edges g0
    predToPredSeg (G.Edge l r Pred) = return $ PS l r
    predToPredSeg _ = Nothing

    -- Here is our problem (possibly also related to the self loops
    -- appearing).  We find new edges with findEdge, which just
    -- consults adjacency links.  Some of these refer to old nodes
    -- that were eliminated?  Shouldn't...  But the edges identified
    -- might not exist (and will never exist because their endpoints
    -- are collapsed).
    closureEdges ns g
      | HS.null ns = return g
      | otherwise = do
        BuilderState _ v _ <- get
        let inclusions = mapReduceThresh 1024 ns (findAndSimplifyEdge v g) mappend mempty
        case null inclusions of
          True -> return g
          False -> do
            (g', affectedNodes) <- foldM (addInclusion True) (g, mempty) inclusions
            closureEdges affectedNodes g'

{-# INLINE findAndSimplifyEdge #-}
findAndSimplifyEdge :: (Eq v, Eq c)
                       => Vector (SetExpression v c)
                       -> IFGraph
                       -> PredSegment
                       -> [Inclusion v c]
findAndSimplifyEdge v g (PS l x) =
  G.foldSuc (toNewInclusion v g l) mempty g x

{-# INLINE toNewInclusion #-}
toNewInclusion :: (Eq v, Eq c)
                  => Vector (SetExpression v c)
                  -> IFGraph
                  -> Int
                  -> Int
                  -> ConstraintEdge
                  -> [Inclusion v c]
                  -> [Inclusion v c]
toNewInclusion _ _ _ _ Pred acc = acc
toNewInclusion v g l r Succ acc
  | G.edgeExists g l r = acc
  | otherwise =
    let incl = V.unsafeIndex v l :<= V.unsafeIndex v r
        Just incl' = simplifyInclusion [] incl
    in incl' ++ acc

solvedSystemGraphElems :: (Eq v, Eq c) => SolvedSystem v c -> ([(Int, SetExpression v c)], [(Int, Int, ConstraintEdge)])
solvedSystemGraphElems (SolvedSystem g _ v) = (ns, es)
  where
    ns = map (\nid -> (nid, V.unsafeIndex v nid)) $ G.vertices g
    es = map (\(G.Edge s d l) -> (s, d, l)) $ G.edges g


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
