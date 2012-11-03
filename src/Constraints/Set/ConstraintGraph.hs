{-# LANGUAGE BangPatterns #-}
-- | This is a very simple graph data structure.  It is less
-- featureful than FGL or hbgl, but the operations required for
-- saturation are faster and allocate much less memory.
--
-- The main changes are that it doesn't provide a @match@ operation
-- and it does provide in-place iteration over predecessor and
-- successor edges.
module Constraints.Set.ConstraintGraph (
  Graph,
  ConstraintEdge(..),
  emptyGraph,
  insNode,
  insEdge,
  numNodes,
  edgeExists,
  foldlPred,
  foldlSucc,
  removeNode,
  graphNodes,
  graphEdges
  ) where

import Data.IntMap ( IntMap )
import qualified Data.IntMap as IM
import Data.Monoid

data ConstraintEdge = Succ | Pred
                    deriving (Eq, Ord, Show)
-- Pred Succ
data Adj = Adj !(IntMap ConstraintEdge) !(IntMap ConstraintEdge)
type Gr = IntMap Adj

newtype Graph = Graph { unGraph :: Gr }

emptyAdj :: Adj
emptyAdj = Adj mempty mempty

emptyGraph :: Graph
emptyGraph = Graph mempty

insEdge :: Int -> Int -> ConstraintEdge -> Graph -> Graph
insEdge src dst lbl (Graph g) =
  let !g1 = IM.adjust (addSucc dst lbl) src g
      !g2 = IM.adjust (addPred src lbl) dst g1
  in Graph g2

addSucc :: Int -> ConstraintEdge -> Adj -> Adj
addSucc dst lbl (Adj ps ss) = Adj ps (IM.insert dst lbl ss)

addPred :: Int -> ConstraintEdge -> Adj -> Adj
addPred src lbl (Adj ps ss) = Adj (IM.insert src lbl ps) ss

insNode :: Int -> Graph -> Graph
insNode nid = Graph . IM.insert nid emptyAdj . unGraph

edgeExists :: Graph -> Int -> Int -> Bool
edgeExists (Graph g) src dst =
  case IM.lookup src g of
    Nothing -> False
    Just (Adj _ ss) -> IM.member dst ss

foldlPred :: (a -> Int -> ConstraintEdge -> a) -> a -> Graph -> Int -> a
foldlPred f seed (Graph g) nid =
  case IM.lookup nid g of
    Nothing -> seed
    Just (Adj ps _) -> IM.foldlWithKey' f seed ps

foldlSucc :: (a -> Int -> ConstraintEdge -> a) -> a -> Graph -> Int -> a
foldlSucc f seed (Graph g) nid =
  case IM.lookup nid g of
    Nothing -> seed
    Just (Adj _ ss) -> IM.foldlWithKey' f seed ss

removeNode :: Int -> Graph -> Graph
removeNode n g@(Graph g0) =
  case IM.lookup n g0 of
    Nothing -> g
    Just (Adj ps ss) ->
      let !g1 = IM.foldrWithKey' (\src _ -> IM.adjust (removeSucc n) src) g0 ps
          !g2 = IM.foldrWithKey' (\dst _ -> IM.adjust (removePred n) dst) g1 ss
      in Graph $ IM.delete n g2

removeSucc :: Int -> Adj -> Adj
removeSucc n (Adj ps ss) = Adj ps (IM.delete n ss)

removePred :: Int -> Adj -> Adj
removePred n (Adj ps ss) = Adj (IM.delete n ps) ss

numNodes :: Graph -> Int
numNodes = IM.size . unGraph

graphNodes :: Graph -> [(Int, ())]
graphNodes (Graph g) = zip (IM.keys g) (repeat ())

graphEdges :: Graph -> [(Int, Int, ConstraintEdge)]
graphEdges = IM.foldrWithKey edgesForNode [] . unGraph
  where
    edgesForNode nid (Adj _ ss) acc =
      IM.foldrWithKey (mkEdge nid) acc ss
    mkEdge srcid dstid lbl acc = (srcid, dstid, lbl) : acc
