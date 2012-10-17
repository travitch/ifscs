module Constraints.Set.ConstraintGraph (
  Graph,
  emptyGraph,
  insNode,
  insEdge,
  nodes,
  edgeExists,
  foldlPred,
  foldlSucc,
  graphNodes,
  graphEdges
  ) where

import Data.IntMap ( IntMap )
import qualified Data.IntMap as IM
import Data.Monoid

-- Pred Succ
data Adj e = Adj (IntMap e) (IntMap e)
type Gr e = IntMap (Adj e)

newtype Graph e = Graph { unGraph :: Gr e }

emptyAdj :: Adj e
emptyAdj = Adj mempty mempty

emptyGraph :: Graph e
emptyGraph = Graph mempty

insEdge :: Int -> Int -> e -> Graph e -> Graph e
insEdge src dst lbl (Graph g) =
  let g1 = IM.adjust (addSucc dst lbl) src g
      g2 = IM.adjust (addPred src lbl) dst g1
  in Graph g2

addSucc :: Int -> e -> Adj e -> Adj e
addSucc dst lbl (Adj ps ss) = Adj ps (IM.insert dst lbl ss)

addPred :: Int -> e -> Adj e -> Adj e
addPred src lbl (Adj ps ss) = Adj (IM.insert src lbl ps) ss

insNode :: Int -> Graph e -> Graph e
insNode nid = Graph . IM.insert nid emptyAdj . unGraph

edgeExists :: Graph e -> Int -> Int -> Bool
edgeExists (Graph g) src dst =
  case IM.lookup src g of
    Nothing -> False
    Just (Adj _ ss) -> IM.member dst ss

foldlPred :: (a -> Int -> e -> a) -> a -> Graph e -> Int -> a
foldlPred f seed (Graph g) nid =
  case IM.lookup nid g of
    Nothing -> seed
    Just (Adj ps _) -> IM.foldlWithKey' f seed ps

foldlSucc :: (a -> Int -> e -> a) -> a -> Graph e -> Int -> a
foldlSucc f seed (Graph g) nid =
  case IM.lookup nid g of
    Nothing -> seed
    Just (Adj _ ss) -> IM.foldlWithKey' f seed ss

nodes :: Graph e -> [Int]
nodes = IM.keys . unGraph

graphNodes :: Graph e -> [(Int, ())]
graphNodes (Graph g) = zip (IM.keys g) (repeat ())

graphEdges :: Graph e -> [(Int, Int, e)]
graphEdges = IM.foldrWithKey edgesForNode [] . unGraph
  where
    edgesForNode nid (Adj _ ss) acc =
      IM.foldrWithKey (mkEdge nid) acc ss
    mkEdge srcid dstid lbl acc = (srcid, dstid, lbl) : acc
