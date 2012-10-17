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

import Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as HM
import Data.Monoid

-- Pred Succ
data Adj e = Adj (HashMap Int e) (HashMap Int e)
type Gr e = HashMap Int (Adj e)

newtype Graph e = Graph { unGraph :: Gr e }

emptyAdj :: Adj e
emptyAdj = Adj mempty mempty

emptyGraph :: Graph e
emptyGraph = Graph mempty

insEdge :: Int -> Int -> e -> Graph e -> Graph e
insEdge src dst lbl (Graph g) =
  let g1 = HM.adjust (addSucc dst lbl) src g
      g2 = HM.adjust (addPred src lbl) dst g1
  in Graph g2

addSucc :: Int -> e -> Adj e -> Adj e
addSucc dst lbl (Adj ps ss) = Adj ps (HM.insert dst lbl ss)

addPred :: Int -> e -> Adj e -> Adj e
addPred src lbl (Adj ps ss) = Adj (HM.insert src lbl ps) ss

insNode :: Int -> Graph e -> Graph e
insNode nid = Graph . HM.insert nid emptyAdj . unGraph

edgeExists :: Graph e -> Int -> Int -> Bool
edgeExists (Graph g) src dst =
  case HM.lookup src g of
    Nothing -> False
    Just (Adj _ ss) -> HM.member dst ss

foldlPred :: (a -> Int -> e -> a) -> a -> Graph e -> Int -> a
foldlPred f seed (Graph g) nid =
  case HM.lookup nid g of
    Nothing -> seed
    Just (Adj ps _) -> HM.foldlWithKey' f seed ps

foldlSucc :: (a -> Int -> e -> a) -> a -> Graph e -> Int -> a
foldlSucc f seed (Graph g) nid =
  case HM.lookup nid g of
    Nothing -> seed
    Just (Adj _ ss) -> HM.foldlWithKey' f seed ss

nodes :: Graph e -> [Int]
nodes = HM.keys . unGraph

graphNodes :: Graph e -> [(Int, ())]
graphNodes (Graph g) = zip (HM.keys g) (repeat ())

graphEdges :: Graph e -> [(Int, Int, e)]
graphEdges = HM.foldrWithKey edgesForNode [] . unGraph
  where
    edgesForNode nid (Adj _ ss) acc =
      HM.foldrWithKey (mkEdge nid) acc ss
    mkEdge srcid dstid lbl acc = (srcid, dstid, lbl) : acc
