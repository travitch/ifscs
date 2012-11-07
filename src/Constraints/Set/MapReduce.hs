{-# LANGUAGE BangPatterns #-}
module Constraints.Set.MapReduce ( mapReduceThresh ) where

import Control.DeepSeq
import Control.Monad.Par.Scheds.Direct
import Data.Foldable ( Foldable )
import qualified Data.Foldable as F
import qualified Data.Sequence as S

mapReduceThresh :: (Foldable f, NFData b)
                   => Int -- ^ Threshold to start serial computation
                   -> f a -- ^ A foldable sequence of elements to map over
                   -> (a -> b) -- ^ A map operation to apply
                   -> (b -> b -> b) -- ^ Combine results
                   -> b -- ^ Seed value
                   -> b
mapReduceThresh thresh elts fn red seed =
  runPar $ go s0
  where
    s0 = S.fromList (F.toList elts)
    mapred !a !b = fn b `red` a
    go s
      | S.length s <= thresh =
        return $ F.foldl' mapred seed s

      | otherwise = do
          let mid = S.length s `quot` 2
              (p1, p2) = S.splitAt mid s
          rpart <- spawn $ go p2
          l <- go p1
          r <- get rpart
          return $ red l r
