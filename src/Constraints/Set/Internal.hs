-- | This module exposes some internals useful for testing purposes.
-- The interface exported by this module is not stable and should not
-- be relied on for anything substantial.  It is subject to change
-- without notice.
module Constraints.Set.Internal (
  ConstraintEdge(..),
  solvedSystemGraphElems
  ) where

import Constraints.Set.Implementation
