{-# LANGUAGE
    BangPatterns
  , MultiWayIf
  , RecordWildCards
  , ScopedTypeVariables
  , ViewPatterns
  #-}

module SAT.Mios.Aha where

import Control.Monad (unless, void, when)
import Control.Lens
import Control.Monad.State
import Data.Bits
import Data.Foldable (foldrM)
import Data.Int
import SAT.Mios.Types
import SAT.Mios.MyClause
import SAT.Mios.ClauseManager
import SAT.Mios.MySolver
import SAT.Mios.ClausePool
import SAT.Mios.Criteria
import SAT.Mios.Util.StateT

simplify' :: MyClause -> StateT MySolver IO Bool
simplify' c = do
  let lits_stack = c ^. lits in
    return True
