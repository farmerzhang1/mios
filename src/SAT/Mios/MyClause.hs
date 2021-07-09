-- | (This is a part of MIOS.)
-- MyClause, supporting pointer-based equality
{-# LANGUAGE
    FlexibleInstances
  , MagicHash
  , MultiParamTypeClasses
  , RecordWildCards
  , ViewPatterns
  , TemplateHaskell
  #-}
module SAT.Mios.MyClause where
import GHC.Prim (tagToEnum#, reallyUnsafePtrEquality#)
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import qualified Data.IORef as R
import SAT.Mios.Types
import Control.Lens
import Control.Monad (unless, when)
import Control.Monad.State

type ClauseVector = MV.IOVector MyClause

data MyClause = MyClause
              {
                _lits       :: !Stack    -- ^ literals and rank
              , _rank       :: !Int      -- ^ another metrics of this clause
              , _activity   :: !Double   -- ^ activity of this clause
--            , protected  :: !Bool'    -- ^ protected from reduce
              }
  | MyNullClause                              -- as null pointer
makeLensesFor [("_lits", "lits"), ("_rank", "rank"), ("_activity", "activity")] ''MyClause
instance Eq MyClause where
  {-# SPECIALIZE INLINE (==) :: MyClause -> MyClause -> Bool #-}
  (==) x y = x `seq` y `seq` (tagToEnum# (reallyUnsafePtrEquality# x y) :: Bool)

instance Show MyClause where
  show MyNullClause = "my NullClause"
  show _ = "a clause"

{-# INLINABLE newClauseFromStack #-}
newClauseFromStack :: Bool -> Stack -> IO MyClause
newClauseFromStack l vec = do
  n <- get' vec
  v <- newStack (n + 1)
  let loop ((<= n) -> False) = return ()
      loop i = (setNth v i =<< getNth vec i) >> loop (i + 1)
  loop 0
  return (MyClause v (if l then 1 else 0) 0.0)

data MyClauseManager = MyClauseManager
  {
    _nActives     :: !Int                          -- number of active clause
  , _purged       :: !Bool                         -- whether it needs gc
  , _clauseVector :: R.IORef ClauseVector           -- clause list
  , _keyVector    :: R.IORef (Vec Int)              -- Int list
  }
makeLenses ''MyClauseManager

shrinkBy :: Int -> StateT MyClauseManager IO ()
shrinkBy k = do
    nActives -= k