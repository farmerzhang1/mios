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
import SAT.Mios.Util.StateT
import SAT.Mios.ClauseManager

type MyClauseVector = MV.IOVector (Maybe MyClause)

data MyClause = MyClause {
    _lits       :: !Stack    -- ^ literals and rank
  , _rank       :: !Int      -- ^ another metrics of this clause
  , _activity   :: !Double   -- ^ activity of this clause
--            , protected  :: !Bool'    -- ^ protected from reduce
  } -- | MyNullClause                              -- as null pointer

newClauseVector'  :: Int -> IO MyClauseVector
newClauseVector' n = do
  v <- MV.new (max 4 n)
  MV.set v Nothing
  return v

makeLenses ''MyClause
instance Eq MyClause where
  {-# SPECIALIZE INLINE (==) :: MyClause -> MyClause -> Bool #-}
  (==) x y = x `seq` y `seq` (tagToEnum# (reallyUnsafePtrEquality# x y) :: Bool)

instance Show MyClause where
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
    _nActives     :: Int                          -- number of active clause
  , _purged       :: Bool                         -- whether it needs gc
  , _clauseVector :: R.IORef MyClauseVector           -- clause list
  , _keyVector    :: R.IORef (Vec Int)              -- Int list
  }
makeLenses ''MyClauseManager

shrinkBy' :: Int -> StateT MyClauseManager IO ()
shrinkBy' k = do
  nActives -= k

pushTo :: Maybe MyClause -> StateT MyClauseManager IO ()
pushTo clause = do
  n <- get'' nActives
  v <- readIORef clauseVector
  b <- readIORef keyVector
  if MV.length v -1 <= n
  then do
    let len = max 8 $ div (MV.length v) 2
    v' <- liftIO $ MV.unsafeGrow v len
    b' <- liftIO $ growBy b len
    MV.unsafeWrite v' n clause
    writeIORef clauseVector v'
    writeIORef keyVector b'
  else do
    -- TODO
  nActives += 1
  return ()

  -- | returns a new instance.
newManager' :: Int -> IO MyClauseManager
newManager' initialSize = do
  v <- newClauseVector' initialSize
  b <- newVec (MV.length v) 0
  MyClauseManager 0 False <$> R.newIORef v <*> R.newIORef b
  -- | returns the internal 'C.ClauseVector'.

getClauseVector' :: MyClauseManager -> IO MyClauseVector
getClauseVector' m = R.readIORef (_clauseVector m)

-- instance VecFamily MyClauseManager (Maybe MyClause) where
--   getNth = error "no getNth method for my clause manager"
--   setNth = error "no setNth method for my clause manager"
--   {-# SPECIALIZE INLINE reset :: MyClauseManager -> IO () #-}
--   reset m = SAT.Mios.Types.set' (_nActives m) 0
reset' :: StateT MyClauseManager IO ()
reset' = nActives .= 0
instance VecFamily MyClauseVector (Maybe MyClause) where -- TODO

type MyWatcherList = V.Vector MyClauseManager

pushClauseWithKey :: Maybe MyClause -> Lit -> StateT MyClauseManager IO ()
pushClauseWithKey c k = do
  -- checkConsistency m c
  n <- use nActives
  v <- readIORef clauseVector
  b <- readIORef keyVector
  if MV.length v - 1 <= n
    then do
        let len = max 8 $ div (MV.length v) 2
        v' <- MV.unsafeGrow v len
        b' <- liftIO $ growBy b len
        MV.unsafeWrite v' n c
        setNthWithState b' n k
        writeIORef clauseVector v'
        writeIORef keyVector b'
    else liftIO $ MV.unsafeWrite v n c >> setNth b n k
  -- modify' _nActives (1 +)
  nActives += 1
