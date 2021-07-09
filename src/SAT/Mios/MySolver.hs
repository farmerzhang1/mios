{-# LANGUAGE
    MultiWayIf
  , RecordWildCards
  , ScopedTypeVariables
  , TupleSections
  , ViewPatterns
  , TemplateHaskell
  #-}
module SAT.Mios.MySolver where
import Control.Monad (unless, when)
import Control.Monad.State
import Data.List (intercalate)
import Numeric (showFFloat)
import SAT.Mios.Solver
    ( StatIndex(EndOfStatIndex), VarHeap (..), newVarHeap, decisionLevel )
import SAT.Mios.Types
import SAT.Mios.Clause
import SAT.Mios.ClauseManager
import SAT.Mios.ClausePool
import Control.Lens
import SAT.Mios.Util.StateT
data MySolver = MySolver
              {
                -------- Database
                _clauses     :: !ClauseExtManager  -- ^ List of problem constraints.
              , _learnts     :: !ClauseExtManager  -- ^ List of learnt clauses.
              , _watches     :: !WatcherList       -- ^ list of constraint wathing 'p', literal-indexed
                -------- Assignment Management
              , _assigns     :: !(Vec Int)         -- ^ The current assignments indexed on variables
              , _phases      :: !(Vec Int)         -- ^ The last assignments indexed on variables
              , _trail       :: !Stack             -- ^ List of assignments in chronological order
              , _trailLim    :: !Stack             -- ^ Separator indices for different decision levels in 'trail'.
              , _qHead       :: !Int              -- ^ 'trail' is divided at qHead; assignment part and queue part
              , _reason      :: !ClauseVector      -- ^ For each variable, the constraint that implied its value
              , _level       :: !(Vec Int)         -- ^ For each variable, the decision level it was assigned
              , _ndd         :: !(Vec Int)         -- ^ For each variable, the number of depending decisions
              , _conflicts   :: !Stack             -- ^ Set of literals in the case of conflicts
                -------- Variable Order
              , _activities  :: !(Vec Double)      -- ^ Heuristic measurement of the activity of a variable
              , _order       :: !VarHeap           -- ^ Keeps track of the dynamic variable order.
                -------- Configuration
              , _config      :: !MiosConfiguration -- ^ search paramerters
              , _nVars       :: !Int               -- ^ number of variables
              , _claInc      :: !Double           -- ^ Clause activity increment amount to bump with.
              , _varInc      :: !Double           -- ^ Variable activity increment amount to bump with.
              , _rootLevel   :: !Int              -- ^ Separates incremental and search assumptions.
                -------- DB Size Adjustment
              , _learntSAdj  :: Double            -- ^ used in 'SAT.Mios.Main.search'
              , _learntSCnt  :: Int               -- ^ used in 'SAT.Mios.Main.search'
              , _maxLearnts  :: Double            -- ^ used in 'SAT.Mios.Main.search'
                -------- Working Memory
              , _ok          :: !Int              -- ^ internal flag
              , _an'seen     :: !(Vec Int)         -- ^ used in 'SAT.Mios.Main.analyze'
              , _an'toClear  :: !Stack             -- ^ used in 'SAT.Mios.Main.analyze'
              , _an'stack    :: !Stack             -- ^ used in 'SAT.Mios.Main.analyze'
              , _an'lastDL   :: !Stack             -- ^ last decision level used in 'SAT.Mios.Main.analyze'
              , _clsPool     :: ClausePool         -- ^ clause recycler
              , _litsLearnt  :: !Stack             -- ^ used in 'SAT.Mios.Main.analyze' and 'SAT.Mios.Main.search' to create a learnt clause
              , _stats       :: !(Vec Int)         -- ^ statistics information holder
              , _lbd'seen    :: !(Vec Int)         -- ^ used in lbd computation
              , _lbd'key     :: !Int              -- ^ used in lbd computation
                -------- restart heuristics #62, clause evaluation criteria #74
              , _emaAFast     :: !EMA              -- ^ Number of Assignments Fast
              , _emaASlow     :: !EMA              -- ^ Number of Assignments Slow
              , _emaBDLvl     :: !EMA              -- ^ Backjumped and Restart Dicision Level
              , _emaCDLvl     :: !EMA              -- ^ Conflicting Level
              , _emaDFast     :: !EMA              -- ^ (Literal Block) Distance Fast
              , _emaDSlow     :: !EMA              -- ^ (Literal Block) Distance Slow
              , _nextRestart  :: !Int             -- ^ next restart in number of conflict
              , _restartExp   :: !Double          -- ^ incremented by blocking
              , _emaRstBias   :: !EMA              -- ^ average phase of restart
              }

makeLenses ''MySolver

newMySolver :: MiosConfiguration -> CNFDescription -> IO MySolver
newMySolver conf (CNFDescription nv dummy_nc _) =
  MySolver
    -- Clause Database
    <$> newManager dummy_nc                -- clauses
    <*> newManager 2000                    -- learnts
    <*> newWatcherList nv 1                -- watches
    -- Assignment Management
    <*> newVec nv LBottom                  -- assigns
    <*> newVec nv LBottom                  -- phases
    <*> newStack nv                        -- trail
    <*> newStack nv                        -- trailLim
    <*> return 0                             -- qHead
    <*> newClauseVector (nv + 1)           -- reason
    <*> newVec nv (-1)                     -- level
    <*> newVec (2 * (nv + 1)) 0            -- ndd
    <*> newStack nv                        -- conflicts
    -- Variable Order
    <*> newVec nv 0                        -- activities
    <*> newVarHeap nv                      -- order
    -- Configuration
    <*> return conf                        -- config
    <*> return nv                          -- nVars
    <*> return 1.0                           -- claInc
    <*> return 1.0                           -- varInc
    <*> return 0                             -- rootLevel
    -- Learnt DB Size Adjustment
    <*> return 100                           -- learntSAdj
    <*> return 100                           -- learntSCnt
    <*> return 2000                          -- maxLearnts
    -- Working Memory
    <*> return LiftedT                       -- ok
    <*> newVec nv 0                        -- an'seen
    <*> newStack nv                        -- an'toClear
    <*> newStack nv                        -- an'stack
    <*> newStack nv                        -- an'lastDL
    <*> newClausePool 10                   -- clsPool
    <*> newStack nv                        -- litsLearnt
    <*> newVec (fromEnum EndOfStatIndex) 0 -- stats
    <*> newVec nv 0                        -- lbd'seen
    <*> return 0                             -- lbd'key
    -- restart heuristics #62
    <*> newEMA False ef                    -- emaAFast
    <*> newEMA True es                     -- emaASlow
    <*> newEMA True 2                      -- emaBDLvl
    <*> newEMA True 2                      -- emaCDLvl
    <*> newEMA False ef                    -- emaDFast
    <*> newEMA True es                     -- emaDSlow
    <*> return 100                           -- nextRestart
    <*> return 0.0                           -- restartExp
    <*> newEMA False 100                   -- emaRstBias
  where
    (ef, es) = emaCoeffs conf

nMyAssigns :: MySolver -> IO Int
nMyAssigns s = get' $ view trail s

-- | returns the number of constraints (clauses).
nMyClauses :: MySolver -> IO Int
nMyClauses s = get' $ view clauses s

-- | returns the number of learnt clauses.
nMyLearnts :: MySolver -> IO Int
nMyLearnts s = get' $ view learnts s


setMyAssign :: Int -> LiftedBool -> StateT MySolver IO ()
setMyAssign ind x = do -- setNth assigns v x
  assignments <- use assigns
  setNthWithState assignments ind x

myValueVar :: Var -> StateT MySolver IO Int
myValueVar var = do --getNth . assigns
  assignments <- use assigns
  getNthWithState assignments var

myDecisionLevel :: StateT MySolver IO Int
myDecisionLevel = do -- get' . trailLim
  -- uses trailLim get'
  trailLimStack <- use trailLim
  liftIO $ get' trailLimStack -- stack has multiple values, but we only need the first one here

myEnqueue :: Lit -> Clause -> StateT MySolver IO Bool
myEnqueue p from = do
{-
  -- bump psedue lbd of @from@
  when (from /= NullClause && learnt from) $ do
    l <- get' (lbd from)
    k <- (12 +) <$> decisionLevel s
    when (k < l) $ set' (lbd from) k
-}
  let signumP = lit2lbool p
  let v = lit2var p
  val <- myValueVar v
  levelVec <- use level
  assignments <- use assigns
  reasons <- use reason
  trailStack <- use trail
  if val /= LBottom
  then return $ val == signumP     -- Existing consistent assignment -- don't enqueue (在minisat里面会直接assert)
  else do
    setNthWithState assignments v signumP -- New fact, store it
    setNthWithState levelVec v =<< myDecisionLevel
    setNthWithState reasons v from     -- NOTE: @from@ might be NULL!
    pushToWithState trailStack p
    return True

-- 妙蛙
myAssume :: Lit -> StateT MySolver IO Bool
myAssume p = do
  trail_lim_stack <- use trailLim
  trail_stack <- use trail
  pushToWithState trail_lim_stack =<< get'WithState trail_stack
  myEnqueue p NullClause

-- i want something like this:
-- do
-- ts <- get' trail
-- Lens' MySolver Stack (Lens' s t)
-- VectorFamily t a
-- keeping all assignment at 'level' but not beyond
myCancelUntil :: Int -> StateT MySolver IO ()
myCancelUntil lvl = do
  dl <- myDecisionLevel
  trailStack <- use trail
  trailLimStack <- use trailLim
  assignments <- use assigns
  phaseVec <- use phases
  reasonVec <- use reason
  ts <- get'WithState trailStack
  ls <- get'WithState trailLimStack
  when (lvl < dl) $ do
    lim <- getNthWithState trailLimStack (lvl + 1)
    let
      loopOnTrail :: Int -> StateT MySolver IO ()
      loopOnTrail ((lim <) -> False) = return ()
      loopOnTrail c = do
        x <- lit2var <$> getNthWithState trailStack c
        setNthWithState phaseVec x =<< getNthWithState assignments x
        setNthWithState assignments x LBottom
        setNthWithState reasonVec x NullClause -- 'analyze` uses reason without checking assigns
        s <- get
        liftIO $ undoVO s x
        loopOnTrail $ c - 1
    loopOnTrail ts
    shrinkByWithState trailStack (ts - lim)
    shrinkByWithState trailLimStack (ls - lvl)
    qHead <~ get'WithState trailStack

instance VarOrder MySolver where
  {-# SPECIALIZE INLINE updateVO :: MySolver -> Var -> IO () #-}
  updateVO = increaseHeap
  {-# SPECIALIZE INLINE undoVO :: MySolver -> Var -> IO () #-}
  undoVO s v = inHeap s v >>= (`unless` insertHeap s v)
  {-# SPECIALIZE INLINE selectVO :: MySolver -> IO Var #-}
  selectVO s = do
    let
      asg = _assigns s
      -- | returns the most active var (heap-based implementation)
      loop :: IO Var
      loop = do
        n <- numElementsInHeap s
        if n == 0
          then return 0
          else do
              v <- getHeapRoot s
              x <- getNth asg v
              if x == LBottom then return v else loop
    loop

{-# INLINE inHeap #-}
inHeap :: MySolver -> Var -> IO Bool
inHeap MySolver{..} n = case idxs _order of at -> (/= 0) <$> getNth at n

{-# INLINE numElementsInHeap #-}
numElementsInHeap :: MySolver -> IO Int
numElementsInHeap = get' . heap . _order

{-# INLINE increaseHeap #-}
increaseHeap :: MySolver -> Int -> IO ()
increaseHeap s@MySolver{..} n = case idxs _order of
                                at -> inHeap s n >>= (`when` (percolateUp s =<< getNth at n))

{-# INLINABLE percolateUp #-}
percolateUp :: MySolver -> Int -> IO ()
percolateUp MySolver{..} start = do
  let VarHeap to at = _order
  v <- getNth to start
  ac <- getNth _activities v
  let
    loop :: Int -> IO ()
    loop i = do
      let iP = div i 2          -- parent
      if iP == 0
        then setNth to i v >> setNth at v i -- end
        else do
            v' <- getNth to iP
            acP <- getNth _activities v'
            if ac > acP
              then setNth to i v' >> setNth at v' i >> loop iP -- loop
              else setNth to i v >> setNth at v i              -- end
  loop start

{-# INLINABLE percolateDown #-}
percolateDown :: MySolver -> Int -> IO ()
percolateDown MySolver{..} start = do
  let (VarHeap to at) = _order
  n <- getNth to 0
  v <- getNth to start
  ac <- getNth _activities v
  let
    loop :: Int -> IO ()
    loop i = do
      let iL = 2 * i            -- left
      if iL <= n
        then do
            let iR = iL + 1     -- right
            l <- getNth to iL
            r <- getNth to iR
            acL <- getNth _activities l
            acR <- getNth _activities r
            let (ci, child, ac') = if iR <= n && acL < acR then (iR, r, acR) else (iL, l, acL)
            if ac' > ac
              then setNth to i child >> setNth at child i >> loop ci
              else setNth to i v >> setNth at v i -- end
        else setNth to i v >> setNth at v i       -- end
  loop start

{-# INLINABLE insertHeap #-}
insertHeap :: MySolver -> Var -> IO ()
insertHeap s@(_order -> VarHeap to at) v = do
  n <- (1 +) <$> getNth to 0
  setNth at v n
  setNth to n v
  SAT.Mios.Types.set' to n
  percolateUp s n

{-# INLINABLE getHeapRoot #-}
getHeapRoot :: MySolver -> IO Int
getHeapRoot s@(_order -> VarHeap to at) = do
  r <- getNth to 1
  l <- getNth to =<< getNth to 0 -- the last element's value
  setNth to 1 l
  setNth at l 1
  setNth at r 0
  modifyNth to (subtract 1) 0 -- pop
  n <- getNth to 0
  when (1 < n) $ percolateDown s 1
  return r
