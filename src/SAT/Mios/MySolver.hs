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
    ( StatIndex(EndOfStatIndex), VarHeap, newVarHeap, decisionLevel )
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
assume :: Lit -> StateT MySolver IO Bool
assume p = do
  trail_lim_stack <- use trailLim
  trail_stack <- use trail
  pushToWithState trail_lim_stack =<< get'WithState trail_stack
  myEnqueue p NullClause
