{-# LANGUAGE
    RankNTypes
  , BangPatterns
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

-- whether the clause is simplifiable
canSimplify' :: MyClause -> StateT MySolver IO Bool
canSimplify' clause = do
  n <- liftIO $ get' clause -- TODO implement SingleStorage for MyClause
  let
    loop :: Int -> StateT MySolver IO Bool
    loop ((<= n) -> False) = return False
    loop i = do
      v <- getNthWithState (_lits clause) i >>= valueLit' -- we can't use lens here (no focus of myclause in mysolver)
      if v == 1 then return True else loop (i + 1)
  loop 1
  return True

propagate' :: StateT MySolver IO (Maybe MyClause)
propagate' = do
  let
    while :: Maybe MyClause -> Bool -> StateT MySolver IO (Maybe MyClause)
    while confl False = return confl
    while confl True = do
      qHead += 1
      (p :: Lit) <- getNth' trail =<< use qHead
      -- incrementStat NumOfPropagation 1
      watcherList <- use watches
      let (ws :: MyClauseManager) = getNthWatcher' watcherList p
          falseLit = negateLit p
      end <- liftIO $ get' ws
      cvec <- liftIO $ getClauseVector' ws
      bvec <- liftIO $ getKeyVector' ws
      -- move to temp
      let copy :: Int -> Int -> StateT MySolver IO ()
          copy ((< end) -> False) _ = return ()
          copy !i' !j' = do setNthWithState cvec j' =<< getNthWithState cvec i'
                            setNthWithState bvec j' =<< getNthWithState bvec i'
                            copy (i' + 1) (j' + 1)
      let forClause :: Int -> Int -> StateT MySolver IO (Maybe MyClause)
          forClause i@((< end) -> False) !j = do liftIO $ shrinkBy ws (i - j); return confl
          forClause !i !j = do
            (blocker :: Lit) <- getNthWithState bvec i        -- Try to avoid inspecting the clause:
            bv <- if blocker == 0 then return LiftedF else valueLit' blocker
            if bv == LiftedT
              then do unless (i == j) $ do c <- getNthWithState cvec i
                                           liftIO $ setNth cvec j c
                                           liftIO $ setNth bvec j blocker
                      forClause (i + 1) (j + 1)
              else do                               -- Make sure the false literal is data[1]:
                  (Just c :: Maybe MyClause) <- getNthWithState cvec i
                  let lstack = _lits c
                  tmp <- getNthWithState lstack 1
                  first <- if falseLit == tmp
                           then do l2 <- liftIO $ getNth lstack 2
                                   liftIO $ setNth lstack 2 tmp
                                   liftIO $ setNth lstack 1 l2
                                   return l2
                           else return tmp
                  fv <- valueLit' first
                  if fv == LiftedT
                    then do liftIO $ unless (i == j) $ liftIO $ setNth cvec j (Just c)
                            liftIO $ setNth bvec j first
                            forClause (i + 1) (j + 1)
                    else do cs <- liftIO $ get' c           -- Look for new watch:
                            let newWatch :: Int -> StateT MySolver IO LiftedBool
                                newWatch ((<= cs) -> False) = do -- Did not find watch
                                  liftIO $ setNth cvec j (Just c)
                                  setNthWithState bvec j first
                                  if fv == LiftedF
                                    then do -- ((== 0) <$> decisionLevel s) >>= (`when` set' ok LiftedF)
                                      ok .= LiftedF -- TODO
                                      -- set' qHead =<< get' trail TODO
                                      -- trailSize <- get'' trail
                                      (qHead .=) =<< get'' trail
                                      copy (i + 1) (j + 1)
                                      return LiftedF                 -- conflict
                                    else do
                                      unsafeEnqueue' first (Just c)
                                      return LBottom                 -- unit clause
                                newWatch !k = do (l' :: Lit) <- getNthWithState lstack k
                                                 lv <- valueLit' l'
                                                 if lv /= LiftedF
                                                   then do setNthWithState lstack 2 l'
                                                           setNthWithState lstack k falseLit
                                                           -- (getNthWatcher' watches' (negateLit l'))
                                                           zoom (watches . ix (negateLit l')) $ pushClauseWithKey' (Just c) first
                                                           return LiftedT  -- found another watch
                                                   else newWatch $! k + 1
                            ret <- newWatch 3
                            case ret of
                              LiftedT -> forClause (i + 1) j               -- found another watch
                              LBottom -> forClause (i + 1) (j + 1)         -- unit clause
                              _       -> liftIO $ shrinkBy ws (i - j) >> return (Just c)   -- conflict
      c <- forClause 0 0
      return Nothing
  return Nothing


unsafeEnqueue' ::  Lit -> Maybe MyClause -> StateT MySolver IO ()
unsafeEnqueue' p from = do
  let v = lit2var p
  setNth' assigns v $ lit2lbool p
  setNth' level v =<< myDecisionLevel
  setNth' reason v from     -- NOTE: @from@ might be NULL!
  t <- use trail
  liftIO $ SAT.Mios.Types.pushTo t p

reduceDB' :: StateT MySolver IO ()
reduceDB' = do
  n <- get'' learnts
  lvec <- use learnts
  cvec <- liftIO $ getClauseVector' lvec
  let loop :: Int -> StateT MySolver IO ()
      loop ((< n) -> False) = return ()
      loop i = do
        removeWatch' =<< liftIO (getNth cvec i)
        loop (i+1)
  k <- sortClauses' lvec $ div n 2 -- k is the number of clauses not to be purged
  loop 1
  -- zoom watches reset' -- TODO
  reset' watches
  SAT.Mios.Util.StateT.shrinkBy' learnts (n - k)
  return ()

removeWatch' :: Maybe MyClause -> StateT MySolver IO ()
removeWatch' clause = return () -- TODO

sortClauses' :: MyClauseManager -> Int -> StateT MySolver IO Int
sortClauses' clauseManager limit' = return 8 --

analyze' :: MyClause -> StateT MySolver IO Int
analyze' confl = do
  reset' litsLearnt -- redefine state version if it's vector/stack/..., otherwise use zoom
  pushTo' litsLearnt 0
  dl <- myDecisionLevel
  let
    loopOnClauseChain :: MyClause -> Lit -> Int -> Int -> Int -> StateT MySolver IO Int
    loopOnClauseChain clause p ti bl pathC = do -- p : proposition, ti : trail index, bl : backtrack level
      let d = clause ^. rank
      state <- get
      when (d /= 0) $ zoom (someLens state clause) clauseBumpActivity -- you sure about this ?
      clauseSize <- get'WithState $ clause ^. lits
      let
        lstack = clause ^. lits
        loopOnLiterals :: Int -> Int -> Int -> StateT MySolver IO (Int, Int)
        loopOnLiterals ((<= clauseSize) -> False) b pc = return (b, pc)
        loopOnLiterals j b pc = do
          (q :: Lit) <- getNthWithState lstack j
          let v = lit2var q
          sn <- getNth' an'seen j
          l <- getNth' level v
          if not sn && l > 0 then do -- not seen || l > 0
            varBumpActivity' v
            setNth' an'seen v True
            if l >= dl then
              loopOnLiterals (j+1) b (pc+1)
            else do
              pushTo' litsLearnt q
              loopOnLiterals (j+1) (max b l) pc
          else
            loopOnLiterals (j+1) b pc -- loop on literals done
      -- let finished
      (b', pathC') <- loopOnLiterals (if p == bottomLit then 1 else 2) bl pathC
      let
        nextLit :: Int -> StateT MySolver IO Int
        nextLit i = do seen <- getNth' an'seen . lit2var =<< getNth' trail i
                       if not seen then nextLit (i-1) else return (i-1)
      trail_index <- nextLit (ti + 1)
      nextP <- getNth' trail (trail_index + 1)
      let nextVar = lit2var nextP
      (Just confl') <- getNth' reason nextVar
      setNth' an'seen nextVar False
      if pathC' > 1
      then loopOnClauseChain confl' nextP (trail_index - 1) b' (pathC' - 1)
      else setNth' litsLearnt 1 (negateLit nextP) >> return b'
      return 0
  return 0

clauseBumpActivity :: StateT MyClause IO ()
clauseBumpActivity = do
  -- TODO
  return ()

varBumpActivity' :: Var -> StateT MySolver IO ()
varBumpActivity' var = return () -- TODO

someLens :: MySolver -> MyClause -> Lens' MySolver MyClause
someLens solver clause = lens getter setter where
  getter = const clause
  setter oldSolver newClause = oldSolver

search :: StateT MySolver IO Bool
search = do
  let loop :: StateT MySolver IO Bool
      loop = do
        confl <- propagate'
        d <- myDecisionLevel
        case confl of
          Just mc -> do
            -- r <- use rootLevel TODO: remove rootlevel
            if d == 0 then do
              return False
            else do
              backtrackLevel <- analyze' mc
              myCancelUntil backtrackLevel
              k <- get'' litsLearnt
              when (k == 1) $ do
                (v :: Var) <- lit2var <$> getNth' litsLearnt 1
                setNth' level v 0
              varDecayActivity'
              clauseDecayActivity'
              loop
          Nothing -> do
            when (d == 0) $ void simplifyDB'
            (k1 :: Int) <- get'' learnts
            (k2 :: Int) <- get'' trail
            (n1 :: Int) <- floor <$> use maxLearnts
            when (n1 < k1 - k2) $ do
              reduceDB'
            nv <- use nVars
            if k2 == nv then return True
            else do
              s <- get
              v <- liftIO $ selectVO s
              unsafeEnqueue' v Nothing
              loop
  return True

varDecayActivity' :: StateT MySolver IO ()
varDecayActivity' = return ()
clauseDecayActivity' :: StateT MySolver IO ()
clauseDecayActivity' = return ()

simplifyDB' :: StateT MySolver IO Bool
simplifyDB' = return True

