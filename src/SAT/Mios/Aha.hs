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

-- whether the clause is simplifiable
simplify' :: MyClause -> StateT MySolver IO Bool
simplify' clause = do
  n <- liftIO $ get' clause -- TODO implement SingleStorage for MyClause
  let
    loop :: Int -> StateT MySolver IO Bool
    loop ((<= n) -> False) = return False
    loop i = do
      v <- getNthWithState (_lits clause) i >>= valueLit' -- we can't use lens here (no focus of myclause in mysolver)
      if v == 1 then return True else loop (i + 1)
  loop 1
  return True

analyze' :: MyClause -> StateT MySolver IO Int
analyze' clause = do
  return 0 -- TODO

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
  zoom watches reset' -- TODO
  SAT.Mios.Util.StateT.shrinkBy' learnts (n - k)
  return ()

removeWatch' :: Maybe MyClause -> StateT MySolver IO ()
removeWatch' clause = return () -- TODO

sortClauses' :: MyClauseManager -> Int -> StateT MySolver IO Int
sortClauses' clauseManager limit' = return 8 --

