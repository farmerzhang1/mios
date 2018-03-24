-- | (This file is a part of MIOS.)
-- Minisat-based Implementation and Optimization Study on SAT solver
{-# LANGUAGE
    BangPatterns
  , LambdaCase
  , ViewPatterns
#-}
{-# LANGUAGE Trustworthy #-}

module SAT.Mios
       (
         -- * Interface to the core of solver
         versionId
       , CNFDescription (..)
       , module SAT.Mios.OptionParser
       , runSolver
       , solveSAT
       , solveSATWithConfiguration
       , solve
       , SolverResult
       , Certificate (..)
         -- * Assignment Validator
       , validateAssignment
       , validate
         -- * For standalone programs
       , executeSolverOn
       , executeSolver
       , executeValidatorOn
       , executeValidator
         -- * File IO
       , parseCNF
       , injectClausesFromCNF
       , dumpAssigmentAsCNF
       )
       where

import Control.Concurrent (forkIO, killThread, myThreadId, threadDelay
                          , newEmptyMVar, putMVar, readMVar)
import Control.Exception
import Control.Monad ((<=<), unless, void, when)
import Data.Char
import qualified Data.ByteString.Char8 as B
import Numeric (showFFloat)
-- import Streamly
-- import qualified Streamly.Prelude as S
import System.CPUTime
import System.Exit
import System.IO

import SAT.Mios.Types
import SAT.Mios.Main
import SAT.Mios.OptionParser
import SAT.Mios.Validator

-- import SAT.Mios.Solver (clauses)
-- import SAT.Mios.Clause (Clause(..))
-- import SAT.Mios.ClauseManager (getClauseVector)

-- | version name
versionId :: String
versionId = "mios-1.6.1WIP#72#73#74#77#78 -- https://github.com/shnarazk/mios"

reportElapsedTime :: Bool -> String -> Integer -> IO Integer
reportElapsedTime False _ 0 = return 0
reportElapsedTime False _ _ = getCPUTime
reportElapsedTime True mes t = do
  now <- getCPUTime
  let toSecond = 1000000000000 :: Double
  hPutStr stderr mes
  hPutStrLn stderr $ showFFloat (Just 3) (fromIntegral (now - t) / toSecond) " sec"
  return now

-- | executes a solver on the given CNF file.
-- This is the simplest entry to standalone programs; not for Haskell programs.
executeSolverOn :: FilePath -> IO ()
executeSolverOn path = executeSolver (miosDefaultOption { _targetFile = Just path })

-- | executes a solver on the given 'arg :: MiosConfiguration'.
-- This is another entry point for standalone programs.
executeSolver :: MiosProgramOption -> IO ()
executeSolver opts@(_targetFile -> (Just cnfFile)) = do
  (desc, cls) <- parseCNF (_targetFile opts)
  -- when (_numberOfVariables desc == 0) $ error $ "couldn't load " ++ show cnfFile
  solverId <- myThreadId
  when (_confMaxClauses opts < _numberOfClauses desc) $
    if -1 == _confBenchmark opts
      then errorWithoutStackTrace $ "ABORT: too many clauses to solve, " ++ show desc
      else reportResult opts 0 (Left OutOfMemory) >> killThread solverId

{-
  t0 <- reportElapsedTime False "" $ if _confVerbose opts || 0 <= _confBenchmark opts then -1 else 0
  putStrLn $ " - number of clauses = " ++ show (_numberOfClauses desc)

  -- original ByteString
  s <- newSolver (toMiosConf opts) desc
  ct <- reportElapsedTime True "- making a new solver: " t0
  injectClausesFromCNF s desc . snd =<< parseCNF (_targetFile opts)
  ct <- reportElapsedTime True "injecting w/ ByteString: " ct

  -- Streamly
  s1 <- newSolver (toMiosConf opts) desc
  ct <- reportElapsedTime False " - making a new solver: " ct
  injectClausesStreamly s1 desc cls
  ct <- reportElapsedTime True "injecting w/ streamly: " ct

  -- Handle-based ByteString
  s2 <- newSolver (toMiosConf opts) desc
  ct <- reportElapsedTime False "- making a new solver: " ct
  (desc', h') <- parseCNFHeader (_targetFile opts)
  injectClausesFromHandle s2 desc' h'
  ct <- reportElapsedTime True "injecting w/ Handle: " ct

  -- memory-to-memory pseudo generator
  s2 <- newSolver (toMiosConf opts) desc
  ct <- reportElapsedTime False " - making a new solver: " ct
  realNc <- get' (clauses s)
  cvec <- getClauseVector (clauses s)
  let loop :: Int -> IO Int
      loop n@((< realNc) -> False) = return n
      loop i = do c <- getNth cvec i
                  unless (c == NullClause) $ void $ addClause s2 (lits c)
                  loop (i + 1)
  realc <- loop 1
  void $ reportElapsedTime True ("injecting w/o IO (" ++ show realc ++ "):") ct
  -- killThread solverId
  putStrLn "solving..."
-}
  token <- newEmptyMVar --  :: IO (MVar (Maybe Solver))
  t0 <- reportElapsedTime False "" $ if _confVerbose opts || 0 <= _confBenchmark opts then -1 else 0
  handle (\case
             UserInterrupt -> putStrLn "User interrupt recieved."
             ThreadKilled  -> reportResult opts t0 =<< readMVar token
             e -> print e) $ do
    when (0 < _confBenchmark opts) $
      void $ forkIO $ do let fromMicro = 1000000 :: Int
                         threadDelay $ fromMicro * fromIntegral (_confBenchmark opts)
                         putMVar token (Left TimeOut)
                         killThread solverId
    -- when (_confMaxClauses opts < _numberOfClauses desc) $
    --   if -1 == _confBenchmark opts
    --     then errorWithoutStackTrace $ "ABORT: too many variables to solve, " ++ show desc
    --     else putMVar token (Left OutOfMemory) >> killThread solverId
    -- (desc, cls) <- parseCNFHeader (_targetFile opts)
    s <- newSolver (toMiosConf opts) desc
    -- ct <- reportElapsedTime True "- making a new solver: " t0
    injectClausesFromCNF s desc cls
    void $ reportElapsedTime (_confVerbose opts) ("## [" ++ showPath cnfFile ++ "] Parse: ") t0
    -- ct <- reportElapsedTime True "injecting w/ ByteString: " ct
    when (0 < _confDumpStat opts) $ dumpStats DumpCSVHeader s
    result <- solve s []
    putMVar token result
    killThread solverId

executeSolver _ = return ()

-- | print messages on solver's result
-- Note: the last field of benchmark CSV is:
--   * 0 if UNSAT
--   * 1 if satisfiable (by finding an assignment)
--   * other bigger values are used for aborted cases.
reportResult :: MiosProgramOption -> Integer -> SolverResult -> IO ()
-- abnormal cases, catching 'too large CNF', 'timeout' for now.
reportResult opts@(_targetFile -> Just cnfFile) _ (Left flag) =
  putStrLn ("\"" ++ takeWhile (' ' /=) versionId ++ "\","
             ++ show (_confBenchSeq opts) ++ ","
             ++ "\"" ++ cnfFile ++ "\","
             ++ show (_confBenchmark opts) ++ "," ++ show (fromEnum flag))

-- solver terminated normally
reportResult opts@(_targetFile -> Just cnfFile) t0 (Right result) = do
  t2 <- reportElapsedTime (_confVerbose opts) ("## [" ++ showPath cnfFile ++ "] Total: ") t0
  case result of
    _ | 0 <= _confBenchmark opts -> return ()
    SAT _   | _confNoAnswer opts -> when (_confVerbose opts) $ hPutStrLn stderr "SATISFIABLE"
    UNSAT _ | _confNoAnswer opts -> when (_confVerbose opts) $ hPutStrLn stderr "UNSATISFIABLE"
    SAT asg -> print asg
    UNSAT t -> do when (_confVerbose opts) $ hPutStrLn stderr "UNSAT" -- contradiction
                  print t
  dumpAssigmentAsCNF (_outputFile opts) result
  valid <- if _confCheckAnswer opts -- || 0 <= _confBenchmark opts
           then case result of
                  SAT asg -> do (desc, cls) <- parseCNF (_targetFile opts)
                                s' <- newSolver (toMiosConf opts) desc
                                injectClausesFromCNF s' desc cls
                                validate s' asg
                  UNSAT _ -> return True
           else return True
  when (_confCheckAnswer opts) $ do
    if _confVerbose opts
      then hPutStrLn stderr $ if valid then "A vaild answer" else "Internal error: mios returns a wrong answer"
      else unless valid $ hPutStrLn stderr "Internal error: mios returns a wrong answer"
    void $ reportElapsedTime (_confVerbose opts) ("## [" ++ showPath cnfFile ++ "] Validate: ") t2
  when (0 <= _confBenchmark opts) $ do
    let fromPico = 1000000000000 :: Double
        phase = case result of { SAT _   -> 1; UNSAT _ -> 0::Int }
    putStrLn $ "\"" ++ takeWhile (' ' /=) versionId ++ "\","
      ++ show (_confBenchSeq opts) ++ ","
      ++ "\"" ++ cnfFile ++ "\","
      ++ if valid
         then showFFloat (Just 3) (fromIntegral (t2 - t0) / fromPico) "," ++ show phase
         else show (_confBenchmark opts) ++ "," ++ show (fromEnum InternalInconsistent)

reportResult _ _ _ = return ()

-- | new top-level interface that returns:
--
-- * conflicting literal set :: Left [Int]
-- * satisfiable assignment :: Right [Int]
--
runSolver :: Traversable t => MiosConfiguration -> CNFDescription -> t [Int] -> IO (Either [Int] [Int])
runSolver m d c = do
  s <- newSolver m d
  mapM_ ((s `addClause`) <=< (newStackFromList . map int2lit)) c
  noConf <- simplifyDB s
  if noConf
    then do
        x <- solve s []
        case x of
          Right (SAT a)   -> return $ Right a
          Right (UNSAT a) -> return $ Left a
          _ -> return $ Left []
    else return $ Left []

-- | The easiest interface for Haskell programs.
-- This returns the result @::[[Int]]@ for a given @(CNFDescription, [[Int]])@.
-- The first argument @target@ can be build by @Just target <- cnfFromFile targetfile@.
-- The second part of the first argument is a list of vector, which 0th element is the number of its real elements.
solveSAT :: Traversable m => CNFDescription -> m [Int] -> IO [Int]
solveSAT = solveSATWithConfiguration defaultConfiguration

-- | solves the problem (2rd arg) under the configuration (1st arg).
-- and returns an assignment as list of literals :: Int.
solveSATWithConfiguration :: Traversable m => MiosConfiguration -> CNFDescription -> m [Int] -> IO [Int]
solveSATWithConfiguration conf desc cls = do
  s <- newSolver conf desc
  -- mapM_ (const (newVar s)) [0 .. _numberOfVariables desc - 1]
  mapM_ ((s `addClause`) <=< (newStackFromList . map int2lit)) cls
  noConf <- simplifyDB s
  if noConf
    then do result <- solve s []
            case result of
              Right (SAT a) -> return a
              _             -> return []
    else return []

-- | validates a given assignment from STDIN for the CNF file (2nd arg).
-- this is the entry point for standalone programs.
executeValidatorOn :: FilePath -> IO ()
executeValidatorOn path = executeValidator (miosDefaultOption { _targetFile = Just path })

-- | validates a given assignment for the problem (2nd arg).
-- This is another entry point for standalone programs; see app/mios.hs.
executeValidator :: MiosProgramOption -> IO ()
executeValidator opts@(_targetFile -> target@(Just cnfFile)) = do
  (desc, cls) <- parseCNF target
  when (_numberOfVariables desc == 0) . error $ "couldn't load " ++ show cnfFile
  s <- newSolver (toMiosConf opts) desc
  injectClausesFromCNF s desc cls
  when (_confVerbose opts) $
    hPutStrLn stderr $ cnfFile ++ " was loaded: #v = " ++ show (_numberOfVariables desc) ++ " #c = " ++ show (_numberOfClauses desc)
  asg <- read <$> getContents
  unless (_confNoAnswer opts) $ print asg
  result <- s `validate` (asg :: [Int])
  if result
    then putStrLn ("It's a valid assignment for " ++ cnfFile ++ ".") >> exitSuccess
    else putStrLn ("It's an invalid assignment for " ++ cnfFile ++ ".") >> exitFailure

executeValidator _  = return ()

-- | returns True if a given assignment (2nd arg) satisfies the problem (1st arg).
-- if you want to check the @answer@ which a @slover@ returned, run @solver `validate` answer@,
-- where 'validate' @ :: Traversable t => Solver -> t Lit -> IO Bool@.
validateAssignment :: (Traversable m, Traversable n) => CNFDescription -> m [Int] -> n Int -> IO Bool
validateAssignment desc cls asg = do
  s <- newSolver defaultConfiguration desc
  mapM_ ((s `addClause`) <=< (newStackFromList . map int2lit)) cls
  s `validate` asg

-- | dumps an assigment to file.
-- 2nd arg is
--
-- * @True@ if the assigment is satisfiable assigment
--
-- * @False@ if not
--
-- >>> do y <- solve s ... ; dumpAssigmentAsCNF (Just "result.cnf") y <$> model s
--
dumpAssigmentAsCNF :: Maybe FilePath -> Certificate -> IO ()
dumpAssigmentAsCNF Nothing _ = return ()
-- | FIXME: swtich to DRAT
dumpAssigmentAsCNF (Just fname) (UNSAT _) =
  writeFile fname "s UNSAT\n0\n"
dumpAssigmentAsCNF (Just fname) (SAT l) =
  withFile fname WriteMode $ \h -> do hPutStrLn h "s SAT"; hPutStrLn h . (++ " 0") . unwords $ map show l

--------------------------------------------------------------------------------
-- DIMACS CNF Reader
--------------------------------------------------------------------------------

-- | parses the header of a CNF file
parseCNF :: Maybe FilePath -> IO (CNFDescription, B.ByteString)
parseCNF target@(Just cnfFile) = do
  let -- format: p cnf n m, length "p cnf" == 5
      parseP line = case parseInt (skipWhitespace (B.drop 5 line)) of
                      (x, second) -> case B.readInt (skipWhitespace second) of
                                       Just (y, _) -> CNFDescription x y target
      seek :: B.ByteString -> IO (CNFDescription, B.ByteString)
      seek bs
        | B.head bs == 'p' = return (parseP l, B.tail bs')
        | otherwise = seek (B.tail bs')
        where (l, bs') = B.span ('\n' /=) bs
  seek =<< B.readFile cnfFile

-- | parses ByteString then injects the clauses in it into a solver
{-# INLINABLE injectClausesFromCNF #-}
injectClausesFromCNF :: Solver -> CNFDescription -> B.ByteString -> IO ()
injectClausesFromCNF s (CNFDescription nv nc _) bs = do
  let maxLit = int2lit $ negate nv
  buffer <- newVec (maxLit + 1) 0 :: IO (Vec Int)
  polvec <- newVec (maxLit + 1) 0 :: IO (Vec Int)
  let loop :: Int -> B.ByteString -> IO ()
      loop ((< nc) -> False) _ = return ()
      loop !i !b = loop (i + 1) =<< readClause s buffer polvec b
  loop 0 bs
  -- static polarity
  let checkPolarity :: Int -> IO ()
      checkPolarity ((< nv) -> False) = return ()
      checkPolarity v = do
        p <- getNth polvec $ var2lit v True
        if p == LiftedF
          then setAssign s v p
          else do n <- getNth polvec $ var2lit v False
                  when (n == LiftedF) $ setAssign s v p
        checkPolarity $ v + 1
  checkPolarity 1

{-# INLINE skipWhitespace #-}
skipWhitespace :: B.ByteString -> B.ByteString
skipWhitespace !s = B.dropWhile (`elem` " \t\n") s

-- | skip comment lines
-- __Pre-condition:__ we are on the benngining of a line
{-# INLINE skipComments #-}
skipComments :: B.ByteString -> B.ByteString
skipComments !s
  | c == 'c' = skipComments . B.tail . B.dropWhile (/= '\n') $ s
  | otherwise = s
  where
    c = B.head s

{-# INLINE parseInt #-}
parseInt :: B.ByteString -> (Int, B.ByteString)
parseInt !st = do
  let !zero = ord '0'
      loop :: B.ByteString -> Int -> (Int, B.ByteString)
      loop !s !val = case B.uncons s of
        Just (c, s') -> if '0' <= c && c <= '9' then loop s' (val * 10 + ord c - zero) else (val, s')
  case B.uncons st of
    Just ('-', st') -> let (k, x) = loop st' 0 in (negate k, x)
    Just ('0', st') -> (0, st')
    _ -> loop st 0
{-
parseInt !st = do
  let !zero = ord '0'
      loop :: B.ByteString -> Int -> (Int, B.ByteString)
      loop !s !val = case B.head s of
        c | '0' <= c && c <= '9'  -> loop (B.tail s) (val * 10 + ord c - zero)
        _ -> (val, B.tail s)
  case B.head st of
    '-' -> let (k, x) = loop (B.tail st) 0 in (negate k, x)
    '0' -> (0, B.tail st)
--    '+' -> loop st (0 :: Int)
    _   -> loop st 0
--    c | '0' <= c && c <= '9'  -> loop st 0
--    _ -> error "PARSE ERROR! Unexpected char"
-}

{-# INLINE readClause #-}
readClause :: Solver -> Stack -> Vec Int -> B.ByteString -> IO B.ByteString
readClause s buffer bvec stream = do
  let loop :: Int -> B.ByteString -> IO B.ByteString
      loop !i !b = case parseInt $ skipWhitespace b of
                     (0, b') -> do setNth buffer 0 $ i - 1
                                   sortStack buffer
                                   void $ addClause s buffer
                                   return b'
                     (k, b') -> case int2lit k of
                                  l -> do setNth buffer i l
                                          setNth bvec l LiftedT
                                          loop (i + 1) b'
  loop 1 . skipComments . skipWhitespace $ stream

showPath :: FilePath -> String
showPath str = replicate (len - length basename) ' ' ++ if elem '/' str then basename else basename'
  where
    len = 50
    basename = reverse . takeWhile (/= '/') . reverse $ str
    basename' = take len str

{-
-------------------------------------------------------------------------------- Streamly

parseCNFHeader :: Maybe FilePath -> IO (CNFDescription, Handle)
parseCNFHeader target@(Just cnfFile) = do
  h <- openFile cnfFile ReadMode
  liftIO $ hSetBuffering h LineBuffering
  let skip = do s <- B.hGetLine h
                if B.empty == s
                  then return (CNFDescription (-1) (-1) target, undefined)
                  else case B.head s of
                         'c'-> skip
                         'p' -> let [_, cnf, nv', nc'] = B.words s
                                    Just (nv, _) = B.readInt nv'
                                    Just (nc, _) = B.readInt nc'
                                in return (CNFDescription nv nc target, h)
                         otherwise -> putStrLn (B.unpack s) >> skip
  skip

-- | parses ByteString then injects the clauses in it into a solver
{-# INLINABLE injectClausesStreamly #-}
injectClausesStreamly :: Solver -> CNFDescription -> Handle -> IO ()
injectClausesStreamly s (CNFDescription nv nc _) h = do
  let maxLit = int2lit $ negate nv
  buffer <- newVec (maxLit + 1) 0 :: IO (Vec Int)
  polvec <- newVec (maxLit + 1) 0 :: IO (Vec Int)
  let readClause' :: [Lit] -> IO ()
      readClause' lits = do
        let loop :: [Lit] -> Int -> IO ()
            loop [] i = do setNth buffer 0 (i - 1) -- '1` is the literal corresponding to '0'
                           sortStack buffer
                           void $ addClause s buffer
            loop (l:ls) i = do setNth buffer i l
                               setNth polvec l LiftedT
                               loop ls (i + 1)
        loop lits 1
  runStreaming $ serially $ do y <- S.fromHandle h
                               let lits = map (int2lit . read) (words y)
                               liftIO $ unless (null lits) $ readClause' (init lits)
  -- static polarity
  let checkPolarity :: Int -> IO ()
      checkPolarity ((< nv) -> False) = return ()
      checkPolarity v = do
        p <- getNth polvec $ var2lit v True
        if p == LiftedF
          then setAssign s v p
          else do n <- getNth polvec $ var2lit v False
                  when (n == LiftedF) $ setAssign s v p
        checkPolarity $ v + 1
  checkPolarity 1

---------------------------------------------------------------------- Handle-based ByteString

-- | parses ByteString then injects the clauses in it into a solver
{-# INLINABLE injectClausesFromHandle #-}
injectClausesFromHandle :: Solver -> CNFDescription -> Handle -> IO ()
injectClausesFromHandle s (CNFDescription nv nc _) h = do
  let maxLit = int2lit $ negate nv
  buffer <- newVec (maxLit + 1) 0 :: IO (Vec Int)
  polvec <- newVec (maxLit + 1) 0 :: IO (Vec Int)
  let loop :: Int -> IO ()
      loop ((< nc) -> False) = return ()
      loop !i = readClauseFromHandle s buffer polvec h >> loop (i + 1)
  loop 0
  -- static polarity
  let checkPolarity :: Int -> IO ()
      checkPolarity ((< nv) -> False) = return ()
      checkPolarity v = do
        p <- getNth polvec $ var2lit v True
        if p == LiftedF
          then setAssign s v p
          else do n <- getNth polvec $ var2lit v False
                  when (n == LiftedF) $ setAssign s v p
        checkPolarity $ v + 1
  checkPolarity 1

{-# INLINE readClauseFromHandle #-}
readClauseFromHandle :: Solver -> Stack -> Vec Int -> Handle -> IO ()
readClauseFromHandle s buffer bvec h = do
  let loop :: Int -> B.ByteString -> IO ()
      loop !i !b = case parseInt $ skipWhitespace b of
                     (0, _) -> do setNth buffer 0 $ i - 1
                                  sortStack buffer
                                  void $ addClause s buffer
                     (k, b') -> case int2lit k of
                                  l -> do setNth buffer i l
                                          setNth bvec l LiftedT
                                          loop (i + 1) b'
  loop 1 . skipComments . skipWhitespace =<< B.hGetLine h
-}
