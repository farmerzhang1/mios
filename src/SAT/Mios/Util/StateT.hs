{-# LANGUAGE RankNTypes #-}
module SAT.Mios.Util.StateT where
import SAT.Mios.Types
import SAT.Mios.Solver
import Control.Monad.State
import Control.Lens
import qualified Data.IORef as R

-- utilities
setNthWithState :: VecFamily v a => v -> Int -> a -> StateT e IO ()
setNthWithState aa bb cc = liftIO $ setNth aa bb cc

setNth' :: VecFamily t a => Lens' s t -> Int -> a -> StateT s IO ()
setNth' l index val = do
    vec <- use l
    setNthWithState vec index val

getNthWithState :: VecFamily v a => v -> Int -> StateT e IO a
getNthWithState aa bb = liftIO $ getNth aa bb

getNth' :: VecFamily t a => Lens' s t -> Int -> StateT s IO a
getNth' l index = do
    vec <- use l
    getNthWithState vec index

pushToWithState :: StackFamily s t => s -> t -> StateT e IO ()
pushToWithState aa bb = liftIO $ pushTo aa bb

pushTo' :: StackFamily t a => Lens' s t -> a -> StateT s IO ()
pushTo' l topush = do
    stack <- use l
    pushToWithState stack topush

get'WithState :: SingleStorage s t => s -> StateT e IO t
get'WithState aa = liftIO $ get' aa
get'' :: SingleStorage t a => Lens' s t -> StateT s IO a
get'' l = do
    ss <- use l
    get'WithState ss

undoVOWithState :: Var -> StateT e IO ()
undoVOWithState aa  = error "undo TODO"

shrinkByWithState :: StackFamily s t => s -> Int -> StateT e IO ()
shrinkByWithState stack i = liftIO $ shrinkBy stack i

shrinkBy' :: StackFamily t a => Lens' s t -> Int -> StateT s IO ()
shrinkBy' l num = do
    stack <- use l
    shrinkByWithState stack num

readIORef :: Lens' s (R.IORef t) -> StateT s IO t
readIORef l = do
    ref <- use l
    liftIO $ R.readIORef ref

writeIORef :: Lens' s (R.IORef t) -> t -> StateT s IO ()
writeIORef l val = do
    ref <- use l
    liftIO $ R.writeIORef ref val

reset' :: VecFamily t a => Lens' s t -> StateT s IO ()
reset' l = do
    to_reset <- use l
    liftIO $ reset to_reset