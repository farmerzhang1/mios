module SAT.Mios.Util.StateT where
import SAT.Mios.Types
import Control.Monad.State
-- utilities
setNthWithState :: VecFamily v a => v -> Int -> a -> StateT e IO ()
setNthWithState aa bb cc = liftIO $ setNth aa bb cc
getNthWithState :: VecFamily v a => v -> Int -> StateT e IO a
getNthWithState aa bb = liftIO $ getNth aa bb
pushToWithState :: StackFamily s t => s -> t -> StateT e IO ()
pushToWithState aa bb = liftIO $ pushTo aa bb
get'WithState :: SingleStorage s t => s -> StateT e IO t
get'WithState aa = liftIO $ get' aa
