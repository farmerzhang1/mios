{-# LANGUAGE
    BangPatterns
  , FlexibleInstances
  , FunctionalDependencies
  , MagicHash
  , MultiParamTypeClasses
  , RecordWildCards
  , TupleSections
  , TypeFamilies
  , UndecidableInstances
  , ViewPatterns
  #-}
{-# LANGUAGE Trustworthy #-}

-- | FIXME: this is a too heavy implementation that enables peeking
--
-- * __FixedQueueOf Lit__ @:: UV.IOVector Int@
--
module SAT.Solver.Mios.Data.QueueOfBoundedInt
       (
         QueueOfBoundedInt
       , newQueue
       , sizeOfQueue
       , clearQueue
       , insertQueue
       , dequeue
       )
       where

import Control.Monad (when)
import qualified Data.Vector.Unboxed.Mutable as UV
import SAT.Solver.Mios.Types

-- | __version 1.1__
--
-- a shrinked version of 'MutableRings' (a single-linked memory chunk)
--
-- __Layout__
--
-- This is 2*n+3 length vector for n variables.
--
-- * ring[0] is the queue length
--
-- * ring[1] is the first assgined literal
--
-- * ring[2] is the last (latest) assigned literal
--
-- * ring[n+2] == the literal assigned after Literl /n/
--
-- __Definition__ (an empty case is eliminated)
--
-- * insert x = @do x' <- ring .! 2; setAt ring (x' + 2) x; setAt ring 2 x@
--
-- * dequeue = @do x <- ring .! 1; x' <- ring .! (x + 2); setAt ring 1 x'; return x@
--
-- * initialization = @setAt ring 0 0; setAt ring 1 0; setAt ring 2 0@
--
newtype QueueOfBoundedInt = QueueOfBoundedInt
              {
                ring :: UV.IOVector Int -- ^ emulate a linked data structure on mutable vector
              }

{-# INLINE sizeOfQueue #-}
sizeOfQueue :: QueueOfBoundedInt -> IO Int
sizeOfQueue QueueOfBoundedInt{..} = UV.unsafeRead ring 0

{-# INLINE clearQueue #-}
clearQueue :: QueueOfBoundedInt -> IO ()
clearQueue QueueOfBoundedInt{..} = UV.set ring 0

{-# INLINE insertQueue #-}
insertQueue :: QueueOfBoundedInt -> Int -> IO ()
insertQueue QueueOfBoundedInt{..} !x = do
  let !k = x + 3
  !exists <- UV.unsafeRead ring k
  when (0 == exists) $ do
    !n <- UV.unsafeRead ring 0
    if 0 == n
      then do
          UV.unsafeWrite ring 1 x
      else do
          !i <- (3 +) <$> UV.unsafeRead ring 2 -- the slot for the current last element
          UV.unsafeWrite ring i x                    -- points 'x` now
    UV.unsafeWrite ring 2 x                    -- and the pointer points 'x'
    UV.unsafeWrite ring k 0
    UV.unsafeWrite ring 0 $! n + 1

{-# INLINE dequeue #-}
dequeue :: QueueOfBoundedInt -> IO Int
dequeue QueueOfBoundedInt{..} = do
  n <- UV.unsafeRead ring 0
  x <- UV.unsafeRead ring 1
  let !x' = x + 3
  if 1 == n
    then do
        UV.unsafeWrite ring x' 0
        UV.unsafeWrite ring 1 0
        UV.unsafeWrite ring 2 0
    else do
        i <- UV.unsafeRead ring x'
        UV.unsafeWrite ring x' 0    -- clear the dequeued field
        UV.unsafeWrite ring 1 i     -- and the pointer points the element
  UV.unsafeWrite ring 0 $! n - 1
  return x

-- | /n/ is the number of Literals
newQueue :: Int -> IO QueueOfBoundedInt
newQueue n = do
   q <- UV.new $ 3 + int2lit (negate n) + 1
   UV.unsafeWrite q 0 0
   UV.unsafeWrite q 1 0
   UV.unsafeWrite q 2 0
   return $ QueueOfBoundedInt q

traverseQueue :: QueueOfBoundedInt -> IO [Int]
traverseQueue QueueOfBoundedInt{..} = do
  let
    loop l 0 = return $ reverse l
    loop l x = loop (x:l) =<< UV.unsafeRead ring (x + 3)
  loop [] =<< UV.unsafeRead ring 1
