{-# LANGUAGE
    BangPatterns
  , FlexibleContexts
  , FlexibleInstances
  , FunctionalDependencies
  , MultiParamTypeClasses
  , TypeFamilies
  , UndecidableInstances
  #-}
{-# LANGUAGE Trustworthy #-}

-- | Basic abstract data types used throughout the code.
module SAT.Solver.Mios.Types
       (
         -- Singleton
         module SAT.Solver.Mios.Data.Singleton
         -- Fixed Unboxed Mutable Int Vector
       , module SAT.Solver.Mios.Data.Vec
         -- Abstract interfaces
       , VectorFamily (..)
         -- * misc function
       , Var
       , bottomVar
         -- * Internal encoded Literal
       , Lit
       , lit2int
       , int2lit
       , bottomLit
       , newLit
       , positiveLit
       , lit2var
       , var2lit
       , negateLit
         -- Assignment
       , LBool
       , lbool
       , lFalse
       , lTrue
       , lBottom
       , VarOrder (..)
         -- * CNF
       , CNFDescription (..)
       )
       where

import Control.Monad (forM)
import GHC.Exts (Int(..))
import GHC.Prim
import qualified Data.Vector.Unboxed.Mutable as UV
import SAT.Solver.Mios.Data.Singleton
import SAT.Solver.Mios.Data.Vec

-- | Public interface as /Container/
class VectorFamily s t | s -> t where
  -- * Size operations
  -- | erases all elements in it
  clear :: s -> IO ()
  clear = error "no default method for clear"
  -- * Debug
  -- | dump the contents
  dump :: Show t => String -> s -> IO String
  dump msg _ = error $ msg ++ ": no defalut method for dump"
  -- | get a raw data
  asVec :: s -> UV.IOVector Int
  asVec = error "asVector undefined"
  -- | converts into a list
  asList :: s -> IO [t]
  asList = error "asList undefined"
  {-# MINIMAL dump #-}

-- | provides 'clear' and 'size'
instance VectorFamily Vec Int where
  clear = error "Vec.clear"
  {-# SPECIALIZE INLINE asList :: Vec -> IO [Int] #-}
  asList v = forM [0 .. UV.length v - 1] $ UV.unsafeRead v
  dump str v = (str ++) . show <$> asList v
  {-# SPECIALIZE INLINE asVec :: Vec -> Vec #-}
  asVec = id

-- | represents "Var"
type Var = Int

-- | Special constant in 'Var' (p.7)
bottomVar :: Var
bottomVar = 0

-- | The literal data has an 'index' method which converts the literal to
-- a "small" integer suitable for array indexing. The 'var'  method returns
-- the underlying variable of the literal, and the 'sign' method if the literal
-- is signed (False for /x/ and True for /-x/).
type Lit = Int

-- | Special constant in 'Lit' (p.7)
bottomLit :: Lit
bottomLit = 0

-- | converts "Var" into 'Lit'
newLit :: Var -> Lit
newLit = error "newLit undefined"

-- | returns @True@ if the literal is positive 
{-# INLINE positiveLit #-}
positiveLit :: Lit -> Bool
positiveLit = even

----------------------------------------
----------------- Var
----------------------------------------

-- | converts 'Lit' into 'Var'
-- >>> lit2var 1  -- -1
-- 1
-- >>> lit2var 2  -- 1
-- 1
-- >>> lit2var 3 -- -2
-- 2
-- >>> lit2var 4 -- 2
-- 2
{-# INLINE lit2var #-}
lit2var :: Lit -> Var
lit2var n = div (n + 1) 2

-- >>> var2lit 1 True
-- 2
-- >>> var2lit 1 False
-- 1
-- >>> var2lit 2 True
-- 4
-- >>> var2lit 2 False
-- 3
{-# INLINE var2lit #-}
var2lit :: Var -> Bool -> Lit
var2lit v True = 2 * v
var2lit v _ = 2 * v - 1

----------------------------------------
----------------- Int
----------------------------------------

-- | convert 'Int' into 'Lit'   -- lit2int . int2lit == id
--
-- >>> int2lit (-1)
-- 1
-- >>> int2lit 1
-- 2
-- >>> int2lit (-2)
-- 3
-- >>> int2lit 2
-- 4
--
{-# INLINE int2lit #-}
int2lit :: Int -> Lit
int2lit n
  | 0 < n = 2 * n
  | otherwise = -2 * n - 1

-- | converts `Lit' into 'Int'   -- int2lit . lit2int == id
-- >>> lit2int 1
-- -1
-- >>> lit2int 2
-- 1
-- >>> lit2int 3
-- -2
-- >>> lit2int 4
-- 2
{-# INLINE lit2int #-}
lit2int l
  | even l = div l 2
  | otherwise = negate (div l 2) - 1

-- | negates literal
{-# INLINE negateLit #-}
negateLit :: Lit -> Lit
negateLit l = if even l then l - 1 else l + 1

-- | Lifted Boolean domain (p.7) that extends 'Bool' with "⊥" means /undefined/
type LBool = Int

-- | converts 'Bool' into 'LBool'
{-# INLINE lbool #-}
lbool :: Bool -> LBool
lbool True = lTrue
lbool False = lFalse

-- | A contant representing False
lFalse:: LBool
lFalse = -1

-- | A constant representing True
lTrue :: LBool
lTrue = 1

-- | A constant for "undefined"
lBottom :: LBool
lBottom = 0

-- | Assisting ADT for the dynamic variable ordering of the solver.
-- The constructor takes references to the assignment vector and the activity
-- vector of the solver. The method 'select' will return the unassigned variable
-- with the highest activity.
class VarOrder o where
  -- | constructor
  newVarOrder :: (VectorFamily v1 Bool, VectorFamily v2 Double) => v1 -> v2 -> IO o
  newVarOrder _ _ = error "newVarOrder undefined"

  -- | Called when a new variable is created.
  newVar :: o -> IO Var
  newVar = error "newVar undefined"

  -- | Called when variable has increased in activity.
  update :: o -> Var -> IO ()
  update _  = error "update undefined"

  -- | Called when all variables have been assigned new activities.
  updateAll :: o -> IO ()
  updateAll = error "updateAll undefined"

  -- | Called when variable is unbound (may be selected again).
  undo :: o -> Var -> IO ()
  undo _ _  = error "undo undefined"

  -- | Called to select a new, unassigned variable.
  select :: o -> IO Var
  select    = error "select undefined"

-- | misc information on CNF
data CNFDescription = CNFDescription
  {
    _numberOfVariables :: !Int           -- ^ number of variables
  , _numberOfClauses :: !Int             -- ^ number of clauses
  , _pathname :: Maybe FilePath          -- ^ given filename
  }
  deriving (Eq, Ord, Show)
