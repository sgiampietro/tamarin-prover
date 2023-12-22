{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE ViewPatterns               #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt, Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
-- Portability : GHC only
--
-- Support for reasoning with and about disjunctions of substitutions.
module Theory.Tools.DHEquationStore (
  -- * Equations
    SplitId(..)

  , DHEqStore(..)
  , emptyDHEqStore
  , eqsSubst
  , eqsConj

  -- ** Equalitiy constraint conjunctions
  , falseEqConstrConj

  -- ** Queries
  , eqsIsFalse


  -- ** Adding equalities
  , addEqs
  -- , addRuleVariants
  --, addDisj

  -- ** Case splitting
  -- , performSplit
  --, dropNameHintsBound

  --, splits
  --, splitSize
  --, splitExists

  -- * Simplification
  --, simp
  --, simpDisjunction

  -- ** Pretty printing
  , prettyEqStore
) where

import           GHC.Generics          (Generic)
import           Logic.Connectives
import           Term.Unification
import           Theory.Text.Pretty

import           Control.Monad.Fresh
import           Control.Monad.Bind
import           Control.Monad.Reader
import           Extension.Prelude
import           Utils.Misc

import           Debug.Trace.Ignore

import           Control.Basics
import           Control.DeepSeq
import           Control.Monad.State   hiding (get, modify, put)
import qualified Control.Monad.State   as MS

import           Data.Binary
import qualified Data.Foldable         as F
import           Data.List          (delete,find,intersect,intersperse,nub,(\\))
import           Data.Maybe
import qualified Data.Set              as S
import           Extension.Data.Label  hiding (for, get)
import qualified Extension.Data.Label  as L
-- import           Extension.Data.Monoid

------------------------------------------------------------------------------
-- Equation Store                                                --
------------------------------------------------------------------------------




-- | An equality.
data EqInd a b = EqInd { eqFact1 :: a, eqFact2:a, indTerm :: b, term:: b }
    deriving (Eq, Show)

-- | True iff the two sides of the equality are equal with respect to their
-- 'Eq' instance.
evalDHInd :: Eq a => EqInd a -> Bool
evalDHInd (EqInd l r indt t) = l == r

instance Functor EqInd where
    fmap f (EqInd lhs rhs indt term) = EqInd (f lhs) (f rhs) (f indth) (t term)

instance Semigroup a => Semigroup (EqInd a) where
    (EqInd l1 r1 indt1 t1) <> (EqInd l2 r2 indt2 t2) =
        EqInd (l1 <> l2) (r1 <> r2) (indt1 <> indt2) (t1 <> t2)

instance Monoid a => Monoid (EqInd a) where
    mempty                                = EqInd mempty mempt mempty mempty

instance Foldable EqInd where
    foldMap f (EqInd l r indt t) = f l `mappend` f r `mappend` f t `mappend` f indt 

instance Traversable EqInd where
    traverse f (EqInd l r indt t) = EqInd <$> f l <*> f r <*> f indt <*> f t

instance Applicative EqInd where
    pure x                        = EqInd x x x x
    (EqInd fl fr findt ft) <*> (EqInd l r indt t) = EqInd (fl l) (fr r) (findt indt) (ft t)


