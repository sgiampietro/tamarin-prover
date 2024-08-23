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
module Theory.Tools.DHActionFacts (
  basisOfRule
  , notBasisOfRule
 
) where

import           Term.Unification
import           Term.LTerm
import           Term.DHMultiplication
import           Theory.Text.Pretty
import           Theory.Model.Rule
import           Theory.Model

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
-- Auxiliary functions for DH Action fact basis sets                                                --
------------------------------------------------------------------------------



basisOfRule :: Rule i -> [LNTerm]
basisOfRule ru = [] -- concatMap eTermsOf (enumInTerms ru)

notBasisOfRule :: Rule i -> [LNTerm]
notBasisOfRule ru = concatMap eTermsOf (enumNotInTerms ru)

enumInTerms :: Rule i -> [LNTerm]
enumInTerms ru = concat [ factTerms fa  | (i,fa) <- enumPrems ru ] -- , factTag fa == InFact ]

enumNotInTerms :: Rule i -> [LNTerm]
enumNotInTerms ru = concat [ factTerms fa  | (i,fa) <- enumPrems ru] -- , factTag fa /= InFact ]