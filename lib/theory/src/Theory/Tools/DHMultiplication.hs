{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns     #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
  -- spurious warnings for view patterns
-- |
-- Copyright   : (c) 2010-2012 Sofia Giampietro
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
-- Portability : GHC only
--
module Theory.Tools.DHMultiplication (
    clean
  , indicator
  , simplify


  -- ** Classifiers
  , isDExpRule
  , isDEMapRule
  , isDPMultRule
  ) where

import           Control.Basics hiding (empty)
import           Control.Monad.Reader

import           Data.List
import qualified Data.Set                          as S
import           Data.ByteString.Char8 (ByteString, append, pack, empty)

import           Extension.Data.Label

import           Utils.Misc

import           Term.Maude.Signature
import           Term.Narrowing.Variants.Compute
import           Term.Rewriting.Norm
import           Term.SubtermRule
import           Term.Subsumption
import           Term.Positions

import           Theory.Model

-- import           Debug.Trace

-- Useful functions for the diffie-hellman multiplication approach
----------------------------------------------------------------------

-- | @clean@ returns the message term cleaned of its diffie-hellman terms,
-- replacing them by fresh variables

-- TODO: take care of the list of variables used in the returned substitutions are fresh. 
-- Q: I think the "LNSubstVFresh" needs to be converted to a SubstVFree which checks this. 
-- This is checked in a certaind MonadFresh context? Look into this. 

clean :: (Show a, IsVar v) => Term a -> (Term a, [(v, VTerm c v)])
clean t@(viewTerm3 -> MsgLit l) = (MsgLit l, [])
clean t@(viewTerm3 -> MsgFApp f ts) = (MsgFapp f (map (fst.clean) ts), concatMap (snd.clean) ts )
clean t@(viewTerm3 -> Box dht) = (Box (Var v1), [(v1, dht)] )
clean t@(viewTerm3 -> DH dht) = (dht, [] )