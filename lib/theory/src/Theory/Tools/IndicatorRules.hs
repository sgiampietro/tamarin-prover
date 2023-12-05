{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns     #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
  -- spurious warnings for view patterns
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
-- Portability : GHC only
--
module Theory.Tools.IndicatorRules (
    specialIntruderRules

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

-- Special constraint solving rules for diffie-hellman multiplication
----------------------------------------------------------------------
{-
These are the indicator rules that we want to introduce for our diffie-hellman
multiplication approach. 
The rules that create case splits are instead defined in the Goal.hs file. 

rule Cind:
   [ Kdh(X.Y)@j, NoCanc(X,Y) ] --[ ]-> [ Kdh( z2.Ind(X)^z )@i), i<j, NoCanc(z2, Ind(X)^z) ]

rule pub:
   [ ] --[ KU( $x ) ]-> [ KU( $x ) ]
   
rule nat:
   [ ] --[ KU( x:nat ) ]-> [ KU( x:nat ) ]

rule gen_fresh:
   [ Fr( ~x ) ] --[ KU( ~x ) ]-> [ KU( ~x ) ]

rule isend:
   [ KU( x) ] --[ K( x ) ]-> [ In( x ) ]

rule irecv:
   [ Out( x) ] --> [ KD( x ) ]

rule iequality:
   [ KU( x ) , KD( x ) ] --> []

-}
-- | @specialIntruderRules@ returns the special intruder rules that are
--   included independently of the message theory
indicatorRules :: [IntrRuleAC]
indicatorRules =
    [ Rule IndRule [kdhFact xy_prod, noCancFact x_var y_var ]  [kdhFact ind_prod, noCancFact z2_var indx] []  [x_var, y_var, z1_var, z2_var]
    ] 
  where
    x_var = varTerm (LVar "x"  LSortG 0)
    y_var = varTerm (LVar "x"  LSortG 0)
    xy_prod = fAppdhMult (x_var, y_var)
    z1_var = varTerm (LVar "x"  LSortE 0)
    z2_var = varTerm (LVar "x"  LSortG 0)
    indx = fAhhExp ( fst (rootIndicator x_var) , z1_var)
    ind_prod = fAppdhMult (z2_var, indx)


