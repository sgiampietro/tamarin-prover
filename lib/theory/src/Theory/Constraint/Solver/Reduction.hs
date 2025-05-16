{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns  #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- A monad for writing constraint reduction steps together with basic steps
-- for inserting nodes, edges, actions, and equations and applying
-- substitutions.
module Theory.Constraint.Solver.Reduction (
  -- * The constraint 'Reduction' monad
    Reduction
  , execReduction
  , runReduction

  -- ** Change management
  , ChangeIndicator(..)
  , whenChanged
  , applyChangeList
  , whileChanging

  -- ** Accessing the 'ProofContext'
  , getProofContext
  , getMaudeHandle
  , getMaudeHandleDH
  , getMaudeHandleCR
  , getVerbose

  , enumConcsDhOut
  , enumConcsDhExpOut
  -- ** Inserting nodes, edges, and atoms
  , labelNodeId
  , exploitNodeId
  , insertFreshNode
  , insertFreshNodeConc
  , insertFreshNodeConcKI
  , insertFreshNodeConcInst
  , insertFreshNodeConcOutInst
  , insertFreshNodeConcOutInstMixed
  , insertFreshNodeConcMixed

  , insertGoal
  , insertAtom
  , insertEdges
  , insertOutKIEdge
  , insertChain
  , insertAction
  , insertLess
  , insertFormula
  , reducibleFormula

  , insertNotBasisElem
  , insertBasisElem
  , insertNoCanc
  , insertDHEdge
  , insertDHEdges
  , insertDHMixedEdge
  , solveNeeded
  , solveNeededList
  , solveNeededList2
  --, setNotReachable

  -- ** Goal management
  , markGoalAsSolved
  , removeSolvedSplitGoals

  -- ** Substitution application
  , substSystem
  , substNodes
  , substEdges
  , substLastAtom
  , substLessAtoms
  , substFormulas
  , substSolvedFormulas

  , normSystem
  , normSystemCR
  , normalizeFact

  -- ** Solving equalities
  , SplitStrategy(..)

  , solveNodeIdEqs
  , solveTermEqs
  , solveFactEqs
  , solveFactDHEqs
  , solveMixedFactEqs
  , solveRuleEqs
  , solveSubstEqs
  , solveIndicatorProto
  , solveIndicator
  , protoCase
  --, solveActionFactDHEqs

  -- ** Conjunction with another constraint 'System'
  , conjoinSystem

  -- ** Convenience export
  , module Logic.Connectives

  ) where

import           Debug.Trace -- .Ignore
import           Prelude                                 hiding (id, (.))

import qualified Data.Foldable                           as F
import qualified Data.Map                                as M
import Data.Maybe (fromJust, isJust)
import qualified Data.Map.Strict                         as M'
import qualified Data.Set                                as S
import qualified Data.ByteString.Char8                   as BC
import           Data.List                               (mapAccumL, delete , subsequences, length , nub, nubBy, permutations, intersect, (\\))
import Data.List.Split (splitPlaces)
import           Safe

import           Control.Basics
import           Control.Category
import           Control.Monad.Bind
import           Control.Monad.Disj
import           Control.Monad.Reader
import           Control.Monad.State                     (StateT, execStateT, gets, runStateT)

import           Text.PrettyPrint.Class

import           Extension.Data.Label
-- import           Extension.Data.Monoid                   (Monoid(..))
import           Extension.Prelude

import           Logic.Connectives

import           Theory.Constraint.Solver.Contradictions
import           Theory.Constraint.Solver.Combination
import           Theory.Constraint.System
import           Theory.Model
import           Utils.Misc
import           Term.DHMultiplication
import           Term.Rewriting.Norm (norm')
import           Theory.Tools.DHActionFacts

------------------------------------------------------------------------------
-- The constraint reduction monad
------------------------------------------------------------------------------

-- | A constraint reduction step. Its state is the current constraint system,
-- it can generate fresh names, split over cases, and access the proof
-- context.
type Reduction = StateT System (FreshT (DisjT (Reader ProofContext)))


-- Executing reductions
-----------------------

-- | Run a constraint reduction. Returns a list of constraint systems whose
-- combined solutions are equal to the solutions of the given system. This
-- property is obviously not enforced, but it must be respected by all
-- functions of type 'Reduction'.
runReduction :: Reduction a -> ProofContext -> System -> FreshState
             -> Disj ((a, System), FreshState)
runReduction m ctxt se fs =  Disj $ (`runReader` ctxt) $ runDisjT $ (`runFreshT` fs) $ runStateT m se

-- | Run a constraint reduction returning only the updated constraint systems
-- and the new freshness states.
execReduction :: Reduction a -> ProofContext -> System -> FreshState
              -> Disj (System, FreshState)
execReduction m ctxt se fs =
    Disj $ (`runReader` ctxt) . runDisjT . (`runFreshT` fs) $ execStateT m se


-- Change management
--------------------

-- | Indicate whether the constraint system was changed or not.
data ChangeIndicator = Unchanged | Changed
       deriving( Eq, Ord, Show )

instance Semigroup ChangeIndicator where
    Changed   <> _         = Changed
    _         <> Changed   = Changed
    Unchanged <> Unchanged = Unchanged

instance Monoid ChangeIndicator where
    mempty = Unchanged

-- | Return 'True' iff there was a change.
wasChanged :: ChangeIndicator -> Bool
wasChanged Changed   = True
wasChanged Unchanged = False

-- | Only apply a monadic action, if there has been a change.
whenChanged :: Monad m => ChangeIndicator -> m () -> m ()
whenChanged = when . wasChanged

-- | Apply a list of changes to the proof state.
applyChangeList :: [Reduction ()] -> Reduction ChangeIndicator
applyChangeList []      = return Unchanged
applyChangeList changes = sequence_ changes >> return Changed

-- | Execute a 'Reduction' as long as it results in changes. Indicate whether
-- at least one change was performed.
whileChanging :: Reduction ChangeIndicator -> Reduction ChangeIndicator
whileChanging reduction =
    go Unchanged
  where
    go indicator = do indicator' <- reduction
                      case indicator' of
                          Unchanged -> return indicator
                          Changed   -> go     indicator'

-- Accessing the proof context
------------------------------

-- | Retrieve the 'ProofContext'.
getProofContext :: Reduction ProofContext
getProofContext = ask

-- | Retrieve the 'MaudeHandle' from the 'ProofContext'.
getMaudeHandle :: Reduction MaudeHandle
getMaudeHandle = askM pcMaudeHandle

-- | Retrieve the 'MaudeHandleDH' from the 'ProofContext'.
getMaudeHandleDH :: Reduction MaudeHandle
getMaudeHandleDH = askM pcMaudeHandleDH

getMaudeHandleCR :: Reduction MaudeHandle
getMaudeHandleCR = askM pcMaudeHandleCR

-- | Retrieve the verbose parameter from the 'ProofContext'.
getVerbose :: Reduction Bool
getVerbose = askM pcVerbose


-- Inserting (fresh) nodes into the constraint system
-----------------------------------------------------

-- | Insert a fresh rule node labelled with a fresh instance of one of the
-- rules and return one of the conclusions.
insertFreshNodeConc :: [RuleAC] -> Reduction (RuleACInst, NodeConc, LNFact)
insertFreshNodeConc rules = do
    (i, ru) <- insertFreshNode rules Nothing
    (v, fa) <- disjunctionOfList $  enumConcs ru
    return (ru, (i, v), fa)

insertFreshNodeConcInst ::  [RuleAC] -> [(NodeId,RuleACInst)] -> Reduction (RuleACInst, NodeConc, LNFact)
insertFreshNodeConcInst rules instrules = do
     (i,ru) <- disjunctionOfList instrules
     (v, fa) <- disjunctionOfList $ [(c,f)|  (c,f) <- enumConcs ru, isDHFact f ]
     return (ru, (i, v), fa)
    `disjunction`
    (do
        (i, ru) <- insertFreshNode rules Nothing
        (v, fa) <- disjunctionOfList $ [(c,f)| (c,f) <- enumConcs ru,  isDHFact f ]
        return (ru, (i, v), fa))

insertFreshNodeConcKI ::  [RuleAC] -> [(NodeId,RuleACInst)] -> Reduction (RuleACInst, NodeConc, (LNFact, LNTerm))
insertFreshNodeConcKI rules instrules = do
      -- irulist <- replicateM n $ traverseDHNodes rules
      irulist <- traverseDHNodes rules
      let pairs = [(ru, (i,c), (f, rterm), mc) | (i, ru, mc) <- irulist, (c,f) <- enumConcs ru, (factTag f == OutFact), isMixedFact f, rterm <- map fst $ extractMixedRoot ((head $ factTerms f)), sortOfLNTerm rterm == LSortE || sortOfLNTerm rterm == LSortFrNZE  ]
      (ru,(i,c),f, mc) <- disjunctionOfList pairs
      exploitNodeId i ru mc 
      return (ru, (i,c),f)
    `disjunction`
    (do 
        let pairs = [(ru, (i,c), (f, rterm)) | (i, ru) <- instrules, (c,f) <- enumConcs ru, (factTag f == OutFact), isMixedFact f, rterm <- map fst $ extractMixedRoot ((head $ factTerms f))  ]
        disjunctionOfList pairs )




insertFreshNodeConcMixed ::  [RuleAC] -> [(NodeId,RuleACInst)] -> Reduction (RuleACInst, NodeConc, LNFact)
insertFreshNodeConcMixed rules instrules = do
      (i,ru) <- disjunctionOfList instrules
      (v, fa) <- disjunctionOfList $ [(c,f)|  (c,f) <- enumConcs ru,  isMixedFact f ]
      return (ru, (i, v), fa)
    `disjunction`
    (do
        (i, ru) <- insertFreshNode rules Nothing
        contradictoryIf (elem i [i | (i,ru) <- instrules])
        (v, fa) <- disjunctionOfList $ [(c,f)| (c,f) <- enumConcs ru, isMixedFact f ]
        return (ru, (i, v), fa))

combinations :: Int -> [a] -> [[a]]
combinations k ns = filter ((k==).length) $ subsequences ns

traverseDHNodes :: [RuleAC] -> Reduction [(NodeId, RuleACInst, Maybe RuleACConstrs)]
traverseDHNodes rules = do
    let m = trace (show "I get here") length rules
    ilist <- replicateM m $ freshLVar "vr" LSortNode
    tuplist <- mapM importRule rules
    return $ zipWith (\i (ru,mrconstrs) -> (i,ru, mrconstrs)) ilist tuplist
  where
    -- | Import a rule with all its variables renamed to fresh variables.
    importRule ru = someRuleACInst ru `evalBindT` noBindings


insertFreshNodeConcOutInst ::  [RuleAC] -> [(NodeId,RuleACInst)] -> Int -> Maybe ((NodeId, RuleACInst, LNFact, ConcIdx), LNTerm) -> Reduction [(RuleACInst, NodeConc, (LNFact, LNTerm), LNTerm, Maybe RuleACConstrs,Bool)]
insertFreshNodeConcOutInst rules instrules n Nothing = do
      -- irulist <- replicateM n $ traverseDHNodes rules
      irulist <- traverseDHNodes rules
      let pairs = [(ru, (i,c), (f, headf), rterm, mconstrs,b) | (i, ru, mconstrs, b) <- ((map (\(a,b)->(a,b,Nothing, False)) instrules)++ (map (\(a,b,c)->(a,b,c, True)) irulist)), (c,f) <- enumConcs ru, (factTag f == OutFact), isMixedFact f, not $ isMuTerm (head $ factTerms f), (rterm, headf) <- extractMixedRoot (head $ factTerms f)]
      disjunctionOfList (nub $ concatMap permutations (nub $ combinations n pairs))
insertFreshNodeConcOutInst rules instrules n (Just ((j,ruj,faConc,cj), ta)) = do
      -- irulist <- replicateM n $ traverseDHNodes rules
      irulist <- traverseDHNodes rules
      let pairs = [(ru, (i,c), (f, headf), rterm, mconstrs,b) | (i, ru, mconstrs, b) <- ((map (\(a,b)->(a,b,Nothing, False)) instrules)++ (map (\(a,b,c)->(a,b,c, True)) irulist)), (c,f) <- enumConcs ru, (factTag f == OutFact), isMixedFact f, not $ isMuTerm (head $ factTerms f), (rterm, headf) <- extractMixedRoot (head $ factTerms f)]
          pairs2 =  [(ruj, (j,cj), (faConc, ta), rterm , Nothing,False) | rterm <- multRootList ta ]
          finallist = nub $ (concatMap permutations (filter ( any (\(a,(i,b),c,d,e,f) -> i==j && a ==ruj)) (combinations n $ pairs++pairs2)) )
      disjunctionOfList finallist


insertFreshNodeConcOutInstMixed ::  [RuleAC] -> [(NodeId,RuleACInst)] -> Reduction (RuleACInst, NodeConc, LNFact)
insertFreshNodeConcOutInstMixed rules instrules = do
      (i,ru) <- disjunctionOfList instrules
      (v, fa) <- disjunctionOfList $ [(c,f)|  (c,f) <- enumConcs ru, (factTag f == OutFact), isMixedFact f ]
      return (ru, (i, v), fa)
    `disjunction`
    (do
            (i, ru) <- insertFreshNode rules Nothing
            (v, fa) <- disjunctionOfList $ [(c,f)| (c,f) <- enumConcs ru, (factTag f == OutFact)]
            return (ru, (i, v), fa))


-- | Insert a fresh rule node labelled with a fresh instance of one of the rules
-- and solve it's 'Fr', 'In', and 'KU' premises immediately.
-- If a parent node is given, updates the remaining rule applications.
insertFreshNode :: [RuleAC] -> Maybe RuleACInst -> Reduction (NodeId, RuleACInst)
insertFreshNode rules parent = do
    i <- freshLVar "vr" LSortNode
    (,) i <$> labelNodeId i rules parent

-- | Label a node-id with a fresh instance of one of the rules and
-- solve it's 'Fr', 'In', and 'KU' premises immediately.
-- If a parent node is given, updates the remaining rule applications.
--
-- PRE: Node must not yet be labelled with a rule.

labelNodeId :: NodeId -> [RuleAC] -> Maybe RuleACInst -> Reduction RuleACInst
labelNodeId = \i rules parent -> do
    (ru1, mrconstrs) <- importRule =<< disjunctionOfList rules
    let ru = case parent of
                Just pa | (getRuleName pa == getRuleName ru1) && (getRemainingRuleApplications pa > 1)
                    -> setRemainingRuleApplications ru1 ((getRemainingRuleApplications pa) - 1)
                _   -> ru1
    exploitNodeId i ru mrconstrs
  where
    -- | Import a rule with all its variables renamed to fresh variables.
    importRule ru = someRuleACInst ru `evalBindT` noBindings


exploitNodeId :: NodeId ->  RuleACInst -> Maybe RuleACConstrs -> Reduction RuleACInst
exploitNodeId i ru mrconstrs = do
    solveRuleConstraints mrconstrs
    modM sNodes (M.insert i ru)
    forM (basisVars ru) insertNotBasisElem
    exploitPrems i ru
    return ru
  where
    mkISendRuleAC ann m = return $ Rule (IntrInfo (ISendRule))
                                    [kuFactAnn ann m] [inFact m] [kLogFact m] []


    mkFreshRuleAC m = Rule (ProtoInfo (ProtoRuleACInstInfo FreshRule [] []))
                           [] [freshFact m] [] [m]

    mkFreshDHRuleAC m = Rule (ProtoInfo (ProtoRuleACInstInfo FreshRule [] []))
                           [] [freshDHFact m] [] [m]

    exploitPrems i ru = mapM_ (exploitPrem i ru) (enumPrems ru)

    exploitPrem i ru (v, fa) = case fa of
        -- CR-rule *DG2_2* specialized for *In* facts.
        -- Fact InFact ann [m] | (not $ isDHFact fa) -> do
        Fact InFact ann [m]  -> do
            j <- freshLVar "vf" LSortNode
            ruKnows <- mkISendRuleAC ann m
            modM sNodes (M.insert j ruKnows)
            modM sEdges (S.insert $ Edge (j, ConcIdx 0) (i, v))
            trace (show ("infacts", m)) $ exploitPrems j ruKnows

        -- CR-rule *DG2_2* specialized for *Fr* facts.
        Fact FreshFact _ [m] -> do
            j <- freshLVar "vf" LSortNode
            modM sNodes (M.insert j (mkFreshRuleAC m))
            unless (isFreshVar m) $ do
                -- 'm' must be of sort fresh ==> enforce via unification
                n <- varTerm <$> freshLVar "n" LSortFresh
                void (solveTermEqs SplitNow [Equal m n])
            modM sEdges (S.insert $ Edge (j, ConcIdx 0) (i,v))

        Fact FreshDHFact _ [m] -> do
            j <- freshLVar "vf" LSortNode
            modM sNodes (M.insert j (mkFreshDHRuleAC m))
            unless (isFrNZEVar m) $ do
                -- 'm' must be of sort fresh ==> enforce via unification
                n <- varTerm <$> freshLVar "n" LSortFrNZE
                void (solveTermEqs SplitNow [Equal m n])
            modM sEdges (S.insert $ Edge (j, ConcIdx 0) (i,v))
        
        _ | (isKUFact fa) -> do
              j <- freshLVar "vk" LSortNode
              insertLess j i Adversary
              void (insertAction j fa)

          -- Store premise goal for later processing using CR-rule *DG2_2*
          | otherwise -> (insertGoal (PremiseG (i,v) fa) (v `elem` breakers))
      where
        breakers = ruleInfo (get praciLoopBreakers) (const []) $ get rInfo ru

-- | Insert a chain constrain.
insertChain :: NodeConc -> NodePrem -> Reduction ()
insertChain c p = insertGoal (ChainG c p) False

-- | Insert an edge constraint. CR-rule *DG1_2* is enforced automatically,
-- i.e., the fact equalities are enforced.
insertEdges :: [(NodeConc, LNFact, LNFact, NodePrem)] -> Reduction ()
insertEdges edges = do
    void (solveFactEqs SplitNow [ Equal fa1 fa2 | (_, fa1, fa2, _) <- edges ])
    modM sEdges (\es -> foldr S.insert es [ Edge c p | (c,_,_,p) <- edges])

insertOutKIEdge :: (NodeConc, LNFact,LNTerm, LNFact, NodePrem) -> Reduction ()
insertOutKIEdge (c, fa1,t1,fa2,p) = do
    trace (show ("solvingfactsoutKI", fa1,fa2) ) $ void (solveFactOutKIEqs SplitNow fa1 t1 fa2)
    trace (show ("inesrting edge", fa1,fa2) ) $ modM sEdges (\es -> foldr S.insert es [ Edge c p ])


-- | Insert an 'Action' atom. Ensures that (almost all) trivial *KU* actions
-- are solved immediately using rule *S_{at,u,triv}*. We currently avoid
-- adding intermediate products. Indicates whether nodes other than the given
-- action have been added to the constraint system.
--
-- FIXME: Ensure that intermediate products are also solved before stating
-- that no rule is applicable.
insertAction :: NodeId -> LNFact -> Reduction ChangeIndicator
insertAction i fa@(Fact _ ann _) = do
    present <- (goal `M.member`) <$> getM sGoals
    isdiff <- getM sDiffSystem
    nodePresent <- (i `M.member`) <$> getM sNodes
    if present
      then do return Unchanged
      else do case kFactView fa of
                Just (UpK, viewTerm2 -> FPair m1 m2) -> do
                -- In the diff case, add pair rule instead of goal
                    if isdiff
                       then do
                          -- if the node is already present in the graph, do not insert it again. (This can be caused by substitutions applying and changing a goal.)
                          if not nodePresent
                             then do
                               modM sNodes (M.insert i (Rule (IntrInfo (ConstrRule $ BC.pack "_pair")) ([(kuFactAnn ann m1),(kuFactAnn ann m2)]) ([fa]) ([fa]) []))
                               insertGoal goal False
                               markGoalAsSolved "pair" goal
                               requiresKU m1 *> requiresKU m2 *> return Changed
                             else do
                               insertGoal goal False
                               markGoalAsSolved "exists" goal
                               return Changed
                       else do
                          insertGoal goal False
                          requiresKU m1 *> requiresKU m2 *> return Changed

                Just (UpK, viewTerm2 -> FInv m) -> do
                -- In the diff case, add inv rule instead of goal
                    if isdiff
                       then do
                          -- if the node is already present in the graph, do not insert it again. (This can be caused by substitutions applying and changing a goal.)
                          if not nodePresent
                             then do
                               modM sNodes (M.insert i (Rule (IntrInfo (ConstrRule $ BC.pack "_inv")) ([(kuFactAnn ann m)]) ([fa]) ([fa]) []))
                               insertGoal goal False
                               markGoalAsSolved "inv" goal
                               requiresKU m *> return Changed
                             else do
                               insertGoal goal False
                               markGoalAsSolved "exists" goal
                               return Changed
                       else do
                          insertGoal goal False
                          requiresKU m *> return Changed

                Just (UpK, viewTerm2 -> FMult ms) -> do
                -- In the diff case, add mult rule instead of goal
                    if isdiff
                       then do
                          -- if the node is already present in the graph, do not insert it again. (This can be caused by substitutions applying and changing a goal.)
                          if not nodePresent
                             then do
                               modM sNodes (M.insert i (Rule (IntrInfo (ConstrRule $ BC.pack "_mult")) (map (\x -> kuFactAnn ann x) ms) ([fa]) ([fa]) []))
                               insertGoal goal False
                               markGoalAsSolved "mult" goal
                               mapM_ requiresKU ms *> return Changed
                             else do
                               insertGoal goal False
                               markGoalAsSolved "exists" goal
                               return Changed

                       else do
                          insertGoal goal False
                          mapM_ requiresKU ms *> return Changed

                Just (UpK, viewTerm2 -> FUnion ms) -> do
                -- In the diff case, add union (?) rule instead of goal
                    if isdiff
                       then do
                          -- if the node is already present in the graph, do not insert it again. (This can be caused by substitutions applying and changing a goal.)
                          if not nodePresent
                             then do
                               modM sNodes (M.insert i (Rule (IntrInfo (ConstrRule $ BC.pack "_union")) (map (\x -> kuFactAnn ann x) ms) ([fa]) ([fa]) []))
                               insertGoal goal False
                               markGoalAsSolved "union" goal
                               mapM_ requiresKU ms *> return Changed
                             else do
                               insertGoal goal False
                               markGoalAsSolved "exists" goal
                               return Changed

                       else do
                          insertGoal goal False
                          mapM_ requiresKU ms *> return Changed

                _ -> do
                    insertGoal goal False
                    return Unchanged
  where
    goal = ActionG i fa
    -- Here we rely on the fact that the action is new. Otherwise, we might
    -- loop due to generating new KU-nodes that are merged immediately.
    requiresKU t = do
      j <- freshLVar "vk" LSortNode
      let faKU = kuFactAnn ann t
      insertLess j i Adversary
      void (insertAction j faKU)

-- | Insert a 'Less' atom. @insertLess i j@ means that *i < j* is added.
insertLess :: NodeId -> NodeId -> Reason-> Reduction ()
insertLess i j r = modM sLessAtoms (S.insert (i, j, r))

-- | Insert a 'Subterm' atom. *x ⊏ y* is added to the SubtermStore
insertSubterm :: LNTerm -> LNTerm -> Reduction ()
insertSubterm x y = setM sSubtermStore . addSubterm (x, y) =<< getM sSubtermStore

-- | Insert the negation of a 'Subterm' atom. *¬ x ⊏ y* is added to the SubtermStore
insertNegSubterm :: LNTerm -> LNTerm -> Reduction()
insertNegSubterm x y = setM sSubtermStore . addNegSubterm (x, y) =<< getM sSubtermStore


insertDHEq :: LNTerm -> LNTerm -> Reduction ()
insertDHEq t1 t2 = insertGoal (DHEqG t1 t2) False

-- | Insert a 'Last' atom and ensure their uniqueness.
insertLast :: NodeId -> Reduction ChangeIndicator
insertLast i = do
    lst <- getM sLastAtom
    case lst of
      Nothing -> setM sLastAtom (Just i) >> return Unchanged
      Just j  -> solveNodeIdEqs [Equal i j]

-- | Insert an atom. Returns 'Changed' if another part of the constraint
-- system than the set of actions was changed.
insertAtom :: LNAtom -> Reduction ()
insertAtom ato = case ato of
    EqE x y       -> if (isDHTerm x && isDHTerm y) then insertDHEq x y else void $ solveTermEqs SplitNow [Equal x y]
    Subterm x y   -> insertSubterm x y
    Action i fa   -> void $ insertAction (ltermNodeId' i) fa
    Less i j      -> insertLess (ltermNodeId' i) (ltermNodeId' j) Formula
    Last i        -> void $ insertLast (ltermNodeId' i)
    Syntactic _   -> return ()

-- | Insert a 'Guarded' formula. Ensures that existentials, conjunctions, negated
-- last atoms, and negated less atoms, are immediately solved using the rules
-- *S_exists*, *S_and*, *S_not,last*, and *S_not,less*. Only the inserted
-- formula is marked as solved. Other intermediate formulas are not marked.
insertFormula :: LNGuarded -> Reduction ()
insertFormula = do
    insert True
  where
    insert mark fm = do
        formulas       <- getM sFormulas
        solvedFormulas <- getM sSolvedFormulas
        insert' mark formulas solvedFormulas fm

    insert' mark formulas solvedFormulas fm
      | fm `S.member` formulas       = return ()
      | fm `S.member` solvedFormulas = return ()
      | otherwise = case fm of
          GAto ato -> do
              markAsSolved
              insertAtom (bvarToLVar ato)

          -- CR-rule *S_∧*
          GConj fms -> do
              markAsSolved
              mapM_ (insert False) (getConj fms)

          -- Store for later applications of CR-rule *S_∨*
          GDisj disj -> do
              modM sFormulas (S.insert fm)
              insertGoal (DisjG disj) False

          -- CR-rule *S_∃*
          GGuarded Ex ss as gf -> do
              -- must always mark as solved, as we otherwise may repeatedly
              -- introduce fresh variables.
              modM sSolvedFormulas $ S.insert fm
              xs <- mapM (uncurry freshLVar) ss
              let body = gconj (map GAto as ++ [gf])
              insert False (substBound (zip [0..] (reverse xs)) body)

          -- CR-rule *S_{¬,⋖}*
          GGuarded All [] [Less i j] gf  | gf == gfalse -> do
              markAsSolved
              insert False (gdisj [GAto (EqE i j), GAto (Less j i)])

          -- negative Subterm
          GGuarded All [] [Subterm i j] gf  | gf == gfalse -> do
              markAsSolved
              insertNegSubterm (bTermToLTerm i) (bTermToLTerm j)

          -- CR-rule: FIXME add this rule to paper
          GGuarded All [] [EqE i@(bltermNodeId -> Just _)
                               j@(bltermNodeId -> Just _) ] gf
            | gf == gfalse -> do
                markAsSolved
                insert False (gdisj [GAto (Less i j), GAto (Less j i)])

          -- CR-rule *S_{¬,last}*
          GGuarded All [] [Last i]   gf  | gf == gfalse -> do
              markAsSolved
              lst <- getM sLastAtom
              j <- case lst of
                     Nothing  -> do j <- freshLVar "last" LSortNode
                                    void (insertLast j)
                                    return (varTerm (Free j))
                     Just j -> return (varTerm (Free j))
              insert False $ gdisj [ GAto (Less j i), GAto (Less i j) ]

          -- Guarded All quantification: store for saturation
          GGuarded All _ _ _ -> modM sFormulas (S.insert fm)
      where
        markAsSolved = when mark $ modM sSolvedFormulas $ S.insert fm

-- | 'True' iff the formula can be reduced by one of the rules implemented in
-- 'insertFormula'.
reducibleFormula :: LNGuarded -> Bool
reducibleFormula fm = case fm of
    GAto _                           -> True
    GConj _                          -> True
    GGuarded Ex _ _ _                -> True
    GGuarded All [] [Less _ _]    gf -> gf == gfalse
    GGuarded All [] [Subterm _ _] gf -> gf == gfalse
    GGuarded All [] [Last _]      gf -> gf == gfalse
    _                                -> False


-- Goal management
------------------

-- | Combine the status of two goals.
combineGoalStatus :: GoalStatus -> GoalStatus -> GoalStatus
combineGoalStatus (GoalStatus solved1 age1 loops1)
                  (GoalStatus solved2 age2 loops2) =
    GoalStatus (solved1 || solved2) (min age1 age2) (loops1 || loops2)

-- | Insert a goal and its status with a new age. Merge status if goal exists.
insertGoalStatus :: Goal -> GoalStatus -> Reduction ()
insertGoalStatus goal status = do
    age <- getM sNextGoalNr
    modM sGoals $ M'.insertWith combineGoalStatus goal (set gsNr age status)
    sNextGoalNr =: succ age

-- | Insert a 'Goal' and store its age.
insertGoal :: Goal -> Bool -> Reduction ()
insertGoal goal looping = insertGoalStatus goal (GoalStatus False 0 looping)

-- | Mark the given goal as solved.
markGoalAsSolved :: String -> Goal -> Reduction ()
markGoalAsSolved how goal =
    case goal of
      ActionG _ _     -> updateStatus
      PremiseG _ fa
        | isKDFact fa -> modM sGoals $ M.delete goal
        | otherwise   -> updateStatus
      ChainG _ _      -> modM sGoals $ M.delete goal
      SplitG _        -> updateStatus
      DisjG disj      -> modM sFormulas       (S.delete $ GDisj disj) >>
                         modM sSolvedFormulas (S.insert $ GDisj disj) >>
                         updateStatus
      SubtermG _      -> updateStatus
      NoCancG _       -> modM sGoals $ M.delete goal
      DHEqG _ _ ->    modM sGoals $ M.delete goal 
  where
    updateStatus = do
        mayStatus <- M.lookup goal <$> getM sGoals
        verbose <- getVerbose
        case mayStatus of
          Just status -> if (verbose) then trace (msg status) $
              modM sGoals $ M.insert goal $ set gsSolved True status else modM sGoals $ M.insert goal $ set gsSolved True status
          Nothing     -> trace ("markGoalAsSolved: inexistent goal " ++ show goal) $ return ()

    msg status = render $ nest 2 $ fsep $
        [ text ("solved goal nr. "++ show (get gsNr status))
          <-> parens (text how) <> colon
        , nest 2 (prettyGoal goal) ]

removeSolvedSplitGoals :: Reduction ()
removeSolvedSplitGoals = do
    goals    <- getM sGoals
    existent <- splitExists <$> getM sEqStore
    sequence_ [ modM sGoals $ M.delete goal
              | goal@(SplitG i) <- M.keys goals, not (existent i) ]


------------------------------------------------------------------------------
 ---- DH multiplication part
------------------------------------------------------------------------------

insertEdge :: (NodeConc, LNFact, LNFact, NodePrem) -> Reduction ()
insertEdge (c, fa1, fa2, p) = do
    void (solveFactEqs SplitNow [ Equal fa1 fa2 ])
    -- modM sEdges (\es -> foldr S.insert es [ Edge c p ])


insertDHEdge ::   (NodeConc, LNFact, LNFact, NodePrem) -> S.Set LNTerm -> S.Set LNTerm -> Reduction ()
insertDHEdge (c, fa1, fa2, p) bset nbset = do --fa1 should be an Out fact
    void (solveFactDHEqs SplitNow fa1 fa2 bset nbset (protoCase SplitNow bset nbset))
    modM sEdges (\es -> foldr S.insert es [ Edge c p ])


doubleFresh :: M.Map NodeId RuleACInst -> Bool
doubleFresh nodes = isitcontr
    where   allprems = map (\(i, ru) -> (i, filter (\f -> isFrDHFact f) $ map snd $ enumPrems ru)) $ M.assocs nodes
            allprems2 = nub $ concatMap snd allprems
            isitcontr = any (\x-> length (filter (\(i,prems) -> elem x prems) allprems) > 1) allprems2


insertMuAction ::  (LNTerm -> NodeId -> Reduction String) ->
      Term (Lit Name LVar) -> NodeId -> Reduction ()
insertMuAction fun x@(LIT l) i | sortOfLNTerm x == LSortFrNZE =  do 
           nodes <- getM sNodes
           let rus = M.elems nodes
               outconcs = concatMap (\ru -> filter isDHFact $ get rConcs ru) rus
           if (elem (outFact x) outconcs ) || (elem (outFact $ fAppdhInv x) outconcs)
             then insertNotBasisElem x
                else do 
                  insertBasisElem x
                  `disjunction` do
                    fun x i
                    insertNotBasisElem x

insertDHEdges :: [(RuleACInst, NodeConc, (LNFact,LNTerm), LNTerm, Maybe RuleACConstrs, Bool)] -> [LNTerm] -> LNTerm -> NodePrem -> 
    (LNTerm -> NodeId -> Reduction String) -> Reduction ()
insertDHEdges tuplelist indts premTerm p fun = do
    let rootpairs = zip (map (\(a,b,(c,t),d,e,f)-> (t,d)) tuplelist) indts
        cllist = nubBy (\(a,b,c,d,e,f) (a2,b2,c2,d2,e2,f2) -> b == b2) tuplelist
        temppairs = map (\((a,b),c)-> a ) rootpairs
    --return ()
    --(faPremsubst, listterms) <- foldM (\faP c -> solveIndFactDH SplitNow c faP) (premTerm,[]) rootpairs
    void substSystem
    nodes <- getM sNodes
    edges <- getM sEdges
    trace (show ("onDHEDges",doubleFresh nodes)) $ contradictoryIf $ doubleFresh nodes
    bset <- getM sBasis
    nbset <- getM sNotBasis
    case neededexponentslist bset nbset temppairs of 
        Nothing -> do
            (faPremsubst, listterms) <-  solveIndFactDH SplitNow rootpairs premTerm
            trace (show ("insertDHedhes", faPremsubst, bset, nbset, listterms)) $ solveIndicator faPremsubst listterms
            forM_ (map (\(_,b,_,_, _, _)->b) cllist) (\c-> (modM sEdges (\es -> foldr S.insert es [ Edge c p ])))
            forM_ (map (\(ru,(i,b),_,_, mc,f)->(i,ru, mc)) (filter (\(ru,_,_,_, mc,b)->b) cllist)) (\(c1,c2,c3) -> exploitNodeId c1 c2 c3)
        Just es -> do
            let les = S.toList es
                fres = filter (\fe -> sortOfLNTerm fe == LSortFrNZE) les
                otheres = les \\ fres
            ifs <- replicateM (length fres) $ freshLVar "vk" LSortNode
            forM_ (zip ifs fres) (\(i,x) -> insertMuAction fun x i)
            (newb,newNb) <- disjunctionOfList $ solveNeededList2 otheres
            trace (show ("insertBasisDHEdges", newb,newNb, "old", bset,nbset,"rootpairs", rootpairs,"temppairs",temppairs, premTerm)) $ forM_ newb (insertBasisElem)
            forM_ newNb (insertNotBasisElem)
            is<- replicateM (length newNb) $ freshLVar "vk" LSortNode
            trace (show ("shouldnotfethereinsertDHEdges1", es)) $ forM_ (zip is newNb) (\(i,x)-> insertGoal (ActionG i (kdhFact x)) False)
            (faPremsubst, listterms) <-  trace (show ("shouldnotfethereinsertDHEdges2", es)) $  solveIndFactDH SplitNow rootpairs premTerm
            --solveNeededList fun (S.toList es)
            trace (show ("tryingthis", es, listterms))  $ solveIndicator faPremsubst listterms
            -- trace (show ("shouldnotfethereinsertDHEdges", es, listterms))  substSystem
            -- return () -- $
            forM_ (map (\(_,b,_,_, _, _)->b) cllist) (\c-> (modM sEdges (\es -> foldr S.insert es [ Edge c p ])))
            forM_ (map (\(ru,(i,b),_,_, mc,f)->(i,ru, mc)) (filter (\(ru,_,_,_, mc,b)->b) cllist)) (\(c1,c2,c3) -> exploitNodeId c1 c2 c3)


insertDHMixedEdge :: Bool -> (NodeConc, LNFact, LNFact, NodePrem) -> RuleACInst
                    -> S.Set LNTerm -> S.Set LNTerm -> [RuleAC] -> [(NodeId, RuleACInst)] ->
                    (LNTerm -> NodeId -> Reduction String) -> Reduction ()
                    --(LNTerm -> NodeId -> StateT System (FreshT (DisjT (Reader ProofContext))) a0) -> Reduction ()
-- fa1 is conclusion, fa2 is premise
insertDHMixedEdge True (c, fa1, fa2, p) cRule bset nbset rules rulesinst fun = do --fa1 should be an Out fact
    (solveMixedFactEqs SplitNow (Equal fa2 fa1) bset nbset (protoCase SplitNow bset nbset) )
    modM sEdges (\es -> foldr S.insert es [ Edge c p ])
insertDHMixedEdge False ((ic,c), fa1, fa2, p) cRule bset nbset rules rulesinst fun= do --fa1 should be an Out fact
    let chainFun = solveTermDHEqsChain SplitNow Nothing rules rulesinst fun p fa2 (ic, cRule, fa1, c)
    (solveMixedFactEqs SplitNow (Equal fa2 fa1) bset nbset chainFun)
    return ()-- (modM sEdges (\es -> foldr S.insert es [ Edge (ic,c) p ]))


insertBasisElem :: LNTerm -> Reduction ()
insertBasisElem x = do
    modM sBasis (\es -> S.insert x es)

insertNotBasisElem :: LNTerm -> Reduction ()
insertNotBasisElem x = do
    modM sNotBasis (\es -> S.insert x es)

insertNoCanc :: LNTerm -> LNTerm -> Reduction ()
insertNoCanc x y = do
    modM sNoCanc (\es -> S.insert (x,y) es)



------------------------------------------------------------------------------

-- Substitution
---------------

-- | Apply the current substitution of the equation store to the remainder of
-- the sequent.
substSystem :: Reduction ChangeIndicator
substSystem = do
    c1 <- substNodes
    substEdges
    substNoCanc
    substBasis
    substNotBasis
    substGNotBasis
    substLastAtom
    substLessAtoms
    substSubtermStore
    substFormulas
    substSolvedFormulas
    substLemmas
    c2 <- substGoals
    substNextGoalNr
    return (c1 <> c2)

-- no invariants to maintain here
substEdges, substLessAtoms, substSubtermStore, substLastAtom, substFormulas,
  substSolvedFormulas, substLemmas, substNextGoalNr :: Reduction ()

substEdges          = substPart sEdges
substNoCanc         = substPart sNoCanc
substBasis          = substPart sBasis
substNotBasis       = substPart sNotBasis
substGNotBasis      = substPart sGNotBasis

substLessAtoms      = substPart sLessAtoms
substSubtermStore   = substPart sSubtermStore
substLastAtom       = substPart sLastAtom
substFormulas       = substPart sFormulas
substSolvedFormulas = substPart sSolvedFormulas
substLemmas         = substPart sLemmas
substNextGoalNr     = return ()


-- | Apply the current substitution of the equation store to a part of the
-- sequent. This is an internal function.
substPart :: Apply LNSubst a => (System :-> a) -> Reduction ()
substPart l = do subst <- getM sSubst
                 modM l (apply subst)

-- | Apply the current substitution of the equation store the nodes of the
-- constraint system. Indicates whether additional equalities were added to
-- the equations store.

getFrVars :: LNFact -> LVar
getFrVars fct = case (head $ factTerms fct) of 
    LIT (Var v) -> v
    _ -> error "fresh fact should have variable terms"

{-
cyclicSubstNode :: (NodeId, RuleACInst) -> LNSubst -> Bool
cyclicSubstNode (nodeid, ru) subst = trace (show ("cyclicsubstnode", subst, freshpremises, premisevars, varsrange, any (`elem` varsrange) freshvars)) $ any (`elem` varsrange) freshvars
    where premisefacts = map snd $ enumPrems ru
          freshpremises = filter isFrDHFact premisefacts
          freshvars = map getFrVars freshpremises
          premisevars = concatMap varsVTerm (concatMap factTerms premisefacts)
          premisevars' = premisevars \\ freshvars
          varsrange = varsRange (restrict premisevars' subst)-}

cyclicSubstNode :: (NodeId, RuleACInst) -> Bool
cyclicSubstNode (nodeid, ru) =  any (`elem` premisevars) freshvars
    where premisefacts = map snd $ enumPrems ru
          freshpremises = filter isFrDHFact premisefacts
          freshvars = map getFrVars freshpremises
          notfreshpremises = filter (not . isFrDHFact) premisefacts
          premisevars = concatMap varsVTerm (concatMap factTerms notfreshpremises)

substNodes :: Reduction ChangeIndicator
substNodes =
    substNodeIds <* ((modM sNodes . M.map . apply) =<< getM sSubst)

-- | @setNodes nodes@ normalizes the @nodes@ such that node ids are unique and
-- then updates the @sNodes@ field of the proof state to the corresponding map.
-- Return @True@ iff new equalities have been added to the equation store.
setNodes :: [(NodeId, RuleACInst)] -> Reduction ChangeIndicator
setNodes nodes0 = do
    sNodes =: M.fromList nodes
    if null ruleEqs then                                    return Unchanged
                    else solveRuleEqs SplitLater ruleEqs >> return Changed
  where
    -- merge nodes with equal node id
    (ruleEqs, nodes) = first concat $ unzip $ map merge $ groupSortOn fst nodes0

    merge []            = unreachable "setNodes"
    merge (keep:remove) = (map (Equal (snd keep) . snd) remove, keep)

-- | Apply the current substitution of the equation store to the node ids and
-- ensure uniqueness of the labels, as required by rule *U_lbl*. Indicates
-- whether there where new equalities added to the equations store.
substNodeIds :: Reduction ChangeIndicator
substNodeIds =
    whileChanging $ do
        subst <- getM sSubst
        nodes <- gets (map (first (apply subst)) . M.toList . get sNodes)
        setNodes nodes

-- | Substitute all goals. Keep the ones with the lower nr.
substGoals :: Reduction ChangeIndicator
substGoals = do
    subst <- getM sSubst
    goals <- M.toList <$> getM sGoals
    sGoals =: M.empty
    changes <- forM goals $ \(goal, status) -> case goal of
        -- Look out for KU-actions that might need to be solved again.
        ActionG i fa@(kFactView -> Just (UpK, m))
          | (isMsgVar m || isProduct m || isUnion m {--|| isXor m-}) && (apply subst m /= m) ->
              insertAction i (apply subst fa)
        _ -> do modM sGoals $
                  M'.insertWith combineGoalStatus (apply subst goal) status
                return Unchanged
    return (mconcat changes)


-- Conjoining two constraint systems
------------------------------------

-- | @conjoinSystem se@ conjoins the logical information in @se@ to the
-- constraint system. It assumes that the free variables in @se@ are shared
-- with the free variables in the proof state.
conjoinSystem :: System -> Reduction ()
conjoinSystem sys = do
    kind <- getM sSourceKind
    unless (kind == get sSourceKind sys) $
        error "conjoinSystem: source-kind mismatch"
    joinSets sSolvedFormulas
    joinSets sLemmas
    joinSets sEdges
    F.mapM_ insertLast                 $ get sLastAtom    sys
    F.mapM_  (uncurry3 insertLess)     $ get sLessAtoms   sys
    -- split-goals are not valid anymore
    mapM_   (uncurry insertGoalStatus) $ filter (not . isSplitGoal . fst) $ M.toList $ get sGoals sys
    F.mapM_ insertFormula $ get sFormulas sys
    -- update nodes
    _ <- (setNodes . (M.toList (get sNodes sys) ++) . M.toList) =<< getM sNodes
    -- conjoin equation store
    eqs <- getM sEqStore
    let (eqs',splitIds) = (mapAccumL addDisj eqs (map snd . getConj $ get sConjDisjEqs sys))
    setM sEqStore eqs'
    -- conjoin subterm store
    modM sSubtermStore (conjoinSubtermStores (get sSubtermStore sys))
    -- add split-goals for all disjunctions of sys
    mapM_  (`insertGoal` False) $ SplitG <$> splitIds
    void (solveSubstEqs SplitNow $ get sSubst sys)
    -- Propagate substitution changes. Ignore change indicator, as it is
    -- assumed to be 'Changed' by default.
    void substSystem
  where
    joinSets :: Ord a => (System :-> S.Set a) -> Reduction ()
    joinSets proj = modM proj (`S.union` get proj sys)




-- Normalization
---------------
-- TODO: Ideally, we'd like a function that normalizes the entire Constraint System. 
-- (how come it doesn't already exist??+)
-- | Normalize the entire system.
normSystem :: Reduction ChangeIndicator
normSystem = do
    hnd <- getMaudeHandle
    nodes <- getM sNodes
    setM sNodes $ M.map (\r -> runReader (normRule r) hnd) nodes
    --edges <- getM sEdges
    --substEdges
    nocanc <- getM sNoCanc
    setM sNoCanc $ S.map (\(t1,t2) -> (runReader (norm' t1) hnd,runReader (norm' t2) hnd )) nocanc
    basis <- getM sBasis
    setM sBasis $ S.map (\t1 -> (runReader (norm' t1) hnd)) basis
    notbasis <- getM sNotBasis
    setM sNotBasis $ S.map (\t1 -> (runReader (norm' t1) hnd)) notbasis
    gnotbasis <- getM sGNotBasis
    setM sGNotBasis $ S.map (\t1 -> (runReader (norm' t1) hnd)) gnotbasis
    c2 <- normGoals hnd
    return c2


normalizeFact :: MaudeHandle -> LNFact -> LNFact
normalizeFact hnd fa@(Fact f1 f2 faterms) = Fact f1 f2 (map (\t-> runReader (norm' t) hnd) faterms)

normalizeGoal :: MaudeHandle -> Goal -> Goal
normalizeGoal hnd goal = case goal of
        ActionG v fact -> ActionG v $ normalizeFact hnd fact
        PremiseG prem fact -> PremiseG prem $ normalizeFact hnd fact
        NoCancG (t1, t2) -> NoCancG (runReader (norm' t1) hnd, runReader (norm' t2) hnd)
        DHEqG t1 t2 -> DHEqG (runReader (norm' t1) hnd) (runReader (norm' t2) hnd)
        _ -> goal

normalizeGoalCR :: MaudeHandle -> Goal -> Goal
normalizeGoalCR hnd goal = case goal of
        ActionG v fact -> ActionG v $ normFactCR fact hnd
        PremiseG prem fact -> (PremiseG prem $ normFactCR fact hnd)
        NoCancG (t1, t2) -> NoCancG (normTermCR t1 hnd, normTermCR t2 hnd)
        DHEqG t1 t2 -> DHEqG (normTermCR t1 hnd) (normTermCR t2 hnd)
        _ -> goal

normGoals :: MaudeHandle -> Reduction ChangeIndicator
normGoals hnd = do
    goals <- M.toList <$> getM sGoals
    sGoals =: M.empty
    changes <- forM goals $ \(goal, status) ->  do modM sGoals $
                                                     M'.insertWith combineGoalStatus (normalizeGoal hnd goal) status
                                                   return Unchanged
    return (mconcat changes)


normGoalsCR :: MaudeHandle -> Reduction ChangeIndicator
normGoalsCR hnd = do
    goals <- M.toList <$> getM sGoals
    sGoals =: M.empty
    changes <- forM goals $ \(goal, status) ->  do modM sGoals $
                                                     M'.insertWith combineGoalStatus (normalizeGoalCR hnd goal) status
                                                   return Unchanged
    return (mconcat changes)

normSystemCR :: Reduction ChangeIndicator
normSystemCR = do
    hnd <- getMaudeHandleCR
    nodes <- getM sNodes
    setM sNodes $ M.map (\r -> runReader (normRuleCR r) hnd) nodes
    nodes' <- getM sNodes
    contradictoryIf $ any (cyclicSubstNode) (M.toList nodes')
    nocanc <- getM sNoCanc
    setM sNoCanc $ S.map (\(t1,t2) -> (normTermCR t1 hnd, normTermCR t2 hnd )) nocanc
    basis <- getM sBasis
    setM sBasis $ S.map (\t1 -> (normTermCR t1 hnd)) basis
    notbasis <- getM sNotBasis
    setM sNotBasis $ S.map (\t1 -> (normTermCR t1 hnd)) notbasis
    c2 <- normGoalsCR hnd
    return c2


-- Unification via the equation store
-------------------------------------

-- | 'SplitStrategy' denotes if the equation store should be split into
-- multiple equation stores.
data SplitStrategy = SplitNow | SplitLater

-- The 'ChangeIndicator' indicates whether at least one non-trivial equality
-- was solved.

-- | @noContradictoryEqStore@ succeeds iff the equation store is not
-- contradictory.
noContradictoryEqStore :: Reduction ()
noContradictoryEqStore = (contradictoryIf . eqsIsFalse) =<< getM sEqStore

--noContradictoryDHEqStore :: Reduction ()
--noContradictoryDHEqStore = (contradictoryIf . eqsIsFalse) =<< getM sDHEqStore

-- | Add a list of term equalities to the equation store. And
--  split resulting disjunction of equations according
--  to given split strategy.
--
-- Note that updating the remaining parts of the constraint system with the
-- substitution has to be performed using a separate call to 'substSystem'.
solveTermEqs :: SplitStrategy -> [Equal LNTerm] -> Reduction ChangeIndicator
solveTermEqs splitStrat eqs0 =
    case filter (not . evalEqual) eqs0 of
      []  -> do return Unchanged
      eqs1 -> do
        hnd <- getMaudeHandle
        se  <- gets id
        (eqs2, maySplitId) <- addEqs hnd eqs1 =<< getM sEqStore
        setM sEqStore
            =<< simp hnd (substCreatesNonNormalTerms hnd se)
            =<< case (maySplitId, splitStrat) of
                  (Just splitId, SplitNow) -> disjunctionOfList
                                                $ fromJustNote "solveTermEqs"
                                                $ performSplit eqs2 splitId
                  (Just splitId, SplitLater) -> do
                      insertGoal (SplitG splitId) False
                      return eqs2
                  _                        -> return eqs2
        noContradictoryEqStore
        return Changed

solveMixedTermEqs :: SplitStrategy -> S.Set LNTerm -> S.Set LNTerm  -> ((LNTerm,LNTerm)->Reduction ChangeIndicator) -> (LNTerm, LNTerm) -> Reduction ChangeIndicator
solveMixedTermEqs splitStrat bset nbset fun (lhs,rhs)
    | (evalEqual (Equal lhs rhs)) = return Unchanged
    | isDHTerm lhs && isDHTerm rhs = (solveTermDHEqs splitStrat fun) (lhs,rhs)
    | isMixedTerm rhs = do
        (cleanedlhs, lhsDHvars) <- clean lhs
        (cleanedrhs, rhsDHvars) <- clean rhs
        hnd <- getMaudeHandle
        se  <- gets id
        (eqs2, maySplitId,dheqs) <- addMixedEqs hnd [Equal cleanedlhs cleanedrhs] ((map fst lhsDHvars) ++ (map fst rhsDHvars)) =<< getM sEqStore
        setM sEqStore
            =<< simp hnd (substCreatesNonNormalTerms hnd se)
            =<< case (maySplitId, splitStrat) of
                  (Just splitId, SplitNow) -> disjunctionOfList
                                                $ fromJustNote "solveTermEqs"
                                                $ performSplit eqs2 splitId
                  (Just splitId, SplitLater) -> do
                      insertGoal (SplitG splitId) False
                      return eqs2
                  _                        -> return eqs2
        let substdhvars = map (\(a,b) -> (applyVTerm compsubst a, applyVTerm compsubst b)) dheqs
            compsubst = substFromList (lhsDHvars ++ rhsDHvars)
        eqStore <- getM sEqStore 
        setM sEqStore $ applyEqStore hnd (compsubst) eqStore
        void substSystem
        if all (\x -> elem x (varsVTerm lhs) ) (concatMap varsVTerm (map fst substdhvars))
            then solveListDHEqs (solveTermDHEqs splitStrat (protoCase SplitNow bset nbset)) substdhvars
            else solveListDHEqs (\(a,b)-> solveTermDHEqs splitStrat (protoCase SplitNow bset nbset) (b,a)) substdhvars
        noContradictoryEqStore
        return Changed
    | otherwise =  solveTermEqs splitStrat [(Equal lhs rhs)]




normalizeSubstList :: MaudeHandle -> [(LVar, LNTerm)] -> [(LVar, LNTerm)]
normalizeSubstList hnd [] = []
normalizeSubstList hnd [(t,t2)] = [(t, runReader ( norm' t2) hnd)]
normalizeSubstList hnd ((t,t2) : xs) = (t, runReader ( norm' t2) hnd):(normalizeSubstList hnd xs)


multiplyterm :: LVar -> LNTerm -> LNTerm 
multiplyterm wvar t@(LIT l) = if (sortOfLNTerm t == LSortVarE) then t else fAppdhTimesE(varTerm wvar, t)
multiplyterm wvar t@(FAPP (DHMult o) ts) = case ts of
    [ t1, t2 ] | o == dhTimesSym   -> if null (varTermsOf t) then fAppdhTimes (varTerm wvar,t) else t
    [ t1, t2 ] | o == dhTimesESym   -> if null (varTermsOf t) then fAppdhTimes (varTerm wvar,t) else t
    [t1 ,t2]   | o == dhPlusSym -> fAppdhPlus (multiplyterm wvar t1, multiplyterm wvar t2)
    [t1 ,t2]   | o == dhMultSym -> fAppdhMult (multiplyterm wvar t1, multiplyterm wvar t2)
    [ t1, t2 ] | o == dhExpSym   -> multiplyterm wvar t2
    [ t1 ]     | o == dhInvSym    -> fAppdhTimes (varTerm wvar, t) 
    [ t1 ]     | o == dhGinvSym    -> multiplyterm wvar t1
    [ t1 ]     | o == dhMinusSym    -> fAppdhTimes (varTerm wvar, t)
    [ t1 ]     | o == dhMuSym    -> fAppdhTimes (varTerm wvar, t)  --TODO: not sure what to do here? t1 is actually a G term??
    []         | o == dhZeroSym    -> t
    []         | o == dhOneSym    -> t
    _                               -> error $ "this shouldn't have happened, unexpected term form: `"++show t++"'"


monomials :: LNTerm -> [LNTerm]
monomials t@(viewTerm2 -> FdhPlus t1 t2) = (monomials t1) ++ (monomials t2)
monomials t@(viewTerm2 -> FdhTimes t1 t2) = [t]
monomials t@(viewTerm2 -> FdhTimesE t1 t2) = [t]
monomials t@(viewTerm2 -> FdhMinus t2) = monomials t2
monomials t = [t]

secretmonomials :: [LNTerm] -> LNTerm -> LNTerm -> [LNTerm]
secretmonomials bb indt t@(viewTerm2 -> FdhPlus t1 t2) = (secretmonomials bb indt t1) ++ (secretmonomials bb indt t2)
secretmonomials bb indt t@(viewTerm2 -> FdhTimes t1 t2) = if null newsecrets then [] else [foldr (\a b -> if b == fAppdhOne then a else fAppdhTimes (a,b)) fAppdhOne newsecrets]
        where newsecrets = map (\v -> varTerm v) ( ((nub $ varsVTerm t) \\ (nub $ varsVTerm indt)) `intersect` (concatMap varsVTerm bb))
secretmonomials bb indt t@(viewTerm2 -> FdhTimesE t1 t2) = if null newsecrets then [] else [foldr (\a b -> if b == fAppdhOne then a else fAppdhTimes (a,b)) fAppdhOne newsecrets]
        where newsecrets = map (\v -> varTerm v) ( ((nub $ varsVTerm t) \\ (nub $ varsVTerm indt)) `intersect` (concatMap varsVTerm bb))
secretmonomials bb indt t@(viewTerm2 -> FdhMinus t2) = secretmonomials bb indt t2
secretmonomials _ _ _ = []

solveIndicator ::  LNTerm -> [LNTerm] -> Reduction String
solveIndicator t22 terms2  = do
  let t2 = trace (show ("nowsolving", t22, terms2)) $ gTerm2Exp t22
      terms = map gTerm2Exp terms2
  hndNormal  <- getMaudeHandle
  bb <- getM sBasis
  let newsecretvars = trace (show ("nowsolving", t2, terms, bb)) $ (( (nub $ concatMap varsVTerm terms) \\ (nub $ varsVTerm t22)) ) `intersect` (concatMap varsVTerm $ S.toList bb)
      secretmonoms = concatMap (secretmonomials (S.toList bb) t22) terms 
  zvars <- replicateM (length secretmonoms) $ freshLVar "zz" LSortVarE 
  js <- freshLVar "jz" LSortNode
  wvars <- replicateM (length terms) $ freshLVar "wy" LSortVarE
  is <- replicateM (length terms + 1) $ freshLVar "iw" LSortNode
  wvarextra <- freshLVar "ww" LSortVarE
  trace (show ("secretmons", secretmonoms)) $ forM_ (zip (map varTerm (wvars ++ [wvarextra])) (is)) (\(t,i)-> insertAction i (kLogFact t) ) -- kdhFact 
  let genterms = zipWith multiplyterm wvars terms
      extraterms = zipWith (\a b -> fAppdhTimesE (a, varTerm b)) secretmonoms zvars 
      extraterm = runReader (norm' $ foldr (\a b -> if b == fAppdhZero then a else fAppdhPlus (a,b)) fAppdhZero extraterms) hndNormal 
      advterm = runReader (norm' $ foldr (\a b -> fAppdhPlus (a,b)) (varTerm wvarextra) genterms) hndNormal 
      advterm2 = if null extraterms then advterm else fAppdhPlus (advterm, extraterm)
      nt2 = runReader (norm' t2) hndNormal
      matrixvars = getVariablesOfK [nt2,advterm2]   
      kterm = if sortOfLNTerm (head terms2) == LSortG then fAppdhExp(pubGTerm "g", extraterm) else extraterm
  forM_ (if null newsecretvars then [] else [kterm]) (\t -> insertAction js (kdhFact t)) --kdhFact     
  freevars <- replicateM (length matrixvars) $ freshLVar "vy" LSortE
  if length matrixvars >1 
    then solveIndicatorKFacts (map varTerm freevars) nt2 advterm2 `disjunction` (solveIndicatorKFacts2 (map varTerm freevars) nt2 advterm2)
    else solveIndicatorKFacts (map varTerm freevars) nt2 advterm2



variableCheck :: LNTerm -> [(LVar, LNTerm)] -> LNTerm -> [(LVar,LNTerm)] -> Bool 
variableCheck t1 subst12 t2 normsubst =  elem True (concatMap (\v -> map (checkvar v) (getvars v) ) problematicvars)
    where mumap = M.fromList subst12
          allvars = M.keys mumap
          substmap = M.fromList normsubst
          substvars = varsRange $ substFromList normsubst
          problematicvars = filter (`elem` allvars) substvars
          value v mumap = fromJust (M.lookup v mumap)
          getvars v = filter (\x -> isvarGVar (LIT (Var x)) || isvarEVar (LIT (Var x))) $ varsVTerm (value v mumap)
          checkvar v varv = elem v $ varsVTerm (value varv substmap)

solveIndicatorProto2 :: [LNTerm] -> LNTerm -> LNTerm -> Reduction String
solveIndicatorProto2 basis t1 t2 = do
  hnd  <- getMaudeHandle
  let matrixvars = getVariablesOf [t1, t2]
      subst0 = substFromList [(fromJust $ getVar (head matrixvars), fAppdhZero)]
      newt1 =  runReader (norm' $ applyVTerm subst0 t1) hnd
      newt2 = runReader (norm' $ applyVTerm subst0 t2) hnd
  eqStore <- getM sEqStore
  setM sEqStore $ applyEqStore hnd subst0 eqStore
  void substSystem
  void normSystem
  bb <- disjunctionOfList $ (solveIndicatorGaussProto hnd basis newt1 newt2)
  case bb of
   Just substlist ->  do
        eqStore <-  getM sEqStore
        hndCR <- getMaudeHandleCR
        (subst', subst12) <- disjunctionOfList substlist
        let normsubst = (normalizeSubstList hndCR subst') 
        contradictoryIf $ variableCheck t1 subst12 t2 normsubst
        let normsubst' = compose (substFromList subst12) (substFromList normsubst)
        setM sEqStore $ applyEqStore hnd (normsubst') eqStore
        neweqstore <- getM sEqStore
        let oldsubsts =  _eqsSubst neweqstore
            newsubst =  substFromList $ normalizeSubstList hnd (substToList oldsubsts)
            newsubstCR = substFromList $ normalizeSubstList hnd $ normalizeSubstList hndCR (substToList oldsubsts) 
        setM sEqStore ( neweqstore{_eqsSubst = newsubst} )
        void substSystem
        void normSystemCR
        let normedpair = (runReader (norm' $ fAppPair ((applyVTerm newsubstCR t1, applyVTerm newsubstCR t2))) hnd)
            unpair t = case viewTerm t of
                            (FApp (NoEq pairSym) [x, y]) ->(x,y)
                            _ -> error $ "something went wrong" ++ show t
            (sta1,sta2) =  unpair normedpair
        contradictoryIf (not (sta1 == sta2)) 
        void normSystem
        return "Matched"
   Nothing -> do
          contradictoryIf True
          return "CONTRADICTION"          

solveIndicatorProto :: [LNTerm] -> LNTerm -> LNTerm -> Reduction String
solveIndicatorProto basis t1 t2 = do
  hnd  <- getMaudeHandle
  bb <- disjunctionOfList $ (solveIndicatorGaussProto hnd basis t1 t2 )
  case bb of
   Just substlist ->  do
        eqStore <-  getM sEqStore
        hndCR <- getMaudeHandleCR
        bset <- getM sNotBasis
        (subst', subst12) <- disjunctionOfList substlist
        let normsubst = (normalizeSubstList hndCR subst') 
        contradictoryIf $ variableCheck t1 subst12 t2 normsubst
        -- hndCR
        let normsubst' = compose (substFromList subst12) (substFromList normsubst)
        setM sEqStore $ applyEqStore hnd (normsubst') eqStore
        neweqstore <- getM sEqStore
        let oldsubsts =  _eqsSubst neweqstore
            newsubst =  substFromList $ normalizeSubstList hnd (substToList oldsubsts)
            newsubstCR = substFromList $ normalizeSubstList hnd $ normalizeSubstList hndCR (substToList oldsubsts) 
        setM sEqStore ( neweqstore{_eqsSubst = newsubst} )
        void substSystem
        void normSystemCR
        let normedpair = (runReader (norm' $ fAppPair ((applyVTerm newsubstCR t1, applyVTerm newsubstCR t2))) hnd)
            unpair t = case viewTerm t of
                            (FApp (NoEq pairSym) [x, y]) ->(x,y)
                            _ -> error $ "something went wrong" ++ show t
            (sta1,sta2) =  unpair normedpair
        contradictoryIf (not (sta1 == sta2))       
        void normSystem
        return "Matched"
   Nothing -> do
          contradictoryIf True
          return "CONTRADICTION"



solveIndicatorKFacts :: [LNTerm] -> LNTerm -> LNTerm -> Reduction String
solveIndicatorKFacts basis t1 t2 = do
  hnd  <- trace (show ("KFACTS", t1,t2, basis)) getMaudeHandle
  nb <- getM sNotBasis
  bb <-getM sBasis
  let bb = (solveIndicatorGauss3 hnd (S.toList nb) basis t2 t1 )
  case bb of
   Just substlist ->  do
        eqStore <-  trace (show ("thisissolution", substlist))$ getM sEqStore
        hndCR <- trace (show ("thisiseqStore", eqStore))$ getMaudeHandleCR
        (subst') <- disjunctionOfList substlist
        let checksub = substFromList subst'
        trace (show ("contr", subst',(dom checksub `intersect` varsRange checksub /= []))) $ contradictoryIf (dom checksub `intersect` varsRange checksub /= [])
        let normsubst = trace (show ("tryingthis", subst')) (normalizeSubstList hndCR subst') 
        setM sEqStore $ applyEqStore hnd (substFromList normsubst) eqStore
        neweqstore <- getM sEqStore
        let oldsubsts =  _eqsSubst neweqstore
            newsubst =  substFromList $ normalizeSubstList hnd (substToList oldsubsts)
        setM sEqStore ( neweqstore{_eqsSubst = newsubst} )
        void substSystem
        void normSystemCR
        subst <- getM sSubst
        let normedpair = (runReader (norm' $ fAppPair ((applyVTerm subst t1, applyVTerm subst t2))) hnd)
            unpair t = case viewTerm t of
                            (FApp (NoEq pairSym) [x, y]) ->(x,y)
                            _ -> error $ "something went wrong" ++ show t
            (sta1,sta2) =  unpair normedpair
        trace (show ("solutionfound", sta1,sta2, "nb", nb, bb)) $ contradictoryIf (not (sta1 == sta2))                                 
        void normSystem
        return "Matched"
   Nothing -> do
          contradictoryIf True
          return "CONTRADICTION"


solveIndicatorKFacts2 :: [LNTerm] -> LNTerm -> LNTerm -> Reduction String
solveIndicatorKFacts2 basis t1 t2 = do
  hnd  <- getMaudeHandle
  nb <- getM sNotBasis
  let matrixvars =  getVariablesOfK [t1, t2]
      subst0 = substFromList [(fromJust $ getVar (head matrixvars), fAppdhZero)]
      newt1 = runReader (norm' $ applyVTerm subst0 t1) hnd
      newt2 = runReader (norm' $ applyVTerm subst0 t2) hnd
  eqStore <- getM sEqStore
  setM sEqStore $ applyEqStore hnd subst0 eqStore
  void substSystem
  void normSystem
  let bb = (solveIndicatorGauss3 hnd (S.toList nb) basis t2 t1 )
  case bb of
   Just substlist ->  do
        eqStore <-  getM sEqStore
        hndCR <- getMaudeHandleCR
        (subst') <- disjunctionOfList substlist
        let checksub = substFromList subst'
        contradictoryIf (dom checksub `intersect` varsRange checksub /= [])
        let normsubst = (normalizeSubstList hndCR subst') 
        setM sEqStore $ applyEqStore hnd (substFromList normsubst) eqStore
        neweqstore <- getM sEqStore
        let oldsubsts =  _eqsSubst neweqstore
            newsubst =  substFromList $ normalizeSubstList hnd (substToList oldsubsts)
        setM sEqStore ( neweqstore{_eqsSubst = newsubst} )
        void substSystem
        void normSystemCR
        subst <- getM sSubst
        let normedpair = (runReader (norm' $ fAppPair ((applyVTerm subst t1, applyVTerm subst t2))) hnd)
            unpair t = case viewTerm t of
                            (FApp (NoEq pairSym) [x, y]) ->(x,y)
                            _ -> error $ "something went wrong" ++ show t
            (sta1,sta2) =  unpair normedpair
        contradictoryIf (not (sta1 == sta2))                                 
        void normSystem
        return "Matched"
   Nothing -> do
          contradictoryIf True
          return "CONTRADICTION"



solveDHProtoEqsAux :: SplitStrategy -> S.Set LNTerm  -> S.Set LNTerm -> MaudeHandle -> MaudeHandle -> [LVar] -> [LNTerm] -> LNTerm -> LNTerm -> [LNTerm] -> StateT System (FreshT (DisjT (Reader ProofContext))) ()
solveDHProtoEqsAux splitStrat bset nbset hndNormal hnd allevars xindterms ta1 ta2 permutedlist= do
    -- permutedlist <- disjunctionOfList $ permutations outterms
    zzs <- replicateM (length xindterms) $ freshLVar "zz" LSortE
    let genindterms = zipWith (\i z-> (i, runReader (norm' $ fAppdhExp (i, LIT (Var z)) ) hndNormal, z) ) xindterms zzs
    --  let genindterms = zip xindterms zzs
    eqstore <- getM sEqStore
    (eqs2, maySplitId) <- addDHProtoEqs hnd allevars genindterms permutedlist False eqstore
    se  <-  gets id
    setM sEqStore =<< simp hnd (substCreatesNonNormalTerms hnd se) eqs2
    noContradictoryEqStore
    -- setM sEqStore eqs2 
    subst <- getM sSubst
    let substlist =  M.fromList $ substToList subst
        newvars = concatMap (\e -> filter (\v->sortOfLNTerm (varTerm v) == LSortE) $ varsVTerm $ substlist M.! e) allevars
        varta1 = filter (\x -> not (isvarEVar (LIT (Var x)) || isvarGVar (LIT (Var x)))) $ varsVTerm ta1
        varta2 = filter (\x -> not (isvarEVar (LIT (Var x)) || isvarGVar (LIT (Var x)))) $ varsVTerm ta2
        varsta1 = filter (\x -> not (isvarEVar (LIT (Var x)) || isvarGVar (LIT (Var x)))) $ varsVTerm (apply subst ta1)
        varsta2 = filter (\x -> not (isvarEVar (LIT (Var x)) || isvarGVar (LIT (Var x)))) $ varsVTerm (apply subst ta2)
        toset1 = filter (\x -> (isEVar (LIT (Var x))) && (x `elem` (varsRange subst) ) ) $ (varsta1 \\ varsta2) ++ (varsta2 \\ varsta1)
        toset2 = toset1 \\ newvars
    if  null toset2
     then do
        noContradictoryEqStore
        let normedpair = (runReader (norm' $ fAppPair (apply subst ta1, apply subst ta2)) hndNormal)
            unpair t = case viewTerm t of
                        (FApp (NoEq pairSym) [x, y]) ->(x,y)
                        _ -> error $ "something went wrong" ++ show t
            (sta1,sta2) =  unpair normedpair
        case varTermsOf sta2 of
            [] -> case varTermsOf (sta1) of
                    [] -> do
                            if sta1 == sta2
                              then do
                                            void substSystem
                                            void normSystem
                              else contradictoryIf True
                    _  -> do
                            void substSystem
                            let matrixvars = getVariablesOf [sta1, sta2]
                            freevars <- replicateM (length matrixvars) $ freshLVar "vy" LSortE
                            if length matrixvars >1 
                              
                              then (solveIndicatorProto (map varTerm freevars) sta1 sta2
                                `disjunction`
                                    solveIndicatorProto2 (map varTerm freevars) sta1 sta2)
                              else solveIndicatorProto (map varTerm freevars) sta1 sta2-- nb sta1 sta2
                            void normSystem
            _  -> do
                    void substSystem
                    let matrixvars = getVariablesOf [sta1, sta2]                 
                    freevars <- replicateM (length matrixvars) $ freshLVar "vy" LSortE
                    if length matrixvars >1 
                              then (solveIndicatorProto (map varTerm freevars) sta1 sta2) `disjunction` (solveIndicatorProto2 (map varTerm freevars) sta1 sta2)
                              else solveIndicatorProto (map varTerm freevars) sta1 sta2
                    void normSystem
     else do
        let newsubsts = substFromList $ map (\x -> (x, fAppdhOne)) toset2
        eqStore <- getM sEqStore
        setM sEqStore $ applyEqStore hnd newsubsts eqStore
        subst2 <- getM sSubst
        noContradictoryEqStore
        let normedpair = (runReader (norm' $ fAppPair (apply subst2 ta1, apply subst2 ta2)) hndNormal)
            unpair t = case viewTerm t of
                        (FApp (NoEq pairSym) [x, y]) ->(x,y)
                        _ -> error $ "something went wrong" ++ show t
            (sta1,sta2) =  unpair normedpair
        case varTermsOf sta2 of
            [] -> case varTermsOf (sta1) of
                    [] -> do
                            if sta1 == sta2
                              then do
                                            void substSystem
                                            void normSystem
                              else contradictoryIf True
                    _  -> do
                            void substSystem
                            let matrixvars = getVariablesOf [sta1, sta2]                 
                            freevars <-  replicateM (length matrixvars) $ freshLVar "vy" LSortE
                            if length matrixvars >1 
                              then (solveIndicatorProto (map varTerm freevars) sta1 sta2) `disjunction` (solveIndicatorProto2 (map varTerm freevars) sta1 sta2)
                              else solveIndicatorProto (map varTerm freevars) sta1 sta2
                            void normSystem
            _  -> do
                    void substSystem
                    let matrixvars = getVariablesOf [sta1, sta2]                   
                    freevars <- replicateM (length matrixvars) $ freshLVar "vy" LSortE
                    if length matrixvars >1 
                              then (solveIndicatorProto (map varTerm freevars) sta1 sta2) `disjunction` (solveIndicatorProto2 (map varTerm freevars) sta1 sta2)
                              else solveIndicatorProto (map varTerm freevars) sta1 sta2
                    void normSystem  

solveNeeded ::  (LNTerm -> NodeId -> StateT  System (FreshT (DisjT (Reader ProofContext))) a0) -> LNTerm ->  NodeId ->        -- exponent that is needed.
                Reduction String -- ^ Case name to use.
solveNeeded fun x i = do
     insertBasisElem x
     return "case Secret Set"
    `disjunction`
    (do
          (insertNotBasisElem x)
          case viewTerm x of 
            Lit (Var lvar) -> do
                _ <- fun x i
                return "case Leaked Set"
            _ -> do
                _ <- insertAction i (kLogFact x) -- kdhfact 
                return "case Leaked Set"
           )

solveNeededList2 :: [LNTerm] -> [([LNTerm], [LNTerm])]
solveNeededList2 es = map (\b -> (b, es \\ b)) sublists
    where sublists = nub $ subsequences es

solveNeededList :: (LNTerm -> NodeId -> Reduction String) -> [LNTerm] ->  
                Reduction String -- ^ Case name to use.
solveNeededList fun [x] = do
      i <- freshLVar "vk" LSortNode
      solveNeeded fun x i
solveNeededList fun (x:xs) = do
      i  <- freshLVar "vk" LSortNode
      solveNeeded fun x i
      solveNeededList fun xs

solveTermDHEqsChain :: SplitStrategy -> (Maybe (S.Set LNTerm, S.Set LNTerm)) -> [RuleAC] -> [(NodeId,RuleACInst)] ->
                        (LNTerm -> NodeId -> Reduction String)
                        -> NodePrem -> LNFact -> (NodeId, RuleACInst, LNFact, ConcIdx)
                        -> (LNTerm, LNTerm) -> Reduction ChangeIndicator
solveTermDHEqsChain splitStrat mayB rules instrules fun p faPrem (j,ruj, fa1, c) (ta2,ta1) = do
    hndNormal <- getMaudeHandle
    bset <- getM sBasis
    nbset <- getM sNotBasis
    let (currB, currNB) = case mayB of 
                            Nothing -> (bset, nbset)
                            Just (bb,nbb) -> (bb, nbb)
    substs <- getM sSubst
    substSystem
    let nta2 = runReader (norm' ((applyVTerm substs ta2))) hndNormal
        nta1 = runReader (norm'((applyVTerm substs ta1))) hndNormal
    case neededexponents currB currNB nta2 of
        [] -> do
            let xrooterms = (multRootList nta2)
                indlist = map (\x -> rootIndKnown2 hndNormal bset nbset x) xrooterms
        --indlist = map (\x -> runReader (rootIndKnownMaude bset nbset x) hndNormal) (multRootList $ runReader (norm' ta2) hndNormal)
                neededInds = filter (not . isPublic) indlist
                n = length neededInds
                h = head xrooterms
                toaddnocanc = filter (\t -> not $ isNoCanc h t) (tail xrooterms)
            forM_ (toaddnocanc) (\t->insertNoCanc h t)
            if null neededInds
                then insertDHEdge ((j,c), fa1, faPrem, p) bset nbset -- TODO: fix this
                else do
                    possibletuple <- insertFreshNodeConcOutInst rules instrules n (Just ((j,ruj, fa1, c), nta1))
                    insertDHEdges possibletuple neededInds ta2 p fun
            return Changed
        es -> do
                let fres = filter (\fe -> sortOfLNTerm fe == LSortFrNZE) es
                    otheres = es \\ fres
                ifs<- replicateM (length fres) $ freshLVar "vk" LSortNode
                forM_ (zip ifs fres) (\(i,x) -> insertMuAction fun x i)
                (newb,newNb) <- disjunctionOfList $ solveNeededList2 otheres
                trace (show ("insertingBasisDirectEdge", newb, faPrem, nta2, "old", bset,nbset)) $ forM_ newb (insertBasisElem)
                forM_ newNb (insertNotBasisElem)
                is<- replicateM (length newNb) $ freshLVar "vk" LSortNode
                forM_ (zip is newNb) (\(i,x)-> insertGoal (ActionG i (kdhFact x)) False)
                newbset <- getM sBasis
                newnbset <- getM sNotBasis
                trace (show ("shouldnevergethereDirectEdge", newb, newNb, "old",bset,nbset,"updated",newbset,newnbset, (factTerms faPrem, es))) substSystem
                solveTermDHEqsChain splitStrat (Just (newbset, newnbset)) rules instrules fun p faPrem (j,ruj, fa1, c) (ta2,ta1)


combineNlists :: Int -> [LNTerm] -> [[LNTerm]]
combineNlists 0 _ = []
combineNlists 1 xs = [ [x] | x <- xs]
combineNlists 2 xs = [x:[y] | x<-xs , y<- xs]
combineNlists n xs = [ x:zs  | x<- xs, zs<-(combineNlists (n-1) xs)]

createPerms :: Int -> LNTerm -> [[LNTerm]]
createPerms m t = if m == 1 
                    then map (\x-> [x]) indts
                    else combineNlists m indts          
                   where indts = multRootList t 

etermOf :: LNTerm -> Maybe LVar
etermOf x =  if null elist then Nothing else Just (head elist)
              where elist = filter (\v->lvarSort v == LSortE) $ varsVTerm x



replacesubsts :: [LNTerm] -> M.Map LNTerm [(LVar,LNTerm)] -> [LNTerm]
replacesubsts [] _ = []
replacesubsts [x] map1 | M.notMember x map1 = [x]
replacesubsts [x] map1 | otherwise = [applyVTerm (substFromList $ [head (map1 M.! x)]) x]
replacesubsts (x:xs) map1 | M.notMember x map1 = x : (replacesubsts xs map1)
replacesubsts (x:xs) map1 | otherwise = (applyVTerm (substFromList [head (map1 M.! x)]) x): (replacesubsts xs map')
                             where map' = M.adjust (drop 1) x map1

markFirst :: [LVar] -> [LVar]
markFirst [] = []
markFirst (x:xs) = (x{lvarName = "ff1"}):xs

protoCase :: SplitStrategy -> S.Set LNTerm -> S.Set LNTerm -> (LNTerm, LNTerm) -> Reduction ChangeIndicator
protoCase splitStrat bset nbset (ta1, ta2) = do
        subst <- getM sEqStore
        nocancs <- getM sNoCanc
        hndNormal <- getMaudeHandle
        let ta11 = applyVTerm (_eqsSubst subst) ta1
            ta22 = applyVTerm (_eqsSubst subst) ta2
            -- todo! check here if nta1 and nta2 are already equal!
            normedpair = (runReader (norm' $ fAppPair (ta11, ta22)) hndNormal)
            unpair t = case viewTerm t of
                                (FApp (NoEq pairSym) [x, y]) ->(x,y)
                                _ -> error $ "something went wrong" ++ show t
            (nta1,nta2) =  unpair normedpair
            --nta2 = runReader (norm' ta22) hndNormal
            --nta1 = runReader (norm' ta11) hndNormal
        if nta1 == nta2
         then do
            return Changed
         else case prodTerms nta1 of
            Just (x,y) ->   do 
                            let xrooterms = multRootList nta1
                                repxindterms = filter (not . isPublic) $ map (\x -> rootIndKnown2 hndNormal bset nbset x) xrooterms
                                xindterms = nub repxindterms 
                                n = length xindterms
                                h = head xrooterms
                                toaddnocanc = filter (\t -> not $ isNoCanc h t) (tail xrooterms)
                            forM_ (toaddnocanc) (\t->insertNoCanc h t)   
                            hnd <- getMaudeHandleDH
                            permutedlist <- disjunctionOfList $ createPerms n nta2
                            let nublist = nub permutedlist
                                eterms = map etermOf nublist
                                appearances = map (\x -> length $ filter (==x) permutedlist) nublist
                                zipped = zip nublist $ zip appearances eterms
                            if any (\(a,(b,c))-> b>1 && null c) zipped
                              then contradictoryIf True
                              else do 
                                    let nubapp = filter (\(a,b)-> b>1) $ nub $ zip eterms appearances 
                                        numapp =  map snd nubapp
                                    ffs <- replicateM (foldl (+) 0 numapp) $ freshLVar "ff" LSortE 
                                    let esubsts = filter (\(a,(b,c))-> b>1) zipped
                                        evars = (map (\(a,(b,c))-> (a,c)) esubsts)
                                        splitlist = map markFirst $ splitPlaces (numapp) ffs
                                        ffsums = map (\f -> foldl (\t v -> if t == fAppdhZero then LIT (Var v) else fAppdhPlus (t, LIT (Var v))) fAppdhZero f) splitlist
                                        permsubsts :: [(LNTerm, [(LVar, LNTerm)])]
                                        permsubsts = map (\((a,(b,e)),fs) -> (a, map (\f-> (fromJust e,LIT (Var f))) fs)) $  zip (filter (\(a,(b,c))-> b>1) zipped) splitlist
                                        newsubst = substFromList $ zip (map (fromJust . snd) evars) ffsums
                                        newpermlist = replacesubsts permutedlist (M.fromList permsubsts)
                                    oldsubst <- getM sSubst
                                    eqstore <- getM sEqStore
                                    setM sEqStore ( eqstore{_eqsSubst = substFromList $ normalizeSubstList hndNormal $ substToList (compose newsubst oldsubst)} )
                                    eqstore2 <- getM sEqStore
                                    void normSystem
                                    void substSystem
                                    let nta2p = (runReader (norm' $ applyVTerm newsubst nta2) hndNormal) 
                                        allevars = filter (\x -> lvarSort x == LSortE) $ nub $ varsVTerm nta1 ++ varsVTerm nta2p
                                    solveDHProtoEqsAux splitStrat bset nbset hndNormal hnd allevars xindterms nta1 nta2p newpermlist -- $ map (rootIndKnown2 hndNormal bset $ S.fromList (filter isFrNZEVar $ S.toList nbset)) newpermlist
                            return Changed
            _ -> error "TODO"

solveTermDHEqs :: SplitStrategy -> ((LNTerm,LNTerm)->Reduction ChangeIndicator) -> (LNTerm, LNTerm) -> Reduction ChangeIndicator
solveTermDHEqs splitStrat fun (ta1, ta2)
        | ta1 == ta2 = return Unchanged
        | ta1 == fAppdhZero && ta2 == fAppdhOne = do contradictoryIf True
                                                     return Changed
        | ta1 == fAppdhOne && ta2 == fAppdhZero = do contradictoryIf True
                                                     return Changed
        | (isDHLit ta1 && compatibleLitsStrict ta1 ta2) = (do
                            solveTermEqs splitStrat [(Equal ta1 ta2)]
                            void substSystem
                            void normSystem
                            return Changed)
        | (isDHLit ta2 && compatibleLitsStrict ta2 ta1) = ( do
                            solveTermEqs splitStrat [(Equal ta1 ta2)]
                            void substSystem
                            void normSystem
                            return Changed)
        | (isDHLit ta1 && (not $ compatibleLits ta1 ta2)) = do
            contradictoryIf True 
            return Changed
        | (isDHLit ta2 && (not $ compatibleLits ta2 ta1)) = do
            contradictoryIf True 
            return Changed 
        | otherwise = case (isPubExp ta1, isPubExp ta2) of
                (Just (pg1,e1), Just (pg2,e2)) -> do
                    if pg1 == pg2
                     then do
                        solveTermDHEqs splitStrat fun (e1, e2)
                     else do
                        solveTermEqs splitStrat [(Equal pg1 pg2)]
                        solveTermDHEqs splitStrat fun (e1, e2)
                _ -> fun (ta1,ta2)



-- | Add a list of equalities in substitution form to the equation store
solveSubstEqs :: SplitStrategy -> LNSubst -> Reduction ChangeIndicator
solveSubstEqs split subst =
    solveTermEqs split [Equal (varTerm v) t | (v, t) <- substToList subst]

-- | Add a list of node equalities to the equation store.
solveNodeIdEqs :: [Equal NodeId] -> Reduction ChangeIndicator
solveNodeIdEqs = solveTermEqs SplitNow . map (fmap varTerm)

-- | Add a list of fact equalities to the equation store, if possible.
solveFactEqs :: SplitStrategy -> [Equal LNFact] -> Reduction ChangeIndicator
solveFactEqs split eqs = do
    contradictoryIf (not $ all evalEqual $ map (fmap factTag) eqs)
    (solveListEqs (solveTermEqs split) $ map (fmap factTerms) eqs)

solveFactOutKIEqs :: SplitStrategy -> LNFact -> LNTerm -> LNFact -> Reduction ChangeIndicator
solveFactOutKIEqs split fa1 ta1 fa2 = do
    trace (show ("factOutKI", fa1,fa2)) $ contradictoryIf (not (factTag fa1 == OutFact) && (factTag fa2 == KIFact ) )
    contradictoryIf (not ((length $ factTerms fa1) == (length $ factTerms fa2)))
    hndNormal <- getMaudeHandle
    case (factTerms fa2) of 
        [ta2] -> (solveTermEqs split)  $ [Equal ta1 ta2]
        _ -> error "Out and KI facts should be of arity 1"
    --(solveTermEqs split) $ (zipWith (\a b-> Equal a b) (factTerms fa1) (factTerms fa2))


solveMixedFactEqs :: SplitStrategy -> Equal LNFact -> S.Set LNTerm -> S.Set LNTerm -> ((LNTerm, LNTerm) -> Reduction ChangeIndicator) -> Reduction ChangeIndicator
solveMixedFactEqs split (Equal fa1 fa2) bset nbset fun = do
    contradictoryIf (not (factTag fa1 == factTag fa2))
    contradictoryIf (not ((length $ factTerms fa1) == (length $ factTerms fa2)))
    let normalfacts = filter (\a -> not $ isMixedTerm a) (factTerms fa1)
        normalfacts2 = filter (\a -> not $ isMixedTerm a) (factTerms fa2)
    solveTermEqs split $ zipWith (\a b -> (Equal a b)) normalfacts normalfacts2
    subst <- getM sEqStore
    let dhfacts1 = map (applyVTerm (_eqsSubst subst)) (factTerms fa1) -- filter isMixedTerm (factTerms fa1) 
        dhfacts2 = map (applyVTerm (_eqsSubst subst)) (factTerms fa2) -- filter isMixedTerm (factTerms fa2)
    solveListDHEqs (solveMixedTermEqs split bset nbset fun) $ zip dhfacts1 dhfacts2
    return Changed

-- t1 here is the result of factTerms fa2, and indt1 the indicator of one product term of t1. 
solveFactDHEqs ::  SplitStrategy -> LNFact -> LNFact -> S.Set LNTerm -> S.Set LNTerm  -> ((LNTerm,LNTerm)->Reduction ChangeIndicator) ->  Reduction ChangeIndicator
solveFactDHEqs split fa1 fa2 bset nbset fun= do
            contradictoryIf (not (factTag fa1 == factTag fa2))
            contradictoryIf (not ((length $ factTerms fa1) == (length $ factTerms fa2)))
            solveListDHEqs (solveTermDHEqs split fun) $ zip (factTerms fa1) (factTerms fa2)

createEqs t1 t2 =
    case (isPubExp t1, isPubExp t2) of
        (Just (pg1,e1), Just (pg2,e2)) -> (Equal e1 e2) 
        _ ->  (Equal t1 t2)


genTerm :: MaudeHandle -> Term (Lit Name LVar) -> LVar -> (Term (Lit Name LVar), LNTerm, LVar)
genTerm hnd i z  = case sortOfLNTerm i of
    LSortE ->  (i, runReader (norm' $ fAppdhTimesE (i, LIT (Var z)) ) hnd, z) 
    LSortNZE ->  (i, runReader (norm' $ fAppdhTimesE (i, LIT (Var z)) ) hnd, z) 
    LSortFrNZE ->  (i, runReader (norm' $ fAppdhTimesE (i, LIT (Var z)) ) hnd, z) 
    _ ->  (i, runReader (norm' $ fAppdhExp (i, LIT (Var z)) ) hnd, z) 

solveIndFactDH :: SplitStrategy -> [((LNTerm, LNTerm), LNTerm)] -> LNTerm -> Reduction (LNTerm, [LNTerm])
solveIndFactDH split listtups faPrem = do
    --  let genindterms = zip xindterms zzs
    --eqstore <- getM sEqStore
    --(eqs2, maySplitId) <- addDHProtoEqs hnd allevars genindterms permutedlist False eqstore
    hndNormal <- trace (show ("Iamhere", faPrem)) getMaudeHandle
    let queries = map (\((t,rt), ind)-> createEqs rt ind) listtups
        xindterms = map (\(Equal rt ind) -> ind) queries
        prterms = map (\(Equal rt ind) -> rt) queries
    zzs <- replicateM (length xindterms) $ freshLVar "zz" LSortE
    let genindterms = zipWith (genTerm hndNormal) xindterms zzs
    se  <- gets id
    hnd <- trace (show ("gen", genindterms, "p", prterms)) getMaudeHandleDH
    (eqs2, maySplitId,subst1) <- addDHEqs2 hnd False genindterms prterms =<< getM sEqStore 
    setM sEqStore =<< simp hnd (substCreatesNonNormalTerms hnd se) eqs2
    noContradictoryEqStore
    void substSystem
    void normSystem
    subst <- getM sEqStore
    return (applyVTerm (_eqsSubst subst) faPrem, map (\((a,b),c)-> applyVTerm (_eqsSubst subst) a ) listtups)



-- | Add a list of rule equalities to the equation store, if possible.
solveRuleEqs :: SplitStrategy -> [Equal RuleACInst] -> Reduction ChangeIndicator
solveRuleEqs split eqs = do
    contradictoryIf (not $ all evalEqual $ map (fmap (get rInfo)) eqs)
    solveListEqs (solveFactEqs split) $
        map (fmap (get rConcs)) eqs ++ map (fmap (get rPrems)) eqs
        ++ map (fmap (get rActs)) eqs

-- | Solve a number of equalities between lists interpreted as free terms
-- using the given solver for solving the entailed per-element equalities.
solveListEqs :: ([Equal a] -> Reduction b) -> [(Equal [a])] -> Reduction b
solveListEqs solver eqs = do
    contradictoryIf (not $ all evalEqual $ map (fmap length) eqs)
    solver $ concatMap flatten eqs
  where
    flatten (Equal l r) = zipWith Equal l r
    -- on RHS "Equal" is a function that from two lists of terms, returns the list of pair of Equal of terms.

solveListDHEqs :: ( (a,a) -> Reduction ChangeIndicator) -> [(a,a)] -> Reduction ChangeIndicator
solveListDHEqs solver eqs = do
    case eqs of
        [] -> return Unchanged
        [a] -> solver a
        (a : as) -> do
            solver a
            solveListDHEqs solver as

-- | Solve the constraints associated with a rule.
solveRuleConstraints :: Maybe RuleACConstrs -> Reduction ()
solveRuleConstraints (Just eqConstr) = do
    hnd <- getMaudeHandle
    (eqs, splitId) <- addRuleVariants eqConstr <$> getM sEqStore
    insertGoal (SplitG splitId) False
    -- do not use expensive substCreatesNonNormalTerms here
    setM sEqStore =<< simp hnd (const (const False)) eqs
    noContradictoryEqStore
solveRuleConstraints Nothing = return ()

