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
  , getVerbose

  , enumConcsDhOut
  , enumConcsDhExpOut
  -- ** Inserting nodes, edges, and atoms
  , labelNodeId
  , exploitNodeId
  , insertFreshNode
  , insertFreshNodeMixed
  , insertFreshNodeConc
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

  , insertNoCanc
  , insertNotBasisElem
  , insertBasisElem
  , insertDHEdge
  , insertDHEdges
  , insertDHMixedEdge
  , solveNeeded
  , solveNeededList
  , setNotReachable

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

import           Debug.Trace.Ignore
import           Prelude                                 hiding (id, (.))

import qualified Data.Foldable                           as F
import qualified Data.Map                                as M
import qualified Data.Map.Strict                         as M'
import qualified Data.Set                                as S
import qualified Data.ByteString.Char8                   as BC
import           Data.List                               (mapAccumL, delete , subsequences, length , nubBy, permutations, intersect)
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

insertFreshNodeConcMixed ::  [RuleAC] -> [(NodeId,RuleACInst)] -> Reduction (RuleACInst, NodeConc, LNFact)
insertFreshNodeConcMixed rules instrules = do
      (i,ru) <- disjunctionOfList instrules
      (v, fa) <- disjunctionOfList $ [(c,f)|  (c,f) <- enumConcs ru,  isMixedFact f ]
      return (ru, (i, v), fa)
    `disjunction`        
    (do
        (i, ru) <- insertFreshNode rules Nothing
        -- subst <- getM sEqStore
        -- applyVTerm (_eqsSubst subst) ta1
        contradictoryIf (elem i [i | (i,ru) <- instrules])
        (v, fa) <- disjunctionOfList $ [(c,f)| (c,f) <- enumConcs ru, isMixedFact f ]
        return (ru, (i, v), fa))

combinations :: Int -> [a] -> [[a]]
combinations k ns = filter ((k==).length) $ subsequences ns


traverseDHNodes :: [RuleAC] -> Reduction [(NodeId, RuleACInst, Maybe RuleACConstrs)]
traverseDHNodes rules = do
    let m = length rules
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
      let pairs = [(ru, (i,c), (f, head $ factTerms f), rterm, mconstrs,b) | (i, ru, mconstrs, b) <- ((map (\(a,b)->(a,b,Nothing, False)) instrules)++ (map (\(a,b,c)->(a,b,c, True)) irulist)), (c,f) <- enumConcs ru, (factTag f == OutFact), isDHFact f, rterm <- multRootList (head $ factTerms f)]
      disjunctionOfList (concatMap permutations (combinations n pairs)) 
insertFreshNodeConcOutInst rules instrules n (Just ((j,ruj,faConc,cj), ta)) = do
      -- irulist <- replicateM n $ traverseDHNodes rules
      irulist <- traverseDHNodes rules
      let pairs = [(ru, (i,c), (f, head $ factTerms f), rterm, mconstrs,b) | (i, ru, mconstrs, b) <- ((map (\(a,b)->(a,b,Nothing, False)) instrules)++ (map (\(a,b,c)->(a,b,c, True)) irulist)), (c,f) <- enumConcs ru, (factTag f == OutFact), isDHFact f, rterm <- multRootList (head $ factTerms f)]
          pairs2 =  [(ruj, (j,cj), (faConc, ta), rterm , Nothing,False) | rterm <- multRootList ta ]
          finallist = (concatMap permutations (filter ( any (\(a,(i,b),c,d,e,f) -> i==j && a ==ruj)) (combinations n $ pairs++pairs2)) )
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

insertFreshNodeMixed :: [RuleAC] -> [(NodeId,RuleACInst)] -> Maybe RuleACInst -> Reduction (NodeId, RuleACInst)
insertFreshNodeMixed rules instrules parent = do
     (i,ru) <- disjunctionOfList instrules
     return (i,ru)
    `disjunction`
    (do
        i <- freshLVar "vr" LSortNode
        (,) i <$> labelNodeId i rules parent) 




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
            exploitPrems j ruKnows
        {-Fact InFact ann [m] |  (isMixedFact fa) -> do
            j <- freshLVar "vf" LSortNode
            (cleanedm, mDHvars) <- clean m
            ruKnows <- mkISendRuleAC ann cleanedm
            modM sNodes (M.insert j ruKnows)
            modM sEdges (S.insert $ Edge (j, ConcIdx 0) (i, v))
            exploitPrems j ruKnows -}

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

          -- CR-rule *DG2_{2,u}*: solve a KU-premise by inserting the
          -- corresponding KU-actions before this node.
        --_ | (isKUFact fa && (not (isDHFact fa))) -> do
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

insertOutKIEdge :: (NodeConc, LNFact, LNFact, NodePrem) -> Reduction ()
insertOutKIEdge (c, fa1,fa2,p) = do
    void (solveFactOutKIEqs SplitNow (Equal fa1 fa2))
    modM sEdges (\es -> foldr S.insert es [ Edge c p ])


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


--insertNoCanc :: LNTerm -> LNTerm -> Reduction ()
--insertNoCanc x y = modM sNoCanc (S. insert (x,y))



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
    EqE x y       -> void $ solveTermEqs SplitNow [Equal x y]
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
    modM sEdges (\es -> foldr S.insert es [ Edge c p ])


insertDHEdge ::   (NodeConc, LNFact, LNFact, NodePrem) -> S.Set LNTerm -> S.Set LNTerm -> Reduction ()
insertDHEdge (c, fa1, fa2, p) bset nbset = do --fa1 should be an Out fact
    void (solveFactDHEqs SplitNow fa1 fa2 bset nbset (protoCase SplitNow bset nbset))
    modM sEdges (\es -> foldr S.insert es [ Edge c p ])

insertDHEdges :: [(RuleACInst, NodeConc, (LNFact,LNTerm), LNTerm, Maybe RuleACConstrs, Bool)] -> [LNTerm] -> LNTerm -> NodePrem -> Reduction ()
insertDHEdges tuplelist indts premTerm p = do
    let rootpairs = zip (map (\(a,b,(c,t),d,e,f)-> (t,d)) tuplelist) indts
        cllist = nubBy (\(a,b,c,d,e,f) (a2,b2,c2,d2,e2,f2) -> b == b2) tuplelist
    return ()
    (faPremsubst, listterms) <- foldM (\faP c -> solveIndFactDH SplitNow c faP) (premTerm,[]) rootpairs
    void $ solveIndicator faPremsubst listterms
    forM_ (map (\(_,b,_,_, _, _)->b) cllist) (\c-> (modM sEdges (\es -> foldr S.insert es [ Edge c p ])))
    forM_ (map (\(ru,(i,b),_,_, mc,f)->(i,ru, mc)) (filter (\(ru,_,_,_, mc,b)->b) cllist)) (\(c1,c2,c3) -> exploitNodeId c1 c2 c3)

insertDHMixedEdge :: Bool -> (NodeConc, LNFact, LNFact, NodePrem) -> RuleACInst -> RuleACInst 
                    -> S.Set LNTerm -> S.Set LNTerm -> [RuleAC] -> [(NodeId, RuleACInst)] ->
                    (LNTerm -> NodeId -> StateT System (FreshT (DisjT (Reader ProofContext))) a0) -> Reduction ()
-- fa1 is conclusion, fa2 is premise
insertDHMixedEdge True (c, fa1, fa2, p) cRule pRule bset nbset rules rulesinst fun = do --fa1 should be an Out fact
    (solveMixedFactEqs SplitNow (Equal fa1 fa2) bset nbset (protoCase SplitNow bset nbset) )
    modM sEdges (\es -> foldr S.insert es [ Edge c p ])
insertDHMixedEdge False ((ic,c), fa1, fa2, p) cRule pRule bset nbset rules rulesinst fun= do --fa1 should be an Out fact
    let chainFun = solveTermDHEqsChain SplitNow rules rulesinst fun p fa2 (ic, cRule, fa1, c)
    (solveMixedFactEqs SplitNow (Equal fa1 fa2) bset nbset chainFun) 
    modM sEdges (\es -> foldr S.insert es [ Edge (ic,c) p ])


insertBasisElem :: LNTerm -> Reduction ()
insertBasisElem x = do
    modM sBasis (\es -> S.insert x es)

insertNotBasisElem :: LNTerm -> Reduction ()
insertNotBasisElem x = do
    modM sNotBasis (\es -> S.insert x es)

setNotReachable :: Reduction ()
setNotReachable  = do
    setM sNotReach True

insertNoCanc :: LNTerm -> LNTerm -> Reduction ChangeIndicator
insertNoCanc x y = do
        insertGoal (NoCancG (x, y)) False
        return Changed


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
    --substLastAtom
    --substLessAtoms
    --substSubtermStore
    --substFormulas -- todo: ADD THIS!!
    --substSolvedFormulas -- todo: ADD THIS!!
    --substLemmas -- todo: ADD THIS!!
    c2 <- normGoals hnd
    --substNextGoalNr
    return c2


{-normFormula :: MaudeHandle -> LNGuarded -> LNGuarded
normFormula hnd f = traverseFormulaAtom  (\t-> runReader (norm' t) hnd) f
  -}

normalizeFact :: MaudeHandle -> LNFact -> LNFact
normalizeFact hnd fa@(Fact f1 f2 faterms) = Fact f1 f2 (map (\t-> runReader (norm' t) hnd) faterms)

normalizeGoal :: MaudeHandle -> Goal -> Goal
normalizeGoal hnd goal = case goal of
        ActionG v fact -> ActionG v $ normalizeFact hnd fact
        PremiseG prem fact -> PremiseG prem $ normalizeFact hnd fact
        NoCancG (t1, t2) -> NoCancG (runReader (norm' t1) hnd, runReader (norm' t2) hnd)
        _ -> goal

normGoals :: MaudeHandle -> Reduction ChangeIndicator
normGoals hnd = do
    goals <- M.toList <$> getM sGoals
    sGoals =: M.empty
    changes <- forM goals $ \(goal, status) ->  do modM sGoals $
                                                     M'.insertWith combineGoalStatus (normalizeGoal hnd goal) status
                                                   return Unchanged
    return (mconcat changes)

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
    | isDHTerm lhs && isDHTerm rhs = (solveTermDHEqs splitStrat bset nbset fun) (lhs,rhs)
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
        solveListDHEqs (solveTermDHEqs splitStrat bset nbset fun) substdhvars
        noContradictoryEqStore
        return Changed
    | otherwise =  solveTermEqs splitStrat [(Equal lhs rhs)]




normalizeSubstList :: MaudeHandle -> [(LVar, LNTerm)] -> [(LVar, LNTerm)]
normalizeSubstList hnd [] = []
normalizeSubstList hnd [(t,t2)] = [(t, runReader ( norm' t2) hnd)]
normalizeSubstList hnd ((t,t2) : xs) = (t, runReader ( norm' t2) hnd):(normalizeSubstList hnd xs)

solveIndicator ::  LNTerm -> [LNTerm] -> Reduction String
solveIndicator t2 terms  = do 
  nbset <- getM sNotBasis
  hndNormal  <- getMaudeHandle
  --irules <- getM sNodes
  --let rules = M.elems irules
  --    terms = (concatMap enumConcsDhOut rules)
  --    exps = (concatMap enumConcsDhExpOut rules)-
  let isEq (a,b) = (runReader (norm' $ fAppPair (a, b)) hndNormal)
      termpairs = map (\x -> isEq (t2,x)) terms
      unpair t = case viewTerm t of
                    (FApp (NoEq pairSym) [x, y]) -> (x,y)
                    _ -> error $ "something went wrong" ++ show t
  if (any (\(a,b)-> a==b) $ map unpair termpairs) 
    then return "Found indicators"
    else do 
        case solveIndicatorGauss (S.toList nbset) terms t2 of 
          Just vec -> do
              return ("Found indicators! attack by result:" ++ show (vec, terms, t2))
          Nothing -> do 
              contradictoryIf True 
              return ("Safe,cannot combine from (leaked set, terms):"++ show ((S.toList nbset), terms, t2))


solveIndicatorProto :: [LNTerm] -> LNTerm -> LNTerm -> Reduction String
solveIndicatorProto nb t1 t2 = do
  case solveIndicatorGaussProto nb t1 t2 of
   Just subst ->  do
        eqStore <-  getM sEqStore
        hnd  <- getMaudeHandle
        setM sEqStore $ applyEqStore hnd (substFromList $ normalizeSubstList hnd subst) eqStore
        --substCheck <- gets (substCreatesNonNormalTerms hnd)
        --store <- getM sEqStore
        neweqstore <- getM sEqStore
        let oldsubsts =  _eqsSubst neweqstore
            newsubst = substFromList $ normalizeSubstList hnd (substToList oldsubsts)
        setM sEqStore ( neweqstore{_eqsSubst = newsubst} )
        void substSystem
        void normSystem
        nodes <- getM sNodes
        setM sNodes $ M.map (\r -> runReader (normRule r) hnd) nodes
        return ("Matched" ++ show (normalizeSubstList hnd subst))
   Nothing -> do
          --setNotReachable
          contradictoryIf True
          return "Contradiction! Cannot find exponent"
  where
    terms = [t1]

solveDHProtoEqsAux :: SplitStrategy -> S.Set LNTerm  -> S.Set LNTerm -> MaudeHandle -> MaudeHandle -> [LNTerm] -> LNTerm -> LNTerm -> [LNTerm] -> StateT System (FreshT (DisjT (Reader ProofContext))) ()
solveDHProtoEqsAux splitStrat bset nbset hndNormal hnd xindterms ta1 ta2 permutedlist= do
    -- permutedlist <- disjunctionOfList $ permutations outterms
    zzs <- replicateM (length xindterms) $ freshLVar "zz" LSortE
    let genindterms = zipWith (\i z-> (i, runReader (norm' $ fAppdhExp (i, LIT (Var z)) ) hndNormal, z) ) xindterms zzs
    --  let genindterms = zip xindterms zzs
    (eqs2, maySplitId) <- addDHProtoEqs hnd genindterms permutedlist False =<< getM sEqStore
    se  <- gets id
    setM sEqStore =<< simp hnd (substCreatesNonNormalTerms hnd se) eqs2
    noContradictoryEqStore
    subst <- getM sSubst
    let sta2 =  (runReader (norm' $ apply subst ta2) hndNormal)
        sta1 = (runReader (norm' $ apply subst ta1) hndNormal)
    case varTermsOf sta2 of
        [] -> case varTermsOf (sta1) of
                [] -> do
                        let normedpair = (runReader (norm' $ fAppPair (sta1, sta2)) hndNormal)
                            unpair t = case viewTerm t of
                                            (FApp (NoEq pairSym) [x, y]) -> (x,y)
                                            _ -> error $ "something went wrong" ++ show t
                        if (\(a,b)-> a==b) $ unpair normedpair 
                          then do 
                                            void substSystem
                                            void normSystem
                          else contradictoryIf True
                _  -> do
                        -- TODO: fix basis set to take into account the substituions .
                        -- (maybe you can directly consider all exponents in the matrix combination function directly?)
                        void $ solveIndicatorProto (S.toList nbset) sta1 sta2 -- (concatMap eTermsOf $ map (\x -> runReader (norm' $ apply subst x) hndNormal) (S.toList nbset))
                        void substSystem
                        void normSystem
        _  -> do
                void $ solveIndicatorProto (S.toList nbset) sta2 sta1
                void substSystem
                void normSystem


solveNeeded ::  (LNTerm -> NodeId -> StateT  System (FreshT (DisjT (Reader ProofContext))) a0) -> LNTerm ->  NodeId ->        -- exponent that is needed.
                Reduction String -- ^ Case name to use.
solveNeeded fun x i = do
     insertBasisElem x
                --insertGoal (PremiseG (i, PremIdx 0) (kdFact x)) False !!(adversary shouldn't know x? check if we actually _need_ to prove it CANNOT)
                -- TODO: insertSecret x
     return "case Secret Set"
    `disjunction`
    (do 
          (insertNotBasisElem x)
          _ <- fun x i
          return "case Leaked Set" )

solveNeededList :: (LNTerm -> NodeId -> StateT  System (FreshT (DisjT (Reader ProofContext))) a0) -> [LNTerm] ->        -- exponent that is needed.
                Reduction String -- ^ Case name to use.
solveNeededList fun [x] = do
      i <- freshLVar "vk" LSortNode
      solveNeeded fun x i
solveNeededList fun (x:xs) = do
      i  <- freshLVar "vk" LSortNode
      solveNeeded fun x i
      solveNeededList fun xs

solveTermDHEqsChain :: SplitStrategy -> [RuleAC] -> [(NodeId,RuleACInst)] -> 
                        (LNTerm -> NodeId -> StateT  System (FreshT (DisjT (Reader ProofContext))) a0) 
                        -> NodePrem -> LNFact -> (NodeId, RuleACInst, LNFact, ConcIdx)
                        -> (LNTerm, LNTerm) -> Reduction ChangeIndicator
solveTermDHEqsChain splitStrat rules instrules fun p faPrem (j,ruj, fa1, c) (ta1,ta2) = do
    bset <- getM sBasis
    nbset <- getM sNotBasis
    -- case neededexponents bset nbset ta2 of 
    --  [] -> do  
    hndNormal <- getMaudeHandle
    let indlist = map (\x -> runReader (rootIndKnownMaude bset nbset x) hndNormal) (multRootList $ runReader (norm' ta2) hndNormal)
        neededInds = filter (not . isPublic) indlist
        n = length neededInds
    if null neededInds 
     then insertDHEdge ((j,c), fa1, faPrem, p) bset nbset -- TODO: fix this
     else do
            possibletuple <- insertFreshNodeConcOutInst rules instrules n (Just ((j,ruj, fa1, c), ta1))
            insertDHEdges possibletuple neededInds ta2 p
    return Changed
    --  es -> do
    --      solveNeededList fun es
    --      solveTermDHEqsChain splitStrat rules instrules fun p faPrem (j,ruj, fa1, c) (ta1,ta2)
    --      return Changed 
         

protoCase :: SplitStrategy -> S.Set LNTerm -> S.Set LNTerm -> (LNTerm, LNTerm) -> Reduction ChangeIndicator
protoCase splitStrat bset nbset (ta1, ta2) = do
        subst <- getM sEqStore
        nocancs <- getM sNoCanc
        hndNormal <- getMaudeHandle
        let ta11 = applyVTerm (_eqsSubst subst) ta1
            ta22 = applyVTerm (_eqsSubst subst) ta2
            nta2 = runReader (norm' ta22) hndNormal
            nta1 = runReader (norm' ta11) hndNormal
        case prodTerms ta11 of
            Just (x,y) -> if not (S.member (x,y) nocancs  || isNoCanc x y) then error "TODO"
                          else do
                            let xrooterms = multRootList nta1
                                xindterms = map (\x -> runReader (rootIndKnownMaude bset nbset x) hndNormal) xrooterms
                            hnd <- getMaudeHandleDH
                            permutedlist <- disjunctionOfList $ permutations (multRootList nta2)
                            solveDHProtoEqsAux splitStrat bset nbset hndNormal hnd xindterms nta1 nta2 permutedlist
                            return Changed
            _ -> error "TODO"

solveTermDHEqs :: SplitStrategy -> S.Set LNTerm -> S.Set LNTerm -> ((LNTerm,LNTerm)->Reduction ChangeIndicator) -> (LNTerm, LNTerm) -> Reduction ChangeIndicator
solveTermDHEqs splitStrat bset nbset fun (ta1, ta2)
        | ta1 == ta2 = return Unchanged
        | (isDHLit ta1 && compatibleLits ta1 ta2) = (do
                            solveTermEqs splitStrat [(Equal ta1 ta2)]
                            void substSystem
                            void normSystem
                            return Changed)
        | (isDHLit ta2 && compatibleLits ta2 ta1) = ( do
                            solveTermEqs splitStrat [(Equal ta1 ta2)]
                            void substSystem
                            void normSystem
                            return Changed)
        | otherwise = case (isPubExp ta1, isPubExp ta2) of
                (Just (pg1,e1), Just (pg2,e2)) -> do
                    if pg1 == pg2 
                     then do
                        solveTermDHEqs splitStrat bset nbset fun (e1, e2)
                     else do
                        solveTermEqs splitStrat [(Equal pg1 pg2)]
                        solveTermDHEqs splitStrat bset nbset fun (e1, e2)
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

solveFactOutKIEqs :: SplitStrategy -> Equal LNFact -> Reduction ChangeIndicator
solveFactOutKIEqs split (Equal fa1 fa2) = do
    contradictoryIf (not (factTag fa1 == OutFact) && (factTag fa2 == KIFact ) )
    contradictoryIf (not ((length $ factTerms fa1) == (length $ factTerms fa2)))
    (solveTermEqs split) $ (zipWith (\a b-> Equal a b) (factTerms fa1) (factTerms fa2))


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
            solveListDHEqs (solveTermDHEqs split bset nbset fun) $ zip (factTerms fa1) (factTerms fa2)


solveIndFactDH :: SplitStrategy -> ((LNTerm, LNTerm), LNTerm) -> (LNTerm, [LNTerm]) -> Reduction (LNTerm, [LNTerm])
solveIndFactDH split ((fa1, t1), t2) (fa2, acclist)= 
    case (isPubExp t1, isPubExp t2) of
        (Just (pg1,e1), Just (pg2,e2)) -> do
                solveTermEqs split [(Equal pg1 pg2)]
                solveIndFactDH split ((fa1, e1), e2) (fa2, acclist)
        _ ->  do
                se  <- gets id
                hnd <- getMaudeHandleDH
                (eqs2, maySplitId) <- addDHEqs2 hnd t1 t2 =<< getM sEqStore
                setM sEqStore =<< simp hnd (substCreatesNonNormalTerms hnd se) eqs2
                noContradictoryEqStore
                void substSystem
                void normSystem
                subst <- getM sEqStore
                return $ (applyVTerm (_eqsSubst subst) fa2, map (\y -> applyVTerm (_eqsSubst subst) y) $ acclist++[fa1])


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

