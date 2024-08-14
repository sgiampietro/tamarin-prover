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
  , insertFreshNode
  , insertFreshNodeConc
  , insertFreshNodeConcOut

  , insertGoal
  , insertAtom
  , insertEdges
  , insertChain
  , insertAction
  , insertLess
  , insertFormula
  , reducibleFormula

  , insertNoCanc
  , insertContInd
  , insertContIndProto
  , insertNotBasisElem
  , insertBasisElem
  , insertDHEdge
  , insertNeeded
  , insertNeededList
  , insertDHInd
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

  -- ** Solving equalities
  , SplitStrategy(..)

  , solveNodeIdEqs
  , solveTermEqs
  , solveFactEqs
  , solveRuleEqs
  , solveSubstEqs
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
import           Data.List                               (mapAccumL)
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
import           Theory.Constraint.System
import           Theory.Model
import           Utils.Misc
import           Term.DHMultiplication
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
runReduction m ctxt se fs =
    Disj $ (`runReader` ctxt) $ runDisjT $ (`runFreshT` fs) $ runStateT m se

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

insertFreshNodeConcOut :: [RuleAC] -> Reduction (RuleACInst, NodeConc, LNFact)
insertFreshNodeConcOut rules = do
    (i, ru) <- insertFreshNode rules Nothing
    (v, fa) <- disjunctionOfList $ [(c,f)| (c,f) <- enumConcs ru, (factTag f == OutFact || factTag f == KdhFact) ]
    return (ru, (i, v), fa)

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
    solveRuleConstraints mrconstrs
    modM sNodes (M.insert i ru)
    exploitPrems i ru
    return ru
  where
    -- | Import a rule with all its variables renamed to fresh variables.
    importRule ru = someRuleACInst ru `evalBindT` noBindings

    mkISendRuleAC ann m = return $ Rule (IntrInfo (ISendRule))
                                    [kuFactAnn ann m] [inFact m] [kLogFact m] []


    mkFreshRuleAC m = Rule (ProtoInfo (ProtoRuleACInstInfo FreshRule [] []))
                           [] [freshFact m] [] [m]

    mkFreshDHRuleAC m = Rule (ProtoInfo (ProtoRuleACInstInfo FreshRule [] []))
                           [] [freshDHFact m] [] [m]

    exploitPrems i ru = mapM_ (exploitPrem i ru) (enumPrems ru)

    exploitPrem i ru (v, fa) = case fa of
        -- CR-rule *DG2_2* specialized for *In* facts.
        Fact InFact ann [m] -> do
            j <- freshLVar "vf" LSortNode
            ruKnows <- mkISendRuleAC ann m
            modM sNodes (M.insert j ruKnows)
            modM sEdges (S.insert $ Edge (j, ConcIdx 0) (i, v))
            exploitPrems j ruKnows

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
        _ | isKUFact fa -> do
              j <- freshLVar "vk" LSortNode
              insertLess j i Adversary
              void (insertAction j fa)

          -- Store premise goal for later processing using CR-rule *DG2_2*
          | otherwise -> trace (show ("inserting premise", fa)) (insertGoal (PremiseG (i,v) fa) (v `elem` breakers))
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
      DHIndG _ _    -> modM sGoals $ M.delete goal
      NoCancG _       -> modM sGoals $ M.delete goal
      NeededG _ _       -> modM sGoals $ M.delete goal
      IndicatorG _       -> modM sGoals $ M.delete goal
      IndicatorGExp _       -> modM sGoals $ M.delete goal
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


insertDHEdge ::  Bool -> (NodeConc, LNFact, LNFact, NodePrem) -> S.Set LNTerm -> S.Set LNTerm -> Reduction ()
insertDHEdge b (c, fa1, fa2, p) bset nbset = do --fa1 should be an Out fact
    void (solveFactDHEqs b SplitNow fa1 fa2 bset nbset) 
    modM sEdges (\es -> foldr S.insert es [ Edge c p ])

insertBasisElem :: LNTerm -> Reduction ()
insertBasisElem x = do
    modM sBasis (\es -> S.insert x es)

insertNotBasisElem :: LNTerm -> Reduction ()
insertNotBasisElem x = do
    modM sNotBasis (\es -> S.insert x es)

setNotReachable :: Reduction ()
setNotReachable  = do
    setM sNotReach True

insertContInd :: LNTerm -> LNTerm -> Reduction ()
insertContInd x y = modM sContInd (S.insert (x,y))

insertContIndProto :: LNTerm -> LNTerm -> Reduction ()
insertContIndProto x y = modM sContIndProto (S.insert (x,y))

-- TODO: the following not needed ?
insertDHInd :: NodePrem -> LNFact ->  Reduction ()
insertDHInd nodep fa = insertGoal (DHIndG nodep fa) False

insertNoCanc :: LNTerm -> LNTerm -> Reduction ChangeIndicator
insertNoCanc x y = do
        insertGoal (NoCancG (x, y)) False
        return Changed

insertNeeded :: LNTerm  -> Reduction ()
insertNeeded x = do
    j <- freshLVar "vk" LSortNode
    insertGoal (NeededG x j) False


insertNeededList' :: [LNTerm] -> Reduction ()
insertNeededList' [x] = do
        insertNeeded x
insertNeededList' (x:xs) = do
        insertNeeded x
        insertNeededList' xs


insertNeededList :: [LNTerm] -> NodePrem -> LNFact -> Reduction ChangeIndicator
insertNeededList xs p faPrem = do
    insertNeededList' xs
    insertDHInd p faPrem
    return Changed

{-
-- | Insert a fresh rule node labelled with a fresh instance of one of the
-- rules and return one of the conclusions.
insertOutConc :: [RuleAC] -> Reduction (RuleACInst, NodeConc, LNFact)
insertOutConc rules = do
    (i, ru) <- insertFreshNode rules Nothing
    (v, fa) <- disjunctionOfList $ enumConcs ru
    return (ru, (i, v), fa)
-}




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
    substContInd
    substContIndProto
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
substContInd        = substPart sContInd
substContIndProto        = substPart sContIndProto
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
            =<< simp hnd (substCreatesNonNormalTerms hnd se) -- (\x y -> False) this solves the NORMAL FORM ISSUE!! check that. 
            =<< case (maySplitId, splitStrat) of
                  (Just splitId, SplitNow) -> disjunctionOfList
                                                $ fromJustNote "solveTermEqs"
                                                $ performSplit eqs2 splitId
                  (Just splitId, SplitLater) -> do
                      insertGoal (SplitG splitId) False
                      return eqs2
                  _                        -> return eqs2
        trace ("DEBUG-EQ-TERMS" ++ show eqs2) noContradictoryEqStore
        return Changed


solveTermDHEqs ::  Bool -> SplitStrategy -> S.Set LNTerm -> S.Set LNTerm -> (LNTerm, LNTerm) -> Reduction ChangeIndicator
solveTermDHEqs True splitStrat bset nbset (ta1, ta2)=
        if ta1 == ta2 then (do return Unchanged) else (
        case (isDHLit ta1, isDHLit ta2) of 
            (True, _)  -> solveTermEqs splitStrat [(Equal (unbox ta1) (unbox ta2))]
            ( _, True) -> solveTermEqs splitStrat [(Equal (unbox ta1) (unbox ta2))]
            _          -> do
                        nocancs <- getM sNoCanc
                        case prodTerms ta1 of 
                            Just (x,y) -> if not (S.member (x,y) nocancs  || isNoCanc x y) then error "TODO"
                                          else do 
                                            hndNormal <- getMaudeHandle
                                            let indt = (runReader (rootIndKnownMaude bset nbset x) hndNormal)
        --    indtexp = fAppdhExp (indt, LIT (Var z1) )             -- z1 <- freshLVar "Z1" LSortE
                                            hnd <- getMaudeHandleDH -- unless the simplified unification algorithm is already implemented in Maude, this shouldn't be necessary? the simplified unification algorithm is as if we had the DHMult theory loaded.
                                            se  <- gets id
                                            (eqs2, maySplitId) <- addDHProtoEqs hnd ta2 indt =<< getM sEqStore
                                            insertContIndProto ta2 ta1
                                            insertGoal (IndicatorGExp (ta1,ta2)) False
                                            setM sEqStore
                                                =<< simp hnd (substCreatesNonNormalTerms hnd se)
                                                =<< case (maySplitId, splitStrat) of
                                                    (Just splitId, SplitNow) -> disjunctionOfList  $ fromJustNote "solveTermEqs" $ performSplit eqs2 splitId
                                                    (Just splitId, SplitLater) -> do
                                                            insertGoal (SplitG splitId) False
                                                            return eqs2
                                                    _        -> return eqs2
                                            noContradictoryEqStore
                                            return Changed
                            _ -> error "TODO")
solveTermDHEqs False splitStrat bset nbset (ta1, ta2) =
        if ta1 == ta2 then (do return Unchanged) else (
        case (isDHLit ta1, isDHLit ta2) of 
            (True, _)  -> solveTermEqs splitStrat [(Equal (unbox ta1) (unbox ta2))]
            ( _, True) -> solveTermEqs splitStrat [(Equal (unbox ta1) (unbox ta2))]
            _          -> do
                nocancs <- getM sNoCanc
                case prodTerms ta1 of 
                    Just (x,y) -> if not (S.member (x,y) nocancs  || isNoCanc x y) then error "TODO"
                     else do 
                        hndNormal <- getMaudeHandle
            -- z1 <- freshLVar "Z1" LSortE
                        let indt = (runReader (rootIndKnownMaude bset nbset ta1) hndNormal)
        --    indtexp = fAppdhExp (indt, LIT (Var z1) )
--            z1 <- freshLVar "Z1" LSortE
--            let indt = (runReader (rootIndKnownMaude bset nbset x) hnd)
--                indtexp = fAppdhExp (indt, LIT (Var z1) )
                        hnd <- getMaudeHandleDH -- unless the simplified unification algorithm is already implemented in Maude, this shouldn't be necessary? the simplified unification algorithm is as if we had the DHMult theory loaded.
                        se  <- gets id
                        (eqs2, maySplitId) <- addDHEqs hnd ta2 indt =<< getM sEqStore
                        insertContInd ta1 ta2
                        insertGoal (IndicatorG (ta1,ta2)) False
                        setM sEqStore
                            =<< simp hnd (substCreatesNonNormalTerms hnd se)
                             =<< case (maySplitId, splitStrat) of
                                    (Just splitId, SplitNow) -> disjunctionOfList $ fromJustNote "solveTermEqs" $ performSplit eqs2 splitId
                                    (Just splitId, SplitLater) -> do
                                        insertGoal (SplitG splitId) False
                                        return eqs2
                                    _                        -> return eqs2
                        noContradictoryEqStore
                        return Changed
                    _ -> error "TODO")


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
    --trace ("DEBUG-EQ-FACTS" ++ show eqs) 
    (solveListEqs (solveTermEqs split) $ map (fmap factTerms) eqs)

-- DH: Fix this

factDHTag ::  EqInd LNFact LNTerm -> Equal FactTag
factDHTag (EqInd e indt t) =  (fmap factTag) e

factDHTerms :: EqInd LNFact LNTerm -> Equal [LNTerm]
factDHTerms (EqInd e indt t) = (fmap factTerms) e

solveActionFactEqs :: SplitStrategy -> LNFact -> LNFact -> Reduction ChangeIndicator
solveActionFactEqs split fa1 fa2 = do
    contradictoryIf (not $ all evalEqual $ map (fmap factTag) ([Equal fa1 fa2]) )
    return Changed

-- t1 here is the result of factTerms fa2, and indt1 the indicator of one product term of t1. 
solveFactDHEqs ::  Bool -> SplitStrategy -> LNFact -> LNFact -> S.Set LNTerm -> S.Set LNTerm -> Reduction ChangeIndicator
solveFactDHEqs b split fa1 fa2 bset nbset
    -- if one of fa1 or fa2 is a variable here we should apply substitution immediately!!
    | b =  do
            contradictoryIf (not (factTag fa1 == factTag fa2))
            contradictoryIf (not ((length $ factTerms fa1) == (length $ factTerms fa2)))
            solveListDHEqs (solveTermDHEqs b split bset nbset) $ zip (factTerms fa1) (factTerms fa2)
          --      outterm <- disjunctionOfList (multRootList t)
    | otherwise = do
            contradictoryIf (not (factTag fa1 == OutFact) && (factTag fa2 == KdhFact) )
            solveListDHEqs (solveTermDHEqs b split bset nbset) $ zip (factTerms fa1) (factTerms fa2)
         -- but be careful because that should hold only for G terms. E terms should be handled differrently.


-- need to take care of indicators here. Trying to do this in the "solveIndEqTermDHEqs" function. 
{-solveActionFactDHEqs :: SplitStrategy -> Equal LNFact -> RuleACInst -> Reduction ChangeIndicator
solveActionFactDHEqs split eq@(Equal fa1 fa2) ru = do
    contradictoryIf (not (factTag fa1 == factTag fa2) )
    contradictoryIf (not $ evalEqual $ (fmap length) eq1)
    (solveListDHEqs (solveIndEqTermDHEqs split b nb) $ flatten eq1)
        where 
            eq1 = ((fmap factTerms) eq)
            flatten (Equal l r) = zipWith Equal l r
            b = S.fromList $ basisOfRule ru
            nb = S.fromList $ notBasisOfRule ru
-}

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

solveListDHEqs :: ( (a,a) -> Reduction b) -> [(a,a)] -> Reduction b
solveListDHEqs solver eqs = do
    case eqs of
        [a] -> solver a
        (a : as) -> do
            solver a
            solveListDHEqs solver as
    -- on RHS "Equal" 

-- | Solve a number of equalities between lists interpreted as free terms
-- using the given solver for solving the entailed per-element equalities.
{-solveListDHEqs :: ([EqInd a b] -> Reduction c) -> [EqInd [a] [b]] -> Reduction c
solveListDHEqs solver eqs = do
    contradictoryIf (not $ all evalEqual $ map (fmap length) (map geteq eqs)) -- TODO: what is the length doing here?
    solver $ concatMap flatten eqs -- flatten eqs
  where
    flatten (EqInd eqp indt t) = zipWith (EqInd eqp indt t)
-}

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

