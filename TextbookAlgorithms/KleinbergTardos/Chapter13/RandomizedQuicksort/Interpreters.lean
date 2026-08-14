/-
Copyright (c) 2026 James Needham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Needham
-/

import ResourceAware.Program.Randomized
import ResourceAware.Effects.TraceM
import TextbookAlgorithms.KleinbergTardos.Chapter13.RandomizedQuicksort.ResourceModel
import Mathlib.Probability.Distributions.Uniform

/-!
# Interpreters for Kleinberg--Tardos randomized Quicksort

This module gives several meanings to the single free program in `Algorithm.lean`. Pivot and
comparison semantics are selected independently of resource costs. Ordinary probabilistic
execution folds the program into `PMF`; measured execution folds the same program into
`RandCostM Nat`. In particular, `quicksort` below is only an interpreter application and contains
no recursive algorithm definition in the concrete cost monad.

An optional state-transformer interpretation records ordered operation outcomes and their selected
measurements while retaining the same joint result/cost distribution after trace erasure.
-/

universe u

namespace KleinbergRandomizedQuicksort

open Cslib.Algorithms.Lean
open ResourceAware.Program
open ResourceAware.Algorithms

noncomputable section

/-! ## Semantic backends -/

/-- A source of pivot indices for every positive recursive subproblem size. -/
structure PivotBackend where
  choose : (tailLength : Nat) -> PMF (ULift (Fin (tailLength + 1)))

namespace PivotBackend

/-- Uniformly choose one of the `tailLength + 1` valid list positions. -/
def uniform : PivotBackend where
  choose := fun tailLength => PMF.uniformOfFintype (ULift (Fin (tailLength + 1)))

/-- Always choose index zero. This deterministic backend exposes a worst-case test branch. -/
def first : PivotBackend where
  choose := fun tailLength =>
    PMF.pure (ULift.up ⟨0, Nat.zero_lt_succ tailLength⟩)

/-- Always choose the last valid index. -/
def last : PivotBackend where
  choose := fun tailLength => PMF.pure (ULift.up (Fin.last tailLength))

@[simp] theorem first_choose (tailLength : Nat) :
    first.choose tailLength =
      PMF.pure (ULift.up ⟨0, Nat.zero_lt_succ tailLength⟩) :=
  rfl

@[simp] theorem last_choose (tailLength : Nat) :
    last.choose tailLength = PMF.pure (ULift.up (Fin.last tailLength)) :=
  rfl

end PivotBackend

/-- Probabilistic pivot semantics paired with deterministic comparison semantics. -/
structure SemanticBackend (alpha : Type u) where
  pivot : PivotBackend
  comparison : Sorting.ComparisonBackend alpha

namespace SemanticBackend

/-- The source semantics: uniform pivots and the ascending order on keys. -/
def uniformLinearOrder [LinearOrder alpha] : SemanticBackend alpha where
  pivot := .uniform
  comparison := .linearOrder

/-- Ascending comparisons with a deterministic first-position pivot. -/
def firstLinearOrder [LinearOrder alpha] : SemanticBackend alpha where
  pivot := .first
  comparison := .linearOrder

/-- Ascending comparisons with a deterministic last-position pivot. -/
def lastLinearOrder [LinearOrder alpha] : SemanticBackend alpha where
  pivot := .last
  comparison := .linearOrder

end SemanticBackend

/-! ## Operation handlers -/

/-- Interpret one operation probabilistically, without attaching a resource charge. -/
def semanticHandler (backend : SemanticBackend alpha) :
    (operation : Op alpha) -> PMF (Response operation)
  | .comparison (.le left right) =>
      PMF.pure (ULift.up (backend.comparison.le left right))
  | .baseCase _ => PMF.pure .unit
  | .choosePivotIndex tailLength => backend.pivot.choose tailLength

/-- Interpret one operation with the selected branch cost. -/
def measuredHandler (backend : SemanticBackend alpha) (model : CostModel alpha) :
    (operation : Op alpha) -> RandCostM Nat (Response operation) :=
  fun operation =>
    RandCostM.sampleAtCost (semanticHandler backend operation) (model.operationCost operation)

@[simp] theorem measuredHandler_joint (backend : SemanticBackend alpha)
    (model : CostModel alpha) (operation : Op alpha) :
    (measuredHandler backend model operation).joint =
      (semanticHandler backend operation).map fun response =>
        (response, model.operationCost operation) :=
  rfl

/-- The deterministic response selected by the first-position pivot backend. -/
def firstResponse [LinearOrder alpha] : (operation : Op alpha) -> Response operation
  | .comparison (.le left right) => ULift.up (decide (left <= right))
  | .baseCase _ => .unit
  | .choosePivotIndex tailLength => ULift.up ⟨0, Nat.zero_lt_succ tailLength⟩

/-- Deterministic cost semantics corresponding to `SemanticBackend.firstLinearOrder`. -/
def firstTimeHandler [LinearOrder alpha] (model : CostModel alpha)
    (operation : Op alpha) : TimeM Nat (Response operation) :=
  ⟨firstResponse operation, model.operationCost operation⟩

/-- Executable deterministic fold of the free program using first-position pivots. -/
def runFirstTime [LinearOrder alpha] (model : CostModel alpha)
    (program : Program alpha beta) : TimeM Nat beta :=
  ResourceAware.Program.runTime (firstTimeHandler model) program

@[simp] theorem semanticHandler_firstLinearOrder [LinearOrder alpha]
    (operation : Op alpha) :
    semanticHandler (.firstLinearOrder) operation = PMF.pure (firstResponse operation) := by
  cases operation with
  | comparison comparison => cases comparison; rfl
  | baseCase => rfl
  | choosePivotIndex => rfl

@[simp] theorem measuredHandler_firstLinearOrder [LinearOrder alpha]
    (model : CostModel alpha) (operation : Op alpha) :
    measuredHandler (.firstLinearOrder) model operation =
      ResourceAware.Program.deterministicRandCost (firstTimeHandler model operation) := by
  apply RandCostM.ext
  rw [measuredHandler_joint, semanticHandler_firstLinearOrder, PMF.pure_map]
  rfl

@[simp] theorem measuredHandler_ret (backend : SemanticBackend alpha)
    (model : CostModel alpha) (operation : Op alpha) :
    (measuredHandler backend model operation).ret = semanticHandler backend operation := by
  simp [measuredHandler]

@[simp] theorem semanticHandler_comparison (backend : SemanticBackend alpha)
    (left right : alpha) :
    semanticHandler backend (.comparison (.le left right)) =
      PMF.pure (ULift.up (backend.comparison.le left right)) :=
  rfl

@[simp] theorem semanticHandler_baseCase (backend : SemanticBackend alpha) (size : Nat) :
    semanticHandler backend (.baseCase size) = PMF.pure .unit :=
  rfl

@[simp] theorem semanticHandler_choosePivotIndex (backend : SemanticBackend alpha)
    (tailLength : Nat) :
    semanticHandler backend (.choosePivotIndex tailLength) = backend.pivot.choose tailLength :=
  rfl

/-! ## PMF and RandCostM runners -/

/-- Evaluate a free program under an explicitly selected semantic backend. -/
def evalWith (backend : SemanticBackend alpha) (program : Program alpha beta) : PMF beta :=
  ResourceAware.Program.evalPMF (semanticHandler backend) program

/-- Evaluate under uniform pivots and the ascending linear order. -/
def eval [LinearOrder alpha] (program : Program alpha beta) : PMF beta :=
  evalWith .uniformLinearOrder program

/-- Measure a free program under independently selected semantic and cost backends. -/
def interpretWith (backend : SemanticBackend alpha) (model : CostModel alpha)
    (program : Program alpha beta) : RandCostM Nat beta :=
  ResourceAware.Program.runRandCost (measuredHandler backend model) program

/-- Measure under the source's uniform-pivot ascending semantics. -/
def interpret [LinearOrder alpha] (model : CostModel alpha)
    (program : Program alpha beta) : RandCostM Nat beta :=
  interpretWith .uniformLinearOrder model program

/--
The requested comparison-counting Quicksort view.

All recursive control remains in `quicksortProgram`; this declaration merely interprets that free
program in `RandCostM Nat` using the comparison-only model.
-/
def quicksort [LinearOrder alpha] (xs : List alpha) : RandCostM Nat (List alpha) :=
  interpret CostModel.comparisonOnly (quicksortProgram xs)

/-- Deterministic first-pivot execution, useful for endpoint-branch tests and witnesses. -/
def interpretFirst [LinearOrder alpha] (model : CostModel alpha)
    (program : Program alpha beta) : RandCostM Nat beta :=
  interpretWith .firstLinearOrder model program

/-- First-pivot execution is the singleton randomized embedding of an executable `TimeM` fold. -/
theorem interpretFirst_eq_deterministicRandCost [LinearOrder alpha]
    (model : CostModel alpha) (program : Program alpha beta) :
    interpretFirst model program =
      ResourceAware.Program.deterministicRandCost (runFirstTime model program) := by
  unfold interpretFirst interpretWith runFirstTime
  have hhandler :
      measuredHandler (SemanticBackend.firstLinearOrder (alpha := alpha)) model =
        fun operation => ResourceAware.Program.deterministicRandCost
          (firstTimeHandler model operation) := by
    funext operation
    exact measuredHandler_firstLinearOrder model operation
  rw [hhandler]
  exact ResourceAware.Program.runRandCost_deterministic_eq_runTime
    (firstTimeHandler model) program

/-- Deterministic last-pivot execution, useful for endpoint-branch tests and witnesses. -/
def interpretLast [LinearOrder alpha] (model : CostModel alpha)
    (program : Program alpha beta) : RandCostM Nat beta :=
  interpretWith .lastLinearOrder model program

@[simp] theorem evalWith_pure (backend : SemanticBackend alpha) (value : beta) :
    evalWith backend (pure value : Program alpha beta) = PMF.pure value :=
  rfl

@[simp] theorem interpretWith_pure (backend : SemanticBackend alpha)
    (model : CostModel alpha) (value : beta) :
    interpretWith backend model (pure value : Program alpha beta) = pure value :=
  rfl

@[simp] theorem evalWith_request (backend : SemanticBackend alpha) (operation : Op alpha) :
    evalWith backend (request operation) = semanticHandler backend operation := by
  exact ResourceAware.Program.evalPMF_request (signature := Signature alpha)
    (semanticHandler backend) operation

@[simp] theorem evalWith_markBaseCase (backend : SemanticBackend alpha) (size : Nat) :
    evalWith backend (markBaseCase size) = PMF.pure .unit := by
  unfold markBaseCase
  rw [evalWith_request]
  rfl

@[simp] theorem evalWith_compareLE (backend : SemanticBackend alpha)
    (left right : alpha) :
    evalWith backend (compareLE left right) =
      PMF.pure (ULift.up (backend.comparison.le left right)) := by
  unfold compareLE
  rw [evalWith_request]
  rfl

@[simp] theorem evalWith_choosePivotIndex (backend : SemanticBackend alpha)
    (tailLength : Nat) :
    evalWith backend (choosePivotIndex tailLength) = backend.pivot.choose tailLength := by
  unfold choosePivotIndex
  rw [evalWith_request]
  rfl

theorem evalWith_liftBind (backend : SemanticBackend alpha)
    (operation : Op alpha) (next : Response operation -> Program alpha beta) :
    evalWith backend (.liftBind operation next) =
      (semanticHandler backend operation >>= fun response =>
        evalWith backend (next response)) :=
  rfl

theorem evalWith_bind (backend : SemanticBackend alpha)
    (program : Program alpha beta) (next : beta -> Program alpha gamma) :
    evalWith backend (program >>= next) =
      (evalWith backend program >>= fun value => evalWith backend (next value)) := by
  exact ResourceAware.Program.evalPMF_bind (semanticHandler backend) program next

@[simp] theorem interpretWith_request (backend : SemanticBackend alpha)
    (model : CostModel alpha) (operation : Op alpha) :
    interpretWith backend model (request operation) = measuredHandler backend model operation := by
  exact ResourceAware.Program.runRandCost_request (signature := Signature alpha)
    (measuredHandler backend model) operation

@[simp] theorem interpretWith_markBaseCase (backend : SemanticBackend alpha)
    (model : CostModel alpha) (size : Nat) :
    interpretWith backend model (markBaseCase size) =
      measuredHandler backend model (.baseCase size) := by
  unfold markBaseCase
  rw [interpretWith_request]

@[simp] theorem interpretWith_compareLE (backend : SemanticBackend alpha)
    (model : CostModel alpha) (left right : alpha) :
    interpretWith backend model (compareLE left right) =
      measuredHandler backend model (.comparison (.le left right)) := by
  unfold compareLE
  rw [interpretWith_request]

@[simp] theorem interpretWith_choosePivotIndex (backend : SemanticBackend alpha)
    (model : CostModel alpha) (tailLength : Nat) :
    interpretWith backend model (choosePivotIndex tailLength) =
      measuredHandler backend model (.choosePivotIndex tailLength) := by
  unfold choosePivotIndex
  rw [interpretWith_request]

theorem interpretWith_liftBind (backend : SemanticBackend alpha)
    (model : CostModel alpha) (operation : Op alpha)
    (next : Response operation -> Program alpha beta) :
    interpretWith backend model (.liftBind operation next) =
      (measuredHandler backend model operation >>= fun response =>
        interpretWith backend model (next response)) :=
  rfl

theorem interpretWith_bind (backend : SemanticBackend alpha)
    (model : CostModel alpha) (program : Program alpha beta)
    (next : beta -> Program alpha gamma) :
    interpretWith backend model (program >>= next) =
      (interpretWith backend model program >>= fun value =>
        interpretWith backend model (next value)) := by
  exact ResourceAware.Program.runRandCost_bind (measuredHandler backend model) program next

@[simp] theorem evalWith_compareSwap (backend : SemanticBackend alpha) (left right : alpha) :
    evalWith backend (compareSwap left right) =
      PMF.pure (if backend.comparison.le left right then (left, right) else (right, left)) := by
  unfold compareSwap
  rw [evalWith_bind, evalWith_compareLE]
  cases h : backend.comparison.le left right
  case false =>
    change
      (PMF.pure (ULift.up false)).bind
          (fun value => evalWith backend
            (if value.down = true then pure (left, right) else pure (right, left))) =
        PMF.pure (right, left)
    rw [PMF.pure_bind]
    exact evalWith_pure backend (right, left)
  case true =>
    change
      (PMF.pure (ULift.up true)).bind
          (fun value => evalWith backend
            (if value.down = true then pure (left, right) else pure (right, left))) =
        PMF.pure (left, right)
    rw [PMF.pure_bind]
    exact evalWith_pure backend (left, right)

@[simp] theorem interpretWith_compareSwap (backend : SemanticBackend alpha)
    (model : CostModel alpha) (left right : alpha) :
    interpretWith backend model (compareSwap left right) =
      RandCostM.deterministic
        (if backend.comparison.le left right then (left, right) else (right, left))
        (model.comparison.cost left right) := by
  unfold compareSwap
  rw [interpretWith_bind, interpretWith_compareLE]
  apply RandCostM.ext
  cases h : backend.comparison.le left right <;>
    simp [measuredHandler, semanticHandler, h, RandCostM.sampleAtCost,
      RandCostM.sampleWithCost, RandCostM.deterministic, PMF.pure_map]

@[simp] theorem interpretWith_ret_eq_evalWith (backend : SemanticBackend alpha)
    (model : CostModel alpha) (program : Program alpha beta) :
    (interpretWith backend model program).ret = evalWith backend program := by
  apply ResourceAware.Program.ret_runRandCost_eq_evalPMF
  exact measuredHandler_ret backend model

@[simp] theorem interpret_ret_eq_eval [LinearOrder alpha] (model : CostModel alpha)
    (program : Program alpha beta) :
    (interpret model program).ret = eval program :=
  interpretWith_ret_eq_evalWith .uniformLinearOrder model program

/-- Changing only costs leaves the complete result marginal unchanged. -/
theorem interpretWith_ret_eq (backend : SemanticBackend alpha)
    (left right : CostModel alpha) (program : Program alpha beta) :
    (interpretWith backend left program).ret = (interpretWith backend right program).ret := by
  rw [interpretWith_ret_eq_evalWith, interpretWith_ret_eq_evalWith]

/-! ## Ordered observations -/

/--
One executed operation outcome paired with its selected measurement.

The dependent pivot-index field records a valid index for exactly the frame that emitted it.
-/
inductive Observation (alpha : Type u) where
  | baseCase (size measurement : Nat)
  | pivotIndex (tailLength : Nat) (index : Fin (tailLength + 1)) (measurement : Nat)
  | comparison (left right : alpha) (answer : Bool) (measurement : Nat)
deriving Repr, DecidableEq

namespace Observation

/-- Recover the abstract operation represented by an observation. -/
def operation : Observation alpha -> Op alpha
  | .baseCase size _ => .baseCase size
  | .pivotIndex tailLength _ _ => .choosePivotIndex tailLength
  | .comparison left right _ _ => .comparison (.le left right)

/-- Read the model-selected cost stored in an observation. -/
def measurement : Observation alpha -> Nat
  | .baseCase _ cost => cost
  | .pivotIndex _ _ cost => cost
  | .comparison _ _ _ cost => cost

/-- Whether an observation is an element comparison. -/
def isComparison : Observation alpha -> Bool
  | .comparison _ _ _ _ => true
  | _ => false

end Observation

/-- Build the observation determined by one operation, its response, and its selected cost. -/
def observe (model : CostModel alpha) :
    (operation : Op alpha) -> Response operation -> Observation alpha
  | .comparison (.le left right), response =>
      .comparison left right response.down
        (model.operationCost (.comparison (.le left right)))
  | .baseCase size, _ => .baseCase size (model.operationCost (.baseCase size))
  | .choosePivotIndex tailLength, response =>
      .pivotIndex tailLength response.down
        (model.operationCost (.choosePivotIndex tailLength))

@[simp] theorem observe_operation (model : CostModel alpha) (operation : Op alpha)
    (response : Response operation) :
    (observe model operation response).operation = operation := by
  cases operation with
  | comparison comparison => cases comparison; rfl
  | baseCase => rfl
  | choosePivotIndex => rfl

@[simp] theorem observe_measurement (model : CostModel alpha) (operation : Op alpha)
    (response : Response operation) :
    (observe model operation response).measurement = model.operationCost operation := by
  cases operation with
  | comparison comparison => cases comparison; rfl
  | baseCase => rfl
  | choosePivotIndex => rfl

/-- Deterministic first-pivot operation semantics with one ordered observation per request. -/
def firstTraceHandler [LinearOrder alpha] (model : CostModel alpha)
    (operation : Op alpha) : ResourceAware.TraceM (Observation alpha) (Response operation) :=
  ⟨firstResponse operation,
    ResourceAware.EventTrace.singleton (observe model operation (firstResponse operation))⟩

/-- Executable ordered trace of the same free program under deterministic first pivots. -/
def runFirstTrace [LinearOrder alpha] (model : CostModel alpha)
    (program : Program alpha beta) : ResourceAware.TraceM (Observation alpha) beta :=
  program.liftM (firstTraceHandler model)

/-- Sum the selected measurements in an ordered observation list. -/
def exactTraceCost (observations : List (Observation alpha)) : Nat :=
  observations.foldl (fun total observation => total + observation.measurement) 0

/-- Number of element-comparison observations. -/
def comparisonCount (observations : List (Observation alpha)) : Nat :=
  observations.countP Observation.isComparison

/-- One measured operation as a state transformation accumulating ordered observations. -/
def tracedMeasuredHandler (backend : SemanticBackend alpha) (model : CostModel alpha)
    (operation : Op alpha) :
    StateT (List (Observation alpha)) (RandCostM Nat) (Response operation) :=
  fun observations => do
    let response <- measuredHandler backend model operation
    pure (response, observations ++ [observe model operation response])

/-- Fold a free program into the stateful traced view from an explicit initial trace. -/
def interpretTracedFrom (backend : SemanticBackend alpha) (model : CostModel alpha)
    (program : Program alpha beta) (observations : List (Observation alpha)) :
    RandCostM Nat (beta × List (Observation alpha)) :=
  program.liftM (tracedMeasuredHandler backend model) observations

@[simp] theorem interpretTracedFrom_pure (backend : SemanticBackend alpha)
    (model : CostModel alpha) (value : beta)
    (observations : List (Observation alpha)) :
    interpretTracedFrom backend model (pure value) observations =
      pure (value, observations) :=
  rfl

theorem interpretTracedFrom_bind (backend : SemanticBackend alpha)
    (model : CostModel alpha) (program : Program alpha beta)
    (next : beta -> Program alpha gamma) (observations : List (Observation alpha)) :
    interpretTracedFrom backend model (program >>= next) observations =
      (do
        let outcome <- interpretTracedFrom backend model program observations
        interpretTracedFrom backend model (next outcome.1) outcome.2) := by
  unfold interpretTracedFrom
  rw [PFunctor.FreeM.liftM_bind]
  rfl

/-- Fold a free program into the stateful traced view with an initially empty trace. -/
def interpretTracedWith (backend : SemanticBackend alpha) (model : CostModel alpha)
    (program : Program alpha beta) : RandCostM Nat (beta × List (Observation alpha)) :=
  interpretTracedFrom backend model program []

/-- Uniform-pivot ascending traced execution. -/
def interpretTraced [LinearOrder alpha] (model : CostModel alpha)
    (program : Program alpha beta) : RandCostM Nat (beta × List (Observation alpha)) :=
  interpretTracedWith .uniformLinearOrder model program

set_option maxHeartbeats 800000 in
-- The dependent StateT continuation equality takes extra elaboration work for this free signature.
private theorem run'_liftM_tracedMeasuredHandler (backend : SemanticBackend alpha)
    (model : CostModel alpha) (program : Program alpha beta)
    (observations : List (Observation alpha)) :
    StateT.run'
        (program.liftM (tracedMeasuredHandler backend model)) observations =
      program.liftM (measuredHandler backend model) := by
  induction program generalizing observations with
  | pure value =>
      change
        (Prod.fst <$> (pure (value, observations) :
          RandCostM Nat (beta × List (Observation alpha)))) =
        (pure value : RandCostM Nat beta)
      apply RandCostM.ext
      simp [RandCostM.deterministic, PMF.pure_map]
  | liftBind operation next ih =>
      change Op alpha at operation
      simp only [PFunctor.FreeM.liftM, StateT.run'_eq, StateT.run_bind, map_bind]
      change
        ((measuredHandler backend model operation >>= fun response =>
            pure (response, observations ++ [observe model operation response])) >>= fun outcome =>
          Prod.fst <$>
            ((next outcome.1).liftM (tracedMeasuredHandler backend model)).run outcome.2) =
        (measuredHandler backend model operation >>= fun response =>
          (next response).liftM (measuredHandler backend model))
      rw [LawfulMonad.bind_assoc]
      apply congrArg (fun continuation =>
        measuredHandler backend model operation >>= continuation)
      funext response
      simp only [LawfulMonad.pure_bind]
      simpa only [StateT.run'_eq] using
        ih response (observations ++ [observe model operation response])

private theorem eraseTrace_interpretTracedFrom (backend : SemanticBackend alpha)
    (model : CostModel alpha) (program : Program alpha beta)
    (observations : List (Observation alpha)) :
    (Prod.fst <$> interpretTracedFrom backend model program observations) =
      interpretWith backend model program := by
  exact run'_liftM_tracedMeasuredHandler backend model program observations

/-- Erasing observations preserves the complete measured joint result/cost distribution. -/
theorem eraseTrace_interpretTracedWith (backend : SemanticBackend alpha)
    (model : CostModel alpha) (program : Program alpha beta) :
    (Prod.fst <$> interpretTracedWith backend model program) =
      interpretWith backend model program := by
  exact eraseTrace_interpretTracedFrom backend model program []

@[simp] theorem interpretTracedWith_ret_map_fst (backend : SemanticBackend alpha)
    (model : CostModel alpha) (program : Program alpha beta) :
    (interpretTracedWith backend model program).ret.map Prod.fst = evalWith backend program := by
  rw [<- RandCostM.ret_map, eraseTrace_interpretTracedWith, interpretWith_ret_eq_evalWith]

end

end KleinbergRandomizedQuicksort
