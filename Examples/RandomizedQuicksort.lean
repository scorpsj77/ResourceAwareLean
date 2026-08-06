/-
Copyright (c) 2026 James Needham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Needham
-/

import TextbookAlgorithms.KleinbergTardos.Chapter13.RandomizedQuicksort.Correctness
import TextbookAlgorithms.KleinbergTardos.Chapter13.RandomizedQuicksort.Complexity

/-!
# Architecture and exact-cost checks for randomized Quicksort

The executable first-pivot folds check concrete results, costs, and ordered observations. The
correspondence theorems then connect those deterministic checks to the actual `RandCostM`
interpreters without implementing the algorithm in a concrete cost monad.
-/

namespace Cslib.Textbooks.KleinbergTardos.Chapter13.RandomizedQuicksort.Test

open Cslib.Algorithms.Lean
open ResourceAware.Program
open ResourceAware.Algorithms

set_option linter.style.nativeDecide false

noncomputable section

/-! ## Decidable views of dependent observations -/

/-- A fully informative, decidable view used only for executable trace assertions. -/
inductive ObservationView where
  | baseCase (size measurement : Nat)
  | pivotIndex (tailLength index measurement : Nat)
  | comparison (left right : Nat) (answer : Bool) (measurement : Nat)
deriving Repr, DecidableEq

/-- Forget only the proof that a recorded pivot index is in bounds. -/
def observationView : Observation Nat -> ObservationView
  | .baseCase size measurement => .baseCase size measurement
  | .pivotIndex tailLength index measurement =>
      .pivotIndex tailLength index.val measurement
  | .comparison left right answer measurement =>
      .comparison left right answer measurement

/-! ## A nontrivial constant-size execution -/

def smallInput : List Nat := [3, 1, 2]

def smallBaseTime : TimeM Nat (List Nat) :=
  runFirstTime CostModel.comparisonOnly (quicksortProgram smallInput)

def smallScaledTime : TimeM Nat (List Nat) :=
  runFirstTime (CostModel.scaledComparisons 2) (quicksortProgram smallInput)

def smallTextbookTime : TimeM Nat (List Nat) :=
  runFirstTime CostModel.textbookModel (quicksortProgram smallInput)

def smallBaseRun : RandCostM Nat (List Nat) :=
  interpretFirst CostModel.comparisonOnly (quicksortProgram smallInput)

def smallBasePureRun : PMF (List Nat) :=
  evalWith .firstLinearOrder (quicksortProgram smallInput)

def smallBaseTraceRun : ResourceAware.TraceM (Observation Nat) (List Nat) :=
  runFirstTrace CostModel.comparisonOnly (quicksortProgram smallInput)

def smallBaseTrace : List ObservationView :=
  [ .baseCase 3 0,
    .comparison 3 1 false 1,
    .comparison 3 2 false 1,
    .comparison 1 2 true 1 ]

def smallBaseTracedRun : RandCostM Nat (List Nat × List (Observation Nat)) :=
  interpretTracedWith .firstLinearOrder CostModel.comparisonOnly
    (quicksortProgram smallInput)

example : smallBaseTime.ret = [1, 2, 3] := by
  native_decide

example : smallBaseTime.time = 3 := by
  native_decide

example : smallScaledTime.ret = smallBaseTime.ret := by
  native_decide

example : smallScaledTime.time = 6 := by
  native_decide

example : smallTextbookTime.ret = smallBaseTime.ret := by
  native_decide

example : smallTextbookTime.time = 4 := by
  native_decide

example : smallBaseRun.joint = PMF.pure ([1, 2, 3], 3) := by
  rw [smallBaseRun, interpretFirst_eq_deterministicRandCost]
  change PMF.pure (smallBaseTime.ret, smallBaseTime.time) = PMF.pure ([1, 2, 3], 3)
  congr 1
  all_goals native_decide

/-- Cost erasure exposes the same checked result in the pure PMF view. -/
example : smallBaseRun.ret = smallBasePureRun := by
  exact interpretWith_ret_eq_evalWith .firstLinearOrder CostModel.comparisonOnly
    (quicksortProgram smallInput)

example : smallBasePureRun = PMF.pure [1, 2, 3] := by
  rw [<- show smallBaseRun.ret = smallBasePureRun from
    interpretWith_ret_eq_evalWith .firstLinearOrder CostModel.comparisonOnly
      (quicksortProgram smallInput)]
  rw [smallBaseRun, interpretFirst_eq_deterministicRandCost]
  change (RandCostM.deterministic smallBaseTime.ret smallBaseTime.time).ret = _
  rw [RandCostM.ret_deterministic]
  congr 1
  native_decide

example : smallBaseTraceRun.ret = [1, 2, 3] := by
  native_decide

example : (ResourceAware.TraceM.events smallBaseTraceRun).map observationView =
    smallBaseTrace := by
  native_decide

example : exactTraceCost (ResourceAware.TraceM.events smallBaseTraceRun) = 3 := by
  native_decide

example : comparisonCount (ResourceAware.TraceM.events smallBaseTraceRun) = 3 := by
  native_decide

/-- Erasing the actual randomized observation trace preserves the measured computation. -/
example : (Prod.fst <$> smallBaseTracedRun) = smallBaseRun := by
  exact eraseTrace_interpretTracedWith .firstLinearOrder CostModel.comparisonOnly
    (quicksortProgram smallInput)

/-! ## The exact uniform distribution on four elements -/

/-- Pivot-free continuations cannot distinguish uniform pivots from first pivots. -/
theorem interpretWith_uniform_eq_first_of_pivotFree [LinearOrder alpha]
    (model : CostModel alpha) (program : Program alpha beta) (hProgram : PivotFree program) :
    interpretWith .uniformLinearOrder model program = interpretFirst model program := by
  unfold interpretWith interpretFirst
  induction program with
  | pure value => rfl
  | liftBind operation next ih =>
      unfold PivotFree at hProgram
      simp only [ResourceAware.Program.runRandCost, PFunctor.FreeM.liftM]
      cases operation with
      | comparison comparison =>
          cases comparison with
          | le left right =>
              rw [show
                measuredHandler
                    (SemanticBackend.uniformLinearOrder (alpha := alpha)) model
                    (.comparison (.le left right)) =
                  measuredHandler
                    (SemanticBackend.firstLinearOrder (alpha := alpha)) model
                    (.comparison (.le left right)) by rfl]
              apply congrArg (fun continuation =>
                measuredHandler
                    (SemanticBackend.firstLinearOrder (alpha := alpha)) model
                    (.comparison (.le left right)) >>= continuation)
              funext response
              exact ih response (hProgram.2 response)
      | baseCase size =>
          rw [show
            measuredHandler
                (SemanticBackend.uniformLinearOrder (alpha := alpha)) model (.baseCase size) =
              measuredHandler
                (SemanticBackend.firstLinearOrder (alpha := alpha)) model (.baseCase size) by
              rfl]
          apply congrArg (fun continuation =>
            measuredHandler
                (SemanticBackend.firstLinearOrder (alpha := alpha)) model (.baseCase size) >>=
              continuation)
          funext response
          exact ih response (hProgram.2 response)
      | choosePivotIndex tailLength =>
          exact hProgram.1.elim

/-- A pivot-free uniform continuation is the singleton embedding of its executable fold. -/
theorem interpretWith_uniform_eq_deterministic_of_pivotFree [LinearOrder alpha]
    (model : CostModel alpha) (program : Program alpha beta) (hProgram : PivotFree program) :
    interpretWith .uniformLinearOrder model program =
      ResourceAware.Program.deterministicRandCost (runFirstTime model program) := by
  calc
    interpretWith .uniformLinearOrder model program = interpretFirst model program :=
      interpretWith_uniform_eq_first_of_pivotFree model program hProgram
    _ = ResourceAware.Program.deterministicRandCost (runFirstTime model program) :=
      interpretFirst_eq_deterministicRandCost model program

def fourInput : List Nat := [4, 1, 3, 2]

/-- The concrete universe-zero type of the four root positions. -/
abbrev FourIndex := ULift.{0, 0} (Fin 4)

/-- The root continuation after one of the four uniformly sampled pivot positions. -/
def fourAfterPivot (sampledIndex : FourIndex) : Program Nat (List Nat) := do
  let pivot := fourInput.get sampledIndex.down
  let remainder := fourInput.eraseIdx sampledIndex.down
  let parts <- partitionProgram pivot remainder
  let sortedLower <- quicksortProgram parts.lower
  let sortedUpper <- quicksortProgram parts.upper
  pure (sortedLower ++ pivot :: sortedUpper)

theorem quicksortProgram_fourInput :
    quicksortProgram fourInput = choosePivotIndex 3 >>= fourAfterPivot := by
  unfold fourAfterPivot fourInput
  rw [quicksortProgram]
  simp [List.length]

/-- Every n=4 root continuation is pivot-free because both partitions have size at most three. -/
theorem pivotFree_fourAfterPivot (sampledIndex : FourIndex) :
    PivotFree (fourAfterPivot sampledIndex) := by
  unfold fourAfterPivot
  refine PivotFree.bind _ _ (PivotFree.partitionProgram _ _) ?_
  intro parts
  have hErase :
      (fourInput.eraseIdx sampledIndex.down).length + 1 = fourInput.length :=
    List.length_eraseIdx_add_one sampledIndex.down.isLt
  have hFourLength : fourInput.length = 4 := by
    native_decide
  have hEraseLength : (fourInput.eraseIdx sampledIndex.down).length = 3 := by
    omega
  have hParts :
      parts.lower.length + parts.upper.length =
        (fourInput.eraseIdx sampledIndex.down).length := by
    simpa using parts.perm.length_eq
  refine PivotFree.bind _ _
    (PivotFree.quicksortProgram_of_length_le_three parts.lower (by omega)) ?_
  intro sortedLower
  refine PivotFree.bind _ _
    (PivotFree.quicksortProgram_of_length_le_three parts.upper (by omega)) ?_
  intro sortedUpper
  exact PivotFree.pure _

/-- Execute one already-selected root branch in the deterministic cost fold. -/
def fourBranchTime (model : CostModel Nat) (sampledIndex : FourIndex) : Nat :=
  (runFirstTime model (fourAfterPivot sampledIndex)).time

/-- Uniform n=4 execution under an arbitrary operation-cost model. -/
def fourRunWith (model : CostModel Nat) : RandCostM Nat (List Nat) :=
  interpret model (quicksortProgram fourInput)

/-- Separate the sole random root request from its four deterministic continuations. -/
theorem fourRunWith_eq_uniform_branches (model : CostModel Nat) :
    fourRunWith model =
      (RandCostM.sampleAtCost (PMF.uniformOfFintype FourIndex)
          (model.operationCost (.choosePivotIndex 3)) >>= fun index =>
        ResourceAware.Program.deterministicRandCost (runFirstTime model (fourAfterPivot index))) :=
    by
  unfold fourRunWith interpret
  rw [quicksortProgram_fourInput, interpretWith_bind, interpretWith_choosePivotIndex]
  change
    (RandCostM.sampleAtCost (PMF.uniformOfFintype FourIndex)
        (model.operationCost (.choosePivotIndex 3)) >>= fun index =>
      interpretWith .uniformLinearOrder model (fourAfterPivot index)) = _
  apply congrArg (fun continuation =>
    RandCostM.sampleAtCost (PMF.uniformOfFintype FourIndex)
      (model.operationCost (.choosePivotIndex 3)) >>= continuation)
  funext index
  exact interpretWith_uniform_eq_deterministic_of_pivotFree
    model (fourAfterPivot index) (pivotFree_fourAfterPivot index)

/-- Expected cost of n=4 is the uniform average of the four executable branch costs. -/
theorem fourRunWith_expectedCost (model : CostModel Nat) :
    (fourRunWith model).expectedCost =
      (model.operationCost (.choosePivotIndex 3) : ENNReal) +
        RandCostM.weightedSum (PMF.uniformOfFintype FourIndex)
          (fun index => (fourBranchTime model index : ENNReal)) := by
  rw [fourRunWith_eq_uniform_branches, RandCostM.expectedCost_bind_split]
  simp only [RandCostM.ret_sampleAtCost]
  have hSampleCost :
      (RandCostM.sampleAtCost (PMF.uniformOfFintype FourIndex)
        (model.operationCost (.choosePivotIndex 3))).expectedCost =
          (model.operationCost (.choosePivotIndex 3) : ENNReal) := by
    simp [RandCostM.sampleAtCost]
  rw [hSampleCost]
  simp only [ResourceAware.Program.deterministicRandCost,
    RandCostM.expectedCost_deterministic]
  rfl

def uniformFourRun : RandCostM Nat (List Nat) :=
  fourRunWith CostModel.comparisonOnly

def scaledFourRun : RandCostM Nat (List Nat) :=
  fourRunWith (CostModel.scaledComparisons 2)

def textbookFourRun : RandCostM Nat (List Nat) :=
  fourRunWith CostModel.textbookModel

theorem comparisonFourBranchTime_eq (sampledIndex : FourIndex) :
    fourBranchTime CostModel.comparisonOnly sampledIndex =
      if sampledIndex.down.val < 2 then 6 else 4 := by
  rcases sampledIndex with ⟨sampledIndex⟩
  fin_cases sampledIndex <;> native_decide

theorem scaledFourBranchTime_eq (sampledIndex : FourIndex) :
    fourBranchTime (CostModel.scaledComparisons 2) sampledIndex =
      if sampledIndex.down.val < 2 then 12 else 8 := by
  rcases sampledIndex with ⟨sampledIndex⟩
  fin_cases sampledIndex <;> native_decide

theorem textbookFourBranchTime_eq (sampledIndex : FourIndex) :
    fourBranchTime CostModel.textbookModel sampledIndex =
      if sampledIndex.down.val < 2 then 8 else 6 := by
  rcases sampledIndex with ⟨sampledIndex⟩
  fin_cases sampledIndex <;> native_decide

/-- Complete branch cost, including the random-pivot request at the root. -/
def fourTotalCost (model : CostModel Nat) (sampledIndex : FourIndex) : Nat :=
  model.operationCost (.choosePivotIndex 3) + fourBranchTime model sampledIndex

theorem comparisonFourTotalCost_eq (sampledIndex : FourIndex) :
    fourTotalCost CostModel.comparisonOnly sampledIndex =
      if sampledIndex.down.val < 2 then 6 else 4 := by
  simp [fourTotalCost, comparisonFourBranchTime_eq]

theorem scaledFourTotalCost_eq (sampledIndex : FourIndex) :
    fourTotalCost (CostModel.scaledComparisons 2) sampledIndex =
      if sampledIndex.down.val < 2 then 12 else 8 := by
  simp [fourTotalCost, scaledFourBranchTime_eq]

theorem textbookFourTotalCost_eq (sampledIndex : FourIndex) :
    fourTotalCost CostModel.textbookModel sampledIndex =
      if sampledIndex.down.val < 2 then 12 else 10 := by
  simp [fourTotalCost, textbookFourBranchTime_eq]
  split <;> norm_num

/-- Every uniform root branch returns the same sorted list. -/
theorem fourBranchResult_eq (sampledIndex : FourIndex) :
    (runFirstTime CostModel.comparisonOnly (fourAfterPivot sampledIndex)).ret =
      [1, 2, 3, 4] := by
  rcases sampledIndex with ⟨sampledIndex⟩
  fin_cases sampledIndex <;> native_decide

theorem uniformFourRun_ret : uniformFourRun.ret = PMF.pure [1, 2, 3, 4] := by
  rw [uniformFourRun, fourRunWith_eq_uniform_branches, RandCostM.ret_bind]
  simp only [RandCostM.ret_sampleAtCost, ResourceAware.Program.deterministicRandCost,
    RandCostM.ret_deterministic]
  simp_rw [fourBranchResult_eq]
  exact PMF.bind_const _ _

example : scaledFourRun.ret = uniformFourRun.ret := by
  unfold scaledFourRun uniformFourRun fourRunWith interpret
  exact interpretWith_ret_eq .uniformLinearOrder _ _ _

example : textbookFourRun.ret = uniformFourRun.ret := by
  unfold textbookFourRun uniformFourRun fourRunWith interpret
  exact interpretWith_ret_eq .uniformLinearOrder _ _ _

theorem uniformFourRun_expectedCost : uniformFourRun.expectedCost = 5 := by
  rw [uniformFourRun, fourRunWith_expectedCost]
  simp only [CostModel.operationCost_choosePivotIndex,
    CostModel.comparisonOnly_splitterFrame, Nat.cast_zero, zero_add]
  rw [ResourceAware.Program.weightedSum_uniformOfFintype]
  simp only [Fintype.card_ulift, Fintype.card_fin]
  have hSum :
      ∑ index : FourIndex,
        (fourBranchTime CostModel.comparisonOnly index : ENNReal) = 20 := by
    rw [<- (Equiv.ulift : FourIndex ≃ Fin 4).symm.sum_comp]
    simp_rw [comparisonFourBranchTime_eq]
    norm_num [Fin.sum_univ_succ]
  rw [hSum]
  norm_num only [Nat.cast_ofNat]
  rw [show (20 : ENNReal) = (4 : ENNReal) * 5 by norm_num]
  exact ENNReal.inv_mul_cancel_left (by norm_num) (by norm_num)

theorem scaledFourRun_expectedCost : scaledFourRun.expectedCost = 10 := by
  rw [scaledFourRun, fourRunWith_expectedCost]
  simp only [CostModel.operationCost_choosePivotIndex,
    CostModel.scaledComparisons_splitterFrame, Nat.cast_zero, zero_add]
  rw [ResourceAware.Program.weightedSum_uniformOfFintype]
  simp only [Fintype.card_ulift, Fintype.card_fin]
  have hSum :
      ∑ index : FourIndex,
        (fourBranchTime (CostModel.scaledComparisons 2) index : ENNReal) = 40 := by
    rw [<- (Equiv.ulift : FourIndex ≃ Fin 4).symm.sum_comp]
    simp_rw [scaledFourBranchTime_eq]
    norm_num [Fin.sum_univ_succ]
  rw [hSum]
  norm_num only [Nat.cast_ofNat]
  rw [show (40 : ENNReal) = (4 : ENNReal) * 10 by norm_num]
  exact ENNReal.inv_mul_cancel_left (by norm_num) (by norm_num)

theorem textbookFourRun_expectedCost : textbookFourRun.expectedCost = 11 := by
  rw [textbookFourRun, fourRunWith_expectedCost]
  simp only [CostModel.operationCost_choosePivotIndex,
    CostModel.textbookModel_splitterFrame]
  rw [ResourceAware.Program.weightedSum_uniformOfFintype]
  simp only [Fintype.card_ulift, Fintype.card_fin]
  have hSum :
      ∑ index : FourIndex,
        (fourBranchTime CostModel.textbookModel index : ENNReal) = 28 := by
    rw [<- (Equiv.ulift : FourIndex ≃ Fin 4).symm.sum_comp]
    simp_rw [textbookFourBranchTime_eq]
    norm_num [Fin.sum_univ_succ]
  rw [hSum]
  norm_num only [Nat.cast_ofNat]
  rw [show (28 : ENNReal) = (4 : ENNReal) * 7 by norm_num,
    ENNReal.inv_mul_cancel_left] <;>
    norm_num

example : RandCostM.ecwp uniformFourRun (fun _ => 0) = 5 := by
  rw [RandCostM.ecwp_zero, uniformFourRun_expectedCost]

/-! ## A deterministic endpoint branch -/

def endpointInput : List Nat := [0, 1, 2, 3, 4]

def leftmostFiveTime : TimeM Nat (List Nat) :=
  runFirstTime CostModel.comparisonOnly (quicksortProgram endpointInput)

def leftmostFiveRun : RandCostM Nat (List Nat) :=
  interpretFirst CostModel.comparisonOnly (quicksortProgram endpointInput)

def leftmostFiveTraceRun : ResourceAware.TraceM (Observation Nat) (List Nat) :=
  runFirstTrace CostModel.comparisonOnly (quicksortProgram endpointInput)

example : leftmostFiveTime.ret = endpointInput := by
  native_decide

example : leftmostFiveTime.time = 10 := by
  native_decide

example : leftmostFiveRun.joint = PMF.pure (endpointInput, 10) := by
  rw [leftmostFiveRun, interpretFirst_eq_deterministicRandCost]
  change PMF.pure (leftmostFiveTime.ret, leftmostFiveTime.time) =
    PMF.pure (endpointInput, 10)
  congr 1
  all_goals native_decide

example : leftmostFiveTraceRun.ret = endpointInput := by
  native_decide

example : exactTraceCost (ResourceAware.TraceM.events leftmostFiveTraceRun) = 10 := by
  native_decide

example : comparisonCount (ResourceAware.TraceM.events leftmostFiveTraceRun) = 10 := by
  native_decide

example : 10 = Nat.choose 5 2 := by
  native_decide

/-! ## Theorem-backed endpoint checks -/

example (output : List Nat) (hOutput : output ∈ (quicksort smallInput).ret.support) :
    Sorting.Correct smallInput output := by
  exact quicksort_result_correct smallInput output (by native_decide) hOutput

example :
    (quicksort endpointInput).expectedCost ≤
      expectedComparisonEnvelopeENN endpointInput.length := by
  exact quicksort_expectedComparisonCost_le endpointInput (by native_decide)

example : worstComparisonCost endpointInput = 10 := by
  rw [worstComparisonCost_eq_choose endpointInput (by native_decide)]
  native_decide

end

end Cslib.Textbooks.KleinbergTardos.Chapter13.RandomizedQuicksort.Test
