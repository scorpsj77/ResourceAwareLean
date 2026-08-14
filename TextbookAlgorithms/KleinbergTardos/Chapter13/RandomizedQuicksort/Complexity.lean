/-
Copyright (c) 2026 James Needham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Needham
-/

import TextbookAlgorithms.KleinbergTardos.Chapter13.RandomizedQuicksort.Correctness
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Finset.Sort
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Find

/-!
# Expected complexity of Kleinberg--Tardos randomized Quicksort

This file develops the expected-comparison recurrence in a form suitable for connection to
`RandCostM.ecwp`. The recurrence is kept separate from the free-program implementation: its
eventual endpoint below observes the program only through the concrete uniform interpreter.
-/

namespace Cslib.Textbooks.KleinbergTardos.Chapter13.RandomizedQuicksort

open Cslib.Algorithms.Lean
open ResourceAware.Program
open ResourceAware.Algorithms
open Filter Asymptotics

noncomputable section

variable {alpha : Type}

/-! ## Joint-support decomposition -/

/-- Membership in the joint support of a cost-monad bind exposes both branch costs. -/
theorem mem_joint_support_bind_iff (m : RandCostM Nat beta)
    (next : beta -> RandCostM Nat gamma) (result : gamma) (cost : Nat) :
    (result, cost) ∈ (m >>= next).joint.support ↔
      ∃ value firstCost secondCost,
        (value, firstCost) ∈ m.joint.support ∧
        (result, secondCost) ∈ (next value).joint.support ∧
        cost = firstCost + secondCost := by
  rw [RandCostM.joint_bind, PMF.mem_support_bind_iff]
  constructor
  · rintro ⟨⟨value, firstCost⟩, hFirst, hRest⟩
    obtain ⟨⟨nextResult, secondCost⟩, hSecond, hPure⟩ :=
      (PMF.mem_support_bind_iff _ _ _).mp hRest
    rw [PMF.mem_support_pure_iff] at hPure
    cases hPure
    exact ⟨value, firstCost, secondCost, hFirst, hSecond, rfl⟩
  · rintro ⟨value, firstCost, secondCost, hFirst, hSecond, rfl⟩
    refine ⟨(value, firstCost), hFirst, ?_⟩
    refine (PMF.mem_support_bind_iff _ _ _).mpr
      ⟨(result, secondCost), hSecond, ?_⟩
    exact (PMF.mem_support_pure_iff _ _).mpr rfl

theorem joint_support_sample_cost_eq_zero (distribution : PMF beta)
    (value : beta) (cost : Nat)
    (hMem : (value, cost) ∈
      (RandCostM.sample distribution : RandCostM Nat beta).joint.support) :
    cost = 0 := by
  rw [RandCostM.joint_sample, PMF.mem_support_map_iff] at hMem
  obtain ⟨sampled, _, hEqual⟩ := hMem
  exact (congrArg Prod.snd hEqual).symm

theorem mem_joint_support_sample_of_mem (distribution : PMF beta) (value : beta)
    (hValue : value ∈ distribution.support) :
    (value, 0) ∈
      (RandCostM.sample distribution : RandCostM Nat beta).joint.support := by
  rw [RandCostM.joint_sample, PMF.mem_support_map_iff]
  exact ⟨value, hValue, rfl⟩

/-! ## Exact comparison cost of partitioning -/

/-- The mathematical partition selected by the truthful linear-order comparison backend. -/
def linearPartition [LinearOrder alpha] (pivot : alpha) :
    (input : List alpha) -> PartitionResult input
  | [] => ⟨[], [], .refl []⟩
  | value :: rest =>
      let parts := linearPartition pivot rest
      if value <= pivot then
        {
          lower := value :: parts.lower
          upper := parts.upper
          perm := by simpa using parts.perm.cons value
        }
      else
        {
          lower := parts.lower
          upper := value :: parts.upper
          perm := by exact List.perm_middle.trans (parts.perm.cons value)
        }

@[simp] theorem linearPartition_lower [LinearOrder alpha]
    (pivot : alpha) (input : List alpha) :
    (linearPartition pivot input).lower =
      input.filter (fun value => decide (value <= pivot)) := by
  induction input with
  | nil => rfl
  | cons value rest ih =>
      by_cases hle : value <= pivot <;>
        simp [linearPartition, hle, ih]

@[simp] theorem linearPartition_upper [LinearOrder alpha]
    (pivot : alpha) (input : List alpha) :
    (linearPartition pivot input).upper =
      input.filter (fun value => decide (pivot < value)) := by
  induction input with
  | nil => rfl
  | cons value rest ih =>
      by_cases hle : value <= pivot
      · have hnot : ¬ pivot < value := not_lt_of_ge hle
        simp [linearPartition, hle, hnot, ih]
      · have hlt : pivot < value := lt_of_not_ge hle
        simp [linearPartition, hle, hlt, ih]

/-- Reindex list positions by the sorted rank of the selected value. Duplicate freedom makes
this a permutation of `Fin input.length`. -/
def pivotRankEquiv [LinearOrder alpha] (input : List alpha) (hNodup : input.Nodup) :
    Fin input.length ≃ Fin input.length :=
  (hNodup.getEquiv input).trans <|
    (Equiv.subtypeEquivRight fun _value => List.mem_toFinset.symm).trans <|
      (input.toFinset.orderIsoOfFin
        (List.toFinset_card_of_nodup hNodup)).symm.toEquiv

/-- In a finite linear order presented by `orderEmbOfFin`, exactly `i` elements precede
the element at rank `i`. -/
theorem card_filter_lt_orderEmb [LinearOrder alpha] (values : Finset alpha)
    {n : Nat} (hCard : values.card = n) (i : Fin n) :
    (values.filter fun value => value < values.orderEmbOfFin hCard i).card = i := by
  classical
  rw [← Fin.card_Iio i]
  apply Finset.card_bij
      (fun value hValue =>
        (values.orderIsoOfFin hCard).symm
          ⟨value, (Finset.mem_filter.mp hValue).1⟩)
  · intro value hValue
    rw [Finset.mem_Iio]
    have hLess := (Finset.mem_filter.mp hValue).2
    have hLessSubtype :
        (⟨value, (Finset.mem_filter.mp hValue).1⟩ : values) <
          values.orderIsoOfFin hCard i := hLess
    simpa using
      (values.orderIsoOfFin hCard).symm.lt_iff_lt.mpr hLessSubtype
  · intro left hLeft right hRight hEqual
    have hSubtype :
        (⟨left, (Finset.mem_filter.mp hLeft).1⟩ : values) =
          ⟨right, (Finset.mem_filter.mp hRight).1⟩ :=
      (values.orderIsoOfFin hCard).symm.injective hEqual
    exact congrArg Subtype.val hSubtype
  · intro rank hRank
    refine ⟨values.orderEmbOfFin hCard rank, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨values.orderEmbOfFin_mem hCard rank, ?_⟩
      have hLess : rank < i := Finset.mem_Iio.mp hRank
      have hLessSubtype :
          values.orderIsoOfFin hCard rank < values.orderIsoOfFin hCard i :=
        (values.orderIsoOfFin hCard).lt_iff_lt.mpr hLess
      exact hLessSubtype
    · change (values.orderIsoOfFin hCard).symm
          (values.orderIsoOfFin hCard rank) = rank
      exact (values.orderIsoOfFin hCard).symm_apply_apply rank

/-- The concrete lower partition has the sorted rank of the chosen pivot as its length. -/
theorem linearPartition_lower_length_eq_rank [LinearOrder alpha]
    (input : List alpha) (hNodup : input.Nodup) (index : Fin input.length) :
    (linearPartition (input.get index) (input.eraseIdx index)).lower.length =
      pivotRankEquiv input hNodup index := by
  classical
  let rank := pivotRankEquiv input hNodup index
  let values := input.toFinset
  have hCard : values.card = input.length :=
    List.toFinset_card_of_nodup hNodup
  have hPivotAtRank :
      values.orderEmbOfFin hCard rank = input.get index := by
    change ((values.orderIsoOfFin hCard
      ((values.orderIsoOfFin hCard).symm
        ⟨input.get index, List.mem_toFinset.mpr (List.get_mem input index)⟩) : values) :
          alpha) = input.get index
    rw [(values.orderIsoOfFin hCard).apply_symm_apply]
  have hRemainderNodup : (input.eraseIdx index).Nodup := hNodup.eraseIdx _
  have hFilterNodup :
      ((input.eraseIdx index).filter
        (fun value => decide (value <= input.get index))).Nodup :=
    hRemainderNodup.filter _
  have hFilteredFinset :
      ((input.eraseIdx index).filter
        (fun value => decide (value <= input.get index))).toFinset =
      input.toFinset.filter (fun value => value < input.get index) := by
    rw [← hNodup.erase_get index]
    ext value
    simp only [List.toFinset_filter, Finset.mem_filter, List.mem_toFinset,
      decide_eq_true_eq]
    rw [hNodup.mem_erase_iff]
    constructor
    · rintro ⟨⟨hne, hmem⟩, hle⟩
      exact ⟨hmem, lt_of_le_of_ne hle hne⟩
    · rintro ⟨hmem, hlt⟩
      exact ⟨⟨ne_of_lt hlt, hmem⟩, le_of_lt hlt⟩
  rw [linearPartition_lower]
  calc
    ((input.eraseIdx index).filter
        (fun value => decide (value <= input.get index))).length =
        ((input.eraseIdx index).filter
          (fun value => decide (value <= input.get index))).toFinset.card :=
      (List.toFinset_card_of_nodup hFilterNodup).symm
    _ = (input.toFinset.filter (fun value => value < input.get index)).card := by
      rw [hFilteredFinset]
    _ = (input.toFinset.filter
        (fun value => value < values.orderEmbOfFin hCard rank)).card := by
      rw [hPivotAtRank]
    _ = rank := card_filter_lt_orderEmb values hCard rank

/-- The complementary concrete upper partition has size `n - 1 - rank`. -/
theorem linearPartition_upper_length_eq [LinearOrder alpha]
    (input : List alpha) (hNodup : input.Nodup) (index : Fin input.length) :
    (linearPartition (input.get index) (input.eraseIdx index)).upper.length =
      input.length - 1 - pivotRankEquiv input hNodup index := by
  have hErase := List.length_eraseIdx_add_one index.isLt
  have hParts :=
    (linearPartition (input.get index) (input.eraseIdx index)).perm.length_eq
  have hLower := linearPartition_lower_length_eq_rank input hNodup index
  simp only [List.length_append] at hParts
  omega

/-- Under the comparison-only model, one partition pass costs exactly one comparison per
input element. This theorem is about the actual `RandCostM` interpretation, not an isolated
recurrence. -/
@[simp] theorem interpretWith_compareLE_comparisonOnly [LinearOrder alpha]
    (left right : alpha) :
    interpretWith SemanticBackend.uniformLinearOrder CostModel.comparisonOnly
        (compareLE left right) =
      RandCostM.deterministic (ULift.up (decide (left <= right))) 1 := by
  apply RandCostM.ext
  simp [interpretWith_compareLE, measuredHandler, semanticHandler,
    SemanticBackend.uniformLinearOrder, Sorting.ComparisonBackend.linearOrder,
    CostModel.operationCost, CostModel.comparisonOnly,
    Sorting.ComparisonCostModel.constant, RandCostM.sampleAtCost,
    RandCostM.sampleWithCost, RandCostM.deterministic, PMF.pure_map]

/-- Interpretation preserves the functorial map of the free program. -/
theorem interpretWith_map (backend : SemanticBackend alpha) (model : CostModel alpha)
    (f : beta -> gamma) (program : Program alpha beta) :
    interpretWith backend model (f <$> program) =
      f <$> interpretWith backend model program := by
  rw [map_eq_pure_bind, interpretWith_bind, map_eq_pure_bind]
  simp [interpretWith_pure]

@[simp] theorem expectedCost_interpretWith_map
    (backend : SemanticBackend alpha) (model : CostModel alpha)
    (f : beta -> gamma) (program : Program alpha beta) :
    (interpretWith backend model (f <$> program)).expectedCost =
      (interpretWith backend model program).expectedCost := by
  rw [interpretWith_map, RandCostM.expectedCost_map]

@[simp] theorem interpretWith_markBaseCase_comparisonOnly
    (backend : SemanticBackend alpha) (size : Nat) :
    interpretWith backend CostModel.comparisonOnly (markBaseCase size) =
      RandCostM.deterministic PUnit.unit 0 := by
  apply RandCostM.ext
  simp [interpretWith_markBaseCase, measuredHandler, semanticHandler,
    CostModel.operationCost, CostModel.comparisonOnly,
    RandCostM.sampleAtCost, RandCostM.sampleWithCost,
    RandCostM.deterministic, PMF.pure_map]

theorem interpret_partitionProgram_comparisonOnly [LinearOrder alpha]
    (pivot : alpha) (input : List alpha) :
    interpret CostModel.comparisonOnly (partitionProgram pivot input) =
      RandCostM.deterministic (linearPartition pivot input) input.length := by
  induction input with
  | nil =>
      simp [partitionProgram, linearPartition, interpret, interpretWith]
  | cons value rest ih =>
      change interpretWith SemanticBackend.uniformLinearOrder CostModel.comparisonOnly
          (partitionProgram pivot (value :: rest)) = _
      change interpretWith SemanticBackend.uniformLinearOrder CostModel.comparisonOnly
          (partitionProgram pivot rest) = _ at ih
      rw [partitionProgram, interpretWith_bind,
        interpretWith_compareLE_comparisonOnly]
      apply RandCostM.ext
      by_cases hle : value <= pivot <;>
        simp [RandCostM.deterministic, ih, interpretWith_bind,
          interpretWith_pure, linearPartition, hle, Nat.add_comm]

/-- Exact comparison count of the fixed sorting network used for sizes at most three. -/
def smallComparisonCost : Nat -> Nat
  | 2 => 1
  | 3 => 3
  | _ => 0

/-- The interpreted base-case sorting network has its advertised exact comparison cost. -/
theorem expectedCost_sortSmallProgram_comparisonOnly [LinearOrder alpha]
    (input : List alpha) (hLength : input.length <= 3) :
    (interpret CostModel.comparisonOnly (sortSmallProgram input)).expectedCost =
      smallComparisonCost input.length := by
  rcases input with _ | ⟨first, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, rest⟩⟩⟩⟩
  · norm_num [smallComparisonCost]
    unfold interpret
    change (interpretWith (SemanticBackend.uniformLinearOrder (alpha := alpha))
      CostModel.comparisonOnly (sortSmallProgram ([] : List alpha))).expectedCost =
        (0 : ENNReal)
    rw [sortSmallProgram, interpretWith_bind,
      interpretWith_markBaseCase_comparisonOnly]
    simp [RandCostM.expectedCost_bind_split]
  · norm_num [smallComparisonCost]
    unfold interpret
    change (interpretWith (SemanticBackend.uniformLinearOrder (alpha := alpha))
      CostModel.comparisonOnly (sortSmallProgram [first])).expectedCost =
        (0 : ENNReal)
    rw [sortSmallProgram, interpretWith_bind,
      interpretWith_markBaseCase_comparisonOnly]
    simp [RandCostM.expectedCost_bind_split]
  · norm_num [smallComparisonCost]
    unfold interpret
    change (interpretWith (SemanticBackend.uniformLinearOrder (alpha := alpha))
      CostModel.comparisonOnly
        (sortSmallProgram [first, second])).expectedCost = (1 : ENNReal)
    rw [sortSmallProgram, interpretWith_bind,
      interpretWith_markBaseCase_comparisonOnly]
    simp [RandCostM.expectedCost_bind_split,
      interpretWith_map, CostModel.comparisonOnly,
      Sorting.ComparisonCostModel.constant]
  · norm_num [smallComparisonCost]
    unfold interpret
    change (interpretWith (SemanticBackend.uniformLinearOrder (alpha := alpha))
      CostModel.comparisonOnly
        (sortSmallProgram [first, second, third])).expectedCost = (3 : ENNReal)
    rw [sortSmallProgram, interpretWith_bind,
      interpretWith_markBaseCase_comparisonOnly]
    simp [RandCostM.expectedCost_bind_split, interpretWith_bind,
      interpretWith_map, CostModel.comparisonOnly,
      Sorting.ComparisonCostModel.constant]
    norm_num
  · simp only [List.length_cons] at hLength
    omega

/-! ## A run-derived uniform-pivot recurrence -/

/-- The deterministic partition selected after choosing a concrete pivot position. -/
def partitionAt [LinearOrder alpha] (input : List alpha) (index : Fin input.length) :
    PartitionResult (input.eraseIdx index) :=
  linearPartition (input.get index) (input.eraseIdx index)

/-- The lower recursive input selected by one pivot position. -/
def lowerSubproblem [LinearOrder alpha] (input : List alpha)
    (index : Fin input.length) : List alpha :=
  (partitionAt input index).lower

/-- The upper recursive input selected by one pivot position. -/
def upperSubproblem [LinearOrder alpha] (input : List alpha)
    (index : Fin input.length) : List alpha :=
  (partitionAt input index).upper

theorem lowerSubproblem_nodup [LinearOrder alpha]
    (input : List alpha) (hNodup : input.Nodup) (index : Fin input.length) :
    (lowerSubproblem input index).Nodup := by
  unfold lowerSubproblem partitionAt
  rw [linearPartition_lower]
  exact (hNodup.eraseIdx _).filter _

theorem upperSubproblem_nodup [LinearOrder alpha]
    (input : List alpha) (hNodup : input.Nodup) (index : Fin input.length) :
    (upperSubproblem input index).Nodup := by
  unfold upperSubproblem partitionAt
  rw [linearPartition_upper]
  exact (hNodup.eraseIdx _).filter _

@[simp] theorem lowerSubproblem_length [LinearOrder alpha]
    (input : List alpha) (hNodup : input.Nodup) (index : Fin input.length) :
    (lowerSubproblem input index).length = pivotRankEquiv input hNodup index := by
  exact linearPartition_lower_length_eq_rank input hNodup index

@[simp] theorem upperSubproblem_length [LinearOrder alpha]
    (input : List alpha) (hNodup : input.Nodup) (index : Fin input.length) :
    (upperSubproblem input index).length =
      input.length - 1 - pivotRankEquiv input hNodup index := by
  exact linearPartition_upper_length_eq input hNodup index

/-- The free-program continuation after a pivot position has been supplied. -/
def quicksortContinuation [LinearOrder alpha] (input : List alpha)
    (index : Fin input.length) : Program alpha (List alpha) := do
  let pivot := input.get index
  let remainder := input.eraseIdx index
  let parts <- partitionProgram pivot remainder
  let sortedLower <- quicksortProgram parts.lower
  let sortedUpper <- quicksortProgram parts.upper
  pure (sortedLower ++ pivot :: sortedUpper)

/-- Supplying a fixed pivot to the actual interpreter costs one partition pass followed by
the costs of the two actual recursive calls. -/
theorem expectedCost_quicksortContinuation [LinearOrder alpha]
    (input : List alpha) (index : Fin input.length) :
    (interpret CostModel.comparisonOnly
      (quicksortContinuation input index)).expectedCost =
      ((input.length - 1 : Nat) : ENNReal) +
        (quicksort (lowerSubproblem input index)).expectedCost +
        (quicksort (upperSubproblem input index)).expectedCost := by
  have hPartition := interpret_partitionProgram_comparisonOnly
    (input.get index) (input.eraseIdx index)
  have hErase : (input.eraseIdx index).length = input.length - 1 :=
    List.length_eraseIdx_of_lt index.isLt
  unfold interpret at hPartition
  unfold quicksortContinuation interpret
  rw [interpretWith_bind, hPartition]
  simp [RandCostM.expectedCost_bind_split, interpretWith_bind,
    quicksort, interpret, lowerSubproblem, upperSubproblem, partitionAt,
    hErase, add_assoc]

/-- Choosing a pivot under the source backend is exactly zero-cost uniform sampling. -/
@[simp] theorem interpretWith_choosePivotIndex_comparisonOnly [LinearOrder alpha]
    (tailLength : Nat) :
    interpretWith (SemanticBackend.uniformLinearOrder (alpha := alpha))
        (CostModel.comparisonOnly (alpha := alpha))
        (choosePivotIndex tailLength) =
      (RandCostM.sample
        (PMF.uniformOfFintype (ULift (Fin (tailLength + 1)))) :
          RandCostM Nat (ULift (Fin (tailLength + 1)))) := by
  rw [interpretWith_choosePivotIndex]
  rfl

/-- Exact expected-cost equation obtained by unfolding the actual uniform-pivot runner once. -/
theorem expectedCost_quicksort_step [LinearOrder alpha]
    (first : alpha) (rest : List alpha)
    (hLong : ¬(first :: rest).length <= 3) :
    (quicksort (first :: rest)).expectedCost =
      (((first :: rest).length : Nat) : ENNReal)⁻¹ *
        ∑ index : Fin (first :: rest).length,
          (interpret CostModel.comparisonOnly
            (quicksortContinuation (first :: rest) index)).expectedCost := by
  unfold quicksort interpret
  rw [quicksortProgram, if_neg hLong, interpretWith_bind,
    interpretWith_choosePivotIndex_comparisonOnly,
    RandCostM.expectedCost_bind_split]
  simp only [RandCostM.expectedCost_sample, zero_add, RandCostM.ret_sample]
  rw [ResourceAware.Program.weightedSum_uniformOfFintype]
  simp only [Fintype.card_ulift, Fintype.card_fin]
  congr 1
  exact Fintype.sum_equiv Equiv.ulift _ _ fun sampled => by
    rfl

/-- The preceding run-derived equation with the exact partition and recursive costs exposed. -/
theorem expectedCost_quicksort_recurrence [LinearOrder alpha]
    (first : alpha) (rest : List alpha)
    (hLong : ¬(first :: rest).length <= 3) :
    (quicksort (first :: rest)).expectedCost =
      (((first :: rest).length : Nat) : ENNReal)⁻¹ *
        ∑ index : Fin (first :: rest).length,
          ((((first :: rest).length - 1 : Nat) : ENNReal) +
            (quicksort
              (lowerSubproblem (alpha := alpha) (first :: rest)
                (index : Fin (first :: rest).length))).expectedCost +
            (quicksort
              (upperSubproblem (alpha := alpha) (first :: rest)
                (index : Fin (first :: rest).length))).expectedCost) := by
  rw [expectedCost_quicksort_step first rest hLong]
  apply congrArg fun total =>
    (((first :: rest).length : Nat) : ENNReal)⁻¹ * total
  apply Finset.sum_congr rfl
  intro index _
  exact expectedCost_quicksortContinuation (first :: rest) index

/-! ## A harmonic comparison envelope -/

/-- A convenient real-valued upper envelope for the standard uniform-pivot recurrence. -/
def expectedComparisonEnvelope (n : Nat) : Real :=
  3 * (n + 1) * (harmonic n : Real)

theorem harmonic_nonneg_real (n : Nat) : (0 : Real) <= (harmonic n : Real) := by
  have hHarmonicRat : (0 : Rat) <= harmonic n := by
    unfold harmonic
    exact Finset.sum_nonneg fun i _ => inv_nonneg.mpr (by positivity)
  exact_mod_cast hHarmonicRat

@[simp] theorem expectedComparisonEnvelope_zero : expectedComparisonEnvelope 0 = 0 := by
  simp [expectedComparisonEnvelope]

theorem expectedComparisonEnvelope_nonneg (n : Nat) :
    0 <= expectedComparisonEnvelope n := by
  have hHarmonic := harmonic_nonneg_real n
  unfold expectedComparisonEnvelope
  positivity

/-- The real-valued n-times-one-plus-log-n benchmark used for the asymptotic statement. -/
def nLogN (n : Nat) : Real :=
  n * (1 + Real.log n)

theorem nLogN_nonneg {n : Nat} (hn : 1 <= n) : 0 <= nLogN n := by
  unfold nLogN
  positivity

/-- The nonnegative recurrence envelope is asymptotically bounded by the conventional
`n * log n` benchmark. -/
theorem nLogN_isBigO_mul_log :
    nLogN =O[atTop] (fun n : Nat => (n : Real) * Real.log n) := by
  refine IsBigO.of_bound 2
    (Filter.eventually_atTop.2 ⟨3, fun n hn => ?_⟩)
  have hnReal : (3 : Real) ≤ n := by exact_mod_cast hn
  have hLogThree : (1 : Real) ≤ Real.log 3 := by
    linarith [Real.log_three_gt_d9]
  have hLog : (1 : Real) ≤ Real.log n :=
    hLogThree.trans (Real.log_le_log (by norm_num) hnReal)
  have hnNonneg : (0 : Real) ≤ n := by positivity
  have hRightNonneg : (0 : Real) ≤ (n : Real) * Real.log n := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (nLogN_nonneg (by omega))]
  rw [Real.norm_eq_abs, abs_of_nonneg hRightNonneg]
  unfold nLogN
  nlinarith

/-- The harmonic comparison envelope grows in O(n log n). -/
theorem expectedComparisonEnvelope_isBigO :
    expectedComparisonEnvelope =O[atTop] nLogN := by
  refine IsBigO.of_bound 6 (Filter.eventually_atTop.2 ⟨1, ?_⟩)
  intro n hn
  have hnReal : (1 : Real) <= n := by exact_mod_cast hn
  have hLog : 0 <= 1 + Real.log n := by positivity
  have hHarmonic : (harmonic n : Real) <= 1 + Real.log n :=
    harmonic_le_one_add_log n
  have hHarmonicNonneg := harmonic_nonneg_real n
  rw [Real.norm_eq_abs, abs_of_nonneg (expectedComparisonEnvelope_nonneg n)]
  rw [Real.norm_eq_abs, abs_of_nonneg (nLogN_nonneg hn)]
  change expectedComparisonEnvelope n <= 6 * nLogN n
  calc
    expectedComparisonEnvelope n
        <= 3 * (2 * (n : Real)) * (1 + Real.log n) := by
          unfold expectedComparisonEnvelope
          gcongr
          linarith
    _ = 6 * nLogN n := by
          unfold nLogN
          ring

/-! ## Solving the uniform-pivot recurrence -/

/-- The weighted harmonic sum that appears after averaging the two recursive subproblems. -/
theorem sum_weighted_harmonic (n : Nat) :
    ∑ k ∈ Finset.range n, ((k + 1 : Nat) : Real) * (harmonic k : Real) =
      (n : Real) * (n + 1) / 2 * (harmonic n : Real) -
        (n : Real) * (n + 3) / 4 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, harmonic_succ]
      push_cast
      have hn : (n : Real) + 1 ≠ 0 := by positivity
      field_simp
      ring

/-- The sum of the harmonic envelopes below `n`. -/
theorem sum_expectedComparisonEnvelope (n : Nat) :
    ∑ k ∈ Finset.range n, expectedComparisonEnvelope k =
      3 * ((n : Real) * (n + 1) / 2 * (harmonic n : Real) -
        (n : Real) * (n + 3) / 4) := by
  calc
    ∑ k ∈ Finset.range n, expectedComparisonEnvelope k =
        3 * ∑ k ∈ Finset.range n,
          ((k + 1 : Nat) : Real) * (harmonic k : Real) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      unfold expectedComparisonEnvelope
      push_cast
      ring
    _ = 3 * ((n : Real) * (n + 1) / 2 * (harmonic n : Real) -
        (n : Real) * (n + 3) / 4) := by
      rw [sum_weighted_harmonic]

/-- The harmonic envelope is a supersolution of the uniform-pivot comparison recurrence. -/
theorem expectedComparisonEnvelope_recurrence (n : Nat) (hLong : 4 <= n) :
    (((n - 1 : Nat) : Real) +
        (n : Real)⁻¹ *
          ∑ k ∈ Finset.range n,
            (expectedComparisonEnvelope k +
              expectedComparisonEnvelope (n - 1 - k))) <=
      expectedComparisonEnvelope n := by
  have hnPos : 0 < n := by omega
  have hnOne : 1 <= n := by omega
  have hnRealPos : (0 : Real) < n := by exact_mod_cast hnPos
  rw [Finset.sum_add_distrib,
    Finset.sum_range_reflect expectedComparisonEnvelope n,
    sum_expectedComparisonEnvelope,
    Nat.cast_sub hnOne]
  norm_num
  calc
    (n : Real) - 1 + (n : Real)⁻¹ *
        (3 * ((n : Real) * (n + 1) / 2 * (harmonic n : Real) -
            (n : Real) * (n + 3) / 4) +
          3 * ((n : Real) * (n + 1) / 2 * (harmonic n : Real) -
            (n : Real) * (n + 3) / 4)) =
      expectedComparisonEnvelope n - ((n : Real) / 2 + 11 / 2) := by
        unfold expectedComparisonEnvelope
        field_simp
        ring
    _ <= expectedComparisonEnvelope n := by
      have : (0 : Real) <= (n : Real) / 2 + 11 / 2 := by positivity
      linarith

/-- The same harmonic envelope in the codomain used by `RandCostM.ecwp`. -/
def expectedComparisonEnvelopeENN (n : Nat) : ENNReal :=
  ENNReal.ofReal (expectedComparisonEnvelope n)

@[simp] theorem expectedComparisonEnvelopeENN_zero :
    expectedComparisonEnvelopeENN 0 = 0 := by
  simp [expectedComparisonEnvelopeENN]

/-- `ENNReal` form of the recurrence supersolution, indexed by `Finset.range`. -/
theorem expectedComparisonEnvelopeENN_recurrence_range
    (n : Nat) (hLong : 4 <= n) :
    (((n - 1 : Nat) : ENNReal) +
        (n : ENNReal)⁻¹ *
          ∑ k ∈ Finset.range n,
            (expectedComparisonEnvelopeENN k +
              expectedComparisonEnvelopeENN (n - 1 - k))) <=
      expectedComparisonEnvelopeENN n := by
  have hnPos : 0 < n := by omega
  have hnRealPos : (0 : Real) < n := by exact_mod_cast hnPos
  have hTermNonneg : ∀ k ∈ Finset.range n,
      (0 : Real) <= expectedComparisonEnvelope k +
        expectedComparisonEnvelope (n - 1 - k) := by
    intro k _
    exact add_nonneg (expectedComparisonEnvelope_nonneg k)
      (expectedComparisonEnvelope_nonneg (n - 1 - k))
  have hSumNonneg :
      (0 : Real) <= ∑ k ∈ Finset.range n,
        (expectedComparisonEnvelope k +
          expectedComparisonEnvelope (n - 1 - k)) :=
    Finset.sum_nonneg hTermNonneg
  have hInvNonneg : (0 : Real) <= (n : Real)⁻¹ := inv_nonneg.mpr (le_of_lt hnRealPos)
  have hLift := ENNReal.ofReal_le_ofReal
    (expectedComparisonEnvelope_recurrence n hLong)
  rw [ENNReal.ofReal_add (by positivity)
      (mul_nonneg hInvNonneg hSumNonneg),
    ENNReal.ofReal_mul hInvNonneg,
    ENNReal.ofReal_inv_of_pos hnRealPos,
    ENNReal.ofReal_sum_of_nonneg hTermNonneg] at hLift
  have hOfTerm : ∀ k,
      ENNReal.ofReal
          (expectedComparisonEnvelope k +
            expectedComparisonEnvelope (n - 1 - k)) =
        expectedComparisonEnvelopeENN k +
          expectedComparisonEnvelopeENN (n - 1 - k) := by
    intro k
    rw [ENNReal.ofReal_add (expectedComparisonEnvelope_nonneg k)
      (expectedComparisonEnvelope_nonneg (n - 1 - k))]
    rfl
  simp_rw [hOfTerm] at hLift
  simpa [expectedComparisonEnvelopeENN] using hLift

/-- `Fin n` form used by the interpreter's uniform-pivot recurrence. -/
theorem expectedComparisonEnvelopeENN_recurrence
    (n : Nat) (hLong : 4 <= n) :
    (((n - 1 : Nat) : ENNReal) +
        (n : ENNReal)⁻¹ *
          ∑ index : Fin n,
            (expectedComparisonEnvelopeENN index.val +
              expectedComparisonEnvelopeENN (n - 1 - index.val))) <=
      expectedComparisonEnvelopeENN n := by
  have hSum :
      (∑ index : Fin n,
          (expectedComparisonEnvelopeENN index.val +
            expectedComparisonEnvelopeENN (n - 1 - index.val))) =
        ∑ k ∈ Finset.range n,
          (expectedComparisonEnvelopeENN k +
            expectedComparisonEnvelopeENN (n - 1 - k)) :=
    Fin.sum_univ_eq_sum_range
      (fun k => expectedComparisonEnvelopeENN k +
        expectedComparisonEnvelopeENN (n - 1 - k)) n
  rw [hSum]
  exact expectedComparisonEnvelopeENN_recurrence_range n hLong

/-- The recurrence in the exact shape emitted by the runner, with the partition charge inside
the uniform average. -/
theorem expectedComparisonEnvelopeENN_recurrence_averaged
    (n : Nat) (hLong : 4 <= n) :
    (n : ENNReal)⁻¹ *
        ∑ index : Fin n,
          ((((n - 1 : Nat) : ENNReal) +
              expectedComparisonEnvelopeENN index.val) +
            expectedComparisonEnvelopeENN (n - 1 - index.val)) <=
      expectedComparisonEnvelopeENN n := by
  have hnZero : (n : ENNReal) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  have hnTop : (n : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top n
  calc
    (n : ENNReal)⁻¹ *
        ∑ index : Fin n,
          ((((n - 1 : Nat) : ENNReal) +
              expectedComparisonEnvelopeENN index.val) +
            expectedComparisonEnvelopeENN (n - 1 - index.val)) =
      (n : ENNReal)⁻¹ *
        (((n : ENNReal) * ((n - 1 : Nat) : ENNReal)) +
          ∑ index : Fin n,
            (expectedComparisonEnvelopeENN index.val +
              expectedComparisonEnvelopeENN (n - 1 - index.val))) := by
        simp_rw [add_assoc]
        rw [Finset.sum_add_distrib]
        simp [nsmul_eq_mul]
    _ = (((n - 1 : Nat) : ENNReal) +
        (n : ENNReal)⁻¹ *
          ∑ index : Fin n,
            (expectedComparisonEnvelopeENN index.val +
              expectedComparisonEnvelopeENN (n - 1 - index.val))) := by
      rw [mul_add, ENNReal.inv_mul_cancel_left hnZero hnTop]
    _ <= expectedComparisonEnvelopeENN n :=
      expectedComparisonEnvelopeENN_recurrence n hLong

/-- The fixed base-case network lies below the common harmonic envelope. -/
theorem smallComparisonCost_le_expectedComparisonEnvelopeENN
    (n : Nat) (hSmall : n <= 3) :
    (smallComparisonCost n : ENNReal) <= expectedComparisonEnvelopeENN n := by
  interval_cases n <;>
    norm_num [smallComparisonCost, expectedComparisonEnvelopeENN,
      expectedComparisonEnvelope, harmonic, Finset.sum_range_succ]

theorem expectedCost_quicksort_of_length_le_three [LinearOrder alpha]
    (input : List alpha) (hSmall : input.length <= 3) :
    (quicksort input).expectedCost = smallComparisonCost input.length := by
  unfold quicksort
  cases input with
  | nil =>
      rw [quicksortProgram]
      exact expectedCost_sortSmallProgram_comparisonOnly [] hSmall
  | cons first rest =>
      rw [quicksortProgram, if_pos hSmall]
      exact expectedCost_sortSmallProgram_comparisonOnly (first :: rest) hSmall

/-- Approved extension (expected comparisons): the actual uniform `RandCostM` runner has
expected comparison cost at most the harmonic envelope on every duplicate-free input. -/
theorem quicksort_expectedComparisonCost_le [LinearOrder alpha]
    (input : List alpha) (hNodup : input.Nodup) :
    (quicksort input).expectedCost <=
      expectedComparisonEnvelopeENN input.length := by
  induction hInputLength : input.length using Nat.strong_induction_on
      generalizing input with
  | h n ih =>
      subst hInputLength
      by_cases hSmall : input.length <= 3
      · rw [expectedCost_quicksort_of_length_le_three input hSmall]
        exact smallComparisonCost_le_expectedComparisonEnvelopeENN
          input.length hSmall
      · cases input with
        | nil => simp at hSmall
        | cons first rest =>
            have hLong : 4 <= (first :: rest).length := by omega
            rw [expectedCost_quicksort_recurrence first rest hSmall]
            let source := first :: rest
            let c : ENNReal := ((source.length - 1 : Nat) : ENNReal)
            have hSumBound :
                (∑ index : Fin source.length,
                    ((c +
                        (quicksort (lowerSubproblem source index)).expectedCost) +
                      (quicksort (upperSubproblem source index)).expectedCost)) <=
                  ∑ index : Fin source.length,
                    ((c + expectedComparisonEnvelopeENN
                        (lowerSubproblem source index).length) +
                      expectedComparisonEnvelopeENN
                        (upperSubproblem source index).length) := by
              apply Finset.sum_le_sum
              intro index _
              have hLowerShort : (lowerSubproblem source index).length < source.length := by
                rw [lowerSubproblem_length source hNodup index]
                exact (pivotRankEquiv source hNodup index).isLt
              have hUpperShort : (upperSubproblem source index).length < source.length := by
                rw [upperSubproblem_length source hNodup index]
                omega
              have hLowerBound := ih (lowerSubproblem source index).length
                hLowerShort (lowerSubproblem source index)
                (lowerSubproblem_nodup source hNodup index) rfl
              have hUpperBound := ih (upperSubproblem source index).length
                hUpperShort (upperSubproblem source index)
                (upperSubproblem_nodup source hNodup index) rfl
              exact add_le_add (add_le_add_right hLowerBound c) hUpperBound
            refine le_trans (mul_le_mul_right hSumBound (source.length : ENNReal)⁻¹) ?_
            have hReindex :
                (∑ index : Fin source.length,
                    ((c + expectedComparisonEnvelopeENN
                        (lowerSubproblem source index).length) +
                      expectedComparisonEnvelopeENN
                        (upperSubproblem source index).length)) =
                  ∑ rank : Fin source.length,
                    ((c + expectedComparisonEnvelopeENN rank.val) +
                      expectedComparisonEnvelopeENN
                        (source.length - 1 - rank.val)) := by
              exact Fintype.sum_equiv (pivotRankEquiv source hNodup) _ _
                fun index => by
                  rw [lowerSubproblem_length source hNodup index,
                    upperSubproblem_length source hNodup index]
            rw [hReindex]
            exact expectedComparisonEnvelopeENN_recurrence_averaged
              source.length hLong

/-- The requested `ecwp` statement; zero post-cost observes exactly the expected comparison
count proved above. -/
theorem quicksort_ecwp_comparisons_le [LinearOrder alpha]
    (input : List alpha) (hNodup : input.Nodup) :
    RandCostM.ecwp (quicksort input) (fun _ => 0) <=
      expectedComparisonEnvelopeENN input.length := by
  simpa using quicksort_expectedComparisonCost_le input hNodup

/-- A size-indexed real-valued observation of the actual runner, using `List.range n` as a
canonical duplicate-free input. The pointwise theorem above shows that the same envelope applies
to every duplicate-free input of that size. -/
def expectedComparisonsBySize (n : Nat) : Real :=
  (quicksort (List.range n)).expectedCost.toReal

theorem expectedComparisonsBySize_nonneg (n : Nat) :
    0 <= expectedComparisonsBySize n :=
  ENNReal.toReal_nonneg

theorem expectedComparisonsBySize_le (n : Nat) :
    expectedComparisonsBySize n <= expectedComparisonEnvelope n := by
  have hBound := quicksort_expectedComparisonCost_le
    (List.range n) List.nodup_range
  have hBound' :
      (quicksort (List.range n)).expectedCost <=
        expectedComparisonEnvelopeENN n := by
    simpa using hBound
  have hEnvelopeFinite : expectedComparisonEnvelopeENN n ≠ ⊤ := by
    simp [expectedComparisonEnvelopeENN]
  have hCostFinite : (quicksort (List.range n)).expectedCost ≠ ⊤ :=
    ne_top_of_le_ne_top hEnvelopeFinite hBound'
  have hToReal :=
    (ENNReal.toReal_le_toReal hCostFinite hEnvelopeFinite).2 hBound'
  simpa [expectedComparisonsBySize, expectedComparisonEnvelopeENN,
    ENNReal.toReal_ofReal (expectedComparisonEnvelope_nonneg n)] using hToReal

/-- Approved extension (expected comparisons): the `ecwp` expected comparison count of the
actual uniform runner is `O(n log n)`. -/
theorem expectedComparisonsBySize_isBigO :
    expectedComparisonsBySize =O[atTop]
      (fun n : Nat => (n : Real) * Real.log n) := by
  have hToEnvelope :
      expectedComparisonsBySize =O[atTop] expectedComparisonEnvelope := by
    refine IsBigO.of_bound 1 (Filter.Eventually.of_forall fun n => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (expectedComparisonsBySize_nonneg n)]
    rw [Real.norm_eq_abs, abs_of_nonneg (expectedComparisonEnvelope_nonneg n)]
    simpa using expectedComparisonsBySize_le n
  exact (hToEnvelope.trans expectedComparisonEnvelope_isBigO).trans
    nLogN_isBigO_mul_log

/-! ## Worst-case comparison branches -/

/-- Splitting a set cannot create more unordered pairs than the original set. -/
theorem choose_two_add (left right : Nat) :
    (left + right).choose 2 =
      left.choose 2 + right.choose 2 + left * right := by
  induction right with
  | zero => simp
  | succ right ih =>
      rw [Nat.add_succ, Nat.choose_succ_succ, Nat.choose_one_right,
        Nat.choose_succ_succ, Nat.choose_one_right, ih]
      ring

/-- One partition charge plus the two subproblem pair counts is at most `n.choose 2`. -/
theorem comparison_split_quadratic_bound (n k : Nat) (hk : k < n) :
    n - 1 + k.choose 2 + (n - 1 - k).choose 2 <= n.choose 2 := by
  cases n with
  | zero => omega
  | succ n =>
      have hkn : k <= n := by omega
      have hAdd := choose_two_add k (n - k)
      have hSum : k + (n - k) = n := Nat.add_sub_of_le hkn
      rw [hSum] at hAdd
      have hPairs : k.choose 2 + (n - k).choose 2 <= n.choose 2 := by
        calc
          k.choose 2 + (n - k).choose 2 <=
              k.choose 2 + (n - k).choose 2 + k * (n - k) := by omega
          _ = n.choose 2 := hAdd.symm
      simp only [Nat.succ_sub_one, Nat.choose_succ_succ, Nat.choose_one_right]
      simpa [add_assoc] using Nat.add_le_add_left hPairs n

theorem smallComparisonCost_eq_choose_two (n : Nat) (hSmall : n <= 3) :
    smallComparisonCost n = n.choose 2 := by
  interval_cases n <;> norm_num [smallComparisonCost, Nat.choose]

/-- Every branch of the fixed base-case network has its advertised comparison count. -/
theorem sortSmallProgram_joint_cost_eq [LinearOrder alpha]
    (input output : List alpha) (cost : Nat) (hSmall : input.length <= 3)
    (hMem : (output, cost) ∈
      (interpret CostModel.comparisonOnly (sortSmallProgram input)).joint.support) :
    cost = smallComparisonCost input.length := by
  rcases input with _ | ⟨first, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, rest⟩⟩⟩⟩
  · simp only [interpret, sortSmallProgram, bind_pure_comp, interpretWith_map,
      interpretWith_markBaseCase, RandCostM.joint_map, measuredHandler_joint,
      CostModel.operationCost_baseCase, CostModel.comparisonOnly_baseCase,
      semanticHandler_baseCase, PMF.pure_map, PMF.support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, smallComparisonCost, List.length_nil] at hMem ⊢
    exact hMem.2
  · simp only [interpret, sortSmallProgram, bind_pure_comp, interpretWith_map,
      interpretWith_markBaseCase, RandCostM.joint_map, measuredHandler_joint,
      CostModel.operationCost_baseCase, CostModel.comparisonOnly_baseCase,
      semanticHandler_baseCase, PMF.pure_map, PMF.support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, smallComparisonCost, List.length_cons, List.length_nil,
      zero_add] at hMem ⊢
    exact hMem.2
  · simp only [interpret, CostModel.comparisonOnly, Sorting.ComparisonCostModel.constant,
      sortSmallProgram, bind_pure_comp, interpretWith_bind, interpretWith_markBaseCase,
      interpretWith_map, interpretWith_compareSwap, RandCostM.deterministic,
      RandCostM.joint_bind, measuredHandler_joint, CostModel.operationCost_baseCase,
      semanticHandler_baseCase, PMF.pure_map, RandCostM.joint_map, PMF.pure_bind,
      zero_add, PMF.support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
      smallComparisonCost, List.length_cons, List.length_nil, Nat.reduceAdd] at hMem ⊢
    exact hMem.2
  · simp only [interpret, CostModel.comparisonOnly, Sorting.ComparisonCostModel.constant,
      sortSmallProgram, bind_pure_comp, interpretWith_bind, interpretWith_markBaseCase,
      interpretWith_compareSwap, RandCostM.deterministic, interpretWith_map,
      RandCostM.joint_bind, measuredHandler_joint, CostModel.operationCost_baseCase,
      semanticHandler_baseCase, PMF.pure_map, RandCostM.joint_map, PMF.pure_bind,
      Nat.reduceAdd, zero_add, PMF.support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
      smallComparisonCost, List.length_cons, List.length_nil] at hMem ⊢
    omega
  · simp only [List.length_cons] at hSmall
    omega

/-- A supported fixed-pivot continuation branch decomposes into its exact partition charge and
the two supported recursive branch costs. -/
theorem quicksortContinuation_joint_cost_decompose [LinearOrder alpha]
    (input : List alpha) (index : Fin input.length)
    (output : List alpha) (cost : Nat)
    (hMem : (output, cost) ∈
      (interpret CostModel.comparisonOnly
        (quicksortContinuation input index)).joint.support) :
    ∃ lowerOutput lowerCost upperOutput upperCost,
      (lowerOutput, lowerCost) ∈
          (quicksort (lowerSubproblem input index)).joint.support ∧
      (upperOutput, upperCost) ∈
          (quicksort (upperSubproblem input index)).joint.support ∧
      cost = input.length - 1 + lowerCost + upperCost := by
  have hPartition := interpret_partitionProgram_comparisonOnly
    (input.get index) (input.eraseIdx index)
  unfold interpret at hPartition
  change (output, cost) ∈
    (interpretWith SemanticBackend.uniformLinearOrder CostModel.comparisonOnly
      (quicksortContinuation input index)).joint.support at hMem
  unfold quicksortContinuation at hMem
  rw [interpretWith_bind, hPartition] at hMem
  obtain ⟨parts, partitionCost, afterPartitionCost,
      hParts, hAfterPartition, hCost⟩ :=
    (mem_joint_support_bind_iff _ _ _ _).mp hMem
  rw [RandCostM.joint_deterministic, PMF.mem_support_pure_iff] at hParts
  injection hParts with hPartsResult hPartsCost
  subst parts
  subst partitionCost
  rw [interpretWith_bind] at hAfterPartition
  obtain ⟨lowerOutput, lowerCost, afterLowerCost,
      hLower, hAfterLower, hAfterPartitionCost⟩ :=
    (mem_joint_support_bind_iff _ _ _ _).mp hAfterPartition
  rw [interpretWith_bind] at hAfterLower
  obtain ⟨upperOutput, upperCost, finalCost,
      hUpper, hFinal, hAfterLowerCost⟩ :=
    (mem_joint_support_bind_iff _ _ _ _).mp hAfterLower
  rw [interpretWith_pure] at hFinal
  rw [RandCostM.joint_pure, PMF.mem_support_pure_iff] at hFinal
  have hFinalCost := congrArg Prod.snd hFinal
  have hErase : (input.eraseIdx index).length = input.length - 1 :=
    List.length_eraseIdx_of_lt index.isLt
  refine ⟨lowerOutput, lowerCost, upperOutput, upperCost, ?_, ?_, ?_⟩
  · simpa [quicksort, interpret, lowerSubproblem, partitionAt] using hLower
  · simpa [quicksort, interpret, upperSubproblem, partitionAt] using hUpper
  · omega

/-- Supported recursive branches assemble into a supported fixed-pivot continuation branch,
with the partition comparisons and both recursive costs added exactly. -/
theorem quicksortContinuation_joint_support_of_recursive [LinearOrder alpha]
    (input : List alpha) (index : Fin input.length)
    (lowerOutput upperOutput : List alpha) (lowerCost upperCost : Nat)
    (hLower : (lowerOutput, lowerCost) ∈
      (quicksort (lowerSubproblem input index)).joint.support)
    (hUpper : (upperOutput, upperCost) ∈
      (quicksort (upperSubproblem input index)).joint.support) :
    (lowerOutput ++ input.get index :: upperOutput,
        input.length - 1 + lowerCost + upperCost) ∈
      (interpret CostModel.comparisonOnly
        (quicksortContinuation input index)).joint.support := by
  have hPartition := interpret_partitionProgram_comparisonOnly
    (input.get index) (input.eraseIdx index)
  unfold interpret at hPartition
  change (lowerOutput ++ input.get index :: upperOutput,
      input.length - 1 + lowerCost + upperCost) ∈
    (interpretWith SemanticBackend.uniformLinearOrder CostModel.comparisonOnly
      (quicksortContinuation input index)).joint.support
  unfold quicksortContinuation
  rw [interpretWith_bind, hPartition]
  refine (mem_joint_support_bind_iff _ _ _ _).mpr ?_
  refine ⟨linearPartition (input.get index) (input.eraseIdx index),
    (input.eraseIdx index).length, lowerCost + upperCost, ?_, ?_, ?_⟩
  · simp [RandCostM.deterministic]
  · rw [interpretWith_bind]
    refine (mem_joint_support_bind_iff _ _ _ _).mpr ?_
    refine ⟨lowerOutput, lowerCost, upperCost, ?_, ?_, rfl⟩
    · simpa [quicksort, interpret, lowerSubproblem, partitionAt] using hLower
    · rw [interpretWith_bind]
      refine (mem_joint_support_bind_iff _ _ _ _).mpr ?_
      refine ⟨upperOutput, upperCost, 0, ?_, ?_, by omega⟩
      · simpa [quicksort, interpret, upperSubproblem, partitionAt] using hUpper
      · rw [interpretWith_pure]
        simp [RandCostM.deterministic]
  · rw [List.length_eraseIdx_of_lt index.isLt]
    simp [add_assoc]

/-- Every concrete pivot position has positive probability under the actual uniform runner, so
a supported fixed-pivot continuation branch is also a supported full Quicksort branch. -/
theorem quicksort_joint_support_of_pivot [LinearOrder alpha]
    (first : alpha) (rest : List alpha)
    (index : Fin (first :: rest).length) (output : List alpha) (cost : Nat)
    (hLong : ¬(first :: rest).length <= 3)
    (hContinuation : (output, cost) ∈
      (interpret CostModel.comparisonOnly
        (quicksortContinuation (first :: rest) index)).joint.support) :
    (output, cost) ∈ (quicksort (first :: rest)).joint.support := by
  unfold quicksort interpret
  rw [quicksortProgram, if_neg hLong, interpretWith_bind,
    interpretWith_choosePivotIndex_comparisonOnly]
  refine (mem_joint_support_bind_iff _ _ _ _).mpr ?_
  refine ⟨ULift.up index, 0, cost, ?_, ?_, by simp⟩
  · exact mem_joint_support_sample_of_mem _ _
      (PMF.mem_support_uniformOfFintype (ULift.up index))
  · simpa [quicksortContinuation, interpret] using hContinuation

theorem quicksort_joint_cost_eq_of_length_le_three [LinearOrder alpha]
    (input output : List alpha) (cost : Nat) (hSmall : input.length <= 3)
    (hMem : (output, cost) ∈ (quicksort input).joint.support) :
    cost = smallComparisonCost input.length := by
  unfold quicksort at hMem
  cases input with
  | nil =>
      rw [quicksortProgram] at hMem
      exact sortSmallProgram_joint_cost_eq [] output cost hSmall hMem
  | cons first rest =>
      rw [quicksortProgram, if_pos hSmall] at hMem
      exact sortSmallProgram_joint_cost_eq (first :: rest) output cost hSmall hMem

/-- Approved extension (worst comparisons), upper half: every supported comparison-counting
branch uses at most one comparison per unordered input pair. -/
theorem quicksort_branch_comparisonCost_le [LinearOrder alpha]
    (input output : List alpha) (cost : Nat) (hNodup : input.Nodup)
    (hMem : (output, cost) ∈ (quicksort input).joint.support) :
    cost <= input.length.choose 2 := by
  induction hInputLength : input.length using Nat.strong_induction_on
      generalizing input output cost with
  | h n ih =>
      subst hInputLength
      by_cases hSmall : input.length <= 3
      · have hCost := quicksort_joint_cost_eq_of_length_le_three
          input output cost hSmall hMem
        rw [hCost, smallComparisonCost_eq_choose_two input.length hSmall]
      · cases input with
        | nil => simp at hSmall
        | cons first rest =>
            change (output, cost) ∈
              (interpretWith SemanticBackend.uniformLinearOrder
                CostModel.comparisonOnly
                (quicksortProgram (first :: rest))).joint.support at hMem
            rw [quicksortProgram, if_neg hSmall, interpretWith_bind,
              interpretWith_choosePivotIndex_comparisonOnly] at hMem
            obtain ⟨sampledIndex, pivotCost, continuationCost,
                hPivot, hContinuation, hCost⟩ :=
              (mem_joint_support_bind_iff _ _ _ _).mp hMem
            have hPivotCost : pivotCost = 0 :=
              joint_support_sample_cost_eq_zero _ _ _ hPivot
            subst pivotCost
            change (output, continuationCost) ∈
              (interpret CostModel.comparisonOnly
                (quicksortContinuation (first :: rest)
                  sampledIndex.down)).joint.support at hContinuation
            obtain ⟨lowerOutput, lowerCost, upperOutput, upperCost,
                hLower, hUpper, hContinuationCost⟩ :=
              quicksortContinuation_joint_cost_decompose
                (first :: rest) sampledIndex.down output continuationCost
                hContinuation
            let source := first :: rest
            let index : Fin source.length := sampledIndex.down
            have hLowerShort : (lowerSubproblem source index).length < source.length := by
              rw [lowerSubproblem_length source hNodup index]
              exact (pivotRankEquiv source hNodup index).isLt
            have hUpperShort : (upperSubproblem source index).length < source.length := by
              rw [upperSubproblem_length source hNodup index]
              omega
            have hLowerBound := ih (lowerSubproblem source index).length
              hLowerShort (lowerSubproblem source index) lowerOutput lowerCost
              (lowerSubproblem_nodup source hNodup index) hLower rfl
            have hUpperBound := ih (upperSubproblem source index).length
              hUpperShort (upperSubproblem source index) upperOutput upperCost
              (upperSubproblem_nodup source hNodup index) hUpper rfl
            have hSplit := comparison_split_quadratic_bound source.length
              (pivotRankEquiv source hNodup index).val
              (pivotRankEquiv source hNodup index).isLt
            have hLowerLength := lowerSubproblem_length source hNodup index
            have hUpperLength := upperSubproblem_length source hNodup index
            have hCostBound :
                cost <= source.length - 1 +
                  (lowerSubproblem source index).length.choose 2 +
                  (upperSubproblem source index).length.choose 2 := by
              dsimp [source, index] at hCost hContinuationCost
              dsimp [source, index] at hLowerBound hUpperBound
              dsimp [source, index]
              omega
            calc
              cost <= source.length - 1 +
                  (lowerSubproblem source index).length.choose 2 +
                  (upperSubproblem source index).length.choose 2 := hCostBound
              _ = source.length - 1 +
                  (pivotRankEquiv source hNodup index).val.choose 2 +
                  (source.length - 1 -
                    (pivotRankEquiv source hNodup index).val).choose 2 := by
                    rw [hLowerLength, hUpperLength]
              _ <= source.length.choose 2 := hSplit
              _ = (first :: rest).length.choose 2 := by rfl

/-- Approved extension (worst comparisons), lower half: repeatedly selecting the minimum-rank
pivot gives a supported branch that compares every unordered pair exactly once. -/
theorem quicksort_exists_max_comparison_branch [LinearOrder alpha]
    (input : List alpha) (hNodup : input.Nodup) :
    ∃ output, (output, input.length.choose 2) ∈ (quicksort input).joint.support := by
  induction hInputLength : input.length using Nat.strong_induction_on
      generalizing input with
  | h n ih =>
      subst hInputLength
      by_cases hSmall : input.length <= 3
      · obtain ⟨branch, hBranch⟩ := (quicksort input).joint.support_nonempty
        rcases branch with ⟨output, cost⟩
        have hCost := quicksort_joint_cost_eq_of_length_le_three
          input output cost hSmall hBranch
        rw [hCost, smallComparisonCost_eq_choose_two input.length hSmall] at hBranch
        exact ⟨output, hBranch⟩
      · cases input with
        | nil => simp at hSmall
        | cons first rest =>
            let source := first :: rest
            let zeroRank : Fin source.length := ⟨0, by simp [source]⟩
            let index : Fin source.length :=
              (pivotRankEquiv source hNodup).symm zeroRank
            have hRank : pivotRankEquiv source hNodup index = zeroRank :=
              (pivotRankEquiv source hNodup).apply_symm_apply zeroRank
            have hRankValue : (pivotRankEquiv source hNodup index).val = 0 := by
              exact congrArg Fin.val hRank
            have hLowerLength : (lowerSubproblem source index).length = 0 := by
              rw [lowerSubproblem_length source hNodup index]
              exact hRankValue
            have hUpperLength :
                (upperSubproblem source index).length = source.length - 1 := by
              rw [upperSubproblem_length source hNodup index, hRankValue]
              simp
            have hLowerShort :
                (lowerSubproblem source index).length < source.length := by
              rw [hLowerLength]
              simp [source]
            have hUpperShort :
                (upperSubproblem source index).length < source.length := by
              rw [hUpperLength]
              simp [source]
            obtain ⟨lowerOutput, hLower⟩ :=
              ih (lowerSubproblem source index).length hLowerShort
                (lowerSubproblem source index)
                (lowerSubproblem_nodup source hNodup index) rfl
            obtain ⟨upperOutput, hUpper⟩ :=
              ih (upperSubproblem source index).length hUpperShort
                (upperSubproblem source index)
                (upperSubproblem_nodup source hNodup index) rfl
            have hContinuation := quicksortContinuation_joint_support_of_recursive
              source index lowerOutput upperOutput
              ((lowerSubproblem source index).length.choose 2)
              ((upperSubproblem source index).length.choose 2) hLower hUpper
            have hCost :
                source.length - 1 +
                    (lowerSubproblem source index).length.choose 2 +
                    (upperSubproblem source index).length.choose 2 =
                  source.length.choose 2 := by
              rw [hLowerLength, hUpperLength]
              simp [source, Nat.choose_succ_succ, Nat.choose_one_right]
            rw [hCost] at hContinuation
            refine ⟨lowerOutput ++ source.get index :: upperOutput, ?_⟩
            simpa [source] using quicksort_joint_support_of_pivot
              first rest index (lowerOutput ++ source.get index :: upperOutput)
                (source.length.choose 2) hSmall hContinuation

/-- The greatest supported comparison cost for a fixed input, searched under the proved cap. -/
noncomputable def worstComparisonCost [LinearOrder alpha] (input : List alpha) : Nat := by
  classical
  exact Nat.findGreatest
    (fun cost => ∃ output, (output, cost) ∈ (quicksort input).joint.support)
    (input.length.choose 2)

/-- On distinct inputs the greatest supported comparison cost is exactly `n.choose 2`. -/
theorem worstComparisonCost_eq_choose [LinearOrder alpha]
    (input : List alpha) (hNodup : input.Nodup) :
    worstComparisonCost input = input.length.choose 2 := by
  classical
  unfold worstComparisonCost
  exact Nat.findGreatest_eq
    (quicksort_exists_max_comparison_branch input hNodup)

/-- The comparison-cost maximum is attained and bounds every supported branch. -/
theorem worstComparisonCost_isMaximum [LinearOrder alpha]
    (input : List alpha) (hNodup : input.Nodup) :
    (∃ output,
      (output, worstComparisonCost input) ∈ (quicksort input).joint.support) ∧
    ∀ output cost, (output, cost) ∈ (quicksort input).joint.support →
      cost ≤ worstComparisonCost input := by
  rw [worstComparisonCost_eq_choose input hNodup]
  exact ⟨quicksort_exists_max_comparison_branch input hNodup,
    fun output cost hMem =>
      quicksort_branch_comparisonCost_le input output cost hNodup hMem⟩

/-- The worst supported comparison cost on the canonical distinct input of size `n`. -/
noncomputable def worstComparisonsBySize (n : Nat) : Nat :=
  worstComparisonCost (List.range n)

@[simp] theorem worstComparisonsBySize_eq_choose (n : Nat) :
    worstComparisonsBySize n = n.choose 2 := by
  simpa [worstComparisonsBySize] using
    worstComparisonCost_eq_choose (List.range n) List.nodup_range

/-- Approved extension: the actual worst supported comparison count is `Θ(n²)`. -/
theorem worstComparisonsBySize_isTheta :
    (fun n : Nat => (worstComparisonsBySize n : Real)) =Θ[atTop]
      (fun n : Nat => (n ^ 2 : Real)) := by
  simpa only [worstComparisonsBySize_eq_choose] using (isTheta_choose 2)

/-! ## Textbook running-time model -/

/-- The same free Quicksort program interpreted with the approved unit linear textbook model. -/
def textbookQuicksort [LinearOrder alpha] (input : List alpha) :
    RandCostM Nat (List alpha) :=
  interpret CostModel.textbookModel (quicksortProgram input)

@[simp] theorem interpretWith_compareLE_textbookModel [LinearOrder alpha]
    (left right : alpha) :
    interpretWith SemanticBackend.uniformLinearOrder CostModel.textbookModel
        (compareLE left right) =
      RandCostM.deterministic (ULift.up (decide (left <= right))) 1 := by
  apply RandCostM.ext
  simp [interpretWith_compareLE, measuredHandler, semanticHandler,
    SemanticBackend.uniformLinearOrder, Sorting.ComparisonBackend.linearOrder,
    CostModel.operationCost, CostModel.textbookModel, CostModel.linearTextbook,
    Sorting.ComparisonCostModel.constant, RandCostM.sampleAtCost,
    RandCostM.sampleWithCost, RandCostM.deterministic, PMF.pure_map]

@[simp] theorem interpretWith_markBaseCase_textbookModel
    (backend : SemanticBackend alpha) (size : Nat) :
    interpretWith backend CostModel.textbookModel (markBaseCase size) =
      RandCostM.deterministic PUnit.unit 1 := by
  apply RandCostM.ext
  simp [interpretWith_markBaseCase, measuredHandler, semanticHandler,
    CostModel.operationCost, CostModel.textbookModel, CostModel.linearTextbook,
    RandCostM.sampleAtCost, RandCostM.sampleWithCost,
    RandCostM.deterministic, PMF.pure_map]

/-- Under the approved textbook model, partitioning still costs exactly one unit per key
comparison; the separately charged splitter frame is emitted by the pivot operation. -/
theorem interpret_partitionProgram_textbookModel [LinearOrder alpha]
    (pivot : alpha) (input : List alpha) :
    interpret CostModel.textbookModel (partitionProgram pivot input) =
      RandCostM.deterministic (linearPartition pivot input) input.length := by
  induction input with
  | nil =>
      simp [partitionProgram, linearPartition, interpret, interpretWith]
  | cons value rest ih =>
      change interpretWith SemanticBackend.uniformLinearOrder CostModel.textbookModel
          (partitionProgram pivot (value :: rest)) = _
      change interpretWith SemanticBackend.uniformLinearOrder CostModel.textbookModel
          (partitionProgram pivot rest) = _ at ih
      rw [partitionProgram, interpretWith_bind,
        interpretWith_compareLE_textbookModel]
      apply RandCostM.ext
      by_cases hle : value <= pivot <;>
        simp [RandCostM.deterministic, ih, interpretWith_bind,
          interpretWith_pure, linearPartition, hle, Nat.add_comm]

/-- The constant-size sorting network costs one textbook base-frame unit in addition to its
exact element-comparison count. -/
theorem expectedCost_sortSmallProgram_textbookModel [LinearOrder alpha]
    (input : List alpha) (hLength : input.length <= 3) :
    (interpret CostModel.textbookModel (sortSmallProgram input)).expectedCost =
      1 + smallComparisonCost input.length := by
  rcases input with _ | ⟨first, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, rest⟩⟩⟩⟩
  · norm_num [smallComparisonCost]
    unfold interpret
    rw [sortSmallProgram, interpretWith_bind,
      interpretWith_markBaseCase_textbookModel]
    simp [RandCostM.expectedCost_bind_split]
  · norm_num [smallComparisonCost]
    unfold interpret
    rw [sortSmallProgram, interpretWith_bind,
      interpretWith_markBaseCase_textbookModel]
    simp [RandCostM.expectedCost_bind_split]
  · norm_num [smallComparisonCost]
    unfold interpret
    rw [sortSmallProgram, interpretWith_bind,
      interpretWith_markBaseCase_textbookModel]
    simp [RandCostM.expectedCost_bind_split,
      interpretWith_map, CostModel.textbookModel, CostModel.linearTextbook,
      Sorting.ComparisonCostModel.constant]
    norm_num
  · norm_num [smallComparisonCost]
    unfold interpret
    rw [sortSmallProgram, interpretWith_bind,
      interpretWith_markBaseCase_textbookModel]
    simp [RandCostM.expectedCost_bind_split, interpretWith_bind,
      interpretWith_map, CostModel.textbookModel, CostModel.linearTextbook,
      Sorting.ComparisonCostModel.constant]
    norm_num
  · simp only [List.length_cons] at hLength
    omega

@[simp] theorem interpretWith_choosePivotIndex_textbookModel [LinearOrder alpha]
    (tailLength : Nat) :
    interpretWith (SemanticBackend.uniformLinearOrder (alpha := alpha))
        (CostModel.textbookModel (alpha := alpha))
        (choosePivotIndex tailLength) =
      RandCostM.sampleAtCost
        (PMF.uniformOfFintype (ULift (Fin (tailLength + 1))))
        (tailLength + 1) := by
  rw [interpretWith_choosePivotIndex]
  simp [measuredHandler, semanticHandler, CostModel.operationCost,
    SemanticBackend.uniformLinearOrder, PivotBackend.uniform,
    CostModel.textbookModel, CostModel.linearTextbook]

@[simp] theorem expectedCost_sampleAtCost_nat (distribution : PMF beta) (cost : Nat) :
    (RandCostM.sampleAtCost distribution cost : RandCostM Nat beta).expectedCost = cost := by
  simp [RandCostM.sampleAtCost]

/-- A fixed-pivot textbook continuation has the same partition comparison charge as the
comparison-only model, followed by the two textbook-cost recursive calls. -/
theorem expectedCost_textbookQuicksortContinuation [LinearOrder alpha]
    (input : List alpha) (index : Fin input.length) :
    (interpret CostModel.textbookModel
      (quicksortContinuation input index)).expectedCost =
      ((input.length - 1 : Nat) : ENNReal) +
        (textbookQuicksort (lowerSubproblem input index)).expectedCost +
        (textbookQuicksort (upperSubproblem input index)).expectedCost := by
  have hPartition := interpret_partitionProgram_textbookModel
    (input.get index) (input.eraseIdx index)
  have hErase : (input.eraseIdx index).length = input.length - 1 :=
    List.length_eraseIdx_of_lt index.isLt
  unfold interpret at hPartition
  unfold quicksortContinuation interpret
  rw [interpretWith_bind, hPartition]
  simp [RandCostM.expectedCost_bind_split, interpretWith_bind,
    textbookQuicksort, interpret, lowerSubproblem, upperSubproblem, partitionAt,
    hErase, add_assoc]

/-- The actual uniform textbook runner, unfolded for one recursive step. The leading `n` is the
approved size-linear splitter-frame charge. -/
theorem expectedCost_textbookQuicksort_step [LinearOrder alpha]
    (first : alpha) (rest : List alpha)
    (hLong : ¬(first :: rest).length <= 3) :
    (textbookQuicksort (first :: rest)).expectedCost =
      (((first :: rest).length : Nat) : ENNReal) +
        (((first :: rest).length : Nat) : ENNReal)⁻¹ *
          ∑ index : Fin (first :: rest).length,
            (interpret CostModel.textbookModel
              (quicksortContinuation (first :: rest) index)).expectedCost := by
  unfold textbookQuicksort interpret
  rw [quicksortProgram, if_neg hLong, interpretWith_bind,
    interpretWith_choosePivotIndex_textbookModel,
    RandCostM.expectedCost_bind_split]
  simp only [expectedCost_sampleAtCost_nat, RandCostM.ret_sampleAtCost]
  rw [ResourceAware.Program.weightedSum_uniformOfFintype]
  simp only [Fintype.card_ulift, Fintype.card_fin]
  congr 2
  exact Fintype.sum_equiv Equiv.ulift _ _ fun sampled => by
    rfl

/-- Exact expected textbook-running-time recurrence derived from the interpreted free program. -/
theorem expectedCost_textbookQuicksort_recurrence [LinearOrder alpha]
    (first : alpha) (rest : List alpha)
    (hLong : ¬(first :: rest).length <= 3) :
    (textbookQuicksort (first :: rest)).expectedCost =
      (((first :: rest).length : Nat) : ENNReal) +
        (((first :: rest).length : Nat) : ENNReal)⁻¹ *
          ∑ index : Fin (first :: rest).length,
            ((((first :: rest).length - 1 : Nat) : ENNReal) +
              (textbookQuicksort
                (lowerSubproblem (alpha := alpha) (first :: rest)
                  (index : Fin (first :: rest).length))).expectedCost +
              (textbookQuicksort
                (upperSubproblem (alpha := alpha) (first :: rest)
                  (index : Fin (first :: rest).length))).expectedCost) := by
  rw [expectedCost_textbookQuicksort_step first rest hLong]
  simp_rw [expectedCost_textbookQuicksortContinuation]

theorem expectedCost_textbookQuicksort_of_length_le_three [LinearOrder alpha]
    (input : List alpha) (hSmall : input.length <= 3) :
    (textbookQuicksort input).expectedCost =
      1 + smallComparisonCost input.length := by
  unfold textbookQuicksort
  cases input with
  | nil =>
      rw [quicksortProgram]
      exact expectedCost_sortSmallProgram_textbookModel [] hSmall
  | cons first rest =>
      rw [quicksortProgram, if_pos hSmall]
      exact expectedCost_sortSmallProgram_textbookModel (first :: rest) hSmall

theorem subproblem_lengths_add [LinearOrder alpha]
    (input : List alpha) (index : Fin input.length) :
    (lowerSubproblem input index).length +
      (upperSubproblem input index).length = input.length - 1 := by
  have hParts := (partitionAt input index).perm.length_eq
  simp only [List.length_append] at hParts
  change (lowerSubproblem input index).length +
      (upperSubproblem input index).length =
        (input.eraseIdx index).length at hParts
  simpa [List.length_eraseIdx_of_lt index.isLt] using hParts

theorem lowerSubproblem_length_lt [LinearOrder alpha]
    (input : List alpha) (index : Fin input.length) :
    (lowerSubproblem input index).length < input.length := by
  have hSizes := subproblem_lengths_add input index
  have hPositive : 0 < input.length := Nat.zero_lt_of_lt index.isLt
  omega

theorem upperSubproblem_length_lt [LinearOrder alpha]
    (input : List alpha) (index : Fin input.length) :
    (upperSubproblem input index).length < input.length := by
  have hSizes := subproblem_lengths_add input index
  have hPositive : 0 < input.length := Nat.zero_lt_of_lt index.isLt
  omega

private theorem textbook_branch_le
    (n lowerSize upperSize : Nat)
    (tLower tUpper cLower cUpper : ENNReal)
    (hn : 0 < n) (hSizes : lowerSize + upperSize = n - 1)
    (hLower : tLower <= 2 * cLower + 2 * (lowerSize : ENNReal) + 1)
    (hUpper : tUpper <= 2 * cUpper + 2 * (upperSize : ENNReal) + 1) :
    (((n - 1 : Nat) : ENNReal) + tLower) + tUpper <=
      2 * ((((n - 1 : Nat) : ENNReal) + cLower) + cUpper) +
        ((n : ENNReal) + 1) := by
  calc
    (((n - 1 : Nat) : ENNReal) + tLower) + tUpper <=
        (((n - 1 : Nat) : ENNReal) +
          (2 * cLower + 2 * (lowerSize : ENNReal) + 1)) +
          (2 * cUpper + 2 * (upperSize : ENNReal) + 1) :=
      add_le_add (add_le_add_right hLower _) hUpper
    _ = _ := by
      have hSizesE : (lowerSize : ENNReal) + (upperSize : ENNReal) =
          ((n - 1 : Nat) : ENNReal) := by
        exact_mod_cast hSizes
      have hPredE : ((n - 1 : Nat) : ENNReal) + 1 = (n : ENNReal) := by
        exact_mod_cast (show n - 1 + 1 = n by omega)
      rw [← hPredE, ← hSizesE]
      ring

/-- Kleinberg--Tardos, pp. 732 and 734 (unnumbered expected-running-time claim): under the
approved unit linear textbook model, expected running time is controlled by twice the actual
comparison expectation plus a linear term. -/
theorem textbookQuicksort_expectedCost_le [LinearOrder alpha]
    (input : List alpha) :
    (textbookQuicksort input).expectedCost <=
      2 * (quicksort input).expectedCost +
        2 * (input.length : ENNReal) + 1 := by
  induction hInputLength : input.length using Nat.strong_induction_on
      generalizing input with
  | h n ih =>
      subst hInputLength
      by_cases hSmall : input.length <= 3
      · rw [expectedCost_textbookQuicksort_of_length_le_three input hSmall,
          expectedCost_quicksort_of_length_le_three input hSmall]
        calc
          (1 : ENNReal) + smallComparisonCost input.length <=
              ((1 : ENNReal) + smallComparisonCost input.length) +
                ((smallComparisonCost input.length : ENNReal) +
                  2 * (input.length : ENNReal)) := by
            simp
          _ = 2 * (smallComparisonCost input.length : ENNReal) +
                2 * (input.length : ENNReal) + 1 := by ring
      · cases input with
        | nil => simp at hSmall
        | cons first rest =>
            rw [expectedCost_textbookQuicksort_recurrence first rest hSmall,
              expectedCost_quicksort_recurrence first rest hSmall]
            let source := first :: rest
            let tBranch : Fin source.length -> ENNReal := fun index =>
              (((source.length - 1 : Nat) : ENNReal) +
                  (textbookQuicksort (lowerSubproblem source index)).expectedCost) +
                (textbookQuicksort (upperSubproblem source index)).expectedCost
            let cBranch : Fin source.length -> ENNReal := fun index =>
              (((source.length - 1 : Nat) : ENNReal) +
                  (quicksort (lowerSubproblem source index)).expectedCost) +
                (quicksort (upperSubproblem source index)).expectedCost
            change (source.length : ENNReal) +
                (source.length : ENNReal)⁻¹ * ∑ index, tBranch index <=
              2 * ((source.length : ENNReal)⁻¹ * ∑ index, cBranch index) +
                2 * (source.length : ENNReal) + 1
            have hPointwise (index : Fin source.length) :
                tBranch index <=
                  2 * cBranch index + ((source.length : ENNReal) + 1) := by
              have hSizes := subproblem_lengths_add source index
              have hLowerShort :
                  (lowerSubproblem source index).length < source.length := by
                exact lowerSubproblem_length_lt source index
              have hUpperShort :
                  (upperSubproblem source index).length < source.length := by
                exact upperSubproblem_length_lt source index
              have hLower := ih (lowerSubproblem source index).length hLowerShort
                (lowerSubproblem source index) rfl
              have hUpper := ih (upperSubproblem source index).length hUpperShort
                (upperSubproblem source index) rfl
              simpa [tBranch, cBranch] using
                textbook_branch_le source.length
                  (lowerSubproblem source index).length
                  (upperSubproblem source index).length
                  (textbookQuicksort (lowerSubproblem source index)).expectedCost
                  (textbookQuicksort (upperSubproblem source index)).expectedCost
                  (quicksort (lowerSubproblem source index)).expectedCost
                  (quicksort (upperSubproblem source index)).expectedCost
                  (Nat.zero_lt_of_lt index.isLt) hSizes hLower hUpper
            letI : Nonempty (Fin source.length) := ⟨⟨0, by simp [source]⟩⟩
            let pivotDistribution : PMF (Fin source.length) :=
              PMF.uniformOfFintype (Fin source.length)
            have hUniform (weight : Fin source.length -> ENNReal) :
                RandCostM.weightedSum pivotDistribution weight =
                  (source.length : ENNReal)⁻¹ * ∑ index, weight index := by
              simpa [pivotDistribution] using
                (ResourceAware.Program.weightedSum_uniformOfFintype
                  (index := Fin source.length) weight)
            have hAverage :
                RandCostM.weightedSum pivotDistribution tBranch <=
                  RandCostM.weightedSum pivotDistribution
                    (fun index => 2 * cBranch index +
                      ((source.length : ENNReal) + 1)) :=
              RandCostM.weightedSum_mono pivotDistribution hPointwise
            have hLinear :
                RandCostM.weightedSum pivotDistribution
                    (fun index => 2 * cBranch index +
                      ((source.length : ENNReal) + 1)) =
                  2 * RandCostM.weightedSum pivotDistribution cBranch +
                    ((source.length : ENNReal) + 1) := by
              simp only [two_mul]
              rw [RandCostM.weightedSum_add, RandCostM.weightedSum_add,
                RandCostM.weightedSum_const]
            calc
              (source.length : ENNReal) +
                  (source.length : ENNReal)⁻¹ * ∑ index, tBranch index =
                (source.length : ENNReal) +
                  RandCostM.weightedSum pivotDistribution tBranch := by
                    rw [hUniform]
              _ <= (source.length : ENNReal) +
                  RandCostM.weightedSum pivotDistribution
                    (fun index => 2 * cBranch index +
                      ((source.length : ENNReal) + 1)) :=
                add_le_add_right hAverage _
              _ = (source.length : ENNReal) +
                  (2 * RandCostM.weightedSum pivotDistribution cBranch +
                    ((source.length : ENNReal) + 1)) := by rw [hLinear]
              _ = 2 * ((source.length : ENNReal)⁻¹ *
                    ∑ index, cBranch index) +
                  2 * (source.length : ENNReal) + 1 := by
                rw [hUniform]
                ring

/-- The expected-cost weakest preexpectation for the textbook runner obeys the same bound. -/
theorem textbookQuicksort_ecwp_le [LinearOrder alpha] (input : List alpha) :
    RandCostM.ecwp (textbookQuicksort input) (fun _ => 0) <=
      2 * (quicksort input).expectedCost +
        2 * (input.length : ENNReal) + 1 := by
  simpa using textbookQuicksort_expectedCost_le input

/-- The unit textbook model is an instance of the implementation handoff's approved bounded
linear model family. -/
theorem textbookModel_isBoundedBy :
    (CostModel.textbookModel (alpha := alpha)).IsBoundedBy
      (CostModel.linearTextbookBounds 1 1 1) := by
  simpa [CostModel.textbookModel] using
    (CostModel.linearTextbook_isBoundedBy (alpha := alpha) 1 1 1)

/-- Size-indexed real observation of the textbook runner on canonical distinct inputs. -/
def expectedTextbookRuntimeBySize (n : Nat) : Real :=
  (textbookQuicksort (List.range n)).expectedCost.toReal

/-- Real envelope obtained by transferring the comparison bound through the textbook-cost
coupling theorem. -/
def expectedTextbookRuntimeEnvelope (n : Nat) : Real :=
  2 * expectedComparisonEnvelope n + 2 * n + 1

theorem expectedTextbookRuntimeBySize_nonneg (n : Nat) :
    0 <= expectedTextbookRuntimeBySize n :=
  ENNReal.toReal_nonneg

theorem expectedTextbookRuntimeEnvelope_nonneg (n : Nat) :
    0 <= expectedTextbookRuntimeEnvelope n := by
  have hComparison := expectedComparisonEnvelope_nonneg n
  unfold expectedTextbookRuntimeEnvelope
  positivity

theorem expectedTextbookRuntimeBySize_le (n : Nat) :
    expectedTextbookRuntimeBySize n <= expectedTextbookRuntimeEnvelope n := by
  have hRuntime := textbookQuicksort_expectedCost_le (List.range n)
  have hComparisons := quicksort_expectedComparisonCost_le
    (List.range n) List.nodup_range
  have hRuntime' :
      (textbookQuicksort (List.range n)).expectedCost <=
        2 * (quicksort (List.range n)).expectedCost + 2 * (n : ENNReal) + 1 := by
    simpa using hRuntime
  have hComparisons' :
      (quicksort (List.range n)).expectedCost <=
        expectedComparisonEnvelopeENN n := by
    simpa using hComparisons
  have hBound :
      (textbookQuicksort (List.range n)).expectedCost <=
        2 * expectedComparisonEnvelopeENN n + 2 * (n : ENNReal) + 1 :=
    hRuntime'.trans (by gcongr)
  have hRightFinite :
      2 * expectedComparisonEnvelopeENN n + 2 * (n : ENNReal) + 1 ≠ ⊤ := by
    apply (ENNReal.add_ne_top).2
    constructor
    · apply (ENNReal.add_ne_top).2
      exact ⟨ENNReal.mul_ne_top (by norm_num)
          (by simp [expectedComparisonEnvelopeENN]),
        ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top n)⟩
    · norm_num
  have hLeftFinite :
      (textbookQuicksort (List.range n)).expectedCost ≠ ⊤ :=
    ne_top_of_le_ne_top hRightFinite hBound
  have hToReal :=
    (ENNReal.toReal_le_toReal hLeftFinite hRightFinite).2 hBound
  have hSumFinite :
      2 * expectedComparisonEnvelopeENN n + 2 * (n : ENNReal) ≠ ⊤ :=
    ((ENNReal.add_ne_top).mp hRightFinite).1
  have hFirstFinite : 2 * expectedComparisonEnvelopeENN n ≠ ⊤ :=
    ((ENNReal.add_ne_top).mp hSumFinite).1
  have hSecondFinite : 2 * (n : ENNReal) ≠ ⊤ :=
    ((ENNReal.add_ne_top).mp hSumFinite).2
  rw [ENNReal.toReal_add hSumFinite (by norm_num),
    ENNReal.toReal_add hFirstFinite hSecondFinite] at hToReal
  simpa [expectedTextbookRuntimeBySize, expectedTextbookRuntimeEnvelope,
    expectedComparisonEnvelopeENN, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (expectedComparisonEnvelope_nonneg n)] using hToReal

theorem expectedTextbookRuntimeEnvelope_isBigO :
    expectedTextbookRuntimeEnvelope =O[atTop] nLogN := by
  refine IsBigO.of_bound 15 (Filter.eventually_atTop.2 ⟨1, ?_⟩)
  intro n hn
  have hnReal : (1 : Real) <= n := by exact_mod_cast hn
  have hLogNonneg : (0 : Real) <= Real.log n := Real.log_nonneg hnReal
  have hLogFactor : (1 : Real) <= 1 + Real.log n := by linarith
  have hNLogNonneg := nLogN_nonneg hn
  have hNLe : (n : Real) <= nLogN n := by
    unfold nLogN
    nlinarith
  have hOneLe : (1 : Real) <= nLogN n := hnReal.trans hNLe
  have hComparison : expectedComparisonEnvelope n <= 6 * nLogN n := by
    have hHarmonic : (harmonic n : Real) <= 1 + Real.log n :=
      harmonic_le_one_add_log n
    have hHarmonicNonneg := harmonic_nonneg_real n
    calc
      expectedComparisonEnvelope n <=
          3 * (2 * (n : Real)) * (1 + Real.log n) := by
            unfold expectedComparisonEnvelope
            gcongr
            linarith
      _ = 6 * nLogN n := by
            unfold nLogN
            ring
  rw [Real.norm_eq_abs,
    abs_of_nonneg (expectedTextbookRuntimeEnvelope_nonneg n)]
  rw [Real.norm_eq_abs, abs_of_nonneg hNLogNonneg]
  change expectedTextbookRuntimeEnvelope n <= 15 * nLogN n
  unfold expectedTextbookRuntimeEnvelope
  linarith

/-- Kleinberg--Tardos, pp. 732 and 734 (unnumbered): the expected running time of the actual
uniform-pivot free program, interpreted by the approved textbook model, is `O(n log n)`. -/
theorem expectedTextbookRuntimeBySize_isBigO :
    expectedTextbookRuntimeBySize =O[atTop]
      (fun n : Nat => (n : Real) * Real.log n) := by
  have hToEnvelope :
      expectedTextbookRuntimeBySize =O[atTop] expectedTextbookRuntimeEnvelope := by
    refine IsBigO.of_bound 1 (Filter.Eventually.of_forall fun n => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (expectedTextbookRuntimeBySize_nonneg n)]
    rw [Real.norm_eq_abs, abs_of_nonneg (expectedTextbookRuntimeEnvelope_nonneg n)]
    simpa using expectedTextbookRuntimeBySize_le n
  exact (hToEnvelope.trans expectedTextbookRuntimeEnvelope_isBigO).trans
    nLogN_isBigO_mul_log

/-! ## Worst-case textbook running time -/

theorem joint_support_sampleAtCost_cost_eq (distribution : PMF beta)
    (chargedCost : Nat) (value : beta) (cost : Nat)
    (hMem : (value, cost) ∈
      (RandCostM.sampleAtCost distribution chargedCost :
        RandCostM Nat beta).joint.support) :
    cost = chargedCost := by
  rw [RandCostM.sampleAtCost, RandCostM.joint_sampleWithCost,
    PMF.mem_support_map_iff] at hMem
  obtain ⟨sampled, _, hEqual⟩ := hMem
  exact (congrArg Prod.snd hEqual).symm

theorem mem_joint_support_sampleAtCost_of_mem (distribution : PMF beta)
    (chargedCost : Nat) (value : beta) (hValue : value ∈ distribution.support) :
    (value, chargedCost) ∈
      (RandCostM.sampleAtCost distribution chargedCost :
        RandCostM Nat beta).joint.support := by
  rw [RandCostM.sampleAtCost, RandCostM.joint_sampleWithCost,
    PMF.mem_support_map_iff]
  exact ⟨value, hValue, rfl⟩

theorem sortSmallProgram_joint_cost_textbookModel [LinearOrder alpha]
    (input output : List alpha) (cost : Nat) (hSmall : input.length <= 3)
    (hMem : (output, cost) ∈
      (interpret CostModel.textbookModel (sortSmallProgram input)).joint.support) :
    cost = 1 + smallComparisonCost input.length := by
  rcases input with _ | ⟨first, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, rest⟩⟩⟩⟩
  · simp only [interpret, CostModel.textbookModel, CostModel.linearTextbook,
      Sorting.ComparisonCostModel.constant, one_mul, sortSmallProgram, bind_pure_comp,
      interpretWith_map, interpretWith_markBaseCase, RandCostM.joint_map,
      measuredHandler_joint, CostModel.operationCost_baseCase, semanticHandler_baseCase,
      PMF.pure_map, PMF.support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
      smallComparisonCost, List.length_nil, add_zero] at hMem ⊢
    exact hMem.2
  · simp only [interpret, CostModel.textbookModel, CostModel.linearTextbook,
      Sorting.ComparisonCostModel.constant, one_mul, sortSmallProgram, bind_pure_comp,
      interpretWith_map, interpretWith_markBaseCase, RandCostM.joint_map,
      measuredHandler_joint, CostModel.operationCost_baseCase, semanticHandler_baseCase,
      PMF.pure_map, PMF.support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
      smallComparisonCost, List.length_cons, List.length_nil, zero_add,
      add_zero] at hMem ⊢
    exact hMem.2
  · simp only [interpret, CostModel.textbookModel, CostModel.linearTextbook,
      Sorting.ComparisonCostModel.constant, one_mul, sortSmallProgram, bind_pure_comp,
      interpretWith_bind, interpretWith_markBaseCase, interpretWith_map,
      interpretWith_compareSwap, RandCostM.deterministic, RandCostM.joint_bind,
      measuredHandler_joint, CostModel.operationCost_baseCase, semanticHandler_baseCase,
      PMF.pure_map, RandCostM.joint_map, PMF.pure_bind, Nat.reduceAdd,
      PMF.support_pure, Set.mem_singleton_iff, Prod.mk.injEq, smallComparisonCost,
      List.length_cons, List.length_nil, zero_add] at hMem ⊢
    omega
  · simp only [interpret, CostModel.textbookModel, CostModel.linearTextbook,
      Sorting.ComparisonCostModel.constant, one_mul, sortSmallProgram, bind_pure_comp,
      interpretWith_bind, interpretWith_markBaseCase, interpretWith_compareSwap,
      RandCostM.deterministic, interpretWith_map, RandCostM.joint_bind,
      measuredHandler_joint, CostModel.operationCost_baseCase, semanticHandler_baseCase,
      PMF.pure_map, RandCostM.joint_map, PMF.pure_bind, Nat.reduceAdd,
      PMF.support_pure, Set.mem_singleton_iff, Prod.mk.injEq, smallComparisonCost,
      List.length_cons, List.length_nil, zero_add] at hMem ⊢
    omega
  · simp only [List.length_cons] at hSmall
    omega

theorem textbookQuicksort_joint_cost_eq_of_length_le_three [LinearOrder alpha]
    (input output : List alpha) (cost : Nat) (hSmall : input.length <= 3)
    (hMem : (output, cost) ∈ (textbookQuicksort input).joint.support) :
    cost = 1 + smallComparisonCost input.length := by
  unfold textbookQuicksort at hMem
  cases input with
  | nil =>
      rw [quicksortProgram] at hMem
      exact sortSmallProgram_joint_cost_textbookModel [] output cost hSmall hMem
  | cons first rest =>
      rw [quicksortProgram, if_pos hSmall] at hMem
      exact sortSmallProgram_joint_cost_textbookModel
        (first :: rest) output cost hSmall hMem

theorem textbookQuicksortContinuation_joint_cost_decompose [LinearOrder alpha]
    (input : List alpha) (index : Fin input.length)
    (output : List alpha) (cost : Nat)
    (hMem : (output, cost) ∈
      (interpret CostModel.textbookModel
        (quicksortContinuation input index)).joint.support) :
    ∃ lowerOutput lowerCost upperOutput upperCost,
      (lowerOutput, lowerCost) ∈
          (textbookQuicksort (lowerSubproblem input index)).joint.support ∧
      (upperOutput, upperCost) ∈
          (textbookQuicksort (upperSubproblem input index)).joint.support ∧
      cost = input.length - 1 + lowerCost + upperCost := by
  have hPartition := interpret_partitionProgram_textbookModel
    (input.get index) (input.eraseIdx index)
  unfold interpret at hPartition
  change (output, cost) ∈
    (interpretWith SemanticBackend.uniformLinearOrder CostModel.textbookModel
      (quicksortContinuation input index)).joint.support at hMem
  unfold quicksortContinuation at hMem
  rw [interpretWith_bind, hPartition] at hMem
  obtain ⟨parts, partitionCost, afterPartitionCost,
      hParts, hAfterPartition, hCost⟩ :=
    (mem_joint_support_bind_iff _ _ _ _).mp hMem
  rw [RandCostM.joint_deterministic, PMF.mem_support_pure_iff] at hParts
  injection hParts with hPartsResult hPartsCost
  subst parts
  subst partitionCost
  rw [interpretWith_bind] at hAfterPartition
  obtain ⟨lowerOutput, lowerCost, afterLowerCost,
      hLower, hAfterLower, hAfterPartitionCost⟩ :=
    (mem_joint_support_bind_iff _ _ _ _).mp hAfterPartition
  rw [interpretWith_bind] at hAfterLower
  obtain ⟨upperOutput, upperCost, finalCost,
      hUpper, hFinal, hAfterLowerCost⟩ :=
    (mem_joint_support_bind_iff _ _ _ _).mp hAfterLower
  rw [interpretWith_pure] at hFinal
  rw [RandCostM.joint_pure, PMF.mem_support_pure_iff] at hFinal
  have hFinalCost := congrArg Prod.snd hFinal
  have hErase : (input.eraseIdx index).length = input.length - 1 :=
    List.length_eraseIdx_of_lt index.isLt
  refine ⟨lowerOutput, lowerCost, upperOutput, upperCost, ?_, ?_, ?_⟩
  · simpa [textbookQuicksort, interpret, lowerSubproblem, partitionAt] using hLower
  · simpa [textbookQuicksort, interpret, upperSubproblem, partitionAt] using hUpper
  · omega

theorem textbookQuicksortContinuation_joint_support_of_recursive [LinearOrder alpha]
    (input : List alpha) (index : Fin input.length)
    (lowerOutput upperOutput : List alpha) (lowerCost upperCost : Nat)
    (hLower : (lowerOutput, lowerCost) ∈
      (textbookQuicksort (lowerSubproblem input index)).joint.support)
    (hUpper : (upperOutput, upperCost) ∈
      (textbookQuicksort (upperSubproblem input index)).joint.support) :
    (lowerOutput ++ input.get index :: upperOutput,
        input.length - 1 + lowerCost + upperCost) ∈
      (interpret CostModel.textbookModel
        (quicksortContinuation input index)).joint.support := by
  have hPartition := interpret_partitionProgram_textbookModel
    (input.get index) (input.eraseIdx index)
  unfold interpret at hPartition
  change (lowerOutput ++ input.get index :: upperOutput,
      input.length - 1 + lowerCost + upperCost) ∈
    (interpretWith SemanticBackend.uniformLinearOrder CostModel.textbookModel
      (quicksortContinuation input index)).joint.support
  unfold quicksortContinuation
  rw [interpretWith_bind, hPartition]
  refine (mem_joint_support_bind_iff _ _ _ _).mpr ?_
  refine ⟨linearPartition (input.get index) (input.eraseIdx index),
    (input.eraseIdx index).length, lowerCost + upperCost, ?_, ?_, ?_⟩
  · simp [RandCostM.deterministic]
  · rw [interpretWith_bind]
    refine (mem_joint_support_bind_iff _ _ _ _).mpr ?_
    refine ⟨lowerOutput, lowerCost, upperCost, ?_, ?_, rfl⟩
    · simpa [textbookQuicksort, interpret, lowerSubproblem, partitionAt] using hLower
    · rw [interpretWith_bind]
      refine (mem_joint_support_bind_iff _ _ _ _).mpr ?_
      refine ⟨upperOutput, upperCost, 0, ?_, ?_, by omega⟩
      · simpa [textbookQuicksort, interpret, upperSubproblem, partitionAt] using hUpper
      · rw [interpretWith_pure]
        simp [RandCostM.deterministic]
  · rw [List.length_eraseIdx_of_lt index.isLt]
    simp [add_assoc]

theorem textbookQuicksort_joint_support_of_pivot [LinearOrder alpha]
    (first : alpha) (rest : List alpha)
    (index : Fin (first :: rest).length) (output : List alpha)
    (continuationCost : Nat) (hLong : ¬(first :: rest).length <= 3)
    (hContinuation : (output, continuationCost) ∈
      (interpret CostModel.textbookModel
        (quicksortContinuation (first :: rest) index)).joint.support) :
    (output, (first :: rest).length + continuationCost) ∈
      (textbookQuicksort (first :: rest)).joint.support := by
  unfold textbookQuicksort interpret
  rw [quicksortProgram, if_neg hLong, interpretWith_bind,
    interpretWith_choosePivotIndex_textbookModel]
  refine (mem_joint_support_bind_iff _ _ _ _).mpr ?_
  refine ⟨ULift.up index, (first :: rest).length, continuationCost, ?_, ?_, rfl⟩
  · exact mem_joint_support_sampleAtCost_of_mem _ _ _
      (PMF.mem_support_uniformOfFintype (ULift.up index))
  · simpa [quicksortContinuation, interpret] using hContinuation

/-- A Nat-valued quadratic cap for every supported textbook-cost branch. -/
def textbookRuntimeEnvelopeNat (n : Nat) : Nat :=
  2 * n.choose 2 + 2 * n + 1

theorem textbook_split_quadratic_bound (n lowerSize upperSize : Nat)
    (hPositive : 0 < n) (hSizes : lowerSize + upperSize = n - 1) :
    n + (n - 1) + textbookRuntimeEnvelopeNat lowerSize +
        textbookRuntimeEnvelopeNat upperSize <=
      textbookRuntimeEnvelopeNat n := by
  have hLowerShort : lowerSize < n := by omega
  have hUpperEq : upperSize = n - 1 - lowerSize := by omega
  have hSplit := comparison_split_quadratic_bound n lowerSize hLowerShort
  rw [← hUpperEq] at hSplit
  unfold textbookRuntimeEnvelopeNat
  omega

/-- Every supported branch of the approved textbook model is bounded by a quadratic envelope. -/
theorem textbookQuicksort_branch_cost_le [LinearOrder alpha]
    (input output : List alpha) (cost : Nat)
    (hMem : (output, cost) ∈ (textbookQuicksort input).joint.support) :
    cost <= textbookRuntimeEnvelopeNat input.length := by
  induction hInputLength : input.length using Nat.strong_induction_on
      generalizing input output cost with
  | h n ih =>
      subst hInputLength
      by_cases hSmall : input.length <= 3
      · have hCost := textbookQuicksort_joint_cost_eq_of_length_le_three
          input output cost hSmall hMem
        rw [hCost, smallComparisonCost_eq_choose_two input.length hSmall]
        unfold textbookRuntimeEnvelopeNat
        omega
      · cases input with
        | nil => simp at hSmall
        | cons first rest =>
            change (output, cost) ∈
              (interpretWith SemanticBackend.uniformLinearOrder
                CostModel.textbookModel
                (quicksortProgram (first :: rest))).joint.support at hMem
            rw [quicksortProgram, if_neg hSmall, interpretWith_bind,
              interpretWith_choosePivotIndex_textbookModel] at hMem
            obtain ⟨sampledIndex, pivotCost, continuationCost,
                hPivot, hContinuation, hCost⟩ :=
              (mem_joint_support_bind_iff _ _ _ _).mp hMem
            have hPivotCost : pivotCost = (first :: rest).length :=
              joint_support_sampleAtCost_cost_eq _ _ _ _ hPivot
            subst pivotCost
            change (output, continuationCost) ∈
              (interpret CostModel.textbookModel
                (quicksortContinuation (first :: rest)
                  sampledIndex.down)).joint.support at hContinuation
            obtain ⟨lowerOutput, lowerCost, upperOutput, upperCost,
                hLower, hUpper, hContinuationCost⟩ :=
              textbookQuicksortContinuation_joint_cost_decompose
                (first :: rest) sampledIndex.down output continuationCost
                hContinuation
            let source := first :: rest
            let index : Fin source.length := sampledIndex.down
            have hLowerShort := lowerSubproblem_length_lt source index
            have hUpperShort := upperSubproblem_length_lt source index
            have hLowerBound := ih (lowerSubproblem source index).length
              hLowerShort (lowerSubproblem source index) lowerOutput lowerCost hLower rfl
            have hUpperBound := ih (upperSubproblem source index).length
              hUpperShort (upperSubproblem source index) upperOutput upperCost hUpper rfl
            have hSizes := subproblem_lengths_add source index
            have hSplit := textbook_split_quadratic_bound source.length
              (lowerSubproblem source index).length
              (upperSubproblem source index).length
              (Nat.zero_lt_of_lt index.isLt) hSizes
            dsimp [source, index] at hCost hContinuationCost
            dsimp [source, index] at hLowerBound hUpperBound hSplit
            dsimp [source, index]
            omega

/-- Repeated minimum-rank pivots give a supported textbook-model branch with quadratic cost. -/
theorem textbookQuicksort_exists_quadratic_branch [LinearOrder alpha]
    (input : List alpha) (hNodup : input.Nodup) :
    ∃ output cost,
      (output, cost) ∈ (textbookQuicksort input).joint.support ∧
      input.length.choose 2 ≤ cost := by
  induction hInputLength : input.length using Nat.strong_induction_on
      generalizing input with
  | h n ih =>
      subst hInputLength
      by_cases hSmall : input.length ≤ 3
      · obtain ⟨branch, hBranch⟩ :=
          (textbookQuicksort input).joint.support_nonempty
        rcases branch with ⟨output, cost⟩
        have hCost := textbookQuicksort_joint_cost_eq_of_length_le_three
          input output cost hSmall hBranch
        refine ⟨output, cost, hBranch, ?_⟩
        rw [hCost, smallComparisonCost_eq_choose_two input.length hSmall]
        omega
      · cases input with
        | nil => simp at hSmall
        | cons first rest =>
            let source := first :: rest
            let zeroRank : Fin source.length := ⟨0, by simp [source]⟩
            let index : Fin source.length :=
              (pivotRankEquiv source hNodup).symm zeroRank
            have hRank : pivotRankEquiv source hNodup index = zeroRank :=
              (pivotRankEquiv source hNodup).apply_symm_apply zeroRank
            have hRankValue : (pivotRankEquiv source hNodup index).val = 0 :=
              congrArg Fin.val hRank
            have hLowerLength : (lowerSubproblem source index).length = 0 := by
              rw [lowerSubproblem_length source hNodup index]
              exact hRankValue
            have hUpperLength :
                (upperSubproblem source index).length = source.length - 1 := by
              rw [upperSubproblem_length source hNodup index, hRankValue]
              simp
            have hLowerShort := lowerSubproblem_length_lt source index
            have hUpperShort := upperSubproblem_length_lt source index
            obtain ⟨lowerOutput, lowerCost, hLower, hLowerCost⟩ :=
              ih (lowerSubproblem source index).length hLowerShort
                (lowerSubproblem source index)
                (lowerSubproblem_nodup source hNodup index) rfl
            obtain ⟨upperOutput, upperCost, hUpper, hUpperCost⟩ :=
              ih (upperSubproblem source index).length hUpperShort
                (upperSubproblem source index)
                (upperSubproblem_nodup source hNodup index) rfl
            have hContinuation :=
              textbookQuicksortContinuation_joint_support_of_recursive
                source index lowerOutput upperOutput lowerCost upperCost hLower hUpper
            have hPairCost :
                source.length - 1 +
                    (lowerSubproblem source index).length.choose 2 +
                    (upperSubproblem source index).length.choose 2 =
                  source.length.choose 2 := by
              rw [hLowerLength, hUpperLength]
              simp [source, Nat.choose_succ_succ, Nat.choose_one_right]
            have hContinuationLower :
                source.length.choose 2 ≤
                  source.length - 1 + lowerCost + upperCost := by
              omega
            have hTotalLower :
                source.length.choose 2 ≤
                  source.length +
                    (source.length - 1 + lowerCost + upperCost) := by
              omega
            refine ⟨lowerOutput ++ source.get index :: upperOutput,
              source.length + (source.length - 1 + lowerCost + upperCost), ?_, ?_⟩
            · simpa [source] using textbookQuicksort_joint_support_of_pivot
                first rest index (lowerOutput ++ source.get index :: upperOutput)
                (source.length - 1 + lowerCost + upperCost) hSmall hContinuation
            · simpa [source] using hTotalLower

/-- A cost belongs to some supported textbook-model branch on a distinct Nat input of size `n`. -/
def IsTextbookBranchCost (n cost : Nat) : Prop :=
  ∃ input output : List Nat,
    input.Nodup ∧ input.length = n ∧
    (output, cost) ∈ (textbookQuicksort input).joint.support

theorem isTextbookBranchCost_le {n cost : Nat}
    (h : IsTextbookBranchCost n cost) :
    cost ≤ textbookRuntimeEnvelopeNat n := by
  rcases h with ⟨input, output, _, hLength, hMem⟩
  simpa [hLength] using textbookQuicksort_branch_cost_le input output cost hMem

theorem exists_isTextbookBranchCost (n : Nat) :
    ∃ cost, IsTextbookBranchCost n cost := by
  obtain ⟨⟨output, cost⟩, hMem⟩ :=
    (textbookQuicksort (List.range n)).joint.support_nonempty
  exact ⟨cost, List.range n, output, List.nodup_range, by simp, hMem⟩

/-- The actual maximum supported textbook-model cost over distinct Nat inputs of size `n`. -/
noncomputable def worstTextbookRuntimeBySize (n : Nat) : Nat := by
  classical
  exact Nat.findGreatest (IsTextbookBranchCost n) (textbookRuntimeEnvelopeNat n)

theorem worstTextbookRuntimeBySize_le_envelope (n : Nat) :
    worstTextbookRuntimeBySize n ≤ textbookRuntimeEnvelopeNat n := by
  classical
  unfold worstTextbookRuntimeBySize
  exact Nat.findGreatest_le _

theorem isTextbookBranchCost_le_worst {n cost : Nat}
    (h : IsTextbookBranchCost n cost) :
    cost ≤ worstTextbookRuntimeBySize n := by
  classical
  unfold worstTextbookRuntimeBySize
  exact Nat.le_findGreatest (isTextbookBranchCost_le h) h

theorem worstTextbookRuntimeBySize_isBranchCost (n : Nat) :
    IsTextbookBranchCost n (worstTextbookRuntimeBySize n) := by
  classical
  obtain ⟨cost, hCost⟩ := exists_isTextbookBranchCost n
  unfold worstTextbookRuntimeBySize
  exact Nat.findGreatest_spec (isTextbookBranchCost_le hCost) hCost

theorem worstTextbookRuntimeBySize_isMaximum (n : Nat) :
    IsTextbookBranchCost n (worstTextbookRuntimeBySize n) ∧
      ∀ cost, IsTextbookBranchCost n cost →
        cost ≤ worstTextbookRuntimeBySize n :=
  ⟨worstTextbookRuntimeBySize_isBranchCost n,
    fun _ h => isTextbookBranchCost_le_worst h⟩

theorem choose_two_le_worstTextbookRuntimeBySize (n : Nat) :
    n.choose 2 ≤ worstTextbookRuntimeBySize n := by
  obtain ⟨output, cost, hMem, hLower⟩ :=
    textbookQuicksort_exists_quadratic_branch
      (List.range n) List.nodup_range
  have hLower' : n.choose 2 ≤ cost := by simpa using hLower
  have hBranch : IsTextbookBranchCost n cost :=
    ⟨List.range n, output, List.nodup_range, by simp, hMem⟩
  exact hLower'.trans (isTextbookBranchCost_le_worst hBranch)

theorem textbookRuntimeEnvelopeNat_isBigO :
    (fun n : Nat => (textbookRuntimeEnvelopeNat n : Real)) =O[atTop]
      (fun n : Nat => (n ^ 2 : Real)) := by
  refine IsBigO.of_bound 5
    (Filter.eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  have hChoose : n.choose 2 ≤ n ^ 2 := Nat.choose_le_pow n 2
  have hnSq : n ≤ n ^ 2 := by nlinarith
  have hOneSq : 1 ≤ n ^ 2 := hn.trans hnSq
  have hNat : textbookRuntimeEnvelopeNat n ≤ 5 * n ^ 2 := by
    unfold textbookRuntimeEnvelopeNat
    omega
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  exact_mod_cast hNat

/-- Kleinberg--Tardos p. 732: the actual worst supported textbook-model runtime is `Θ(n²)`. -/
theorem worstTextbookRuntimeBySize_isTheta :
    (fun n : Nat => (worstTextbookRuntimeBySize n : Real)) =Θ[atTop]
      (fun n : Nat => (n ^ 2 : Real)) := by
  have hWorstToEnvelope :
      (fun n : Nat => (worstTextbookRuntimeBySize n : Real)) =O[atTop]
        (fun n : Nat => (textbookRuntimeEnvelopeNat n : Real)) := by
    refine IsBigO.of_bound 1 (Filter.Eventually.of_forall fun n => ?_)
    simp only [Real.norm_eq_abs, one_mul]
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    exact_mod_cast worstTextbookRuntimeBySize_le_envelope n
  have hChooseToWorst :
      (fun n : Nat => (n.choose 2 : Real)) =O[atTop]
        (fun n : Nat => (worstTextbookRuntimeBySize n : Real)) := by
    refine IsBigO.of_bound 1 (Filter.Eventually.of_forall fun n => ?_)
    simp only [Real.norm_eq_abs, one_mul]
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    exact_mod_cast choose_two_le_worstTextbookRuntimeBySize n
  exact IsBigO.antisymm
    (hWorstToEnvelope.trans textbookRuntimeEnvelopeNat_isBigO)
    ((isTheta_choose 2).isBigO_symm.trans hChooseToWorst)

end

end Cslib.Textbooks.KleinbergTardos.Chapter13.RandomizedQuicksort
