/-
Copyright (c) 2026 James Needham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Needham
-/

import TextbookAlgorithms.KleinbergTardos.Chapter13.RandomizedQuicksort.Interpreters
import ResourceAware.Algorithms.Sorting.Specification

/-!
# Correctness of Kleinberg--Tardos randomized Quicksort

The proofs in this file apply to the result marginal of the actual free-program interpreter.
Random pivot choices may change the execution branch and its cost, but every supported result is
a sorted permutation of the input.
-/

namespace Cslib.Textbooks.KleinbergTardos.Chapter13.RandomizedQuicksort

open Cslib.Algorithms.Lean
open ResourceAware.Program
open ResourceAware.Algorithms
open List

noncomputable section

variable {alpha : Type}

/-- Order facts established by one interpreted partitioning pass. -/
def PartitionCorrect [LE alpha] (pivot : alpha) {input : List alpha}
    (parts : PartitionResult input) : Prop :=
  And (forall value, value ∈ parts.lower -> value <= pivot)
    (forall value, value ∈ parts.upper -> pivot <= value)

/-- Every result supported by the linear-order partition interpreter lies on the proper side of
the pivot. The permutation component is already carried by `PartitionResult`. -/
theorem partitionProgram_support_correct [LinearOrder alpha] (pivot : alpha) :
    forall (input : List alpha) (parts : PartitionResult input),
      parts ∈ (eval (partitionProgram pivot input)).support ->
        PartitionCorrect pivot parts := by
  intro input
  induction input with
  | nil =>
      intro parts hparts
      simp [partitionProgram, eval, evalWith] at hparts
      subst parts
      simp [PartitionCorrect]
  | cons value rest ih =>
      intro parts hparts
      change parts ∈
        (evalWith SemanticBackend.uniformLinearOrder
          (partitionProgram pivot (value :: rest))).support at hparts
      rw [partitionProgram, evalWith_bind, evalWith_compareLE] at hparts
      obtain ⟨answer, hanswer, hparts⟩ :=
        (PMF.mem_support_bind_iff _ _ _).mp hparts
      rw [PMF.mem_support_pure_iff] at hanswer
      subst answer
      rw [evalWith_bind] at hparts
      by_cases hle : value <= pivot
      · simp only [SemanticBackend.uniformLinearOrder,
          Sorting.ComparisonBackend.linearOrder, hle, decide_true, ↓reduceIte,
          evalWith_pure, PMF.mem_support_iff, ne_eq] at hparts
        obtain ⟨restParts, hrestParts, hparts⟩ :=
          (PMF.mem_support_bind_iff _ _ _).mp hparts
        rw [PMF.mem_support_pure_iff] at hparts
        subst parts
        have hrest := ih restParts hrestParts
        exact ⟨by simpa [PartitionCorrect] using And.intro hle hrest.1,
          hrest.2⟩
      · simp only [SemanticBackend.uniformLinearOrder,
          Sorting.ComparisonBackend.linearOrder, hle, decide_false,
          Bool.false_eq_true, ↓reduceIte, evalWith_pure, PMF.mem_support_iff,
          ne_eq] at hparts
        obtain ⟨restParts, hrestParts, hparts⟩ :=
          (PMF.mem_support_bind_iff _ _ _).mp hparts
        rw [PMF.mem_support_pure_iff] at hparts
        subst parts
        have hrest := ih restParts hrestParts
        exact ⟨hrest.1, by
          intro other hmem
          simp only [List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · exact le_of_not_ge hle
          · exact hrest.2 other hmem⟩

/-! ## Correctness of the constant-size sorting network -/

/-- Evaluation preserves the functorial map of a free program. -/
theorem evalWith_map (backend : SemanticBackend alpha) (f : beta -> gamma)
    (program : Program alpha beta) :
    evalWith backend (f <$> program) = (evalWith backend program).map f := by
  rw [map_eq_pure_bind, evalWith_bind]
  change PMF.bind (evalWith backend program)
      (fun value => PMF.pure (f value)) = _
  simpa [Function.comp_def] using PMF.bind_pure_comp f (evalWith backend program)

/-- Evaluation turns syntax-level right sequencing into probabilistic bind. -/
theorem evalWith_seqRight (backend : SemanticBackend alpha)
    (program : Program alpha beta) (next : Program alpha gamma) :
    evalWith backend (program *> next) =
      (evalWith backend program >>= fun _ => evalWith backend next) := by
  rw [seqRight_eq_bind, evalWith_bind]

/-- The type-class presentation of PMF bind has the expected pure-left law. -/
@[simp] theorem pmf_pure_bind_local (value : beta) (next : beta -> PMF gamma) :
    ((pure value : PMF beta) >>= next) = next value := by
  change PMF.bind (PMF.pure value) next = next value
  exact PMF.pure_bind value next

/-- One interpreted compare-and-swap returns an ordered permutation of its inputs. -/
theorem compareSwap_support_correct [LinearOrder alpha]
    (left right : alpha) (pair : alpha × alpha)
    (hpair : pair ∈ (eval (compareSwap left right)).support) :
    pair.1 <= pair.2 ∧ [pair.1, pair.2].Perm [left, right] := by
  rw [eval, evalWith_compareSwap, PMF.mem_support_pure_iff] at hpair
  by_cases hle : left <= right
  · simp only [SemanticBackend.uniformLinearOrder,
      Sorting.ComparisonBackend.linearOrder, hle, decide_true, ↓reduceIte] at hpair
    subst pair
    exact ⟨hle, .refl _⟩
  · have hright : right <= left := le_of_not_ge hle
    simp only [SemanticBackend.uniformLinearOrder,
      Sorting.ComparisonBackend.linearOrder, hle, decide_false,
      Bool.false_eq_true, ↓reduceIte] at hpair
    subst pair
    exact ⟨hright, List.Perm.swap _ _ []⟩

/-- The fixed network used for textbook base cases returns a sorted permutation. -/
theorem sortSmallProgram_support_correct [LinearOrder alpha]
    (input output : List alpha)
    (hLength : input.length <= 3)
    (hOutput : output ∈ (eval (sortSmallProgram input)).support) :
    Sorting.Correct input output := by
  rcases input with _ | ⟨first, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, rest⟩⟩⟩⟩
  · have h : output = [] := by
      simpa [sortSmallProgram, eval, evalWith_bind, evalWith_map,
        evalWith_seqRight] using hOutput
    subst output
    simp [Sorting.Correct, Sorting.IsSorted]
  · have h : output = [first] := by
      simpa [sortSmallProgram, eval, evalWith_bind, evalWith_map,
        evalWith_seqRight] using hOutput
    subst output
    simp [Sorting.Correct, Sorting.IsSorted]
  · change output ∈
      (evalWith SemanticBackend.uniformLinearOrder
        (sortSmallProgram [first, second])).support at hOutput
    rw [sortSmallProgram, evalWith_bind, evalWith_markBaseCase] at hOutput
    change output ∈ (PMF.bind (PMF.pure PUnit.unit) _).support at hOutput
    rw [PMF.pure_bind] at hOutput
    by_cases hle : first <= second
    · have h : output = [first, second] := by
        simpa [evalWith_map,
          SemanticBackend.uniformLinearOrder,
          Sorting.ComparisonBackend.linearOrder, hle] using hOutput
      subst output
      simp [Sorting.Correct, Sorting.IsSorted, hle]
    · have hright : second <= first := le_of_not_ge hle
      have h : output = [second, first] := by
        simpa [evalWith_map,
          SemanticBackend.uniformLinearOrder,
          Sorting.ComparisonBackend.linearOrder, hle] using hOutput
      subst output
      exact ⟨by simpa [Sorting.IsSorted] using hright,
        List.Perm.swap _ _ []⟩
  · change output ∈
      (evalWith SemanticBackend.uniformLinearOrder
        (sortSmallProgram [first, second, third])).support at hOutput
    rw [sortSmallProgram, evalWith_bind, evalWith_markBaseCase] at hOutput
    change output ∈ (PMF.bind (PMF.pure PUnit.unit) _).support at hOutput
    rw [PMF.pure_bind] at hOutput
    rw [evalWith_bind] at hOutput
    obtain ⟨firstPair, hFirstPair, hOutput⟩ :=
      (PMF.mem_support_bind_iff _ _ _).mp hOutput
    rw [evalWith_bind] at hOutput
    obtain ⟨secondPair, hSecondPair, hOutput⟩ :=
      (PMF.mem_support_bind_iff _ _ _).mp hOutput
    rw [evalWith_bind] at hOutput
    obtain ⟨thirdPair, hThirdPair, hOutput⟩ :=
      (PMF.mem_support_bind_iff _ _ _).mp hOutput
    rw [evalWith_pure, PMF.mem_support_pure_iff] at hOutput
    subst output
    have hFirst := compareSwap_support_correct first second firstPair hFirstPair
    have hSecond :=
      compareSwap_support_correct firstPair.2 third secondPair hSecondPair
    have hThird :=
      compareSwap_support_correct firstPair.1 secondPair.1 thirdPair hThirdPair
    have hFirstToLast : firstPair.1 <= secondPair.2 := by
      have hmem : firstPair.2 ∈ [secondPair.1, secondPair.2] :=
        hSecond.2.mem_iff.mpr (by simp)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with hmem | hmem
      · calc
          firstPair.1 <= firstPair.2 := hFirst.1
          _ = secondPair.1 := hmem
          _ <= secondPair.2 := hSecond.1
      · calc
          firstPair.1 <= firstPair.2 := hFirst.1
          _ = secondPair.2 := hmem
    have hThirdToLast : thirdPair.2 <= secondPair.2 := by
      have hmem : thirdPair.2 ∈ [firstPair.1, secondPair.1] :=
        hThird.2.mem_iff.mp (by simp)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with hmem | hmem
      · rw [hmem]
        exact hFirstToLast
      · rw [hmem]
        exact hSecond.1
    constructor
    · simpa [Sorting.IsSorted] using
        And.intro (And.intro hThird.1 (hThird.1.trans hThirdToLast))
          hThirdToLast
    · calc
        [thirdPair.1, thirdPair.2, secondPair.2] ~
            [firstPair.1, secondPair.1, secondPair.2] :=
          hThird.2.append (.refl [secondPair.2])
        _ ~ [firstPair.1, firstPair.2, third] := hSecond.2.cons firstPair.1
        _ ~ [first, second, third] := hFirst.2.append (.refl [third])
  · simp only [List.length_cons] at hLength
    omega

/-! ## Recursive Quicksort correctness -/

/-- Correct recursive results can be joined around a certified partition pivot. -/
theorem join_correct [LinearOrder alpha] {input remainder : List alpha} (pivot : alpha)
    (parts : PartitionResult remainder) (sortedLower sortedUpper : List alpha)
    (hPartition : PartitionCorrect pivot parts)
    (hLower : Sorting.Correct parts.lower sortedLower)
    (hUpper : Sorting.Correct parts.upper sortedUpper)
    (hPivot : (pivot :: remainder).Perm input) :
    Sorting.Correct input (sortedLower ++ pivot :: sortedUpper) := by
  have hLowerOrder : forall value, value ∈ sortedLower -> value <= pivot := by
    intro value hmem
    exact hPartition.1 value (hLower.2.mem_iff.mp hmem)
  have hUpperOrder : forall value, value ∈ sortedUpper -> pivot <= value := by
    intro value hmem
    exact hPartition.2 value (hUpper.2.mem_iff.mp hmem)
  constructor
  · change List.Pairwise (fun left right : alpha => left <= right)
      (sortedLower ++ pivot :: sortedUpper)
    rw [List.pairwise_append, List.pairwise_cons]
    refine ⟨hLower.1, ⟨hUpperOrder, hUpper.1⟩, ?_⟩
    intro lowerValue hLowerMem upperValue hUpperMem
    simp only [List.mem_cons] at hUpperMem
    rcases hUpperMem with rfl | hUpperMem
    · exact hLowerOrder lowerValue hLowerMem
    · exact (hLowerOrder lowerValue hLowerMem).trans
        (hUpperOrder upperValue hUpperMem)
  · calc
      sortedLower ++ pivot :: sortedUpper ~
          parts.lower ++ pivot :: parts.upper :=
        hLower.2.append (hUpper.2.cons pivot)
      _ ~ pivot :: (parts.lower ++ parts.upper) := List.perm_middle
      _ ~ pivot :: remainder := parts.perm.cons pivot
      _ ~ input := hPivot

/--
Kleinberg--Tardos, Section 13.5, pages 731--732: every result supported by the
uniform-pivot free-program interpretation is a sorted permutation of its input.
-/
theorem quicksortProgram_support_correct [LinearOrder alpha]
    (input output : List alpha)
    (hOutput : output ∈ (eval (quicksortProgram input)).support) :
    Sorting.Correct input output := by
  induction hInputLength : input.length using Nat.strong_induction_on
      generalizing input output with
  | h n ih =>
      subst hInputLength
      cases input with
      | nil =>
          rw [quicksortProgram] at hOutput
          exact sortSmallProgram_support_correct [] output (by simp) hOutput
      | cons first rest =>
          by_cases hLength : (first :: rest).length <= 3
          · rw [quicksortProgram, if_pos hLength] at hOutput
            exact sortSmallProgram_support_correct
              (first :: rest) output hLength hOutput
          · change output ∈
              (evalWith SemanticBackend.uniformLinearOrder
                (quicksortProgram (first :: rest))).support at hOutput
            rw [quicksortProgram, if_neg hLength, evalWith_bind] at hOutput
            obtain ⟨sampledIndex, hSampledIndex, hOutput⟩ :=
              (PMF.mem_support_bind_iff _ _ _).mp hOutput
            rw [evalWith_bind] at hOutput
            obtain ⟨parts, hParts, hOutput⟩ :=
              (PMF.mem_support_bind_iff _ _ _).mp hOutput
            rw [evalWith_bind] at hOutput
            obtain ⟨sortedLower, hSortedLower, hOutput⟩ :=
              (PMF.mem_support_bind_iff _ _ _).mp hOutput
            rw [evalWith_bind] at hOutput
            obtain ⟨sortedUpper, hSortedUpper, hOutput⟩ :=
              (PMF.mem_support_bind_iff _ _ _).mp hOutput
            rw [evalWith_pure, PMF.mem_support_pure_iff] at hOutput
            subst output
            let pivot := (first :: rest).get sampledIndex.down
            let remainder := (first :: rest).eraseIdx sampledIndex.down
            have hPartition : PartitionCorrect pivot parts :=
              partitionProgram_support_correct pivot remainder parts hParts
            have hErase : remainder.length + 1 = (first :: rest).length :=
              List.length_eraseIdx_add_one sampledIndex.down.isLt
            have hPartsLength :
                parts.lower.length + parts.upper.length = remainder.length := by
              simpa using parts.perm.length_eq
            have hLowerShort : parts.lower.length < (first :: rest).length := by
              omega
            have hUpperShort : parts.upper.length < (first :: rest).length := by
              omega
            have hLowerCorrect : Sorting.Correct parts.lower sortedLower :=
              ih parts.lower.length hLowerShort parts.lower sortedLower
                hSortedLower rfl
            have hUpperCorrect : Sorting.Correct parts.upper sortedUpper :=
              ih parts.upper.length hUpperShort parts.upper sortedUpper
                hSortedUpper rfl
            exact join_correct pivot parts sortedLower sortedUpper hPartition
              hLowerCorrect hUpperCorrect
              (List.getElem_cons_eraseIdx_perm sampledIndex.down.isLt)

/-- Kleinberg--Tardos, pp. 731--732 (unnumbered): every supported result of the actual
comparison-counting `RandCostM` runner is a sorted permutation of the input. -/
theorem quicksort_result_correct [LinearOrder alpha]
    (input output : List alpha) (_hNodup : input.Nodup)
    (hOutput : output ∈ (quicksort input).ret.support) :
    Sorting.Correct input output := by
  change output ∈
    (interpret CostModel.comparisonOnly (quicksortProgram input)).ret.support at hOutput
  rw [interpret_ret_eq_eval] at hOutput
  exact quicksortProgram_support_correct input output hOutput

/-- Every result-cost branch of the default runner returns a correct sorting result. -/
theorem quicksort_joint_support_correct [LinearOrder alpha]
    (input output : List alpha) (cost : Nat)
    (_hNodup : input.Nodup)
    (hOutput : (output, cost) ∈ (quicksort input).joint.support) :
    Sorting.Correct input output := by
  apply quicksort_result_correct input output _hNodup
  unfold RandCostM.ret
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨(output, cost), hOutput, rfl⟩

end

end Cslib.Textbooks.KleinbergTardos.Chapter13.RandomizedQuicksort
