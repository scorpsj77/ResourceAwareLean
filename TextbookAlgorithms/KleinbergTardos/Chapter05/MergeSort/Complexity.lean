/-
Copyright (c) 2026 Jiyuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan
-/
import TextbookAlgorithms.KleinbergTardos.Chapter05.MergeSort.Correctness
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic.Ring

/-!
# Kleinberg merge-sort cost recurrence

This file connects four levels of resource reasoning:

1. the generic runner measures comparisons, splits, merges, and base cases under a selected model;
2. one cost-independent operation-profile proof bounds the complete MergeSort trace;
3. Theorem 5.1 packages those costs as a recurrence with explicit implementation constants;
4. Theorem 5.2 solves that recurrence by Kleinberg's substitution proof.

Kleinberg assumes even problem sizes and suppresses floors and ceilings.  The substitution theorem
therefore states the result for `n = 2^k`, where both recursive subproblems have size exactly
`n / 2`.  The explicit bound is stronger and more precise than merely writing `O(n log n)`.
-/

universe u

namespace KleinbergMergeSort

open ResourceAware ResourceAware.Algorithms
open Filter Asymptotics

/-! ## Cost-independent operation profile -/

/-- One merge performs at most one weighted comparison per input element. -/
theorem mergeCore_weightedOperationCost_le {α : Type u} [LinearOrder α]
    (model : CostModel α) (bounds : CostBounds) (xs ys : List α) :
    ResourceAware.Program.weightedOperationCost (operationCharge bounds)
      (interpret model (mergeCore xs ys)) ≤
        bounds.comparison * (xs.length + ys.length) := by
  fun_induction mergeCore with
  | case1 => simp
  | case2 => simp
  | case3 x xs y ys ihLeft ihRight =>
      simp only [weightedOperationCost_interpret_bind]
      rw [eval_request, weightedOperationCost_interpret_request]
      simp only [operationCharge, List.length_cons]
      split <;> simp_all [Nat.mul_add] <;> omega

/-- A merge profile contains one structural merge and its actual comparisons. -/
theorem merge_weightedOperationCost_le {α : Type u} [LinearOrder α]
    (model : CostModel α) (bounds : CostBounds) (xs ys : List α) :
    ResourceAware.Program.weightedOperationCost (operationCharge bounds)
      (interpret model (merge xs ys)) ≤
        bounds.mergeUnit * (xs.length + ys.length) +
          bounds.comparison * (xs.length + ys.length) := by
  simp only [merge, weightedOperationCost_interpret_bind]
  rw [weightedOperationCost_interpret_request]
  simp only [operationCharge]
  exact Nat.add_le_add_left
    (mergeCore_weightedOperationCost_le model bounds xs ys) _

/-- Every executable base-case profile is bounded by the recurrence coefficient. -/
theorem sortBase_weightedOperationCost_le {α : Type u} [LinearOrder α]
    (model : CostModel α) (bounds : CostBounds) (xs : List α) (hsize : xs.length ≤ 2) :
    ResourceAware.Program.weightedOperationCost (operationCharge bounds)
      (interpret model (sortBase xs)) ≤ bounds.recurrenceCoefficient := by
  rcases xs with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩
  · simp only [sortBase, weightedOperationCost_interpret_bind]
    rw [weightedOperationCost_interpret_request]
    simp [operationCharge, CostBounds.recurrenceCoefficient]
    omega
  · simp only [sortBase, weightedOperationCost_interpret_bind]
    rw [weightedOperationCost_interpret_request]
    simp [operationCharge, CostBounds.recurrenceCoefficient]
    omega
  · by_cases h : x ≤ y
    all_goals
      simp only [sortBase, weightedOperationCost_interpret_bind]
      repeat rw [weightedOperationCost_interpret_request]
      repeat rw [eval_request]
      simp [h, operationCharge, CostBounds.recurrenceCoefficient]
      omega
  · simp at hsize

@[simp] theorem eval_mergeSort_length {α : Type u} [LinearOrder α] (xs : List α) :
    (eval (mergeSort xs)).length = xs.length :=
  (mergeSort_correct xs).2.length_eq

/-- One recursive MergeSort operation profile obeys the textbook cost decomposition. -/
theorem mergeSort_weightedOperationCost_step {α : Type u} [LinearOrder α]
    (model : CostModel α) (bounds : CostBounds) (xs : List α) (hsize : 2 < xs.length) :
    ResourceAware.Program.weightedOperationCost (operationCharge bounds)
        (interpret model (mergeSort xs) : TraceM (Event α) (List α × PUnit.{u + 1})) ≤
      ResourceAware.Program.weightedOperationCost (operationCharge bounds)
          (interpret model (mergeSort (xs.take (xs.length / 2))) :
            TraceM (Event α) (List α × PUnit.{u + 1})) +
        ResourceAware.Program.weightedOperationCost (operationCharge bounds)
          (interpret model (mergeSort (xs.drop (xs.length / 2))) :
            TraceM (Event α) (List α × PUnit.{u + 1})) +
        bounds.recurrenceCoefficient * xs.length := by
  have hbranch : ¬xs.length ≤ 2 := by omega
  rw [mergeSort]
  simp only [hbranch, if_false, weightedOperationCost_interpret_bind]
  rw [weightedOperationCost_interpret_request]
  simp only [operationCharge]
  have hparts : (xs.take (xs.length / 2)).length +
      (xs.drop (xs.length / 2)).length = xs.length := by
    simp [List.length_take, List.length_drop]
    omega
  have hmerge := merge_weightedOperationCost_le model bounds
    (eval (mergeSort (xs.take (xs.length / 2))))
    (eval (mergeSort (xs.drop (xs.length / 2))))
  simp only [eval_mergeSort_length, hparts] at hmerge
  simp only [CostBounds.recurrenceCoefficient, Nat.add_mul]
  omega

/-! ## Kleinberg Theorem 5.1 -/

/--
The recurrence assumptions in Kleinberg Theorem 5.1.

The `Even n` premise records the textbook convention that both recursive calls have size `n / 2`.
The fully general executable algorithm instead uses `floor (n / 2)` and `ceil (n / 2)`.
-/
structure SatisfiesRecurrence (T : Nat → Nat) (c : Nat) : Prop where
  base : T 2 ≤ c
  step : ∀ n, 2 < n → Even n → T n ≤ 2 * T (n / 2) + c * n

/-- A recurrence upper bound whose non-base branch is exactly Kleinberg Theorem 5.1. -/
def traceWorstCase (c : Nat) : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => c
  | n + 3 => 2 * traceWorstCase c ((n + 3) / 2) + c * (n + 3)
termination_by n => n
decreasing_by omega

theorem traceWorstCase_eq (c n : Nat) (h : 2 < n) :
    traceWorstCase c n = 2 * traceWorstCase c (n / 2) + c * n := by
  rcases n with _ | _ | _ | n <;> simp_all [traceWorstCase]

theorem traceWorstCase_satisfies (c : Nat) : SatisfiesRecurrence (traceWorstCase c) c := by
  constructor
  · simp [traceWorstCase]
  · intro n hn _
    rcases n with _ | _ | _ | n <;> simp_all [traceWorstCase]

/-! ## Kleinberg Theorem 5.2: substitution -/

/-- A positive power of two is even. -/
private theorem even_two_pow_succ (k : Nat) : Even (2 ^ (k + 1)) := by
  refine ⟨2 ^ k, ?_⟩
  rw [pow_succ]
  omega

/-- Halving `2^(k+1)` gives `2^k` exactly. -/
private theorem two_pow_succ_div_two (k : Nat) : 2 ^ (k + 1) / 2 = 2 ^ k := by
  rw [pow_succ]
  omega

/-- For `k ≥ 1`, the next power of two is strictly larger than the base-case size. -/
private theorem two_lt_two_pow_succ {k : Nat} (hk : 1 ≤ k) : 2 < 2 ^ (k + 1) := by
  have hpow : 2 ^ 2 ≤ 2 ^ (k + 1) :=
    Nat.pow_le_pow_right (by omega : 0 < 2) (by omega)
  norm_num at hpow ⊢
  omega

/--
Kleinberg Theorem 5.2, proved by substitution.

For an input size `n = 2^k`, `k` is `log₂ n`; hence this explicit inequality is the textbook
`T(n) = O(n log n)` bound.  The induction step literally substitutes the hypothesis for
`T(n / 2)` into Theorem 5.1 and simplifies `log₂(n / 2) = log₂ n - 1` through the exponent `k`.
-/
theorem theorem_5_2_substitution {T : Nat → Nat} {c : Nat}
    (hrec : SatisfiesRecurrence T c) :
    ∀ k, 1 ≤ k → T (2 ^ k) ≤ c * (2 ^ k) * k := by
  intro k
  induction k with
  | zero => omega
  | succ k ih =>
      intro hk
      by_cases hkzero : k = 0
      · subst k
        norm_num
        exact hrec.base.trans (by omega)
      · have hkpos : 1 ≤ k := by omega
        have ihk := ih hkpos
        calc
          T (2 ^ (k + 1)) ≤
              2 * T (2 ^ (k + 1) / 2) + c * (2 ^ (k + 1)) :=
            hrec.step (2 ^ (k + 1)) (two_lt_two_pow_succ hkpos)
              (even_two_pow_succ k)
          _ = 2 * T (2 ^ k) + c * (2 ^ (k + 1)) := by
            rw [two_pow_succ_div_two]
          _ ≤ 2 * (c * (2 ^ k) * k) + c * (2 ^ (k + 1)) := by
            exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 ihk) _
          _ = c * (2 ^ (k + 1)) * (k + 1) := by
            rw [pow_succ]
            ring

/--
Kleinberg Theorem 5.2 as a Mathlib `IsBigO` statement along power-of-two input sizes.

The index `k` represents inputs of size `n = 2^k`, so the comparison function
`2^k * k` is exactly `n log₂ n`.
-/
theorem theorem_5_2_isBigO {T : Nat → Nat} {c : Nat}
    (hrec : SatisfiesRecurrence T c) :
    (fun k : Nat ↦ (T (2 ^ k) : Real)) =O[atTop]
      fun k ↦ ((2 ^ k : Nat) : Real) * k := by
  refine IsBigO.of_bound (c : Real) (Filter.eventually_atTop.2 ⟨1, fun k hk ↦ ?_⟩)
  have hbound := theorem_5_2_substitution hrec k hk
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg, abs_of_nonneg]
  · have hbound' : T (2 ^ k) ≤ c * (2 ^ k * k) := by
      simpa [mul_assoc] using hbound
    exact_mod_cast hbound'
  · positivity
  · positivity

/-! ## End-to-end trace bound -/

/-- On power-of-two inputs, the cost-independent operation profile obeys the recurrence. -/
theorem mergeSort_weightedOperationCost_le_traceWorstCase {α : Type u} [LinearOrder α]
    (model : CostModel α) (bounds : CostBounds) :
    ∀ k, 1 ≤ k → ∀ xs : List α, xs.length = 2 ^ k →
      ResourceAware.Program.weightedOperationCost (operationCharge bounds)
          (interpret model (mergeSort xs) : TraceM (Event α) (List α × PUnit.{u + 1})) ≤
        traceWorstCase bounds.recurrenceCoefficient (2 ^ k) := by
  intro k
  induction k with
  | zero => omega
  | succ k ih =>
      intro hk xs hlength
      by_cases hkzero : k = 0
      · subst k
        have hbase : xs.length ≤ 2 := by norm_num at hlength ⊢; omega
        rw [mergeSort]
        simp only [hbase, if_true]
        simpa [traceWorstCase] using
          sortBase_weightedOperationCost_le model bounds xs hbase
      · have hkpos : 1 ≤ k := by omega
        have hsize : 2 < xs.length := by
          rw [hlength]
          exact two_lt_two_pow_succ hkpos
        have hhalf : xs.length / 2 = 2 ^ k := by
          rw [hlength, two_pow_succ_div_two]
        have hleftLength : (xs.take (xs.length / 2)).length = 2 ^ k := by
          simp [List.length_take, hlength, pow_succ]
        have hrightLength : (xs.drop (xs.length / 2)).length = 2 ^ k := by
          rw [List.length_drop, hhalf, hlength, pow_succ]
          omega
        have hleft := ih hkpos (xs.take (xs.length / 2)) hleftLength
        have hright := ih hkpos (xs.drop (xs.length / 2)) hrightLength
        calc
          _ ≤ _ :=
            mergeSort_weightedOperationCost_step model bounds xs hsize
          _ ≤ traceWorstCase bounds.recurrenceCoefficient (2 ^ k) +
              traceWorstCase bounds.recurrenceCoefficient (2 ^ k) +
                bounds.recurrenceCoefficient * (2 ^ (k + 1)) := by
            exact Nat.add_le_add (Nat.add_le_add hleft hright)
              (Nat.mul_le_mul_left _ (Nat.le_of_eq hlength))
          _ = traceWorstCase bounds.recurrenceCoefficient (2 ^ (k + 1)) := by
            rw [traceWorstCase_eq _ _ (two_lt_two_pow_succ hkpos),
              two_pow_succ_div_two]
            ring

/-- Any bounded MergeSort cost model is controlled by the same operation-profile recurrence. -/
theorem mergeSort_exactCost_le_traceWorstCase {α : Type u} [LinearOrder α]
    (model : CostModel α) (bounds : CostBounds) (hbounded : model.IsBoundedBy bounds) :
    ∀ k, 1 ≤ k → ∀ xs : List α, xs.length = 2 ^ k →
      exactCost (interpret model (mergeSort xs) :
        TraceM (Event α) (List α × PUnit.{u + 1})) ≤
      traceWorstCase bounds.recurrenceCoefficient (2 ^ k) := by
  intro k hk xs hlength
  have hcost := exactCost_interpretWith_le_weightedOperationCost
    Sorting.ComparisonBackend.linearOrder model bounds hbounded (mergeSort xs)
  have hprofile :=
    mergeSort_weightedOperationCost_le_traceWorstCase model bounds k hk xs hlength
  have hcost' : exactCost (interpret model (mergeSort xs) :
      TraceM (Event α) (List α × PUnit.{u + 1})) ≤
      ResourceAware.Program.weightedOperationCost (operationCharge bounds)
        (interpret model (mergeSort xs) :
          TraceM (Event α) (List α × PUnit.{u + 1})) := by
    simpa [interpret] using hcost
  exact hcost'.trans hprofile

/-- Every bounded MergeSort model satisfies the explicit `c n log₂ n` bound. -/
theorem mergeSort_exactCost_le_bounded {α : Type u} [LinearOrder α]
    (model : CostModel α) (bounds : CostBounds) (hbounded : model.IsBoundedBy bounds)
    (k : Nat) (hk : 1 ≤ k) (xs : List α) (hlength : xs.length = 2 ^ k) :
    exactCost (interpret model (mergeSort xs) :
      TraceM (Event α) (List α × PUnit.{u + 1})) ≤
      bounds.recurrenceCoefficient * xs.length * k := by
  rw [hlength]
  exact (mergeSort_exactCost_le_traceWorstCase model bounds hbounded k hk xs hlength).trans
    (theorem_5_2_substitution (traceWorstCase_satisfies bounds.recurrenceCoefficient) k hk)

/--
The exact measured cost of bounded-model MergeSort is `O(n log₂ n)` along any family of
power-of-two-sized inputs.

The function is indexed by `k`, with `(inputs k).length = 2^k`; hence the comparison function
`2^k * k` is `n log₂ n`.
-/
theorem mergeSort_exactCost_isBigO_on_powersOfTwo {α : Type u} [LinearOrder α]
    (model : CostModel α) (bounds : CostBounds) (hbounded : model.IsBoundedBy bounds)
    (inputs : Nat → List α) (hlength : ∀ k, (inputs k).length = 2 ^ k) :
    (fun k : Nat ↦
      (exactCost (interpret model (mergeSort (inputs k)) :
        TraceM (Event α) (List α × PUnit.{u + 1})) : Real)) =O[atTop]
      fun k ↦ ((2 ^ k : Nat) : Real) * k := by
  refine IsBigO.of_bound (bounds.recurrenceCoefficient : Real)
    (Filter.eventually_atTop.2 ⟨1, fun k hk ↦ ?_⟩)
  have hbound := mergeSort_exactCost_le_bounded model bounds hbounded
    k hk (inputs k) (hlength k)
  rw [hlength k] at hbound
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg, abs_of_nonneg]
  · have hbound' :
        exactCost (interpret model (mergeSort (inputs k)) :
          TraceM (Event α) (List α × PUnit.{u + 1})) ≤
          bounds.recurrenceCoefficient * (2 ^ k * k) := by
      simpa [mul_assoc] using hbound
    exact_mod_cast hbound'
  · positivity
  · positivity

/-- The linear Kleinberg model is one specialization of the general bounded-cost theorem. -/
theorem mergeSort_exactCost_le {α : Type u} [LinearOrder α]
    (comparisonUnit splitUnit mergeUnit k : Nat) (hk : 1 ≤ k)
    (xs : List α) (hlength : xs.length = 2 ^ k) :
    exactCost (interpret (CostModel.linearKleinberg comparisonUnit splitUnit mergeUnit)
      (mergeSort xs) : TraceM (Event α) (List α × PUnit.{u + 1})) ≤
      CostModel.kleinbergCoefficient comparisonUnit splitUnit mergeUnit * xs.length * k := by
  simpa using mergeSort_exactCost_le_bounded
    (CostModel.linearKleinberg comparisonUnit splitUnit mergeUnit)
    (CostModel.linearKleinbergBounds comparisonUnit splitUnit mergeUnit)
    (CostModel.linearKleinberg_isBoundedBy comparisonUnit splitUnit mergeUnit)
    k hk xs hlength

end KleinbergMergeSort
