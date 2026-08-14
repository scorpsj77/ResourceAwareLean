/-
Copyright (c) 2026 Jiyuan (Chai Yuen) Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan (Chai Yuen) Ji
-/
import TextbookAlgorithms.KleinbergTardos.Chapter05.MergeSort.ResourceModel
import ResourceAware.Algorithms.Sorting.Specification

/-!
# Functional correctness of Kleinberg merge sort

Correctness is first proved against the pure linear-order interpreter, then transferred to every
measured interpretation through an observation-erasure theorem.  No recurrence or asymptotic
argument is needed for these functional-correctness statements.
-/

universe u

namespace KleinbergMergeSort

open ResourceAware ResourceAware.Algorithms
open List

variable {α : Type u} [LinearOrder α]

/-- The abstract comparison-based merge computes mathlib's pure list merge. -/
@[simp, grind =]
theorem eval_mergeCore (xs ys : List α) :
    eval (mergeCore xs ys) = xs.merge ys := by
  fun_induction mergeCore with
  | case1 => simp
  | case2 => simp
  | case3 x xs y ys ihLeft ihRight =>
      by_cases h : x ≤ y
      · rw [eval_bind, eval_request]
        simp [h, ihLeft]
      · rw [eval_bind, eval_request]
        simp [h, ihRight]

/-- The outer merge observation does not change the merged result. -/
@[simp]
theorem eval_merge (xs ys : List α) :
    eval (merge xs ys) = xs.merge ys := by
  simp [merge]

/-- Sorting a size-at-most-two base case produces a sorted permutation. -/
theorem sortBase_correct (xs : List α) (hsize : xs.length ≤ 2) :
    Sorting.Correct xs (eval (sortBase xs)) := by
  /- four cases: empty, singleton, [x,y], [x :: y :: z :: rest] -/
  rcases xs with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩
  · simp [sortBase, Sorting.Correct, Sorting.IsSorted]
  · simp [sortBase, Sorting.Correct, Sorting.IsSorted]
  · by_cases h : x ≤ y
    · simp only [sortBase, eval_bind]
      rw [eval_request]
      simp [h, Sorting.Correct, Sorting.IsSorted]
    · have hyx : y ≤ x := le_of_not_ge h
      simp only [sortBase, eval_bind]
      rw [eval_request]
      simp [h, hyx, Sorting.Correct, Sorting.IsSorted, List.Perm.swap]
  /- impossible case since we assume xs.length <= 2. -/
  · simp at hsize

/-- Kleinberg merge sort returns a sorted permutation of its input. -/
theorem mergeSort_correct (xs : List α) :
    Sorting.Correct xs (eval (mergeSort xs)) := by
  fun_induction mergeSort xs with
  | case1 xs hsize =>
      exact sortBase_correct xs hsize
  | case2 xs hsize ihLeft ihRight =>
      let half := xs.length / 2
      let left := xs.take half
      let right := xs.drop half
      have hleft := ihLeft
      have hright := ihRight
      simp only [eval_bind, eval_merge]
      constructor
      · exact hleft.1.merge hright.1
      · calc
          (eval (mergeSort left)).merge (eval (mergeSort right)) ~
              eval (mergeSort left) ++ eval (mergeSort right) :=
            List.merge_perm_append (fun left right : α ↦ decide (left ≤ right))
          _ ~ left ++ right := List.Perm.append hleft.2 hright.2
          _ ~ xs := by simp [left, right]

/-- Every selected cost model preserves the functionally correct MergeSort result. -/
theorem interpret_mergeSort_correct (model : CostModel α) (xs : List α) :
    Sorting.Correct xs ((interpret model (mergeSort xs)).ret.1) := by
  rw [interpret_result_eq_eval]
  exact mergeSort_correct xs

end KleinbergMergeSort
