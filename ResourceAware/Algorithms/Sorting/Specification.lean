/-
Copyright (c) 2026 Jiyuan (Chai Yuen) Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan (Chai Yuen) Ji
-/
import Mathlib.Data.List.Sort

/-!
# Shared specifications for sorting algorithms

Sorting implementations may use different control structures, data representations, and resource
models.  Their functional correctness statements nevertheless share the same mathematical target:
the output is sorted and is a permutation of the input.
-/

universe u

namespace ResourceAware.Algorithms.Sorting

/-- A list is sorted according to `LE.le`. -/
abbrev IsSorted {α : Type u} [LE α] (xs : List α) : Prop :=
  xs.Pairwise (· ≤ ·)

/-- Shared functional-correctness specification for comparison sorting. -/
def Correct {α : Type u} [LE α] (input output : List α) : Prop :=
  IsSorted output ∧ output.Perm input

/-- Every correct sorting result has the same length as its input. -/
theorem Correct.length_eq {α : Type u} [LE α] {input output : List α}
    (h : Correct input output) : output.length = input.length :=
  h.2.length_eq

end ResourceAware.Algorithms.Sorting
