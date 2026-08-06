/-
Copyright (c) 2026 Jiyuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan
-/
import ResourceAware.Program.Model
import Mathlib.Order.Defs.LinearOrder

/-!
# Shared sorting model

This module contains the small amount of family-level structure shared by comparison-based sorting
algorithms: comparison requests, pure comparison semantics, and reusable comparison charges.
Tracing, operation profiles, and bound lifting come directly from `ResourceAware.Program`.
-/

universe u

namespace ResourceAware.Algorithms.Sorting

/-- A key comparison requested by a comparison-based sorting algorithm. -/
inductive ComparisonOp (α : Type u) : Type u where
  | le (left right : α)
deriving Repr, DecidableEq

/-- The Boolean answer returned by a comparison implementation. -/
abbrev ComparisonResponse {α : Type u} : ComparisonOp α → Type u
  | .le _ _ => ULift Bool

/-- Pure comparison semantics, independent of instrumentation and its resource model. -/
structure ComparisonBackend (α : Type u) where
  le : α → α → Bool

namespace ComparisonBackend

/-- The ordinary ascending comparison supplied by a linear order. -/
def linearOrder [LinearOrder α] : ComparisonBackend α where
  le := fun left right ↦ decide (left ≤ right)

/-- Reverse the ordering selected by an existing comparison backend. -/
def reverse (backend : ComparisonBackend α) : ComparisonBackend α where
  le := fun left right ↦ backend.le right left

end ComparisonBackend

/-- Resource charge assigned to one key comparison. -/
structure ComparisonCostModel (α : Type u) where
  cost : α → α → Nat

namespace ComparisonCostModel

/-- Charge the same fixed amount for every key comparison. -/
def constant (charge : Nat) : ComparisonCostModel α where
  cost := fun _ _ ↦ charge

end ComparisonCostModel
end ResourceAware.Algorithms.Sorting
