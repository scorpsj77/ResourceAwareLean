/-
Copyright (c) 2026 James Needham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Needham
-/

import TextbookAlgorithms.KleinbergTardos.Chapter13.RandomizedQuicksort.Algorithm

/-!
# Resource models for Kleinberg--Tardos randomized Quicksort

The abstract Quicksort program contains no resource charges. This module independently assigns
natural-number costs to its three operations. The primary model counts only key comparisons. A
second family gives the textbook's abstract running-time convention: a bounded base case, a
size-linear splitter frame, and a constant charge for each comparison.

`splitterFrameCost` accounts for random selection, pivot access and removal, non-comparison list
partition work, and output glue. It deliberately excludes key comparisons, which are always
charged by `comparison.cost`; this prevents the two components from double-counting work.

Persistent list allocation, recursion-stack space, and literal Lean evaluator time are outside
these models.
-/

universe u

namespace Cslib.Textbooks.KleinbergTardos.Chapter13.RandomizedQuicksort

open ResourceAware.Algorithms

/-- Independent costs for the operations emitted by randomized Quicksort. -/
structure CostModel (alpha : Type u) where
  /-- Cost of one ordered-key comparison. -/
  comparison : Sorting.ComparisonCostModel alpha
  /-- Aggregate non-comparison work for a constant-size base case. -/
  baseCaseCost : Nat -> Nat
  /-- Aggregate non-comparison work for a recursive frame of the given positive size. -/
  splitterFrameCost : Nat -> Nat

/-- Uniform base/comparison bounds and a size-linear splitter-frame coefficient. -/
structure CostBounds where
  baseCase : Nat
  comparison : Nat
  splitterUnit : Nat
deriving Repr, DecidableEq

namespace CostBounds

/-- A convenient coefficient collecting all nonrecursive costs of one recurrence frame. -/
def recurrenceCoefficient (bounds : CostBounds) : Nat :=
  bounds.baseCase + bounds.comparison + bounds.splitterUnit

end CostBounds

namespace CostModel

/-- A cost model satisfies the approved primitive uniform and linear bounds. -/
structure IsBoundedBy (model : CostModel alpha) (bounds : CostBounds) : Prop where
  baseCase : forall size, model.baseCaseCost size <= bounds.baseCase
  comparison : forall left right, model.comparison.cost left right <= bounds.comparison
  splitterFrame : forall size,
    model.splitterFrameCost size <= bounds.splitterUnit * size

/-- Count every element comparison once and make all non-comparison work free. -/
def comparisonOnly : CostModel alpha where
  comparison := .constant 1
  baseCaseCost := fun _ => 0
  splitterFrameCost := fun _ => 0

/-- Count each comparison at rate `comparisonUnit`, leaving structural work free. -/
def scaledComparisons (comparisonUnit : Nat) : CostModel alpha where
  comparison := .constant comparisonUnit
  baseCaseCost := fun _ => 0
  splitterFrameCost := fun _ => 0

/--
The textbook running-time family.

A base case costs `baseUnit`; a size-`n` splitter frame costs `frameUnit * n`; and every
comparison costs `comparisonUnit`. The frame component excludes the comparisons.
-/
def linearTextbook (baseUnit frameUnit comparisonUnit : Nat) : CostModel alpha where
  comparison := .constant comparisonUnit
  baseCaseCost := fun _ => baseUnit
  splitterFrameCost := fun size => frameUnit * size

/-- Unit-cost specialization used for the textbook running-time claims. -/
def textbookModel : CostModel alpha :=
  linearTextbook 1 1 1

/-- Bounds exactly realized by `linearTextbook`. -/
def linearTextbookBounds (baseUnit frameUnit comparisonUnit : Nat) : CostBounds where
  baseCase := baseUnit
  comparison := comparisonUnit
  splitterUnit := frameUnit

/-- The approved linear textbook model satisfies its declared primitive bounds. -/
theorem linearTextbook_isBoundedBy (baseUnit frameUnit comparisonUnit : Nat) :
    (linearTextbook (alpha := alpha) baseUnit frameUnit comparisonUnit).IsBoundedBy
      (linearTextbookBounds baseUnit frameUnit comparisonUnit) := by
  constructor <;>
    simp [linearTextbook, linearTextbookBounds, Sorting.ComparisonCostModel.constant]

/-- Primitive bounds for the comparison-only model. -/
def comparisonOnlyBounds : CostBounds where
  baseCase := 0
  comparison := 1
  splitterUnit := 0

/-- The comparison-only model satisfies its exact primitive bounds. -/
theorem comparisonOnly_isBoundedBy :
    (comparisonOnly (alpha := alpha)).IsBoundedBy comparisonOnlyBounds := by
  constructor <;>
    simp [comparisonOnly, comparisonOnlyBounds, Sorting.ComparisonCostModel.constant]

/-- Read the cost assigned to one complete Quicksort operation. -/
def operationCost (model : CostModel alpha) : Op alpha -> Nat
  | .comparison (.le left right) => model.comparison.cost left right
  | .baseCase size => model.baseCaseCost size
  | .choosePivotIndex tailLength => model.splitterFrameCost (tailLength + 1)

@[simp] theorem operationCost_comparison (model : CostModel alpha) (left right : alpha) :
    model.operationCost (.comparison (.le left right)) = model.comparison.cost left right :=
  rfl

@[simp] theorem operationCost_baseCase (model : CostModel alpha) (size : Nat) :
    model.operationCost (.baseCase size) = model.baseCaseCost size :=
  rfl

@[simp] theorem operationCost_choosePivotIndex (model : CostModel alpha) (tailLength : Nat) :
    model.operationCost (.choosePivotIndex tailLength) =
      model.splitterFrameCost (tailLength + 1) :=
  rfl

@[simp] theorem comparisonOnly_comparison (left right : alpha) :
    (comparisonOnly (alpha := alpha)).comparison.cost left right = 1 :=
  rfl

@[simp] theorem comparisonOnly_baseCase (size : Nat) :
    (comparisonOnly (alpha := alpha)).baseCaseCost size = 0 :=
  rfl

@[simp] theorem comparisonOnly_splitterFrame (size : Nat) :
    (comparisonOnly (alpha := alpha)).splitterFrameCost size = 0 :=
  rfl

@[simp] theorem scaledComparisons_comparison (comparisonUnit : Nat) (left right : alpha) :
    (scaledComparisons (alpha := alpha) comparisonUnit).comparison.cost left right =
      comparisonUnit :=
  rfl

@[simp] theorem scaledComparisons_baseCase (comparisonUnit size : Nat) :
    (scaledComparisons (alpha := alpha) comparisonUnit).baseCaseCost size = 0 :=
  rfl

@[simp] theorem scaledComparisons_splitterFrame (comparisonUnit size : Nat) :
    (scaledComparisons (alpha := alpha) comparisonUnit).splitterFrameCost size = 0 :=
  rfl

@[simp] theorem linearTextbook_comparison (baseUnit frameUnit comparisonUnit : Nat)
    (left right : alpha) :
    (linearTextbook (alpha := alpha) baseUnit frameUnit comparisonUnit).comparison.cost
      left right = comparisonUnit :=
  rfl

@[simp] theorem linearTextbook_baseCase (baseUnit frameUnit comparisonUnit size : Nat) :
    (linearTextbook (alpha := alpha) baseUnit frameUnit comparisonUnit).baseCaseCost size =
      baseUnit :=
  rfl

@[simp] theorem linearTextbook_splitterFrame
    (baseUnit frameUnit comparisonUnit size : Nat) :
    (linearTextbook (alpha := alpha) baseUnit frameUnit comparisonUnit).splitterFrameCost size =
      frameUnit * size :=
  rfl

@[simp] theorem textbookModel_comparison (left right : alpha) :
    (textbookModel (alpha := alpha)).comparison.cost left right = 1 :=
  rfl

@[simp] theorem textbookModel_baseCase (size : Nat) :
    (textbookModel (alpha := alpha)).baseCaseCost size = 1 :=
  rfl

@[simp] theorem textbookModel_splitterFrame (size : Nat) :
    (textbookModel (alpha := alpha)).splitterFrameCost size = size := by
  simp [textbookModel, linearTextbook]

end CostModel

end Cslib.Textbooks.KleinbergTardos.Chapter13.RandomizedQuicksort
