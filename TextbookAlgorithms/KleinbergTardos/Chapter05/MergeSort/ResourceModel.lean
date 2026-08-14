/-
Copyright (c) 2026 Jiyuan (Chai Yuen) Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan (Chai Yuen) Ji
-/
import TextbookAlgorithms.KleinbergTardos.Chapter05.MergeSort.Algorithm
import ResourceAware.Program.Cost

/-!
# Semantics and resource models for Kleinberg merge sort

The abstract algorithm records comparisons, constant-size base cases, splits, and merges. Split
and merge measurements come from a selected structural backend, while comparisons have their own
shared sorting cost model. This file supplies those choices to the generic
`ResourceAware.Program` interpreter; it contains no algorithm-specific free-monad fold.
-/

universe u

namespace KleinbergMergeSort

open ResourceAware ResourceAware.Algorithms

/--
Representation-sensitive costs for the two structural sequence operations used by merge sort.

One abstract split or merge event may have a measurement greater than one.  A list-copy backend,
an array-copy backend, and a constant-time slice backend can therefore interpret the same abstract
algorithm differently without adding representation-specific element events to its syntax.
-/
structure StructuralCostBackend where
  splitCost : Nat → Nat
  mergeStructuralCost : Nat → Nat

namespace StructuralCostBackend

/-- Treat structural sequence operations as free. -/
def free : StructuralCostBackend where
  splitCost := fun _ ↦ 0
  mergeStructuralCost := fun _ ↦ 0

/--
A convenient linear backend: splitting a size-`n` problem costs `splitUnit * n`, and structurally
forming its merged output costs `mergeUnit * n`.  Comparisons are deliberately not included.
-/
def linear (splitUnit mergeUnit : Nat) : StructuralCostBackend where
  splitCost := fun size ↦ splitUnit * size
  mergeStructuralCost := fun size ↦ mergeUnit * size

end StructuralCostBackend

/-- Costs assigned to the abstract operations of Kleinberg merge sort. -/
structure CostModel (α : Type u) where
  comparison : Sorting.ComparisonCostModel α
  baseCaseCost : Nat → Nat
  structural : StructuralCostBackend

/-- Uniform and size-linear upper bounds for the operations emitted by merge sort. -/
structure CostBounds where
  baseCase : Nat
  comparison : Nat
  splitUnit : Nat
  mergeUnit : Nat

namespace CostBounds

/-- Coefficient contributed by all nonrecursive work at one merge-sort level. -/
def recurrenceCoefficient (bounds : CostBounds) : Nat :=
  bounds.baseCase + bounds.splitUnit + bounds.mergeUnit + bounds.comparison

end CostBounds

namespace CostModel

/-- A merge-sort cost model respects the selected uniform and size-linear operation bounds. -/
structure IsBoundedBy (model : CostModel α) (bounds : CostBounds) : Prop where
  baseCase : ∀ size, model.baseCaseCost size ≤ bounds.baseCase
  comparison : ∀ left right, model.comparison.cost left right ≤ bounds.comparison
  split : ∀ size, model.structural.splitCost size ≤ bounds.splitUnit * size
  merge : ∀ size, model.structural.mergeStructuralCost size ≤ bounds.mergeUnit * size

/-- Count key comparisons at a selected constant rate and make structural operations free. -/
def comparisonOnly (comparisonUnit : Nat := 1) : CostModel α where
  comparison := .constant comparisonUnit
  baseCaseCost := fun _ ↦ 0
  structural := .free

/--
Kleinberg's comparison policy combined with an independently selected structural backend.

Each actual key comparison costs `comparisonUnit`.  The backend supplies the aggregate structural
costs of a split and a merge and must exclude key-comparison work from `mergeStructuralCost`.
-/
def kleinberg (comparisonUnit : Nat) (structural : StructuralCostBackend) : CostModel α where
  comparison := .constant comparisonUnit
  baseCaseCost := fun _ ↦ 0
  structural := structural

/-- Kleinberg's comparison policy with a convenient linear structural backend. -/
def linearKleinberg (comparisonUnit splitUnit mergeUnit : Nat) : CostModel α :=
  kleinberg comparisonUnit (.linear splitUnit mergeUnit)

/-- Primitive bounds realized by the linear Kleinberg cost model. -/
def linearKleinbergBounds (comparisonUnit splitUnit mergeUnit : Nat) : CostBounds where
  baseCase := 0
  comparison := comparisonUnit
  splitUnit := splitUnit
  mergeUnit := mergeUnit

/--
One valid coefficient for Kleinberg's recurrence: the split, structural-merge, and comparison
coefficients.
-/
def kleinbergCoefficient (comparisonUnit splitUnit mergeUnit : Nat) : Nat :=
  splitUnit + mergeUnit + comparisonUnit

/-- The linear Kleinberg model satisfies its declared primitive bounds. -/
theorem linearKleinberg_isBoundedBy (comparisonUnit splitUnit mergeUnit : Nat) :
    (linearKleinberg (α := α) comparisonUnit splitUnit mergeUnit).IsBoundedBy
      (linearKleinbergBounds comparisonUnit splitUnit mergeUnit) := by
  constructor <;> simp [linearKleinberg, linearKleinbergBounds, kleinberg,
    StructuralCostBackend.linear, Sorting.ComparisonCostModel.constant]

@[simp] theorem linearKleinbergBounds_recurrenceCoefficient
    (comparisonUnit splitUnit mergeUnit : Nat) :
    (linearKleinbergBounds comparisonUnit splitUnit mergeUnit).recurrenceCoefficient =
      kleinbergCoefficient comparisonUnit splitUnit mergeUnit := by
  simp [linearKleinbergBounds, CostBounds.recurrenceCoefficient, kleinbergCoefficient]

end CostModel

open ResourceAware ResourceAware.Algorithms

abbrev Event (α : Type u) := ResourceAware.Program.Event (Op α) Nat

def semantics (backend : Sorting.ComparisonBackend α) :
    ResourceAware.Program.Semantics (Signature α) PUnit where
  initialState := .unit
  step operation _ :=
    match operation with
    | .comparison (.le left right) => (ULift.up (backend.le left right), .unit)
    | .baseCase _ => (.unit, .unit)
    | .split _ => (.unit, .unit)
    | .merge _ => (.unit, .unit)

def measuredCostModel (model : CostModel α) :
    ResourceAware.Program.CostModel (Signature α) PUnit Nat where
  measure operation _ _ _ :=
    match operation with
    | .comparison (.le left right) => model.comparison.cost left right
    | .baseCase size => model.baseCaseCost size
    | .split size => model.structural.splitCost size
    | .merge size => model.structural.mergeStructuralCost size

def evalWith (backend : Sorting.ComparisonBackend α) (program : Program α β) : β :=
  (ResourceAware.Program.Semantics.eval (semantics backend) program).1

def eval [LinearOrder α] (program : Program α β) : β :=
  evalWith .linearOrder program

@[simp] theorem eval_pure [LinearOrder α] (value : β) :
    eval (pure value : Program α β) = value := rfl

@[simp] theorem eval_bind [LinearOrder α] (program : Program α β)
    (next : β → Program α γ) :
    eval (program >>= next) = eval (next (eval program)) := by
  unfold eval evalWith ResourceAware.Program.Semantics.eval
  rw [ResourceAware.Program.Semantics.evalFrom_bind]

@[simp] theorem eval_map [LinearOrder α] (function : β → γ) (program : Program α β) :
    eval (function <$> program) = function (eval program) := by
  unfold eval evalWith ResourceAware.Program.Semantics.eval
    ResourceAware.Program.Semantics.evalFrom
  rw [PFunctor.FreeM.liftM_map]
  rfl

@[simp] theorem eval_request [LinearOrder α] (operation : Op α) :
    eval (request operation) =
      match operation with
      | .comparison (.le left right) => ULift.up (decide (left ≤ right))
      | .baseCase _ => .unit
      | .split _ => .unit
      | .merge _ => .unit := by
  cases operation with
  | comparison operation =>
      cases operation
      rfl
  | baseCase => rfl
  | split => rfl
  | merge => rfl

def operationCharge (bounds : CostBounds) : Op α → Nat
  | .comparison _ => bounds.comparison
  | .baseCase _ => bounds.baseCase
  | .split size => bounds.splitUnit * size
  | .merge size => bounds.mergeUnit * size

def interpretWith (backend : Sorting.ComparisonBackend α) (model : CostModel α)
    (program : Program α β) : TraceM (Event α) (β × PUnit) :=
  ResourceAware.Program.run (semantics backend) (measuredCostModel model) program

def interpret [LinearOrder α] (model : CostModel α) (program : Program α β) :
    TraceM (Event α) (β × PUnit) :=
  interpretWith .linearOrder model program

@[simp] theorem interpret_pure [LinearOrder α] (model : CostModel α) (value : β) :
    interpret model (pure value : Program α β) = pure (value, .unit) := rfl

theorem interpret_bind [LinearOrder α] (model : CostModel α) (program : Program α β)
    (next : β → Program α γ) :
    interpret model (program >>= next) = (do
      let result ← interpret model program
      interpret model (next result.1)) := by
  let handler := ResourceAware.Program.measuredHandler
    (semantics (Sorting.ComparisonBackend.linearOrder : Sorting.ComparisonBackend α))
    (measuredCostModel model)
  change ((program >>= next).liftM handler).run .unit =
    ((program.liftM handler).run .unit >>= fun result ↦
      ((next result.1).liftM handler).run .unit)
  rw [PFunctor.FreeM.liftM_bind]
  change
    ((program.liftM handler).run .unit >>= fun result ↦
        ((next result.1).liftM handler).run result.2) =
      ((program.liftM handler).run .unit >>= fun result ↦
        ((next result.1).liftM handler).run .unit)
  generalize (program.liftM handler).run .unit = result
  rcases result with ⟨⟨value, state⟩, time⟩
  cases state
  rfl

@[simp] theorem interpretWith_result_eq_evalWith (backend : Sorting.ComparisonBackend α)
    (model : CostModel α) (program : Program α β) :
    (interpretWith backend model program).ret.1 = evalWith backend program := by
  simp [interpretWith, ResourceAware.Program.run, evalWith,
    ResourceAware.Program.Semantics.eval]

@[simp] theorem interpret_result_eq_eval [LinearOrder α] (model : CostModel α)
    (program : Program α β) :
    (interpret model program).ret.1 = eval program :=
  interpretWith_result_eq_evalWith .linearOrder model program

def exactCost (computation : TraceM (Event α) β) : Nat :=
  ResourceAware.Program.exactCost computation

theorem exactCost_interpretWith_le_weightedOperationCost
    (backend : Sorting.ComparisonBackend α) (model : CostModel α) (bounds : CostBounds)
    (hbounded : model.IsBoundedBy bounds) (program : Program α β) :
    exactCost (interpretWith backend model program :
      TraceM (Event α) (β × PUnit.{u + 1})) ≤
      ResourceAware.Program.weightedOperationCost (operationCharge bounds)
        (interpretWith backend model program :
          TraceM (Event α) (β × PUnit.{u + 1})) := by
  apply ResourceAware.Program.exactCost_runFrom_le_weightedOperationCost
  intro operation _
  cases operation with
  | comparison operation =>
      cases operation with
      | le left right => exact hbounded.comparison left right
  | baseCase size => exact hbounded.baseCase size
  | split size => exact hbounded.split size
  | merge size => exact hbounded.merge size

@[simp] theorem weightedOperationCost_interpret_bind [LinearOrder α]
    (charge : Op α → Nat) (model : CostModel α) (program : Program α β)
    (next : β → Program α γ) :
    ResourceAware.Program.weightedOperationCost charge
        (interpret model (program >>= next) : TraceM (Event α) (γ × PUnit.{u + 1})) =
      ResourceAware.Program.weightedOperationCost charge
          (interpret model program : TraceM (Event α) (β × PUnit.{u + 1})) +
        ResourceAware.Program.weightedOperationCost charge
          (interpret model (next (eval program)) : TraceM (Event α) (γ × PUnit.{u + 1})) := by
  rw [interpret_bind, ResourceAware.Program.weightedOperationCost_bind, interpret_result_eq_eval]

@[simp] theorem weightedOperationCost_interpret_map [LinearOrder α]
    (charge : Op α → Nat) (model : CostModel α) (function : β → γ)
    (program : Program α β) :
    ResourceAware.Program.weightedOperationCost charge
        (interpret model (function <$> program) : TraceM (Event α) (γ × PUnit.{u + 1})) =
      ResourceAware.Program.weightedOperationCost charge
        (interpret model program : TraceM (Event α) (β × PUnit.{u + 1})) := by
  rw [show function <$> program = (program >>= fun result ↦ pure (function result)) by
    symm
    exact PFunctor.FreeM.bind_pure_comp function program]
  rw [weightedOperationCost_interpret_bind]
  simp

@[simp] theorem weightedOperationCost_interpret_request [LinearOrder α]
    (charge : Op α → Nat) (model : CostModel α) (operation : Op α) :
    ResourceAware.Program.weightedOperationCost charge (interpret model (request operation)) =
      charge operation := rfl

end KleinbergMergeSort
