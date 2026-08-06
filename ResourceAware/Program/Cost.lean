/-
Copyright (c) 2026 Jiyuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan
-/
import ResourceAware.Program.Interpreter

/-!
# Generic trace costs and bounds

Measured traces can be projected to cost-independent operation traces and then reweighted under
arbitrary models. Pointwise bounds for primitive requests lift through the generic interpreter to
complete programs. These definitions and theorems apply to every operation signature.
-/

universe u

namespace ResourceAware.Program

/-- Ordered operations with model-selected measurements erased. -/
def operationTrace (computation : TraceM (Event Operation Measurement) α) : List Operation :=
  TraceM.projectedEvents Event.erase computation

/-- Number of occurrences of one fully specified operation. -/
def operationCount [DecidableEq Operation] (operation : Operation)
    (computation : TraceM (Event Operation Measurement) α) : Nat :=
  (operationTrace computation).count operation

/-- Reinterpret an operation trace under arbitrary natural-number weights. -/
def weightedOperationCost (charge : Operation → Nat)
    (computation : TraceM (Event Operation Measurement) α) : Nat :=
  TraceM.projectedCost Event.erase charge computation

/-- Indicator weight for one fully specified operation. -/
def operationIndicator [DecidableEq Operation] (target : Operation) : Operation → Nat :=
  fun operation ↦ if operation = target then 1 else 0

@[simp] theorem operationTrace_pure (value : α) :
    operationTrace (pure value : TraceM (Event Operation Measurement) α) = [] := rfl

@[simp] theorem operationTrace_emit (event : Event Operation Measurement) :
    operationTrace (TraceM.emit event) = [event.operation] := rfl

@[simp] theorem operationTrace_bind
    (computation : TraceM (Event Operation Measurement) α)
    (next : α → TraceM (Event Operation Measurement) β) :
    operationTrace (computation >>= next) =
      operationTrace computation ++ operationTrace (next computation.ret) := by
  simp [operationTrace]

@[simp] theorem operationCount_pure [DecidableEq Operation]
    (operation : Operation) (value : α) :
    operationCount operation (pure value : TraceM (Event Operation Measurement) α) = 0 := by
  simp [operationCount]

@[simp] theorem operationCount_bind [DecidableEq Operation] (operation : Operation)
    (computation : TraceM (Event Operation Measurement) α)
    (next : α → TraceM (Event Operation Measurement) β) :
    operationCount operation (computation >>= next) =
      operationCount operation computation + operationCount operation (next computation.ret) := by
  simp [operationCount]

@[simp] theorem weightedOperationCost_pure (charge : Operation → Nat) (value : α) :
    weightedOperationCost charge (pure value : TraceM (Event Operation Measurement) α) = 0 := by
  simp [weightedOperationCost]

@[simp] theorem weightedOperationCost_bind (charge : Operation → Nat)
    (computation : TraceM (Event Operation Measurement) α)
    (next : α → TraceM (Event Operation Measurement) β) :
    weightedOperationCost charge (computation >>= next) =
      weightedOperationCost charge computation +
        weightedOperationCost charge (next computation.ret) := by
  simp [weightedOperationCost]

@[simp] theorem weightedOperationCost_emit (charge : Operation → Nat)
    (event : Event Operation Measurement) :
    weightedOperationCost charge (TraceM.emit event) = charge event.operation := by
  simp [weightedOperationCost, TraceM.projectedCost, TraceM.cost, TraceM.traceCost,
    Event.erase]

/-- Weighted operation cost is a fold over the erased operation trace. -/
theorem weightedOperationCost_eq_foldr (charge : Operation → Nat)
    (computation : TraceM (Event Operation Measurement) α) :
    weightedOperationCost charge computation =
      (operationTrace computation).foldr (fun operation total ↦ charge operation + total) 0 := by
  unfold weightedOperationCost TraceM.projectedCost TraceM.cost TraceM.traceCost
  unfold operationTrace TraceM.projectedEvents TraceM.events
  simp only [EventTrace.cost, List.foldr_map, Function.comp_apply, Event.erase]

/-- Exact operation counts are weighted costs under the corresponding indicator. -/
theorem weightedOperationCost_indicator [DecidableEq Operation] (target : Operation)
    (computation : TraceM (Event Operation Measurement) α) :
    weightedOperationCost (operationIndicator target) computation =
      operationCount target computation := by
  rw [weightedOperationCost_eq_foldr]
  unfold operationCount
  induction operationTrace computation with
  | nil => simp
  | cons operation operations ih =>
      simp only [List.foldr_cons]
      rw [ih]
      by_cases h : operation = target
      · subst operation
        simp [operationIndicator, Nat.add_comm]
      · simp [operationIndicator, h]

/-- Weighted cost depends only on the erased operation trace. -/
theorem weightedOperationCost_eq_of_operationTrace_eq (charge : Operation → Nat)
    {left : TraceM (Event Operation Measurement₁) α}
    {right : TraceM (Event Operation Measurement₂) β}
    (h : operationTrace left = operationTrace right) :
    weightedOperationCost charge left = weightedOperationCost charge right := by
  unfold operationTrace TraceM.projectedEvents TraceM.events at h
  unfold weightedOperationCost TraceM.projectedCost TraceM.cost TraceM.traceCost
  simpa only [EventTrace.cost, List.foldr_map, Function.comp_apply, Event.erase] using
    congrArg (List.foldr (fun operation total ↦ charge operation + total) 0) h

/-- Sum the measurements stored in an interpreted trace. -/
def exactCost [AddMonoid Measurement]
    (computation : TraceM (Event Operation Measurement) α) : Measurement :=
  TraceM.cost Event.cost computation

/-- Pointwise operation weights bound the measurements stored in a trace. -/
theorem exactCost_le_weightedOperationCost
    (charge : Operation → Nat) (computation : TraceM (Event Operation Nat) α)
    (h : ∀ event ∈ TraceM.events computation,
      event.measurement ≤ charge event.operation) :
    exactCost computation ≤ weightedOperationCost charge computation := by
  exact TraceM.cost_le_cost Event.cost (charge ∘ Event.erase) computation h

/-- Exact per-event charges make measured and profile-interpreted costs equal. -/
theorem exactCost_eq_weightedOperationCost
    (charge : Operation → Nat) (computation : TraceM (Event Operation Nat) α)
    (h : ∀ event ∈ TraceM.events computation,
      event.measurement = charge event.operation) :
    exactCost computation = weightedOperationCost charge computation := by
  apply Nat.le_antisymm
  · exact exactCost_le_weightedOperationCost charge computation fun event hmem ↦
      (h event hmem).le
  · exact TraceM.cost_le_cost (charge ∘ Event.erase) Event.cost computation fun event hmem ↦
      (h event hmem).ge

/-- Convert a naturally measured trace to CSLib's existing numeric `TimeM` interface. -/
def toTimeM (computation : TraceM (Event Operation Nat) α) :
    Cslib.Algorithms.Lean.TimeM Nat α :=
  TraceM.toTimeM Event.cost computation

private theorem events_liftM {TraceEvent : Type u} (predicate : TraceEvent → Prop)
    (program : Free signature α)
    (handler : (operation : signature.A) →
      TraceStateM TraceEvent State (signature.B operation))
    (hhandler : ∀ operation state event,
      event ∈ TraceM.events ((handler operation).run state) → predicate event) :
    ∀ state event,
      event ∈ TraceM.events ((program.liftM handler).run state) → predicate event := by
  induction program with
  | pure value =>
      intro state event hmem
      change event ∈ [] at hmem
      simp at hmem
  | liftBind operation next ih =>
      intro state event hmem
      change event ∈
        TraceM.events ((handler operation).run state) ++
          TraceM.events
            (((next ((handler operation).run state).ret.1).liftM handler).run
              ((handler operation).run state).ret.2) at hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · exact hhandler operation state event hmem
      · exact ih ((handler operation).run state).ret.1
          ((handler operation).run state).ret.2 event hmem

/-- A pointwise primitive bound lifts through the generic interpreter to every program. -/
theorem events_runFrom_le (semantics : Semantics signature State)
    (costModel : CostModel signature State Nat) (charge : signature.A → Nat)
    (hbounded : ∀ operation state,
      let (response, after) := semantics.step operation state
      costModel.measure operation state response after ≤ charge operation)
    (program : Free signature α) (state : State) :
    ∀ event ∈ TraceM.events (runFrom semantics costModel program state),
      event.measurement ≤ charge event.operation := by
  change ∀ event ∈ TraceM.events
    ((program.liftM (measuredHandler semantics costModel)).run state),
    event.measurement ≤ charge event.operation
  refine events_liftM (fun event ↦ event.measurement ≤ charge event.operation)
    program (measuredHandler semantics costModel) ?_ state
  intro operation before event hmem
  change event ∈
    [⟨operation,
      costModel.measure operation before
        (semantics.step operation before).1 (semantics.step operation before).2⟩] at hmem
  rcases List.mem_singleton.mp hmem with rfl
  exact hbounded operation before

/-- Primitive bounds lift once through interpretation to a weighted operation-profile bound. -/
theorem exactCost_runFrom_le_weightedOperationCost
    (semantics : Semantics signature State)
    (costModel : CostModel signature State Nat) (charge : signature.A → Nat)
    (hbounded : ∀ operation state,
      let (response, after) := semantics.step operation state
      costModel.measure operation state response after ≤ charge operation)
    (program : Free signature α) (state : State) :
    exactCost (runFrom semantics costModel program state) ≤
      weightedOperationCost charge (runFrom semantics costModel program state) := by
  exact exactCost_le_weightedOperationCost charge _
    (events_runFrom_le semantics costModel charge hbounded program state)

/-- A single request contributes exactly its operation weight. -/
@[simp] theorem weightedOperationCost_runFrom_request
    (semantics : Semantics signature State)
    (costModel : CostModel signature State Measurement) (charge : signature.A → Nat)
    (operation : signature.A) (state : State) :
    weightedOperationCost charge
      (runFrom semantics costModel (request operation) state) = charge operation := rfl

end ResourceAware.Program
