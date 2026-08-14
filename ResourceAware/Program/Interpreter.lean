/-
Copyright (c) 2026 Jiyuan (Chai Yuen) Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan (Chai Yuen) Ji
-/
import ResourceAware.Effects.TraceStateM
import ResourceAware.Program.Instrumentation

/-!
# Generic program interpreters

The same free program can be executed as a pure state computation, an operation-only trace, or
a measured trace. Algorithms instantiate semantics and cost models; they do not implement
their own free-monad folds.
-/

universe u v w

namespace ResourceAware.Program

/-- Generic measured handler induced by semantics and a cost model. -/
def measuredHandler (semantics : Semantics signature State)
    (costModel : CostModel signature State Measurement) :
    (operation : signature.A) →
      TraceStateM (Event signature.A Measurement) State (signature.B operation) :=
  fun operation ↦ do
    let before ← TraceStateM.get
    let (response, after) := semantics.step operation before
    TraceStateM.emit ⟨operation, costModel.measure operation before response after⟩
    TraceStateM.set after
    pure response

/-- Generic operation-only handler induced by execution semantics. -/
def operationHandler (semantics : Semantics signature State) :
    (operation : signature.A) → TraceStateM signature.A State (signature.B operation) :=
  fun operation ↦ do
    let before ← TraceStateM.get
    let (response, after) := semantics.step operation before
    TraceStateM.emit operation
    TraceStateM.set after
    pure response

/-- Run a measured program from an explicit state. -/
def runFrom (semantics : Semantics signature State)
    (costModel : CostModel signature State Measurement)
    (program : Free signature α) (state : State) :
    TraceM (Event signature.A Measurement) (α × State) :=
  (program.liftM (measuredHandler semantics costModel)).run state

/-- Run a measured program from the semantics' initial state. -/
def run (semantics : Semantics signature State)
    (costModel : CostModel signature State Measurement)
    (program : Free signature α) : TraceM (Event signature.A Measurement) (α × State) :=
  runFrom semantics costModel program semantics.initialState

/-- Run a program while retaining operations but erasing measurements. -/
def runOperationsFrom (semantics : Semantics signature State)
    (program : Free signature α) (state : State) : TraceM signature.A (α × State) :=
  (program.liftM (operationHandler semantics)).run state

/-- Run an operation-only program from the semantics' initial state. -/
def runOperations (semantics : Semantics signature State)
    (program : Free signature α) : TraceM signature.A (α × State) :=
  runOperationsFrom semantics program semantics.initialState

@[simp] theorem runFrom_pure (semantics : Semantics signature State)
    (costModel : CostModel signature State Measurement) (value : α) (state : State) :
    runFrom semantics costModel (pure value) state = pure (value, state) := rfl

theorem runFrom_bind (semantics : Semantics signature State)
    (costModel : CostModel signature State Measurement)
    (program : Free signature α) (next : α → Free signature β) (state : State) :
    runFrom semantics costModel (program >>= next) state = (do
      let (result, state') ← runFrom semantics costModel program state
      runFrom semantics costModel (next result) state') := by
  rw [runFrom, PFunctor.FreeM.liftM_bind]
  rfl

private theorem mapEvents_liftM {SourceEvent : Type v} {TargetEvent : Type w}
    (projection : SourceEvent → TargetEvent) (program : Free signature α)
    (handler : (operation : signature.A) →
      TraceStateM SourceEvent State (signature.B operation)) :
    TraceStateM.mapEvents projection (program.liftM handler) =
      program.liftM fun operation ↦ TraceStateM.mapEvents projection (handler operation) := by
  induction program with
  | pure value => simp
  | liftBind operation next ih =>
      simp only [PFunctor.FreeM.liftM, TraceStateM.mapEvents_bind]
      congr 1
      funext response
      exact ih response

/-- Erasing measurements from a measured run yields the operation-only run. -/
theorem mapEvents_runFrom (semantics : Semantics signature State)
    (costModel : CostModel signature State Measurement)
    (program : Free signature α) (state : State) :
    TraceM.mapEvents Event.erase (runFrom semantics costModel program state) =
      runOperationsFrom semantics program state := by
  change (TraceStateM.mapEvents Event.erase
    (program.liftM (measuredHandler semantics costModel))).run state = _
  rw [mapEvents_liftM]
  congr 2

/-- Instrumentation preserves the semantic result and final state. -/
@[simp] theorem runFrom_ret (semantics : Semantics signature State)
    (costModel : CostModel signature State Measurement)
    (program : Free signature α) (state : State) :
    (runFrom semantics costModel program state).ret = semantics.evalFrom program state := by
  induction program generalizing state with
  | pure value => rfl
  | liftBind operation next ih =>
      change
        (runFrom semantics costModel (next (semantics.step operation state).1)
          (semantics.step operation state).2).ret =
        semantics.evalFrom (next (semantics.step operation state).1)
          (semantics.step operation state).2
      exact ih _ _

/-- Changing only the cost model preserves the erased operations, result, and final state. -/
theorem mapEvents_runFrom_eq (semantics : Semantics signature State)
    (left : CostModel signature State Measurement₁)
    (right : CostModel signature State Measurement₂)
    (program : Free signature α) (state : State) :
    TraceM.mapEvents Event.erase (runFrom semantics left program state) =
      TraceM.mapEvents Event.erase (runFrom semantics right program state) := by
  rw [mapEvents_runFrom, mapEvents_runFrom]

end ResourceAware.Program
