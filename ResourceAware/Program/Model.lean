/-
Copyright (c) 2026 Jiyuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan
-/
import Cslib.Foundations.Data.PFunctor.Free

/-!
# Abstract programs and their semantics

An algorithm is a free program over a polynomial operation signature. The program fixes only
control flow and requested operations. A `Semantics` value separately implements those operations
as deterministic state transitions, without attaching traces or resource costs.
-/

universe u

set_option linter.checkUnivs false

namespace ResourceAware.Program

/-- An operation signature with a response type for each operation. -/
abbrev Signature := PFunctor

/-- A representation- and cost-independent program over a signature. -/
abbrev Free (signature : Signature.{u, u}) (α : Type u) :=
  signature.FreeM α

/-- Lift one abstract operation into a free program. -/
def request {signature : Signature.{u, u}} (operation : signature.A) :
    Free signature (signature.B operation) :=
  PFunctor.FreeM.lift operation

/-- Deterministic execution semantics, kept separate from resource measurements. -/
structure Semantics (signature : Signature.{u, u}) (State : Type u) where
  initialState : State
  step : (operation : signature.A) → State → signature.B operation × State

namespace Semantics

/-- Interpret one operation as an ordinary state transition. -/
def handler (semantics : Semantics signature State) :
    (operation : signature.A) → StateM State (signature.B operation) :=
  fun operation state ↦ semantics.step operation state

/-- Execute a program from an explicit state, without instrumentation. -/
def evalFrom (semantics : Semantics signature State) (program : Free signature α)
    (state : State) : α × State :=
  program.liftM semantics.handler state

/-- Execute a program from the semantics' initial state. -/
def eval (semantics : Semantics signature State) (program : Free signature α) : α × State :=
  semantics.evalFrom program semantics.initialState

@[simp] theorem evalFrom_pure (semantics : Semantics signature State) (value : α)
    (state : State) :
    semantics.evalFrom (pure value) state = (value, state) := rfl

theorem evalFrom_bind (semantics : Semantics signature State)
    (program : Free signature α) (next : α → Free signature β) (state : State) :
    semantics.evalFrom (program >>= next) state =
      let (result, state') := semantics.evalFrom program state
      semantics.evalFrom (next result) state' := by
  rw [evalFrom, PFunctor.FreeM.liftM_bind]
  rfl

end Semantics
end ResourceAware.Program
