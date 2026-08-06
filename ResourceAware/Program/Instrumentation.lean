/-
Copyright (c) 2026 Jiyuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan
-/
import ResourceAware.Program.Model

/-!
# Generic instrumentation and cost models

An event pairs an executed operation with a model-selected measurement. A cost model is
separate from semantics and may inspect the state before execution, the operation's response,
and the state after execution.
-/

universe u v

namespace ResourceAware.Program

/-- One executed operation paired with a model-selected measurement. -/
structure Event (Operation : Type u) (Measurement : Type v) where
  operation : Operation
  measurement : Measurement
deriving Repr, DecidableEq

namespace Event

/-- Erase the measurement while retaining the operation. -/
def erase (event : Event Operation Measurement) : Operation :=
  event.operation

/-- Read the measurement stored in an event. -/
def cost (event : Event Operation Measurement) : Measurement :=
  event.measurement

end Event

/-- Measurements assigned independently of execution semantics.

The measurement may inspect the operation, state before execution, response, and state after
execution. This supports operand-, state-, result-, and transition-sensitive models. -/
structure CostModel (signature : Signature.{u, u}) (State : Type u) (Measurement : Type v) where
  measure :
    (operation : signature.A) → State → signature.B operation → State → Measurement

namespace CostModel

/-- Assign the same measurement to every operation. -/
def constant (measurement : Measurement) : CostModel signature State Measurement where
  measure := fun _ _ _ _ ↦ measurement

end CostModel
end ResourceAware.Program
