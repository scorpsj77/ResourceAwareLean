/-
Copyright (c) 2026 Jiyuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan
-/
import ResourceAware.Effects.TraceM

/-!
# State computations with ordered observations

`TraceStateM Event State α` combines mutable interpreter state with the ordered event trace from
`TraceM`.  It is shared infrastructure: algorithms and data-structure interpreters can use it
without committing to a numeric cost model.
-/

universe u v w

namespace ResourceAware

/-- A state computation whose execution records an ordered sequence of events.
Running a computation produces: result of type alpha, final state, and ordered list of events. -/
@[ext]
structure TraceStateM (Event : Type u) (State : Type v) (α : Type w) : Type (max u v w) where
  run : State → TraceM Event (α × State)

namespace TraceStateM

variable {Event : Type u} {State : Type v} {α β : Type w}

/-- Project every emitted event without changing return values or state transitions. -/
def mapEvents (f : Event → Event')
    (computation : TraceStateM Event State α) : TraceStateM Event' State α where
  run := fun state ↦ TraceM.mapEvents f (computation.run state)

/- returns a without changing the state or recording the event. -/
protected def pure (a : α) : TraceStateM Event State α where
  run := fun state ↦ pure (a, state)

/- runs and records two events. -/
protected def bind (computation : TraceStateM Event State α)
    (next : α → TraceStateM Event State β) : TraceStateM Event State β where
  run := fun state ↦ do
    let (result, state') ← computation.run state
    (next result).run state'

instance : Pure (TraceStateM Event State) where
  pure := TraceStateM.pure

instance : Bind (TraceStateM Event State) where
  bind := TraceStateM.bind

/- enables Lean's do notation. -/
instance : Monad (TraceStateM Event State) where
  pure := Pure.pure
  bind := Bind.bind
  map f computation := computation >>= fun result ↦ pure (f result)
  seq function argument := function >>= fun f ↦ argument () >>= fun a ↦ pure (f a)
  seqLeft left right := left >>= fun result ↦ right () >>= fun _ ↦ pure result
  seqRight left right := left >>= fun _ ↦ right ()

/-- `TraceStateM` satisfies the monad laws inherited from its underlying `TraceM`. -/
instance : LawfulMonad (TraceStateM Event State) := .mk'
  (id_map := fun computation ↦ by
    change (computation >>= fun result ↦ pure result) = computation
    apply TraceStateM.ext
    funext state
    change (computation.run state >>= fun result ↦ pure result) = computation.run state
    exact bind_pure (computation.run state))
  (pure_bind := fun value next ↦ by
    apply TraceStateM.ext
    funext state
    change ((pure (value, state) : TraceM Event _) >>= fun result ↦
      (next result.1).run result.2) = (next value).run state
    simp)
  (bind_assoc := fun computation next finish ↦ by
    apply TraceStateM.ext
    funext state
    change ((computation.run state >>= fun result ↦
      (next result.1).run result.2) >>= fun result ↦
        (finish result.1).run result.2) =
      (computation.run state >>= fun result ↦
        ((next result.1).run result.2 >>= fun result ↦
          (finish result.1).run result.2))
    exact LawfulMonad.bind_assoc _ _ _)
  (seqLeft_eq := fun _ _ ↦ rfl)
  (bind_pure_comp := fun _ _ ↦ rfl)

@[simp] theorem mapEvents_pure (f : Event → Event') (value : α) :
    mapEvents f (pure value : TraceStateM Event State α) = pure value := by
  ext state <;> rfl

@[simp] theorem mapEvents_bind (f : Event → Event')
    (computation : TraceStateM Event State α)
    (next : α → TraceStateM Event State β) :
    mapEvents f (computation >>= next) =
      mapEvents f computation >>= fun value ↦ mapEvents f (next value) := by
  apply TraceStateM.ext
  funext state
  change TraceM.mapEvents f
      (computation.run state >>= fun result ↦ (next result.1).run result.2) =
    (TraceM.mapEvents f (computation.run state) >>= fun result ↦
      TraceM.mapEvents f ((next result.1).run result.2))
  exact TraceM.mapEvents_bind f (computation.run state) _

/-- Emit one event without changing the interpreter state.
Appends event to the ordered trace, returns Unit, and doesn't change the state.
state ↦ (Unit, state, [event]) -/
def emit (event : Event) : TraceStateM Event State PUnit where
  run := fun state ↦ do
    TraceM.emit event
    pure (.unit, state)

@[simp] theorem mapEvents_emit (f : Event → Event') (event : Event) :
    mapEvents f (emit event : TraceStateM Event State PUnit) = emit (f event) := by
  apply TraceStateM.ext
  funext state
  rfl

/-- Read the interpreter state. Returns current state without changing it.
(state, state): (result, continuing state). -/
def get : TraceStateM Event State State where
  run := fun state ↦ pure (state, state)

/-- Replace the interpreter state. Ignores old state, installs newState, returns Unit, and
doesn't record event. -/
def set (state : State) : TraceStateM Event State PUnit where
  run := fun _ ↦ pure (.unit, state)

/-- Modify the interpreter state. Applying f to current state to get modified. -/
def modify (f : State → State) : TraceStateM Event State PUnit where
  run := fun state ↦ pure (.unit, f state)

end TraceStateM
end ResourceAware
