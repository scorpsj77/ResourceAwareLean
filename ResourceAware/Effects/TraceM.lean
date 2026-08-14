/-
Copyright (c) 2026 Daya Kumaran. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daya Kumaran
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Algebra.Group.Nat.Defs

/-!
# TraceM

`TraceM Event α` is a specialization of `TimeM` whose annotation is the ordered sequence of
events emitted during a computation. Sequential composition concatenates traces in execution
order.

Event counts and resource costs are derived from the ordered trace. Algorithms can therefore
record what happened without fixing a cost model, while correctness proofs continue to use the
unchanged return value.
-/

@[expose] public section

namespace ResourceAware

open Cslib.Algorithms.Lean

/-! ## Ordered event traces -/

/-- The ordered events emitted by a computation. -/
@[ext]
structure EventTrace (Event : Type*) where
  events : List Event
deriving Repr

namespace EventTrace

/-- The empty event trace. -/
def empty : EventTrace Event :=
  ⟨[]⟩

/-- The trace containing exactly one event. -/
def singleton (event : Event) : EventTrace Event :=
  ⟨[event]⟩

/-- Concatenate two traces while preserving execution order. -/
def append (xs ys : EventTrace Event) : EventTrace Event :=
  ⟨xs.events ++ ys.events⟩

/-- Apply a projection to every event while preserving its position in the trace. -/
def map (f : Event → Event') (trace : EventTrace Event) : EventTrace Event' :=
  ⟨trace.events.map f⟩

instance : Zero (EventTrace Event) := ⟨empty⟩

instance : Add (EventTrace Event) := ⟨append⟩

instance : AddMonoid (EventTrace Event) where
  zero := empty
  add := append
  zero_add := by
    rintro ⟨events⟩
    change append empty ⟨events⟩ = ⟨events⟩
    rfl
  add_zero := by
    rintro ⟨events⟩
    change append ⟨events⟩ empty = ⟨events⟩
    simp [append, empty]
  add_assoc := by
    rintro ⟨xs⟩ ⟨ys⟩ ⟨zs⟩
    change append (append ⟨xs⟩ ⟨ys⟩) ⟨zs⟩ =
      append ⟨xs⟩ (append ⟨ys⟩ ⟨zs⟩)
    simp [append, List.append_assoc]
  nsmul := nsmulRec

@[simp] theorem events_empty : (empty : EventTrace Event).events = [] := rfl

@[simp] theorem events_zero : (0 : EventTrace Event).events = [] := rfl

@[simp] theorem events_singleton (event : Event) : (singleton event).events = [event] := rfl

@[simp] theorem events_append (xs ys : EventTrace Event) :
    (append xs ys).events = xs.events ++ ys.events := rfl

@[simp] theorem events_add (xs ys : EventTrace Event) :
    (xs + ys).events = xs.events ++ ys.events := rfl

@[simp] theorem events_map (f : Event → Event') (trace : EventTrace Event) :
    (map f trace).events = trace.events.map f := rfl

@[simp] theorem map_empty (f : Event → Event') :
    map f (empty : EventTrace Event) = empty := rfl

@[simp] theorem map_singleton (f : Event → Event') (event : Event) :
    map f (singleton event) = singleton (f event) := rfl

@[simp] theorem map_append (f : Event → Event') (xs ys : EventTrace Event) :
    map f (append xs ys) = append (map f xs) (map f ys) := by
  ext
  simp [map, append]

/-- Count occurrences of one event in an ordered trace. -/
def count [BEq Event] (trace : EventTrace Event) (event : Event) : Nat :=
  trace.events.count event

/-- Interpret an ordered trace by assigning a resource cost to each event. -/
def cost [AddMonoid Cost] (charge : Event → Cost) (trace : EventTrace Event) : Cost :=
  trace.events.foldr (fun event total ↦ charge event + total) 0

private theorem foldr_cost_acc [AddMonoid Cost] (charge : Event → Cost)
    (events : List Event) (initial : Cost) :
    events.foldr (fun event total ↦ charge event + total) initial =
      events.foldr (fun event total ↦ charge event + total) 0 + initial := by
  induction events with
  | nil => simp
  | cons event events ih =>
      simp only [List.foldr_cons]
      rw [ih]
      simp [add_assoc]

@[simp] theorem cost_empty [AddMonoid Cost] (charge : Event → Cost) :
    cost charge (empty : EventTrace Event) = 0 := rfl

@[simp] theorem cost_zero [AddMonoid Cost] (charge : Event → Cost) :
    cost charge (0 : EventTrace Event) = 0 := rfl

@[simp] theorem cost_singleton [AddMonoid Cost] (charge : Event → Cost) (event : Event) :
    cost charge (singleton event) = charge event := by
  simp [cost, singleton]

@[simp] theorem cost_append [AddMonoid Cost] (charge : Event → Cost)
    (xs ys : EventTrace Event) :
    cost charge (append xs ys) = cost charge xs + cost charge ys := by
  simp only [cost, append, List.foldr_append]
  exact foldr_cost_acc charge xs.events _

@[simp] theorem cost_add [AddMonoid Cost] (charge : Event → Cost)
    (xs ys : EventTrace Event) :
    cost charge (xs + ys) = cost charge xs + cost charge ys :=
  cost_append charge xs ys

/-- Projecting a trace and then charging it is the same as charging the source events through
the projection. -/
@[simp] theorem cost_map [AddMonoid Cost] (charge : Event' → Cost)
    (f : Event → Event') (trace : EventTrace Event) :
    cost charge (map f trace) = cost (charge ∘ f) trace := by
  simp only [cost, map, List.foldr_map]
  rfl

/-- Pointwise larger natural-number charges give a larger total trace cost. -/
theorem cost_mono_nat (lower upper : Event → Nat) (trace : EventTrace Event)
    (h : ∀ event ∈ trace.events, lower event ≤ upper event) :
    cost lower trace ≤ cost upper trace := by
  rcases trace with ⟨events⟩
  induction events with
  | nil => simp [cost]
  | cons event events ih =>
      simp only [cost, List.foldr_cons]
      exact Nat.add_le_add (h event (by simp))
        (ih fun candidate hmem ↦ h candidate (by simp [hmem]))

end EventTrace

/-! ## Count projection -/

/-- Occurrence counts derived from a trace, represented extensionally as `Event → ℕ`. -/
abbrev EventCounts (Event : Type*) :=
  Event → ℕ

namespace EventCounts

/-- The empty event-count map. -/
def empty : EventCounts Event :=
  fun _ ↦ 0

/-- Add event counts pointwise. -/
def add (xs ys : EventCounts Event) : EventCounts Event :=
  fun event ↦ xs event + ys event

/-- The count map for one occurrence of `event`. -/
def singleton [DecidableEq Event] (event : Event) : EventCounts Event :=
  fun event' ↦ if event' = event then 1 else 0

/-- Count the occurrences of every event in a list. -/
def ofList [DecidableEq Event] : List Event → EventCounts Event
  | [] => empty
  | event :: events => add (singleton event) (ofList events)

/-- Forget event order and retain only occurrence counts. -/
def ofTrace [DecidableEq Event] (trace : EventTrace Event) : EventCounts Event :=
  ofList trace.events

@[simp] theorem empty_apply (event : Event) :
    (empty : EventCounts Event) event = 0 := rfl

@[simp] theorem add_apply (xs ys : EventCounts Event) (event : Event) :
    add xs ys event = xs event + ys event := rfl

@[simp] theorem singleton_self [DecidableEq Event] (event : Event) :
    singleton event event = 1 := by
  simp [singleton]

@[simp] theorem singleton_of_ne [DecidableEq Event] {event event' : Event}
    (h : event' ≠ event) : singleton event event' = 0 := by
  simp [singleton, h]

@[simp] theorem ofList_nil [DecidableEq Event] :
    (ofList [] : EventCounts Event) = empty := rfl

@[simp] theorem ofList_cons [DecidableEq Event] (event : Event) (events : List Event) :
    ofList (event :: events) = add (singleton event) (ofList events) := rfl

@[simp] theorem ofList_append [DecidableEq Event] (xs ys : List Event) :
    ofList (xs ++ ys) = add (ofList xs) (ofList ys) := by
  induction xs with
  | nil =>
      funext event
      simp [ofList, add, empty]
  | cons head tail ih =>
      funext event
      simp [ofList, ih, add, Nat.add_assoc]

@[simp] theorem ofTrace_empty [DecidableEq Event] :
    ofTrace (EventTrace.empty : EventTrace Event) = empty := rfl

@[simp] theorem ofTrace_singleton [DecidableEq Event] (event : Event) :
    ofTrace (EventTrace.singleton event) = singleton event := by
  funext event'
  simp [ofTrace, ofList, singleton, add, empty]

@[simp] theorem ofTrace_append [DecidableEq Event] (xs ys : EventTrace Event) :
    ofTrace (EventTrace.append xs ys) = add (ofTrace xs) (ofTrace ys) := by
  simp [ofTrace, EventTrace.append]

end EventCounts

/-! ## Traced computations -/

/-- A computation that returns an `α` and records an ordered event trace. -/
abbrev TraceM (Event : Type*) (α : Type*) :=
  TimeM (EventTrace Event) α

namespace TraceM

/-- Emit one event. -/
def emit (event : Event) : TraceM Event PUnit :=
  TimeM.tick (EventTrace.singleton event)

/-- Emit several events in their given order. -/
def emitMany (events : List Event) : TraceM Event PUnit :=
  TimeM.tick ⟨events⟩

/-- Extract the ordered events from a traced computation. -/
def events (computation : TraceM Event α) : List Event :=
  computation.time.events

/-- Project every emitted event without changing the result of the computation. -/
def mapEvents (f : Event → Event') (computation : TraceM Event α) : TraceM Event' α :=
  ⟨computation.ret, computation.time.map f⟩

/-- Extract an ordered projection of the events emitted by a computation. -/
def projectedEvents (f : Event → Event') (computation : TraceM Event α) : List Event' :=
  (events computation).map f

/-- Sequential composition preserves the execution order of emitted events. -/
@[simp] theorem events_bind (computation : TraceM Event α)
    (next : α → TraceM Event β) :
    events (computation >>= next) =
      events computation ++ events (next computation.ret) := rfl

@[simp] theorem ret_mapEvents (f : Event → Event') (computation : TraceM Event α) :
    (mapEvents f computation).ret = computation.ret := rfl

@[simp] theorem events_mapEvents (f : Event → Event') (computation : TraceM Event α) :
    events (mapEvents f computation) = projectedEvents f computation := rfl

@[simp] theorem projectedEvents_pure (f : Event → Event') (value : α) :
    projectedEvents f (pure value : TraceM Event α) = [] := rfl

@[simp] theorem projectedEvents_emit (f : Event → Event') (event : Event) :
    projectedEvents f (emit event) = [f event] := rfl

@[simp] theorem projectedEvents_bind (f : Event → Event')
    (computation : TraceM Event α) (next : α → TraceM Event β) :
    projectedEvents f (computation >>= next) =
      projectedEvents f computation ++ projectedEvents f (next computation.ret) := by
  simp [projectedEvents]

@[simp] theorem mapEvents_pure (f : Event → Event') (value : α) :
    mapEvents f (pure value : TraceM Event α) = pure value := rfl

@[simp] theorem mapEvents_emit (f : Event → Event') (event : Event) :
    mapEvents f (emit event) = emit (f event) := rfl

@[simp] theorem mapEvents_bind (f : Event → Event')
    (computation : TraceM Event α) (next : α → TraceM Event β) :
    mapEvents f (computation >>= next) =
      mapEvents f computation >>= fun value ↦ mapEvents f (next value) := by
  ext <;> simp [mapEvents, EventTrace.map]

/-- Forget event order and retain only occurrence counts. -/
def counts [DecidableEq Event] (computation : TraceM Event α) : EventCounts Event :=
  EventCounts.ofTrace computation.time

/-- Interpret a trace by assigning a resource cost to every event. -/
def traceCost [AddMonoid Cost] (charge : Event → Cost) (trace : EventTrace Event) : Cost :=
  trace.cost charge

/-- Interpret the trace of a completed computation. -/
def cost [AddMonoid Cost] (charge : Event → Cost) (computation : TraceM Event α) : Cost :=
  traceCost charge computation.time

/-- Convert an event-traced computation into a computation with an interpreted cost. -/
def toTimeM [AddMonoid Cost] (charge : Event → Cost)
    (computation : TraceM Event α) : TimeM Cost α :=
  ⟨computation.ret, cost charge computation⟩

@[simp] theorem time_emit (event : Event) :
    (emit event).time = EventTrace.singleton event := rfl

@[simp] theorem ret_emit (event : Event) :
    (emit event).ret = () := rfl

@[simp] theorem events_emit (event : Event) :
    events (emit event) = [event] := rfl

@[simp] theorem time_emitMany (emitted : List Event) :
    (emitMany emitted).time = ⟨emitted⟩ := rfl

@[simp] theorem ret_emitMany (emitted : List Event) :
    (emitMany emitted).ret = () := rfl

@[simp] theorem events_emitMany (emitted : List Event) :
    events (emitMany emitted) = emitted := rfl

@[simp] theorem traceCost_zero [AddMonoid Cost] (charge : Event → Cost) :
    traceCost charge (0 : EventTrace Event) = 0 := by
  simp [traceCost]

@[simp] theorem traceCost_add [AddMonoid Cost] (charge : Event → Cost)
    (xs ys : EventTrace Event) :
    traceCost charge (xs + ys) = traceCost charge xs + traceCost charge ys := by
  simp [traceCost]

@[simp] theorem traceCost_singleton [AddMonoid Cost] (charge : Event → Cost)
    (event : Event) : traceCost charge (EventTrace.singleton event) = charge event := by
  simp [traceCost]

@[simp] theorem traceCost_time_pure [AddMonoid Cost] (charge : Event → Cost) (a : α) :
    traceCost charge (pure a : TraceM Event α).time = 0 := by
  simp [traceCost]

@[simp] theorem cost_pure [AddMonoid Cost] (charge : Event → Cost) (value : α) :
    cost charge (pure value : TraceM Event α) = 0 := by
  simp [cost]

@[simp] theorem cost_bind [AddMonoid Cost] (charge : Event → Cost)
    (computation : TraceM Event α) (next : α → TraceM Event β) :
    cost charge (computation >>= next) =
      cost charge computation + cost charge (next computation.ret) := by
  simp [cost]

/-- A pointwise upper bound on the emitted events bounds the interpreted natural-number cost. -/
theorem cost_le_cost (lower upper : Event → Nat) (computation : TraceM Event α)
    (h : ∀ event ∈ events computation, lower event ≤ upper event) :
    cost lower computation ≤ cost upper computation :=
  EventTrace.cost_mono_nat lower upper computation.time h

/-- Weighted cost after an event projection. -/
def projectedCost [AddMonoid Cost] (projection : Event → Event')
    (charge : Event' → Cost) (computation : TraceM Event α) : Cost :=
  cost (charge ∘ projection) computation

@[simp] theorem projectedCost_pure [AddMonoid Cost] (projection : Event → Event')
    (charge : Event' → Cost) (value : α) :
    projectedCost projection charge (pure value : TraceM Event α) = 0 := by
  simp [projectedCost]

@[simp] theorem projectedCost_bind [AddMonoid Cost] (projection : Event → Event')
    (charge : Event' → Cost) (computation : TraceM Event α)
    (next : α → TraceM Event β) :
    projectedCost projection charge (computation >>= next) =
      projectedCost projection charge computation +
        projectedCost projection charge (next computation.ret) := by
  simp [projectedCost]

@[simp] theorem ret_toTimeM [AddMonoid Cost] (charge : Event → Cost)
    (computation : TraceM Event α) : (toTimeM charge computation).ret = computation.ret := rfl

@[simp] theorem time_toTimeM [AddMonoid Cost] (charge : Event → Cost)
    (computation : TraceM Event α) : (toTimeM charge computation).time = cost charge computation :=
  rfl

end TraceM
end ResourceAware
