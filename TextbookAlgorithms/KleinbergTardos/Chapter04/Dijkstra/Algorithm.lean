/-
Copyright (c) 2026 Lechen Wang, Daya Kumaran. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lechen Wang, Daya Kumaran
-/
import Batteries.Data.Array.Lemmas
import Mathlib.Algebra.Order.AddGroupWithTop
import ResourceAware.Foundations.PriorityQueue.Algorithm
import ResourceAware.Program.Model

/-!
# Kleinberg--Tardos Dijkstra algorithm

The program follows the priority-queue presentation from Section 4.4. It initializes all dense
vertex names, repeatedly extracts the minimum active name, scans that vertex's ordered outgoing
edge occurrences, and applies `ChangeKey` after each strict improvement.

Operations express independently variable semantic or resource choices. No operation in this
file carries a cost. `dijkstraLoop` uses one unit of explicit fuel per attempted extraction; the
default runner supplies the verified vertex count.
-/

universe u v

namespace KleinbergDijkstra

/-- Dijkstra stores finite edge weights in a distance domain with an unreachable value. -/
abbrev Distance (Weight : Type v) := WithTop Weight

/-- An outgoing edge occurrence whose target has already been encoded as a dense identifier. -/
structure IndexedOutgoingEdge (n : Nat) (Edge : Type u) (Weight : Type v) where
  edge : Edge
  target : Fin n
  weight : Weight
deriving Repr, DecidableEq

/-- The exact predecessor occurrence retained after a successful relaxation. -/
structure Predecessor (n : Nat) (Edge : Type u) (Weight : Type v) where
  source : Fin n
  /-- The array/heap name updated by this predecessor occurrence. -/
  target : Fin n
  edge : Edge
  weight : Weight
deriving Repr, DecidableEq

/-- Abstract requests used by the textbook algorithm. -/
inductive Op (n : Nat) (Edge : Type u) (Weight : Type v) : Type (max u v) where
  | initialize (source : Fin n)
  | extractMin
  | outgoingEdges (source : Fin n)
  | relaxationCandidate (sourceDistance : Distance Weight)
      (outgoing : IndexedOutgoingEdge n Edge Weight)
  | changeKey (predecessor : Predecessor n Edge Weight) (candidate : Distance Weight)
deriving Repr, DecidableEq

/-- Interpreter response type for every Dijkstra request. -/
abbrev Response {n : Nat} {Edge : Type u} {Weight : Type v} :
    Op n Edge Weight → Type (max u v)
  | .initialize _ => ULift Bool
  | .extractMin => ULift (Option (KleinbergPriorityQueue.Entry n (Distance Weight)))
  | .outgoingEdges _ => List (IndexedOutgoingEdge n Edge Weight)
  | .relaxationCandidate _ _ => ULift (Option (Distance Weight))
  | .changeKey _ _ => ULift Bool

/-- Polynomial signature for the textbook-local Dijkstra effects. -/
def Signature (n : Nat) (Edge : Type u) (Weight : Type v) :
    ResourceAware.Program.Signature.{max u v, max u v} where
  A := Op n Edge Weight
  B := fun operation ↦ Response operation

/-- Representation- and cost-independent Dijkstra programs. -/
abbrev Program (n : Nat) (Edge : Type u) (Weight : Type v) (α : Type (max u v)) :=
  ResourceAware.Program.Free (Signature n Edge Weight) α

variable {n : Nat} {Edge : Type u} {Weight : Type v}

/-- Lift one Dijkstra operation into the free monad. -/
def request (operation : Op n Edge Weight) :
    Program n Edge Weight (Response operation) :=
  ResourceAware.Program.request (signature := Signature n Edge Weight) operation

/-- Initialize the heap, distance table, predecessor table, and settled list. -/
def «initialize» (source : Fin n) : Program n Edge Weight (ULift Bool) :=
  request (.initialize source)

/-- Remove and return the minimum active heap entry. -/
def extractMin :
    Program n Edge Weight
      (ULift (Option (KleinbergPriorityQueue.Entry n (Distance Weight)))) :=
  request .extractMin

/-- Enumerate the ordered outgoing edge occurrences of one decoded source. -/
def outgoingEdges (source : Fin n) :
    Program n Edge Weight (List (IndexedOutgoingEdge n Edge Weight)) :=
  request (.outgoingEdges source)

/-- Inspect an active target and return its strictly improving candidate, if any. -/
def relaxationCandidate (sourceDistance : Distance Weight)
    (outgoing : IndexedOutgoingEdge n Edge Weight) :
    Program n Edge Weight (ULift (Option (Distance Weight))) :=
  request (.relaxationCandidate sourceDistance outgoing)

/-- Apply `ChangeKey` and update the matching result-table entries. -/
def changeKey (predecessor : Predecessor n Edge Weight) (candidate : Distance Weight) :
    Program n Edge Weight (ULift Bool) :=
  request (.changeKey predecessor candidate)

/--
Inspect each outgoing occurrence exactly once. Row access is a separate request; this recursion
accounts only for candidate inspection and successful heap/table changes.
-/
def processEdges (source : Fin n) (sourceDistance : Distance Weight) :
    List (IndexedOutgoingEdge n Edge Weight) → Program n Edge Weight PUnit
  | [] => pure .unit
  | outgoing :: rest => do
      let candidate ← relaxationCandidate sourceDistance outgoing
      match candidate.down with
      | none => processEdges source sourceDistance rest
      | some value =>
          let predecessor : Predecessor n Edge Weight :=
            ⟨source, outgoing.target, outgoing.edge, outgoing.weight⟩
          let _ ← changeKey predecessor value
          processEdges source sourceDistance rest

/--
Perform at most one `ExtractMin` per unit of fuel. The model's vertex count is the mathematical
bound used by the default runner; an unexpected empty heap stops the loop early.
-/
def dijkstraLoop : Nat → Program n Edge Weight PUnit
  | 0 => pure .unit
  | fuel + 1 => do
      let extracted ← extractMin
      match extracted.down with
      | none => pure .unit
      | some entry =>
          let row ← outgoingEdges entry.name
          processEdges entry.name entry.key row
          dijkstraLoop fuel

/-- Initialize every dense vertex name and run the priority-queue loop for exactly `n` fuel. -/
def dijkstra (n : Nat) (source : Fin n) : Program n Edge Weight PUnit := do
  let initialized ← «initialize» source
  if initialized.down then dijkstraLoop n else pure .unit

end KleinbergDijkstra
