/-
Copyright (c) 2026 Jiyuan (Chai Yuen) Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan (Chai Yuen) Ji
-/
import Batteries.Data.Array.Lemmas
import Mathlib.Tactic

/-!
# Bounded named heaps

This file contains only the representation and its logical invariants.  The active heap array
`H` uses Lean's zero-based indexing.  `Position` is a fixed-size table, represented extensionally
as a function on `Fin capacity`; an inactive name maps to `none`.

The textbook's one-based tree arithmetic translates to

* `parent i = (i - 1) / 2`,
* `leftChild i = 2 * i + 1`,
* `rightChild i = 2 * i + 2`.
-/

universe u

namespace KleinbergPriorityQueue

/-- A named priority-queue entry.  Names are bounded by the queue capacity. -/
structure Entry (capacity : Nat) (Key : Type u) where
  name : Fin capacity
  key : Key
deriving Repr, DecidableEq

/--
The two arrays from the textbook presentation.

`H` contains precisely the active entries.  `Position` is a fixed-size map because its domain is
`Fin capacity`; it records a heap-array index for active names and `none` for inactive names.
-/
structure Heap (capacity : Nat) (Key : Type u) where
  H : Array (Entry capacity Key)
  Position : Fin capacity → Option Nat

/-- Zero-based parent index. -/
def parent (i : Nat) : Nat :=
  (i - 1) / 2

/-- Zero-based left-child index. -/
def leftChild (i : Nat) : Nat :=
  2 * i + 1

/-- Zero-based right-child index. -/
def rightChild (i : Nat) : Nat :=
  2 * i + 2

theorem parent_lt_size {i n : Nat} (hi : i < n) : parent i < n := by
  unfold parent
  exact lt_of_le_of_lt
    ((Nat.div_le_self (i - 1) 2).trans (Nat.sub_le i 1)) hi

theorem parent_lt_self {i : Nat} (hi : i ≠ 0) : parent i < i := by
  have hpos : 0 < i := Nat.pos_of_ne_zero hi
  unfold parent
  exact lt_of_le_of_lt (Nat.div_le_self (i - 1) 2) (Nat.sub_lt hpos (by omega))

namespace Heap

variable {capacity : Nat} {Key : Type u}

/-- Extensional form of updating the two Position cells affected by a swap. -/
def swapPosition (position : Fin capacity → Option Nat) (i j : Nat) :
    Fin capacity → Option Nat :=
  fun name =>
    match position name with
    | none => none
    | some k =>
        if k = i then some j
        else if k = j then some i
        else some k

/-- The number of active entries. -/
def size (heap : Heap capacity Key) : Nat :=
  heap.H.size

/-- Direct name-membership query supported by `Position`. -/
def contains (heap : Heap capacity Key) (name : Fin capacity) : Bool :=
  (heap.Position name).isSome

/--
Logical, representation-independent contents view.

It maps each bounded name to its active key, or to `none` when the name is inactive.  Public
algorithm results expose named `Entry` values; clients need not know their heap-array positions.
-/
def contents (heap : Heap capacity Key) (name : Fin capacity) : Option Key :=
  (heap.Position name).bind fun i => (heap.H[i]?).map Entry.key

/-- Heap order on all parent-child edges.  The root contributes the left disjunct. -/
def HeapOrdered [LE Key] (heap : Heap capacity Key) : Prop :=
  ∀ i : Fin heap.H.size,
    i.val = 0 ∨
      (heap.H[parent i.val]'(parent_lt_size i.isLt)).key ≤ heap.H[i].key

/--
`H` and `Position` are mutual inverses on active entries.

The forward direction says every array entry points back to its own index.  The reverse direction
says every nonempty Position cell points to an in-bounds entry carrying that name.
-/
def PositionInverse (heap : Heap capacity Key) : Prop :=
  (∀ i : Fin heap.H.size, heap.Position heap.H[i].name = some i.val) ∧
    (∀ name : Fin capacity,
      match heap.Position name with
      | none => True
      | some i => (heap.H[i]?).map Entry.name = some name)

/-- The three essential representation invariants. -/
def WellFormed [LE Key] (heap : Heap capacity Key) : Prop :=
  heap.H.size ≤ capacity ∧ heap.HeapOrdered ∧ heap.PositionInverse

instance [LinearOrder Key] (heap : Heap capacity Key) : Decidable heap.HeapOrdered := by
  unfold HeapOrdered
  exact Fintype.decidableForallFintype

instance (heap : Heap capacity Key) : Decidable heap.PositionInverse := by
  unfold PositionInverse
  letI : DecidablePred (fun name : Fin capacity =>
      match heap.Position name with
      | none => True
      | some i => (heap.H[i]?).map Entry.name = some name) := fun name => by
    cases hposition : heap.Position name with
    | none => simpa [hposition] using (inferInstance : Decidable True)
    | some i => simpa [hposition] using
        (inferInstance : Decidable ((heap.H[i]?).map Entry.name = some name))
  exact @instDecidableAnd _ _ Fintype.decidableForallFintype
    Fintype.decidableForallFintype

/-- Executable check for the mutual-inverse portion of the representation invariant. -/
def positionInverseB (heap : Heap capacity Key) : Bool :=
  decide heap.PositionInverse

@[simp] theorem positionInverseB_eq_true (heap : Heap capacity Key) :
    heap.positionInverseB = true ↔ heap.PositionInverse := by
  simp [positionInverseB]

instance [LinearOrder Key] (heap : Heap capacity Key) : Decidable heap.WellFormed :=
  by
    unfold WellFormed
    infer_instance

/--
Optional executable invariant check for diagnostics and checked wrappers.

The textbook operations do not call this whole-heap scan.
-/
def wellFormedB [LinearOrder Key] (heap : Heap capacity Key) : Bool :=
  decide heap.WellFormed

@[simp] theorem wellFormedB_eq_true [LinearOrder Key] (heap : Heap capacity Key) :
    heap.wellFormedB = true ↔ heap.WellFormed := by
  simp [wellFormedB]

/-- `StartHeap(capacity)`: the empty bounded heap and empty Position table. -/
def startHeap (capacity : Nat) (Key : Type u) : Heap capacity Key where
  H := #[]
  Position := fun _ => none

/--
Swap two valid heap-array positions and update the Position table in the same constant-size step.

The table transformer is the extensional form of writing the two affected Position cells.
Invalid indices leave the heap unchanged.
-/
def swapEntries (heap : Heap capacity Key) (i j : Nat) : Heap capacity Key :=
  if hi : i < heap.H.size then
    if hj : j < heap.H.size then
      { H := heap.H.swap i j hi hj
        Position := swapPosition heap.Position i j }
    else heap
  else heap

end Heap

end KleinbergPriorityQueue
