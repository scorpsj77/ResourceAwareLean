/-
Copyright (c) 2026 Jiyuan (Chai Yuen) Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan (Chai Yuen) Ji
-/
import ResourceAware.Foundations.PriorityQueue.DataStructure

/-!
# Textbook heap algorithms

The recursive control flow mirrors Section 2.5: Heapify-up follows parents, Heapify-down follows
the smaller child, deletion moves the last entry into the hole, and name-based operations consult
`Position`.

Public mutations perform only the textbook's local writes, comparisons, swaps, and root-to-leaf
repairs. Their invariants are established externally in `Correctness.lean`; optional whole-heap
validation wrappers live in `Checked.lean`. Ordinary failures return the original heap and
`false`/`none`.
-/

universe u

namespace KleinbergPriorityQueue

namespace Heap

variable {capacity : Nat} {Key : Type u} [LinearOrder Key]

/-! ## Local repairs -/

/-- Move a too-small entry toward the root.  Invalid indices leave the heap unchanged. -/
def heapifyUp (heap : Heap capacity Key) (i : Nat) : Heap capacity Key :=
  if hi : i < heap.H.size then
    if hroot : i = 0 then
      heap
    else
      let p := parent i
      if heap.H[i].key < (heap.H[p]'(parent_lt_size hi)).key then
        heapifyUp (heap.swapEntries i p) p
      else
        heap
  else
    heap
termination_by i
decreasing_by
  exact parent_lt_self hroot

/-- Select the existing child with smaller key, preferring the left child on a tie. -/
def smallerChild? (heap : Heap capacity Key) (i : Nat) : Option Nat :=
  let left := leftChild i
  if hleft : left < heap.H.size then
    let right := rightChild i
    if hright : right < heap.H.size then
      if heap.H[right].key < heap.H[left].key then some right else some left
    else
      some left
  else
    none

/-- Fuelled Heapify-down loop; one recursive call descends to the selected child. -/
def heapifyDownLoop : Nat → Heap capacity Key → Nat → Heap capacity Key
  | 0, heap, _ => heap
  | fuel + 1, heap, i =>
      match heap.smallerChild? i with
      | none => heap
      | some child =>
          match heap.H[i]?, heap.H[child]? with
          | some here, some below =>
              if below.key < here.key then
                heapifyDownLoop fuel (heap.swapEntries i child) child
              else
                heap
          | _, _ => heap

/-- Move a too-big entry toward the leaves.  Invalid indices leave the heap unchanged. -/
def heapifyDown (heap : Heap capacity Key) (i : Nat) : Heap capacity Key :=
  heapifyDownLoop heap.H.size heap i

/-! ## Public operations -/

/--
Insert a fresh named entry.

Failure is explicit for a full heap or an already-active name. On failure the original heap is
returned. Well-formedness is established by external theorems rather than an executable scan.
-/
def insert (heap : Heap capacity Key) (entry : Entry capacity Key) :
    Heap capacity Key × Bool :=
  if heap.H.size < capacity then
    if heap.contains entry.name then
      (heap, false)
    else
      let i := heap.H.size
      let appended : Heap capacity Key :=
        { H := heap.H.push entry
          Position := Function.update heap.Position entry.name (some i) }
      (appended.heapifyUp i, true)
  else
    (heap, false)

/-- Return the root entry without removing it. -/
def findMin (heap : Heap capacity Key) : Option (Entry capacity Key) :=
  heap.H[0]?

/--
Delete by zero-based heap position.

The last active entry is swapped into the hole, the removed name is marked inactive, and the
replacement is repaired upward or downward as appropriate.
-/
def delete (heap : Heap capacity Key) (i : Nat) :
    Heap capacity Key × Option (Entry capacity Key) :=
  match heap.H[i]? with
  | none => (heap, none)
  | some removed =>
      let last := heap.H.size - 1
      let moved := heap.swapEntries i last
      let shortened : Heap capacity Key :=
        { H := moved.H.pop
          Position := Function.update moved.Position removed.name none }
      let repaired :=
        if hi : i < shortened.H.size then
          if hroot : i = 0 then
            shortened.heapifyDown i
          else
            let p := parent i
            if shortened.H[i].key <
                (shortened.H[p]'(parent_lt_size hi)).key then
              shortened.heapifyUp i
            else
              shortened.heapifyDown i
        else
          shortened
      (repaired, some removed)

/-- `ExtractMin`: delete and return the root entry, or `none` for an empty heap. -/
def extractMin (heap : Heap capacity Key) :
    Heap capacity Key × Option (Entry capacity Key) :=
  heap.delete 0

/--
Return the array position for `name` only when the local `Position` entry points to an in-bounds
array entry carrying that same name.

This is a constant-size guard, not a whole-heap representation-invariant scan.
-/
def validPosition? (heap : Heap capacity Key) (name : Fin capacity) : Option Nat :=
  match heap.Position name with
  | none => none
  | some i =>
      match heap.H[i]? with
      | none => none
      | some entry => if entry.name = name then some i else none

/--
Delete an active element by name through `Position`; inactive or stale names fail with `none`.
-/
def deleteByName (heap : Heap capacity Key) (name : Fin capacity) :
    Heap capacity Key × Option (Entry capacity Key) :=
  match heap.validPosition? name with
  | none => (heap, none)
  | some i => heap.delete i

/--
Change an active name's key and choose Heapify-up, Heapify-down, or no movement by comparing the
new and old keys.  Inactive or stale Position entries fail and leave the heap unchanged.
-/
def changeKey (heap : Heap capacity Key) (name : Fin capacity) (newKey : Key) :
    Heap capacity Key × Bool :=
  match heap.validPosition? name with
  | none => (heap, false)
  | some i =>
      match heap.H[i]? with
      | none => (heap, false)
      | some oldEntry =>
          let updated : Heap capacity Key :=
            { heap with
              H := heap.H.setIfInBounds i { oldEntry with key := newKey } }
          let repaired :=
            if newKey < oldEntry.key then
              updated.heapifyUp i
            else if oldEntry.key < newKey then
              updated.heapifyDown i
            else
              updated
          (repaired, true)

/--
Derived bulk insertion, defined compositionally from ordinary `insert`.

It stops at the first failure and returns the heap produced by earlier successful insertions.
-/
def insertAll (heap : Heap capacity Key) (entries : List (Entry capacity Key)) :
    Heap capacity Key × Bool :=
  entries.foldl
    (fun (state : Heap capacity Key × Bool) entry =>
      if state.2 then state.1.insert entry else state)
    (heap, true)

end Heap

end KleinbergPriorityQueue
