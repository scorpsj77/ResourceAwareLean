/-
Copyright (c) 2026 Jiyuan (Chai Yuen) Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan (Chai Yuen) Ji
-/
import ResourceAware.Foundations.PriorityQueue

/-!
# Infrastructure example: priority queues

These examples check semantic results, Position consistency, the main well-formedness predicate,
and one aggregate measurement per operation.
-/

namespace KleinbergPriorityQueue.Test

open KleinbergPriorityQueue

set_option linter.style.nativeDecide false

abbrev Capacity := 10
abbrev Name := Fin Capacity
abbrev NatHeap := Heap Capacity Nat

def entry (name : Name) (key : Nat) : Entry Capacity Nat :=
  ⟨name, key⟩

def empty : NatHeap :=
  Heap.startHeap Capacity Nat

def insertOne (heap : NatHeap) (name : Name) (key : Nat) : NatHeap :=
  (heap.insert (entry name key)).1

/-- Name `3` moves from index 3 to the root in two Heapify-up iterations. -/
def upward : NatHeap :=
  insertOne
    (insertOne
      (insertOne
        (insertOne empty 0 9)
        1 7)
      2 8)
    3 1

/-- A larger heap whose minimum extraction moves the last key down multiple levels. -/
def populated : NatHeap :=
  insertOne
    (insertOne
      (insertOne
        (insertOne upward 4 3)
        5 4)
      6 5)
    7 6

def extracted := populated.extractMin
def deletedAtTwo := extracted.1.delete 2
def deletedByName := extracted.1.deleteByName 6

/-- Decreasing name `0` from `9` to `0` requires multiple upward moves. -/
def decreased := populated.changeKey 0 0

/-- Increasing the root name `3` from `1` to `20` requires multiple downward moves. -/
def increased := populated.changeKey 3 20

def duplicate := populated.insert (entry 1 100)
def inactiveChange := populated.changeKey 9 0
def inactiveDelete := populated.deleteByName 9
def invalidPositionDelete := populated.delete 99
def equalChange := populated.changeKey 4 3
def checkedExtracted := populated.checkedExtractMin
def checkedDecreased := populated.checkedChangeKey 0 0

/--
A malformed heap whose Position entry for name `1` points in bounds to the entry for name `0`.

Name-based mutations must reject this local mismatch rather than mutating or deleting name `0`.
-/
def stalePosition : Heap 2 Nat where
  H := #[⟨0, 10⟩]
  Position := fun name => if name = 1 then some 0 else none

def staleChange := stalePosition.changeKey 1 3
def staleDelete := stalePosition.deleteByName 1

def fullTiny : Heap 2 Nat :=
  let first := (Heap.startHeap 2 Nat).insert ⟨0, 2⟩ |>.1
  (first.insert ⟨1, 1⟩).1

def fullInsertion := fullTiny.insert ⟨0, 0⟩

def tied : NatHeap :=
  insertOne (insertOne (insertOne empty 0 2) 1 1) 2 1

def tiedAfterExtract := tied.extractMin.1

/-! ## Repeated-insertion initialization -/

def infinity : Nat := 1000

def initializationEntries : List (Entry Capacity Nat) :=
  [entry 0 infinity, entry 1 infinity, entry 2 infinity, entry 3 0,
    entry 4 infinity, entry 5 infinity, entry 6 infinity, entry 7 infinity,
    entry 8 infinity, entry 9 infinity]

def initialized := empty.insertAll initializationEntries

def duplicateInitialization :=
  empty.insertAll [entry 0 7, entry 0 3]

def capacityInitialization : Heap 2 Nat × Bool :=
  (Heap.startHeap 2 Nat).insertAll [⟨0, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩]

theorem initialization_full_distinct_names :
    (initializationEntries.map Entry.name).Nodup := by
  native_decide

theorem initialization_full_success :
    initialized.2 = true ∧ initialized.1.H.size = Capacity := by
  native_decide

theorem initialization_exact_keys :
    ∀ name : Name,
      initialized.1.contents name =
        some (if name = 3 then 0 else infinity) := by
  native_decide

theorem initialization_unique_source_minimum :
    initialized.1.findMin = some (entry 3 0) ∧
      ∀ name : Name, name ≠ 3 →
        initialized.1.contents 3 = some 0 ∧
          initialized.1.contents name = some infinity ∧ 0 < infinity := by
  native_decide

theorem initialization_tied_infinity_keys :
    initialized.1.contents 0 = initialized.1.contents 1 ∧
      initialized.1.contents 1 = initialized.1.contents 9 ∧
      initialized.1.contents 9 = some infinity := by
  native_decide

theorem initialization_wellFormed :
    initialized.1.WellFormed := by
  native_decide

theorem initialization_positionInverse :
    initialized.1.PositionInverse := by
  native_decide

theorem initialization_duplicate_failure :
    duplicateInitialization.2 = false ∧
      duplicateInitialization.1.H.size = 1 ∧
      duplicateInitialization.1.contents 0 = some 7 := by
  native_decide

theorem initialization_capacity_failure :
    capacityInitialization.2 = false ∧
      capacityInitialization.1.H.size = 2 := by
  native_decide

theorem initialization_exact_time :
    (Heap.measuredStartHeap Capacity Nat).measurement +
          (empty.measuredInsertAll initializationEntries).measurement =
        Capacity + repeatedInsertionCost 0 Capacity ∧
      (Heap.measuredStartHeap Capacity Nat).measurement +
          (empty.measuredInsertAll initializationEntries).measurement = 39 := by
  native_decide

theorem initialization_exact_space :
    (SpaceUsage.reserved Capacity).total = 2 * Capacity := by
  native_decide

/-! ## Upward and downward movement -/

example : upward.H[0]? = some (entry 3 1) := by native_decide
example : upward.Position 3 = some 0 := by native_decide
example : upward.Position 0 = some 3 := by native_decide
example : upward.contents 3 = some 1 := by native_decide
example : upward.WellFormed := by native_decide

example : extracted.2 = some (entry 3 1) := by native_decide
example : extracted.1.findMin = some (entry 4 3) := by native_decide
example : extracted.1.Position 3 = none := by native_decide
example : extracted.1.Position 7 = some 1 := by native_decide
example : extracted.1.WellFormed := by native_decide

/-! ## Deletion by position and name -/

example : deletedAtTwo.2 = some (entry 5 4) := by native_decide
example : deletedAtTwo.1.contains 5 = false := by native_decide
example : deletedAtTwo.1.H.size = 6 := by native_decide
example : deletedAtTwo.1.WellFormed := by native_decide

example : deletedByName.2 = some (entry 6 5) := by native_decide
example : deletedByName.1.Position 6 = none := by native_decide
example : deletedByName.1.WellFormed := by native_decide

/-! ## Key changes in both directions -/

example : decreased.2 = true := by native_decide
example : decreased.1.findMin = some (entry 0 0) := by native_decide
example : decreased.1.Position 0 = some 0 := by native_decide
example : decreased.1.WellFormed := by native_decide

example : increased.2 = true := by native_decide
example : increased.1.contents 3 = some 20 := by native_decide
example : increased.1.Position 3 = some 7 := by native_decide
example : increased.1.WellFormed := by native_decide

/-! ## Explicit failure behavior -/

example : duplicate.2 = false := by native_decide
example : duplicate.1.H.size = populated.H.size := by native_decide
example : inactiveChange.2 = false := by native_decide
example : inactiveDelete.2 = none := by native_decide
example : invalidPositionDelete.2 = none := by native_decide
example : empty.extractMin.2 = none := by native_decide
example : fullInsertion.2 = false := by native_decide
example : equalChange.2 = true := by native_decide
example : equalChange.1.H.toList = populated.H.toList := by native_decide
example : staleChange.2 = false := by native_decide
example : staleChange.1.H.toList = stalePosition.H.toList := by native_decide
example : staleDelete.2 = none := by native_decide
example : staleDelete.1.H.toList = stalePosition.H.toList := by native_decide
example : ((Heap.startHeap 0 Nat).insertAll []).2 = true := by native_decide

/-! ## Optional diagnostic wrappers agree on these well-formed textbook results -/

example : checkedExtracted.1.H.toList = extracted.1.H.toList := by native_decide
example : checkedExtracted.2 = extracted.2 := by native_decide
example : checkedDecreased.1.H.toList = decreased.1.H.toList := by native_decide
example : checkedDecreased.2 = decreased.2 := by native_decide

/-! ## Ties: only the minimum key is specified, not a stable name order -/

example : tied.findMin.map Entry.key = some 1 := by native_decide
example : tiedAfterExtract.findMin.map Entry.key = some 1 := by native_decide
example : tiedAfterExtract.WellFormed := by native_decide

/-! ## Lightweight aggregate costs -/

example : (Heap.measuredStartHeap Capacity Nat).measurement = Capacity := by native_decide
example : (populated.measuredFindMin).measurement = 1 := by native_decide
example :
    (populated.measuredInsert (entry 8 10)).measurement =
      logarithmicCost populated.H.size := by native_decide
example :
    (populated.measuredExtractMin).measurement =
      logarithmicCost populated.H.size := by native_decide
example : (SpaceUsage.reserved Capacity).total = 2 * Capacity := by native_decide

#eval upward.H.toList
#eval extracted.1.H.toList
#eval decreased.1.H.toList
#eval increased.1.H.toList

end KleinbergPriorityQueue.Test
