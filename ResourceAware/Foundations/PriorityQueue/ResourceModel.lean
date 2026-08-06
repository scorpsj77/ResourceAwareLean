import ResourceAware.Foundations.PriorityQueue.Algorithm

/-!
# Lightweight priority-queue resource model

One public semantic operation receives one aggregate natural-number measurement.  Heapify work is
bounded by the height of a root-to-leaf path; the model deliberately does not expose separate
events for array reads, writes, Position accesses, size reads, comparisons, or persistent-array
copying. Queue initialization is the existing `insertAll` fold over `insert`; charging the
successive insertion sizes is an explicit implementation convention, not an
operation-for-operation claim about a textbook initialization routine.
-/

universe u

namespace KleinbergPriorityQueue

/-- Textbook-level operations, parameterized only by the size relevant to their cost. -/
inductive Operation where
  | startHeap (capacity : Nat)
  | heapifyUp (index : Nat)
  | heapifyDown (size : Nat)
  | insert (size : Nat)
  | insertAll (initialSize count : Nat)
  | findMin
  | delete (size : Nat)
  | extractMin (size : Nat)
  | deleteByName (size : Nat)
  | changeKey (size : Nat)
deriving Repr, DecidableEq

/-- A convenient closed-form bound for one root-to-leaf heap path. -/
def logarithmicCost (n : Nat) : Nat :=
  1 + Nat.log2 (n + 1)

/-- Aggregate cost of `count` successful insertions starting at `initialSize`. -/
def repeatedInsertionCost : Nat → Nat → Nat
  | _, 0 => 0
  | initialSize, count + 1 =>
      logarithmicCost initialSize + repeatedInsertionCost (initialSize + 1) count

namespace Operation

/-- Aggregate source-level time charged to one textbook operation. -/
def cost : Operation → Nat
  | .startHeap capacity => capacity
  | .findMin => 1
  | .heapifyUp index => logarithmicCost index
  | .insertAll initialSize count => repeatedInsertionCost initialSize count
  | .heapifyDown size
  | .insert size
  | .delete size
  | .extractMin size
  | .deleteByName size
  | .changeKey size => logarithmicCost size

end Operation

/-- A semantic result paired with its one aggregate operation measurement. -/
structure Measured (α : Type u) where
  result : α
  measurement : Nat
deriving Repr

/-- Attach the selected operation's aggregate measurement to a pure result. -/
def measure (operation : Operation) (result : α) : Measured α :=
  ⟨result, operation.cost⟩

namespace Heap

variable {capacity : Nat} {Key : Type u} [LinearOrder Key]

def measuredStartHeap (capacity : Nat) (Key : Type u) :
    Measured (Heap capacity Key) :=
  measure (.startHeap capacity) (startHeap capacity Key)

def measuredHeapifyUp (heap : Heap capacity Key) (i : Nat) :
    Measured (Heap capacity Key) :=
  measure (.heapifyUp i) (heap.heapifyUp i)

def measuredHeapifyDown (heap : Heap capacity Key) (i : Nat) :
    Measured (Heap capacity Key) :=
  measure (.heapifyDown heap.H.size) (heap.heapifyDown i)

def measuredInsert (heap : Heap capacity Key) (entry : Entry capacity Key) :
    Measured (Heap capacity Key × Bool) :=
  measure (.insert heap.H.size) (heap.insert entry)

/--
Measure the existing repeated-`insert` implementation of `insertAll`.

For successful initialization, the charged sizes are exactly the successive active sizes.
-/
def measuredInsertAll (heap : Heap capacity Key)
    (entries : List (Entry capacity Key)) :
    Measured (Heap capacity Key × Bool) :=
  measure (.insertAll heap.H.size entries.length) (heap.insertAll entries)

@[simp] theorem measuredStartHeap_insertAll_time (capacity : Nat) (Key : Type u)
    [LinearOrder Key] (entries : List (Entry capacity Key)) :
    ((startHeap capacity Key).measuredInsertAll entries).measurement =
      repeatedInsertionCost 0 entries.length := by
  rfl

@[simp] theorem repeatedInsertion_initialization_time (capacity : Nat) (Key : Type u)
    [LinearOrder Key] (entries : List (Entry capacity Key)) :
    (measuredStartHeap capacity Key).measurement +
        ((startHeap capacity Key).measuredInsertAll entries).measurement =
      capacity + repeatedInsertionCost 0 entries.length := by
  rfl

def measuredFindMin (heap : Heap capacity Key) :
    Measured (Option (Entry capacity Key)) :=
  measure .findMin heap.findMin

def measuredDelete (heap : Heap capacity Key) (i : Nat) :
    Measured (Heap capacity Key × Option (Entry capacity Key)) :=
  measure (.delete heap.H.size) (heap.delete i)

def measuredExtractMin (heap : Heap capacity Key) :
    Measured (Heap capacity Key × Option (Entry capacity Key)) :=
  measure (.extractMin heap.H.size) heap.extractMin

def measuredDeleteByName (heap : Heap capacity Key) (name : Fin capacity) :
    Measured (Heap capacity Key × Option (Entry capacity Key)) :=
  measure (.deleteByName heap.H.size) (heap.deleteByName name)

def measuredChangeKey (heap : Heap capacity Key) (name : Fin capacity) (newKey : Key) :
    Measured (Heap capacity Key × Bool) :=
  measure (.changeKey heap.H.size) (heap.changeKey name newKey)

end Heap

/-- Reserved source-level storage for the bounded heap array and fixed-size Position table. -/
structure SpaceUsage where
  heapArray : Nat
  positionTable : Nat
deriving Repr, DecidableEq

namespace SpaceUsage

def reserved (capacity : Nat) : SpaceUsage :=
  ⟨capacity, capacity⟩

def total (usage : SpaceUsage) : Nat :=
  usage.heapArray + usage.positionTable

@[simp] theorem repeatedInsertion_initialization_space (capacity : Nat) :
    (reserved capacity).total = 2 * capacity := by
  simp [reserved, total, Nat.two_mul]

end SpaceUsage

end KleinbergPriorityQueue
