import ResourceAware.Foundations.PriorityQueue.Algorithm

/-!
# Optional checked priority-queue operations

The textbook operations in `Algorithm.lean` perform only local heap work. This module provides
diagnostic wrappers that validate a complete result before returning success. They are useful at
untrusted boundaries and in debugging, but they are intentionally excluded from the textbook
resource model.
-/

universe u

namespace KleinbergPriorityQueue

namespace Heap

variable {capacity : Nat} {Key : Type u} [LinearOrder Key]

/-- Validate a successful mutation, falling back to the original heap if validation fails. -/
def checkedMutation (old : Heap capacity Key) (result : Heap capacity Key × Bool) :
    Heap capacity Key × Bool :=
  if result.2 then
    if result.1.wellFormedB then result else (old, false)
  else
    result

/-- Diagnostic wrapper around textbook insertion. -/
def checkedInsert (heap : Heap capacity Key) (entry : Entry capacity Key) :
    Heap capacity Key × Bool :=
  checkedMutation heap (heap.insert entry)

/-- Validate a successful removal, falling back to the original heap if validation fails. -/
def checkedRemoval (old : Heap capacity Key)
    (result : Heap capacity Key × Option (Entry capacity Key)) :
    Heap capacity Key × Option (Entry capacity Key) :=
  if result.2.isSome then
    if result.1.wellFormedB then result else (old, none)
  else
    result

/-- Diagnostic wrapper around textbook positional deletion. -/
def checkedDelete (heap : Heap capacity Key) (i : Nat) :
    Heap capacity Key × Option (Entry capacity Key) :=
  checkedRemoval heap (heap.delete i)

/-- Diagnostic wrapper around textbook minimum extraction. -/
def checkedExtractMin (heap : Heap capacity Key) :
    Heap capacity Key × Option (Entry capacity Key) :=
  checkedRemoval heap heap.extractMin

/-- Diagnostic wrapper around textbook name-based deletion. -/
def checkedDeleteByName (heap : Heap capacity Key) (name : Fin capacity) :
    Heap capacity Key × Option (Entry capacity Key) :=
  checkedRemoval heap (heap.deleteByName name)

/-- Diagnostic wrapper around textbook key changes. -/
def checkedChangeKey (heap : Heap capacity Key) (name : Fin capacity) (newKey : Key) :
    Heap capacity Key × Bool :=
  checkedMutation heap (heap.changeKey name newKey)

end Heap

end KleinbergPriorityQueue
