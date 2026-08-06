import ResourceAware.Foundations.PriorityQueue.ResourceModel
import Mathlib.Analysis.Asymptotics.Defs

/-!
# Textbook asymptotic costs for bounded heaps

The resource model already assigns one closed-form upper bound to each public operation.  These
theorems connect those measurements to Mathlib's asymptotic notation.
-/

namespace KleinbergPriorityQueue

open Filter Asymptotics

/-- Real-valued linear comparison function. -/
abbrev linearReference (n : Nat) : Real :=
  n

/-- Real-valued constant comparison function. -/
abbrev constantReference (_ : Nat) : Real :=
  1

/-- Real-valued logarithmic heap-height comparison function. -/
abbrev logarithmicReference (n : Nat) : Real :=
  logarithmicCost n

theorem startHeapCost_isBigO :
    (fun n : Nat => (Operation.cost (.startHeap n) : Real)) =O[atTop]
      linearReference := by
  simpa [Operation.cost] using isBigO_refl linearReference atTop

theorem findMinCost_isBigO :
    (fun _ : Nat => (Operation.cost .findMin : Real)) =O[atTop]
      constantReference := by
  simpa [Operation.cost] using isBigO_refl constantReference atTop

theorem heapifyUpCost_isBigO :
    (fun i : Nat => (Operation.cost (.heapifyUp i) : Real)) =O[atTop]
      logarithmicReference := by
  simpa [Operation.cost] using isBigO_refl logarithmicReference atTop

theorem heapifyDownCost_isBigO :
    (fun n : Nat => (Operation.cost (.heapifyDown n) : Real)) =O[atTop]
      logarithmicReference := by
  simpa [Operation.cost] using isBigO_refl logarithmicReference atTop

theorem insertCost_isBigO :
    (fun n : Nat => (Operation.cost (.insert n) : Real)) =O[atTop]
      logarithmicReference := by
  simpa [Operation.cost] using isBigO_refl logarithmicReference atTop

theorem deleteCost_isBigO :
    (fun n : Nat => (Operation.cost (.delete n) : Real)) =O[atTop]
      logarithmicReference := by
  simpa [Operation.cost] using isBigO_refl logarithmicReference atTop

theorem extractMinCost_isBigO :
    (fun n : Nat => (Operation.cost (.extractMin n) : Real)) =O[atTop]
      logarithmicReference := by
  simpa [Operation.cost] using isBigO_refl logarithmicReference atTop

theorem deleteByNameCost_isBigO :
    (fun n : Nat => (Operation.cost (.deleteByName n) : Real)) =O[atTop]
      logarithmicReference := by
  simpa [Operation.cost] using isBigO_refl logarithmicReference atTop

theorem changeKeyCost_isBigO :
    (fun n : Nat => (Operation.cost (.changeKey n) : Real)) =O[atTop]
      logarithmicReference := by
  simpa [Operation.cost] using isBigO_refl logarithmicReference atTop

/-- The two capacity-sized arrays reserve linear total space. -/
theorem reservedSpace_isBigO :
    (fun n : Nat => ((SpaceUsage.reserved n).total : Real)) =O[atTop]
      linearReference := by
  simpa [SpaceUsage.reserved, SpaceUsage.total, Nat.cast_add] using
    (isBigO_refl linearReference atTop).add (isBigO_refl linearReference atTop)

end KleinbergPriorityQueue
