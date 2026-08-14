/-
Copyright (c) 2026 Jiyuan (Chai Yuen) Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan (Chai Yuen) Ji
-/
import TextbookAlgorithms.KleinbergTardos.Chapter05.MergeSort.Complexity
import TextbookAlgorithms.KleinbergTardos.Chapter05.MergeSort.Correctness

/-!
# Algorithm example: Kleinberg merge sort

The same abstract program is interpreted under two cost models.  The ordered operation sequence
and sorted result are unchanged; only the measured event costs differ.
-/

namespace KleinbergMergeSort.Test

open ResourceAware ResourceAware.Algorithms

def input : List Nat := [4, 1, 3, 2]

def comparisonRun : TraceM (Event Nat) (List Nat × PUnit.{1}) :=
  interpret (CostModel.comparisonOnly (α := Nat)) (mergeSort input)

/-- A list-style model that charges one structural unit per input/output position. -/
def listStructuralBackend : StructuralCostBackend :=
  .linear 1 1

def kleinbergRun : TraceM (Event Nat) (List Nat × PUnit.{1}) :=
  interpret (CostModel.kleinberg (α := Nat) 1 listStructuralBackend) (mergeSort input)

def comparisonTwoRun : TraceM (Event Nat) (List Nat × PUnit.{1}) :=
  interpret (CostModel.kleinberg (α := Nat) 2 listStructuralBackend) (mergeSort input)

def descendingBackend : Sorting.ComparisonBackend Nat :=
  .reverse .linearOrder

def descendingRun : TraceM (Event Nat) (List Nat × PUnit.{1}) :=
  interpretWith descendingBackend (CostModel.comparisonOnly (α := Nat)) (mergeSort input)

def isComparison : Event Nat → Bool
  | ⟨.comparison _, _⟩ => true
  | _ => false

def isSplit : Event Nat → Bool
  | ⟨.split _, _⟩ => true
  | _ => false

def isMerge : Event Nat → Bool
  | ⟨.merge _, _⟩ => true
  | _ => false

def eventCount (predicate : Event Nat → Bool) (run : TraceM (Event Nat) β) : Nat :=
  (TraceM.events run).countP predicate

/-!
## Executed checks

These are `#guard` commands, not theorems.  Each is evaluated when this file is built and fails
the build if it does not hold, but none of them enters the logical environment or introduces an
axiom.

They cannot be stated as kernel-checked theorems: `mergeSort` and `mergeCore` are both defined by
well-founded recursion, which does not reduce definitionally, so `decide` cannot discharge them.
(The same is true of CSLib's own merge sort, which avoids the issue only by never evaluating on
concrete data.)  The alternative would be `native_decide`, which asserts the compiler's answer as
an axiom; `#guard` performs the same computation without dressing it as a proof.

The general correctness and complexity results — proved, kernel-checked, and free of these
concerns — live in `TextbookAlgorithms.KleinbergTardos.Chapter05.MergeSort`.
-/

-- Both interpretations execute the same sorting semantics.
#guard comparisonRun.ret.1 == [1, 2, 3, 4]

#guard kleinbergRun.ret.1 == [1, 2, 3, 4]

-- Comparison semantics can change independently of the program and its resource model.
#guard descendingRun.ret.1 == [4, 3, 2, 1]

-- The original comparison-only model observes five key comparisons.
#guard exactCost comparisonRun == 5

-- The backend charges split `4`, merge structure `4`, and five comparisons: total `13`.
#guard exactCost kleinbergRun == 13

-- With comparison unit `2`, the same five comparisons contribute `10`: total `18`.
#guard exactCost comparisonTwoRun == 18

-- The trace retains the exact execution order under either model.
#guard (TraceM.events comparisonRun).length == 9

#guard (TraceM.events kleinbergRun).length == 9

-- Abstract structural operations occur once; their backend-selected costs may exceed one.
#guard eventCount isSplit kleinbergRun == 1

#guard eventCount isComparison kleinbergRun == 5

#guard eventCount isMerge kleinbergRun == 1

-- Backend costs and comparison costs are accumulated without double counting.
#guard exactCost (interpret (CostModel.kleinberg (α := Nat) 1 listStructuralBackend)
    (request (α := Nat) (.split 4))) == 4

#guard exactCost (interpret (CostModel.kleinberg (α := Nat) 1 listStructuralBackend)
    (request (α := Nat) (.merge 4))) == 4

#eval (comparisonRun.ret.1 : List Nat)
#eval (TraceM.events comparisonRun : List (Event Nat))
#eval (exactCost comparisonRun : Nat)
#eval (TraceM.events kleinbergRun : List (Event Nat))
#eval (exactCost kleinbergRun : Nat)

end KleinbergMergeSort.Test
