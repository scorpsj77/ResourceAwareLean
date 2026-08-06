# Heap-Based Priority Queue

This foundation is a fresh, small formalization of the array-backed minimum heap from Section 2.5
of Kleinberg and Tardos. It is independent of the repository's earlier indexed-heap and
shortest-path infrastructure.

```text
DataStructure.lean  Entry, Heap, index arithmetic, contents, and invariants
Algorithm.lean      textbook heapify and public priority-queue operations
Checked.lean        optional whole-heap validation wrappers for debugging
ResourceModel.lean  one aggregate measurement per public operation
Correctness.lean    representation and public semantic theorems
Complexity.lean     Mathlib IsBigO statements
```

Executable semantic, `Position`, invariant, and cost checks live in
`Examples/PriorityQueue.lean`.

## Textbook correspondence

`Heap capacity Key` contains the two textbook arrays in one priority-queue value:

```text
H         active Array (Entry capacity Key)
Position  fixed table Fin capacity -> Option Nat
```

`H` is zero based. The book's one-based formulas therefore become:

```text
parent i      = (i - 1) / 2
leftChild i   = 2 * i + 1
rightChild i  = 2 * i + 2
```

The main invariant contains only the active-size bound, parent-child heap order, and the mutual
inverse law between `H` and `Position`. Active-name uniqueness is proved from that inverse rather
than stored separately. `contents` is the representation-independent view from a bounded name to
its optional active key.

## Public operations and failures

The implementation provides:

```text
startHeap
heapifyUp
heapifyDown
insert
findMin
delete
extractMin
deleteByName
changeKey
insertAll
contains
```

`insert` and `changeKey` return a heap and `Bool`; deletion and extraction return a heap and an
`Option Entry`. A full heap, duplicate insertion, invalid position, inactive name, or empty
extraction leaves the original heap unchanged and reports `false` or `none`. `changeKey` handles
decreases, increases, and equal keys. Comparisons are strict when choosing movement, so ties do
not promise a stable name order.

`swapEntries` changes both affected Position cells extensionally. The ordinary operations then
continue immediately with the next local heap step; they do not run `PositionInverse` or
`WellFormed` scans. Name-based mutations use `validPosition?` to check only that the selected
Position cell points in bounds to an entry carrying the requested name. This constant-size guard
rejects a stale local lookup without changing the logarithmic resource model. Correctness of the
ordinary operations is established by proofs in `Correctness.lean`.

`Checked.lean` provides opt-in `checkedInsert`, `checkedDelete`, `checkedExtractMin`,
`checkedDeleteByName`, and `checkedChangeKey` wrappers. These validate a successful result and
fall back to the old heap if validation fails. They are intended for debugging or untrusted
boundaries and are deliberately outside the textbook resource model.

## Dijkstra-facing surface

Names are `Fin capacity`, so graph instances can use vertex names directly and select `ENat` as
their ordered key type. `extractMin` returns a representation-independent named `Entry`, and
`changeKey` locates a named active vertex through `Position`. The Chapter 4 Dijkstra development
keeps tentative distances in its own state; no distance or predecessor table is mixed into this
queue. `insertAll` is merely a fold over ordinary insertion, not a permutation-based full-heap
primitive.

## Resource model

There is one natural-number measurement per textbook operation:

```text
StartHeap(N)                       N
FindMin                            1
Heapify-up/down and mutations      1 + log2 (n + 1)
InsertAll from size s              sum of insertion costs at sizes s .. s+k-1
reserved space                     2 * N
```

Thus a full repeated-insertion initialization from `startHeap N` is charged `N` plus the
successive insertion costs.

The model treats one heapify iteration as constant source-level work. It intentionally does not
count individual array reads/writes, Position accesses, size accesses, comparisons, or copying by
Lean's persistent `Array`. Because the core implementation contains no validation scan, its
visible control flow now matches this assigned logarithmic cost: a local Position lookup followed
by at most one root-to-leaf repair. This remains a source-level model, not a claim about literal
Lean VM runtime. In particular, initialization is the implementation's existing repeated
insertion convention; it is not claimed to match a textbook initialization routine
operation-for-operation. `Complexity.lean` states the resulting `O(N)`, `O(1)`, `O(log n)`, and
`O(N)` space bounds using Mathlib asymptotic notation.

## Correctness and proof boundary

Proved results include:

- empty-heap well-formedness;
- active-name uniqueness and valid Position lookup consequences;
- Position-inverse and logical-contents preservation by direct local swaps;
- size, Position-inverse, active-name, and logical-contents preservation by both heapify
  procedures;
- Heapify-up and Heapify-down restore heap order from their localized textbook preconditions;
- the root-minimum theorem and `findMin` correctness;
- insertion preserves well-formedness, grows by exactly one on success, stores the requested key,
  leaves every other logical entry unchanged, and rejects duplicate names or exhausted capacity;
- successful `insertAll` preserves well-formedness and the Position inverse; distinct, fresh
  capacity-fitting entries all succeed and receive exactly their requested keys;
- positional deletion returns exactly the entry formerly at that position;
- extraction from a nonempty heap succeeds, returns a minimum input entry, removes exactly that
  root name, preserves every other logical entry, and leaves a well-formed heap;
- changing an active key succeeds;
- `changeKey` stores exactly the requested key, leaves every other logical entry unchanged,
  preserves the active-name set, and leaves a well-formed heap for decreases, increases, and
  equal keys.

The remaining proof boundary is focused away from the Dijkstra path. This case study does not yet
package full well-formedness and exact-contents theorems for arbitrary positional deletion or
name-based deletion. Their executable cases remain covered in `Examples/PriorityQueue.lean`. The
optional checked wrappers can still validate all public mutations when useful. No claimed result
uses `sorry`.

Run the focused checks from the repository root:

```sh
lake env lean Examples/PriorityQueue.lean
lake build ResourceAware.Foundations.PriorityQueue
```
