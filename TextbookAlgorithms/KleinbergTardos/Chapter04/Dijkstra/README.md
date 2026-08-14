# Kleinberg--Tardos Dijkstra

This directory implements the priority-queue presentation of Dijkstra's algorithm from
Kleinberg and Tardos, *Algorithm Design*, Chapter 4, Section 4.4, textbook pages 137--142.
The heap convention and logarithmic operation costs follow Chapter 2, pages 57--65.

The implementation inserts every dense vertex name into a minimum heap, with key zero for the
source and infinity for every other vertex. It then performs at most `n` `ExtractMin` operations.
This is the page 141--142 priority-queue convention, including extraction of the source, rather
than the conceptual presentation in which the source is already in the settled set and the loop
has `n - 1` iterations.

The implementation is generic in an edge-weight type `Weight`. Edge occurrences and predecessors
store `Weight`, while heap keys, relaxation candidates, and result distances use
`Distance Weight`, an alias for `WithTop Weight`. The semantic runner assumes an additive
commutative monoid with a linear, canonical nonnegative order:

```lean
[AddCommMonoid Weight] [LinearOrder Weight] [CanonicallyOrderedAdd Weight]
```

These standard Mathlib assumptions supply zero, addition, total comparison, and the intended
nonnegative domain. They are satisfied by `Nat`, `NNRat`, and `NNReal`; there is only one Dijkstra
program and one semantic implementation for all three.

## Files

- `Algorithm.lean` defines occurrence-preserving edge and predecessor payloads, the five-operation
  free-monad signature, request helpers, structural row processing, and the fuelled Dijkstra loop.
- `ResourceModel.lean` supplies the named-heap/array semantics, separate unit and logarithmic heap
  cost models, pure and measured runners, exact-cost access, measurement-erasure interfaces, and
  source-level space components.
- `Correctness.lean` proves successful full-queue initialization, heap well-formedness, the
  active/settled partition, preservation through row processing and extraction, and the
  complete-loop settlement/empty-heap bridge. It also proves claim (4.14): the predecessor table
  recursively reconstructs exact edge occurrences of the stored weight, and every settled
  vertex's reconstructed path is shortest, for the pure and both measured runners.
- `Complexity.lean` proves claim (4.15), the exact adjacency-list operation decomposition, the
  actual heap-run finite bound, `O((m+n) log(n+1))`, the reachability bound `n ≤ m+1`, and the
  textbook `O(m log n)` corollary for nontrivial reachable inputs.
- `Examples/Algorithms/Dijkstra.lean` packages executable `Nat` and `NNRat` adjacency-list backends plus an `NNReal`
  mathematical smoke specialization. It checks semantic output, predecessor occurrences,
  operation counts, exact costs, theorem-backed complexity instances, fractional arithmetic, and
  agreement between interpreter views.

The implementation reuses:

- `ResourceAware.Foundations.Graph.Interface` and `ResourceModel` for the stable weighted graph
  interface, ordered edge-occurrence rows, vertex enumeration, dense `VertexIndex`, graph storage,
  and representation-sensitive row-query cost;
- `ResourceAware.Foundations.PriorityQueue` for the bounded named heap, repeated-insertion
  initialization, `ExtractMin`, `ChangeKey`, and logarithmic aggregate costs;
- `ResourceAware.Program` for free programs, deterministic semantics, measured and operation-only
  interpreters, ordered events, measurement erasure, and exact cost;
- `ResourceAware.Algorithms.ShortestPaths.Specification`, added with this implementation, for
  source-independent occurrence-preserving paths, additive path weight, and shortestness.

## Semantic and resource conventions

`Model.semantics` decodes heap identifiers through a graph-owned `VertexIndex`, obtains the
selected ordered weighted row, and re-encodes every target. A successful relaxation changes the
heap key and writes the same candidate and exact predecessor occurrence to fixed-length arrays.
The state retains extraction order in `settled`. Relaxation computes
`sourceDistance + (outgoing.weight : WithTop Weight)`.

Every measured event stores both the requested `Op` and a natural-number measurement:

- `initialize` costs `4*n + 1` in the unit profile. This aggregates heap setup, `n` unit
  insertions, two `n`-cell arrays, and the source write.
- `initialize` costs
  `3*n + 1 + KleinbergPriorityQueue.repeatedInsertionCost 0 n` in the heap profile.
- `extractMin` costs one in the unit profile and
  `KleinbergPriorityQueue.Operation.cost (.extractMin activeSize)` in the heap profile.
- `outgoingEdges source` costs the selected
  `WeightedResourceModel.weightedNeighborCost graph decodedSource`; the adjacency-list fixtures
  therefore charge one per returned edge occurrence.
- `relaxationCandidate` costs one target-activity lookup/addition/comparison inspection in both
  profiles.
- `changeKey` costs one in the unit profile and
  `KleinbergPriorityQueue.Operation.cost (.changeKey activeSize)` in the heap profile.

Heap-internal comparisons, swaps, position-table accesses, repairs, and array writes are included
only in their aggregate heap operation. Row retrieval is not charged again by candidate
inspection, and the comparison selecting a `ChangeKey` is not charged again by `ChangeKey`.
Literal persistent-array copying in the Lean runtime is outside this source-level RAM model.

`SpaceUsage` separates static `graphStorage` from the heap array, position table, distance table,
predecessor table, and at-most-`n` settled list. No formal space theorem is claimed in this pass.

## Weight specializations and execution

- `Nat` edge weights produce `WithTop Nat` (`ENat`) distances. The five-vertex,
  parallel/zero-weight, and singleton fixtures run natively and check the original exact outputs:
  distances, settlement and predecessor identities, empty heaps, operation counts, costs
  `56/83`, `27/36`, and `6/7`, and interpreter/trace agreement.
- `NNRat` edge weights produce `WithTop NNRat` distances. A two-vertex executable fixture uses a
  genuine `1/2` edge and checks that the resulting finite distance is `1/2`.
- `NNReal` edge weights produce `WithTop NNReal`, definitionally `ENNReal`, distances. This is the
  proof-oriented specialization intended for Stage 2. Smoke tests accept a `1/2` weight, prove
  two half segments total one, prove infinity absorbs a finite extension, and instantiate all
  semantic runners.

The generic algorithm and semantics are computable. Only the `NNReal` test definitions are
declared noncomputable because exact real comparison (and hence the `ENNReal` heap order) is
noncomputable in Lean. The `Nat` and `NNRat` specializations use the same definitions with
executable order instances; no parallel implementation is maintained.

## Termination

`processEdges` is structurally recursive over one finite outgoing row. `dijkstraLoop` consumes one
unit of explicit fuel for each attempted extraction. `dijkstra` and all public runners derive the
fuel from the complete duplicate-free vertex enumeration, so it is exactly the verified vertex
count. `Operational.dijkstraLoop_queueInvariant` proves that full initialization permits exactly
`n` successful extractions, leaves an empty heap, and settles every dense identifier exactly once.

## Proved complexity results

`Complexity.claim_4_15_adjacencyList` is connected to the actual
`Interpreter.runDecomposition` trace. For `n` enumerated vertices and `m` directed edge
occurrences, it proves:

- exactly `m` units of adjacency-row scan work;
- exactly `m` relaxation inspections and therefore exactly `2*m` non-queue work;
- exactly `n` `ExtractMin` requests;
- at most `m` `ChangeKey` requests.

`Complexity.claim_4_15_heap_exact_bound` bounds the exact measurements of
`Interpreter.runHeap` by

```text
initializationHeapCost n + n*logarithmicCost n + 2*m + m*logarithmicCost n.
```

The proof uses the active heap size at each real event, rather than replacing the run with an
unconnected arithmetic model. `heapCostUpperBound_isBigO` proves the resulting
`O((m+n) log(n+1))` envelope. Reachability supplies `n ≤ m+1` through
`vertexCount_le_directedEdgeOccurrenceCount_add_one_of_reachable`, and
`claim_4_15_heap_corollary` connects the actual run to the textbook `O(m log n)` family when
`n ≥ 2`.

## Build and run

From the repository root:

```sh
lake env lean ResourceAware/Algorithms/ShortestPaths/Specification.lean
lake env lean TextbookAlgorithms/KleinbergTardos/Chapter04/Dijkstra/Algorithm.lean
lake env lean TextbookAlgorithms/KleinbergTardos/Chapter04/Dijkstra/ResourceModel.lean
lake build TextbookAlgorithms.KleinbergTardos.Chapter04.Dijkstra.Correctness
lake build TextbookAlgorithms.KleinbergTardos.Chapter04.Dijkstra.Complexity
lake env lean Examples/Algorithms/Dijkstra.lean
lake build Examples.Algorithms.Dijkstra
lake build ResourceAware
lake build TextbookAlgorithms
lake build
```

The examples in `Examples/Algorithms/Dijkstra.lean` cover all three specializations described
above.

## Correctness theorem

`Correctness.claim_4_14` proves the pure-run result for every `Weight` satisfying the documented
additive and order assumptions, provided every enumerated vertex is reachable from the source.
`PredecessorReaches` is the recursive certificate:
each stored predecessor names an exact outgoing edge occurrence, its parent is already settled,
and its distance equation is exact. `predecessorReaches_path` turns that certificate into a
`NetworkPath` of the stored weight. The first-crossing cut lemma and heap-minimum property prove
shortestness. `claim_4_14_runDecomposition` and `claim_4_14_runHeap` lift the same result to both
cost-instrumented executions without changing their cost models.
