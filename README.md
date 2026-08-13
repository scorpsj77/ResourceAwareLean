# ResourceAware

ResourceAwareLean supports the flexible analysis of algorithms under different
cost models. Algorithms are written as free programs over abstract operation
signatures, while their semantic backends and cost models are supplied
independently. The framework proves that changing only the cost model preserves
the returned value, final state, and erased operation trace. Because traces
record operations in execution order, the same trace can be evaluated under
multiple cost models, connecting exact modeled costs to asymptotic (`IsBigO`)
bounds. For randomized algorithms, `RandCostM` represents computations as
distributions over result-cost pairs, supporting branchwise cost accumulation
and expected-cost reasoning.

## Architecture

```text
textbook algorithm
      |
      v
free program over an operation signature      (ResourceAware/Program/Model)
      |
      +--> Semantics  (state transitions)     \  independent records,
      +--> CostModel  (transition measures)   /  proved non-interfering
      |
      v
generic interpreter -> measured event trace   (ResourceAware/Program/Interpreter)
      |
      +--> erase measurements -> operation profile   (ResourceAware/Effects/TraceM)
      +--> reweight profile   -> cost bounds         (ResourceAware/Program/Cost)
      |
      v
exact modeled cost -> Mathlib IsBigO asymptotic bounds
```

Libraries:

| Library | Contents |
| --- | --- |
| `ResourceAware` | The framework: free programs, semantics/cost records, generic interpreter, traces, erasure, reweighting, graph interface and resource models |
| `TextbookAlgorithms` | Kleinberg–Tardos case studies: BFS and DFS (Chapter 3), Dijkstra (Chapter 4), MergeSort (Chapter 5), and randomized Quicksort (Chapter 13) |
| `ThirdParty` | Local copy of the graph API from CSLib PR #503 (not authored by this project; see `ThirdParty/README.md`) |
| `Examples` | Executable demonstrations for BFS, DFS, Dijkstra, MergeSort, randomized Quicksort, and their reusable infrastructure |

## Status

All libraries build without `sorry`, `admit`, or custom axioms.

| Claim | Status |
| --- | --- |
| Semantics/cost separation with a proved independence theorem (`mapEvents_runFrom_eq`: changing only the cost model preserves the result, the final state, and the erased operation trace) | Proved |
| Erasure and reweighting: operation profiles as reusable proof objects (`weightedOperationCost_eq_of_operationTrace_eq`, `exactCost_le_weightedOperationCost`) | Proved |
| BFS and DFS: execution-linked reachability with representation-sensitive cost models (the same program under adjacency-list and adjacency-matrix models) | Proved |
| Dijkstra: execution-linked shortest paths over nonnegative weights with heap and graph-representation cost models | Proved |
| Exact modeled cost carried through to Mathlib `IsBigO` bounds (MergeSort bound stated on powers of two; representation-cost bounds for both graph models) | Proved, with the stated restrictions |
| MergeSort as introductory case study: correctness and exact/weighted cost under two cost models | Proved |
| Randomized Quicksort: sorted-permutation correctness and expected-cost bounds over the probabilistic cost interpreter | Proved |
| Executable examples that actually run (`#eval` demonstrations under `lake env lean`) | Working |

## Get started

```sh
lake build
```

This builds the `ResourceAware` and `TextbookAlgorithms` libraries. To build
everything, including the third-party graph API and the examples:

```sh
lake build ResourceAware TextbookAlgorithms ThirdParty Examples
```

Run an executable example and see its `#eval` output:

```sh
lake env lean Examples/BFS.lean
lake env lean Examples/DFS.lean
lake env lean Examples/Dijkstra.lean
lake env lean Examples/MergeSort.lean
lake env lean Examples/RandomizedQuicksort.lean
```

## Relationship to CSLib

This package depends on a pinned revision of
[CSLib](https://github.com/leanprover/cslib) and was developed against it. The
foundations it builds on — the `FreeM` free monad and the `TimeM` time monad —
are CSLib's. See `NOTICE` for attribution.
Selected reusable components of this package are candidates for focused
upstream contributions.

## Limitations

- **Exact cost is relative to the operation signature.** It is the sum of
  modeled measures for the operations an algorithm exposes, not the runtime of
  Lean's evaluator or of compiled code. Structural work outside the signature
  (list appends in BFS layers, the DFS stack, MergeSort's `length`/`take`/`drop`)
  is either absorbed into aggregate charges or unmodeled; each case study
  documents its accounting.
- **BFS tree certificate.** The executable BFS proves execution-linked exact
  reachability. The shortest-path-tree certificate is supplied by a separate
  noncomputable construction; it is not yet proved that the concrete edge list
  and level table emitted by the run form that shortest-path tree.
<!-- - **DFS certificate.** The executable iterative DFS proves execution-linked
  reachability. The Kleinberg–Tardos ancestor theorem is proved from an
  abstract recursive-tree certificate structure that the executable DFS does
  not currently construct. -->
- The MergeSort asymptotic bound is stated on inputs whose length is a power
  of two.

## Related work

### AlgoLean

[AlgoLean](https://github.com/Shreyas4991/Algolean) is a standalone Lean
package for algorithm complexity built on the same CSLib foundations, and is a
complementary design point. Both projects write algorithms as programs over an
operation signature with explicit primitive costs and derive complexity
structurally. This project's emphasis is on separating semantics from cost
models with a proved independence theorem and on ordered measured traces with
erasure and reweighting; AlgoLean covers ground this project does not, including
comparison-sort lower bounds, circuits, and Turing-machine models.

### References

- Kleinberg, J., & Tardos, É. (2006). *Algorithm design* (1st ed.). Pearson
  Education. Source for the textbook algorithms and complexity claims
  formalized in this repository.
- Barrett et al. (2026). *CSLib: The Lean computer science library*. arXiv.
  https://arxiv.org/abs/2602.04846. The accompanying
  [CSLib repository](https://github.com/leanprover/cslib) provides the `FreeM`
  and `TimeM` foundations used by the framework.
- Mathlib contributors. (2026). *mathlib4* [Computer software].
  https://github.com/leanprover-community/mathlib4. Provides the mathematical
  library used for correctness, probability, and asymptotic-complexity proofs.

## License and authorship

Apache License 2.0; see `LICENSE` and `NOTICE`. Authorship is recorded in
per-file headers and `CITATION.cff`. This is a student research project; see
`CONTRIBUTING.md`.
