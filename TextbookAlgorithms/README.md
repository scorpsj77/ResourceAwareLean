# Textbook Formalizations

This tree preserves the source structure and theorem ownership of textbook case studies.

```text
KleinbergTardos/
  Chapter03/
    BFS.lean
    BFS/
    DFS.lean
    DFS/
  Chapter04/
    Dijkstra.lean
    Dijkstra/
  Chapter05/
    MergeSort.lean
    MergeSort/
  Chapter13/
    RandomizedQuicksort.lean
    RandomizedQuicksort/
```

Each completed algorithm has an aggregate module and a source directory with:

```text
Algorithm.lean       source-shaped abstract free program
ResourceModel.lean   semantic/cost choices and thin runners
Correctness.lean     functional and structural proofs
Complexity.lean      exact and asymptotic resource proofs
```

Executable checks live in the top-level `Examples/` library. Reusable execution belongs in
`ResourceAware.Program`; family-specific semantics live in `ResourceAware/Algorithms`. Randomized
Quicksort additionally has `Interpreters.lean`, which connects its free program to `PMF`,
`RandCostM`, and traced randomized semantics. Reusable effects and algorithm infrastructure belong
in `ResourceAware`; upstream CSLib declarations remain in `Cslib`.
