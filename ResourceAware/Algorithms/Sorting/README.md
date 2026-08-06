# Shared Sorting Infrastructure

This directory contains the small shared model and correctness specification for comparison-based
sorting case studies.

```text
Model.lean         comparison requests, semantic backends, and comparison-cost choices
Specification.lean sorted-permutation correctness target
```

Algorithm-specific operations remain inside their case-study directories. For example, MergeSort
under `TextbookAlgorithms/KleinbergTardos/Chapter05/MergeSort` adds split, merge, and base-case
operations, while randomized Quicksort under
`TextbookAlgorithms/KleinbergTardos/Chapter13/RandomizedQuicksort` adds pivot selection. A future
HeapSort development can add array, swap, and heap operations without expanding the shared
comparison signature.

Events, operation traces, weighted costs, and primitive-bound lifting come directly from
`ResourceAware.Program`; Sorting does not wrap those generic declarations. Algorithm-specific
models use `ResourceAware.Program.Semantics`, `CostModel`, and the generic runner without defining
another free-monad fold.
