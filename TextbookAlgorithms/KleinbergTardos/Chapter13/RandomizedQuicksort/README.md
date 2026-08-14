# Kleinberg--Tardos Randomized Quicksort

This directory implements the original randomized Quicksort from *Algorithm Design*, Section
13.5, pages 731--734. It does not implement the modified central-splitter rejection loop or the
section's Select algorithm.

The textbook input set is represented by a list. The proved textbook-facing statements assume
that this list has no duplicate keys. At every non-base call, the program
chooses a list position uniformly, removes that pivot, compares each remaining value with it once,
recursively sorts both partitions, and returns the lower result followed by the pivot and upper
result. The source's unspecified sort for sizes at most three is represented by a fixed sorting
network: zero comparisons for sizes zero and one, one for size two, and three for size three.

## Files

- `Algorithm.lean` defines the polynomial operation signature and the only recursive Quicksort
  implementation. It contains no concrete resource charges and does not recurse in a concrete
  effect monad.
- `ResourceModel.lean` assigns independent base-case, splitter-frame, and comparison charges.
- `Interpreters.lean` folds the free program into unmeasured `PMF`, measured `RandCostM Nat`,
  deterministic-pivot test semantics, and an optional observation-carrying view.
- `Correctness.lean` proves partition, base-case, join, free-program, and interpreted-run
  correctness.
- `Complexity.lean` derives comparison and textbook-cost recurrences from the interpreted run and
  proves the requested asymptotic bounds.
- `Examples/Algorithms/RandomizedQuicksort.lean` checks results, operation observations, exact costs under multiple models, and small
  theorem-backed endpoints.

Generic PMF and `RandCostM` folds live in `ResourceAware.Program.Randomized`. The shared comparison
request, semantic backend, and comparison-cost interface come from
`ResourceAware.Algorithms.Sorting.Model`.

Declarations in this case study live in the `KleinbergRandomizedQuicksort` namespace, matching the
short project namespaces used by the other textbook algorithms.

## One program, several interpretations

`quicksortProgram` is the algorithm. `RandCostM` is only an interpreter target: the public
comparison-counting `quicksort` runner is obtained by folding `quicksortProgram` with the uniform
pivot backend and comparison-only cost model. No Quicksort recursion is duplicated in `RandCostM`,
`PMF`, `StateM`, `TimeM`, or a trace monad.

The semantic backend selects a pivot distribution and comparison answers independently from the
cost model. Uniform pivots give the textbook semantics; deterministic first and last pivots are
provided for executable tests and supported worst-case witnesses.

## Proved results

For pairwise-distinct inputs over a linearly ordered type,
`quicksort_result_correct` proves that every supported result of the actual uniform
comparison-counting runner is a sorted permutation of the input. The proof passes through
`quicksortProgram_support_correct` and the cost-erasure bridge `interpret_ret_eq_eval`; it is not
merely a theorem about a separate pure list function.

The comparison-only model has these run-connected endpoints:

- `quicksort_expectedComparisonCost_le` and `quicksort_ecwp_comparisons_le` bound expected
  comparisons by a harmonic envelope;
- `expectedComparisonsBySize_isBigO` proves the resulting `O(n log n)` bound on canonical distinct
  inputs `List.range n`;
- `worstComparisonCost_eq_choose` identifies the attained maximum supported comparison count as
  `n.choose 2`, and `worstComparisonsBySize_isTheta` proves `Θ(n²)`.

For textbook running time, `textbookQuicksort` interprets the same free program with the unit
`CostModel.textbookModel`: one unit for each comparison and base-case marker, plus a size-linear
splitter-frame charge. `textbookQuicksort_expectedCost_le` couples that actual expected cost to the
comparison cost, and `expectedTextbookRuntimeBySize_isBigO` proves the textbook `O(n log n)` claim.
The maximum ranges over supported branches of all distinct `List Nat` inputs of length `n`;
`worstTextbookRuntimeBySize_isMaximum` proves it is attained, and
`worstTextbookRuntimeBySize_isTheta` proves the textbook `Θ(n²)` worst-case claim.

## Resource accounting

The comparison-only model charges exactly one unit for every key comparison. Pivot sampling, list
indexing and removal, list construction, append, recursion bookkeeping, and allocation are free in
that model.

The linear textbook model additionally permits:

- a bounded base-case charge excluding its key comparisons;
- a size-linear splitter-frame charge for sampling, pivot access/removal, non-comparison partition
  structure, and final glue;
- an independently bounded charge for each key comparison.

The splitter-frame charge always excludes comparisons, so no unit of work is counted twice. The
functional list implementation allocates partition and output list structure, and the optional
observation interpreter stores an execution trace. Neither allocation nor peak live space is a
requested metric in this case study.

## Termination

The program uses well-founded recursion on input length. A pivot response is a valid finite index,
so erasing it removes exactly one element. The partition helper returns lower and upper lists with
a certificate that their concatenation permutes the erased remainder. Consequently both recursive
arguments are shorter for every possible free-program continuation response, independently of a
particular interpreter's support.

## Build and inspect

From the repository root, run:

    lake build ResourceAware.Program.Randomized
    lake build TextbookAlgorithms.KleinbergTardos.Chapter13.RandomizedQuicksort.Algorithm
    lake build TextbookAlgorithms.KleinbergTardos.Chapter13.RandomizedQuicksort.ResourceModel
    lake build TextbookAlgorithms.KleinbergTardos.Chapter13.RandomizedQuicksort.Interpreters
    lake build TextbookAlgorithms.KleinbergTardos.Chapter13.RandomizedQuicksort.Correctness
    lake build TextbookAlgorithms.KleinbergTardos.Chapter13.RandomizedQuicksort.Complexity
    lake build Examples.Algorithms.RandomizedQuicksort
    lake build ResourceAware
    lake build TextbookAlgorithms
    lake build
    lake env lean Examples/Algorithms/RandomizedQuicksort.lean

Uniform PMFs are noncomputable, so their exact probability and expectation checks are kernel
proofs. Runtime `#eval` output, when present, is limited to deterministic-pivot views.

## Boundaries

The formalization deliberately excludes the modified central-splitter rejection loop,
Select/median-finding, duplicate-key handling as an advertised interface, an in-place imperative
array implementation, and an exact closed-form expected-comparison formula. The comparison model
does not charge list allocation, pivot access/removal, recursion bookkeeping, or evaluator time;
the textbook model covers these only through its stated unit linear abstraction. Neither model
claims an allocation or peak-live-space bound.
