# Kleinberg--Tardos Merge Sort

This directory formalizes the merge-sort presentation from Section 5.1, including correctness,
exact resource traces, the recurrence, and the `O(n log n)` result on power-of-two inputs.

It is separate from CSLib's original `TimeM Nat` comparison-counting MergeSort. The textbook model
observes split and merge structure as well as the comparisons that actually occur.

## Files

```text
Algorithm.lean       free program for split, merge, comparison, and base-case requests
ResourceModel.lean   semantics, reusable cost choices, runners, and primitive bounds
Correctness.lean     sorted-permutation correctness for pure and measured runs
Complexity.lean      operation profile, recurrence, and asymptotic theorem
```

Executable examples live in `Examples/MergeSort.lean`.

`MergeSort.lean` is the aggregate import for the completed case study. There is intentionally no
`Interpreters.lean`: `ResourceModel.lean` only supplies the MergeSort-specific semantics and cost
model, then uses the generic fold from `ResourceAware.Program.Interpreter`.

## One program, several views

```text
mergeSort : Program α
       |
       +-- evalWith backend
       |     pure result and final state
       |
       +-- interpretWith backend costModel
             result, final state, and measured events
```

When an operation-only view is needed, the same program and semantics can be passed directly to
`ResourceAware.Program.runOperations`; MergeSort does not maintain a wrapper for it.

The comparison backend determines Boolean answers independently of cost. The default backend uses
ascending `LinearOrder`; the reverse backend changes the ordering semantics without changing the
algorithm.

Theorems inherited from the generic layer show that:

- instrumentation preserves the semantic result;
- erasing event measurements yields the operation-only execution;
- changing only the cost model preserves the operation trace and result.

## Cost models

`CostModel.comparisonOnly` charges comparisons and assigns zero to split, merge, and base-case
events. Those zero-cost operations remain in the trace.

`CostModel.kleinberg` combines independently selected charges for:

```text
comparison work
split structural work
merge structural work excluding comparisons
base-case work
```

The structural backend may be size-sensitive. The linear textbook instance uses

```text
splitCost n           = splitUnit * n
mergeStructuralCost n = mergeUnit * n
```

but the abstract algorithm does not require those formulas. A different representation can give
constant-time splits or another merge cost by supplying a different backend.

`CostModel.IsBoundedBy` states pointwise bounds for primitive requests. The generic program layer
lifts these bounds over the complete free program, yielding

```text
exactCost run <= weightedOperationCost charge run.
```

The remaining MergeSort proof is cost-independent: it bounds the weighted operation profile and
solves the recurrence.

## Complexity connection

The proof has three explicit stages:

```text
measured execution
    exact primitive measurements
            |
            v
weighted operation profile
    primitive upper bounds lifted generically
            |
            v
recurrence and asymptotic theorem
    MergeSort-specific combinatorial proof
```

`SatisfiesRecurrence T c` packages the textbook recurrence for equal power-of-two halves, and
`theorem_5_2_substitution` proves

```text
T (2^k) <= c * 2^k * k.
```

The end-to-end theorem applies this to the exact measured cost of `mergeSort`. It is not merely a
count of comparison ticks: the selected model may charge comparisons, splitting, merging, and base
cases independently.

## Executable example

Run:

```sh
lake env lean Examples/MergeSort.lean
```

For `[4, 1, 3, 2]`, comparison-only execution records five comparisons. With unit comparison,
linear split, and linear structural merge costs, the same operation trace costs `5 + 4 + 4 = 13`.
The test also executes the program with the reverse comparison backend to obtain descending output.
