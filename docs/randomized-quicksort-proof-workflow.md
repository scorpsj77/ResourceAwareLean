# From operations to $O(n \log n)$: the Randomized quicksort proof workflow

This note explains how the randomized quicksort development connects executable operation
costs and pivot probabilities to a formal expected-runtime bound. The central idea is to keep
the algorithm, its random choices, and its costs together long enough to derive an exact
expectation recurrence. Only after that recurrence is established does the proof introduce an
upper bound and conclude that the expected cost is $O(n \log n)$.

## Proof roadmap

```text
instrumented quicksort program
        +
uniform pivot semantics
        +
exact operation-cost model
        |
        v
joint distribution of (result, accumulated cost)
        |
        v
exact expected-cost recurrence
        |
        v
harmonic-number upper envelope
        |
        v
Mathlib IsBigO theorem: expected cost is O(n log n)
```

## 1. The algorithm exposes the operations that can incur cost

The quicksort program is written against an operation signature with three observable
operations:

- `comparison` compares two keys;
- `baseCase` records the small-input sorting case;
- `choosePivotIndex` selects a pivot index for a nontrivial recursive call.

The signature is defined in
[`Algorithm.lean`](../TextbookAlgorithms/KleinbergTardos/Chapter13/RandomizedQuicksort/Algorithm.lean#L34-L38).
For an input of length greater than three, the program chooses a pivot, removes it, partitions
the remaining elements, and recursively sorts the two partitions. The implementation is in
[`quicksortProgram`](../TextbookAlgorithms/KleinbergTardos/Chapter13/RandomizedQuicksort/Algorithm.lean#L266-L278).

This instrumentation matters because the cost model assigns a cost to these operations rather
than to the Lean function as an opaque whole.

## 2. A cost model gives every operation an exact charge

The `CostModel` separates the costs of comparisons, base cases, and splitter frames. Its
`operationCost` function converts an operation request into a concrete natural-number cost:

[`ResourceModel.lean`](../TextbookAlgorithms/KleinbergTardos/Chapter13/RandomizedQuicksort/ResourceModel.lean#L31-L38)
and
[`operationCost`](../TextbookAlgorithms/KleinbergTardos/Chapter13/RandomizedQuicksort/ResourceModel.lean#L116-L120).

The proof studies two models:

| Operation | Comparison-only model | Unit textbook model |
| --- | ---: | ---: |
| One comparison | $1$ | $1$ |
| One base-case marker | $0$ | $1$ |
| Pivot/splitter frame on an input of length $n$ | $0$ | $n$ |

The comparison-only model isolates the number of key comparisons. The textbook model also
charges for the recursive splitter frame and the small-input base case. Their definitions are
in
[`ResourceModel.lean`](../TextbookAlgorithms/KleinbergTardos/Chapter13/RandomizedQuicksort/ResourceModel.lean#L64-L89).

Partitioning is also exact: the program compares the pivot with each of the other $n-1$
elements once. Consequently, partitioning an input of length $n-1$ has comparison cost
exactly $n-1$, as proved by
[`interpret_partitionProgram_comparisonOnly`](../TextbookAlgorithms/KleinbergTardos/Chapter13/RandomizedQuicksort/Complexity.lean#L268-L285).

## 3. The interpreter combines exact charges with exact probabilities

Pivot selection uses a uniform probability distribution over the finite set of valid indices:

[`PivotBackend.uniform`](../TextbookAlgorithms/KleinbergTardos/Chapter13/RandomizedQuicksort/Interpreters.lean#L43-L45).

The measured interpreter handles an operation by sampling its semantic result and attaching
the exact cost assigned by the selected model:

[`measuredHandler`](../TextbookAlgorithms/KleinbergTardos/Chapter13/RandomizedQuicksort/Interpreters.lean#L101-L105).

The result lives in `RandCostM Nat`. A `RandCostM` computation contains a joint probability
distribution over pairs `(result, cost)`, not two unrelated distributions:

[`RandCostM`](../ResourceAware/Program/RandCostM.lean#L35-L40).

When computations are sequenced, monadic `bind` samples both stages and adds their costs on
that particular execution branch:

[`RandCostM.bind`](../ResourceAware/Program/RandCostM.lean#L56-L65).

Keeping the distribution joint is essential. The pivot determines the two recursive
subproblems, so the result of the random choice is correlated with the future cost. Recording
only a return-value distribution and a separate cost distribution would lose that dependency.

## 4. Expected cost is computed from the joint distribution

`expectedCost` is the probability-weighted sum of the cost component of every branch:

[`expectedCost`](../ResourceAware/Program/RandCostM.lean#L440-L444).

The key sequencing law is:

$$
\mathbb E[\operatorname{cost}(m \mathbin{\texttt{>>=}} f)]
=
\mathbb E[\operatorname{cost}(m)]
+
\mathbb E_{a \leftarrow m}
  [\mathbb E[\operatorname{cost}(f(a))]].
$$

It is formalized by
[`expectedCost_bind_split`](../ResourceAware/Program/RandCostM.lean#L493-L505).
For a uniform distribution over $n$ pivot indices, the weighted expectation becomes the
finite average

$$
\mathbb E[f(I)] = \frac{1}{n}\sum_{i=0}^{n-1} f(i).
$$

The generic uniform-distribution identity is
[`weightedSum_uniformOfFintype`](../ResourceAware/Program/Randomized.lean#L146-L153).

## 5. These laws produce an exact comparison recurrence

Let $C(x)$ be the expected comparison cost of running randomized quicksort on the list
$x$, and let $n = |x|$. For $n>3$, selecting index $i$ produces lower and upper
partitions $L_i$ and $U_i$. The Lean proof derives the equality

$$
C(x)
=
\frac{1}{n}
\sum_{i=0}^{n-1}
\left((n-1)+C(L_i)+C(U_i)\right).
$$

This is not an assumed recurrence. It follows from the interpreted program, the exact
partition cost, cost addition under `bind`, and the uniform pivot distribution. The theorem is
[`expectedCost_quicksort_recurrence`](../TextbookAlgorithms/KleinbergTardos/Chapter13/RandomizedQuicksort/Complexity.lean#L443-L462).

The small cases are exact as well. The sorting network uses zero, one, or three comparisons for
input sizes zero or one, two, or three respectively; its expected-cost theorem is proved in
[`Complexity.lean`](../TextbookAlgorithms/KleinbergTardos/Chapter13/RandomizedQuicksort/Complexity.lean#L288-L337).

## 6. Distinct pivot positions are reindexed by pivot rank

The exact recurrence initially sums over positions in the input list. To obtain the usual
quicksort recurrence, the proof reindexes those positions by the pivot's rank in sorted order.
For a duplicate-free input, this reindexing is a permutation:

[`pivotRankEquiv`](../TextbookAlgorithms/KleinbergTardos/Chapter13/RandomizedQuicksort/Complexity.lean#L119-L126).

A pivot of rank $k$ produces subproblems of sizes

$$
k \qquad\text{and}\qquad n-1-k.
$$

The two size results are proved in
[`linearPartition_lower_length_eq_rank`](../TextbookAlgorithms/KleinbergTardos/Chapter13/RandomizedQuicksort/Complexity.lean#L167-L170)
and
[`linearPartition_upper_length_eq`](../TextbookAlgorithms/KleinbergTardos/Chapter13/RandomizedQuicksort/Complexity.lean#L217-L220).
The recurrence can therefore be compared with the size-only form

$$
C_n
=
n-1
+
\frac{1}{n}
\sum_{k=0}^{n-1}
\left(C_k+C_{n-1-k}\right).
$$

## 7. A harmonic envelope bounds the exact recurrence

The development defines the comparison-cost envelope

$$
E_n = 3(n+1)H_n,
$$

where $H_n$ is the $n$-th harmonic number:

[`expectedComparisonEnvelope`](../TextbookAlgorithms/KleinbergTardos/Chapter13/RandomizedQuicksort/Complexity.lean#L467-L468).

It then proves that this envelope is a supersolution of the quicksort recurrence:

$$
n-1
+
\frac{1}{n}
\sum_{k=0}^{n-1}
\left(E_k+E_{n-1-k}\right)
\le E_n.
$$

See
[`expectedComparisonEnvelope_recurrence`](../TextbookAlgorithms/KleinbergTardos/Chapter13/RandomizedQuicksort/Complexity.lean#L569-L597).

A strong induction on the input length now replaces each actual recursive expected cost with
its envelope bound. Reindexing the pivot sum by rank puts it into exactly the form required by
the supersolution theorem. The result is the pointwise bound

$$
\mathbb E[\text{comparisons on }x]
\le 3(|x|+1)H_{|x|}
$$

for every duplicate-free input `x`. This is
[`quicksort_expectedComparisonCost_le`](../TextbookAlgorithms/KleinbergTardos/Chapter13/RandomizedQuicksort/Complexity.lean#L728-L791).

## 8. The harmonic bound yields $O(n \log n)$

The standard estimate

$$
H_n \le 1+\log n
$$

implies

$$
E_n = O(n(1+\log n)) = O(n\log n).
$$

The envelope's asymptotic theorem is
[`expectedComparisonEnvelope_isBigO`](../TextbookAlgorithms/KleinbergTardos/Chapter13/RandomizedQuicksort/Complexity.lean#L511-L532).
The development then defines a size-indexed expected comparison cost by running on
`List.range n`, proves it is bounded by the envelope, and composes the bounds using Mathlib's
`IsBigO` relation:

[`expectedComparisonsBySize_isBigO`](../TextbookAlgorithms/KleinbergTardos/Chapter13/RandomizedQuicksort/Complexity.lean#L828-L840).

Internally, the exact expectations and recurrence bounds use `ENNReal`, which can represent
infinite expectations. The size-indexed functions used by the final asymptotic statements
convert these values to `Real` only after proving that the relevant expectations are finite.

## 9. The textbook operation model reuses the comparison analysis

Let $T(x)$ be expected cost under the unit textbook model. On a nontrivial input of length
$n$, pivot selection contributes exactly $n$, partitioning contributes exactly $n-1$,
and the two recursive calls contribute their own branch-dependent costs. The resulting exact
recurrence is

$$
T(x)
=
n
+
\frac{1}{n}
\sum_{i=0}^{n-1}
\left((n-1)+T(L_i)+T(U_i)\right).
$$

It is proved in
[`expectedCost_textbookQuicksort_recurrence`](../TextbookAlgorithms/KleinbergTardos/Chapter13/RandomizedQuicksort/Complexity.lean#L1355-L1371).

Instead of solving a second recurrence from scratch, the proof relates textbook cost to the
already-analyzed comparison cost:

$$
T(x) \le 2C(x)+2|x|+1.
$$

The strong-induction proof is
[`textbookQuicksort_expectedCost_le`](../TextbookAlgorithms/KleinbergTardos/Chapter13/RandomizedQuicksort/Complexity.lean#L1435-L1545).
Substituting the harmonic comparison bound gives the larger envelope

$$
T_n
\le
2\bigl(3(n+1)H_n\bigr)+2n+1,
$$

which is still $O(n\log n)$. The final theorem is
[`expectedTextbookRuntimeBySize_isBigO`](../TextbookAlgorithms/KleinbergTardos/Chapter13/RandomizedQuicksort/Complexity.lean#L1657-L1669).

## Where exactness ends and asymptotic bounding begins

| Stage | Kind of result |
| --- | --- |
| Cost attached to each operation | Exact definition |
| Probability of each pivot index | Exact uniform distribution |
| Cost accumulated along each execution branch | Exact joint semantics |
| Comparison and textbook recurrences | Equality |
| Actual comparison cost versus harmonic envelope | Inequality |
| Textbook cost versus comparison cost | Inequality |
| Harmonic envelope versus $n\log n$ | Asymptotic upper bound |

The proof therefore does not begin by assuming that randomized quicksort costs
$O(n\log n)$. It begins with the exact probabilistic execution semantics, derives the
expected-cost recurrences from those semantics, and only then bounds their solutions.

## Current scope

The final expected-complexity results currently assume:

- uniformly selected pivot indices;
- duplicate-free inputs, which make pivot positions equivalent to distinct ranks;
- either the comparison-only model or the specific unit textbook model.

The repository also defines a general `CostModel.IsBoundedBy` interface, but the randomized
quicksort development does not yet use it to derive a single expected $O(n\log n)$ theorem
for every bounded cost model. Generalizing the final theorem in that direction would make the
cost-model substitution story stronger.
