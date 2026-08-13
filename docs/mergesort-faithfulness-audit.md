---
title: "MergeSort Formalization"
subtitle: "Declaration Headers and Natural-Language Faithfulness Audit"
author: "Generated from Resource-Aware-CSLib source"
date: "12 August 2026"
---

**Audit purpose.** This dossier places every `def` and `theorem` header from the modular MergeSort formalization next to a statement-level natural-language reading. It is designed for a manual check of whether the Lean claim matches the intended textbook claim.

**Snapshot.** Commit `6194a4137cb8d4f2c2b57ca939e607161a541784`; formalization sources inspected on 12 August 2026. Source locations are line-based and may drift after edits.

**Coverage.** 59 declarations (56 public, 3 private). Declarations written with `abbrev`, `structure`, or `inductive`, along with proof bodies, namespace commands, imports, and executable examples, are intentionally excluded.

**How to audit an entry.** Check (1) quantified inputs and type-class assumptions, (2) graph, size, representation, or cost hypotheses, (3) the exact conclusion, and (4) which semantic or resource interpretation is being measured. The prose explains the statement; it does not claim more than the displayed header.

# Contents {#contents}

- [High-level faithfulness guide](#high-level-faithfulness-guide)
  - [Important scope boundaries](#important-scope-boundaries)
  - [Notation used in the headers](#notation-used-in-the-headers)
- [Algorithm: abstract program](#algorithm) (6 declarations)
- [Resource model, semantics, and runners](#resourcemodel) (30 declarations)
- [Correctness and graph-theoretic certificates](#correctness) (5 declarations)
- [Complexity and resource bounds](#complexity) (18 declarations)
- [Audit completion checklist](#audit-completion-checklist)
- [Source inventory](#source-inventory)

# High-level faithfulness guide {#high-level-faithfulness-guide}

The formalization uses one free MergeSort program with explicit comparison, base-case, split, and merge requests. Pure evaluation and measured interpretation share the same comparison semantics. Correctness proves a sorted permutation, while complexity first bounds a weighted operation profile, then solves the equal-halves recurrence on powers of two and transfers it to exact measured cost.

## Important scope boundaries {#important-scope-boundaries}

- Inputs of length at most two use `sortBase`; larger inputs split at `length / 2`, recursively sort both pieces, and merge them.
- `comparisonOnly` charges comparisons and leaves split, merge structure, and base cases free; `linearKleinberg` can charge all four categories.
- Structural merge cost excludes the separately recorded key comparisons.
- Correctness is representation- and cost-independent because measured interpretation preserves the pure semantic result.
- `SatisfiesRecurrence` assumes even recursive sizes, and the substitution theorem is stated on positive powers of two.
- The end-to-end asymptotic theorem is correspondingly restricted to the power-of-two size family; it is not a general all-input-size theorem.
- Exact cost means the sum of abstract primitive measurements selected by the supplied model, not wall-clock time or allocation cost.

## Notation used in the headers {#notation-used-in-the-headers}

- `Program α β`: a representation- and cost-independent free program returning a value of type `β`.
- `TraceM (Event α) β`: a deterministic result paired with an ordered trace of measured MergeSort events.
- `eval`: pure evaluation using the ascending linear-order backend.
- `interpret model`: measured evaluation under the selected primitive cost model.
- `exactCost`: the sum of measurements recorded in the trace.
- `weightedOperationCost charge`: the sum of a separately assigned charge over the same operation trace.
- `IsBoundedBy`: a pointwise assertion that a cost model's primitive measurements satisfy declared bounds.
- `=O[atTop]`: asymptotic big-O as the natural size index tends to infinity.

# Algorithm: abstract program {#algorithm}

[Back to contents](#contents)

**Source file:** `TextbookAlgorithms/KleinbergTardos/Chapter05/MergeSort/Algorithm.lean`  
**Declarations in this section:** 6

The free program and its algorithm-specific recursive helpers.

### Signature — def

*Source:* `Algorithm.lean:39`; public

```lean
def Signature (α : Type u) : ResourceAware.Program.Signature.{u, u}
```

**Natural-language explanation.** Polynomial signature for Kleinberg merge sort.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### request — def

*Source:* `Algorithm.lean:50`; public

```lean
def request (op : Op α) : Program α (Response op)
```

**Natural-language explanation.** Lift one merge-sort request into the free monad.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### mergeCore — def

*Source:* `Algorithm.lean:56`; public

```lean
def mergeCore : List α → List α → Program α (List α)
```

**Natural-language explanation.** Merge two sorted lists, requesting one abstract key comparison at every comparison step.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### merge — def

*Source:* `Algorithm.lean:69`; public

```lean
def merge (xs ys : List α) : Program α (List α)
```

**Natural-language explanation.** Request structural recombination, then execute its separately observed key comparisons.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### sortBase — def

*Source:* `Algorithm.lean:74`; public

```lean
def sortBase : List α → Program α (List α)
```

**Natural-language explanation.** Sort Kleinberg's constant-size base cases.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### mergeSort — def

*Source:* `Algorithm.lean:91`; public

```lean
def mergeSort (xs : List α) : Program α (List α)
```

**Natural-language explanation.** Kleinberg's merge sort.  Unlike CSLib's original comparison-counting version, this formulation bottoms out at size two and explicitly observes division, recombination, and every key comparison.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.


# Resource model, semantics, and runners {#resourcemodel}

[Back to contents](#contents)

**Source file:** `TextbookAlgorithms/KleinbergTardos/Chapter05/MergeSort/ResourceModel.lean`  
**Declarations in this section:** 30

The selected semantic backends, cost interpretation, runner, and space model.

### free — def

*Source:* `ResourceModel.lean:38`; public

```lean
def free : StructuralCostBackend
```

**Natural-language explanation.** Treat structural sequence operations as free.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### linear — def

*Source:* `ResourceModel.lean:46`; public

```lean
def linear (splitUnit mergeUnit : Nat) : StructuralCostBackend
```

**Natural-language explanation.** A convenient linear backend: splitting a size-`n` problem costs `splitUnit * n`, and structurally forming its merged output costs `mergeUnit * n`.  Comparisons are deliberately not included.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### recurrenceCoefficient — def

*Source:* `ResourceModel.lean:68`; public

```lean
def recurrenceCoefficient (bounds : CostBounds) : Nat
```

**Natural-language explanation.** Coefficient contributed by all nonrecursive work at one merge-sort level.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### comparisonOnly — def

*Source:* `ResourceModel.lean:83`; public

```lean
def comparisonOnly (comparisonUnit : Nat := 1) : CostModel α
```

**Natural-language explanation.** Count key comparisons at a selected constant rate and make structural operations free.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### kleinberg — def

*Source:* `ResourceModel.lean:94`; public

```lean
def kleinberg (comparisonUnit : Nat) (structural : StructuralCostBackend) : CostModel α
```

**Natural-language explanation.** Kleinberg's comparison policy combined with an independently selected structural backend. Each actual key comparison costs `comparisonUnit`.  The backend supplies the aggregate structural costs of a split and a merge and must exclude key-comparison work from `mergeStructuralCost`.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### linearKleinberg — def

*Source:* `ResourceModel.lean:100`; public

```lean
def linearKleinberg (comparisonUnit splitUnit mergeUnit : Nat) : CostModel α
```

**Natural-language explanation.** Kleinberg's comparison policy with a convenient linear structural backend.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### linearKleinbergBounds — def

*Source:* `ResourceModel.lean:104`; public

```lean
def linearKleinbergBounds (comparisonUnit splitUnit mergeUnit : Nat) : CostBounds
```

**Natural-language explanation.** Primitive bounds realized by the linear Kleinberg cost model.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### kleinbergCoefficient — def

*Source:* `ResourceModel.lean:114`; public

```lean
def kleinbergCoefficient (comparisonUnit splitUnit mergeUnit : Nat) : Nat
```

**Natural-language explanation.** One valid coefficient for Kleinberg's recurrence: the split, structural-merge, and comparison coefficients.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### linearKleinberg_isBoundedBy — theorem

*Source:* `ResourceModel.lean:118`; public

```lean
theorem linearKleinberg_isBoundedBy (comparisonUnit splitUnit mergeUnit : Nat) :
    (linearKleinberg (α := α) comparisonUnit splitUnit mergeUnit).IsBoundedBy
      (linearKleinbergBounds comparisonUnit splitUnit mergeUnit)
```

**Natural-language explanation.** The linear Kleinberg model satisfies its declared primitive bounds.

**Audit focus.** The bound is pointwise over primitive operations; inspect the selected constants and size factors.

### linearKleinbergBounds_recurrenceCoefficient — theorem

*Source:* `ResourceModel.lean:124`; public; attributes: `@[simp]`

```lean
@[simp] theorem linearKleinbergBounds_recurrenceCoefficient
    (comparisonUnit splitUnit mergeUnit : Nat) :
    (linearKleinbergBounds comparisonUnit splitUnit mergeUnit).recurrenceCoefficient =
      kleinbergCoefficient comparisonUnit splitUnit mergeUnit
```

**Natural-language explanation.** The recurrence coefficient derived from the linear Kleinberg bounds is exactly the sum of the comparison, split, and structural-merge units.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### semantics — def

*Source:* `ResourceModel.lean:136`; public

```lean
def semantics (backend : Sorting.ComparisonBackend α) :
    ResourceAware.Program.Semantics (Signature α) PUnit
```

**Natural-language explanation.** Build the pure operation semantics: comparisons use the selected backend, while base-case, split, and merge requests return unit and carry no mutable state.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### measuredCostModel — def

*Source:* `ResourceModel.lean:146`; public

```lean
def measuredCostModel (model : CostModel α) :
    ResourceAware.Program.CostModel (Signature α) PUnit Nat
```

**Natural-language explanation.** Turn a MergeSort cost model into primitive event measurements for comparisons, base cases, splits, and structural merges.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### evalWith — def

*Source:* `ResourceModel.lean:155`; public

```lean
def evalWith (backend : Sorting.ComparisonBackend α) (program : Program α β) : β
```

**Natural-language explanation.** Evaluate a free MergeSort program with the selected comparison backend and return only its semantic value.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### eval — def

*Source:* `ResourceModel.lean:158`; public

```lean
def eval [LinearOrder α] (program : Program α β) : β
```

**Natural-language explanation.** Evaluate a free MergeSort program using the ascending linear-order comparison backend.

**Audit focus.** The declaration assumes an ascending linear order on the element type.

### eval_pure — theorem

*Source:* `ResourceModel.lean:161`; public; attributes: `@[simp]`

```lean
@[simp] theorem eval_pure [LinearOrder α] (value : β) :
    eval (pure value : Program α β) = value
```

**Natural-language explanation.** Pure evaluation returns the supplied value.

**Audit focus.** The declaration assumes an ascending linear order on the element type.

### eval_bind — theorem

*Source:* `ResourceModel.lean:164`; public; attributes: `@[simp]`

```lean
@[simp] theorem eval_bind [LinearOrder α] (program : Program α β)
    (next : β → Program α γ) :
    eval (program >>= next) = eval (next (eval program))
```

**Natural-language explanation.** Pure evaluation of a bind equals evaluating its continuation at the first program's evaluated value.

**Audit focus.** The declaration assumes an ascending linear order on the element type.

### eval_map — theorem

*Source:* `ResourceModel.lean:170`; public; attributes: `@[simp]`

```lean
@[simp] theorem eval_map [LinearOrder α] (function : β → γ) (program : Program α β) :
    eval (function <$> program) = function (eval program)
```

**Natural-language explanation.** Pure evaluation commutes with mapping a function over a program.

**Audit focus.** The declaration assumes an ascending linear order on the element type.

### eval_request — theorem

*Source:* `ResourceModel.lean:177`; public; attributes: `@[simp]`

```lean
@[simp] theorem eval_request [LinearOrder α] (operation : Op α) :
    eval (request operation) =
      match operation with
```

**Natural-language explanation.** Pure evaluation answers comparison requests with the linear order and returns unit for base-case, split, and merge requests.

**Audit focus.** The declaration assumes an ascending linear order on the element type.

### operationCharge — def

*Source:* `ResourceModel.lean:192`; public

```lean
def operationCharge (bounds : CostBounds) : Op α → Nat
```

**Natural-language explanation.** Assign the declared upper-bound charge to each operation, scaling split and merge charges by the operation's size.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### interpretWith — def

*Source:* `ResourceModel.lean:198`; public

```lean
def interpretWith (backend : Sorting.ComparisonBackend α) (model : CostModel α)
    (program : Program α β) : TraceM (Event α) (β × PUnit)
```

**Natural-language explanation.** Run a MergeSort program with independently selected comparison semantics and primitive cost measurements, producing an ordered event trace.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### interpret — def

*Source:* `ResourceModel.lean:202`; public

```lean
def interpret [LinearOrder α] (model : CostModel α) (program : Program α β) :
    TraceM (Event α) (β × PUnit)
```

**Natural-language explanation.** Run a MergeSort program with ascending linear-order semantics and the supplied cost model.

**Audit focus.** The declaration assumes an ascending linear order on the element type.

### interpret_pure — theorem

*Source:* `ResourceModel.lean:206`; public; attributes: `@[simp]`

```lean
@[simp] theorem interpret_pure [LinearOrder α] (model : CostModel α) (value : β) :
    interpret model (pure value : Program α β) = pure (value, .unit)
```

**Natural-language explanation.** Interpreting a pure return produces the value, unit state, and no measured event.

**Audit focus.** The declaration assumes an ascending linear order on the element type.

### interpret_bind — theorem

*Source:* `ResourceModel.lean:209`; public

```lean
theorem interpret_bind [LinearOrder α] (model : CostModel α) (program : Program α β)
    (next : β → Program α γ) :
    interpret model (program >>= next) = (do
      let result ← interpret model program
      interpret model (next result.1))
```

**Natural-language explanation.** Interpreting a bind composes the two measured executions, feeding the first semantic result into the continuation.

**Audit focus.** The declaration assumes an ascending linear order on the element type.

### interpretWith_result_eq_evalWith — theorem

*Source:* `ResourceModel.lean:231`; public; attributes: `@[simp]`

```lean
@[simp] theorem interpretWith_result_eq_evalWith (backend : Sorting.ComparisonBackend α)
    (model : CostModel α) (program : Program α β) :
    (interpretWith backend model program).ret.1 = evalWith backend program
```

**Natural-language explanation.** The semantic result of measured interpretation equals pure evaluation under the same comparison backend.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### interpret_result_eq_eval — theorem

*Source:* `ResourceModel.lean:237`; public; attributes: `@[simp]`

```lean
@[simp] theorem interpret_result_eq_eval [LinearOrder α] (model : CostModel α)
    (program : Program α β) :
    (interpret model program).ret.1 = eval program
```

**Natural-language explanation.** Under the linear-order backend, measured interpretation returns the same semantic result as pure evaluation.

**Audit focus.** The declaration assumes an ascending linear order on the element type.

### exactCost — def

*Source:* `ResourceModel.lean:242`; public

```lean
def exactCost (computation : TraceM (Event α) β) : Nat
```

**Natural-language explanation.** Sum all primitive measurements recorded in a completed MergeSort event trace.

**Audit focus.** This concerns the sum of the abstract primitive measurements recorded in the trace.

### exactCost_interpretWith_le_weightedOperationCost — theorem

*Source:* `ResourceModel.lean:245`; public

```lean
theorem exactCost_interpretWith_le_weightedOperationCost
    (backend : Sorting.ComparisonBackend α) (model : CostModel α) (bounds : CostBounds)
    (hbounded : model.IsBoundedBy bounds) (program : Program α β) :
    exactCost (interpretWith backend model program :
      TraceM (Event α) (β × PUnit.{u + 1})) ≤
      ResourceAware.Program.weightedOperationCost (operationCharge bounds)
        (interpretWith backend model program :
          TraceM (Event α) (β × PUnit.{u + 1}))
```

**Natural-language explanation.** If every primitive measurement satisfies the declared bounds, the trace's exact cost is at most its weighted operation cost.

**Audit focus.** This concerns a weighted operation profile, which is not automatically the trace's exact measured cost. The bound is pointwise over primitive operations; inspect the selected constants and size factors.

### weightedOperationCost_interpret_bind — theorem

*Source:* `ResourceModel.lean:263`; public; attributes: `@[simp]`

```lean
@[simp] theorem weightedOperationCost_interpret_bind [LinearOrder α]
    (charge : Op α → Nat) (model : CostModel α) (program : Program α β)
    (next : β → Program α γ) :
    ResourceAware.Program.weightedOperationCost charge
        (interpret model (program >>= next) : TraceM (Event α) (γ × PUnit.{u + 1})) =
      ResourceAware.Program.weightedOperationCost charge
          (interpret model program : TraceM (Event α) (β × PUnit.{u + 1})) +
        ResourceAware.Program.weightedOperationCost charge
          (interpret model (next (eval program)) : TraceM (Event α) (γ × PUnit.{u + 1}))
```

**Natural-language explanation.** Weighted operation cost is additive across interpreted monadic bind.

**Audit focus.** The declaration assumes an ascending linear order on the element type. This concerns a weighted operation profile, which is not automatically the trace's exact measured cost.

### weightedOperationCost_interpret_map — theorem

*Source:* `ResourceModel.lean:274`; public; attributes: `@[simp]`

```lean
@[simp] theorem weightedOperationCost_interpret_map [LinearOrder α]
    (charge : Op α → Nat) (model : CostModel α) (function : β → γ)
    (program : Program α β) :
    ResourceAware.Program.weightedOperationCost charge
        (interpret model (function <$> program) : TraceM (Event α) (γ × PUnit.{u + 1})) =
      ResourceAware.Program.weightedOperationCost charge
        (interpret model program : TraceM (Event α) (β × PUnit.{u + 1}))
```

**Natural-language explanation.** Mapping a pure function over an interpreted program does not change its weighted operation cost.

**Audit focus.** The declaration assumes an ascending linear order on the element type. This concerns a weighted operation profile, which is not automatically the trace's exact measured cost.

### weightedOperationCost_interpret_request — theorem

*Source:* `ResourceModel.lean:287`; public; attributes: `@[simp]`

```lean
@[simp] theorem weightedOperationCost_interpret_request [LinearOrder α]
    (charge : Op α → Nat) (model : CostModel α) (operation : Op α) :
    ResourceAware.Program.weightedOperationCost charge (interpret model (request operation)) =
      charge operation
```

**Natural-language explanation.** The weighted operation cost of one interpreted request is exactly its assigned charge.

**Audit focus.** The declaration assumes an ascending linear order on the element type. This concerns a weighted operation profile, which is not automatically the trace's exact measured cost.


# Correctness and graph-theoretic certificates {#correctness}

[Back to contents](#contents)

**Source file:** `TextbookAlgorithms/KleinbergTardos/Chapter05/MergeSort/Correctness.lean`  
**Declarations in this section:** 5

Semantic correctness of completed runs and the case study's graph-theoretic consequences.

### eval_mergeCore — theorem

*Source:* `Correctness.lean:28`; public; attributes: `@[simp, grind =]`

```lean
@[simp, grind =]
theorem eval_mergeCore (xs ys : List α) :
    eval (mergeCore xs ys) = xs.merge ys
```

**Natural-language explanation.** The abstract comparison-based merge computes mathlib's pure list merge.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### eval_merge — theorem

*Source:* `Correctness.lean:42`; public; attributes: `@[simp]`

```lean
@[simp]
theorem eval_merge (xs ys : List α) :
    eval (merge xs ys) = xs.merge ys
```

**Natural-language explanation.** The outer merge observation does not change the merged result.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### sortBase_correct — theorem

*Source:* `Correctness.lean:47`; public

```lean
theorem sortBase_correct (xs : List α) (hsize : xs.length ≤ 2) :
    Sorting.Correct xs (eval (sortBase xs))
```

**Natural-language explanation.** Sorting a size-at-most-two base case produces a sorted permutation.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### mergeSort_correct — theorem

*Source:* `Correctness.lean:65`; public

```lean
theorem mergeSort_correct (xs : List α) :
    Sorting.Correct xs (eval (mergeSort xs))
```

**Natural-language explanation.** Kleinberg merge sort returns a sorted permutation of its input.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### interpret_mergeSort_correct — theorem

*Source:* `Correctness.lean:87`; public

```lean
theorem interpret_mergeSort_correct (model : CostModel α) (xs : List α) :
    Sorting.Correct xs ((interpret model (mergeSort xs)).ret.1)
```

**Natural-language explanation.** Every selected cost model preserves the functionally correct MergeSort result.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.


# Complexity and resource bounds {#complexity}

[Back to contents](#contents)

**Source file:** `TextbookAlgorithms/KleinbergTardos/Chapter05/MergeSort/Complexity.lean`  
**Declarations in this section:** 18

Cost-independent operation profiles, exact-cost transfers, closed bounds, and asymptotic endpoints.

### mergeCore_weightedOperationCost_le — theorem

*Source:* `Complexity.lean:35`; public

```lean
theorem mergeCore_weightedOperationCost_le {α : Type u} [LinearOrder α]
    (model : CostModel α) (bounds : CostBounds) (xs ys : List α) :
    ResourceAware.Program.weightedOperationCost (operationCharge bounds)
      (interpret model (mergeCore xs ys)) ≤
        bounds.comparison * (xs.length + ys.length)
```

**Natural-language explanation.** One merge performs at most one weighted comparison per input element.

**Audit focus.** The declaration assumes an ascending linear order on the element type. This concerns a weighted operation profile, which is not automatically the trace's exact measured cost.

### merge_weightedOperationCost_le — theorem

*Source:* `Complexity.lean:50`; public

```lean
theorem merge_weightedOperationCost_le {α : Type u} [LinearOrder α]
    (model : CostModel α) (bounds : CostBounds) (xs ys : List α) :
    ResourceAware.Program.weightedOperationCost (operationCharge bounds)
      (interpret model (merge xs ys)) ≤
        bounds.mergeUnit * (xs.length + ys.length) +
          bounds.comparison * (xs.length + ys.length)
```

**Natural-language explanation.** A merge profile contains one structural merge and its actual comparisons.

**Audit focus.** The declaration assumes an ascending linear order on the element type. This concerns a weighted operation profile, which is not automatically the trace's exact measured cost.

### sortBase_weightedOperationCost_le — theorem

*Source:* `Complexity.lean:63`; public

```lean
theorem sortBase_weightedOperationCost_le {α : Type u} [LinearOrder α]
    (model : CostModel α) (bounds : CostBounds) (xs : List α) (hsize : xs.length ≤ 2) :
    ResourceAware.Program.weightedOperationCost (operationCharge bounds)
      (interpret model (sortBase xs)) ≤ bounds.recurrenceCoefficient
```

**Natural-language explanation.** Every executable base-case profile is bounded by the recurrence coefficient.

**Audit focus.** The declaration assumes an ascending linear order on the element type. This concerns a weighted operation profile, which is not automatically the trace's exact measured cost.

### eval_mergeSort_length — theorem

*Source:* `Complexity.lean:85`; public; attributes: `@[simp]`

```lean
@[simp] theorem eval_mergeSort_length {α : Type u} [LinearOrder α] (xs : List α) :
    (eval (mergeSort xs)).length = xs.length
```

**Natural-language explanation.** Pure MergeSort evaluation preserves the input list's length.

**Audit focus.** The declaration assumes an ascending linear order on the element type.

### mergeSort_weightedOperationCost_step — theorem

*Source:* `Complexity.lean:90`; public

```lean
theorem mergeSort_weightedOperationCost_step {α : Type u} [LinearOrder α]
    (model : CostModel α) (bounds : CostBounds) (xs : List α) (hsize : 2 < xs.length) :
    ResourceAware.Program.weightedOperationCost (operationCharge bounds)
        (interpret model (mergeSort xs) : TraceM (Event α) (List α × PUnit.{u + 1})) ≤
      ResourceAware.Program.weightedOperationCost (operationCharge bounds)
          (interpret model (mergeSort (xs.take (xs.length / 2))) :
            TraceM (Event α) (List α × PUnit.{u + 1})) +
        ResourceAware.Program.weightedOperationCost (operationCharge bounds)
          (interpret model (mergeSort (xs.drop (xs.length / 2))) :
            TraceM (Event α) (List α × PUnit.{u + 1})) +
        bounds.recurrenceCoefficient * xs.length
```

**Natural-language explanation.** One recursive MergeSort operation profile obeys the textbook cost decomposition.

**Audit focus.** The declaration assumes an ascending linear order on the element type. This concerns a weighted operation profile, which is not automatically the trace's exact measured cost.

### traceWorstCase — def

*Source:* `Complexity.lean:130`; public

```lean
def traceWorstCase (c : Nat) : Nat → Nat
```

**Natural-language explanation.** A recurrence upper bound whose non-base branch is exactly Kleinberg Theorem 5.1.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### traceWorstCase_eq — theorem

*Source:* `Complexity.lean:138`; public

```lean
theorem traceWorstCase_eq (c n : Nat) (h : 2 < n) :
    traceWorstCase c n = 2 * traceWorstCase c (n / 2) + c * n
```

**Natural-language explanation.** Above the base threshold, the explicit worst-case envelope unfolds to two half-size recursive terms plus linear work.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### traceWorstCase_satisfies — theorem

*Source:* `Complexity.lean:142`; public

```lean
theorem traceWorstCase_satisfies (c : Nat) : SatisfiesRecurrence (traceWorstCase c) c
```

**Natural-language explanation.** The explicit `traceWorstCase` function satisfies the packaged textbook recurrence.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### even_two_pow_succ — theorem

*Source:* `Complexity.lean:151`; private

```lean
private theorem even_two_pow_succ (k : Nat) : Even (2 ^ (k + 1))
```

**Natural-language explanation.** A positive power of two is even.

**Audit focus.** This is an internal proof helper, included because the dossier covers private declarations.

### two_pow_succ_div_two — theorem

*Source:* `Complexity.lean:157`; private

```lean
private theorem two_pow_succ_div_two (k : Nat) : 2 ^ (k + 1) / 2 = 2 ^ k
```

**Natural-language explanation.** Halving `2^(k+1)` gives `2^k` exactly.

**Audit focus.** This is an internal proof helper, included because the dossier covers private declarations.

### two_lt_two_pow_succ — theorem

*Source:* `Complexity.lean:162`; private

```lean
private theorem two_lt_two_pow_succ {k : Nat} (hk : 1 ≤ k) : 2 < 2 ^ (k + 1)
```

**Natural-language explanation.** For `k ≥ 1`, the next power of two is strictly larger than the base-case size.

**Audit focus.** This is an internal proof helper, included because the dossier covers private declarations.

### theorem_5_2_substitution — theorem

*Source:* `Complexity.lean:175`; public

```lean
theorem theorem_5_2_substitution {T : Nat → Nat} {c : Nat}
    (hrec : SatisfiesRecurrence T c) :
    ∀ k, 1 ≤ k → T (2 ^ k) ≤ c * (2 ^ k) * k
```

**Natural-language explanation.** Kleinberg Theorem 5.2, proved by substitution. For an input size `n = 2^k`, `k` is `log₂ n`; hence this explicit inequality is the textbook `T(n) = O(n log n)` bound.  The induction step literally substitutes the hypothesis for `T(n / 2)` into Theorem 5.1 and simplifies `log₂(n / 2) = log₂ n - 1` through the exponent `k`.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### theorem_5_2_isBigO — theorem

*Source:* `Complexity.lean:208`; public

```lean
theorem theorem_5_2_isBigO {T : Nat → Nat} {c : Nat}
    (hrec : SatisfiesRecurrence T c) :
    (fun k : Nat ↦ (T (2 ^ k) : Real)) =O[atTop]
      fun k ↦ ((2 ^ k : Nat) : Real) * k
```

**Natural-language explanation.** Kleinberg Theorem 5.2 as a Mathlib `IsBigO` statement along power-of-two input sizes. The index `k` represents inputs of size `n = 2^k`, so the comparison function `2^k * k` is exactly `n log₂ n`.

**Audit focus.** This is an asymptotic upper bound, so multiplicative constants and a finite prefix are hidden.

### mergeSort_weightedOperationCost_le_traceWorstCase — theorem

*Source:* `Complexity.lean:225`; public

```lean
theorem mergeSort_weightedOperationCost_le_traceWorstCase {α : Type u} [LinearOrder α]
    (model : CostModel α) (bounds : CostBounds) :
    ∀ k, 1 ≤ k → ∀ xs : List α, xs.length = 2 ^ k →
      ResourceAware.Program.weightedOperationCost (operationCharge bounds)
          (interpret model (mergeSort xs) : TraceM (Event α) (List α × PUnit.{u + 1})) ≤
        traceWorstCase bounds.recurrenceCoefficient (2 ^ k)
```

**Natural-language explanation.** On power-of-two inputs, the cost-independent operation profile obeys the recurrence.

**Audit focus.** The declaration assumes an ascending linear order on the element type. This concerns a weighted operation profile, which is not automatically the trace's exact measured cost.

### mergeSort_exactCost_le_traceWorstCase — theorem

*Source:* `Complexity.lean:270`; public

```lean
theorem mergeSort_exactCost_le_traceWorstCase {α : Type u} [LinearOrder α]
    (model : CostModel α) (bounds : CostBounds) (hbounded : model.IsBoundedBy bounds) :
    ∀ k, 1 ≤ k → ∀ xs : List α, xs.length = 2 ^ k →
      exactCost (interpret model (mergeSort xs) :
        TraceM (Event α) (List α × PUnit.{u + 1})) ≤
      traceWorstCase bounds.recurrenceCoefficient (2 ^ k)
```

**Natural-language explanation.** Any bounded MergeSort cost model is controlled by the same operation-profile recurrence.

**Audit focus.** The declaration assumes an ascending linear order on the element type. This concerns the sum of the abstract primitive measurements recorded in the trace. The bound is pointwise over primitive operations; inspect the selected constants and size factors.

### mergeSort_exactCost_le_bounded — theorem

*Source:* `Complexity.lean:290`; public

```lean
theorem mergeSort_exactCost_le_bounded {α : Type u} [LinearOrder α]
    (model : CostModel α) (bounds : CostBounds) (hbounded : model.IsBoundedBy bounds)
    (k : Nat) (hk : 1 ≤ k) (xs : List α) (hlength : xs.length = 2 ^ k) :
    exactCost (interpret model (mergeSort xs) :
      TraceM (Event α) (List α × PUnit.{u + 1})) ≤
      bounds.recurrenceCoefficient * xs.length * k
```

**Natural-language explanation.** Every bounded MergeSort model satisfies the explicit `c n log₂ n` bound.

**Audit focus.** The declaration assumes an ascending linear order on the element type. This concerns the sum of the abstract primitive measurements recorded in the trace. The bound is pointwise over primitive operations; inspect the selected constants and size factors.

### mergeSort_exactCost_isBigO_on_powersOfTwo — theorem

*Source:* `Complexity.lean:307`; public

```lean
theorem mergeSort_exactCost_isBigO_on_powersOfTwo {α : Type u} [LinearOrder α]
    (model : CostModel α) (bounds : CostBounds) (hbounded : model.IsBoundedBy bounds)
    (inputs : Nat → List α) (hlength : ∀ k, (inputs k).length = 2 ^ k) :
    (fun k : Nat ↦
      (exactCost (interpret model (mergeSort (inputs k)) :
        TraceM (Event α) (List α × PUnit.{u + 1})) : Real)) =O[atTop]
      fun k ↦ ((2 ^ k : Nat) : Real) * k
```

**Natural-language explanation.** The exact measured cost of bounded-model MergeSort is `O(n log₂ n)` along any family of power-of-two-sized inputs. The function is indexed by `k`, with `(inputs k).length = 2^k`; hence the comparison function `2^k * k` is `n log₂ n`.

**Audit focus.** The declaration assumes an ascending linear order on the element type. This concerns the sum of the abstract primitive measurements recorded in the trace. The bound is pointwise over primitive operations; inspect the selected constants and size factors. This is an asymptotic upper bound, so multiplicative constants and a finite prefix are hidden.

### mergeSort_exactCost_le — theorem

*Source:* `Complexity.lean:331`; public

```lean
theorem mergeSort_exactCost_le {α : Type u} [LinearOrder α]
    (comparisonUnit splitUnit mergeUnit k : Nat) (hk : 1 ≤ k)
    (xs : List α) (hlength : xs.length = 2 ^ k) :
    exactCost (interpret (CostModel.linearKleinberg comparisonUnit splitUnit mergeUnit)
      (mergeSort xs) : TraceM (Event α) (List α × PUnit.{u + 1})) ≤
      CostModel.kleinbergCoefficient comparisonUnit splitUnit mergeUnit * xs.length * k
```

**Natural-language explanation.** The linear Kleinberg model is one specialization of the general bounded-cost theorem.

**Audit focus.** The declaration assumes an ascending linear order on the element type. This concerns the sum of the abstract primitive measurements recorded in the trace.

# Audit completion checklist {#audit-completion-checklist}

[Back to contents](#contents)

- Confirm the base-case threshold and split convention match the intended textbook presentation.
- Check whether each statement concerns pure evaluation, an exact measured trace, or a weighted upper profile.
- Confirm comparison and structural merge work are not double-counted in the selected model.
- Retain the bounded-model hypothesis when transferring weighted profile bounds to exact cost.
- Check all evenness and power-of-two restrictions in recurrence and asymptotic claims.
- Do not generalize the power-of-two `O(n log n)` endpoint to arbitrary input sizes without an additional theorem.
- Record any mismatch as one of: missing hypothesis, stronger or weaker conclusion, wrong semantic interpretation, wrong cost interpretation, wrong quantification domain, or unsupported textbook attribution.

# Source inventory {#source-inventory}

- `Algorithm.lean`: The free program and its algorithm-specific recursive helpers.
- `ResourceModel.lean`: The selected semantic backends, cost interpretation, runner, and space model.
- `Correctness.lean`: Semantic correctness of completed runs and the case study's graph-theoretic consequences.
- `Complexity.lean`: Cost-independent operation profiles, exact-cost transfers, closed bounds, and asymptotic endpoints.
