---
title: "Randomized Quicksort Formalization"
subtitle: "Declaration Headers and Natural-Language Faithfulness Audit"
author: "Generated from Resource-Aware-CSLib source"
date: "12 August 2026"
---

**Audit purpose.** This dossier places every `def` and `theorem` header from the modular randomized Quicksort formalization next to a statement-level natural-language reading. It is designed for a manual check of whether the Lean claim matches the intended textbook claim.

**Snapshot.** Commit `6194a4137cb8d4f2c2b57ca939e607161a541784`; formalization sources inspected on 12 August 2026. Source locations are line-based and may drift after edits.

**Coverage.** 237 declarations (234 public, 3 private). Declarations written with `abbrev`, `structure`, or `inductive`, along with proof bodies, namespace commands, imports, and executable examples, are intentionally excluded.

**How to audit an entry.** Check (1) the quantified inputs and type-class assumptions, (2) hypotheses such as `Nodup`, support membership, or size thresholds, (3) the exact conclusion, and (4) whether the cost model measures comparisons, abstract textbook work, or something else. The prose explains the statement; it does not claim more than the displayed header.

# Contents {#contents}

- [High-level faithfulness guide](#high-level-faithfulness-guide)
  - [Important scope boundaries](#important-scope-boundaries)
  - [Notation used in the headers](#notation-used-in-the-headers)
- [Algorithm: abstract program and recursion](#algorithm)
  - [Foundations](#algorithm-foundations)
  - [Syntactic pivot freedom](#algorithm-syntactic-pivot-freedom)
  - [Certified partitioning](#algorithm-certified-partitioning)
  - [Constant-size sorting network](#algorithm-constant-size-sorting-network)
  - [Randomized Quicksort](#algorithm-randomized-quicksort)
- [Resource models: what is charged](#resource-model)
  - [Foundations](#resource-model-foundations)
- [Interpreters: probability, cost, determinism, and traces](#interpreters)
  - [Semantic backends](#interpreters-semantic-backends)
  - [Operation handlers](#interpreters-operation-handlers)
  - [PMF and RandCostM runners](#interpreters-pmf-and-randcostm-runners)
  - [Ordered observations](#interpreters-ordered-observations)
- [Correctness: sorted permutations of the input](#correctness)
  - [Foundations](#correctness-foundations)
  - [Correctness of the constant-size sorting network](#correctness-small-network)
  - [Recursive Quicksort correctness](#correctness-recursive-quicksort)
- [Complexity: expected and worst supported costs](#complexity)
  - [Joint-support decomposition](#complexity-joint-support)
  - [Exact comparison cost of partitioning](#complexity-partition-cost)
  - [A run-derived uniform-pivot recurrence](#complexity-recurrence)
  - [A harmonic comparison envelope](#complexity-harmonic-envelope)
  - [Solving the uniform-pivot recurrence](#complexity-solving-recurrence)
  - [Worst-case comparison branches](#complexity-worst-comparisons)
  - [Textbook running-time model](#complexity-textbook-model)
  - [Worst-case textbook running time](#complexity-worst-textbook)
- [Audit completion checklist](#audit-completion-checklist)
- [Source inventory](#source-inventory)

# High-level faithfulness guide {#high-level-faithfulness-guide}

The formalization uses one recursive free program, `quicksortProgram`. Uniform randomness, deterministic test pivots, comparison counting, the abstract textbook cost model, and ordered traces are separate interpreters of that program. Functional correctness is proved for supported outputs of the actual interpreter. Expected-cost theorems require duplicate-free inputs; the comparison endpoint is an upper envelope rather than an exact closed form. The worst comparison result is an attained supported-branch maximum. The textbook runtime results concern an explicit abstract cost model, not machine time, allocation, or peak live space.

## Important scope boundaries {#important-scope-boundaries}

- The algorithm chooses a uniformly random list position at each non-base call, removes that pivot, compares every remaining element with it, recursively sorts both partitions, and joins the results.
- Lists of length zero through three use a fixed network with 0, 0, 1, and 3 comparisons respectively.
- Expected and advertised textbook-facing complexity results assume `Nodup`; duplicate-key handling is not the advertised interface.
- The comparison-only model charges exactly one per key comparison and zero for sampling, indexing/removal, allocation, recursion bookkeeping, and list construction.
- The textbook model adds one base-case unit and a size-linear splitter-frame charge, still as an abstraction rather than concrete evaluator time.
- The formalization does not cover the modified central-splitter rejection loop, Select, an in-place array implementation, allocation/space bounds, or an exact closed-form expectation.

## Notation used in the headers {#notation-used-in-the-headers}

- `PMF α`: a probability mass function over values of type `α`.
- `RandCostM Nat α`: a probabilistic computation returning an `α` and accumulating a natural-number cost.
- `.ret`: the result marginal after costs are erased; `.joint`: the joint result/cost distribution.
- `.support`: outcomes with nonzero probability / possible supported branches.
- `Nodup`: the list contains no duplicate values.
- `ENNReal`: extended nonnegative real numbers, used for expectations.
- `=O[atTop]` and `=Θ[atTop]`: asymptotic big-O and theta as the natural size tends to infinity.
- `n.choose 2`: the number of unordered pairs among `n` elements.

# Algorithm: abstract program and recursion {#algorithm}

[Back to contents](#contents)

**Source file:** `TextbookAlgorithms/KleinbergTardos/Chapter13/RandomizedQuicksort/Algorithm.lean`  
**Declarations in this section:** 18

## Foundations {#algorithm-foundations}

### Signature — def

*Source:* `Algorithm.lean:47`; public

```lean
def Signature (α : Type u) : ResourceAware.Program.Signature.{u, u}
```

**Natural-language explanation.** Polynomial signature for randomized Quicksort.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### request — def

*Source:* `Algorithm.lean:58`; public

```lean
def request (operation : Op α) : Program α (Response operation)
```

**Natural-language explanation.** Lift one Quicksort operation into the free monad.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### markBaseCase — def

*Source:* `Algorithm.lean:62`; public

```lean
def markBaseCase (size : Nat) : Program α PUnit
```

**Natural-language explanation.** Mark a textbook constant-size base case without assigning it a resource charge.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### choosePivotIndex — def

*Source:* `Algorithm.lean:66`; public

```lean
def choosePivotIndex (tailLength : Nat) : Program α (ULift (Fin (tailLength + 1)))
```

**Natural-language explanation.** Request a pivot index for a list whose length is `tailLength + 1`.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### compareLE — def

*Source:* `Algorithm.lean:70`; public

```lean
def compareLE (left right : α) : Program α (ULift Bool)
```

**Natural-language explanation.** Request one `left ≤ right` comparison.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

## Syntactic pivot freedom {#algorithm-syntactic-pivot-freedom}

### PivotFree — def

*Source:* `Algorithm.lean:76`; public

```lean
def PivotFree : Program α β -> Prop
```

**Natural-language explanation.** A free program is pivot-free when none of its possible continuations requests a pivot.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### pure — theorem

*Source:* `Algorithm.lean:86`; public; attributes: simp

```lean
@[simp] theorem pure (value : β) :
    PivotFree (pure value : Program α β)
```

**Natural-language explanation.** A pure return contains no pivot-selection request, so it is pivot-free.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### bind — theorem

*Source:* `Algorithm.lean:90`; public

```lean
theorem bind (program : Program α β) (next : β -> Program α γ)
    (hProgram : PivotFree program) (hNext : forall value, PivotFree (next value)) :
    PivotFree (program >>= next)
```

**Natural-language explanation.** A monadic bind is pivot-free when the first program is pivot-free and every continuation selected from it is also pivot-free.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### markBaseCase — theorem

*Source:* `Algorithm.lean:110`; public; attributes: simp

```lean
@[simp] theorem markBaseCase (size : Nat) :
    PivotFree (RandomizedQuicksort.markBaseCase (α := α) size)
```

**Natural-language explanation.** Emitting the base-case marker never requests a pivot.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### compareLE — theorem

*Source:* `Algorithm.lean:116`; public; attributes: simp

```lean
@[simp] theorem compareLE (left right : α) :
    PivotFree (RandomizedQuicksort.compareLE left right)
```

**Natural-language explanation.** Requesting one less-than-or-equal key comparison never requests a pivot.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

## Certified partitioning {#algorithm-certified-partitioning}

### partitionProgram — def

*Source:* `Algorithm.lean:142`; public

```lean
def partitionProgram (pivot : α) : (input : List α) → Program α (PartitionResult input)
```

**Natural-language explanation.** Partition a pivot-free list around `pivot`. Exactly one abstract comparison is requested for every input element. With the ascending linear-order interpreter and a duplicate-free input, `left ≤ pivot` is equivalent to the textbook's strict lower-side test because the selected pivot has already been removed.

**Audit focus.** The upper branch uses the negation of `value <= pivot`; under a linear order this becomes `pivot < value`. Duplicate-free inputs make this match the textbook's strict split after pivot removal.

### PivotFree.partitionProgram — theorem

*Source:* `Algorithm.lean:161`; public

```lean
theorem PivotFree.partitionProgram (pivot : α) (input : List α) :
    PivotFree (partitionProgram pivot input)
```

**Natural-language explanation.** Partitioning is pivot-free: it may compare elements, but it does not sample another pivot.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

## Constant-size sorting network {#algorithm-constant-size-sorting-network}

### compareSwap — def

*Source:* `Algorithm.lean:176`; public

```lean
def compareSwap (left right : α) : Program α (α × α)
```

**Natural-language explanation.** Sort two values using exactly one abstract comparison.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### PivotFree.compareSwap — theorem

*Source:* `Algorithm.lean:180`; public

```lean
theorem PivotFree.compareSwap (left right : α) :
    PivotFree (compareSwap left right)
```

**Natural-language explanation.** The compare-and-swap helper is pivot-free because it performs only one comparison and then returns.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### sortSmallProgram — def

*Source:* `Algorithm.lean:193`; public

```lean
def sortSmallProgram : List α → Program α (List α)
```

**Natural-language explanation.** Implement the textbook's unspecified `Sort S` base case by a fixed sorting network. Lists of length zero or one use no comparisons, length two uses one, and length three uses three. The final fallback makes the helper total but is unreachable from `quicksortProgram`.

**Audit focus.** The final fallback returns inputs longer than three unchanged; the formalized Quicksort never reaches that fallback.

### PivotFree.sortSmallProgram — theorem

*Source:* `Algorithm.lean:212`; public

```lean
theorem PivotFree.sortSmallProgram (input : List α) :
    PivotFree (sortSmallProgram input)
```

**Natural-language explanation.** The fixed sorting network for a small list is pivot-free.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

## Randomized Quicksort {#algorithm-randomized-quicksort}

### quicksortProgram — def

*Source:* `Algorithm.lean:266`; public

```lean
def quicksortProgram : (input : List α) → Program α (List α)
```

**Natural-language explanation.** Kleinberg--Tardos randomized Quicksort. The pivot request supplies an index into the current list. The pivot is removed before partitioning, both certified partitions are recursively sorted, and the results are glued around the pivot. Termination is by list length and holds for every response an interpreter can provide.

**Audit focus.** This is the only recursive Quicksort definition. Randomness and cost are still abstract here. The base case is `length <= 3`, and the pivot is removed before partitioning.

### PivotFree.quicksortProgram_of_length_le_three — theorem

*Source:* `Algorithm.lean:292`; public

```lean
theorem PivotFree.quicksortProgram_of_length_le_three (input : List α)
    (hLength : input.length <= 3) :
    PivotFree (quicksortProgram input)
```

**Natural-language explanation.** On inputs of length at most three, Quicksort takes the base-case path and therefore issues no pivot request.

**Audit focus.** Restricted to the base-case sizes, at most three.

# Resource models: what is charged {#resource-model}

[Back to contents](#contents)

**Source file:** `TextbookAlgorithms/KleinbergTardos/Chapter13/RandomizedQuicksort/ResourceModel.lean`  
**Declarations in this section:** 25

## Foundations {#resource-model-foundations}

### recurrenceCoefficient — def

*Source:* `ResourceModel.lean:50`; public

```lean
def recurrenceCoefficient (bounds : CostBounds) : Nat
```

**Natural-language explanation.** A convenient coefficient collecting all nonrecursive costs of one recurrence frame.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### comparisonOnly — def

*Source:* `ResourceModel.lean:65`; public

```lean
def comparisonOnly : CostModel alpha
```

**Natural-language explanation.** Count every element comparison once and make all non-comparison work free.

**Audit focus.** Uses the model that charges comparisons and makes structural work free.

### scaledComparisons — def

*Source:* `ResourceModel.lean:71`; public

```lean
def scaledComparisons (comparisonUnit : Nat) : CostModel alpha
```

**Natural-language explanation.** Count each comparison at rate `comparisonUnit`, leaving structural work free.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### linearTextbook — def

*Source:* `ResourceModel.lean:82`; public

```lean
def linearTextbook (baseUnit frameUnit comparisonUnit : Nat) : CostModel alpha
```

**Natural-language explanation.** The textbook running-time family. A base case costs `baseUnit`; a size-`n` splitter frame costs `frameUnit * n`; and every comparison costs `comparisonUnit`. The frame component excludes the comparisons.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### textbookModel — def

*Source:* `ResourceModel.lean:88`; public

```lean
def textbookModel : CostModel alpha
```

**Natural-language explanation.** Unit-cost specialization used for the textbook running-time claims.

**Audit focus.** Uses the abstract unit textbook cost model, not wall-clock time.

### linearTextbookBounds — def

*Source:* `ResourceModel.lean:92`; public

```lean
def linearTextbookBounds (baseUnit frameUnit comparisonUnit : Nat) : CostBounds
```

**Natural-language explanation.** Bounds exactly realized by `linearTextbook`.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### linearTextbook_isBoundedBy — theorem

*Source:* `ResourceModel.lean:98`; public

```lean
theorem linearTextbook_isBoundedBy (baseUnit frameUnit comparisonUnit : Nat) :
    (linearTextbook (alpha := alpha) baseUnit frameUnit comparisonUnit).IsBoundedBy
      (linearTextbookBounds baseUnit frameUnit comparisonUnit)
```

**Natural-language explanation.** The approved linear textbook model satisfies its declared primitive bounds.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### comparisonOnlyBounds — def

*Source:* `ResourceModel.lean:105`; public

```lean
def comparisonOnlyBounds : CostBounds
```

**Natural-language explanation.** Primitive bounds for the comparison-only model.

**Audit focus.** Uses the model that charges comparisons and makes structural work free.

### comparisonOnly_isBoundedBy — theorem

*Source:* `ResourceModel.lean:111`; public

```lean
theorem comparisonOnly_isBoundedBy :
    (comparisonOnly (alpha := alpha)).IsBoundedBy comparisonOnlyBounds
```

**Natural-language explanation.** The comparison-only model satisfies its exact primitive bounds.

**Audit focus.** Uses the model that charges comparisons and makes structural work free.

### operationCost — def

*Source:* `ResourceModel.lean:117`; public

```lean
def operationCost (model : CostModel alpha) : Op alpha -> Nat
```

**Natural-language explanation.** Read the cost assigned to one complete Quicksort operation.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### operationCost_comparison — theorem

*Source:* `ResourceModel.lean:122`; public; attributes: simp

```lean
@[simp] theorem operationCost_comparison (model : CostModel alpha) (left right : alpha) :
    model.operationCost (.comparison (.le left right)) = model.comparison.cost left right
```

**Natural-language explanation.** The cost of a comparison operation is exactly the comparison charge supplied by the selected cost model.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### operationCost_baseCase — theorem

*Source:* `ResourceModel.lean:126`; public; attributes: simp

```lean
@[simp] theorem operationCost_baseCase (model : CostModel alpha) (size : Nat) :
    model.operationCost (.baseCase size) = model.baseCaseCost size
```

**Natural-language explanation.** The cost of a base-case operation is exactly the model's base-case charge at that size.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### operationCost_choosePivotIndex — theorem

*Source:* `ResourceModel.lean:130`; public; attributes: simp

```lean
@[simp] theorem operationCost_choosePivotIndex (model : CostModel alpha) (tailLength : Nat) :
    model.operationCost (.choosePivotIndex tailLength) =
      model.splitterFrameCost (tailLength + 1)
```

**Natural-language explanation.** Choosing a pivot for a list of length `tailLength + 1` is charged by the model's splitter-frame cost at that full size.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### comparisonOnly_comparison — theorem

*Source:* `ResourceModel.lean:135`; public; attributes: simp

```lean
@[simp] theorem comparisonOnly_comparison (left right : alpha) :
    (comparisonOnly (alpha := alpha)).comparison.cost left right = 1
```

**Natural-language explanation.** In the comparison-only model, every key comparison costs exactly one unit.

**Audit focus.** Uses the model that charges comparisons and makes structural work free.

### comparisonOnly_baseCase — theorem

*Source:* `ResourceModel.lean:139`; public; attributes: simp

```lean
@[simp] theorem comparisonOnly_baseCase (size : Nat) :
    (comparisonOnly (alpha := alpha)).baseCaseCost size = 0
```

**Natural-language explanation.** In the comparison-only model, every base-case marker costs zero.

**Audit focus.** Uses the model that charges comparisons and makes structural work free.

### comparisonOnly_splitterFrame — theorem

*Source:* `ResourceModel.lean:143`; public; attributes: simp

```lean
@[simp] theorem comparisonOnly_splitterFrame (size : Nat) :
    (comparisonOnly (alpha := alpha)).splitterFrameCost size = 0
```

**Natural-language explanation.** In the comparison-only model, splitter-frame work costs zero at every size.

**Audit focus.** Uses the model that charges comparisons and makes structural work free.

### scaledComparisons_comparison — theorem

*Source:* `ResourceModel.lean:147`; public; attributes: simp

```lean
@[simp] theorem scaledComparisons_comparison (comparisonUnit : Nat) (left right : alpha) :
    (scaledComparisons (alpha := alpha) comparisonUnit).comparison.cost left right =
      comparisonUnit
```

**Natural-language explanation.** In the scaled-comparison model, each comparison costs exactly `comparisonUnit`.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### scaledComparisons_baseCase — theorem

*Source:* `ResourceModel.lean:152`; public; attributes: simp

```lean
@[simp] theorem scaledComparisons_baseCase (comparisonUnit size : Nat) :
    (scaledComparisons (alpha := alpha) comparisonUnit).baseCaseCost size = 0
```

**Natural-language explanation.** In the scaled-comparison model, base-case work is free.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### scaledComparisons_splitterFrame — theorem

*Source:* `ResourceModel.lean:156`; public; attributes: simp

```lean
@[simp] theorem scaledComparisons_splitterFrame (comparisonUnit size : Nat) :
    (scaledComparisons (alpha := alpha) comparisonUnit).splitterFrameCost size = 0
```

**Natural-language explanation.** In the scaled-comparison model, splitter-frame work is free.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### linearTextbook_comparison — theorem

*Source:* `ResourceModel.lean:160`; public; attributes: simp

```lean
@[simp] theorem linearTextbook_comparison (baseUnit frameUnit comparisonUnit : Nat)
    (left right : alpha) :
    (linearTextbook (alpha := alpha) baseUnit frameUnit comparisonUnit).comparison.cost
      left right = comparisonUnit
```

**Natural-language explanation.** In the linear textbook model, each comparison costs `comparisonUnit`.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### linearTextbook_baseCase — theorem

*Source:* `ResourceModel.lean:166`; public; attributes: simp

```lean
@[simp] theorem linearTextbook_baseCase (baseUnit frameUnit comparisonUnit size : Nat) :
    (linearTextbook (alpha := alpha) baseUnit frameUnit comparisonUnit).baseCaseCost size =
      baseUnit
```

**Natural-language explanation.** In the linear textbook model, a base case costs the constant `baseUnit`, regardless of its small size.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### linearTextbook_splitterFrame — theorem

*Source:* `ResourceModel.lean:171`; public; attributes: simp

```lean
@[simp] theorem linearTextbook_splitterFrame
    (baseUnit frameUnit comparisonUnit size : Nat) :
    (linearTextbook (alpha := alpha) baseUnit frameUnit comparisonUnit).splitterFrameCost size =
      frameUnit * size
```

**Natural-language explanation.** In the linear textbook model, a size-`n` splitter frame costs `frameUnit * n`.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### textbookModel_comparison — theorem

*Source:* `ResourceModel.lean:177`; public; attributes: simp

```lean
@[simp] theorem textbookModel_comparison (left right : alpha) :
    (textbookModel (alpha := alpha)).comparison.cost left right = 1
```

**Natural-language explanation.** The unit textbook model charges one unit per comparison.

**Audit focus.** Uses the abstract unit textbook cost model, not wall-clock time.

### textbookModel_baseCase — theorem

*Source:* `ResourceModel.lean:181`; public; attributes: simp

```lean
@[simp] theorem textbookModel_baseCase (size : Nat) :
    (textbookModel (alpha := alpha)).baseCaseCost size = 1
```

**Natural-language explanation.** The unit textbook model charges one unit per base-case marker.

**Audit focus.** Uses the abstract unit textbook cost model, not wall-clock time.

### textbookModel_splitterFrame — theorem

*Source:* `ResourceModel.lean:185`; public; attributes: simp

```lean
@[simp] theorem textbookModel_splitterFrame (size : Nat) :
    (textbookModel (alpha := alpha)).splitterFrameCost size = size
```

**Natural-language explanation.** The unit textbook model charges exactly the current input size for a splitter frame.

**Audit focus.** Uses the abstract unit textbook cost model, not wall-clock time.

# Interpreters: probability, cost, determinism, and traces {#interpreters}

[Back to contents](#contents)

**Source file:** `TextbookAlgorithms/KleinbergTardos/Chapter13/RandomizedQuicksort/Interpreters.lean`  
**Declarations in this section:** 67

## Semantic backends {#interpreters-semantic-backends}

### uniform — def

*Source:* `Interpreters.lean:44`; public

```lean
def uniform : PivotBackend
```

**Natural-language explanation.** Uniformly choose one of the `tailLength + 1` valid list positions.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### first — def

*Source:* `Interpreters.lean:48`; public

```lean
def first : PivotBackend
```

**Natural-language explanation.** Always choose index zero. This deterministic backend exposes a worst-case test branch.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### last — def

*Source:* `Interpreters.lean:53`; public

```lean
def last : PivotBackend
```

**Natural-language explanation.** Always choose the last valid index.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### first_choose — theorem

*Source:* `Interpreters.lean:56`; public; attributes: simp

```lean
@[simp] theorem first_choose (tailLength : Nat) :
    first.choose tailLength =
      PMF.pure (ULift.up ⟨0, Nat.zero_lt_succ tailLength⟩)
```

**Natural-language explanation.** The deterministic first-pivot backend always returns index zero.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### last_choose — theorem

*Source:* `Interpreters.lean:61`; public; attributes: simp

```lean
@[simp] theorem last_choose (tailLength : Nat) :
    last.choose tailLength = PMF.pure (ULift.up (Fin.last tailLength))
```

**Natural-language explanation.** The deterministic last-pivot backend always returns the last valid index.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### uniformLinearOrder — def

*Source:* `Interpreters.lean:75`; public

```lean
def uniformLinearOrder [LinearOrder alpha] : SemanticBackend alpha
```

**Natural-language explanation.** The source semantics: uniform pivots and the ascending order on keys.

**Audit focus.** Assumes a linear order on keys.

### firstLinearOrder — def

*Source:* `Interpreters.lean:80`; public

```lean
def firstLinearOrder [LinearOrder alpha] : SemanticBackend alpha
```

**Natural-language explanation.** Ascending comparisons with a deterministic first-position pivot.

**Audit focus.** Assumes a linear order on keys.

### lastLinearOrder — def

*Source:* `Interpreters.lean:85`; public

```lean
def lastLinearOrder [LinearOrder alpha] : SemanticBackend alpha
```

**Natural-language explanation.** Ascending comparisons with a deterministic last-position pivot.

**Audit focus.** Assumes a linear order on keys.

## Operation handlers {#interpreters-operation-handlers}

### semanticHandler — def

*Source:* `Interpreters.lean:94`; public

```lean
def semanticHandler (backend : SemanticBackend alpha) :
    (operation : Op alpha) -> PMF (Response operation)
```

**Natural-language explanation.** Interpret one operation probabilistically, without attaching a resource charge.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### measuredHandler — def

*Source:* `Interpreters.lean:102`; public

```lean
def measuredHandler (backend : SemanticBackend alpha) (model : CostModel alpha) :
    (operation : Op alpha) -> RandCostM Nat (Response operation)
```

**Natural-language explanation.** Interpret one operation with the selected branch cost.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### measuredHandler_joint — theorem

*Source:* `Interpreters.lean:107`; public; attributes: simp

```lean
@[simp] theorem measuredHandler_joint (backend : SemanticBackend alpha)
    (model : CostModel alpha) (operation : Op alpha) :
    (measuredHandler backend model operation).joint =
      (semanticHandler backend operation).map fun response =>
        (response, model.operationCost operation)
```

**Natural-language explanation.** For one handled operation, the joint distribution pairs every semantic response with the single cost assigned to that operation.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### firstResponse — def

*Source:* `Interpreters.lean:115`; public

```lean
def firstResponse [LinearOrder alpha] : (operation : Op alpha) -> Response operation
```

**Natural-language explanation.** The deterministic response selected by the first-position pivot backend.

**Audit focus.** Assumes a linear order on keys.

### firstTimeHandler — def

*Source:* `Interpreters.lean:121`; public

```lean
def firstTimeHandler [LinearOrder alpha] (model : CostModel alpha)
    (operation : Op alpha) : TimeM Nat (Response operation)
```

**Natural-language explanation.** Deterministic cost semantics corresponding to `SemanticBackend.firstLinearOrder`.

**Audit focus.** Assumes a linear order on keys.

### runFirstTime — def

*Source:* `Interpreters.lean:126`; public

```lean
def runFirstTime [LinearOrder alpha] (model : CostModel alpha)
    (program : Program alpha beta) : TimeM Nat beta
```

**Natural-language explanation.** Executable deterministic fold of the free program using first-position pivots.

**Audit focus.** Assumes a linear order on keys.

### semanticHandler_firstLinearOrder — theorem

*Source:* `Interpreters.lean:130`; public; attributes: simp

```lean
@[simp] theorem semanticHandler_firstLinearOrder [LinearOrder alpha]
    (operation : Op alpha) :
    semanticHandler (.firstLinearOrder) operation = PMF.pure (firstResponse operation)
```

**Natural-language explanation.** Under the first-position/linear-order backend, each operation has the single deterministic response described by `firstResponse`.

**Audit focus.** Assumes a linear order on keys.

### measuredHandler_firstLinearOrder — theorem

*Source:* `Interpreters.lean:138`; public; attributes: simp

```lean
@[simp] theorem measuredHandler_firstLinearOrder [LinearOrder alpha]
    (model : CostModel alpha) (operation : Op alpha) :
    measuredHandler (.firstLinearOrder) model operation =
      ResourceAware.Program.deterministicRandCost (firstTimeHandler model operation)
```

**Natural-language explanation.** The measured first-position handler is exactly the randomized singleton embedding of the deterministic `TimeM` handler.

**Audit focus.** Assumes a linear order on keys.

### measuredHandler_ret — theorem

*Source:* `Interpreters.lean:146`; public; attributes: simp

```lean
@[simp] theorem measuredHandler_ret (backend : SemanticBackend alpha)
    (model : CostModel alpha) (operation : Op alpha) :
    (measuredHandler backend model operation).ret = semanticHandler backend operation
```

**Natural-language explanation.** Discarding costs from one measured operation recovers its ordinary semantic response distribution.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### semanticHandler_comparison — theorem

*Source:* `Interpreters.lean:151`; public; attributes: simp

```lean
@[simp] theorem semanticHandler_comparison (backend : SemanticBackend alpha)
    (left right : alpha) :
    semanticHandler backend (.comparison (.le left right)) =
      PMF.pure (ULift.up (backend.comparison.le left right))
```

**Natural-language explanation.** A comparison request returns, with probability one, the Boolean answer supplied by the backend's comparison semantics.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### semanticHandler_baseCase — theorem

*Source:* `Interpreters.lean:157`; public; attributes: simp

```lean
@[simp] theorem semanticHandler_baseCase (backend : SemanticBackend alpha) (size : Nat) :
    semanticHandler backend (.baseCase size) = PMF.pure .unit
```

**Natural-language explanation.** A base-case request deterministically returns the unit value.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### semanticHandler_choosePivotIndex — theorem

*Source:* `Interpreters.lean:161`; public; attributes: simp

```lean
@[simp] theorem semanticHandler_choosePivotIndex (backend : SemanticBackend alpha)
    (tailLength : Nat) :
    semanticHandler backend (.choosePivotIndex tailLength) = backend.pivot.choose tailLength
```

**Natural-language explanation.** A pivot request is interpreted by the pivot distribution selected in the semantic backend.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

## PMF and RandCostM runners {#interpreters-pmf-and-randcostm-runners}

### evalWith — def

*Source:* `Interpreters.lean:169`; public

```lean
def evalWith (backend : SemanticBackend alpha) (program : Program alpha beta) : PMF beta
```

**Natural-language explanation.** Evaluate a free program under an explicitly selected semantic backend.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### eval — def

*Source:* `Interpreters.lean:173`; public

```lean
def eval [LinearOrder alpha] (program : Program alpha beta) : PMF beta
```

**Natural-language explanation.** Evaluate under uniform pivots and the ascending linear order.

**Audit focus.** Assumes a linear order on keys.

### interpretWith — def

*Source:* `Interpreters.lean:177`; public

```lean
def interpretWith (backend : SemanticBackend alpha) (model : CostModel alpha)
    (program : Program alpha beta) : RandCostM Nat beta
```

**Natural-language explanation.** Measure a free program under independently selected semantic and cost backends.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### interpret — def

*Source:* `Interpreters.lean:182`; public

```lean
def interpret [LinearOrder alpha] (model : CostModel alpha)
    (program : Program alpha beta) : RandCostM Nat beta
```

**Natural-language explanation.** Measure under the source's uniform-pivot ascending semantics.

**Audit focus.** Assumes a linear order on keys.

### quicksort — def

*Source:* `Interpreters.lean:192`; public

```lean
def quicksort [LinearOrder alpha] (xs : List alpha) : RandCostM Nat (List alpha)
```

**Natural-language explanation.** The requested comparison-counting Quicksort view. All recursive control remains in `quicksortProgram`; this declaration merely interprets that free program in `RandCostM Nat` using the comparison-only model.

**Audit focus.** Assumes a linear order on keys.

### interpretFirst — def

*Source:* `Interpreters.lean:196`; public

```lean
def interpretFirst [LinearOrder alpha] (model : CostModel alpha)
    (program : Program alpha beta) : RandCostM Nat beta
```

**Natural-language explanation.** Deterministic first-pivot execution, useful for endpoint-branch tests and witnesses.

**Audit focus.** Assumes a linear order on keys.

### interpretFirst_eq_deterministicRandCost — theorem

*Source:* `Interpreters.lean:201`; public

```lean
theorem interpretFirst_eq_deterministicRandCost [LinearOrder alpha]
    (model : CostModel alpha) (program : Program alpha beta) :
    interpretFirst model program =
      ResourceAware.Program.deterministicRandCost (runFirstTime model program)
```

**Natural-language explanation.** First-pivot execution is the singleton randomized embedding of an executable `TimeM` fold.

**Audit focus.** Assumes a linear order on keys.

### interpretLast — def

*Source:* `Interpreters.lean:217`; public

```lean
def interpretLast [LinearOrder alpha] (model : CostModel alpha)
    (program : Program alpha beta) : RandCostM Nat beta
```

**Natural-language explanation.** Deterministic last-pivot execution, useful for endpoint-branch tests and witnesses.

**Audit focus.** Assumes a linear order on keys.

### evalWith_pure — theorem

*Source:* `Interpreters.lean:221`; public; attributes: simp

```lean
@[simp] theorem evalWith_pure (backend : SemanticBackend alpha) (value : beta) :
    evalWith backend (pure value : Program alpha beta) = PMF.pure value
```

**Natural-language explanation.** Evaluating a pure free program yields the point-mass distribution at its value.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### interpretWith_pure — theorem

*Source:* `Interpreters.lean:225`; public; attributes: simp

```lean
@[simp] theorem interpretWith_pure (backend : SemanticBackend alpha)
    (model : CostModel alpha) (value : beta) :
    interpretWith backend model (pure value : Program alpha beta) = pure value
```

**Natural-language explanation.** Measuring a pure free program yields the pure zero-cost computation.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### evalWith_request — theorem

*Source:* `Interpreters.lean:230`; public; attributes: simp

```lean
@[simp] theorem evalWith_request (backend : SemanticBackend alpha) (operation : Op alpha) :
    evalWith backend (request operation) = semanticHandler backend operation
```

**Natural-language explanation.** Evaluating a single abstract request is the same as applying the semantic handler to that operation.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### evalWith_markBaseCase — theorem

*Source:* `Interpreters.lean:235`; public; attributes: simp

```lean
@[simp] theorem evalWith_markBaseCase (backend : SemanticBackend alpha) (size : Nat) :
    evalWith backend (markBaseCase size) = PMF.pure .unit
```

**Natural-language explanation.** Unmeasured evaluation of a base-case marker deterministically returns unit.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### evalWith_compareLE — theorem

*Source:* `Interpreters.lean:241`; public; attributes: simp

```lean
@[simp] theorem evalWith_compareLE (backend : SemanticBackend alpha)
    (left right : alpha) :
    evalWith backend (compareLE left right) =
      PMF.pure (ULift.up (backend.comparison.le left right))
```

**Natural-language explanation.** Unmeasured evaluation of `compareLE` deterministically returns the backend's comparison answer.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### evalWith_choosePivotIndex — theorem

*Source:* `Interpreters.lean:249`; public; attributes: simp

```lean
@[simp] theorem evalWith_choosePivotIndex (backend : SemanticBackend alpha)
    (tailLength : Nat) :
    evalWith backend (choosePivotIndex tailLength) = backend.pivot.choose tailLength
```

**Natural-language explanation.** Unmeasured evaluation of a pivot request is exactly the backend's pivot distribution.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### evalWith_liftBind — theorem

*Source:* `Interpreters.lean:256`; public

```lean
theorem evalWith_liftBind (backend : SemanticBackend alpha)
    (operation : Op alpha) (next : Response operation -> Program alpha beta) :
    evalWith backend (.liftBind operation next) =
      (semanticHandler backend operation >>= fun response =>
        evalWith backend (next response))
```

**Natural-language explanation.** Evaluating one lifted operation and its continuation is probabilistic bind: sample the response, then evaluate the selected continuation.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### evalWith_bind — theorem

*Source:* `Interpreters.lean:263`; public

```lean
theorem evalWith_bind (backend : SemanticBackend alpha)
    (program : Program alpha beta) (next : beta -> Program alpha gamma) :
    evalWith backend (program >>= next) =
      (evalWith backend program >>= fun value => evalWith backend (next value))
```

**Natural-language explanation.** The evaluator preserves monadic bind from the free program into `PMF`.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### interpretWith_request — theorem

*Source:* `Interpreters.lean:269`; public; attributes: simp

```lean
@[simp] theorem interpretWith_request (backend : SemanticBackend alpha)
    (model : CostModel alpha) (operation : Op alpha) :
    interpretWith backend model (request operation) = measuredHandler backend model operation
```

**Natural-language explanation.** Measuring a single abstract request is the same as applying the measured handler.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### interpretWith_markBaseCase — theorem

*Source:* `Interpreters.lean:275`; public; attributes: simp

```lean
@[simp] theorem interpretWith_markBaseCase (backend : SemanticBackend alpha)
    (model : CostModel alpha) (size : Nat) :
    interpretWith backend model (markBaseCase size) =
      measuredHandler backend model (.baseCase size)
```

**Natural-language explanation.** Measuring a base-case marker uses the measured handler's base-case operation.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### interpretWith_compareLE — theorem

*Source:* `Interpreters.lean:282`; public; attributes: simp

```lean
@[simp] theorem interpretWith_compareLE (backend : SemanticBackend alpha)
    (model : CostModel alpha) (left right : alpha) :
    interpretWith backend model (compareLE left right) =
      measuredHandler backend model (.comparison (.le left right))
```

**Natural-language explanation.** Measuring `compareLE` uses the measured handler's comparison operation.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### interpretWith_choosePivotIndex — theorem

*Source:* `Interpreters.lean:289`; public; attributes: simp

```lean
@[simp] theorem interpretWith_choosePivotIndex (backend : SemanticBackend alpha)
    (model : CostModel alpha) (tailLength : Nat) :
    interpretWith backend model (choosePivotIndex tailLength) =
      measuredHandler backend model (.choosePivotIndex tailLength)
```

**Natural-language explanation.** Measuring a pivot request uses the measured handler's pivot operation.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### interpretWith_liftBind — theorem

*Source:* `Interpreters.lean:296`; public

```lean
theorem interpretWith_liftBind (backend : SemanticBackend alpha)
    (model : CostModel alpha) (operation : Op alpha)
    (next : Response operation -> Program alpha beta) :
    interpretWith backend model (.liftBind operation next) =
      (measuredHandler backend model operation >>= fun response =>
        interpretWith backend model (next response))
```

**Natural-language explanation.** Measuring one lifted operation and its continuation is `RandCostM` bind: run the operation, then the selected continuation.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### interpretWith_bind — theorem

*Source:* `Interpreters.lean:304`; public

```lean
theorem interpretWith_bind (backend : SemanticBackend alpha)
    (model : CostModel alpha) (program : Program alpha beta)
    (next : beta -> Program alpha gamma) :
    interpretWith backend model (program >>= next) =
      (interpretWith backend model program >>= fun value =>
        interpretWith backend model (next value))
```

**Natural-language explanation.** The measured interpreter preserves monadic bind from the free program into `RandCostM`.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### evalWith_compareSwap — theorem

*Source:* `Interpreters.lean:312`; public; attributes: simp

```lean
@[simp] theorem evalWith_compareSwap (backend : SemanticBackend alpha) (left right : alpha) :
    evalWith backend (compareSwap left right) =
      PMF.pure (if backend.comparison.le left right then (left, right) else (right, left))
```

**Natural-language explanation.** Unmeasured compare-and-swap returns the inputs in backend-determined order as a point mass.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### interpretWith_compareSwap — theorem

*Source:* `Interpreters.lean:335`; public; attributes: simp

```lean
@[simp] theorem interpretWith_compareSwap (backend : SemanticBackend alpha)
    (model : CostModel alpha) (left right : alpha) :
    interpretWith backend model (compareSwap left right) =
      RandCostM.deterministic
        (if backend.comparison.le left right then (left, right) else (right, left))
        (model.comparison.cost left right)
```

**Natural-language explanation.** Measured compare-and-swap is deterministic, returns the backend-determined order, and charges exactly one model comparison cost for the original pair.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### interpretWith_ret_eq_evalWith — theorem

*Source:* `Interpreters.lean:348`; public; attributes: simp

```lean
@[simp] theorem interpretWith_ret_eq_evalWith (backend : SemanticBackend alpha)
    (model : CostModel alpha) (program : Program alpha beta) :
    (interpretWith backend model program).ret = evalWith backend program
```

**Natural-language explanation.** Taking the result marginal of any measured interpretation gives the corresponding unmeasured evaluation under the same semantic backend.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### interpret_ret_eq_eval — theorem

*Source:* `Interpreters.lean:354`; public; attributes: simp

```lean
@[simp] theorem interpret_ret_eq_eval [LinearOrder alpha] (model : CostModel alpha)
    (program : Program alpha beta) :
    (interpret model program).ret = eval program
```

**Natural-language explanation.** For the default uniform/linear-order semantics, erasing costs from `interpret` gives `eval`.

**Audit focus.** Assumes a linear order on keys.

### interpretWith_ret_eq — theorem

*Source:* `Interpreters.lean:360`; public

```lean
theorem interpretWith_ret_eq (backend : SemanticBackend alpha)
    (left right : CostModel alpha) (program : Program alpha beta) :
    (interpretWith backend left program).ret = (interpretWith backend right program).ret
```

**Natural-language explanation.** Changing only costs leaves the complete result marginal unchanged.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

## Ordered observations {#interpreters-ordered-observations}

### operation — def

*Source:* `Interpreters.lean:381`; public

```lean
def operation : Observation alpha -> Op alpha
```

**Natural-language explanation.** Recover the abstract operation represented by an observation.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### measurement — def

*Source:* `Interpreters.lean:387`; public

```lean
def measurement : Observation alpha -> Nat
```

**Natural-language explanation.** Read the model-selected cost stored in an observation.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### isComparison — def

*Source:* `Interpreters.lean:393`; public

```lean
def isComparison : Observation alpha -> Bool
```

**Natural-language explanation.** Whether an observation is an element comparison.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### observe — def

*Source:* `Interpreters.lean:400`; public

```lean
def observe (model : CostModel alpha) :
    (operation : Op alpha) -> Response operation -> Observation alpha
```

**Natural-language explanation.** Build the observation determined by one operation, its response, and its selected cost.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### observe_operation — theorem

*Source:* `Interpreters.lean:410`; public; attributes: simp

```lean
@[simp] theorem observe_operation (model : CostModel alpha) (operation : Op alpha)
    (response : Response operation) :
    (observe model operation response).operation = operation
```

**Natural-language explanation.** Recovering the operation from an observation produced by `observe` returns the original operation.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### observe_measurement — theorem

*Source:* `Interpreters.lean:418`; public; attributes: simp

```lean
@[simp] theorem observe_measurement (model : CostModel alpha) (operation : Op alpha)
    (response : Response operation) :
    (observe model operation response).measurement = model.operationCost operation
```

**Natural-language explanation.** The measurement stored by `observe` is exactly the cost model's charge for the original operation.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### firstTraceHandler — def

*Source:* `Interpreters.lean:427`; public

```lean
def firstTraceHandler [LinearOrder alpha] (model : CostModel alpha)
    (operation : Op alpha) : ResourceAware.TraceM (Observation alpha) (Response operation)
```

**Natural-language explanation.** Deterministic first-pivot operation semantics with one ordered observation per request.

**Audit focus.** Assumes a linear order on keys.

### runFirstTrace — def

*Source:* `Interpreters.lean:433`; public

```lean
def runFirstTrace [LinearOrder alpha] (model : CostModel alpha)
    (program : Program alpha beta) : ResourceAware.TraceM (Observation alpha) beta
```

**Natural-language explanation.** Executable ordered trace of the same free program under deterministic first pivots.

**Audit focus.** Assumes a linear order on keys.

### exactTraceCost — def

*Source:* `Interpreters.lean:438`; public

```lean
def exactTraceCost (observations : List (Observation alpha)) : Nat
```

**Natural-language explanation.** Sum the selected measurements in an ordered observation list.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### comparisonCount — def

*Source:* `Interpreters.lean:442`; public

```lean
def comparisonCount (observations : List (Observation alpha)) : Nat
```

**Natural-language explanation.** Number of element-comparison observations.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### tracedMeasuredHandler — def

*Source:* `Interpreters.lean:446`; public

```lean
def tracedMeasuredHandler (backend : SemanticBackend alpha) (model : CostModel alpha)
    (operation : Op alpha) :
    StateT (List (Observation alpha)) (RandCostM Nat) (Response operation)
```

**Natural-language explanation.** One measured operation as a state transformation accumulating ordered observations.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### interpretTracedFrom — def

*Source:* `Interpreters.lean:454`; public

```lean
def interpretTracedFrom (backend : SemanticBackend alpha) (model : CostModel alpha)
    (program : Program alpha beta) (observations : List (Observation alpha)) :
    RandCostM Nat (beta × List (Observation alpha))
```

**Natural-language explanation.** Fold a free program into the stateful traced view from an explicit initial trace.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### interpretTracedFrom_pure — theorem

*Source:* `Interpreters.lean:459`; public; attributes: simp

```lean
@[simp] theorem interpretTracedFrom_pure (backend : SemanticBackend alpha)
    (model : CostModel alpha) (value : beta)
    (observations : List (Observation alpha)) :
    interpretTracedFrom backend model (pure value) observations =
      pure (value, observations)
```

**Natural-language explanation.** Tracing a pure program leaves the initial observation list unchanged and returns the value at zero additional cost.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### interpretTracedFrom_bind — theorem

*Source:* `Interpreters.lean:466`; public

```lean
theorem interpretTracedFrom_bind (backend : SemanticBackend alpha)
    (model : CostModel alpha) (program : Program alpha beta)
    (next : beta -> Program alpha gamma) (observations : List (Observation alpha)) :
    interpretTracedFrom backend model (program >>= next) observations =
      (do
        let outcome <- interpretTracedFrom backend model program observations
        interpretTracedFrom backend model (next outcome.1) outcome.2)
```

**Natural-language explanation.** Tracing a bind first traces the initial program, then starts the chosen continuation from the accumulated trace.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### interpretTracedWith — def

*Source:* `Interpreters.lean:478`; public

```lean
def interpretTracedWith (backend : SemanticBackend alpha) (model : CostModel alpha)
    (program : Program alpha beta) : RandCostM Nat (beta × List (Observation alpha))
```

**Natural-language explanation.** Fold a free program into the stateful traced view with an initially empty trace.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### interpretTraced — def

*Source:* `Interpreters.lean:483`; public

```lean
def interpretTraced [LinearOrder alpha] (model : CostModel alpha)
    (program : Program alpha beta) : RandCostM Nat (beta × List (Observation alpha))
```

**Natural-language explanation.** Uniform-pivot ascending traced execution.

**Audit focus.** Assumes a linear order on keys.

### run'_liftM_tracedMeasuredHandler — theorem

*Source:* `Interpreters.lean:489`; private

```lean
private theorem run'_liftM_tracedMeasuredHandler (backend : SemanticBackend alpha)
    (model : CostModel alpha) (program : Program alpha beta)
    (observations : List (Observation alpha)) :
    StateT.run'
        (program.liftM (tracedMeasuredHandler backend model)) observations =
      program.liftM (measuredHandler backend model)
```

**Natural-language explanation.** Private bridge: after projecting away trace state, folding with the traced handler equals folding with the ordinary measured handler.

**Audit focus.** Private proof helper; not part of the public API.

### eraseTrace_interpretTracedFrom — theorem

*Source:* `Interpreters.lean:521`; private

```lean
private theorem eraseTrace_interpretTracedFrom (backend : SemanticBackend alpha)
    (model : CostModel alpha) (program : Program alpha beta)
    (observations : List (Observation alpha)) :
    (Prod.fst <$> interpretTracedFrom backend model program observations) =
      interpretWith backend model program
```

**Natural-language explanation.** Private bridge: discarding observations from a traced run with any initial trace recovers the ordinary measured interpretation.

**Audit focus.** Private proof helper; not part of the public API.

### eraseTrace_interpretTracedWith — theorem

*Source:* `Interpreters.lean:529`; public

```lean
theorem eraseTrace_interpretTracedWith (backend : SemanticBackend alpha)
    (model : CostModel alpha) (program : Program alpha beta) :
    (Prod.fst <$> interpretTracedWith backend model program) =
      interpretWith backend model program
```

**Natural-language explanation.** Erasing observations preserves the complete measured joint result/cost distribution.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### interpretTracedWith_ret_map_fst — theorem

*Source:* `Interpreters.lean:535`; public; attributes: simp

```lean
@[simp] theorem interpretTracedWith_ret_map_fst (backend : SemanticBackend alpha)
    (model : CostModel alpha) (program : Program alpha beta) :
    (interpretTracedWith backend model program).ret.map Prod.fst = evalWith backend program
```

**Natural-language explanation.** After tracing, discarding both costs and the trace leaves exactly the ordinary unmeasured result distribution.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

# Correctness: sorted permutations of the input {#correctness}

[Back to contents](#contents)

**Source file:** `TextbookAlgorithms/KleinbergTardos/Chapter13/RandomizedQuicksort/Correctness.lean`  
**Declarations in this section:** 11

## Foundations {#correctness-foundations}

### PartitionCorrect — def

*Source:* `Correctness.lean:30`; public

```lean
def PartitionCorrect [LE alpha] (pivot : alpha) {input : List alpha}
    (parts : PartitionResult input) : Prop
```

**Natural-language explanation.** Order facts established by one interpreted partitioning pass.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### partitionProgram_support_correct — theorem

*Source:* `Correctness.lean:37`; public

```lean
theorem partitionProgram_support_correct [LinearOrder alpha] (pivot : alpha) :
    forall (input : List alpha) (parts : PartitionResult input),
      parts ∈ (eval (partitionProgram pivot input)).support ->
        PartitionCorrect pivot parts
```

**Natural-language explanation.** Every result supported by the linear-order partition interpreter lies on the proper side of the pivot. The permutation component is already carried by `PartitionResult`.

**Audit focus.** Assumes a linear order on keys. Quantifies only over supported (possible) outcomes.

## Correctness of the constant-size sorting network {#correctness-small-network}

### evalWith_map — theorem

*Source:* `Correctness.lean:86`; public

```lean
theorem evalWith_map (backend : SemanticBackend alpha) (f : beta -> gamma)
    (program : Program alpha beta) :
    evalWith backend (f <$> program) = (evalWith backend program).map f
```

**Natural-language explanation.** Evaluation preserves the functorial map of a free program.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### evalWith_seqRight — theorem

*Source:* `Correctness.lean:95`; public

```lean
theorem evalWith_seqRight (backend : SemanticBackend alpha)
    (program : Program alpha beta) (next : Program alpha gamma) :
    evalWith backend (program *> next) =
      (evalWith backend program >>= fun _ => evalWith backend next)
```

**Natural-language explanation.** Evaluation turns syntax-level right sequencing into probabilistic bind.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### pmf_pure_bind_local — theorem

*Source:* `Correctness.lean:102`; public; attributes: simp

```lean
@[simp] theorem pmf_pure_bind_local (value : beta) (next : beta -> PMF gamma) :
    ((pure value : PMF beta) >>= next) = next value
```

**Natural-language explanation.** The type-class presentation of PMF bind has the expected pure-left law.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### compareSwap_support_correct — theorem

*Source:* `Correctness.lean:108`; public

```lean
theorem compareSwap_support_correct [LinearOrder alpha]
    (left right : alpha) (pair : alpha × alpha)
    (hpair : pair ∈ (eval (compareSwap left right)).support) :
    pair.1 <= pair.2 ∧ [pair.1, pair.2].Perm [left, right]
```

**Natural-language explanation.** One interpreted compare-and-swap returns an ordered permutation of its inputs.

**Audit focus.** Assumes a linear order on keys. Quantifies only over supported (possible) outcomes.

### sortSmallProgram_support_correct — theorem

*Source:* `Correctness.lean:125`; public

```lean
theorem sortSmallProgram_support_correct [LinearOrder alpha]
    (input output : List alpha)
    (hLength : input.length <= 3)
    (hOutput : output ∈ (eval (sortSmallProgram input)).support) :
    Sorting.Correct input output
```

**Natural-language explanation.** The fixed network used for textbook base cases returns a sorted permutation.

**Audit focus.** Assumes a linear order on keys. Quantifies only over supported (possible) outcomes. Restricted to the base-case sizes, at most three.

## Recursive Quicksort correctness {#correctness-recursive-quicksort}

### join_correct — theorem

*Source:* `Correctness.lean:221`; public

```lean
theorem join_correct [LinearOrder alpha] {input remainder : List alpha} (pivot : alpha)
    (parts : PartitionResult remainder) (sortedLower sortedUpper : List alpha)
    (hPartition : PartitionCorrect pivot parts)
    (hLower : Sorting.Correct parts.lower sortedLower)
    (hUpper : Sorting.Correct parts.upper sortedUpper)
    (hPivot : (pivot :: remainder).Perm input) :
    Sorting.Correct input (sortedLower ++ pivot :: sortedUpper)
```

**Natural-language explanation.** Correct recursive results can be joined around a certified partition pivot.

**Audit focus.** Assumes a linear order on keys.

### quicksortProgram_support_correct — theorem

*Source:* `Correctness.lean:257`; public

```lean
theorem quicksortProgram_support_correct [LinearOrder alpha]
    (input output : List alpha)
    (hOutput : output ∈ (eval (quicksortProgram input)).support) :
    Sorting.Correct input output
```

**Natural-language explanation.** Kleinberg--Tardos, Section 13.5, pages 731--732: every result supported by the uniform-pivot free-program interpretation is a sorted permutation of its input.

**Audit focus.** Assumes a linear order on keys. Quantifies only over supported (possible) outcomes. This stronger free-program theorem does not assume `Nodup`; it proves sorted-permutation correctness for every supported output.

### quicksort_result_correct — theorem

*Source:* `Correctness.lean:316`; public

```lean
theorem quicksort_result_correct [LinearOrder alpha]
    (input output : List alpha) (_hNodup : input.Nodup)
    (hOutput : output ∈ (quicksort input).ret.support) :
    Sorting.Correct input output
```

**Natural-language explanation.** Kleinberg--Tardos, pp. 731--732 (unnumbered): every supported result of the actual comparison-counting `RandCostM` runner is a sorted permutation of the input.

**Audit focus.** Assumes a linear order on keys. Requires a duplicate-free input. Quantifies only over supported (possible) outcomes. The public theorem includes an `input.Nodup` hypothesis, but the proof does not use it. Its conclusion is only functional correctness, not a cost or probability claim.

### quicksort_joint_support_correct — theorem

*Source:* `Correctness.lean:326`; public

```lean
theorem quicksort_joint_support_correct [LinearOrder alpha]
    (input output : List alpha) (cost : Nat)
    (_hNodup : input.Nodup)
    (hOutput : (output, cost) ∈ (quicksort input).joint.support) :
    Sorting.Correct input output
```

**Natural-language explanation.** Every result-cost branch of the default runner returns a correct sorting result.

**Audit focus.** Assumes a linear order on keys. Requires a duplicate-free input. Quantifies over supported result-cost branches. The theorem ranges over supported result-cost pairs but concludes only result correctness; it does not constrain the cost here.

# Complexity: expected and worst supported costs {#complexity}

[Back to contents](#contents)

**Source file:** `TextbookAlgorithms/KleinbergTardos/Chapter13/RandomizedQuicksort/Complexity.lean`  
**Declarations in this section:** 116

## Joint-support decomposition {#complexity-joint-support}

### mem_joint_support_bind_iff — theorem

*Source:* `Complexity.lean:38`; public

```lean
theorem mem_joint_support_bind_iff (m : RandCostM Nat beta)
    (next : beta -> RandCostM Nat gamma) (result : gamma) (cost : Nat) :
    (result, cost) ∈ (m >>= next).joint.support ↔
      ∃ value firstCost secondCost,
        (value, firstCost) ∈ m.joint.support ∧
        (result, secondCost) ∈ (next value).joint.support ∧
        cost = firstCost + secondCost
```

**Natural-language explanation.** Membership in the joint support of a cost-monad bind exposes both branch costs.

**Audit focus.** Quantifies over supported result-cost branches.

### joint_support_sample_cost_eq_zero — theorem

*Source:* `Complexity.lean:59`; public

```lean
theorem joint_support_sample_cost_eq_zero (distribution : PMF beta)
    (value : beta) (cost : Nat)
    (hMem : (value, cost) ∈
      (RandCostM.sample distribution : RandCostM Nat beta).joint.support) :
    cost = 0
```

**Natural-language explanation.** Any supported branch of an uncharged probabilistic sample has cost zero.

**Audit focus.** Quantifies over supported result-cost branches.

### mem_joint_support_sample_of_mem — theorem

*Source:* `Complexity.lean:68`; public

```lean
theorem mem_joint_support_sample_of_mem (distribution : PMF beta) (value : beta)
    (hValue : value ∈ distribution.support) :
    (value, 0) ∈
      (RandCostM.sample distribution : RandCostM Nat beta).joint.support
```

**Natural-language explanation.** Every value in a distribution's support appears in the zero-cost joint support of the corresponding uncharged sample.

**Audit focus.** Quantifies over supported result-cost branches.

## Exact comparison cost of partitioning {#complexity-partition-cost}

### linearPartition — def

*Source:* `Complexity.lean:78`; public

```lean
def linearPartition [LinearOrder alpha] (pivot : alpha) :
    (input : List alpha) -> PartitionResult input
```

**Natural-language explanation.** The mathematical partition selected by the truthful linear-order comparison backend.

**Audit focus.** Assumes a linear order on keys.

### linearPartition_lower — theorem

*Source:* `Complexity.lean:96`; public; attributes: simp

```lean
@[simp] theorem linearPartition_lower [LinearOrder alpha]
    (pivot : alpha) (input : List alpha) :
    (linearPartition pivot input).lower =
      input.filter (fun value => decide (value <= pivot))
```

**Natural-language explanation.** The lower list produced by mathematical partitioning is exactly the input filtered by `value <= pivot`.

**Audit focus.** Assumes a linear order on keys.

### linearPartition_upper — theorem

*Source:* `Complexity.lean:106`; public; attributes: simp

```lean
@[simp] theorem linearPartition_upper [LinearOrder alpha]
    (pivot : alpha) (input : List alpha) :
    (linearPartition pivot input).upper =
      input.filter (fun value => decide (pivot < value))
```

**Natural-language explanation.** The upper list produced by mathematical partitioning is exactly the input filtered by `pivot < value`.

**Audit focus.** Assumes a linear order on keys.

### pivotRankEquiv — def

*Source:* `Complexity.lean:121`; public

```lean
def pivotRankEquiv [LinearOrder alpha] (input : List alpha) (hNodup : input.Nodup) :
    Fin input.length ≃ Fin input.length
```

**Natural-language explanation.** Reindex list positions by the sorted rank of the selected value. Duplicate freedom makes this a permutation of `Fin input.length`.

**Audit focus.** Assumes a linear order on keys. Requires a duplicate-free input.

### card_filter_lt_orderEmb — theorem

*Source:* `Complexity.lean:130`; public

```lean
theorem card_filter_lt_orderEmb [LinearOrder alpha] (values : Finset alpha)
    {n : Nat} (hCard : values.card = n) (i : Fin n) :
    (values.filter fun value => value < values.orderEmbOfFin hCard i).card = i
```

**Natural-language explanation.** In a finite linear order presented by `orderEmbOfFin`, exactly `i` elements precede the element at rank `i`.

**Audit focus.** Assumes a linear order on keys.

### linearPartition_lower_length_eq_rank — theorem

*Source:* `Complexity.lean:167`; public

```lean
theorem linearPartition_lower_length_eq_rank [LinearOrder alpha]
    (input : List alpha) (hNodup : input.Nodup) (index : Fin input.length) :
    (linearPartition (input.get index) (input.eraseIdx index)).lower.length =
      pivotRankEquiv input hNodup index
```

**Natural-language explanation.** The concrete lower partition has the sorted rank of the chosen pivot as its length.

**Audit focus.** Assumes a linear order on keys. Requires a duplicate-free input.

### linearPartition_upper_length_eq — theorem

*Source:* `Complexity.lean:217`; public

```lean
theorem linearPartition_upper_length_eq [LinearOrder alpha]
    (input : List alpha) (hNodup : input.Nodup) (index : Fin input.length) :
    (linearPartition (input.get index) (input.eraseIdx index)).upper.length =
      input.length - 1 - pivotRankEquiv input hNodup index
```

**Natural-language explanation.** The complementary concrete upper partition has size `n - 1 - rank`.

**Audit focus.** Assumes a linear order on keys. Requires a duplicate-free input.

### interpretWith_compareLE_comparisonOnly — theorem

*Source:* `Complexity.lean:231`; public; attributes: simp

```lean
@[simp] theorem interpretWith_compareLE_comparisonOnly [LinearOrder alpha]
    (left right : alpha) :
    interpretWith SemanticBackend.uniformLinearOrder CostModel.comparisonOnly
        (compareLE left right) =
      RandCostM.deterministic (ULift.up (decide (left <= right))) 1
```

**Natural-language explanation.** Under the comparison-only model, one partition pass costs exactly one comparison per input element. This theorem is about the actual `RandCostM` interpretation, not an isolated recurrence.

**Audit focus.** Assumes a linear order on keys. Uses the model that charges comparisons and makes structural work free.

### interpretWith_map — theorem

*Source:* `Complexity.lean:244`; public

```lean
theorem interpretWith_map (backend : SemanticBackend alpha) (model : CostModel alpha)
    (f : beta -> gamma) (program : Program alpha beta) :
    interpretWith backend model (f <$> program) =
      f <$> interpretWith backend model program
```

**Natural-language explanation.** Interpretation preserves the functorial map of the free program.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### expectedCost_interpretWith_map — theorem

*Source:* `Complexity.lean:251`; public; attributes: simp

```lean
@[simp] theorem expectedCost_interpretWith_map
    (backend : SemanticBackend alpha) (model : CostModel alpha)
    (f : beta -> gamma) (program : Program alpha beta) :
    (interpretWith backend model (f <$> program)).expectedCost =
      (interpretWith backend model program).expectedCost
```

**Natural-language explanation.** Mapping a pure function over an interpreted result does not change its expected accumulated cost.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### interpretWith_markBaseCase_comparisonOnly — theorem

*Source:* `Complexity.lean:258`; public; attributes: simp

```lean
@[simp] theorem interpretWith_markBaseCase_comparisonOnly
    (backend : SemanticBackend alpha) (size : Nat) :
    interpretWith backend CostModel.comparisonOnly (markBaseCase size) =
      RandCostM.deterministic PUnit.unit 0
```

**Natural-language explanation.** Under the comparison-only model, a base-case marker deterministically returns unit at cost zero.

**Audit focus.** Uses the model that charges comparisons and makes structural work free.

### interpret_partitionProgram_comparisonOnly — theorem

*Source:* `Complexity.lean:268`; public

```lean
theorem interpret_partitionProgram_comparisonOnly [LinearOrder alpha]
    (pivot : alpha) (input : List alpha) :
    interpret CostModel.comparisonOnly (partitionProgram pivot input) =
      RandCostM.deterministic (linearPartition pivot input) input.length
```

**Natural-language explanation.** Under uniform linear-order semantics and comparison-only cost, partitioning is deterministic, returns `linearPartition`, and costs exactly the input length.

**Audit focus.** Assumes a linear order on keys. Uses the model that charges comparisons and makes structural work free.

### smallComparisonCost — def

*Source:* `Complexity.lean:288`; public

```lean
def smallComparisonCost : Nat -> Nat
```

**Natural-language explanation.** Exact comparison count of the fixed sorting network used for sizes at most three.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### expectedCost_sortSmallProgram_comparisonOnly — theorem

*Source:* `Complexity.lean:294`; public

```lean
theorem expectedCost_sortSmallProgram_comparisonOnly [LinearOrder alpha]
    (input : List alpha) (hLength : input.length <= 3) :
    (interpret CostModel.comparisonOnly (sortSmallProgram input)).expectedCost =
      smallComparisonCost input.length
```

**Natural-language explanation.** The interpreted base-case sorting network has its advertised exact comparison cost.

**Audit focus.** Assumes a linear order on keys. Restricted to the base-case sizes, at most three. Uses the model that charges comparisons and makes structural work free.

## A run-derived uniform-pivot recurrence {#complexity-recurrence}

### partitionAt — def

*Source:* `Complexity.lean:342`; public

```lean
def partitionAt [LinearOrder alpha] (input : List alpha) (index : Fin input.length) :
    PartitionResult (input.eraseIdx index)
```

**Natural-language explanation.** The deterministic partition selected after choosing a concrete pivot position.

**Audit focus.** Assumes a linear order on keys.

### lowerSubproblem — def

*Source:* `Complexity.lean:347`; public

```lean
def lowerSubproblem [LinearOrder alpha] (input : List alpha)
    (index : Fin input.length) : List alpha
```

**Natural-language explanation.** The lower recursive input selected by one pivot position.

**Audit focus.** Assumes a linear order on keys.

### upperSubproblem — def

*Source:* `Complexity.lean:352`; public

```lean
def upperSubproblem [LinearOrder alpha] (input : List alpha)
    (index : Fin input.length) : List alpha
```

**Natural-language explanation.** The upper recursive input selected by one pivot position.

**Audit focus.** Assumes a linear order on keys.

### lowerSubproblem_nodup — theorem

*Source:* `Complexity.lean:356`; public

```lean
theorem lowerSubproblem_nodup [LinearOrder alpha]
    (input : List alpha) (hNodup : input.Nodup) (index : Fin input.length) :
    (lowerSubproblem input index).Nodup
```

**Natural-language explanation.** If the input has no duplicates, the lower recursive subproblem also has no duplicates.

**Audit focus.** Assumes a linear order on keys. Requires a duplicate-free input.

### upperSubproblem_nodup — theorem

*Source:* `Complexity.lean:363`; public

```lean
theorem upperSubproblem_nodup [LinearOrder alpha]
    (input : List alpha) (hNodup : input.Nodup) (index : Fin input.length) :
    (upperSubproblem input index).Nodup
```

**Natural-language explanation.** If the input has no duplicates, the upper recursive subproblem also has no duplicates.

**Audit focus.** Assumes a linear order on keys. Requires a duplicate-free input.

### lowerSubproblem_length — theorem

*Source:* `Complexity.lean:370`; public; attributes: simp

```lean
@[simp] theorem lowerSubproblem_length [LinearOrder alpha]
    (input : List alpha) (hNodup : input.Nodup) (index : Fin input.length) :
    (lowerSubproblem input index).length = pivotRankEquiv input hNodup index
```

**Natural-language explanation.** For a duplicate-free input, the lower subproblem size is the sorted rank of the chosen pivot.

**Audit focus.** Assumes a linear order on keys. Requires a duplicate-free input.

### upperSubproblem_length — theorem

*Source:* `Complexity.lean:375`; public; attributes: simp

```lean
@[simp] theorem upperSubproblem_length [LinearOrder alpha]
    (input : List alpha) (hNodup : input.Nodup) (index : Fin input.length) :
    (upperSubproblem input index).length =
      input.length - 1 - pivotRankEquiv input hNodup index
```

**Natural-language explanation.** For a duplicate-free input of size `n`, the upper subproblem size is `n - 1 - rank`.

**Audit focus.** Assumes a linear order on keys. Requires a duplicate-free input.

### quicksortContinuation — def

*Source:* `Complexity.lean:382`; public

```lean
def quicksortContinuation [LinearOrder alpha] (input : List alpha)
    (index : Fin input.length) : Program alpha (List alpha)
```

**Natural-language explanation.** The free-program continuation after a pivot position has been supplied.

**Audit focus.** Assumes a linear order on keys.

### expectedCost_quicksortContinuation — theorem

*Source:* `Complexity.lean:393`; public

```lean
theorem expectedCost_quicksortContinuation [LinearOrder alpha]
    (input : List alpha) (index : Fin input.length) :
    (interpret CostModel.comparisonOnly
      (quicksortContinuation input index)).expectedCost =
      ((input.length - 1 : Nat) : ENNReal) +
        (quicksort (lowerSubproblem input index)).expectedCost +
        (quicksort (upperSubproblem input index)).expectedCost
```

**Natural-language explanation.** Supplying a fixed pivot to the actual interpreter costs one partition pass followed by the costs of the two actual recursive calls.

**Audit focus.** Assumes a linear order on keys. Uses the model that charges comparisons and makes structural work free.

### interpretWith_choosePivotIndex_comparisonOnly — theorem

*Source:* `Complexity.lean:412`; public; attributes: simp

```lean
@[simp] theorem interpretWith_choosePivotIndex_comparisonOnly [LinearOrder alpha]
    (tailLength : Nat) :
    interpretWith (SemanticBackend.uniformLinearOrder (alpha := alpha))
        (CostModel.comparisonOnly (alpha := alpha))
        (choosePivotIndex tailLength) =
      (RandCostM.sample
        (PMF.uniformOfFintype (ULift (Fin (tailLength + 1)))) :
          RandCostM Nat (ULift (Fin (tailLength + 1))))
```

**Natural-language explanation.** Choosing a pivot under the source backend is exactly zero-cost uniform sampling.

**Audit focus.** Assumes a linear order on keys. Uses the model that charges comparisons and makes structural work free.

### expectedCost_quicksort_step — theorem

*Source:* `Complexity.lean:424`; public

```lean
theorem expectedCost_quicksort_step [LinearOrder alpha]
    (first : alpha) (rest : List alpha)
    (hLong : ¬(first :: rest).length <= 3) :
    (quicksort (first :: rest)).expectedCost =
      (((first :: rest).length : Nat) : ENNReal)⁻¹ *
        ∑ index : Fin (first :: rest).length,
          (interpret CostModel.comparisonOnly
            (quicksortContinuation (first :: rest) index)).expectedCost
```

**Natural-language explanation.** Exact expected-cost equation obtained by unfolding the actual uniform-pivot runner once.

**Audit focus.** Assumes a linear order on keys. Applies only to the recursive case, size greater than three. Uses the model that charges comparisons and makes structural work free.

### expectedCost_quicksort_recurrence — theorem

*Source:* `Complexity.lean:444`; public

```lean
theorem expectedCost_quicksort_recurrence [LinearOrder alpha]
    (first : alpha) (rest : List alpha)
    (hLong : ¬(first :: rest).length <= 3) :
    (quicksort (first :: rest)).expectedCost =
      (((first :: rest).length : Nat) : ENNReal)⁻¹ *
        ∑ index : Fin (first :: rest).length,
          ((((first :: rest).length - 1 : Nat) : ENNReal) +
            (quicksort
              (lowerSubproblem (alpha := alpha) (first :: rest)
                (index : Fin (first :: rest).length))).expectedCost +
            (quicksort
              (upperSubproblem (alpha := alpha) (first :: rest)
                (index : Fin (first :: rest).length))).expectedCost)
```

**Natural-language explanation.** The preceding run-derived equation with the exact partition and recursive costs exposed.

**Audit focus.** Assumes a linear order on keys. Applies only to the recursive case, size greater than three.

## A harmonic comparison envelope {#complexity-harmonic-envelope}

### expectedComparisonEnvelope — def

*Source:* `Complexity.lean:467`; public

```lean
def expectedComparisonEnvelope (n : Nat) : Real
```

**Natural-language explanation.** A convenient real-valued upper envelope for the standard uniform-pivot recurrence.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### harmonic_nonneg_real — theorem

*Source:* `Complexity.lean:470`; public

```lean
theorem harmonic_nonneg_real (n : Nat) : (0 : Real) <= (harmonic n : Real)
```

**Natural-language explanation.** The harmonic number, viewed as a real number, is nonnegative.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### expectedComparisonEnvelope_zero — theorem

*Source:* `Complexity.lean:476`; public; attributes: simp

```lean
@[simp] theorem expectedComparisonEnvelope_zero : expectedComparisonEnvelope 0 = 0
```

**Natural-language explanation.** The comparison envelope is zero at input size zero.

**Audit focus.** Uses a proved upper envelope rather than an exact expected-cost formula.

### expectedComparisonEnvelope_nonneg — theorem

*Source:* `Complexity.lean:479`; public

```lean
theorem expectedComparisonEnvelope_nonneg (n : Nat) :
    0 <= expectedComparisonEnvelope n
```

**Natural-language explanation.** The comparison envelope is nonnegative for every natural input size.

**Audit focus.** Uses a proved upper envelope rather than an exact expected-cost formula.

### nLogN — def

*Source:* `Complexity.lean:486`; public

```lean
def nLogN (n : Nat) : Real
```

**Natural-language explanation.** The real-valued n-times-one-plus-log-n benchmark used for the asymptotic statement.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### nLogN_nonneg — theorem

*Source:* `Complexity.lean:489`; public

```lean
theorem nLogN_nonneg {n : Nat} (hn : 1 <= n) : 0 <= nLogN n
```

**Natural-language explanation.** The chosen `n(1 + log n)` benchmark is nonnegative whenever `n >= 1`.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### nLogN_isBigO_mul_log — theorem

*Source:* `Complexity.lean:495`; public

```lean
theorem nLogN_isBigO_mul_log :
    nLogN =O[atTop] (fun n : Nat => (n : Real) * Real.log n)
```

**Natural-language explanation.** The nonnegative recurrence envelope is asymptotically bounded by the conventional `n * log n` benchmark.

**Audit focus.** Asymptotic upper bound; multiplicative constants and a finite prefix are hidden.

### expectedComparisonEnvelope_isBigO — theorem

*Source:* `Complexity.lean:512`; public

```lean
theorem expectedComparisonEnvelope_isBigO :
    expectedComparisonEnvelope =O[atTop] nLogN
```

**Natural-language explanation.** The harmonic comparison envelope grows in O(n log n).

**Audit focus.** Asymptotic upper bound; multiplicative constants and a finite prefix are hidden. Uses a proved upper envelope rather than an exact expected-cost formula.

## Solving the uniform-pivot recurrence {#complexity-solving-recurrence}

### sum_weighted_harmonic — theorem

*Source:* `Complexity.lean:537`; public

```lean
theorem sum_weighted_harmonic (n : Nat) :
    ∑ k ∈ Finset.range n, ((k + 1 : Nat) : Real) * (harmonic k : Real) =
      (n : Real) * (n + 1) / 2 * (harmonic n : Real) -
        (n : Real) * (n + 3) / 4
```

**Natural-language explanation.** The weighted harmonic sum that appears after averaging the two recursive subproblems.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### sum_expectedComparisonEnvelope — theorem

*Source:* `Complexity.lean:551`; public

```lean
theorem sum_expectedComparisonEnvelope (n : Nat) :
    ∑ k ∈ Finset.range n, expectedComparisonEnvelope k =
      3 * ((n : Real) * (n + 1) / 2 * (harmonic n : Real) -
        (n : Real) * (n + 3) / 4)
```

**Natural-language explanation.** The sum of the harmonic envelopes below `n`.

**Audit focus.** Uses a proved upper envelope rather than an exact expected-cost formula.

### expectedComparisonEnvelope_recurrence — theorem

*Source:* `Complexity.lean:570`; public

```lean
theorem expectedComparisonEnvelope_recurrence (n : Nat) (hLong : 4 <= n) :
    (((n - 1 : Nat) : Real) +
        (n : Real)⁻¹ *
          ∑ k ∈ Finset.range n,
            (expectedComparisonEnvelope k +
              expectedComparisonEnvelope (n - 1 - k))) <=
      expectedComparisonEnvelope n
```

**Natural-language explanation.** The harmonic envelope is a supersolution of the uniform-pivot comparison recurrence.

**Audit focus.** Uses a proved upper envelope rather than an exact expected-cost formula.

### expectedComparisonEnvelopeENN — def

*Source:* `Complexity.lean:600`; public

```lean
def expectedComparisonEnvelopeENN (n : Nat) : ENNReal
```

**Natural-language explanation.** The same harmonic envelope in the codomain used by `RandCostM.ecwp`.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### expectedComparisonEnvelopeENN_zero — theorem

*Source:* `Complexity.lean:603`; public; attributes: simp

```lean
@[simp] theorem expectedComparisonEnvelopeENN_zero :
    expectedComparisonEnvelopeENN 0 = 0
```

**Natural-language explanation.** The extended-nonnegative-real version of the comparison envelope is zero at size zero.

**Audit focus.** Uses a proved upper envelope rather than an exact expected-cost formula.

### expectedComparisonEnvelopeENN_recurrence_range — theorem

*Source:* `Complexity.lean:608`; public

```lean
theorem expectedComparisonEnvelopeENN_recurrence_range
    (n : Nat) (hLong : 4 <= n) :
    (((n - 1 : Nat) : ENNReal) +
        (n : ENNReal)⁻¹ *
          ∑ k ∈ Finset.range n,
            (expectedComparisonEnvelopeENN k +
              expectedComparisonEnvelopeENN (n - 1 - k))) <=
      expectedComparisonEnvelopeENN n
```

**Natural-language explanation.** `ENNReal` form of the recurrence supersolution, indexed by `Finset.range`.

**Audit focus.** Uses a proved upper envelope rather than an exact expected-cost formula.

### expectedComparisonEnvelopeENN_recurrence — theorem

*Source:* `Complexity.lean:651`; public

```lean
theorem expectedComparisonEnvelopeENN_recurrence
    (n : Nat) (hLong : 4 <= n) :
    (((n - 1 : Nat) : ENNReal) +
        (n : ENNReal)⁻¹ *
          ∑ index : Fin n,
            (expectedComparisonEnvelopeENN index.val +
              expectedComparisonEnvelopeENN (n - 1 - index.val))) <=
      expectedComparisonEnvelopeENN n
```

**Natural-language explanation.** `Fin n` form used by the interpreter's uniform-pivot recurrence.

**Audit focus.** Uses a proved upper envelope rather than an exact expected-cost formula.

### expectedComparisonEnvelopeENN_recurrence_averaged — theorem

*Source:* `Complexity.lean:674`; public

```lean
theorem expectedComparisonEnvelopeENN_recurrence_averaged
    (n : Nat) (hLong : 4 <= n) :
    (n : ENNReal)⁻¹ *
        ∑ index : Fin n,
          ((((n - 1 : Nat) : ENNReal) +
              expectedComparisonEnvelopeENN index.val) +
            expectedComparisonEnvelopeENN (n - 1 - index.val)) <=
      expectedComparisonEnvelopeENN n
```

**Natural-language explanation.** The recurrence in the exact shape emitted by the runner, with the partition charge inside the uniform average.

**Audit focus.** Uses a proved upper envelope rather than an exact expected-cost formula.

### smallComparisonCost_le_expectedComparisonEnvelopeENN — theorem

*Source:* `Complexity.lean:709`; public

```lean
theorem smallComparisonCost_le_expectedComparisonEnvelopeENN
    (n : Nat) (hSmall : n <= 3) :
    (smallComparisonCost n : ENNReal) <= expectedComparisonEnvelopeENN n
```

**Natural-language explanation.** The fixed base-case network lies below the common harmonic envelope.

**Audit focus.** Uses a proved upper envelope rather than an exact expected-cost formula.

### expectedCost_quicksort_of_length_le_three — theorem

*Source:* `Complexity.lean:716`; public

```lean
theorem expectedCost_quicksort_of_length_le_three [LinearOrder alpha]
    (input : List alpha) (hSmall : input.length <= 3) :
    (quicksort input).expectedCost = smallComparisonCost input.length
```

**Natural-language explanation.** For inputs of length at most three, the default runner's expected comparison cost equals the exact sorting-network count.

**Audit focus.** Assumes a linear order on keys. Restricted to the base-case sizes, at most three.

### quicksort_expectedComparisonCost_le — theorem

*Source:* `Complexity.lean:730`; public

```lean
theorem quicksort_expectedComparisonCost_le [LinearOrder alpha]
    (input : List alpha) (hNodup : input.Nodup) :
    (quicksort input).expectedCost <=
      expectedComparisonEnvelopeENN input.length
```

**Natural-language explanation.** Approved extension (expected comparisons): the actual uniform `RandCostM` runner has expected comparison cost at most the harmonic envelope on every duplicate-free input.

**Audit focus.** Assumes a linear order on keys. Requires a duplicate-free input. Uses a proved upper envelope rather than an exact expected-cost formula. This is an upper bound, not the exact expected-comparison formula. It requires duplicate-free inputs and counts comparisons only.

### quicksort_ecwp_comparisons_le — theorem

*Source:* `Complexity.lean:795`; public

```lean
theorem quicksort_ecwp_comparisons_le [LinearOrder alpha]
    (input : List alpha) (hNodup : input.Nodup) :
    RandCostM.ecwp (quicksort input) (fun _ => 0) <=
      expectedComparisonEnvelopeENN input.length
```

**Natural-language explanation.** The requested `ecwp` statement; zero post-cost observes exactly the expected comparison count proved above.

**Audit focus.** Assumes a linear order on keys. Requires a duplicate-free input. Uses a proved upper envelope rather than an exact expected-cost formula. The post-cost is identically zero, so this `ecwp` endpoint observes only accumulated comparison cost.

### expectedComparisonsBySize — def

*Source:* `Complexity.lean:804`; public

```lean
def expectedComparisonsBySize (n : Nat) : Real
```

**Natural-language explanation.** A size-indexed real-valued observation of the actual runner, using `List.range n` as a canonical duplicate-free input. The pointwise theorem above shows that the same envelope applies to every duplicate-free input of that size.

**Audit focus.** This size-indexed function evaluates only the canonical distinct input `List.range n`; the preceding pointwise theorem supplies the all-distinct-input bound.

### expectedComparisonsBySize_nonneg — theorem

*Source:* `Complexity.lean:807`; public

```lean
theorem expectedComparisonsBySize_nonneg (n : Nat) :
    0 <= expectedComparisonsBySize n
```

**Natural-language explanation.** The size-indexed expected comparison count on `List.range n` is nonnegative.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### expectedComparisonsBySize_le — theorem

*Source:* `Complexity.lean:811`; public

```lean
theorem expectedComparisonsBySize_le (n : Nat) :
    expectedComparisonsBySize n <= expectedComparisonEnvelope n
```

**Natural-language explanation.** On the canonical input `List.range n`, the real-valued expected comparison count is at most the harmonic comparison envelope.

**Audit focus.** Uses a proved upper envelope rather than an exact expected-cost formula.

### expectedComparisonsBySize_isBigO — theorem

*Source:* `Complexity.lean:830`; public

```lean
theorem expectedComparisonsBySize_isBigO :
    expectedComparisonsBySize =O[atTop]
      (fun n : Nat => (n : Real) * Real.log n)
```

**Natural-language explanation.** Approved extension (expected comparisons): the `ecwp` expected comparison count of the actual uniform runner is `O(n log n)`.

**Audit focus.** Asymptotic upper bound; multiplicative constants and a finite prefix are hidden. The asymptotic endpoint is stated for the canonical size-indexed observation, not as a supremum over all lists.

## Worst-case comparison branches {#complexity-worst-comparisons}

### choose_two_add — theorem

*Source:* `Complexity.lean:845`; public

```lean
theorem choose_two_add (left right : Nat) :
    (left + right).choose 2 =
      left.choose 2 + right.choose 2 + left * right
```

**Natural-language explanation.** Splitting a set cannot create more unordered pairs than the original set.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### comparison_split_quadratic_bound — theorem

*Source:* `Complexity.lean:856`; public

```lean
theorem comparison_split_quadratic_bound (n k : Nat) (hk : k < n) :
    n - 1 + k.choose 2 + (n - 1 - k).choose 2 <= n.choose 2
```

**Natural-language explanation.** One partition charge plus the two subproblem pair counts is at most `n.choose 2`.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### smallComparisonCost_eq_choose_two — theorem

*Source:* `Complexity.lean:873`; public

```lean
theorem smallComparisonCost_eq_choose_two (n : Nat) (hSmall : n <= 3) :
    smallComparisonCost n = n.choose 2
```

**Natural-language explanation.** For sizes at most three, the fixed network's comparison count equals the number of unordered pairs, `n.choose 2`.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### sortSmallProgram_joint_cost_eq — theorem

*Source:* `Complexity.lean:878`; public

```lean
theorem sortSmallProgram_joint_cost_eq [LinearOrder alpha]
    (input output : List alpha) (cost : Nat) (hSmall : input.length <= 3)
    (hMem : (output, cost) ∈
      (interpret CostModel.comparisonOnly (sortSmallProgram input)).joint.support) :
    cost = smallComparisonCost input.length
```

**Natural-language explanation.** Every branch of the fixed base-case network has its advertised comparison count.

**Audit focus.** Assumes a linear order on keys. Quantifies over supported result-cost branches. Restricted to the base-case sizes, at most three. Uses the model that charges comparisons and makes structural work free.

### quicksortContinuation_joint_cost_decompose — theorem

*Source:* `Complexity.lean:909`; public

```lean
theorem quicksortContinuation_joint_cost_decompose [LinearOrder alpha]
    (input : List alpha) (index : Fin input.length)
    (output : List alpha) (cost : Nat)
    (hMem : (output, cost) ∈
      (interpret CostModel.comparisonOnly
        (quicksortContinuation input index)).joint.support) :
    ∃ lowerOutput lowerCost upperOutput upperCost,
      (lowerOutput, lowerCost) ∈
          (quicksort (lowerSubproblem input index)).joint.support ∧
      (upperOutput, upperCost) ∈
          (quicksort (upperSubproblem input index)).joint.support ∧
      cost = input.length - 1 + lowerCost + upperCost
```

**Natural-language explanation.** A supported fixed-pivot continuation branch decomposes into its exact partition charge and the two supported recursive branch costs.

**Audit focus.** Assumes a linear order on keys. Quantifies over supported result-cost branches. Uses the model that charges comparisons and makes structural work free.

### quicksortContinuation_joint_support_of_recursive — theorem

*Source:* `Complexity.lean:954`; public

```lean
theorem quicksortContinuation_joint_support_of_recursive [LinearOrder alpha]
    (input : List alpha) (index : Fin input.length)
    (lowerOutput upperOutput : List alpha) (lowerCost upperCost : Nat)
    (hLower : (lowerOutput, lowerCost) ∈
      (quicksort (lowerSubproblem input index)).joint.support)
    (hUpper : (upperOutput, upperCost) ∈
      (quicksort (upperSubproblem input index)).joint.support) :
    (lowerOutput ++ input.get index :: upperOutput,
        input.length - 1 + lowerCost + upperCost) ∈
      (interpret CostModel.comparisonOnly
        (quicksortContinuation input index)).joint.support
```

**Natural-language explanation.** Supported recursive branches assemble into a supported fixed-pivot continuation branch, with the partition comparisons and both recursive costs added exactly.

**Audit focus.** Assumes a linear order on keys. Quantifies over supported result-cost branches. Uses the model that charges comparisons and makes structural work free.

### quicksort_joint_support_of_pivot — theorem

*Source:* `Complexity.lean:993`; public

```lean
theorem quicksort_joint_support_of_pivot [LinearOrder alpha]
    (first : alpha) (rest : List alpha)
    (index : Fin (first :: rest).length) (output : List alpha) (cost : Nat)
    (hLong : ¬(first :: rest).length <= 3)
    (hContinuation : (output, cost) ∈
      (interpret CostModel.comparisonOnly
        (quicksortContinuation (first :: rest) index)).joint.support) :
    (output, cost) ∈ (quicksort (first :: rest)).joint.support
```

**Natural-language explanation.** Every concrete pivot position has positive probability under the actual uniform runner, so a supported fixed-pivot continuation branch is also a supported full Quicksort branch.

**Audit focus.** Assumes a linear order on keys. Quantifies over supported result-cost branches. Applies only to the recursive case, size greater than three. Uses the model that charges comparisons and makes structural work free.

### quicksort_joint_cost_eq_of_length_le_three — theorem

*Source:* `Complexity.lean:1010`; public

```lean
theorem quicksort_joint_cost_eq_of_length_le_three [LinearOrder alpha]
    (input output : List alpha) (cost : Nat) (hSmall : input.length <= 3)
    (hMem : (output, cost) ∈ (quicksort input).joint.support) :
    cost = smallComparisonCost input.length
```

**Natural-language explanation.** Every supported comparison-counting branch on an input of length at most three has exactly the fixed network's cost.

**Audit focus.** Assumes a linear order on keys. Quantifies over supported result-cost branches. Restricted to the base-case sizes, at most three.

### quicksort_branch_comparisonCost_le — theorem

*Source:* `Complexity.lean:1025`; public

```lean
theorem quicksort_branch_comparisonCost_le [LinearOrder alpha]
    (input output : List alpha) (cost : Nat) (hNodup : input.Nodup)
    (hMem : (output, cost) ∈ (quicksort input).joint.support) :
    cost <= input.length.choose 2
```

**Natural-language explanation.** Approved extension (worst comparisons), upper half: every supported comparison-counting branch uses at most one comparison per unordered input pair.

**Audit focus.** Assumes a linear order on keys. Requires a duplicate-free input. Quantifies over supported result-cost branches.

### quicksort_exists_max_comparison_branch — theorem

*Source:* `Complexity.lean:1102`; public

```lean
theorem quicksort_exists_max_comparison_branch [LinearOrder alpha]
    (input : List alpha) (hNodup : input.Nodup) :
    ∃ output, (output, input.length.choose 2) ∈ (quicksort input).joint.support
```

**Natural-language explanation.** Approved extension (worst comparisons), lower half: repeatedly selecting the minimum-rank pivot gives a supported branch that compares every unordered pair exactly once.

**Audit focus.** Assumes a linear order on keys. Requires a duplicate-free input. Quantifies over supported result-cost branches.

### worstComparisonCost — def

*Source:* `Complexity.lean:1168`; public

```lean
noncomputable def worstComparisonCost [LinearOrder alpha] (input : List alpha) : Nat
```

**Natural-language explanation.** The greatest supported comparison cost for a fixed input, searched under the proved cap.

**Audit focus.** Assumes a linear order on keys. The search cap is `input.length.choose 2`; the exactness theorem needs `input.Nodup`.

### worstComparisonCost_eq_choose — theorem

*Source:* `Complexity.lean:1175`; public

```lean
theorem worstComparisonCost_eq_choose [LinearOrder alpha]
    (input : List alpha) (hNodup : input.Nodup) :
    worstComparisonCost input = input.length.choose 2
```

**Natural-language explanation.** On distinct inputs the greatest supported comparison cost is exactly `n.choose 2`.

**Audit focus.** Assumes a linear order on keys. Requires a duplicate-free input.

### worstComparisonCost_isMaximum — theorem

*Source:* `Complexity.lean:1184`; public

```lean
theorem worstComparisonCost_isMaximum [LinearOrder alpha]
    (input : List alpha) (hNodup : input.Nodup) :
    (∃ output,
      (output, worstComparisonCost input) ∈ (quicksort input).joint.support) ∧
    ∀ output cost, (output, cost) ∈ (quicksort input).joint.support →
      cost ≤ worstComparisonCost input
```

**Natural-language explanation.** The comparison-cost maximum is attained and bounds every supported branch.

**Audit focus.** Assumes a linear order on keys. Requires a duplicate-free input. Quantifies over supported result-cost branches.

### worstComparisonsBySize — def

*Source:* `Complexity.lean:1196`; public

```lean
noncomputable def worstComparisonsBySize (n : Nat) : Nat
```

**Natural-language explanation.** The worst supported comparison cost on the canonical distinct input of size `n`.

**Audit focus.** This is the worst supported branch for `List.range n`, not a maximum over all value lists. The exact comparison theorem shows the same value for every duplicate-free input.

### worstComparisonsBySize_eq_choose — theorem

*Source:* `Complexity.lean:1199`; public; attributes: simp

```lean
@[simp] theorem worstComparisonsBySize_eq_choose (n : Nat) :
    worstComparisonsBySize n = n.choose 2
```

**Natural-language explanation.** The worst supported comparison count on `List.range n` is exactly `n.choose 2`.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### worstComparisonsBySize_isTheta — theorem

*Source:* `Complexity.lean:1205`; public

```lean
theorem worstComparisonsBySize_isTheta :
    (fun n : Nat => (worstComparisonsBySize n : Real)) =Θ[atTop]
      (fun n : Nat => (n ^ 2 : Real))
```

**Natural-language explanation.** Approved extension: the actual worst supported comparison count is `Θ(n²)`.

**Audit focus.** Asymptotic two-sided bound; multiplicative constants and a finite prefix are hidden. This concerns worst supported comparison branches, not expected cost or wall-clock running time.

## Textbook running-time model {#complexity-textbook-model}

### textbookQuicksort — def

*Source:* `Complexity.lean:1213`; public

```lean
def textbookQuicksort [LinearOrder alpha] (input : List alpha) :
    RandCostM Nat (List alpha)
```

**Natural-language explanation.** The same free Quicksort program interpreted with the approved unit linear textbook model.

**Audit focus.** Assumes a linear order on keys. Uses the abstract unit textbook cost model, not wall-clock time. This runner uses the same free program with an abstract unit linear cost model; it is not Lean evaluator time or a concrete machine model.

### interpretWith_compareLE_textbookModel — theorem

*Source:* `Complexity.lean:1217`; public; attributes: simp

```lean
@[simp] theorem interpretWith_compareLE_textbookModel [LinearOrder alpha]
    (left right : alpha) :
    interpretWith SemanticBackend.uniformLinearOrder CostModel.textbookModel
        (compareLE left right) =
      RandCostM.deterministic (ULift.up (decide (left <= right))) 1
```

**Natural-language explanation.** Under the unit textbook model, one truthful comparison is deterministic and costs one.

**Audit focus.** Assumes a linear order on keys. Uses the abstract unit textbook cost model, not wall-clock time.

### interpretWith_markBaseCase_textbookModel — theorem

*Source:* `Complexity.lean:1229`; public; attributes: simp

```lean
@[simp] theorem interpretWith_markBaseCase_textbookModel
    (backend : SemanticBackend alpha) (size : Nat) :
    interpretWith backend CostModel.textbookModel (markBaseCase size) =
      RandCostM.deterministic PUnit.unit 1
```

**Natural-language explanation.** Under the unit textbook model, a base-case marker deterministically returns unit and costs one.

**Audit focus.** Uses the abstract unit textbook cost model, not wall-clock time.

### interpret_partitionProgram_textbookModel — theorem

*Source:* `Complexity.lean:1241`; public

```lean
theorem interpret_partitionProgram_textbookModel [LinearOrder alpha]
    (pivot : alpha) (input : List alpha) :
    interpret CostModel.textbookModel (partitionProgram pivot input) =
      RandCostM.deterministic (linearPartition pivot input) input.length
```

**Natural-language explanation.** Under the approved textbook model, partitioning still costs exactly one unit per key comparison; the separately charged splitter frame is emitted by the pivot operation.

**Audit focus.** Assumes a linear order on keys. Uses the abstract unit textbook cost model, not wall-clock time.

### expectedCost_sortSmallProgram_textbookModel — theorem

*Source:* `Complexity.lean:1262`; public

```lean
theorem expectedCost_sortSmallProgram_textbookModel [LinearOrder alpha]
    (input : List alpha) (hLength : input.length <= 3) :
    (interpret CostModel.textbookModel (sortSmallProgram input)).expectedCost =
      1 + smallComparisonCost input.length
```

**Natural-language explanation.** The constant-size sorting network costs one textbook base-frame unit in addition to its exact element-comparison count.

**Audit focus.** Assumes a linear order on keys. Restricted to the base-case sizes, at most three. Uses the abstract unit textbook cost model, not wall-clock time.

### interpretWith_choosePivotIndex_textbookModel — theorem

*Source:* `Complexity.lean:1296`; public; attributes: simp

```lean
@[simp] theorem interpretWith_choosePivotIndex_textbookModel [LinearOrder alpha]
    (tailLength : Nat) :
    interpretWith (SemanticBackend.uniformLinearOrder (alpha := alpha))
        (CostModel.textbookModel (alpha := alpha))
        (choosePivotIndex tailLength) =
      RandCostM.sampleAtCost
        (PMF.uniformOfFintype (ULift (Fin (tailLength + 1))))
        (tailLength + 1)
```

**Natural-language explanation.** Under the unit textbook model, a uniform pivot is sampled and charged the full current subproblem size `tailLength + 1`.

**Audit focus.** Assumes a linear order on keys. Uses the abstract unit textbook cost model, not wall-clock time.

### expectedCost_sampleAtCost_nat — theorem

*Source:* `Complexity.lean:1309`; public; attributes: simp

```lean
@[simp] theorem expectedCost_sampleAtCost_nat (distribution : PMF beta) (cost : Nat) :
    (RandCostM.sampleAtCost distribution cost : RandCostM Nat beta).expectedCost = cost
```

**Natural-language explanation.** Sampling from any distribution at a fixed natural-number charge has expected cost exactly that charge.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### expectedCost_textbookQuicksortContinuation — theorem

*Source:* `Complexity.lean:1315`; public

```lean
theorem expectedCost_textbookQuicksortContinuation [LinearOrder alpha]
    (input : List alpha) (index : Fin input.length) :
    (interpret CostModel.textbookModel
      (quicksortContinuation input index)).expectedCost =
      ((input.length - 1 : Nat) : ENNReal) +
        (textbookQuicksort (lowerSubproblem input index)).expectedCost +
        (textbookQuicksort (upperSubproblem input index)).expectedCost
```

**Natural-language explanation.** A fixed-pivot textbook continuation has the same partition comparison charge as the comparison-only model, followed by the two textbook-cost recursive calls.

**Audit focus.** Assumes a linear order on keys. Uses the abstract unit textbook cost model, not wall-clock time.

### expectedCost_textbookQuicksort_step — theorem

*Source:* `Complexity.lean:1335`; public

```lean
theorem expectedCost_textbookQuicksort_step [LinearOrder alpha]
    (first : alpha) (rest : List alpha)
    (hLong : ¬(first :: rest).length <= 3) :
    (textbookQuicksort (first :: rest)).expectedCost =
      (((first :: rest).length : Nat) : ENNReal) +
        (((first :: rest).length : Nat) : ENNReal)⁻¹ *
          ∑ index : Fin (first :: rest).length,
            (interpret CostModel.textbookModel
              (quicksortContinuation (first :: rest) index)).expectedCost
```

**Natural-language explanation.** The actual uniform textbook runner, unfolded for one recursive step. The leading `n` is the approved size-linear splitter-frame charge.

**Audit focus.** Assumes a linear order on keys. Applies only to the recursive case, size greater than three. Uses the abstract unit textbook cost model, not wall-clock time.

### expectedCost_textbookQuicksort_recurrence — theorem

*Source:* `Complexity.lean:1356`; public

```lean
theorem expectedCost_textbookQuicksort_recurrence [LinearOrder alpha]
    (first : alpha) (rest : List alpha)
    (hLong : ¬(first :: rest).length <= 3) :
    (textbookQuicksort (first :: rest)).expectedCost =
      (((first :: rest).length : Nat) : ENNReal) +
        (((first :: rest).length : Nat) : ENNReal)⁻¹ *
          ∑ index : Fin (first :: rest).length,
            ((((first :: rest).length - 1 : Nat) : ENNReal) +
              (textbookQuicksort
                (lowerSubproblem (alpha := alpha) (first :: rest)
                  (index : Fin (first :: rest).length))).expectedCost +
              (textbookQuicksort
                (upperSubproblem (alpha := alpha) (first :: rest)
                  (index : Fin (first :: rest).length))).expectedCost)
```

**Natural-language explanation.** Exact expected textbook-running-time recurrence derived from the interpreted free program.

**Audit focus.** Assumes a linear order on keys. Applies only to the recursive case, size greater than three. Uses the abstract unit textbook cost model, not wall-clock time.

### expectedCost_textbookQuicksort_of_length_le_three — theorem

*Source:* `Complexity.lean:1373`; public

```lean
theorem expectedCost_textbookQuicksort_of_length_le_three [LinearOrder alpha]
    (input : List alpha) (hSmall : input.length <= 3) :
    (textbookQuicksort input).expectedCost =
      1 + smallComparisonCost input.length
```

**Natural-language explanation.** For inputs of length at most three, expected textbook cost is one base-case unit plus the exact sorting-network comparisons.

**Audit focus.** Assumes a linear order on keys. Restricted to the base-case sizes, at most three. Uses the abstract unit textbook cost model, not wall-clock time.

### subproblem_lengths_add — theorem

*Source:* `Complexity.lean:1386`; public

```lean
theorem subproblem_lengths_add [LinearOrder alpha]
    (input : List alpha) (index : Fin input.length) :
    (lowerSubproblem input index).length +
      (upperSubproblem input index).length = input.length - 1
```

**Natural-language explanation.** The lower and upper recursive subproblem lengths add to the original length minus the removed pivot.

**Audit focus.** Assumes a linear order on keys.

### lowerSubproblem_length_lt — theorem

*Source:* `Complexity.lean:1397`; public

```lean
theorem lowerSubproblem_length_lt [LinearOrder alpha]
    (input : List alpha) (index : Fin input.length) :
    (lowerSubproblem input index).length < input.length
```

**Natural-language explanation.** The lower recursive subproblem is strictly shorter than the nonempty input.

**Audit focus.** Assumes a linear order on keys.

### upperSubproblem_length_lt — theorem

*Source:* `Complexity.lean:1404`; public

```lean
theorem upperSubproblem_length_lt [LinearOrder alpha]
    (input : List alpha) (index : Fin input.length) :
    (upperSubproblem input index).length < input.length
```

**Natural-language explanation.** The upper recursive subproblem is strictly shorter than the nonempty input.

**Audit focus.** Assumes a linear order on keys.

### textbook_branch_le — theorem

*Source:* `Complexity.lean:1411`; private

```lean
private theorem textbook_branch_le
    (n lowerSize upperSize : Nat)
    (tLower tUpper cLower cUpper : ENNReal)
    (hn : 0 < n) (hSizes : lowerSize + upperSize = n - 1)
    (hLower : tLower <= 2 * cLower + 2 * (lowerSize : ENNReal) + 1)
    (hUpper : tUpper <= 2 * cUpper + 2 * (upperSize : ENNReal) + 1) :
    (((n - 1 : Nat) : ENNReal) + tLower) + tUpper <=
      2 * ((((n - 1 : Nat) : ENNReal) + cLower) + cUpper) +
        ((n : ENNReal) + 1)
```

**Natural-language explanation.** Private arithmetic helper: if each recursive textbook cost is bounded by twice its comparison cost plus a linear term, then the combined branch satisfies the corresponding parent-size bound.

**Audit focus.** Private proof helper; not part of the public API.

### textbookQuicksort_expectedCost_le — theorem

*Source:* `Complexity.lean:1438`; public

```lean
theorem textbookQuicksort_expectedCost_le [LinearOrder alpha]
    (input : List alpha) :
    (textbookQuicksort input).expectedCost <=
      2 * (quicksort input).expectedCost +
        2 * (input.length : ENNReal) + 1
```

**Natural-language explanation.** Kleinberg--Tardos, pp. 732 and 734 (unnumbered expected-running-time claim): under the approved unit linear textbook model, expected running time is controlled by twice the actual comparison expectation plus a linear term.

**Audit focus.** Assumes a linear order on keys. Uses the abstract unit textbook cost model, not wall-clock time. The result couples textbook expected cost to actual comparison expectation plus a linear term; it is not an exact recurrence solution.

### textbookQuicksort_ecwp_le — theorem

*Source:* `Complexity.lean:1548`; public

```lean
theorem textbookQuicksort_ecwp_le [LinearOrder alpha] (input : List alpha) :
    RandCostM.ecwp (textbookQuicksort input) (fun _ => 0) <=
      2 * (quicksort input).expectedCost +
        2 * (input.length : ENNReal) + 1
```

**Natural-language explanation.** The expected-cost weakest preexpectation for the textbook runner obeys the same bound.

**Audit focus.** Assumes a linear order on keys. Uses the abstract unit textbook cost model, not wall-clock time.

### textbookModel_isBoundedBy — theorem

*Source:* `Complexity.lean:1556`; public

```lean
theorem textbookModel_isBoundedBy :
    (CostModel.textbookModel (alpha := alpha)).IsBoundedBy
      (CostModel.linearTextbookBounds 1 1 1)
```

**Natural-language explanation.** The unit textbook model is an instance of the implementation handoff's approved bounded linear model family.

**Audit focus.** Uses the abstract unit textbook cost model, not wall-clock time.

### expectedTextbookRuntimeBySize — def

*Source:* `Complexity.lean:1563`; public

```lean
def expectedTextbookRuntimeBySize (n : Nat) : Real
```

**Natural-language explanation.** Size-indexed real observation of the textbook runner on canonical distinct inputs.

**Audit focus.** This expectation is measured on `List.range n` under the abstract textbook model.

### expectedTextbookRuntimeEnvelope — def

*Source:* `Complexity.lean:1568`; public

```lean
def expectedTextbookRuntimeEnvelope (n : Nat) : Real
```

**Natural-language explanation.** Real envelope obtained by transferring the comparison bound through the textbook-cost coupling theorem.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### expectedTextbookRuntimeBySize_nonneg — theorem

*Source:* `Complexity.lean:1571`; public

```lean
theorem expectedTextbookRuntimeBySize_nonneg (n : Nat) :
    0 <= expectedTextbookRuntimeBySize n
```

**Natural-language explanation.** The size-indexed expected textbook runtime on `List.range n` is nonnegative.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### expectedTextbookRuntimeEnvelope_nonneg — theorem

*Source:* `Complexity.lean:1575`; public

```lean
theorem expectedTextbookRuntimeEnvelope_nonneg (n : Nat) :
    0 <= expectedTextbookRuntimeEnvelope n
```

**Natural-language explanation.** The real-valued textbook runtime envelope is nonnegative.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### expectedTextbookRuntimeBySize_le — theorem

*Source:* `Complexity.lean:1581`; public

```lean
theorem expectedTextbookRuntimeBySize_le (n : Nat) :
    expectedTextbookRuntimeBySize n <= expectedTextbookRuntimeEnvelope n
```

**Natural-language explanation.** The expected textbook cost on `List.range n` is at most the transferred runtime envelope.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### expectedTextbookRuntimeEnvelope_isBigO — theorem

*Source:* `Complexity.lean:1625`; public

```lean
theorem expectedTextbookRuntimeEnvelope_isBigO :
    expectedTextbookRuntimeEnvelope =O[atTop] nLogN
```

**Natural-language explanation.** The transferred textbook runtime envelope is asymptotically bounded by the chosen `n(1 + log n)` benchmark.

**Audit focus.** Asymptotic upper bound; multiplicative constants and a finite prefix are hidden.

### expectedTextbookRuntimeBySize_isBigO — theorem

*Source:* `Complexity.lean:1659`; public

```lean
theorem expectedTextbookRuntimeBySize_isBigO :
    expectedTextbookRuntimeBySize =O[atTop]
      (fun n : Nat => (n : Real) * Real.log n)
```

**Natural-language explanation.** Kleinberg--Tardos, pp. 732 and 734 (unnumbered): the expected running time of the actual uniform-pivot free program, interpreted by the approved textbook model, is `O(n log n)`.

**Audit focus.** Asymptotic upper bound; multiplicative constants and a finite prefix are hidden. The theorem establishes `O(n log n)` for the size-indexed canonical distinct inputs under the approved abstract cost model.

## Worst-case textbook running time {#complexity-worst-textbook}

### joint_support_sampleAtCost_cost_eq — theorem

*Source:* `Complexity.lean:1673`; public

```lean
theorem joint_support_sampleAtCost_cost_eq (distribution : PMF beta)
    (chargedCost : Nat) (value : beta) (cost : Nat)
    (hMem : (value, cost) ∈
      (RandCostM.sampleAtCost distribution chargedCost :
        RandCostM Nat beta).joint.support) :
    cost = chargedCost
```

**Natural-language explanation.** Kleinberg--Tardos, pp. 732 and 734 (unnumbered): the expected running time of the actual uniform-pivot free program, interpreted by the approved textbook model, is `O(n log n)`. -/ theorem expectedTextbookRuntimeBySize_isBigO : expectedTextbookRuntimeBySize =O[atTop] (fun n : Nat => (n : Real) * Real.log n) := by have hToEnvelope : expectedTextbookRuntimeBySize =O[atTop] expectedTextbookRuntimeEnvelope := by refine IsBigO.of_bound 1 (Filter.Eventually.of_forall fun n => ?_) rw [Real.norm_eq_abs, abs_of_nonneg (expectedTextbookRuntimeBySize_nonneg n)] rw [Real.norm_eq_abs, abs_of_nonneg (expectedTextbookRuntimeEnvelope_nonneg n)] simpa using expectedTextbookRuntimeBySize_le n exact (hToEnvelope.trans expectedTextbookRuntimeEnvelope_isBigO).trans nLogN_isBigO_mul_log /-! ## Worst-case textbook running time

**Audit focus.** Quantifies over supported result-cost branches.

### mem_joint_support_sampleAtCost_of_mem — theorem

*Source:* `Complexity.lean:1684`; public

```lean
theorem mem_joint_support_sampleAtCost_of_mem (distribution : PMF beta)
    (chargedCost : Nat) (value : beta) (hValue : value ∈ distribution.support) :
    (value, chargedCost) ∈
      (RandCostM.sampleAtCost distribution chargedCost :
        RandCostM Nat beta).joint.support
```

**Natural-language explanation.** Every supported sampled value appears in joint support paired with the fixed charged cost.

**Audit focus.** Quantifies over supported result-cost branches.

### sortSmallProgram_joint_cost_textbookModel — theorem

*Source:* `Complexity.lean:1693`; public

```lean
theorem sortSmallProgram_joint_cost_textbookModel [LinearOrder alpha]
    (input output : List alpha) (cost : Nat) (hSmall : input.length <= 3)
    (hMem : (output, cost) ∈
      (interpret CostModel.textbookModel (sortSmallProgram input)).joint.support) :
    cost = 1 + smallComparisonCost input.length
```

**Natural-language explanation.** Every supported branch of the small sorting network under the unit textbook model costs one base-case unit plus its exact comparison count.

**Audit focus.** Assumes a linear order on keys. Quantifies over supported result-cost branches. Restricted to the base-case sizes, at most three. Uses the abstract unit textbook cost model, not wall-clock time.

### textbookQuicksort_joint_cost_eq_of_length_le_three — theorem

*Source:* `Complexity.lean:1726`; public

```lean
theorem textbookQuicksort_joint_cost_eq_of_length_le_three [LinearOrder alpha]
    (input output : List alpha) (cost : Nat) (hSmall : input.length <= 3)
    (hMem : (output, cost) ∈ (textbookQuicksort input).joint.support) :
    cost = 1 + smallComparisonCost input.length
```

**Natural-language explanation.** Every supported textbook-model Quicksort branch of size at most three has cost one plus the fixed network comparison count.

**Audit focus.** Assumes a linear order on keys. Quantifies over supported result-cost branches. Restricted to the base-case sizes, at most three. Uses the abstract unit textbook cost model, not wall-clock time.

### textbookQuicksortContinuation_joint_cost_decompose — theorem

*Source:* `Complexity.lean:1740`; public

```lean
theorem textbookQuicksortContinuation_joint_cost_decompose [LinearOrder alpha]
    (input : List alpha) (index : Fin input.length)
    (output : List alpha) (cost : Nat)
    (hMem : (output, cost) ∈
      (interpret CostModel.textbookModel
        (quicksortContinuation input index)).joint.support) :
    ∃ lowerOutput lowerCost upperOutput upperCost,
      (lowerOutput, lowerCost) ∈
          (textbookQuicksort (lowerSubproblem input index)).joint.support ∧
      (upperOutput, upperCost) ∈
          (textbookQuicksort (upperSubproblem input index)).joint.support ∧
      cost = input.length - 1 + lowerCost + upperCost
```

**Natural-language explanation.** A supported fixed-pivot textbook continuation decomposes into supported lower and upper recursive branches, with total continuation cost equal to partition comparisons plus both recursive costs.

**Audit focus.** Assumes a linear order on keys. Quantifies over supported result-cost branches. Uses the abstract unit textbook cost model, not wall-clock time.

### textbookQuicksortContinuation_joint_support_of_recursive — theorem

*Source:* `Complexity.lean:1783`; public

```lean
theorem textbookQuicksortContinuation_joint_support_of_recursive [LinearOrder alpha]
    (input : List alpha) (index : Fin input.length)
    (lowerOutput upperOutput : List alpha) (lowerCost upperCost : Nat)
    (hLower : (lowerOutput, lowerCost) ∈
      (textbookQuicksort (lowerSubproblem input index)).joint.support)
    (hUpper : (upperOutput, upperCost) ∈
      (textbookQuicksort (upperSubproblem input index)).joint.support) :
    (lowerOutput ++ input.get index :: upperOutput,
        input.length - 1 + lowerCost + upperCost) ∈
      (interpret CostModel.textbookModel
        (quicksortContinuation input index)).joint.support
```

**Natural-language explanation.** Any supported lower and upper textbook branches can be assembled into a supported fixed-pivot continuation whose cost is their costs plus the partition comparisons.

**Audit focus.** Assumes a linear order on keys. Quantifies over supported result-cost branches. Uses the abstract unit textbook cost model, not wall-clock time.

### textbookQuicksort_joint_support_of_pivot — theorem

*Source:* `Complexity.lean:1820`; public

```lean
theorem textbookQuicksort_joint_support_of_pivot [LinearOrder alpha]
    (first : alpha) (rest : List alpha)
    (index : Fin (first :: rest).length) (output : List alpha)
    (continuationCost : Nat) (hLong : ¬(first :: rest).length <= 3)
    (hContinuation : (output, continuationCost) ∈
      (interpret CostModel.textbookModel
        (quicksortContinuation (first :: rest) index)).joint.support) :
    (output, (first :: rest).length + continuationCost) ∈
      (textbookQuicksort (first :: rest)).joint.support
```

**Natural-language explanation.** For a non-base input, any supported fixed-pivot continuation becomes a supported full textbook branch after adding the size-linear pivot-frame charge.

**Audit focus.** Assumes a linear order on keys. Quantifies over supported result-cost branches. Applies only to the recursive case, size greater than three. Uses the abstract unit textbook cost model, not wall-clock time.

### textbookRuntimeEnvelopeNat — def

*Source:* `Complexity.lean:1839`; public

```lean
def textbookRuntimeEnvelopeNat (n : Nat) : Nat
```

**Natural-language explanation.** A Nat-valued quadratic cap for every supported textbook-cost branch.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### textbook_split_quadratic_bound — theorem

*Source:* `Complexity.lean:1842`; public

```lean
theorem textbook_split_quadratic_bound (n lowerSize upperSize : Nat)
    (hPositive : 0 < n) (hSizes : lowerSize + upperSize = n - 1) :
    n + (n - 1) + textbookRuntimeEnvelopeNat lowerSize +
        textbookRuntimeEnvelopeNat upperSize <=
      textbookRuntimeEnvelopeNat n
```

**Natural-language explanation.** If two subproblem sizes sum to `n - 1`, the parent frame, partition, and two quadratic envelopes fit under the quadratic envelope at size `n`.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### textbookQuicksort_branch_cost_le — theorem

*Source:* `Complexity.lean:1855`; public

```lean
theorem textbookQuicksort_branch_cost_le [LinearOrder alpha]
    (input output : List alpha) (cost : Nat)
    (hMem : (output, cost) ∈ (textbookQuicksort input).joint.support) :
    cost <= textbookRuntimeEnvelopeNat input.length
```

**Natural-language explanation.** Every supported branch of the approved textbook model is bounded by a quadratic envelope.

**Audit focus.** Assumes a linear order on keys. Quantifies over supported result-cost branches. Uses the abstract unit textbook cost model, not wall-clock time.

### textbookQuicksort_exists_quadratic_branch — theorem

*Source:* `Complexity.lean:1912`; public

```lean
theorem textbookQuicksort_exists_quadratic_branch [LinearOrder alpha]
    (input : List alpha) (hNodup : input.Nodup) :
    ∃ output cost,
      (output, cost) ∈ (textbookQuicksort input).joint.support ∧
      input.length.choose 2 ≤ cost
```

**Natural-language explanation.** Repeated minimum-rank pivots give a supported textbook-model branch with quadratic cost.

**Audit focus.** Assumes a linear order on keys. Requires a duplicate-free input. Quantifies over supported result-cost branches. Uses the abstract unit textbook cost model, not wall-clock time.

### IsTextbookBranchCost — def

*Source:* `Complexity.lean:1985`; public

```lean
def IsTextbookBranchCost (n cost : Nat) : Prop
```

**Natural-language explanation.** A cost belongs to some supported textbook-model branch on a distinct Nat input of size `n`.

**Audit focus.** The maximum ranges over all duplicate-free `List Nat` inputs of length `n`, not over arbitrary ordered key types.

### isTextbookBranchCost_le — theorem

*Source:* `Complexity.lean:1990`; public

```lean
theorem isTextbookBranchCost_le {n cost : Nat}
    (h : IsTextbookBranchCost n cost) :
    cost ≤ textbookRuntimeEnvelopeNat n
```

**Natural-language explanation.** Every cost represented by `IsTextbookBranchCost n cost` is bounded by the quadratic natural-number envelope at size `n`.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### exists_isTextbookBranchCost — theorem

*Source:* `Complexity.lean:1996`; public

```lean
theorem exists_isTextbookBranchCost (n : Nat) :
    ∃ cost, IsTextbookBranchCost n cost
```

**Natural-language explanation.** For every size `n`, at least one supported textbook branch cost exists, witnessed using `List.range n`.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### worstTextbookRuntimeBySize — def

*Source:* `Complexity.lean:2003`; public

```lean
noncomputable def worstTextbookRuntimeBySize (n : Nat) : Nat
```

**Natural-language explanation.** The actual maximum supported textbook-model cost over distinct Nat inputs of size `n`.

**Audit focus.** Unlike `worstComparisonsBySize`, this definition maximizes over all distinct natural-number inputs of the given length and all supported branches.

### worstTextbookRuntimeBySize_le_envelope — theorem

*Source:* `Complexity.lean:2007`; public

```lean
theorem worstTextbookRuntimeBySize_le_envelope (n : Nat) :
    worstTextbookRuntimeBySize n ≤ textbookRuntimeEnvelopeNat n
```

**Natural-language explanation.** The defined worst textbook runtime is at most the quadratic natural-number envelope.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### isTextbookBranchCost_le_worst — theorem

*Source:* `Complexity.lean:2013`; public

```lean
theorem isTextbookBranchCost_le_worst {n cost : Nat}
    (h : IsTextbookBranchCost n cost) :
    cost ≤ worstTextbookRuntimeBySize n
```

**Natural-language explanation.** Every supported textbook branch cost at size `n` is at most the defined worst runtime for that size.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### worstTextbookRuntimeBySize_isBranchCost — theorem

*Source:* `Complexity.lean:2020`; public

```lean
theorem worstTextbookRuntimeBySize_isBranchCost (n : Nat) :
    IsTextbookBranchCost n (worstTextbookRuntimeBySize n)
```

**Natural-language explanation.** The defined worst textbook runtime is actually attained by some supported branch on a duplicate-free natural-number input of size `n`.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### worstTextbookRuntimeBySize_isMaximum — theorem

*Source:* `Complexity.lean:2027`; public

```lean
theorem worstTextbookRuntimeBySize_isMaximum (n : Nat) :
    IsTextbookBranchCost n (worstTextbookRuntimeBySize n) ∧
      ∀ cost, IsTextbookBranchCost n cost →
        cost ≤ worstTextbookRuntimeBySize n
```

**Natural-language explanation.** The defined worst textbook runtime is both attained and an upper bound for every eligible branch cost at that size.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### choose_two_le_worstTextbookRuntimeBySize — theorem

*Source:* `Complexity.lean:2034`; public

```lean
theorem choose_two_le_worstTextbookRuntimeBySize (n : Nat) :
    n.choose 2 ≤ worstTextbookRuntimeBySize n
```

**Natural-language explanation.** The worst textbook runtime is at least `n.choose 2`, via a supported quadratic-cost branch.

**Audit focus.** No extra narrowing beyond the binders and conclusion shown in the header.

### textbookRuntimeEnvelopeNat_isBigO — theorem

*Source:* `Complexity.lean:2044`; public

```lean
theorem textbookRuntimeEnvelopeNat_isBigO :
    (fun n : Nat => (textbookRuntimeEnvelopeNat n : Real)) =O[atTop]
      (fun n : Nat => (n ^ 2 : Real))
```

**Natural-language explanation.** The natural-number quadratic envelope grows in `O(n^2)` after casting to real values.

**Audit focus.** Asymptotic upper bound; multiplicative constants and a finite prefix are hidden.

### worstTextbookRuntimeBySize_isTheta — theorem

*Source:* `Complexity.lean:2060`; public

```lean
theorem worstTextbookRuntimeBySize_isTheta :
    (fun n : Nat => (worstTextbookRuntimeBySize n : Real)) =Θ[atTop]
      (fun n : Nat => (n ^ 2 : Real))
```

**Natural-language explanation.** Kleinberg--Tardos p. 732: the actual worst supported textbook-model runtime is `Θ(n²)`.

**Audit focus.** Asymptotic two-sided bound; multiplicative constants and a finite prefix are hidden. This is a worst-supported-branch theorem under the abstract textbook cost model, not a concrete implementation runtime theorem.

# Audit completion checklist {#audit-completion-checklist}

[Back to contents](#contents)

- Confirm the informal algorithm uses the same base-case threshold (`length <= 3`) and fixed small sorting network.
- Confirm the pivot is a uniformly selected list position and is removed before partitioning.
- Confirm the advertised interface is restricted to duplicate-free inputs wherever rank-based complexity is used.
- Confirm all probability claims are about the actual interpreter, not a detached recurrence.
- Confirm comparison-cost claims do not silently include structural work.
- Confirm textbook-runtime claims are understood as results for `CostModel.textbookModel`.
- Confirm `support` claims are possibility claims, not claims that all branches have equal probability.
- Confirm big-O/theta endpoints use the exact size-indexed functions shown in their headers.
- Record any mismatch as one of: missing hypothesis, stronger/weaker conclusion, wrong cost interpretation, wrong quantification domain, or unsupported textbook attribution.

# Source inventory {#source-inventory}

- `Algorithm.lean`: abstract operation signature, certified partition data, small sorting network, and the only recursive Quicksort program.
- `ResourceModel.lean`: comparison-only, scaled-comparison, and linear textbook cost assignments.
- `Interpreters.lean`: semantic and measured folds, deterministic pivot backends, and trace erasure.
- `Correctness.lean`: partition, small-network, join, free-program, and interpreted-run correctness.
- `Complexity.lean`: run-derived recurrences, harmonic expected-cost bounds, and attained worst-branch bounds.

