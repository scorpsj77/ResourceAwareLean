# Generic Resource-Aware Programs

`ResourceAware.Program` is the common layer that replaces algorithm-specific free-monad
interpreters. 

## Modules

```text
Model.lean            operation signatures, free programs, and pure semantics
Instrumentation.lean events and transition-sensitive cost models
Interpreter.lean     the single operation-only and measured fold
Cost.lean            trace costs, reweighting, and primitive-bound lifting
RandCostM.lean       branch-sensitive probabilistic cost semantics
Randomized.lean      generic PMF and RandCostM folds for free programs
```

## Separation of concerns

An algorithm is a `Program.Free signature α`. It fixes control flow and abstract requests, but not
their representation or cost.

```lean
semantics : Program.Semantics signature State
model     : Program.CostModel signature State Measurement
program   : Program.Free signature α
```

`Semantics.step` computes a response and next state. `CostModel.measure` observes the operation,
state before execution, response, and state after execution. The generic runner combines them:

```lean
Program.runFrom semantics model program state
```

and returns a `TraceM` whose events pair every executed operation with its measurement.

## Why both TraceM and TraceStateM remain

`TraceStateM` is the internal target of interpretation because operations may update a heap,
visited map, tree, or other backend. Running it produces `TraceM`, which exposes the final result
and the ordered, immutable event log used by proofs. The generic program layer therefore removes
duplicated folds without removing either effect.

The same program supports:

```text
Semantics.eval          pure result and final state
runOperations           cost-independent ordered operations
run                     ordered operations plus selected measurements
toTimeM                 compatibility projection to a numeric TimeM cost
```

## Cost flexibility

The measurement need not be a unit tick and need not depend only on the operation name. It may be
operand-, state-, response-, or transition-sensitive. A model can record natural-number time,
structured measurements, or another additive resource type. For natural-number traces,
`exactCost` sums the stored measurements.

Erasing measurements recovers the operation trace. That trace can be reweighted under another
charge function without rerunning or reproving the algorithm's control-flow analysis.

## Proof reuse

The generic layer proves once that instrumentation preserves results and that changing only the
cost model preserves the erased trace. `Cost.lean` also lifts a pointwise primitive bound

```text
measurement(operation, transition) <= charge(operation)
```

to every event of every free program, and hence to a whole-program exact-cost bound. Algorithm
modules are left with the meaningful parts: semantic correctness, cost-independent trace
arguments, and the recurrence or graph argument connecting those traces to complexity.

## Adding an algorithm

1. Reuse or define an operation signature.
2. Write the source-shaped free program.
3. Supply `Semantics` and one or more `CostModel` values in the family or algorithm model.
4. Use `Program.run`, `runFrom`, or their operation-only variants.
5. Prove primitive bounds and a cost-independent operation-profile theorem.

Do not define a new recursive `liftM` fold merely to obtain a different cost model. New model
choices should be values passed to the generic runner.
