# Resource-Aware Infrastructure

This tree contains reusable machinery for algorithms whose semantics and resource usage are
studied together. It is independent of any one textbook presentation.

```text
Effects/                    ordered `TraceM` and stateful `TraceStateM`
Program/                    generic model, instrumentation, interpreter, costs, and bounds
Foundations/Graph/          graph interfaces, adapters, and resource models
Foundations/PriorityQueue/  heap-based priority-queue implementation and proofs
Algorithms/GraphTraversal/  shared traversal language, model, and specification
Algorithms/ShortestPaths/   shared shortest-path specifications
Algorithms/Sorting/         shared comparison model and specification
```

The central design is:

```text
abstract free program
       + semantic transitions
       + independently selected cost model
       = pure execution, operation trace, or measured execution
```

`Program/Interpreter.lean` contains the single free-monad fold. An algorithm family supplies a
`Program.Semantics` value and one or more `Program.CostModel` values; individual algorithms provide
programs and thin runners. `TraceM` and `TraceStateM` remain the observation mechanisms, but they
are no longer reimplemented in every case-study interpreter.

The layer may import `Cslib`, but `Cslib` must not import it. Textbook formalizations consume this
layer from `TextbookAlgorithms` and retain their source-specific algorithms and theorem statements
there.

`Foundations/Graph/Graph.lean` is the local experimental copy of the graph API proposed in CSLib
PR #503. `GraphAdapters.lean` isolates that concrete API from the stable `Interface.lean`; changes
to the candidate definitions should be absorbed by the adapters rather than propagated into
algorithms.

See `Program/README.md` for the generic interface and the proof-reuse guarantees.
