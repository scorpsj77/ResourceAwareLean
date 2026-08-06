# Shared Graph-Traversal Model

This directory defines one reusable operation language and one reusable execution model for graph
traversals. BFS and DFS are programs over that language; neither algorithm defines a free-monad
interpreter.

## Public structure

```text
Language.lean      traversal operations, typed responses, and request helpers
Model.lean         state backends, resource choices, transitions, and measurements
Specification.lean reusable reachability and traversal-tree targets
```

Events use `ResourceAware.Program.Event` directly. Operation traces, weighted costs, and
cost-independence theorems also come directly from `ResourceAware.Program`; there are no
family-specific observation or operation-profile wrappers.

## Execution pipeline

```text
BFS or DFS : GraphTraversal.Program Vertex α
                      |
                      v
GraphTraversal.Model.semantics
  graph + visited + level + tree backends
                      |
         +------------+------------+
         |                         |
         v                         v
Program.Semantics.eval       Program.run
pure result and state        ordered Event trace
                                      |
                                      v
                         exact cost / operation profile
```

The algorithm requests operations such as `neighbors v`, `isVisited v`, or `addTreeEdge u v`.
`Model.semantics` gives those requests their state transitions. `Model.costModel` independently
assigns a measurement to each executed transition. The generic interpreter in
`ResourceAware.Program.Interpreter` performs the free-monad fold and records the events.

This separation provides three useful invariants:

- changing costs does not change responses or final state;
- erasing measurements yields the same ordered operation trace;
- a pointwise bound for each primitive operation lifts to a bound for the whole program.

`CostModel.measure` can inspect the operation, state before execution, response, and state after
execution. Costs can therefore depend on the graph representation, current visited structure,
operand, result, or state transition; they are not restricted to unit ticks.

## Shared operation language

`Language.lean` includes requests for:

```text
loop checks
clearing traversal state
neighbor access
visited lookup and updates
level output
tree-edge output
```

The response type depends on the operation: neighbor access returns a vertex list, visited lookup
returns a Boolean, and update requests return `PUnit`. The algorithm sees these typed answers but
does not see the chosen representation or cost.

## Representation choices

Graph representation costs come from `ResourceAware.Graph.ResourceModel`. For example, the same
program can use adjacency-list or adjacency-matrix neighbor access. Traversal working state is
selected separately:

- Boolean-table visited state;
- discarded or recorded levels;
- discarded or edge-list traversal trees.

The family model combines these choices in a product state. A new traversal can reuse this model
whenever its abstract program uses the shared operation signature.

## BFS and DFS

The textbook developments are:

```text
TextbookAlgorithms/KleinbergTardos/Chapter03/BFS/
TextbookAlgorithms/KleinbergTardos/Chapter03/DFS/
```

In each directory:

```text
Algorithm.lean       source-shaped abstract program
ResourceModel.lean   thin runner plus algorithm-specific fuel and space choices
Correctness.lean     semantic theorems
Complexity.lean      exact, aggregate, and asymptotic resource bounds
```

Executable examples live in `Examples/BFS.lean` and `Examples/DFS.lean`.

BFS and DFS differ in control flow and their fuel/space arguments, but both call
`GraphTraversal.Model.interpret`. This is the key simplification: the family owns the execution
model; an algorithm directory only supplies its program and selected resources.

## Extending the model

To add another traversal over the current requests:

1. define the program in the algorithm's `Algorithm.lean`;
2. select graph and traversal backends in `ResourceModel.lean`;
3. call `GraphTraversal.Model.interpret` or `interpretFrom`;
4. prove an operation-profile bound, then lift the primitive model bounds.

Only extend `Language.lean` and `Model.lean` when the new operation is genuinely reusable across graph
algorithms. If a request is specific to one algorithm, its signature can be handled by that
algorithm's model while still using the generic `ResourceAware.Program` interpreter.
