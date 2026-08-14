# Kleinberg Breadth-First Search

This case study follows Kleinberg and Tardos's layer-based BFS.

```text
Algorithm.lean       abstract layer-based program
ResourceModel.lean   shared-model runner, fuel, and storage choices
Correctness.lean     certified BFS-tree and bipartiteness results
Complexity.lean      adjacency-list and adjacency-matrix time bounds
```

Executable toy graph and trace checks live in `Examples/Algorithms/BFS.lean`.

The program reuses the operations, backends, operation profiles, and semantics in
`GraphTraversal.Model`. The generic free-monad fold lives in `ResourceAware.Program`, while the
thin `KleinbergBFS.Interpreter.run` wrapper is colocated with the BFS resource choices in
`ResourceModel.lean`. `Correctness.lean` proves exact reachability of the completed Boolean-table
run. It separately constructs a noncomputable shortest-path-tree certificate for finite connected
graphs; it does not prove that the run's emitted edge list and level table form that tree.
`Complexity.lean` proves one cost-independent BFS operation profile, then reuses it for arbitrary
exact costs satisfying explicit upper bounds and for the traditional unit-cost corollaries. Run
the executable example from the repository root with:

```sh
lake env lean Examples/Algorithms/BFS.lean
```
