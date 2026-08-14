# Kleinberg Depth-First Search

This case study follows Kleinberg and Tardos's iterative stack-based DFS.

```text
Algorithm.lean       abstract stack-based program
ResourceModel.lean   shared-model runner, stack-pop bound, and storage choices
Correctness.lean     reachability and recursive DFS-tree correctness
Complexity.lean      adjacency-list and adjacency-matrix time bounds
```

Executable toy graph and trace checks live in `Examples/Algorithms/DFS.lean`.

`ResourceModel.lean` calls `GraphTraversal.Model.interpret`; it does not define a DFS-specific
free-monad fold. `Correctness.lean` proves that the completed Boolean-table execution visits exactly the reachable
vertices. It also proves Kleinberg--Tardos theorem (3.7) from the semantic certificate laws of
recursive DFS. The executable iterative DFS does not currently construct that recursive-tree
certificate. `Complexity.lean` proves one cost-independent DFS operation profile, then reuses it
for arbitrary exact costs satisfying explicit upper bounds and for the unit-cost corollaries. Run
the executable example from the repository root with:

```sh
lake env lean Examples/Algorithms/DFS.lean
```
