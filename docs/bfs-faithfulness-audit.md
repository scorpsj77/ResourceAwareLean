---
title: "Breadth-First Search Formalization"
subtitle: "Declaration Headers and Natural-Language Faithfulness Audit"
author: "Generated from Resource-Aware-CSLib source"
date: "12 August 2026"
---

**Audit purpose.** This dossier places every `def` and `theorem` header from the modular BFS formalization next to a statement-level natural-language reading. It is designed for a manual check of whether the Lean claim matches the intended textbook claim.

**Snapshot.** Commit `6194a4137cb8d4f2c2b57ca939e607161a541784`; formalization sources inspected on 12 August 2026. Source locations are line-based and may drift after edits.

**Coverage.** 109 declarations (109 public, 0 private). Declarations written with `abbrev`, `structure`, or `inductive`, along with proof bodies, namespace commands, imports, and executable examples, are intentionally excluded.

**How to audit an entry.** Check (1) quantified inputs and type-class assumptions, (2) graph, size, representation, or cost hypotheses, (3) the exact conclusion, and (4) which semantic or resource interpretation is being measured. The prose explains the statement; it does not claim more than the displayed header.

# Contents {#contents}

- [High-level faithfulness guide](#high-level-faithfulness-guide)
  - [Important scope boundaries](#important-scope-boundaries)
  - [Notation used in the headers](#notation-used-in-the-headers)
- [Algorithm: abstract program](#algorithm) (4 declarations)
- [Resource model, semantics, and runners](#resourcemodel) (5 declarations)
- [Correctness and graph-theoretic certificates](#correctness) (41 declarations)
- [Complexity and resource bounds](#complexity) (59 declarations)
- [Audit completion checklist](#audit-completion-checklist)
- [Source inventory](#source-inventory)

# High-level faithfulness guide {#high-level-faithfulness-guide}

The formalization uses one layer-based free program and interprets it with shared graph-traversal semantics, state backends, and cost models. Correctness connects the completed Boolean-table run to graph reachability; additional mathematical constructions certify shortest-path trees and the same-layer-edge bipartiteness dichotomy. Complexity is stated separately for adjacency-list and adjacency-matrix resource models.

## Important scope boundaries {#important-scope-boundaries}

- The executable BFS is fuel-bounded. `Interpreter.run` chooses the graph model's verified vertex count as fuel.
- The algorithm processes a complete current layer and builds the next layer; it is not presented as a queue implementation.
- The standard correctness run uses a Boolean visited table, an optional-distance table, and an edge-list tree backend.
- Exact-cost theorems sum measured primitive events. Weighted-operation theorems instead use explicit upper charges and require a bounded-cost hypothesis.
- Adjacency-list bounds use `n + m`; adjacency-matrix bounds use `n²`. These are abstract resource-model bounds, not wall-clock measurements.
- The canonical shortest-path tree is a noncomputable mathematical construction from a connected `SimpleGraph`; audit separately how `run_certificate` relates it to a BFS run.
- The final bipartiteness theorem is a disjunction between a valid parity-by-layer coloring and an odd-cycle certificate arising from a same-layer edge.

## Notation used in the headers {#notation-used-in-the-headers}

- `TraceM (Event V) α`: a deterministic result paired with an ordered trace of measured graph-traversal events.
- `.ret`: the returned value of a trace computation; for runs, `.ret.2` is the final product state.
- `ResourceModel G V`: graph interface, neighbor-access behavior, sizes, and representation-dependent resource data for graphs of type `G`.
- `n` and `m`: the model's vertex count and adjacency-entry count in the textbook bounds.
- `weightedOperationCost charge run`: the sum of user-supplied charges over the run's operation trace.
- `IsBoundedBy`: a pointwise assertion that exact primitive measurements do not exceed declared primitive bounds.
- `=O[atTop]`: asymptotic big-O as natural input sizes tend to infinity.

# Algorithm: abstract program {#algorithm}

[Back to contents](#contents)

**Source file:** `TextbookAlgorithms/KleinbergTardos/Chapter03/BFS/Algorithm.lean`  
**Declarations in this section:** 4

The free program and its algorithm-specific recursive helpers.

### processNeighbors — def

*Source:* `Algorithm.lean:39`; public

```lean
def processNeighbors (u : Vertex) (nextLevel : Nat) :
    List Vertex → Program Vertex (List Vertex)
```

**Natural-language explanation.** Inspect the neighbors of one vertex and return exactly the vertices newly discovered from it.  A vertex is marked before recursion continues, so a later occurrence will be skipped.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### processLayer — def

*Source:* `Algorithm.lean:54`; public

```lean
def processLayer (level : Nat) : List Vertex → Program Vertex (List Vertex)
```

**Natural-language explanation.** Process every vertex in one layer and construct the following layer.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### bfsLoop — def

*Source:* `Algorithm.lean:66`; public

```lean
def bfsLoop : Nat → Nat → List Vertex → Program Vertex PUnit
```

**Natural-language explanation.** Repeatedly construct the next layer, stopping at the first empty layer or when fuel is exhausted.  A vertex-count upper bound supplies enough fuel for any finite simple path.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### bfs — def

*Source:* `Algorithm.lean:94`; public

```lean
def bfs (vertexBound : Nat) (source : Vertex) : Program Vertex PUnit
```

**Natural-language explanation.** Run Kleinberg's BFS from `source` with explicit current and next layers. `vertexBound` is supplied by the finite graph representation.  It is used only as termination fuel; the current layer starts as `[source]`, and discovered vertices are recorded by the chosen model.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.


# Resource model, semantics, and runners {#resourcemodel}

[Back to contents](#contents)

**Source file:** `TextbookAlgorithms/KleinbergTardos/Chapter03/BFS/ResourceModel.lean`  
**Declarations in this section:** 5

The selected semantic backends, cost interpretation, runner, and space model.

### runWithBound — def

*Source:* `ResourceModel.lean:37`; public

```lean
def runWithBound {G : Type u} (model : ResourceModel G Vertex) (graph : G)
    (control : GraphTraversal.ControlCostModel)
    (visited : GraphTraversal.VisitedModel Vertex VisitedState)
    (levels : GraphTraversal.LevelModel Vertex LevelState)
    (tree : GraphTraversal.TreeModel Vertex TreeState)
    (vertexBound : Nat) (source : Vertex) :
    TraceM (Event Vertex) (PUnit × State VisitedState LevelState TreeState)
```

**Natural-language explanation.** Run Kleinberg BFS with explicit fuel and independently selected components.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### run — def

*Source:* `ResourceModel.lean:48`; public

```lean
def run {G : Type u} (model : ResourceModel G Vertex) (graph : G)
    (control : GraphTraversal.ControlCostModel)
    (visited : GraphTraversal.VisitedModel Vertex VisitedState)
    (levels : GraphTraversal.LevelModel Vertex LevelState)
    (tree : GraphTraversal.TreeModel Vertex TreeState) (source : Vertex) :
    TraceM (Event Vertex) (PUnit × State VisitedState LevelState TreeState)
```

**Natural-language explanation.** Use the graph model's verified vertex count as termination fuel.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### exactCost — def

*Source:* `ResourceModel.lean:59`; public

```lean
def exactCost (computation : TraceM (Event Vertex) α) : Nat
```

**Natural-language explanation.** Sum the measured primitive work in a completed BFS trace.

**Audit focus.** This concerns the sum of the abstract primitive measurements recorded in the trace.

### total — def

*Source:* `ResourceModel.lean:69`; public

```lean
def total (space : SpaceUsage) : Nat
```

**Natural-language explanation.** Add the static graph-storage amount and the traversal working-storage amount.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### spaceUsage — def

*Source:* `ResourceModel.lean:75`; public

```lean
def spaceUsage {G : Type u} (model : ResourceModel G Vertex) (graph : G)
    (visited : GraphTraversal.VisitedModel Vertex VisitedState)
    (levels : GraphTraversal.LevelModel Vertex LevelState)
    (tree : GraphTraversal.TreeModel Vertex TreeState) : SpaceUsage
```

**Natural-language explanation.** Add active-layer storage to the selected visited, level, and tree backend storage.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.


# Correctness and graph-theoretic certificates {#correctness}

[Back to contents](#contents)

**Source file:** `TextbookAlgorithms/KleinbergTardos/Chapter03/BFS/Correctness.lean`  
**Declarations in this section:** 41

Semantic correctness of completed runs and the case study's graph-theoretic consequences.

### run_visited_eq_loopResult — theorem

*Source:* `Correctness.lean:31`; public

```lean
theorem run_visited_eq_loopResult [DecidableEq V]
    (model : ResourceModel G V) (graph : G) (source : V) :
    (Interpreter.run model graph GraphTraversal.ControlCostModel.unit
        GraphTraversal.VisitedModel.booleanTable GraphTraversal.LevelModel.table
        GraphTraversal.TreeModel.edgeList source).ret.2.visited =
      (Operational.loopResult model graph (model.vertexCount graph) 0 [source]
        (Operational.startVisited source)).visited
```

**Natural-language explanation.** The public Boolean-table runner has the pure visited-state recurrence used below.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### neighborResult_visited_iff — theorem

*Source:* `Correctness.lean:63`; public

```lean
theorem neighborResult_visited_iff [DecidableEq V]
    (visited : V → Bool) (neighbors : List V) (vertex : V) :
    (neighborResult visited neighbors).visited vertex = true ↔
      visited vertex = true ∨ vertex ∈ neighbors
```

**Natural-language explanation.** A neighbor scan changes exactly the bits belonging to the scanned list.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### neighborResult_visited_iff_initial_or_fresh — theorem

*Source:* `Correctness.lean:81`; public

```lean
theorem neighborResult_visited_iff_initial_or_fresh [DecidableEq V]
    (visited : V → Bool) (neighbors : List V) (vertex : V) :
    (neighborResult visited neighbors).visited vertex = true ↔
      visited vertex = true ∨ vertex ∈ (neighborResult visited neighbors).fresh
```

**Natural-language explanation.** A neighbor scan preserves old bits and sets precisely its fresh output bits.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### layerResult_visited_iff_initial_or_fresh — theorem

*Source:* `Correctness.lean:96`; public

```lean
theorem layerResult_visited_iff_initial_or_fresh [DecidableEq V]
    (model : ResourceModel G V) (graph : G) (level : Nat)
    (current : List V) (visited : V → Bool) (vertex : V) :
    (layerResult model graph level current visited).visited vertex = true ↔
      visited vertex = true ∨ vertex ∈ (layerResult model graph level current visited).fresh
```

**Natural-language explanation.** A whole layer preserves old bits and sets precisely the vertices in its fresh output.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### layerResult_visits_neighbors — theorem

*Source:* `Correctness.lean:118`; public

```lean
theorem layerResult_visits_neighbors [DecidableEq V]
    (model : ResourceModel G V) (graph : G) (level : Nat)
    (current : List V) (visited : V → Bool) {parent child : V}
    (hparent : parent ∈ current)
    (hchild : child ∈ model.neighborAccess.outNeighbors graph parent) :
    (layerResult model graph level current visited).visited child = true
```

**Natural-language explanation.** A layer scan visits every neighbor of every vertex in that layer.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### loopResult_monotone — theorem

*Source:* `Correctness.lean:138`; public

```lean
theorem loopResult_monotone [DecidableEq V]
    (model : ResourceModel G V) (graph : G) (fuel level : Nat)
    (current : List V) (visited : V → Bool) {vertex : V}
    (hvertex : visited vertex = true) :
    (loopResult model graph fuel level current visited).visited vertex = true
```

**Natural-language explanation.** A BFS-loop recurrence only turns visited bits on.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### finalFrontier — def

*Source:* `Correctness.lean:154`; public

```lean
def finalFrontier [DecidableEq V] (model : ResourceModel G V) (graph : G) :
    Nat → Nat → List V → (V → Bool) → List V
```

**Natural-language explanation.** The frontier left when the BFS loop stops, including premature fuel exhaustion.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### loopResult_visited_iff_initial_or_discovered — theorem

*Source:* `Correctness.lean:163`; public

```lean
theorem loopResult_visited_iff_initial_or_discovered [DecidableEq V]
    (model : ResourceModel G V) (graph : G) (fuel level : Nat)
    (current : List V) (visited : V → Bool) (vertex : V) :
    (loopResult model graph fuel level current visited).visited vertex = true ↔
      visited vertex = true ∨
        vertex ∈ (loopResult model graph fuel level current visited).discovered
```

**Natural-language explanation.** Final visited bits are exactly the initial bits plus all loop discoveries.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### mem_queried_or_finalFrontier — theorem

*Source:* `Correctness.lean:189`; public

```lean
theorem mem_queried_or_finalFrontier [DecidableEq V]
    (model : ResourceModel G V) (graph : G) (fuel level : Nat)
    (current : List V) (visited : V → Bool) {vertex : V}
    (hvertex : vertex ∈ current ∨
      vertex ∈ (loopResult model graph fuel level current visited).discovered) :
    vertex ∈ (loopResult model graph fuel level current visited).queried ∨
      vertex ∈ finalFrontier model graph fuel level current visited
```

**Natural-language explanation.** Every initial or discovered frontier vertex is eventually queried or remains at termination.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### loopResult_visits_queried_neighbors — theorem

*Source:* `Correctness.lean:221`; public

```lean
theorem loopResult_visits_queried_neighbors [DecidableEq V]
    (model : ResourceModel G V) (graph : G) (fuel level : Nat)
    (current : List V) (visited : V → Bool) {parent child : V}
    (hparent : parent ∈ (loopResult model graph fuel level current visited).queried)
    (hchild : child ∈ model.neighborAccess.outNeighbors graph parent) :
    (loopResult model graph fuel level current visited).visited child = true
```

**Natural-language explanation.** Every neighbor of a queried vertex is visited when the loop finishes.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### finalFrontier_properties — theorem

*Source:* `Correctness.lean:255`; public

```lean
theorem finalFrontier_properties [DecidableEq V]
    (model : ResourceModel G V) (graph : G) (fuel level : Nat)
    (previous current : List V) (visited : V → Bool)
    (hprevious : previous.Nodup) (hcurrent : current.Nodup)
    (hdisjoint : previous.Disjoint current)
    (hpreviousVisited : ∀ vertex ∈ previous, visited vertex = true)
    (hcurrentVisited : ∀ vertex ∈ current, visited vertex = true)
    (hcurrentVertices : ∀ vertex ∈ current,
      vertex ∈ model.vertexEnumeration.vertices graph) :
    FinalFrontierProperties model graph fuel previous
      (loopResult model graph fuel level current visited)
      (finalFrontier model graph fuel level current visited)
```

**Natural-language explanation.** A nonempty terminal frontier would contain an additional distinct graph vertex.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### finalFrontier_eq_nil — theorem

*Source:* `Correctness.lean:322`; public

```lean
theorem finalFrontier_eq_nil [DecidableEq V]
    (model : ResourceModel G V) (graph : G) (source : V)
    (hsource : source ∈ model.interface.vertexSet graph) :
    finalFrontier model graph (model.vertexCount graph) 0 [source]
      (startVisited source) = []
```

**Natural-language explanation.** With one unit of fuel per enumerated vertex, BFS cannot stop on a nonempty layer.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### layerResult_reachable — theorem

*Source:* `Correctness.lean:361`; public

```lean
theorem layerResult_reachable [DecidableEq V]
    (model : ResourceModel G V) (graph : G) (source : V) (level : Nat)
    (current : List V) (visited : V → Bool)
    (hvisited : ∀ {vertex}, visited vertex = true →
      Reachable model.interface graph source vertex)
    (hcurrent : ∀ {vertex}, vertex ∈ current →
      Reachable model.interface graph source vertex) :
    ∀ {vertex}, (layerResult model graph level current visited).visited vertex = true →
      Reachable model.interface graph source vertex
```

**Natural-language explanation.** Processing a reachable layer cannot mark an unreachable vertex.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### loopResult_reachable — theorem

*Source:* `Correctness.lean:391`; public

```lean
theorem loopResult_reachable [DecidableEq V]
    (model : ResourceModel G V) (graph : G) (source : V)
    (fuel level : Nat) (current : List V) (visited : V → Bool)
    (hvisited : ∀ {vertex}, visited vertex = true →
      Reachable model.interface graph source vertex)
    (hcurrent : ∀ {vertex}, vertex ∈ current →
      Reachable model.interface graph source vertex) :
    ∀ {vertex}, (loopResult model graph fuel level current visited).visited vertex = true →
      Reachable model.interface graph source vertex
```

**Natural-language explanation.** Every bit set by a BFS-loop recurrence denotes a vertex reachable from the source.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### loopResult_visitsExactlyReachable — theorem

*Source:* `Correctness.lean:420`; public

```lean
theorem loopResult_visitsExactlyReachable [DecidableEq V]
    (model : ResourceModel G V) (graph : G) (source : V)
    (hsource : source ∈ model.interface.vertexSet graph) :
    GraphTraversal.VisitsExactlyReachable model.interface graph source fun vertex ↦
      (loopResult model graph (model.vertexCount graph) 0 [source]
        (startVisited source)).visited vertex = true
```

**Natural-language explanation.** The Boolean-table BFS recurrence visits exactly the vertices reachable from its source.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### run_visitsExactlyReachable — theorem

*Source:* `Correctness.lean:468`; public

```lean
theorem run_visitsExactlyReachable [DecidableEq V]
    (model : ResourceModel G V) (graph : G) (source : V)
    (hsource : source ∈ model.interface.vertexSet graph) :
    GraphTraversal.VisitsExactlyReachable model.interface graph source fun vertex ↦
      (Interpreter.run model graph GraphTraversal.ControlCostModel.unit
        GraphTraversal.VisitedModel.booleanTable GraphTraversal.LevelModel.table
        GraphTraversal.TreeModel.edgeList source).ret.2.visited vertex = true
```

**Natural-language explanation.** Executable BFS with the standard Boolean table visits exactly the reachable vertices.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### exists_predecessor — theorem

*Source:* `Correctness.lean:486`; public

```lean
theorem exists_predecessor (vertex : V) (hne : vertex ≠ source) :
    ∃ predecessor, graph.Adj predecessor vertex ∧
      graph.dist source vertex = graph.dist source predecessor + 1
```

**Natural-language explanation.** Every non-root vertex has a neighbor one step closer to the root.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### parent — def

*Source:* `Correctness.lean:502`; public

```lean
noncomputable def parent (vertex : V) : V
```

**Natural-language explanation.** Choose the predecessor used by the canonical shortest-path tree.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### parent_spec — theorem

*Source:* `Correctness.lean:507`; public

```lean
theorem parent_spec {vertex : V} (hne : vertex ≠ source) :
    graph.Adj (parent graph connected source vertex) vertex ∧
      graph.dist source vertex =
        graph.dist source (parent graph connected source vertex) + 1
```

**Natural-language explanation.** For a non-source vertex, its selected parent is adjacent to it and lies exactly one graph-distance step closer to the source.

**Audit focus.** Check the exact role of the displayed connectedness data or conclusion.

### tree — def

*Source:* `Correctness.lean:515`; public

```lean
noncomputable def tree : SimpleGraph V
```

**Natural-language explanation.** The graph containing the chosen predecessor edge of every non-root vertex.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### tree_adj — theorem

*Source:* `Correctness.lean:527`; public

```lean
theorem tree_adj {x y : V} : (tree graph connected source).Adj x y ↔
    (x ≠ source ∧ parent graph connected source x = y) ∨
      (y ≠ source ∧ parent graph connected source y = x)
```

**Natural-language explanation.** Two vertices are adjacent in the canonical tree exactly when either one is a non-root vertex whose chosen parent is the other.

**Audit focus.** Check the exact role of the displayed connectedness data or conclusion.

### tree_le — theorem

*Source:* `Correctness.lean:532`; public

```lean
theorem tree_le : tree graph connected source ≤ graph
```

**Natural-language explanation.** Every edge of the canonical chosen-parent tree is also an edge of the original graph.

**Audit focus.** Check the exact role of the displayed connectedness data or conclusion.

### exists_walk_length_dist — theorem

*Source:* `Correctness.lean:540`; public

```lean
theorem exists_walk_length_dist (vertex : V) :
    ∃ walk : (tree graph connected source).Walk source vertex,
      walk.length = graph.dist source vertex
```

**Natural-language explanation.** The chosen-parent edges give a root-to-vertex walk of graph-shortest length.

**Audit focus.** Check the exact role of the displayed connectedness data or conclusion.

### tree_connected — theorem

*Source:* `Correctness.lean:562`; public

```lean
theorem tree_connected : (tree graph connected source).Connected
```

**Natural-language explanation.** The canonical chosen-parent tree is connected.

**Audit focus.** Check the exact role of the displayed connectedness data or conclusion.

### parentEdge — def

*Source:* `Correctness.lean:571`; public

```lean
noncomputable def parentEdge (vertex : { vertex : V // vertex ≠ source }) :
    (tree graph connected source).edgeSet
```

**Natural-language explanation.** The selected edge belonging to a non-root vertex.

**Audit focus.** Check the exact role of the displayed connectedness data or conclusion.

### parentEdge_injective — theorem

*Source:* `Correctness.lean:578`; public

```lean
theorem parentEdge_injective :
    Function.Injective (parentEdge graph connected source)
```

**Natural-language explanation.** Different non-root vertices determine different selected parent edges.

**Audit focus.** Check the exact role of the displayed connectedness data or conclusion.

### parentEdge_surjective — theorem

*Source:* `Correctness.lean:595`; public

```lean
theorem parentEdge_surjective :
    Function.Surjective (parentEdge graph connected source)
```

**Natural-language explanation.** Every edge of the canonical tree is the selected parent edge of some non-root vertex.

**Audit focus.** Check the exact role of the displayed connectedness data or conclusion.

### tree_isTree — theorem

*Source:* `Correctness.lean:610`; public

```lean
theorem tree_isTree [Finite V] : (tree graph connected source).IsTree
```

**Natural-language explanation.** For a finite vertex type, the connected chosen-parent graph satisfies the formal `IsTree` predicate.

**Audit focus.** Retain the displayed finiteness assumption in the informal claim. Check the exact role of the displayed connectedness data or conclusion.

### preservesDistance — theorem

*Source:* `Correctness.lean:627`; public

```lean
theorem preservesDistance (vertex : V) :
    (tree graph connected source).dist source vertex = graph.dist source vertex
```

**Natural-language explanation.** Distance from the source in the canonical tree equals distance from the source in the original graph.

**Audit focus.** Check the exact role of the displayed connectedness data or conclusion.

### Layer — def

*Source:* `Correctness.lean:637`; public

```lean
def Layer (h : Γ.IsUndirected g) (source : V) (i : Nat) : Set V
```

**Natural-language explanation.** Layer `i` consists of the vertices at distance `i` from the BFS source.

**Audit focus.** Check the exact role of the displayed undirectedness certificate.

### HasSameLayerEdge — def

*Source:* `Correctness.lean:641`; public

```lean
def HasSameLayerEdge (h : Γ.IsUndirected g) (source : V) : Prop
```

**Natural-language explanation.** Some graph edge has both endpoints in the same BFS layer.

**Audit focus.** Check the exact role of the displayed undirectedness certificate.

### layerColor — def

*Source:* `Correctness.lean:645`; public

```lean
noncomputable def layerColor (h : Γ.IsUndirected g) (source vertex : V) : Fin 2
```

**Natural-language explanation.** Color even-numbered BFS layers red and odd-numbered layers blue.

**Audit focus.** Check the exact role of the displayed undirectedness certificate.

### IsValidLayerColoring — def

*Source:* `Correctness.lean:649`; public

```lean
def IsValidLayerColoring (h : Γ.IsUndirected g) (source : V) : Prop
```

**Natural-language explanation.** The parity coloring of the BFS layers is a proper graph coloring.

**Audit focus.** Check the exact role of the displayed undirectedness certificate.

### TreeCertificate.ofConnected — def

*Source:* `Correctness.lean:664`; public

```lean
noncomputable def TreeCertificate.ofConnected [DecidableEq V] [Fintype V]
    (h : Γ.IsUndirected g) (source : V) (connected : h.toSimpleGraph.Connected) :
    TreeCertificate h source
```

**Natural-language explanation.** Every finite connected graph has the canonical shortest-path-tree certificate rooted at `source`.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type. Retain the displayed finiteness assumption in the informal claim. Check the exact role of the displayed undirectedness certificate. Check the exact role of the displayed connectedness data or conclusion.

### run_certificate — def

*Source:* `Correctness.lean:683`; public

```lean
noncomputable def run_certificate [DecidableEq V] [Fintype V]
    (model : ResourceModel G V) (graph : G)
    (h : model.interface.IsUndirected graph) (source : V)
    (hsource : source ∈ model.interface.vertexSet graph)
    (connected : h.toSimpleGraph.Connected) : RunCertificate model graph h source
```

**Natural-language explanation.** Executable BFS yields exact reachability together with its shortest-path-tree certificate.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type. Retain the displayed finiteness assumption in the informal claim. Check the exact role of the displayed undirectedness certificate. Check the exact role of the displayed connectedness data or conclusion.

### TreeCertificate.graphConnected — theorem

*Source:* `Correctness.lean:692`; public

```lean
theorem TreeCertificate.graphConnected {h : Γ.IsUndirected g} {source : V}
    (bfs : TreeCertificate h source) : h.toSimpleGraph.Connected
```

**Natural-language explanation.** A certified BFS tree entails the textbook connected-graph hypothesis.

**Audit focus.** Check the exact role of the displayed undirectedness certificate. Check the exact role of the displayed connectedness data or conclusion.

### layerColoring_valid_of_no_sameLayerEdge — theorem

*Source:* `Correctness.lean:697`; public

```lean
theorem layerColoring_valid_of_no_sameLayerEdge (h : Γ.IsUndirected g) (source : V)
    (hno : ¬ HasSameLayerEdge h source) : IsValidLayerColoring h source
```

**Natural-language explanation.** If no edge stays within one layer, BFS layer parity gives a proper two-coloring.

**Audit focus.** Check the exact role of the displayed undirectedness certificate.

### TreeCertificate.oddCycle_of_sameLayerEdge — theorem

*Source:* `Correctness.lean:716`; public

```lean
theorem TreeCertificate.oddCycle_of_sameLayerEdge {h : Γ.IsUndirected g} {source : V}
    (bfs : TreeCertificate h source) (hsame : HasSameLayerEdge h source) :
    Γ.ContainsOddCycle h
```

**Natural-language explanation.** A same-layer edge closes the even-length tree path between its endpoints into an odd cycle. This is the textbook lowest-common-ancestor construction expressed via the unique tree path.

**Audit focus.** Check the exact role of the displayed undirectedness certificate.

### ProperLayerCase — def

*Source:* `Correctness.lean:748`; public

```lean
def ProperLayerCase (h : Γ.IsUndirected g) (source : V) : Prop
```

**Natural-language explanation.** Case (i) of theorem (3.15).

**Audit focus.** Check the exact role of the displayed undirectedness certificate.

### OddCycleCase — def

*Source:* `Correctness.lean:752`; public

```lean
def OddCycleCase (h : Γ.IsUndirected g) (source : V) : Prop
```

**Natural-language explanation.** Case (ii) of theorem (3.15).

**Audit focus.** Check the exact role of the displayed undirectedness certificate.

### bfs_bipartite_or_contains_odd_cycle — theorem

*Source:* `Correctness.lean:758`; public

```lean
theorem bfs_bipartite_or_contains_odd_cycle {h : Γ.IsUndirected g} {source : V}
    (bfs : TreeCertificate h source) :
    Xor (ProperLayerCase h source) (OddCycleCase h source)
```

**Natural-language explanation.** Kleinberg theorem (3.15): exactly one of the proper-layer and odd-cycle cases holds for BFS.

**Audit focus.** Check the exact role of the displayed undirectedness certificate.


# Complexity and resource bounds {#complexity}

[Back to contents](#contents)

**Source file:** `TextbookAlgorithms/KleinbergTardos/Chapter03/BFS/Complexity.lean`  
**Declarations in this section:** 59

Cost-independent operation profiles, exact-cost transfers, closed bounds, and asymptotic endpoints.

### execute — def

*Source:* `Complexity.lean:39`; public

```lean
def execute {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G)
    (program : GraphTraversal.Program Vertex α) (state : State Vertex) :
    TraceM (GraphTraversal.Event Vertex) (α × State Vertex)
```

**Natural-language explanation.** Execute a BFS program from an arbitrary standard-model interpreter state.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### execute_pure — theorem

*Source:* `Complexity.lean:48`; public; attributes: `@[simp]`

```lean
@[simp]
theorem execute_pure {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (value : α) (state : State Vertex) :
    execute model graph (pure value) state = pure (value, state)
```

**Natural-language explanation.** Executing a pure return yields that value with the state unchanged and emits no event.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### execute_bind — theorem

*Source:* `Complexity.lean:53`; public

```lean
theorem execute_bind {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G)
    (program : GraphTraversal.Program Vertex α) (next : α → GraphTraversal.Program Vertex β)
    (state : State Vertex) :
    execute model graph (program >>= next) state = (do
      let (result, state') ← execute model graph program state
      execute model graph (next result) state')
```

**Natural-language explanation.** Executing a monadic bind first executes the initial program and then executes the selected continuation from its resulting state.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### execute_map — theorem

*Source:* `Complexity.lean:62`; public

```lean
theorem execute_map {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (function : α → β)
    (program : GraphTraversal.Program Vertex α) (state : State Vertex) :
    execute model graph (function <$> program) state = (do
      let (result, state') ← execute model graph program state
      pure (function result, state'))
```

**Natural-language explanation.** Executing a mapped program preserves the resulting state and applies the function to the returned value.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### execute_checkLayerEmpty — theorem

*Source:* `Complexity.lean:75`; public; attributes: `@[simp]`

```lean
@[simp]
theorem execute_checkLayerEmpty {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (level : Nat) (state : State Vertex) :
    execute model graph (GraphTraversal.checkLayerEmpty level) state =
      ⟨(.unit, state), EventTrace.singleton ⟨.checkLayerEmpty level, 1⟩⟩
```

**Natural-language explanation.** The standard interpreter executes a layer-empty check without changing state and records one unit-cost event.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### execute_isVisited — theorem

*Source:* `Complexity.lean:82`; public; attributes: `@[simp]`

```lean
@[simp]
theorem execute_isVisited {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (vertex : Vertex) (state : State Vertex) :
    execute model graph (GraphTraversal.isVisited vertex) state =
      ⟨(ULift.up (state.visited vertex), state),
        EventTrace.singleton ⟨.isVisited vertex, 1⟩⟩
```

**Natural-language explanation.** The standard interpreter returns the Boolean visited-table entry, leaves state unchanged, and records one unit-cost event.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### execute_markVisited — theorem

*Source:* `Complexity.lean:90`; public; attributes: `@[simp]`

```lean
@[simp]
theorem execute_markVisited {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (vertex : Vertex) (state : State Vertex) :
    execute model graph (GraphTraversal.markVisited vertex) state =
      ⟨(.unit, { state with visited := GraphTraversal.update state.visited vertex true }),
        EventTrace.singleton ⟨.markVisited vertex, 1⟩⟩
```

**Natural-language explanation.** The standard interpreter sets the vertex's visited entry to true and records one unit-cost event.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### execute_recordLevel — theorem

*Source:* `Complexity.lean:98`; public; attributes: `@[simp]`

```lean
@[simp]
theorem execute_recordLevel {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (vertex : Vertex) (level : Nat)
    (state : State Vertex) :
    execute model graph (GraphTraversal.recordLevel vertex level) state =
      ⟨(.unit, { state with levels := GraphTraversal.update state.levels vertex (some level) }),
        EventTrace.singleton ⟨.recordLevel vertex level, 1⟩⟩
```

**Natural-language explanation.** The standard interpreter stores the supplied level for the vertex and records one unit-cost event.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### execute_addTreeEdge — theorem

*Source:* `Complexity.lean:107`; public; attributes: `@[simp]`

```lean
@[simp]
theorem execute_addTreeEdge {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (parent child : Vertex)
    (state : State Vertex) :
    execute model graph (GraphTraversal.addTreeEdge parent child) state =
      ⟨(.unit, { state with tree := (parent, child) :: state.tree }),
        EventTrace.singleton ⟨.addTreeEdge parent child, 1⟩⟩
```

**Natural-language explanation.** The standard interpreter prepends the parent-child edge to the tree state and records one unit-cost event.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### execute_neighbors — theorem

*Source:* `Complexity.lean:116`; public; attributes: `@[simp]`

```lean
@[simp]
theorem execute_neighbors {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (vertex : Vertex) (state : State Vertex) :
    execute model graph (GraphTraversal.neighbors vertex) state =
      ⟨(model.neighborAccess.outNeighbors graph vertex, state),
        EventTrace.singleton ⟨.neighbors vertex, model.neighborCost graph vertex⟩⟩
```

**Natural-language explanation.** The standard interpreter returns the model's outgoing neighbors, leaves traversal state unchanged, and records the model's neighbor-access cost.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### execute_clearVisited — theorem

*Source:* `Complexity.lean:124`; public; attributes: `@[simp]`

```lean
@[simp]
theorem execute_clearVisited {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (state : State Vertex) :
    execute model graph GraphTraversal.clearVisited state =
      ⟨(.unit, { state with visited := fun _ ↦ false }),
        EventTrace.singleton ⟨.clearVisited, model.vertexCount graph⟩⟩
```

**Natural-language explanation.** The standard interpreter resets every visited entry to false and records a vertex-count-sized event.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### execute_clearLevels — theorem

*Source:* `Complexity.lean:132`; public; attributes: `@[simp]`

```lean
@[simp]
theorem execute_clearLevels {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (state : State Vertex) :
    execute model graph GraphTraversal.clearLevels state =
      ⟨(.unit, { state with levels := fun _ ↦ none }),
        EventTrace.singleton ⟨.clearLevels, model.vertexCount graph⟩⟩
```

**Natural-language explanation.** The standard interpreter resets every level entry to `none` and records a vertex-count-sized event.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### execute_clearTree — theorem

*Source:* `Complexity.lean:140`; public; attributes: `@[simp]`

```lean
@[simp]
theorem execute_clearTree {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (state : State Vertex) :
    execute model graph GraphTraversal.clearTree state =
      ⟨(.unit, { state with tree := [] }),
        EventTrace.singleton ⟨.clearTree, 1⟩⟩
```

**Natural-language explanation.** The standard interpreter empties the stored tree-edge list and records one unit-cost event.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### neighborResult — def

*Source:* `Complexity.lean:153`; public

```lean
def neighborResult [DecidableEq Vertex] :
    (Vertex → Bool) → List Vertex → NeighborResult Vertex
```

**Natural-language explanation.** Semantic recurrence for `processNeighbors` under the standard BFS backends.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### operationCharge — def

*Source:* `Complexity.lean:166`; public

```lean
def operationCharge {G : Type u} (model : ResourceModel G Vertex) (graph : G)
    (checkLayerEmpty isVisited markVisited recordLevel addTreeEdge : Nat)
    (other : GraphTraversal.Op Vertex → Nat) : GraphTraversal.Op Vertex → Nat
```

**Natural-language explanation.** Cost-independent weights used to summarize a BFS operation profile.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### discoveryOperationCost — def

*Source:* `Complexity.lean:178`; public

```lean
def discoveryOperationCost (markVisited recordLevel addTreeEdge : Nat) : Nat
```

**Natural-language explanation.** Combined profile weight of the three updates performed for one discovery.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### processNeighbors_weightedOperationCost_le — theorem

*Source:* `Complexity.lean:183`; public

```lean
theorem processNeighbors_weightedOperationCost_le {G : Type u} {Vertex : Type v}
    [DecidableEq Vertex] (model : ResourceModel G Vertex) (graph : G)
    (checkLayerEmpty isVisited markVisited recordLevel addTreeEdge : Nat)
    (other : GraphTraversal.Op Vertex → Nat) (parent : Vertex) (nextLevel : Nat)
    (neighbors : List Vertex) (state : State Vertex) :
    let expected := neighborResult state.visited neighbors
    let actual := execute model graph (processNeighbors parent nextLevel neighbors) state
    actual.ret.1 = expected.fresh ∧ actual.ret.2.visited = expected.visited ∧
      ResourceAware.Program.weightedOperationCost
          (operationCharge model graph checkLayerEmpty isVisited markVisited recordLevel
            addTreeEdge other) actual ≤
        isVisited * neighbors.length +
          discoveryOperationCost markVisited recordLevel addTreeEdge * expected.fresh.length
```

**Natural-language explanation.** One cost-independent profile proof for scanning neighbors, reusable under every cost model.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type. This concerns a weighted operation profile, which is not automatically the trace's exact measured cost.

### neighborResult_properties — theorem

*Source:* `Complexity.lean:248`; public

```lean
theorem neighborResult_properties [DecidableEq Vertex]
    (visited : Vertex → Bool) (neighbors : List Vertex) :
    NeighborProperties neighbors visited (neighborResult visited neighbors)
```

**Natural-language explanation.** Newly returned neighbors are exactly-once discoveries.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### layerResult — def

*Source:* `Complexity.lean:294`; public

```lean
def layerResult {G : Type u} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (level : Nat) :
    List Vertex → (Vertex → Bool) → LayerResult Vertex
```

**Natural-language explanation.** Semantic recurrence for `processLayer`.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### weightedLayerCost — def

*Source:* `Complexity.lean:305`; public

```lean
def weightedLayerCost {G : Type u} (isVisited : Nat)
    (model : ResourceModel G Vertex) (graph : G) (current : List Vertex) : Nat
```

**Natural-language explanation.** Neighbor-query and visited-test weight in a cost-independent layer profile.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### weightedLayerCost_append — theorem

*Source:* `Complexity.lean:311`; public; attributes: `@[simp]`

```lean
@[simp]
theorem weightedLayerCost_append {G : Type u} (isVisited : Nat)
    (model : ResourceModel G Vertex) (graph : G) (left right : List Vertex) :
    weightedLayerCost isVisited model graph (left ++ right) =
      weightedLayerCost isVisited model graph left +
        weightedLayerCost isVisited model graph right
```

**Natural-language explanation.** The weighted scan cost of two concatenated vertex lists is the sum of their individual weighted scan costs.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### processLayer_weightedOperationCost_le — theorem

*Source:* `Complexity.lean:320`; public

```lean
theorem processLayer_weightedOperationCost_le {G : Type u} {Vertex : Type v}
    [DecidableEq Vertex] (model : ResourceModel G Vertex) (graph : G)
    (checkLayerEmpty isVisited markVisited recordLevel addTreeEdge : Nat)
    (other : GraphTraversal.Op Vertex → Nat) (level : Nat) (current : List Vertex)
    (state : State Vertex) :
    let expected := layerResult model graph level current state.visited
    let actual := execute model graph (processLayer level current) state
    actual.ret.1 = expected.fresh ∧ actual.ret.2.visited = expected.visited ∧
      ResourceAware.Program.weightedOperationCost
          (operationCharge model graph checkLayerEmpty isVisited markVisited recordLevel
            addTreeEdge other) actual ≤
        weightedLayerCost isVisited model graph current +
          discoveryOperationCost markVisited recordLevel addTreeEdge * expected.fresh.length
```

**Natural-language explanation.** One cost-independent operation-profile proof for processing a complete BFS layer.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type. This concerns a weighted operation profile, which is not automatically the trace's exact measured cost.

### layerResult_properties — theorem

*Source:* `Complexity.lean:377`; public

```lean
theorem layerResult_properties {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (level : Nat)
    (current : List Vertex) (visited : Vertex → Bool) :
    LayerProperties model graph current visited
      (layerResult model graph level current visited)
```

**Natural-language explanation.** A complete layer discovers each new vertex once.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### loopResult — def

*Source:* `Complexity.lean:428`; public

```lean
def loopResult {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) :
    Nat → Nat → List Vertex → (Vertex → Bool) → LoopResult Vertex
```

**Natural-language explanation.** Semantic recurrence implemented by the standard-model BFS loop.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### bfsLoop_weightedOperationCost_le — theorem

*Source:* `Complexity.lean:441`; public

```lean
theorem bfsLoop_weightedOperationCost_le {G : Type u} {Vertex : Type v}
    [DecidableEq Vertex] (model : ResourceModel G Vertex) (graph : G)
    (checkLayerEmpty isVisited markVisited recordLevel addTreeEdge : Nat)
    (other : GraphTraversal.Op Vertex → Nat) (fuel level : Nat) (current : List Vertex)
    (state : State Vertex) :
    let expected := loopResult model graph fuel level current state.visited
    let actual := execute model graph (bfsLoop fuel level current) state
    actual.ret.2.visited = expected.visited ∧
      ResourceAware.Program.weightedOperationCost
          (operationCharge model graph checkLayerEmpty isVisited markVisited recordLevel
            addTreeEdge other) actual ≤
        checkLayerEmpty * (fuel + 1) +
          weightedLayerCost isVisited model graph expected.queried +
            discoveryOperationCost markVisited recordLevel addTreeEdge *
              expected.discovered.length
```

**Natural-language explanation.** One cost-independent operation-profile proof for the complete BFS layer loop.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type. This concerns a weighted operation profile, which is not automatically the trace's exact measured cost.

### loopResult_properties — theorem

*Source:* `Complexity.lean:518`; public

```lean
theorem loopResult_properties {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (fuel level : Nat)
    (previous current : List Vertex) (visited : Vertex → Bool)
    (hprevious : previous.Nodup) (hcurrent : current.Nodup)
    (hdisjoint : previous.Disjoint current)
    (hpreviousVisited : ∀ vertex ∈ previous, visited vertex = true)
    (hcurrentVisited : ∀ vertex ∈ current, visited vertex = true)
    (hcurrentVertices : ∀ vertex ∈ current,
      vertex ∈ model.vertexEnumeration.vertices graph) :
    LoopProperties model graph previous current visited
      (loopResult model graph fuel level current visited)
```

**Natural-language explanation.** BFS processes and discovers only globally distinct vertices.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### startVisited — def

*Source:* `Complexity.lean:589`; public

```lean
def startVisited [DecidableEq Vertex] (source : Vertex) : Vertex → Bool
```

**Natural-language explanation.** Visited table immediately before the BFS layer loop starts.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### visitedModel — def

*Source:* `Complexity.lean:634`; public

```lean
def visitedModel [DecidableEq Vertex] (costs : CostModel Vertex) :
    GraphTraversal.VisitedModel Vertex (Vertex → Bool)
```

**Natural-language explanation.** Standard Boolean-table semantics equipped with arbitrary visited-operation costs.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### levelModel — def

*Source:* `Complexity.lean:640`; public

```lean
def levelModel [DecidableEq Vertex] (costs : CostModel Vertex) :
    GraphTraversal.LevelModel Vertex (Vertex → Option Nat)
```

**Natural-language explanation.** Standard level-table semantics equipped with arbitrary level-operation costs.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### treeModel — def

*Source:* `Complexity.lean:645`; public

```lean
def treeModel (costs : CostModel Vertex) :
    GraphTraversal.TreeModel Vertex (List (Vertex × Vertex))
```

**Natural-language explanation.** Standard edge-list semantics equipped with arbitrary tree-operation costs.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### execute — def

*Source:* `Complexity.lean:650`; public

```lean
def execute {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (costs : CostModel Vertex)
    (program : GraphTraversal.Program Vertex α) (state : Operational.State Vertex) :
    TraceM (GraphTraversal.Event Vertex) (α × Operational.State Vertex)
```

**Natural-language explanation.** Execute BFS with the standard backends and arbitrary operation costs.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### discoveryCost — def

*Source:* `Complexity.lean:658`; public

```lean
def discoveryCost (bounds : CostBounds) : Nat
```

**Natural-language explanation.** Upper-bound cost of the three updates performed for one newly discovered vertex.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### otherOperationCharge — def

*Source:* `Complexity.lean:662`; public

```lean
def otherOperationCharge (costs : CostModel Vertex) (bounds : CostBounds) :
    GraphTraversal.Op Vertex → Nat
```

**Natural-language explanation.** Weights for operations outside the BFS loop profile, especially initialization.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### operationCharge — def

*Source:* `Complexity.lean:671`; public

```lean
def operationCharge {G : Type u} (model : ResourceModel G Vertex) (graph : G)
    (costs : CostModel Vertex) (bounds : CostBounds) : GraphTraversal.Op Vertex → Nat
```

**Natural-language explanation.** The operation weights used to reinterpret the cost-independent BFS profile.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### interpreter_isBoundedBy — theorem

*Source:* `Complexity.lean:678`; public

```lean
theorem interpreter_isBoundedBy {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (costs : CostModel Vertex)
    (bounds : CostBounds) (hbounds : costs.IsBoundedBy bounds (model.vertexCount graph)) :
    GraphTraversal.Model.IsBoundedBy model graph costs.control
      (visitedModel costs) (levelModel costs) (treeModel costs)
      (operationCharge model graph costs bounds)
```

**Natural-language explanation.** Primitive cost assumptions are discharged once when constructing the generic interpreter bound, rather than inside each recursive BFS proof.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type. The bound is pointwise over primitive operations; inspect the selected constants and size factors.

### execute_le_standardProfile — theorem

*Source:* `Complexity.lean:711`; public

```lean
theorem execute_le_standardProfile {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (costs : CostModel Vertex)
    (bounds : CostBounds) (hbounds : costs.IsBoundedBy bounds (model.vertexCount graph))
    (program : GraphTraversal.Program Vertex α) (state : Operational.State Vertex) :
    let actual := execute model graph costs program state
    let standard := Operational.execute model graph program state
    actual.ret = standard.ret ∧
      ResourceAware.Program.exactCost actual ≤
        ResourceAware.Program.weightedOperationCost
          (operationCharge model graph costs bounds) standard
```

**Natural-language explanation.** Any bounded-cost BFS execution is semantically equal to the standard execution and is bounded by that execution's single cost-independent profile.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type. This concerns a weighted operation profile, which is not automatically the trace's exact measured cost. The bound is pointwise over primitive operations; inspect the selected constants and size factors.

### layerWeight — def

*Source:* `Complexity.lean:744`; public

```lean
def layerWeight {G : Type u} (bounds : CostBounds) (model : ResourceModel G Vertex)
    (graph : G) (current : List Vertex) : Nat
```

**Natural-language explanation.** Neighbor-query and visited-test work for a list of processed layer vertices.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### initializationCost — def

*Source:* `Complexity.lean:750`; public

```lean
def initializationCost (bounds : CostBounds) : Nat
```

**Natural-language explanation.** Initialization work before the BFS layer loop.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### exactCost_run_le — theorem

*Source:* `Complexity.lean:756`; public

```lean
theorem exactCost_run_le {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (costs : CostModel Vertex)
    (bounds : CostBounds) (hbounds : costs.IsBoundedBy bounds (model.vertexCount graph))
    (source : Vertex) :
    let result := Operational.loopResult model graph (model.vertexCount graph) 0 [source]
      (Operational.startVisited source)
    KleinbergBFS.exactCost
        (KleinbergBFS.Interpreter.run model graph costs.control
          (visitedModel costs) (levelModel costs) (treeModel costs) source) ≤
      initializationCost bounds + bounds.checkLayerEmpty * (model.vertexCount graph + 1) +
        layerWeight bounds model graph result.queried +
          discoveryCost bounds * result.discovered.length
```

**Natural-language explanation.** The public BFS runner obeys arbitrary supplied upper bounds for primitive costs.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type. This concerns the sum of the abstract primitive measurements recorded in the trace. The bound is pointwise over primitive operations; inspect the selected constants and size factors.

### unitCostModel — def

*Source:* `Complexity.lean:822`; public

```lean
def unitCostModel [DecidableEq Vertex] : CostModel Vertex
```

**Natural-language explanation.** Unit-cost instance used only to recover the traditional concrete corollaries.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### unitCostBounds — def

*Source:* `Complexity.lean:829`; public

```lean
def unitCostBounds (n : Nat) : CostBounds
```

**Natural-language explanation.** Bounds realized by the standard unit-cost backends on a graph with `n` vertices.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### unitCostModel_isBoundedBy — theorem

*Source:* `Complexity.lean:840`; public

```lean
theorem unitCostModel_isBoundedBy [DecidableEq Vertex] (n : Nat) :
    (unitCostModel : CostModel Vertex).IsBoundedBy (unitCostBounds n) n
```

**Natural-language explanation.** The standard unit-cost models satisfy their concrete bounds.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type. The bound is pointwise over primitive operations; inspect the selected constants and size factors.

### modelWorkBound — def

*Source:* `Complexity.lean:847`; public

```lean
def modelWorkBound {G : Type u} (bounds : CostBounds) (model : ResourceModel G Vertex)
    (graph : G) : Nat
```

**Natural-language explanation.** Graph-wide BFS work expressed using arbitrary primitive-operation bounds.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### textbookConstant — def

*Source:* `Complexity.lean:854`; public

```lean
def textbookConstant (bounds : CostBounds) : Nat
```

**Natural-language explanation.** A single constant dominating all per-vertex and per-entry BFS work.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### exactCost_le_modelWork — theorem

*Source:* `Complexity.lean:862`; public

```lean
theorem exactCost_le_modelWork {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G)
    (costs : BoundedOperational.CostModel Vertex) (bounds : BoundedOperational.CostBounds)
    (hbounds : costs.IsBoundedBy bounds (model.vertexCount graph))
    (source : Vertex) (hsource : source ∈ model.interface.vertexSet graph) :
    exactCost (Interpreter.run model graph costs.control
        (BoundedOperational.visitedModel costs) (BoundedOperational.levelModel costs)
        (BoundedOperational.treeModel costs) source) ≤
      BoundedOperational.modelWorkBound bounds model graph
```

**Natural-language explanation.** The exact BFS trace is bounded under any operation costs satisfying `bounds`.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type. This concerns the sum of the abstract primitive measurements recorded in the trace. The bound is pointwise over primitive operations; inspect the selected constants and size factors.

### unitCost_le_modelWork — theorem

*Source:* `Complexity.lean:922`; public

```lean
theorem unitCost_le_modelWork {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (source : Vertex)
    (hsource : source ∈ model.interface.vertexSet graph) :
    exactCost (Interpreter.run model graph GraphTraversal.ControlCostModel.unit
        GraphTraversal.VisitedModel.booleanTable GraphTraversal.LevelModel.table
        GraphTraversal.TreeModel.edgeList source) ≤
      6 * model.vertexCount graph + model.adjacencyEntryCount graph +
        model.totalNeighborCost graph + 4
```

**Natural-language explanation.** The previous concrete bound is the unit-cost specialization of the generic theorem.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type. This concerns the sum of the abstract primitive measurements recorded in the trace.

### adjacencyList_exactCost_le — theorem

*Source:* `Complexity.lean:945`; public

```lean
theorem adjacencyList_exactCost_le {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (Γ : Interface G Vertex) (vertices : VertexEnumeration Γ) (neighbors : NeighborAccess Γ)
    (graph : G) (source : Vertex) (hsource : source ∈ Γ.vertexSet graph)
    (costs : BoundedOperational.CostModel Vertex) (bounds : BoundedOperational.CostBounds)
    (hbounds : costs.IsBoundedBy bounds
      ((ResourceModel.ofAdjacencyList Γ vertices neighbors).vertexCount graph))
    {m : Nat}
    (hentries : (ResourceModel.ofAdjacencyList Γ vertices neighbors).adjacencyEntryCount graph =
      2 * m) :
    exactCost (Interpreter.run (ResourceModel.ofAdjacencyList Γ vertices neighbors) graph
        costs.control (BoundedOperational.visitedModel costs)
        (BoundedOperational.levelModel costs) (BoundedOperational.treeModel costs) source) ≤
      BoundedOperational.initializationCost bounds +
        bounds.checkLayerEmpty *
          ((ResourceModel.ofAdjacencyList Γ vertices neighbors).vertexCount graph + 1) +
        2 * m + bounds.isVisited * (2 * m) +
          BoundedOperational.discoveryCost bounds *
            (ResourceModel.ofAdjacencyList Γ vertices neighbors).vertexCount graph
```

**Natural-language explanation.** Adjacency-list BFS under arbitrary bounded primitive-operation costs.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type. This concerns the sum of the abstract primitive measurements recorded in the trace. The bound is pointwise over primitive operations; inspect the selected constants and size factors.

### adjacencyMatrix_exactCost_le — theorem

*Source:* `Complexity.lean:969`; public

```lean
theorem adjacencyMatrix_exactCost_le {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (Γ : Interface G Vertex) (vertices : VertexEnumeration Γ)
    (edge : G → Vertex → Vertex → Bool)
    (edge_iff : ∀ graph source target, edge graph source target = true ↔
      Γ.Adj graph source target)
    (graph : G) (source : Vertex) (hsource : source ∈ Γ.vertexSet graph)
    (costs : BoundedOperational.CostModel Vertex) (bounds : BoundedOperational.CostBounds)
    (hbounds : costs.IsBoundedBy bounds
      ((ResourceModel.ofAdjacencyMatrix Γ vertices edge edge_iff).vertexCount graph)) :
    let model := ResourceModel.ofAdjacencyMatrix Γ vertices edge edge_iff
    exactCost (Interpreter.run model graph costs.control
        (BoundedOperational.visitedModel costs) (BoundedOperational.levelModel costs)
        (BoundedOperational.treeModel costs) source) ≤
      BoundedOperational.initializationCost bounds +
        bounds.checkLayerEmpty * (model.vertexCount graph + 1) +
        model.vertexCount graph * model.vertexCount graph +
        bounds.isVisited * (model.vertexCount graph * model.vertexCount graph) +
          BoundedOperational.discoveryCost bounds * model.vertexCount graph
```

**Natural-language explanation.** Adjacency-matrix BFS under arbitrary bounded primitive-operation costs.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type. This concerns the sum of the abstract primitive measurements recorded in the trace. The bound is pointwise over primitive operations; inspect the selected constants and size factors.

### adjacencyList_unitCost_le — theorem

*Source:* `Complexity.lean:1000`; public

```lean
theorem adjacencyList_unitCost_le {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (Γ : Interface G Vertex) (vertices : VertexEnumeration Γ) (neighbors : NeighborAccess Γ)
    (graph : G) (source : Vertex) (hsource : source ∈ Γ.vertexSet graph) {m : Nat}
    (hentries : (ResourceModel.ofAdjacencyList Γ vertices neighbors).adjacencyEntryCount graph =
      2 * m) :
    exactCost (Interpreter.run (ResourceModel.ofAdjacencyList Γ vertices neighbors) graph
        GraphTraversal.ControlCostModel.unit GraphTraversal.VisitedModel.booleanTable
        GraphTraversal.LevelModel.table
        GraphTraversal.TreeModel.edgeList source) ≤
      6 * (ResourceModel.ofAdjacencyList Γ vertices neighbors).vertexCount graph +
        4 * m + 4
```

**Natural-language explanation.** Unit-cost corollary for an undirected adjacency list.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type. This concerns the sum of the abstract primitive measurements recorded in the trace.

### adjacencyMatrix_unitCost_le — theorem

*Source:* `Complexity.lean:1017`; public

```lean
theorem adjacencyMatrix_unitCost_le {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (Γ : Interface G Vertex) (vertices : VertexEnumeration Γ)
    (edge : G → Vertex → Vertex → Bool)
    (edge_iff : ∀ graph source target, edge graph source target = true ↔
      Γ.Adj graph source target)
    (graph : G) (source : Vertex) (hsource : source ∈ Γ.vertexSet graph) :
    let model := ResourceModel.ofAdjacencyMatrix Γ vertices edge edge_iff
    exactCost (Interpreter.run model graph GraphTraversal.ControlCostModel.unit
        GraphTraversal.VisitedModel.booleanTable GraphTraversal.LevelModel.table
        GraphTraversal.TreeModel.edgeList source) ≤
      6 * model.vertexCount graph +
        2 * (model.vertexCount graph * model.vertexCount graph) + 4
```

**Natural-language explanation.** Unit-cost corollary for an adjacency matrix.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type. This concerns the sum of the abstract primitive measurements recorded in the trace.

### adjacencyListTime — def

*Source:* `Complexity.lean:1040`; public

```lean
def adjacencyListTime (n m : Nat) : Nat
```

**Natural-language explanation.** BFS accounting for an adjacency list: initialization plus two entries per edge.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### adjacencyMatrixTime — def

*Source:* `Complexity.lean:1044`; public

```lean
def adjacencyMatrixTime (n : Nat) : Nat
```

**Natural-language explanation.** BFS accounting for an adjacency matrix: initialization plus at most `n` row scans.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### adjacencyList_exactCost_le_textbook — theorem

*Source:* `Complexity.lean:1048`; public

```lean
theorem adjacencyList_exactCost_le_textbook
    {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (Γ : Interface G Vertex) (vertices : VertexEnumeration Γ) (neighbors : NeighborAccess Γ)
    (graph : G) (source : Vertex) (hsource : source ∈ Γ.vertexSet graph)
    (costs : BoundedOperational.CostModel Vertex) (bounds : BoundedOperational.CostBounds)
    (hbounds : costs.IsBoundedBy bounds
      ((ResourceModel.ofAdjacencyList Γ vertices neighbors).vertexCount graph))
    {m : Nat}
    (hentries : (ResourceModel.ofAdjacencyList Γ vertices neighbors).adjacencyEntryCount graph =
      2 * m) :
    exactCost (Interpreter.run (ResourceModel.ofAdjacencyList Γ vertices neighbors) graph
        costs.control (BoundedOperational.visitedModel costs)
        (BoundedOperational.levelModel costs) (BoundedOperational.treeModel costs) source) ≤
      BoundedOperational.initializationCost bounds +
        BoundedOperational.textbookConstant bounds * adjacencyListTime
          ((ResourceModel.ofAdjacencyList Γ vertices neighbors).vertexCount graph) m +
        bounds.checkLayerEmpty
```

**Natural-language explanation.** The arbitrary-cost adjacency-list trace is bounded by textbook work and supplied constants.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type. This concerns the sum of the abstract primitive measurements recorded in the trace. The bound is pointwise over primitive operations; inspect the selected constants and size factors.

### adjacencyList_unitCost_le_textbook — theorem

*Source:* `Complexity.lean:1073`; public

```lean
theorem adjacencyList_unitCost_le_textbook
    {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (Γ : Interface G Vertex) (vertices : VertexEnumeration Γ) (neighbors : NeighborAccess Γ)
    (graph : G) (source : Vertex) (hsource : source ∈ Γ.vertexSet graph) {m : Nat}
    (hentries : (ResourceModel.ofAdjacencyList Γ vertices neighbors).adjacencyEntryCount graph =
      2 * m) :
    exactCost (Interpreter.run (ResourceModel.ofAdjacencyList Γ vertices neighbors) graph
        GraphTraversal.ControlCostModel.unit GraphTraversal.VisitedModel.booleanTable
        GraphTraversal.LevelModel.table
        GraphTraversal.TreeModel.edgeList source) ≤
      6 * adjacencyListTime
        ((ResourceModel.ofAdjacencyList Γ vertices neighbors).vertexCount graph) m + 4
```

**Natural-language explanation.** Unit-cost specialization of the adjacency-list textbook bound.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type. This concerns the sum of the abstract primitive measurements recorded in the trace.

### adjacencyMatrix_exactCost_le_textbook — theorem

*Source:* `Complexity.lean:1090`; public

```lean
theorem adjacencyMatrix_exactCost_le_textbook
    {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (Γ : Interface G Vertex) (vertices : VertexEnumeration Γ)
    (edge : G → Vertex → Vertex → Bool)
    (edge_iff : ∀ graph source target, edge graph source target = true ↔
      Γ.Adj graph source target)
    (graph : G) (source : Vertex) (hsource : source ∈ Γ.vertexSet graph)
    (costs : BoundedOperational.CostModel Vertex) (bounds : BoundedOperational.CostBounds)
    (hbounds : costs.IsBoundedBy bounds
      ((ResourceModel.ofAdjacencyMatrix Γ vertices edge edge_iff).vertexCount graph)) :
    let model := ResourceModel.ofAdjacencyMatrix Γ vertices edge edge_iff
    exactCost (Interpreter.run model graph costs.control
        (BoundedOperational.visitedModel costs) (BoundedOperational.levelModel costs)
        (BoundedOperational.treeModel costs) source) ≤
      BoundedOperational.initializationCost bounds +
        BoundedOperational.textbookConstant bounds *
          adjacencyMatrixTime (model.vertexCount graph) + bounds.checkLayerEmpty
```

**Natural-language explanation.** The arbitrary-cost matrix trace is bounded by textbook work and supplied constants.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type. This concerns the sum of the abstract primitive measurements recorded in the trace. The bound is pointwise over primitive operations; inspect the selected constants and size factors.

### adjacencyMatrix_unitCost_le_textbook — theorem

*Source:* `Complexity.lean:1115`; public

```lean
theorem adjacencyMatrix_unitCost_le_textbook
    {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (Γ : Interface G Vertex) (vertices : VertexEnumeration Γ)
    (edge : G → Vertex → Vertex → Bool)
    (edge_iff : ∀ graph source target, edge graph source target = true ↔
      Γ.Adj graph source target)
    (graph : G) (source : Vertex) (hsource : source ∈ Γ.vertexSet graph) :
    let model := ResourceModel.ofAdjacencyMatrix Γ vertices edge edge_iff
    exactCost (Interpreter.run model graph GraphTraversal.ControlCostModel.unit
        GraphTraversal.VisitedModel.booleanTable GraphTraversal.LevelModel.table
        GraphTraversal.TreeModel.edgeList source) ≤
      6 * adjacencyMatrixTime (model.vertexCount graph) + 4
```

**Natural-language explanation.** Unit-cost specialization of the adjacency-matrix textbook bound.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type. This concerns the sum of the abstract primitive measurements recorded in the trace.

### adjacencyListTime_isBigO — theorem

*Source:* `Complexity.lean:1132`; public

```lean
theorem adjacencyListTime_isBigO :
    (fun nm : Nat × Nat ↦ (adjacencyListTime nm.1 nm.2 : Real)) =O[atTop]
      fun nm ↦ (nm.2 : Real) + nm.1
```

**Natural-language explanation.** Kleinberg theorem (3.11): adjacency-list BFS runs in `O(m + n)` time.

**Audit focus.** This is an asymptotic upper bound, so multiplicative constants and a finite prefix are hidden.

### adjacencyMatrixTime_isBigO — theorem

*Source:* `Complexity.lean:1138`; public

```lean
theorem adjacencyMatrixTime_isBigO :
    (fun n : Nat ↦ (adjacencyMatrixTime n : Real)) =O[atTop]
      fun n ↦ (n : Real) ^ 2
```

**Natural-language explanation.** With an adjacency matrix, BFS runs in `O(n²)` time.

**Audit focus.** This is an asymptotic upper bound, so multiplicative constants and a finite prefix are hidden.

### timeComplexities — theorem

*Source:* `Complexity.lean:1144`; public

```lean
theorem timeComplexities :
    ((fun nm : Nat × Nat ↦ (adjacencyListTime nm.1 nm.2 : Real)) =O[atTop]
      fun nm ↦ (nm.2 : Real) + nm.1) ∧
    ((fun n : Nat ↦ (adjacencyMatrixTime n : Real)) =O[atTop]
      fun n ↦ (n : Real) ^ 2)
```

**Natural-language explanation.** The adjacency-list and adjacency-matrix BFS bounds, packaged together.

**Audit focus.** This is an asymptotic upper bound, so multiplicative constants and a finite prefix are hidden.

# Audit completion checklist {#audit-completion-checklist}

[Back to contents](#contents)

- Confirm the layer-based program matches the intended textbook BFS pseudocode.
- Confirm every termination argument is understood through the displayed fuel or graph-size hypotheses.
- Check which correctness claims concern the executed BFS state and which concern separately constructed graph certificates.
- Confirm source-membership, graph-interface, finiteness, connectedness, and undirectedness assumptions are not omitted in the informal reading.
- Check that adjacency-list and adjacency-matrix cost claims use their intended neighbor-access and storage models.
- Treat exact trace cost, weighted operation cost, unit cost, and asymptotic textbook time as distinct quantities.
- Record any mismatch as one of: missing hypothesis, stronger or weaker conclusion, wrong semantic interpretation, wrong cost interpretation, wrong quantification domain, or unsupported textbook attribution.

# Source inventory {#source-inventory}

- `Algorithm.lean`: The free program and its algorithm-specific recursive helpers.
- `ResourceModel.lean`: The selected semantic backends, cost interpretation, runner, and space model.
- `Correctness.lean`: Semantic correctness of completed runs and the case study's graph-theoretic consequences.
- `Complexity.lean`: Cost-independent operation profiles, exact-cost transfers, closed bounds, and asymptotic endpoints.
