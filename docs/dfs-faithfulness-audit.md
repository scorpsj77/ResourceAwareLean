---
title: "Depth-First Search Formalization"
subtitle: "Declaration Headers and Natural-Language Faithfulness Audit"
author: "Generated from Resource-Aware-CSLib source"
date: "12 August 2026"
---

**Audit purpose.** This dossier places every `def` and `theorem` header from the modular DFS formalization next to a statement-level natural-language reading. It is designed for a manual check of whether the Lean claim matches the intended textbook claim.

**Snapshot.** Commit `6194a4137cb8d4f2c2b57ca939e607161a541784`; formalization sources inspected on 12 August 2026. Source locations are line-based and may drift after edits.

**Coverage.** 65 declarations (65 public, 0 private). Declarations written with `abbrev`, `structure`, or `inductive`, along with proof bodies, namespace commands, imports, and executable examples, are intentionally excluded.

**How to audit an entry.** Check (1) quantified inputs and type-class assumptions, (2) graph, size, representation, or cost hypotheses, (3) the exact conclusion, and (4) which semantic or resource interpretation is being measured. The prose explains the statement; it does not claim more than the displayed header.

# Contents {#contents}

- [High-level faithfulness guide](#high-level-faithfulness-guide)
  - [Important scope boundaries](#important-scope-boundaries)
  - [Notation used in the headers](#notation-used-in-the-headers)
- [Algorithm: abstract program](#algorithm) (3 declarations)
- [Resource model, semantics, and runners](#resourcemodel) (6 declarations)
- [Correctness and graph-theoretic certificates](#correctness) (15 declarations)
- [Complexity and resource bounds](#complexity) (41 declarations)
- [Audit completion checklist](#audit-completion-checklist)
- [Source inventory](#source-inventory)

# High-level faithfulness guide {#high-level-faithfulness-guide}

The formalization uses an iterative, stack-based free program interpreted by the shared graph-traversal framework. Its completed Boolean-table execution is connected to exact reachability. The recursive DFS-tree edge/ancestor results are stated through an abstract semantic certificate, while the complexity development derives separate adjacency-list and adjacency-matrix bounds from one cost-independent operation profile.

## Important scope boundaries {#important-scope-boundaries}

- The executable DFS is fuel-bounded by stack pops. `Interpreter.run` uses `1 + m`, where `m` is the model's adjacency-entry count.
- Neighbors are pushed onto the front of the stack in reverse order; traversal order therefore depends on the graph model's returned neighbor order.
- The standard correctness run uses a Boolean visited backend and discards level and tree state.
- The theorem that the run visits exactly the reachable vertices is about the completed bounded run and includes the graph-interface/source assumptions shown in its header.
- The recursive DFS-tree theorems are conditional on `RecursiveTreeCertificate`; they do not claim that the iterative program constructs that certificate.
- Adjacency-list bounds use `n + m`; adjacency-matrix bounds use `n²`. Exact, weighted, unit, and asymptotic costs remain distinct.

## Notation used in the headers {#notation-used-in-the-headers}

- `TraceM (Event V) α`: a deterministic result paired with an ordered trace of measured graph-traversal events.
- `.ret`: the returned value of a trace computation; for runs, `.ret.2` is the final product state.
- `ResourceModel G V`: graph interface, neighbor-access behavior, sizes, and representation-dependent resource data for graphs of type `G`.
- `n` and `m`: the model's vertex count and adjacency-entry count in the textbook bounds.
- `weightedOperationCost charge run`: the sum of user-supplied charges over the run's operation trace.
- `IsBoundedBy`: a pointwise assertion that exact primitive measurements do not exceed declared primitive bounds.
- `RecursiveTreeCertificate`: an abstract certificate for the semantic laws of recursive DFS, separate from the iterative runner's returned state.
- `=O[atTop]`: asymptotic big-O as natural input sizes tend to infinity.

# Algorithm: abstract program {#algorithm}

[Back to contents](#contents)

**Source file:** `TextbookAlgorithms/KleinbergTardos/Chapter03/DFS/Algorithm.lean`  
**Declarations in this section:** 3

The free program and its algorithm-specific recursive helpers.

### pushNeighbors — def

*Source:* `Algorithm.lean:36`; public

```lean
def pushNeighbors : List Vertex → List Vertex → List Vertex
```

**Natural-language explanation.** Push every neighbor onto the stack. The head of the list is the stack top.  Processing neighbors left-to-right with cons-style pushes means the last neighbor in the list is popped first.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### dfsLoop — def

*Source:* `Algorithm.lean:44`; public

```lean
def dfsLoop : Nat → List Vertex → Program Vertex PUnit
```

**Natural-language explanation.** Repeatedly pop a vertex from the stack.  If it has not been explored, mark it explored and push all of its neighbors.  Fuel is a stack-pop bound supplied by a finite graph model.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### dfs — def

*Source:* `Algorithm.lean:73`; public

```lean
def dfs (stackPopBound : Nat) (source : Vertex) : Program Vertex PUnit
```

**Natural-language explanation.** Run Kleinberg's DFS from `source`. `stackPopBound` is termination fuel.  For a finite graph, `1 + m` is enough for this textbook variant because each explored vertex pushes its outgoing adjacency list once.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.


# Resource model, semantics, and runners {#resourcemodel}

[Back to contents](#contents)

**Source file:** `TextbookAlgorithms/KleinbergTardos/Chapter03/DFS/ResourceModel.lean`  
**Declarations in this section:** 6

The selected semantic backends, cost interpretation, runner, and space model.

### stackPopBound — def

*Source:* `ResourceModel.lean:33`; public

```lean
def stackPopBound {G : Type u} (model : ResourceModel G Vertex) (graph : G) : Nat
```

**Natural-language explanation.** A finite upper bound on stack pops for the textbook DFS variant.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### runWithBound — def

*Source:* `ResourceModel.lean:41`; public

```lean
def runWithBound {G : Type u} (model : ResourceModel G Vertex) (graph : G)
    (control : GraphTraversal.ControlCostModel)
    (visited : GraphTraversal.VisitedModel Vertex VisitedState)
    (stackPopBound : Nat) (source : Vertex) :
    TraceM (Event Vertex) (PUnit × State VisitedState)
```

**Natural-language explanation.** Run Kleinberg DFS with explicit stack-pop fuel.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### run — def

*Source:* `ResourceModel.lean:50`; public

```lean
def run {G : Type u} (model : ResourceModel G Vertex) (graph : G)
    (control : GraphTraversal.ControlCostModel)
    (visited : GraphTraversal.VisitedModel Vertex VisitedState) (source : Vertex) :
    TraceM (Event Vertex) (PUnit × State VisitedState)
```

**Natural-language explanation.** Use `1 + m` from the graph model as termination fuel.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### exactCost — def

*Source:* `ResourceModel.lean:59`; public

```lean
def exactCost (computation : TraceM (Event Vertex) α) : Nat
```

**Natural-language explanation.** Sum the measured primitive work in a completed DFS trace.

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
    (visited : GraphTraversal.VisitedModel Vertex VisitedState) : SpaceUsage
```

**Natural-language explanation.** Add explored-state storage to the conservative `1 + m` stack-storage bound.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.


# Correctness and graph-theoretic certificates {#correctness}

[Back to contents](#contents)

**Source file:** `TextbookAlgorithms/KleinbergTardos/Chapter03/DFS/Correctness.lean`  
**Declarations in this section:** 15

Semantic correctness of completed runs and the case study's graph-theoretic consequences.

### pushNeighbors_eq_reverse_append — theorem

*Source:* `Correctness.lean:23`; public

```lean
theorem pushNeighbors_eq_reverse_append (neighbors stack : List Vertex) :
    pushNeighbors neighbors stack = neighbors.reverse ++ stack
```

**Natural-language explanation.** Pushing neighbors left-to-right places their reverse in front of the old stack.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### length_pushNeighbors — theorem

*Source:* `Correctness.lean:31`; public

```lean
theorem length_pushNeighbors (neighbors stack : List Vertex) :
    (pushNeighbors neighbors stack).length = neighbors.length + stack.length
```

**Natural-language explanation.** Pushing neighbors increases stack length by exactly the number of neighbors.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### run_visited_eq_loopResult — theorem

*Source:* `Correctness.lean:38`; public

```lean
theorem run_visited_eq_loopResult {G : Type u} {V : Type v} [DecidableEq V]
    (model : ResourceModel G V) (graph : G) (source : V) :
    (Interpreter.run model graph GraphTraversal.ControlCostModel.unit
      GraphTraversal.VisitedModel.booleanTable source).ret.2.visited =
      (Operational.loopResult model graph (stackPopBound model graph) [source]
        (fun _ ↦ false)).visited
```

**Natural-language explanation.** The public Boolean-table runner has the pure visited-state recurrence used below.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### finalStack — def

*Source:* `Correctness.lean:60`; public

```lean
def finalStack {G : Type u} {V : Type v} [DecidableEq V]
    (model : ResourceModel G V) (graph : G) :
    Nat → List V → (V → Bool) → List V
```

**Natural-language explanation.** Stack remaining when DFS stops, including premature fuel exhaustion.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### loopResult_visited_iff_initial_or_queried — theorem

*Source:* `Correctness.lean:74`; public

```lean
theorem loopResult_visited_iff_initial_or_queried {G : Type u} {V : Type v}
    [DecidableEq V] (model : ResourceModel G V) (graph : G)
    (fuel : Nat) (stack : List V) (visited : V → Bool) (vertex : V) :
    (loopResult model graph fuel stack visited).visited vertex = true ↔
      visited vertex = true ∨ vertex ∈ (loopResult model graph fuel stack visited).queried
```

**Natural-language explanation.** DFS only preserves old bits and marks the vertices in its query list.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### mem_stack_visited_or_finalStack — theorem

*Source:* `Correctness.lean:93`; public

```lean
theorem mem_stack_visited_or_finalStack {G : Type u} {V : Type v}
    [DecidableEq V] (model : ResourceModel G V) (graph : G)
    (fuel : Nat) (stack : List V) (visited : V → Bool) {vertex : V}
    (hvertex : vertex ∈ stack) :
    (loopResult model graph fuel stack visited).visited vertex = true ∨
      vertex ∈ finalStack model graph fuel stack visited
```

**Natural-language explanation.** Every initially pending vertex is eventually visited or remains on the terminal stack.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### loopResult_reachable — theorem

*Source:* `Correctness.lean:127`; public

```lean
theorem loopResult_reachable {G : Type u} {V : Type v} [DecidableEq V]
    (model : ResourceModel G V) (graph : G) (source : V)
    (fuel : Nat) (stack : List V) (visited : V → Bool)
    (hvisited : ∀ {vertex}, visited vertex = true →
      Reachable model.interface graph source vertex)
    (hstack : ∀ {vertex}, vertex ∈ stack →
      Reachable model.interface graph source vertex) :
    ∀ {vertex}, (loopResult model graph fuel stack visited).visited vertex = true →
      Reachable model.interface graph source vertex
```

**Natural-language explanation.** Every queried vertex is reachable when the initial stack and bits are reachable.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### fuel_add_finalStack_length — theorem

*Source:* `Correctness.lean:169`; public

```lean
theorem fuel_add_finalStack_length {G : Type u} {V : Type v} [DecidableEq V]
    (model : ResourceModel G V) (graph : G)
    (fuel : Nat) (stack : List V) (visited : V → Bool)
    (hnonempty : finalStack model graph fuel stack visited ≠ []) :
    fuel + (finalStack model graph fuel stack visited).length =
      stack.length + ((loopResult model graph fuel stack visited).queried.map fun vertex ↦
        (model.neighborAccess.outNeighbors graph vertex).length).sum
```

**Natural-language explanation.** A nonempty terminal stack accounts exactly for all fuel-consuming pops.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### finalStack_eq_nil — theorem

*Source:* `Correctness.lean:196`; public

```lean
theorem finalStack_eq_nil {G : Type u} {V : Type v} [DecidableEq V]
    (model : ResourceModel G V) (graph : G) (source : V)
    (hsource : source ∈ model.interface.vertexSet graph) :
    finalStack model graph (stackPopBound model graph) [source] (fun _ ↦ false) = []
```

**Natural-language explanation.** The textbook `1 + m` pop bound cannot leave a nonempty DFS stack.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### loopResult_visits_queried_neighbors — theorem

*Source:* `Correctness.lean:222`; public

```lean
theorem loopResult_visits_queried_neighbors {G : Type u} {V : Type v}
    [DecidableEq V] (model : ResourceModel G V) (graph : G)
    (fuel : Nat) (stack : List V) (visited : V → Bool) {parent child : V}
    (hfinal : finalStack model graph fuel stack visited = [])
    (hparent : parent ∈ (loopResult model graph fuel stack visited).queried)
    (hchild : child ∈ model.neighborAccess.outNeighbors graph parent) :
    (loopResult model graph fuel stack visited).visited child = true
```

**Natural-language explanation.** Once the terminal stack is empty, all neighbors of every queried vertex are visited.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### loopResult_visitsExactlyReachable — theorem

*Source:* `Correctness.lean:261`; public

```lean
theorem loopResult_visitsExactlyReachable {G : Type u} {V : Type v} [DecidableEq V]
    (model : ResourceModel G V) (graph : G) (source : V)
    (hsource : source ∈ model.interface.vertexSet graph) :
    GraphTraversal.VisitsExactlyReachable model.interface graph source fun vertex ↦
      (loopResult model graph (stackPopBound model graph) [source]
        (fun _ ↦ false)).visited vertex = true
```

**Natural-language explanation.** The Boolean-table DFS recurrence visits exactly the vertices reachable from its source.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### run_visitsExactlyReachable — theorem

*Source:* `Correctness.lean:296`; public

```lean
theorem run_visitsExactlyReachable {G : Type u} {V : Type v} [DecidableEq V]
    (model : ResourceModel G V) (graph : G) (source : V)
    (hsource : source ∈ model.interface.vertexSet graph) :
    GraphTraversal.VisitsExactlyReachable model.interface graph source fun vertex ↦
      (Interpreter.run model graph GraphTraversal.ControlCostModel.unit
        GraphTraversal.VisitedModel.booleanTable source).ret.2.visited vertex = true
```

**Natural-language explanation.** Executable DFS with the standard Boolean table visits exactly the reachable vertices.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### IsAncestor — def

*Source:* `Correctness.lean:310`; public

```lean
def IsAncestor (tree : SimpleGraph V) (root ancestor descendant : V) : Prop
```

**Natural-language explanation.** A vertex is an ancestor when it lies on a simple tree path from the root.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### RecursiveTreeCertificate.edge_ancestor — theorem

*Source:* `Correctness.lean:329`; public

```lean
theorem RecursiveTreeCertificate.edge_ancestor {h : Γ.IsUndirected g} {root x y : V}
    (dfs : RecursiveTreeCertificate h root) (hxy : Γ.Adj g x y) :
    IsAncestor dfs.tree root x y ∨ IsAncestor dfs.tree root y x
```

**Natural-language explanation.** Every graph edge in a recursive DFS tree joins an ancestor-descendant pair.

**Audit focus.** Check the exact role of the displayed undirectedness certificate.

### RecursiveTreeCertificate.nonTreeEdge_ancestor — theorem

*Source:* `Correctness.lean:343`; public

```lean
theorem RecursiveTreeCertificate.nonTreeEdge_ancestor {h : Γ.IsUndirected g}
    {root x y : V} (dfs : RecursiveTreeCertificate h root)
    (hxy : Γ.Adj g x y) (_hnotTree : ¬dfs.tree.Adj x y) :
    IsAncestor dfs.tree root x y ∨ IsAncestor dfs.tree root y x
```

**Natural-language explanation.** Kleinberg--Tardos theorem 3.7 for a non-tree edge of a recursive DFS tree.

**Audit focus.** Check the exact role of the displayed undirectedness certificate.


# Complexity and resource bounds {#complexity}

[Back to contents](#contents)

**Source file:** `TextbookAlgorithms/KleinbergTardos/Chapter03/DFS/Complexity.lean`  
**Declarations in this section:** 41

Cost-independent operation profiles, exact-cost transfers, closed bounds, and asymptotic endpoints.

### execute — def

*Source:* `Complexity.lean:36`; public

```lean
def execute {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G)
    (program : GraphTraversal.Program Vertex α) (state : State Vertex) :
    TraceM (GraphTraversal.Event Vertex) (α × State Vertex)
```

**Natural-language explanation.** Execute a DFS program from an arbitrary Boolean-table interpreter state.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### execute_pure — theorem

*Source:* `Complexity.lean:45`; public; attributes: `@[simp]`

```lean
@[simp]
theorem execute_pure {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (value : α) (state : State Vertex) :
    execute model graph (pure value) state = pure (value, state)
```

**Natural-language explanation.** Executing a pure return yields that value with the state unchanged and emits no event.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### execute_bind — theorem

*Source:* `Complexity.lean:50`; public

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

### execute_checkStackEmpty — theorem

*Source:* `Complexity.lean:60`; public; attributes: `@[simp]`

```lean
@[simp]
theorem execute_checkStackEmpty {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (state : State Vertex) :
    execute model graph GraphTraversal.checkStackEmpty state =
      ⟨(.unit, state), EventTrace.singleton ⟨.checkStackEmpty, 1⟩⟩
```

**Natural-language explanation.** The standard interpreter executes a stack-empty check without changing state and records one unit-cost event.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### execute_isVisited — theorem

*Source:* `Complexity.lean:67`; public; attributes: `@[simp]`

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

*Source:* `Complexity.lean:75`; public; attributes: `@[simp]`

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

### execute_neighbors — theorem

*Source:* `Complexity.lean:83`; public; attributes: `@[simp]`

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

*Source:* `Complexity.lean:91`; public; attributes: `@[simp]`

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

### loopResult — def

*Source:* `Complexity.lean:104`; public

```lean
def loopResult {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) :
    Nat → List Vertex → (Vertex → Bool) → LoopResult Vertex
```

**Natural-language explanation.** The semantic recurrence implemented by Boolean-table DFS trace interpretation.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### loopOperationCharge — def

*Source:* `Complexity.lean:121`; public

```lean
def loopOperationCharge {G : Type u} (model : ResourceModel G Vertex) (graph : G)
    (checkStackEmpty isVisited markVisited : Nat) (other : GraphTraversal.Op Vertex → Nat) :
    GraphTraversal.Op Vertex → Nat
```

**Natural-language explanation.** Cost-independent weights used to summarize a DFS-loop operation profile.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### dfsLoop_weightedOperationCost_le — theorem

*Source:* `Complexity.lean:132`; public

```lean
theorem dfsLoop_weightedOperationCost_le {G : Type u} {Vertex : Type v}
    [DecidableEq Vertex] (model : ResourceModel G Vertex) (graph : G)
    (checkStackEmpty isVisited markVisited : Nat) (fuel : Nat) (stack : List Vertex)
    (state : State Vertex) (other : GraphTraversal.Op Vertex → Nat) :
    let expected := loopResult model graph fuel stack state.visited
    let actual := execute model graph (dfsLoop fuel stack) state
    actual.ret.2.visited = expected.visited ∧
      ResourceAware.Program.weightedOperationCost
          (loopOperationCharge model graph checkStackEmpty isVisited markVisited other) actual ≤
        (checkStackEmpty + isVisited) * fuel + checkStackEmpty +
          markVisited * expected.queried.length +
            (expected.queried.map fun vertex ↦ model.neighborCost graph vertex).sum
```

**Natural-language explanation.** One cost-independent DFS operation-profile proof, reusable under every bounded cost model.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type. This concerns a weighted operation profile, which is not automatically the trace's exact measured cost.

### mem_pushNeighbors — theorem

*Source:* `Complexity.lean:195`; public

```lean
theorem mem_pushNeighbors {vertex : Vertex} (neighbors stack : List Vertex) :
    vertex ∈ pushNeighbors neighbors stack ↔ vertex ∈ neighbors ∨ vertex ∈ stack
```

**Natural-language explanation.** Membership after pushing neighbors is membership in the neighbors or the old stack.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### loopResult_visited_and_nodup — theorem

*Source:* `Complexity.lean:206`; public

```lean
theorem loopResult_visited_and_nodup {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (fuel : Nat) (stack : List Vertex)
    (visited : Vertex → Bool) :
    let result := loopResult model graph fuel stack visited
    (∀ vertex, visited vertex = true → result.visited vertex = true) ∧
      (∀ vertex ∈ result.queried, visited vertex = false) ∧ result.queried.Nodup
```

**Natural-language explanation.** DFS only turns visited bits on; queried vertices were initially unvisited and are unique.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### loopResult_queried_mem_vertices — theorem

*Source:* `Complexity.lean:239`; public

```lean
theorem loopResult_queried_mem_vertices {G : Type u} {Vertex : Type v}
    [DecidableEq Vertex] (model : ResourceModel G Vertex) (graph : G)
    (fuel : Nat) (stack : List Vertex) (visited : Vertex → Bool)
    (hstack : ∀ vertex ∈ stack, vertex ∈ model.vertexEnumeration.vertices graph) :
    ∀ vertex ∈ (loopResult model graph fuel stack visited).queried,
      vertex ∈ model.vertexEnumeration.vertices graph
```

**Natural-language explanation.** Every queried vertex belongs to the verified finite vertex enumeration.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### visitedModel — def

*Source:* `Complexity.lean:295`; public

```lean
def visitedModel [DecidableEq Vertex] (costs : CostModel Vertex) :
    GraphTraversal.VisitedModel Vertex (Vertex → Bool)
```

**Natural-language explanation.** Standard Boolean-table semantics equipped with arbitrary visited-operation costs.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### execute — def

*Source:* `Complexity.lean:301`; public

```lean
def execute {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (costs : CostModel Vertex)
    (program : GraphTraversal.Program Vertex α) (state : Operational.State Vertex) :
    TraceM (GraphTraversal.Event Vertex) (α × Operational.State Vertex)
```

**Natural-language explanation.** Execute DFS with the standard backend and arbitrary operation costs.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### popCost — def

*Source:* `Complexity.lean:310`; public

```lean
def popCost (bounds : CostBounds) : Nat
```

**Natural-language explanation.** Upper-bound cost of the check and visited test performed on every stack pop.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### otherOperationCharge — def

*Source:* `Complexity.lean:314`; public

```lean
def otherOperationCharge (costs : CostModel Vertex) (bounds : CostBounds) :
    GraphTraversal.Op Vertex → Nat
```

**Natural-language explanation.** Weights for all operations; the DFS profile uses only the four bounded cases and neighbors.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### operationCharge — def

*Source:* `Complexity.lean:325`; public

```lean
def operationCharge {G : Type u} (model : ResourceModel G Vertex) (graph : G)
    (costs : CostModel Vertex) (bounds : CostBounds) : GraphTraversal.Op Vertex → Nat
```

**Natural-language explanation.** The operation weights used to reinterpret the cost-independent DFS profile.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### interpreter_isBoundedBy — theorem

*Source:* `Complexity.lean:332`; public

```lean
theorem interpreter_isBoundedBy {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (costs : CostModel Vertex)
    (bounds : CostBounds) (hbounds : costs.IsBoundedBy bounds (model.vertexCount graph)) :
    GraphTraversal.Model.IsBoundedBy model graph costs.control
      (visitedModel costs) GraphTraversal.LevelModel.discard GraphTraversal.TreeModel.discard
      (operationCharge model graph costs bounds)
```

**Natural-language explanation.** Primitive cost assumptions are discharged once when constructing the generic interpreter bound, rather than inside every recursive DFS proof.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type. The bound is pointwise over primitive operations; inspect the selected constants and size factors.

### exactCost_run_le — theorem

*Source:* `Complexity.lean:364`; public

```lean
theorem exactCost_run_le {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (costs : CostModel Vertex)
    (bounds : CostBounds) (hbounds : costs.IsBoundedBy bounds (model.vertexCount graph))
    (source : Vertex) :
    let result := Operational.loopResult model graph (stackPopBound model graph) [source]
      (fun _ ↦ false)
    KleinbergDFS.exactCost
        (KleinbergDFS.Interpreter.run model graph costs.control (visitedModel costs) source) ≤
      bounds.clearVisited + popCost bounds * stackPopBound model graph +
        bounds.checkStackEmpty + bounds.markVisited * result.queried.length +
          (result.queried.map fun vertex ↦ model.neighborCost graph vertex).sum
```

**Natural-language explanation.** The public DFS runner obeys arbitrary supplied upper bounds for primitive costs.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type. This concerns the sum of the abstract primitive measurements recorded in the trace. The bound is pointwise over primitive operations; inspect the selected constants and size factors.

### unitCostModel — def

*Source:* `Complexity.lean:440`; public

```lean
def unitCostModel [DecidableEq Vertex] : CostModel Vertex
```

**Natural-language explanation.** Unit-cost instance used only to recover the traditional concrete DFS corollaries.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type.

### unitCostBounds — def

*Source:* `Complexity.lean:445`; public

```lean
def unitCostBounds (n : Nat) : CostBounds
```

**Natural-language explanation.** Bounds realized by the standard unit-cost DFS backends on an `n`-vertex graph.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### unitCostModel_isBoundedBy — theorem

*Source:* `Complexity.lean:452`; public

```lean
theorem unitCostModel_isBoundedBy [DecidableEq Vertex] (n : Nat) :
    (unitCostModel : CostModel Vertex).IsBoundedBy (unitCostBounds n) n
```

**Natural-language explanation.** The standard DFS models satisfy their unit-cost bounds.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type. The bound is pointwise over primitive operations; inspect the selected constants and size factors.

### modelWorkBound — def

*Source:* `Complexity.lean:458`; public

```lean
def modelWorkBound {G : Type u} (bounds : CostBounds) (model : ResourceModel G Vertex)
    (graph : G) : Nat
```

**Natural-language explanation.** Graph-wide DFS work expressed using arbitrary primitive-operation bounds.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### textbookConstant — def

*Source:* `Complexity.lean:465`; public

```lean
def textbookConstant (bounds : CostBounds) : Nat
```

**Natural-language explanation.** A single constant dominating all per-vertex and per-entry DFS work.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### exactCost_le_modelWork — theorem

*Source:* `Complexity.lean:473`; public

```lean
theorem exactCost_le_modelWork {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G)
    (costs : BoundedOperational.CostModel Vertex) (bounds : BoundedOperational.CostBounds)
    (hbounds : costs.IsBoundedBy bounds (model.vertexCount graph))
    (source : Vertex) (hsource : source ∈ model.interface.vertexSet graph) :
    exactCost (Interpreter.run model graph costs.control
        (BoundedOperational.visitedModel costs) source) ≤
      BoundedOperational.modelWorkBound bounds model graph
```

**Natural-language explanation.** The exact DFS trace is bounded under any operation costs satisfying `bounds`.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type. This concerns the sum of the abstract primitive measurements recorded in the trace. The bound is pointwise over primitive operations; inspect the selected constants and size factors.

### unitCost_le_modelWork — theorem

*Source:* `Complexity.lean:509`; public

```lean
theorem unitCost_le_modelWork {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (source : Vertex)
    (hsource : source ∈ model.interface.vertexSet graph) :
    exactCost (Interpreter.run model graph GraphTraversal.ControlCostModel.unit
        GraphTraversal.VisitedModel.booleanTable source) ≤
      2 * model.vertexCount graph + 2 * model.adjacencyEntryCount graph +
        model.totalNeighborCost graph + 3
```

**Natural-language explanation.** The previous concrete bound is the unit-cost specialization of the generic theorem.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type. This concerns the sum of the abstract primitive measurements recorded in the trace.

### adjacencyList_exactCost_le — theorem

*Source:* `Complexity.lean:530`; public

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
        costs.control (BoundedOperational.visitedModel costs) source) ≤
      bounds.clearVisited + BoundedOperational.popCost bounds * (2 * m + 1) +
        bounds.checkStackEmpty + bounds.markVisited *
          (ResourceModel.ofAdjacencyList Γ vertices neighbors).vertexCount graph + 2 * m
```

**Natural-language explanation.** Adjacency-list DFS under arbitrary bounded primitive-operation costs.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type. This concerns the sum of the abstract primitive measurements recorded in the trace. The bound is pointwise over primitive operations; inspect the selected constants and size factors.

### adjacencyMatrix_exactCost_le — theorem

*Source:* `Complexity.lean:550`; public

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
        (BoundedOperational.visitedModel costs) source) ≤
      bounds.clearVisited +
        BoundedOperational.popCost bounds *
          (model.vertexCount graph * model.vertexCount graph + 1) +
        bounds.checkStackEmpty + bounds.markVisited * model.vertexCount graph +
          model.vertexCount graph * model.vertexCount graph
```

**Natural-language explanation.** Adjacency-matrix DFS under arbitrary bounded primitive-operation costs.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type. This concerns the sum of the abstract primitive measurements recorded in the trace. The bound is pointwise over primitive operations; inspect the selected constants and size factors.

### adjacencyList_unitCost_le — theorem

*Source:* `Complexity.lean:580`; public

```lean
theorem adjacencyList_unitCost_le {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (Γ : Interface G Vertex) (vertices : VertexEnumeration Γ) (neighbors : NeighborAccess Γ)
    (graph : G) (source : Vertex) (hsource : source ∈ Γ.vertexSet graph) {m : Nat}
    (hentries : (ResourceModel.ofAdjacencyList Γ vertices neighbors).adjacencyEntryCount graph =
      2 * m) :
    exactCost (Interpreter.run (ResourceModel.ofAdjacencyList Γ vertices neighbors) graph
        GraphTraversal.ControlCostModel.unit GraphTraversal.VisitedModel.booleanTable source) ≤
      2 * (ResourceModel.ofAdjacencyList Γ vertices neighbors).vertexCount graph +
        6 * m + 3
```

**Natural-language explanation.** Unit-cost corollary for an undirected adjacency list.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type. This concerns the sum of the abstract primitive measurements recorded in the trace.

### adjacencyMatrix_unitCost_le — theorem

*Source:* `Complexity.lean:595`; public

```lean
theorem adjacencyMatrix_unitCost_le {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (Γ : Interface G Vertex) (vertices : VertexEnumeration Γ)
    (edge : G → Vertex → Vertex → Bool)
    (edge_iff : ∀ graph source target, edge graph source target = true ↔
      Γ.Adj graph source target)
    (graph : G) (source : Vertex) (hsource : source ∈ Γ.vertexSet graph) :
    let model := ResourceModel.ofAdjacencyMatrix Γ vertices edge edge_iff
    exactCost (Interpreter.run model graph GraphTraversal.ControlCostModel.unit
        GraphTraversal.VisitedModel.booleanTable source) ≤
      2 * model.vertexCount graph +
        3 * (model.vertexCount graph * model.vertexCount graph) + 3
```

**Natural-language explanation.** Unit-cost corollary for an adjacency matrix.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type. This concerns the sum of the abstract primitive measurements recorded in the trace.

### adjacencyListTime — def

*Source:* `Complexity.lean:617`; public

```lean
def adjacencyListTime (n m : Nat) : Nat
```

**Natural-language explanation.** DFS accounting for an adjacency list: initialization plus work linear in its entries.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### adjacencyMatrixTime — def

*Source:* `Complexity.lean:621`; public

```lean
def adjacencyMatrixTime (n : Nat) : Nat
```

**Natural-language explanation.** DFS accounting for an adjacency matrix: initialization plus at most `n` row scans.

**Audit focus.** Check the quantified inputs, hypotheses, and conclusion exactly as displayed; the prose does not strengthen the Lean statement.

### adjacencyList_exactCost_le_textbook — theorem

*Source:* `Complexity.lean:625`; public

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
        costs.control (BoundedOperational.visitedModel costs) source) ≤
      bounds.clearVisited +
        BoundedOperational.textbookConstant bounds * adjacencyListTime
          ((ResourceModel.ofAdjacencyList Γ vertices neighbors).vertexCount graph) m +
        BoundedOperational.popCost bounds + bounds.checkStackEmpty
```

**Natural-language explanation.** The arbitrary-cost adjacency-list trace is bounded by textbook work and supplied constants.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type. This concerns the sum of the abstract primitive measurements recorded in the trace. The bound is pointwise over primitive operations; inspect the selected constants and size factors.

### adjacencyList_unitCost_le_textbook — theorem

*Source:* `Complexity.lean:649`; public

```lean
theorem adjacencyList_unitCost_le_textbook
    {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (Γ : Interface G Vertex) (vertices : VertexEnumeration Γ) (neighbors : NeighborAccess Γ)
    (graph : G) (source : Vertex) (hsource : source ∈ Γ.vertexSet graph) {m : Nat}
    (hentries : (ResourceModel.ofAdjacencyList Γ vertices neighbors).adjacencyEntryCount graph =
      2 * m) :
    exactCost (Interpreter.run (ResourceModel.ofAdjacencyList Γ vertices neighbors) graph
        GraphTraversal.ControlCostModel.unit GraphTraversal.VisitedModel.booleanTable source) ≤
      3 * adjacencyListTime
        ((ResourceModel.ofAdjacencyList Γ vertices neighbors).vertexCount graph) m + 3
```

**Natural-language explanation.** Unit-cost specialization of the adjacency-list textbook bound.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type. This concerns the sum of the abstract primitive measurements recorded in the trace.

### adjacencyMatrix_exactCost_le_textbook — theorem

*Source:* `Complexity.lean:664`; public

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
        (BoundedOperational.visitedModel costs) source) ≤
      bounds.clearVisited + BoundedOperational.textbookConstant bounds *
        adjacencyMatrixTime (model.vertexCount graph) +
          BoundedOperational.popCost bounds + bounds.checkStackEmpty
```

**Natural-language explanation.** The arbitrary-cost matrix trace is bounded by textbook work and supplied constants.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type. This concerns the sum of the abstract primitive measurements recorded in the trace. The bound is pointwise over primitive operations; inspect the selected constants and size factors.

### adjacencyMatrix_unitCost_le_textbook — theorem

*Source:* `Complexity.lean:688`; public

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
        GraphTraversal.VisitedModel.booleanTable source) ≤
      3 * adjacencyMatrixTime (model.vertexCount graph) + 3
```

**Natural-language explanation.** Unit-cost specialization of the adjacency-matrix textbook bound.

**Audit focus.** The declaration assumes decidable equality for the indicated vertex or value type. This concerns the sum of the abstract primitive measurements recorded in the trace.

### adjacencyListTime_isBigO — theorem

*Source:* `Complexity.lean:704`; public

```lean
theorem adjacencyListTime_isBigO :
    (fun nm : Nat × Nat ↦ (adjacencyListTime nm.1 nm.2 : Real)) =O[atTop]
      fun nm ↦ (nm.2 : Real) + nm.1
```

**Natural-language explanation.** Kleinberg theorem (3.13): adjacency-list DFS runs in `O(m + n)` time.

**Audit focus.** This is an asymptotic upper bound, so multiplicative constants and a finite prefix are hidden.

### adjacencyMatrixTime_isBigO — theorem

*Source:* `Complexity.lean:710`; public

```lean
theorem adjacencyMatrixTime_isBigO :
    (fun n : Nat ↦ (adjacencyMatrixTime n : Real)) =O[atTop]
      fun n ↦ (n : Real) ^ 2
```

**Natural-language explanation.** With an adjacency matrix, DFS runs in `O(n²)` time.

**Audit focus.** This is an asymptotic upper bound, so multiplicative constants and a finite prefix are hidden.

### timeComplexities — theorem

*Source:* `Complexity.lean:716`; public

```lean
theorem timeComplexities :
    ((fun nm : Nat × Nat ↦ (adjacencyListTime nm.1 nm.2 : Real)) =O[atTop]
      fun nm ↦ (nm.2 : Real) + nm.1) ∧
    ((fun n : Nat ↦ (adjacencyMatrixTime n : Real)) =O[atTop]
      fun n ↦ (n : Real) ^ 2)
```

**Natural-language explanation.** The adjacency-list and adjacency-matrix DFS bounds, packaged together.

**Audit focus.** This is an asymptotic upper bound, so multiplicative constants and a finite prefix are hidden.

# Audit completion checklist {#audit-completion-checklist}

[Back to contents](#contents)

- Confirm the stack update and neighbor order agree with the intended iterative DFS.
- Check the justification for the `1 + m` stack-pop fuel bound.
- Confirm reachability claims retain source-membership and graph-interface assumptions.
- Do not read conditional recursive DFS-tree certificate theorems as outputs of the iterative runner.
- Check adjacency-list and adjacency-matrix resource assumptions independently.
- Treat exact trace cost, weighted operation cost, unit cost, and asymptotic textbook time as distinct quantities.
- Record any mismatch as one of: missing hypothesis, stronger or weaker conclusion, wrong semantic interpretation, wrong cost interpretation, wrong quantification domain, or unsupported textbook attribution.

# Source inventory {#source-inventory}

- `Algorithm.lean`: The free program and its algorithm-specific recursive helpers.
- `ResourceModel.lean`: The selected semantic backends, cost interpretation, runner, and space model.
- `Correctness.lean`: Semantic correctness of completed runs and the case study's graph-theoretic consequences.
- `Complexity.lean`: Cost-independent operation profiles, exact-cost transfers, closed bounds, and asymptotic endpoints.
