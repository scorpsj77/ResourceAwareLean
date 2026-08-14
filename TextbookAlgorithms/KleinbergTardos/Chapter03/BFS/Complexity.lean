/-
Copyright (c) 2026 Jiyuan (Chai Yuen) Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan (Chai Yuen) Ji
-/
import TextbookAlgorithms.KleinbergTardos.Chapter03.BFS.ResourceModel

/-!
# Resource analysis of Kleinberg's breadth-first search

This module contains the textbook aggregate time bounds for the layer-based BFS. Static and
working-space accounting and the thin runner live in `ResourceModel.lean`; generic execution and
trace collection come from `ResourceAware.Program`. Relating exact traces to these aggregate
bounds requires a separate cost-independent operation-profile proof.
-/

namespace KleinbergBFS

open ResourceAware ResourceAware.Algorithms
open ResourceAware.Graph
open Cslib.Algorithms.Lean
open Filter Asymptotics

/-! ## Cost-independent operation-profile accounting -/

namespace Operational

universe u v

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-- Interpreter state selected by the standard textbook BFS resource model. -/
abbrev State (Vertex : Type v) :=
  GraphTraversal.Model.State
    (Vertex → Bool) (Vertex → Option Nat) (List (Vertex × Vertex))

/-- Execute a BFS program from an arbitrary standard-model interpreter state. -/
def execute {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G)
    (program : GraphTraversal.Program Vertex α) (state : State Vertex) :
    TraceM (GraphTraversal.Event Vertex) (α × State Vertex) :=
  GraphTraversal.Model.interpretFrom program model graph
    GraphTraversal.ControlCostModel.unit GraphTraversal.VisitedModel.booleanTable
    GraphTraversal.LevelModel.table GraphTraversal.TreeModel.edgeList state

@[simp]
theorem execute_pure {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (value : α) (state : State Vertex) :
    execute model graph (pure value) state = pure (value, state) := by
  rfl

theorem execute_bind {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G)
    (program : GraphTraversal.Program Vertex α) (next : α → GraphTraversal.Program Vertex β)
    (state : State Vertex) :
    execute model graph (program >>= next) state = (do
      let (result, state') ← execute model graph program state
      execute model graph (next result) state') := by
  exact GraphTraversal.Model.interpretFrom_bind program next model graph _ _ _ _ state

theorem execute_map {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (function : α → β)
    (program : GraphTraversal.Program Vertex α) (state : State Vertex) :
    execute model graph (function <$> program) state = (do
      let (result, state') ← execute model graph program state
      pure (function result, state')) := by
  rw [show function <$> program = (program >>= fun result ↦ pure (function result)) by
    symm
    simpa using PFunctor.FreeM.bind_pure_comp function program]
  rw [execute_bind]
  simp

@[simp]
theorem execute_checkLayerEmpty {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (level : Nat) (state : State Vertex) :
    execute model graph (GraphTraversal.checkLayerEmpty level) state =
      ⟨(.unit, state), EventTrace.singleton ⟨.checkLayerEmpty level, 1⟩⟩ := by
  rfl

@[simp]
theorem execute_isVisited {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (vertex : Vertex) (state : State Vertex) :
    execute model graph (GraphTraversal.isVisited vertex) state =
      ⟨(ULift.up (state.visited vertex), state),
        EventTrace.singleton ⟨.isVisited vertex, 1⟩⟩ := by
  rfl

@[simp]
theorem execute_markVisited {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (vertex : Vertex) (state : State Vertex) :
    execute model graph (GraphTraversal.markVisited vertex) state =
      ⟨(.unit, { state with visited := GraphTraversal.update state.visited vertex true }),
        EventTrace.singleton ⟨.markVisited vertex, 1⟩⟩ := by
  rfl

@[simp]
theorem execute_recordLevel {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (vertex : Vertex) (level : Nat)
    (state : State Vertex) :
    execute model graph (GraphTraversal.recordLevel vertex level) state =
      ⟨(.unit, { state with levels := GraphTraversal.update state.levels vertex (some level) }),
        EventTrace.singleton ⟨.recordLevel vertex level, 1⟩⟩ := by
  rfl

@[simp]
theorem execute_addTreeEdge {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (parent child : Vertex)
    (state : State Vertex) :
    execute model graph (GraphTraversal.addTreeEdge parent child) state =
      ⟨(.unit, { state with tree := (parent, child) :: state.tree }),
        EventTrace.singleton ⟨.addTreeEdge parent child, 1⟩⟩ := by
  rfl

@[simp]
theorem execute_neighbors {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (vertex : Vertex) (state : State Vertex) :
    execute model graph (GraphTraversal.neighbors vertex) state =
      ⟨(model.neighborAccess.outNeighbors graph vertex, state),
        EventTrace.singleton ⟨.neighbors vertex, model.neighborCost graph vertex⟩⟩ := by
  rfl

@[simp]
theorem execute_clearVisited {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (state : State Vertex) :
    execute model graph GraphTraversal.clearVisited state =
      ⟨(.unit, { state with visited := fun _ ↦ false }),
        EventTrace.singleton ⟨.clearVisited, model.vertexCount graph⟩⟩ := by
  rfl

@[simp]
theorem execute_clearLevels {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (state : State Vertex) :
    execute model graph GraphTraversal.clearLevels state =
      ⟨(.unit, { state with levels := fun _ ↦ none }),
        EventTrace.singleton ⟨.clearLevels, model.vertexCount graph⟩⟩ := by
  rfl

@[simp]
theorem execute_clearTree {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (state : State Vertex) :
    execute model graph GraphTraversal.clearTree state =
      ⟨(.unit, { state with tree := [] }),
        EventTrace.singleton ⟨.clearTree, 1⟩⟩ := by
  rfl

/-- Pure summary of scanning one returned neighbor list. -/
structure NeighborResult (Vertex : Type v) where
  fresh : List Vertex
  visited : Vertex → Bool

/-- Semantic recurrence for `processNeighbors` under the standard BFS backends. -/
def neighborResult [DecidableEq Vertex] :
    (Vertex → Bool) → List Vertex → NeighborResult Vertex
  | visited, [] => ⟨[], visited⟩
  | visited, vertex :: rest =>
      if visited vertex then
        let result := neighborResult visited rest
        ⟨result.fresh, result.visited⟩
      else
        let visited' := GraphTraversal.update visited vertex true
        let result := neighborResult visited' rest
        ⟨vertex :: result.fresh, result.visited⟩

/-- Cost-independent weights used to summarize a BFS operation profile. -/
def operationCharge {G : Type u} (model : ResourceModel G Vertex) (graph : G)
    (checkLayerEmpty isVisited markVisited recordLevel addTreeEdge : Nat)
    (other : GraphTraversal.Op Vertex → Nat) : GraphTraversal.Op Vertex → Nat
  | .checkLayerEmpty _ => checkLayerEmpty
  | .neighbors vertex => model.neighborCost graph vertex
  | .isVisited _ => isVisited
  | .markVisited _ => markVisited
  | .recordLevel _ _ => recordLevel
  | .addTreeEdge _ _ => addTreeEdge
  | operation => other operation

/-- Combined profile weight of the three updates performed for one discovery. -/
def discoveryOperationCost (markVisited recordLevel addTreeEdge : Nat) : Nat :=
  markVisited + recordLevel + addTreeEdge

set_option linter.flexible false in
/-- One cost-independent profile proof for scanning neighbors, reusable under every cost model. -/
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
          discoveryOperationCost markVisited recordLevel addTreeEdge * expected.fresh.length := by
  induction neighbors generalizing state with
  | nil =>
      simp [processNeighbors, neighborResult, operationCharge,
        ResourceAware.Program.weightedOperationCost, TraceM.projectedCost, TraceM.cost]
  | cons vertex rest ih =>
      rw [show processNeighbors parent nextLevel (vertex :: rest) = (do
        let seen ← GraphTraversal.isVisited vertex
        if seen.down then processNeighbors parent nextLevel rest
        else do
          GraphTraversal.markVisited vertex
          GraphTraversal.recordLevel vertex nextLevel
          GraphTraversal.addTreeEdge parent vertex
          let fresh ← processNeighbors parent nextLevel rest
          pure (vertex :: fresh)) by rfl]
      rw [execute_bind, execute_isVisited]
      by_cases hseen : state.visited vertex
      · simp [hseen, neighborResult, operationCharge,
          ResourceAware.Program.weightedOperationCost, TraceM.projectedCost, TraceM.cost,
          ResourceAware.Program.Event.erase]
        have hrest := ih state
        refine ⟨hrest.1, hrest.2.1, ?_⟩
        simp only [ResourceAware.Program.weightedOperationCost, TraceM.projectedCost,
          TraceM.cost] at hrest
        simp [Nat.mul_add]
        omega
      · simp [hseen, neighborResult, execute_bind, execute_map, operationCharge,
          ResourceAware.Program.weightedOperationCost, TraceM.projectedCost, TraceM.cost,
          ResourceAware.Program.Event.erase]
        let nextState : State Vertex :=
          { state with
            visited := GraphTraversal.update state.visited vertex true
            levels := GraphTraversal.update state.levels vertex (some nextLevel)
            tree := (parent, vertex) :: state.tree }
        have hrest := ih nextState
        dsimp [nextState] at hrest
        refine ⟨hrest.1, hrest.2.1, ?_⟩
        simp only [ResourceAware.Program.weightedOperationCost, TraceM.projectedCost,
          TraceM.cost] at hrest
        simp [discoveryOperationCost, Nat.mul_add] at hrest ⊢
        omega

/-- Semantic and counting invariants for one neighbor-list scan. -/
structure NeighborProperties (neighbors : List Vertex) (initial : Vertex → Bool)
    (result : NeighborResult Vertex) : Prop where
  monotone : ∀ vertex, initial vertex = true → result.visited vertex = true
  fresh_unvisited : ∀ vertex ∈ result.fresh, initial vertex = false
  fresh_nodup : result.fresh.Nodup
  fresh_visited : ∀ vertex ∈ result.fresh, result.visited vertex = true
  fresh_mem : ∀ vertex ∈ result.fresh, vertex ∈ neighbors

set_option linter.flexible false in
/-- Newly returned neighbors are exactly-once discoveries. -/
theorem neighborResult_properties [DecidableEq Vertex]
    (visited : Vertex → Bool) (neighbors : List Vertex) :
    NeighborProperties neighbors visited (neighborResult visited neighbors) := by
  induction neighbors generalizing visited with
  | nil =>
      constructor <;> simp [neighborResult]
  | cons vertex rest ih =>
      by_cases hseen : visited vertex
      · have hrest := ih visited
        simp only [neighborResult, hseen, ↓reduceIte]
        constructor
        · exact hrest.monotone
        · exact hrest.fresh_unvisited
        · exact hrest.fresh_nodup
        · exact hrest.fresh_visited
        · intro candidate hcandidate
          exact List.mem_cons_of_mem vertex (hrest.fresh_mem candidate hcandidate)
      · have hrest := ih (GraphTraversal.update visited vertex true)
        simp only [neighborResult, hseen, ↓reduceIte]
        constructor
        · intro candidate hcandidate
          exact hrest.monotone candidate (by simp [GraphTraversal.update, hcandidate])
        · intro candidate hcandidate
          rcases List.mem_cons.mp hcandidate with rfl | hcandidate
          · exact Bool.eq_false_iff.mpr hseen
          · refine Bool.eq_false_iff.mpr fun hcandidateTrue ↦ ?_
            have := hrest.fresh_unvisited candidate hcandidate
            simp [GraphTraversal.update, hcandidateTrue] at this
        · refine List.nodup_cons.mpr ⟨?_, hrest.fresh_nodup⟩
          intro hmem
          simpa [GraphTraversal.update] using hrest.fresh_unvisited vertex hmem
        · intro candidate hcandidate
          rcases List.mem_cons.mp hcandidate with rfl | hcandidate
          · exact hrest.monotone candidate (by simp [GraphTraversal.update])
          · exact hrest.fresh_visited candidate hcandidate
        · intro candidate hcandidate
          rcases List.mem_cons.mp hcandidate with rfl | hcandidate
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem vertex (hrest.fresh_mem candidate hcandidate)

/-- Pure summary of processing one complete BFS layer. -/
structure LayerResult (Vertex : Type v) where
  fresh : List Vertex
  visited : Vertex → Bool

/-- Semantic recurrence for `processLayer`. -/
def layerResult {G : Type u} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (level : Nat) :
    List Vertex → (Vertex → Bool) → LayerResult Vertex
  | [], visited => ⟨[], visited⟩
  | vertex :: rest, visited =>
      let fromVertex := neighborResult visited
        (model.neighborAccess.outNeighbors graph vertex)
      let fromRest := layerResult model graph level rest fromVertex.visited
      ⟨fromVertex.fresh ++ fromRest.fresh, fromRest.visited⟩

/-- Neighbor-query and visited-test weight in a cost-independent layer profile. -/
def weightedLayerCost {G : Type u} (isVisited : Nat)
    (model : ResourceModel G Vertex) (graph : G) (current : List Vertex) : Nat :=
  (current.map fun vertex ↦ model.neighborCost graph vertex +
    isVisited * (model.neighborAccess.outNeighbors graph vertex).length).sum

@[simp]
theorem weightedLayerCost_append {G : Type u} (isVisited : Nat)
    (model : ResourceModel G Vertex) (graph : G) (left right : List Vertex) :
    weightedLayerCost isVisited model graph (left ++ right) =
      weightedLayerCost isVisited model graph left +
        weightedLayerCost isVisited model graph right := by
  simp [weightedLayerCost]

set_option linter.flexible false in
/-- One cost-independent operation-profile proof for processing a complete BFS layer. -/
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
          discoveryOperationCost markVisited recordLevel addTreeEdge * expected.fresh.length := by
  induction current generalizing state with
  | nil =>
      simp [processLayer, layerResult, weightedLayerCost,
        ResourceAware.Program.weightedOperationCost, TraceM.projectedCost, TraceM.cost]
  | cons vertex rest ih =>
      rw [show processLayer level (vertex :: rest) = (do
        let neighbors ← GraphTraversal.neighbors vertex
        let fromVertex ← processNeighbors vertex (level + 1) neighbors
        let fromRest ← processLayer level rest
        pure (fromVertex ++ fromRest)) by rfl]
      rw [execute_bind, execute_neighbors]
      simp [operationCharge, ResourceAware.Program.weightedOperationCost,
        TraceM.projectedCost, TraceM.cost, ResourceAware.Program.Event.erase]
      rw [execute_bind]
      have hneighbors := processNeighbors_weightedOperationCost_le model graph
        checkLayerEmpty isVisited markVisited recordLevel addTreeEdge other vertex (level + 1)
        (model.neighborAccess.outNeighbors graph vertex) state
      simp_rw [execute_map]
      have hrest := ih
        (execute model graph
          (processNeighbors vertex (level + 1)
            (model.neighborAccess.outNeighbors graph vertex)) state).ret.2
      rw [hneighbors.2.1] at hrest
      simp
      refine ⟨congrArg₂ (· ++ ·) hneighbors.1 hrest.1, ?_, ?_⟩
      · simpa only [layerResult] using hrest.2.1
      · simp only [layerResult]
        simp only [ResourceAware.Program.weightedOperationCost, TraceM.projectedCost,
          TraceM.cost] at hneighbors hrest
        simp [weightedLayerCost, Nat.mul_add] at hrest ⊢
        omega

/-- Semantic and counting invariants for processing one complete BFS layer. -/
structure LayerProperties {G : Type u} (model : ResourceModel G Vertex) (graph : G)
    (current : List Vertex) (initial : Vertex → Bool) (result : LayerResult Vertex) : Prop where
  monotone : ∀ vertex, initial vertex = true → result.visited vertex = true
  fresh_unvisited : ∀ vertex ∈ result.fresh, initial vertex = false
  fresh_nodup : result.fresh.Nodup
  fresh_visited : ∀ vertex ∈ result.fresh, result.visited vertex = true
  fresh_vertices : ∀ vertex ∈ result.fresh,
    vertex ∈ model.vertexEnumeration.vertices graph

set_option linter.flexible false in
/-- A complete layer discovers each new vertex once. -/
theorem layerResult_properties {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (level : Nat)
    (current : List Vertex) (visited : Vertex → Bool) :
    LayerProperties model graph current visited
      (layerResult model graph level current visited) := by
  induction current generalizing visited with
  | nil =>
      constructor <;> simp [layerResult]
  | cons vertex rest ih =>
      let fromVertex := neighborResult visited
        (model.neighborAccess.outNeighbors graph vertex)
      let fromRest := layerResult model graph level rest fromVertex.visited
      have hvertex := neighborResult_properties visited
        (model.neighborAccess.outNeighbors graph vertex)
      have hrest := ih fromVertex.visited
      change LayerProperties model graph (vertex :: rest) visited
        { fresh := fromVertex.fresh ++ fromRest.fresh
          visited := fromRest.visited }
      constructor
      · intro candidate hcandidate
        exact hrest.monotone candidate (hvertex.monotone candidate hcandidate)
      · intro candidate hcandidate
        rcases List.mem_append.mp hcandidate with hcandidate | hcandidate
        · exact hvertex.fresh_unvisited candidate hcandidate
        · refine Bool.eq_false_iff.mpr fun hcandidateTrue ↦ ?_
          have := hrest.fresh_unvisited candidate hcandidate
          rw [hvertex.monotone candidate hcandidateTrue] at this
          contradiction
      · apply hvertex.fresh_nodup.append hrest.fresh_nodup
        rw [List.disjoint_iff_ne]
        rintro left hleft _ hright rfl
        have := hrest.fresh_unvisited left hright
        rw [hvertex.fresh_visited left hleft] at this
        contradiction
      · intro candidate hcandidate
        rcases List.mem_append.mp hcandidate with hcandidate | hcandidate
        · exact hrest.monotone candidate (hvertex.fresh_visited candidate hcandidate)
        · exact hrest.fresh_visited candidate hcandidate
      · intro candidate hcandidate
        rcases List.mem_append.mp hcandidate with hcandidate | hcandidate
        · exact model.vertexEnumeration.complete
            (model.neighborAccess.target_mem (hvertex.fresh_mem candidate hcandidate))
        · exact hrest.fresh_vertices candidate hcandidate

/-- Pure summary of the complete layer loop. -/
structure LoopResult (Vertex : Type v) where
  visited : Vertex → Bool
  queried : List Vertex
  discovered : List Vertex

/-- Semantic recurrence implemented by the standard-model BFS loop. -/
def loopResult {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) :
    Nat → Nat → List Vertex → (Vertex → Bool) → LoopResult Vertex
  | 0, _, [], visited => ⟨visited, [], []⟩
  | 0, _, _ :: _, visited => ⟨visited, [], []⟩
  | _ + 1, _, [], visited => ⟨visited, [], []⟩
  | fuel + 1, level, current@(_ :: _), visited =>
      let layer := layerResult model graph level current visited
      let rest := loopResult model graph fuel (level + 1) layer.fresh layer.visited
      ⟨rest.visited, current ++ rest.queried, layer.fresh ++ rest.discovered⟩

set_option linter.flexible false in
/-- One cost-independent operation-profile proof for the complete BFS layer loop. -/
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
              expected.discovered.length := by
  induction fuel generalizing level current state with
  | zero =>
      cases current with
      | nil =>
          simp [bfsLoop, loopResult, operationCharge,
            ResourceAware.Program.weightedOperationCost, TraceM.projectedCost, TraceM.cost,
            ResourceAware.Program.Event.erase]
      | cons vertex rest =>
          simp [bfsLoop, loopResult,
            ResourceAware.Program.weightedOperationCost, TraceM.projectedCost, TraceM.cost]
  | succ fuel ih =>
      cases current with
      | nil =>
          simp [bfsLoop, loopResult, operationCharge,
            ResourceAware.Program.weightedOperationCost, TraceM.projectedCost, TraceM.cost,
            ResourceAware.Program.Event.erase, weightedLayerCost, Nat.mul_add]
      | cons vertex rest =>
          let current := vertex :: rest
          rw [show bfsLoop (fuel + 1) level current = (do
            GraphTraversal.checkLayerEmpty level
            let next ← processLayer level current
            bfsLoop fuel (level + 1) next) by rfl]
          rw [execute_bind, execute_checkLayerEmpty]
          simp [operationCharge, ResourceAware.Program.weightedOperationCost,
            TraceM.projectedCost, TraceM.cost, ResourceAware.Program.Event.erase]
          rw [execute_bind]
          let layerState :=
            (execute model graph (processLayer level current) state).ret.2
          have hlayer := processLayer_weightedOperationCost_le model graph
            checkLayerEmpty isVisited markVisited recordLevel addTreeEdge other
            level current state
          have hrest := ih (level + 1)
            (execute model graph (processLayer level current) state).ret.1 layerState
          dsimp [layerState] at hrest
          rw [hlayer.1, hlayer.2.1] at hrest
          simp
          rw [hlayer.1]
          refine ⟨?_, ?_⟩
          · simpa [loopResult, current] using hrest.1
          · simp only [loopResult, current]
            simp only [current, ResourceAware.Program.weightedOperationCost,
              TraceM.projectedCost, TraceM.cost] at hlayer hrest
            rw [weightedLayerCost_append]
            simp [Nat.mul_add] at hrest ⊢
            omega

/-- Global uniqueness and vertex-membership facts for a complete BFS-loop recurrence. -/
structure LoopProperties {G : Type u} (model : ResourceModel G Vertex) (graph : G)
    (previous current : List Vertex) (initial : Vertex → Bool)
    (result : LoopResult Vertex) : Prop where
  monotone : ∀ vertex, initial vertex = true → result.visited vertex = true
  queried_nodup : result.queried.Nodup
  discovered_nodup : result.discovered.Nodup
  previous_disjoint_queried : previous.Disjoint result.queried
  prior_disjoint_discovered : (previous ++ current).Disjoint result.discovered
  queried_vertices : ∀ vertex ∈ result.queried,
    vertex ∈ model.vertexEnumeration.vertices graph
  discovered_vertices : ∀ vertex ∈ result.discovered,
    vertex ∈ model.vertexEnumeration.vertices graph

set_option linter.flexible false in
/-- BFS processes and discovers only globally distinct vertices. -/
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
      (loopResult model graph fuel level current visited) := by
  induction fuel generalizing level previous current visited with
  | zero =>
      cases current <;> constructor <;> simp [loopResult]
  | succ fuel ih =>
      cases current with
      | nil =>
          constructor <;> simp [loopResult]
      | cons vertex tail =>
          let current := vertex :: tail
          let layer := layerResult model graph level current visited
          let prior := previous ++ current
          have hlayer := layerResult_properties model graph level current visited
          have hpriorNodup : prior.Nodup := hprevious.append hcurrent hdisjoint
          have hpriorVisited : ∀ candidate ∈ prior, layer.visited candidate = true := by
            intro candidate hcandidate
            apply hlayer.monotone candidate
            rcases List.mem_append.mp hcandidate with hcandidate | hcandidate
            · exact hpreviousVisited candidate hcandidate
            · exact hcurrentVisited candidate hcandidate
          have hpriorFreshDisjoint : prior.Disjoint layer.fresh := by
            rw [List.disjoint_iff_ne]
            rintro old hold _ hfresh rfl
            have holdTrue : visited old = true := by
              rcases List.mem_append.mp hold with hold | hold
              · exact hpreviousVisited old hold
              · exact hcurrentVisited old hold
            have := hlayer.fresh_unvisited old hfresh
            simp [holdTrue] at this
          have hrecursive := ih (level + 1) prior layer.fresh layer.visited
            hpriorNodup hlayer.fresh_nodup hpriorFreshDisjoint hpriorVisited
            hlayer.fresh_visited hlayer.fresh_vertices
          have hqueryDisjoint := List.disjoint_append_left.mp
            hrecursive.previous_disjoint_queried
          have hdiscoverDisjoint := List.disjoint_append_left.mp
            hrecursive.prior_disjoint_discovered
          let restResult := loopResult model graph fuel (level + 1) layer.fresh layer.visited
          change LoopProperties model graph previous current visited
            { visited := restResult.visited
              queried := current ++ restResult.queried
              discovered := layer.fresh ++ restResult.discovered }
          constructor
          · intro candidate hcandidate
            exact hrecursive.monotone candidate (hlayer.monotone candidate hcandidate)
          · exact hcurrent.append hrecursive.queried_nodup hqueryDisjoint.2
          · exact hlayer.fresh_nodup.append hrecursive.discovered_nodup
              hdiscoverDisjoint.2
          · rw [List.disjoint_append_right]
            exact ⟨hdisjoint, hqueryDisjoint.1⟩
          · rw [List.disjoint_append_right]
            exact ⟨hpriorFreshDisjoint, hdiscoverDisjoint.1⟩
          · intro candidate hcandidate
            rcases List.mem_append.mp hcandidate with hcandidate | hcandidate
            · exact hcurrentVertices candidate hcandidate
            · exact hrecursive.queried_vertices candidate hcandidate
          · intro candidate hcandidate
            rcases List.mem_append.mp hcandidate with hcandidate | hcandidate
            · exact hlayer.fresh_vertices candidate hcandidate
            · exact hrecursive.discovered_vertices candidate hcandidate

/-- Visited table immediately before the BFS layer loop starts. -/
def startVisited [DecidableEq Vertex] (source : Vertex) : Vertex → Bool :=
  GraphTraversal.update (fun _ ↦ false) source true

end Operational

/-! ## Cost-parametric operational accounting -/

namespace BoundedOperational

universe u v

/-- Arbitrary costs for the standard Boolean-table, level-table, and edge-list BFS backends. -/
structure CostModel (Vertex : Type v) where
  control : GraphTraversal.ControlCostModel
  visited : GraphTraversal.VisitedCostModel Vertex (Vertex → Bool)
  levels : GraphTraversal.LevelCostModel Vertex (Vertex → Option Nat)
  tree : GraphTraversal.TreeCostModel Vertex (List (Vertex × Vertex))

/-- Uniform upper bounds for every primitive operation used by BFS on one graph. -/
structure CostBounds where
  checkLayerEmpty : Nat
  clearVisited : Nat
  clearLevels : Nat
  clearTree : Nat
  isVisited : Nat
  markVisited : Nat
  recordLevel : Nat
  addTreeEdge : Nat

/-- The selected operation costs respect the supplied uniform upper bounds. -/
structure CostModel.IsBoundedBy {Vertex : Type v} (costs : CostModel Vertex)
    (bounds : CostBounds) (vertexCount : Nat) : Prop where
  checkLayerEmpty : ∀ level, costs.control.checkLayerEmptyCost level ≤ bounds.checkLayerEmpty
  clearVisited : costs.visited.clearCost vertexCount ≤ bounds.clearVisited
  clearLevels : costs.levels.clearCost vertexCount ≤ bounds.clearLevels
  clearTree : costs.tree.clearCost vertexCount ≤ bounds.clearTree
  isVisited : ∀ state vertex, costs.visited.isVisitedCost state vertex ≤ bounds.isVisited
  markVisited : ∀ state vertex,
    costs.visited.markVisitedCost state vertex ≤ bounds.markVisited
  recordLevel : ∀ state vertex level,
    costs.levels.recordLevelCost state vertex level ≤ bounds.recordLevel
  addTreeEdge : ∀ state parent child,
    costs.tree.addTreeEdgeCost state parent child ≤ bounds.addTreeEdge

/-- Standard Boolean-table semantics equipped with arbitrary visited-operation costs. -/
def visitedModel [DecidableEq Vertex] (costs : CostModel Vertex) :
    GraphTraversal.VisitedModel Vertex (Vertex → Bool) :=
  { GraphTraversal.VisitedModel.booleanTable with
      cost := costs.visited }

/-- Standard level-table semantics equipped with arbitrary level-operation costs. -/
def levelModel [DecidableEq Vertex] (costs : CostModel Vertex) :
    GraphTraversal.LevelModel Vertex (Vertex → Option Nat) :=
  { GraphTraversal.LevelModel.table with cost := costs.levels }

/-- Standard edge-list semantics equipped with arbitrary tree-operation costs. -/
def treeModel (costs : CostModel Vertex) :
    GraphTraversal.TreeModel Vertex (List (Vertex × Vertex)) :=
  { GraphTraversal.TreeModel.edgeList with cost := costs.tree }

/-- Execute BFS with the standard backends and arbitrary operation costs. -/
def execute {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (costs : CostModel Vertex)
    (program : GraphTraversal.Program Vertex α) (state : Operational.State Vertex) :
    TraceM (GraphTraversal.Event Vertex) (α × Operational.State Vertex) :=
  GraphTraversal.Model.interpretFrom program model graph costs.control
    (visitedModel costs) (levelModel costs) (treeModel costs) state

/-- Upper-bound cost of the three updates performed for one newly discovered vertex. -/
def discoveryCost (bounds : CostBounds) : Nat :=
  bounds.markVisited + bounds.recordLevel + bounds.addTreeEdge

/-- Weights for operations outside the BFS loop profile, especially initialization. -/
def otherOperationCharge (costs : CostModel Vertex) (bounds : CostBounds) :
    GraphTraversal.Op Vertex → Nat
  | .checkStackEmpty => costs.control.checkStackEmptyCost
  | .clearVisited => bounds.clearVisited
  | .clearLevels => bounds.clearLevels
  | .clearTree => bounds.clearTree
  | _ => 0

/-- The operation weights used to reinterpret the cost-independent BFS profile. -/
def operationCharge {G : Type u} (model : ResourceModel G Vertex) (graph : G)
    (costs : CostModel Vertex) (bounds : CostBounds) : GraphTraversal.Op Vertex → Nat :=
  Operational.operationCharge model graph bounds.checkLayerEmpty bounds.isVisited
    bounds.markVisited bounds.recordLevel bounds.addTreeEdge (otherOperationCharge costs bounds)

/-- Primitive cost assumptions are discharged once when constructing the generic interpreter
bound, rather than inside each recursive BFS proof. -/
theorem interpreter_isBoundedBy {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (costs : CostModel Vertex)
    (bounds : CostBounds) (hbounds : costs.IsBoundedBy bounds (model.vertexCount graph)) :
    GraphTraversal.Model.IsBoundedBy model graph costs.control
      (visitedModel costs) (levelModel costs) (treeModel costs)
      (operationCharge model graph costs bounds) := by
  constructor
  · intro level
    simpa [operationCharge, Operational.operationCharge] using hbounds.checkLayerEmpty level
  · simp [operationCharge, Operational.operationCharge, otherOperationCharge]
  · simpa [operationCharge, Operational.operationCharge, otherOperationCharge,
      visitedModel] using hbounds.clearVisited
  · simpa [operationCharge, Operational.operationCharge, otherOperationCharge,
      levelModel] using hbounds.clearLevels
  · simpa [operationCharge, Operational.operationCharge, otherOperationCharge,
      treeModel] using hbounds.clearTree
  · intro vertex
    simp [operationCharge, Operational.operationCharge]
  · intro state vertex
    simpa [operationCharge, Operational.operationCharge, visitedModel] using
      hbounds.isVisited state vertex
  · intro state vertex
    simpa [operationCharge, Operational.operationCharge, visitedModel] using
      hbounds.markVisited state vertex
  · intro state vertex level
    simpa [operationCharge, Operational.operationCharge, levelModel] using
      hbounds.recordLevel state vertex level
  · intro state parent child
    simpa [operationCharge, Operational.operationCharge, treeModel] using
      hbounds.addTreeEdge state parent child

/-- Any bounded-cost BFS execution is semantically equal to the standard execution and is
bounded by that execution's single cost-independent profile. -/
theorem execute_le_standardProfile {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (costs : CostModel Vertex)
    (bounds : CostBounds) (hbounds : costs.IsBoundedBy bounds (model.vertexCount graph))
    (program : GraphTraversal.Program Vertex α) (state : Operational.State Vertex) :
    let actual := execute model graph costs program state
    let standard := Operational.execute model graph program state
    actual.ret = standard.ret ∧
      ResourceAware.Program.exactCost actual ≤
        ResourceAware.Program.weightedOperationCost
          (operationCharge model graph costs bounds) standard := by
  dsimp
  let charge := operationCharge model graph costs bounds
  have hret := GraphTraversal.Model.ret_interpretFrom_eq_of_backend_eq
    program model graph costs.control GraphTraversal.ControlCostModel.unit
    (visitedModel costs) GraphTraversal.VisitedModel.booleanTable
    (levelModel costs) GraphTraversal.LevelModel.table
    (treeModel costs) GraphTraversal.TreeModel.edgeList rfl rfl rfl state
  have htrace := GraphTraversal.Model.operationTrace_interpretFrom_eq_of_backend_eq
    program model graph costs.control GraphTraversal.ControlCostModel.unit
    (visitedModel costs) GraphTraversal.VisitedModel.booleanTable
    (levelModel costs) GraphTraversal.LevelModel.table
    (treeModel costs) GraphTraversal.TreeModel.edgeList rfl rfl rfl state
  have hcost :=
    GraphTraversal.Model.exactCost_interpretFrom_le_weightedOperationCost
      program model graph costs.control (visitedModel costs) (levelModel costs) (treeModel costs)
      charge (interpreter_isBoundedBy model graph costs bounds hbounds) state
  refine ⟨?_, hcost.trans ?_⟩
  · simpa [execute, Operational.execute] using hret
  · apply Nat.le_of_eq
    apply ResourceAware.Program.weightedOperationCost_eq_of_operationTrace_eq charge
    simpa [execute, Operational.execute, ResourceAware.Program.operationTrace] using htrace

/-- Neighbor-query and visited-test work for a list of processed layer vertices. -/
def layerWeight {G : Type u} (bounds : CostBounds) (model : ResourceModel G Vertex)
    (graph : G) (current : List Vertex) : Nat :=
  (current.map fun vertex ↦ model.neighborCost graph vertex +
    bounds.isVisited * (model.neighborAccess.outNeighbors graph vertex).length).sum

/-- Initialization work before the BFS layer loop. -/
def initializationCost (bounds : CostBounds) : Nat :=
  bounds.clearVisited + bounds.clearLevels + bounds.clearTree +
    bounds.markVisited + bounds.recordLevel

set_option linter.flexible false in
/-- The public BFS runner obeys arbitrary supplied upper bounds for primitive costs. -/
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
          discoveryCost bounds * result.discovered.length := by
  let initial : Operational.State Vertex := GraphTraversal.Model.initialState
    (visitedModel costs) (levelModel costs) (treeModel costs)
  let program := bfs (model.vertexCount graph) source
  let charge := operationCharge model graph costs bounds
  let actual := execute model graph costs program initial
  let standard := Operational.execute model graph program initial
  change ResourceAware.Program.exactCost actual ≤ _
  have hstandard := execute_le_standardProfile model graph costs bounds hbounds program initial
  have hloop := Operational.bfsLoop_weightedOperationCost_le model graph
    bounds.checkLayerEmpty bounds.isVisited bounds.markVisited bounds.recordLevel
    bounds.addTreeEdge (otherOperationCharge costs bounds) (model.vertexCount graph) 0 [source]
    ({ visited := Operational.startVisited source
       levels := GraphTraversal.update (fun _ ↦ none) source (some 0)
       tree := [] } : Operational.State Vertex)
  apply hstandard.2.trans
  change ResourceAware.Program.weightedOperationCost charge standard ≤ _
  let loopState : Operational.State Vertex :=
    { visited := Operational.startVisited source
      levels := GraphTraversal.update (fun _ ↦ none) source (some 0)
      tree := [] }
  have hdecompose : ResourceAware.Program.weightedOperationCost charge standard =
      initializationCost bounds + ResourceAware.Program.weightedOperationCost charge
        (Operational.execute model graph (bfsLoop (model.vertexCount graph) 0 [source])
          loopState) := by
    dsimp [standard, program]
    rw [show bfs (model.vertexCount graph) source = (do
      GraphTraversal.clearVisited
      GraphTraversal.clearLevels
      GraphTraversal.clearTree
      GraphTraversal.markVisited source
      GraphTraversal.recordLevel source 0
      bfsLoop (model.vertexCount graph) 0 [source]) by rfl]
    simp [Operational.execute_bind, ResourceAware.Program.weightedOperationCost,
      TraceM.projectedCost, TraceM.cost, ResourceAware.Program.Event.erase, charge, operationCharge,
      Operational.operationCharge, otherOperationCharge, initial, loopState,
      GraphTraversal.Model.initialState, visitedModel, levelModel, treeModel,
      initializationCost, Operational.startVisited]
    omega
  rw [hdecompose]
  have hloopCost : ResourceAware.Program.weightedOperationCost charge
      (Operational.execute model graph (bfsLoop (model.vertexCount graph) 0 [source])
        loopState) ≤
      bounds.checkLayerEmpty * (model.vertexCount graph + 1) +
        layerWeight bounds model graph
          (Operational.loopResult model graph (model.vertexCount graph) 0 [source]
            (Operational.startVisited source)).queried +
        discoveryCost bounds *
          (Operational.loopResult model graph (model.vertexCount graph) 0 [source]
            (Operational.startVisited source)).discovered.length := by
    simpa [charge, operationCharge, loopState, layerWeight, Operational.weightedLayerCost,
      discoveryCost, Operational.discoveryOperationCost] using hloop.2
  omega

/-- Unit-cost instance used only to recover the traditional concrete corollaries. -/
def unitCostModel [DecidableEq Vertex] : CostModel Vertex where
  control := GraphTraversal.ControlCostModel.unit
  visited := GraphTraversal.VisitedCostModel.booleanTable
  levels := GraphTraversal.LevelCostModel.table
  tree := GraphTraversal.TreeCostModel.edgeList

/-- Bounds realized by the standard unit-cost backends on a graph with `n` vertices. -/
def unitCostBounds (n : Nat) : CostBounds where
  checkLayerEmpty := 1
  clearVisited := n
  clearLevels := n
  clearTree := 1
  isVisited := 1
  markVisited := 1
  recordLevel := 1
  addTreeEdge := 1

/-- The standard unit-cost models satisfy their concrete bounds. -/
theorem unitCostModel_isBoundedBy [DecidableEq Vertex] (n : Nat) :
    (unitCostModel : CostModel Vertex).IsBoundedBy (unitCostBounds n) n := by
  constructor <;> simp [unitCostModel, unitCostBounds,
    GraphTraversal.ControlCostModel.unit, GraphTraversal.VisitedCostModel.booleanTable,
    GraphTraversal.LevelCostModel.table, GraphTraversal.TreeCostModel.edgeList]

/-- Graph-wide BFS work expressed using arbitrary primitive-operation bounds. -/
def modelWorkBound {G : Type u} (bounds : CostBounds) (model : ResourceModel G Vertex)
    (graph : G) : Nat :=
  initializationCost bounds + bounds.checkLayerEmpty * (model.vertexCount graph + 1) +
    model.totalNeighborCost graph + bounds.isVisited * model.adjacencyEntryCount graph +
      discoveryCost bounds * model.vertexCount graph

/-- A single constant dominating all per-vertex and per-entry BFS work. -/
def textbookConstant (bounds : CostBounds) : Nat :=
  bounds.checkLayerEmpty + discoveryCost bounds + bounds.isVisited + 1

end BoundedOperational

/-! ## Time complexity -/

/-- The exact BFS trace is bounded under any operation costs satisfying `bounds`. -/
theorem exactCost_le_modelWork {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G)
    (costs : BoundedOperational.CostModel Vertex) (bounds : BoundedOperational.CostBounds)
    (hbounds : costs.IsBoundedBy bounds (model.vertexCount graph))
    (source : Vertex) (hsource : source ∈ model.interface.vertexSet graph) :
    exactCost (Interpreter.run model graph costs.control
        (BoundedOperational.visitedModel costs) (BoundedOperational.levelModel costs)
        (BoundedOperational.treeModel costs) source) ≤
      BoundedOperational.modelWorkBound bounds model graph := by
  let result := Operational.loopResult model graph (model.vertexCount graph) 0 [source]
    (Operational.startVisited source)
  have hproperties := Operational.loopResult_properties model graph
    (model.vertexCount graph) 0 [] [source] (Operational.startVisited source)
    (by simp) (by simp) (by simp) (by simp)
    (by simp [Operational.startVisited, GraphTraversal.update])
    (by simpa using model.vertexEnumeration.complete hsource)
  have hrun := BoundedOperational.exactCost_run_le model graph costs bounds hbounds source
  change exactCost (Interpreter.run model graph costs.control
      (BoundedOperational.visitedModel costs) (BoundedOperational.levelModel costs)
      (BoundedOperational.treeModel costs) source) ≤
    BoundedOperational.initializationCost bounds +
      bounds.checkLayerEmpty * (model.vertexCount graph + 1) +
        BoundedOperational.layerWeight bounds model graph result.queried +
          BoundedOperational.discoveryCost bounds * result.discovered.length at hrun
  apply hrun.trans
  unfold BoundedOperational.modelWorkBound BoundedOperational.layerWeight
  simp only [List.sum_map_add]
  have hneighborSum :
      (result.queried.map (model.neighborCost graph)).sum ≤
        ((model.vertexEnumeration.vertices graph).map fun vertex ↦
          model.neighborCost graph vertex).sum :=
    (ResourceModel.nodup_sublist_length_and_sum_le result.queried
      (model.vertexEnumeration.vertices graph) (model.neighborCost graph)
      hproperties.queried_nodup (model.vertexEnumeration.nodup graph)
      hproperties.queried_vertices).2
  have hvisitedSum : bounds.isVisited *
      (result.queried.map fun vertex ↦
        (model.neighborAccess.outNeighbors graph vertex).length).sum ≤
      bounds.isVisited * ((model.vertexEnumeration.vertices graph).map fun vertex ↦
        (model.neighborAccess.outNeighbors graph vertex).length).sum := by
    simpa only [List.sum_map_mul_left] using
      (ResourceModel.nodup_sublist_length_and_sum_le result.queried
        (model.vertexEnumeration.vertices graph)
        (fun vertex ↦ bounds.isVisited *
          (model.neighborAccess.outNeighbors graph vertex).length)
        hproperties.queried_nodup (model.vertexEnumeration.nodup graph)
        hproperties.queried_vertices).2
  have hdiscoveredLength :=
    (ResourceModel.nodup_sublist_length_and_sum_le result.discovered
      (model.vertexEnumeration.vertices graph) (fun _ ↦ 0)
      hproperties.discovered_nodup (model.vertexEnumeration.nodup graph)
      hproperties.discovered_vertices).1
  simp only [ResourceModel.vertexCount, ResourceModel.adjacencyEntryCount,
    ResourceModel.totalNeighborCost] at hneighborSum hvisitedSum hdiscoveredLength ⊢
  simp only [List.sum_map_mul_left]
  have hdiscoverWork := Nat.mul_le_mul_left
    (BoundedOperational.discoveryCost bounds) hdiscoveredLength
  omega

/-- The previous concrete bound is the unit-cost specialization of the generic theorem. -/
theorem unitCost_le_modelWork {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (source : Vertex)
    (hsource : source ∈ model.interface.vertexSet graph) :
    exactCost (Interpreter.run model graph GraphTraversal.ControlCostModel.unit
        GraphTraversal.VisitedModel.booleanTable GraphTraversal.LevelModel.table
        GraphTraversal.TreeModel.edgeList source) ≤
      6 * model.vertexCount graph + model.adjacencyEntryCount graph +
        model.totalNeighborCost graph + 4 := by
  have hbound := exactCost_le_modelWork model graph
    (BoundedOperational.unitCostModel : BoundedOperational.CostModel Vertex)
    (BoundedOperational.unitCostBounds (model.vertexCount graph))
    (BoundedOperational.unitCostModel_isBoundedBy (model.vertexCount graph))
    source hsource
  change exactCost (Interpreter.run model graph GraphTraversal.ControlCostModel.unit
      GraphTraversal.VisitedModel.booleanTable GraphTraversal.LevelModel.table
      GraphTraversal.TreeModel.edgeList source) ≤
    BoundedOperational.modelWorkBound
      (BoundedOperational.unitCostBounds (model.vertexCount graph)) model graph at hbound
  simp [BoundedOperational.modelWorkBound, BoundedOperational.unitCostBounds,
    BoundedOperational.initializationCost, BoundedOperational.discoveryCost] at hbound
  omega

/-- Adjacency-list BFS under arbitrary bounded primitive-operation costs. -/
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
            (ResourceModel.ofAdjacencyList Γ vertices neighbors).vertexCount graph := by
  simpa only [BoundedOperational.modelWorkBound,
    ResourceModel.ofAdjacencyList_totalNeighborCost, hentries] using
    exactCost_le_modelWork (ResourceModel.ofAdjacencyList Γ vertices neighbors) graph
      costs bounds hbounds source hsource

/-- Adjacency-matrix BFS under arbitrary bounded primitive-operation costs. -/
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
          BoundedOperational.discoveryCost bounds * model.vertexCount graph := by
  let model := ResourceModel.ofAdjacencyMatrix Γ vertices edge edge_iff
  have hbound := exactCost_le_modelWork model graph costs bounds hbounds source hsource
  unfold BoundedOperational.modelWorkBound at hbound
  have hvisitedEntries := Nat.mul_le_mul_left bounds.isVisited
    (ResourceModel.adjacencyEntryCount_le_square model graph)
  have hqueries : model.totalNeighborCost graph =
      model.vertexCount graph * model.vertexCount graph :=
    ResourceModel.ofAdjacencyMatrix_totalNeighborCost Γ vertices edge edge_iff graph
  simp only [model] at hbound hvisitedEntries hqueries ⊢
  rw [hqueries] at hbound
  omega

/-- Unit-cost corollary for an undirected adjacency list. -/
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
        4 * m + 4 := by
  have hbound := unitCost_le_modelWork
    (ResourceModel.ofAdjacencyList Γ vertices neighbors) graph source hsource
  rw [ResourceModel.ofAdjacencyList_totalNeighborCost, hentries] at hbound
  omega

/-- Unit-cost corollary for an adjacency matrix. -/
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
        2 * (model.vertexCount graph * model.vertexCount graph) + 4 := by
  let model := ResourceModel.ofAdjacencyMatrix Γ vertices edge edge_iff
  have hbound := unitCost_le_modelWork model graph source hsource
  have hentries := ResourceModel.adjacencyEntryCount_le_square model graph
  have hqueries : model.totalNeighborCost graph =
      model.vertexCount graph * model.vertexCount graph :=
    ResourceModel.ofAdjacencyMatrix_totalNeighborCost Γ vertices edge edge_iff graph
  simp only [model] at hbound hentries hqueries ⊢
  rw [hqueries] at hbound
  omega

/-- BFS accounting for an adjacency list: initialization plus two entries per edge. -/
def adjacencyListTime (n m : Nat) : Nat :=
  GraphTraversal.TimeComplexity.adjacencyList n m

/-- BFS accounting for an adjacency matrix: initialization plus at most `n` row scans. -/
def adjacencyMatrixTime (n : Nat) : Nat :=
  GraphTraversal.TimeComplexity.adjacencyMatrix n

/-- The arbitrary-cost adjacency-list trace is bounded by textbook work and supplied constants. -/
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
        bounds.checkLayerEmpty := by
  have hbound := adjacencyList_exactCost_le Γ vertices neighbors graph source hsource
    costs bounds hbounds hentries
  simp [BoundedOperational.discoveryCost, adjacencyListTime,
    GraphTraversal.TimeComplexity.adjacencyList, BoundedOperational.textbookConstant,
    Nat.add_mul, Nat.mul_add] at hbound ⊢
  omega

/-- Unit-cost specialization of the adjacency-list textbook bound. -/
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
        ((ResourceModel.ofAdjacencyList Γ vertices neighbors).vertexCount graph) m + 4 := by
  have hbound := adjacencyList_unitCost_le Γ vertices neighbors graph source hsource hentries
  unfold adjacencyListTime GraphTraversal.TimeComplexity.adjacencyList
  omega

/-- The arbitrary-cost matrix trace is bounded by textbook work and supplied constants. -/
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
          adjacencyMatrixTime (model.vertexCount graph) + bounds.checkLayerEmpty := by
  have hbound := adjacencyMatrix_exactCost_le Γ vertices edge edge_iff graph source hsource
    costs bounds hbounds
  simp [BoundedOperational.discoveryCost, adjacencyMatrixTime,
    GraphTraversal.TimeComplexity.adjacencyMatrix, BoundedOperational.textbookConstant,
    Nat.add_mul, Nat.mul_add] at hbound ⊢
  omega

/-- Unit-cost specialization of the adjacency-matrix textbook bound. -/
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
      6 * adjacencyMatrixTime (model.vertexCount graph) + 4 := by
  have hbound := adjacencyMatrix_unitCost_le Γ vertices edge edge_iff graph source hsource
  unfold adjacencyMatrixTime GraphTraversal.TimeComplexity.adjacencyMatrix
  omega

/-- Kleinberg theorem (3.11): adjacency-list BFS runs in `O(m + n)` time. -/
theorem adjacencyListTime_isBigO :
    (fun nm : Nat × Nat ↦ (adjacencyListTime nm.1 nm.2 : Real)) =O[atTop]
      fun nm ↦ (nm.2 : Real) + nm.1 := by
  simpa only [adjacencyListTime] using GraphTraversal.TimeComplexity.adjacencyList_isBigO

/-- With an adjacency matrix, BFS runs in `O(n²)` time. -/
theorem adjacencyMatrixTime_isBigO :
    (fun n : Nat ↦ (adjacencyMatrixTime n : Real)) =O[atTop]
      fun n ↦ (n : Real) ^ 2 := by
  simpa only [adjacencyMatrixTime] using GraphTraversal.TimeComplexity.adjacencyMatrix_isBigO

/-- The adjacency-list and adjacency-matrix BFS bounds, packaged together. -/
theorem timeComplexities :
    ((fun nm : Nat × Nat ↦ (adjacencyListTime nm.1 nm.2 : Real)) =O[atTop]
      fun nm ↦ (nm.2 : Real) + nm.1) ∧
    ((fun n : Nat ↦ (adjacencyMatrixTime n : Real)) =O[atTop]
      fun n ↦ (n : Real) ^ 2) :=
  ⟨adjacencyListTime_isBigO, adjacencyMatrixTime_isBigO⟩

end KleinbergBFS
