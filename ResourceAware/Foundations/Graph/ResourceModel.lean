/-
Copyright (c) 2026 Jiyuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan
-/
import ResourceAware.Foundations.Graph.Interface
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic.Linarith

/-!
# Resource models for executable graph representations

This file sits one layer above `GraphInterface`: it keeps the mathematical graph view,
finite vertex enumeration, executable neighbor query, and graph-representation costs
together.  Algorithm-specific state, traces, and working storage live in algorithm
modules such as `GraphTraversal`.
-/

namespace ResourceAware.Graph

universe u v w x

/--
The graph-side data needed by a resource-aware traversal.

The mathematical graph, its finite enumeration, and its neighbor query are kept together,
but BFS-specific state and working storage deliberately do not appear here.  `neighborCost`
is the cost of one call to `outNeighbors`; `graphSpace` is the storage of the graph
representation itself.
-/
structure ResourceModel (G : Type u) (V : Type v) where
  interface : Interface G V
  vertexEnumeration : VertexEnumeration interface
  neighborAccess : NeighborAccess interface
  neighborCost : G → V → Nat
  graphSpace : G → Nat

/--
The graph-side data additionally needed by weighted algorithms.

The existing `ResourceModel` remains the owner of the semantic graph interface, vertex and
unweighted-neighbor enumerations, query costs, and graph-space accounting.  This extension
adds only a weighted edge view, ordered outgoing-edge access, and the aggregate cost of one
weighted outgoing-row query.
-/
structure WeightedResourceModel (G : Type u) (V : Type v) (Edge : Type w)
    (Weight : Type x) where
  base : ResourceModel G V
  edgeView : WeightedEdgeView base.interface Edge Weight
  weightedNeighborAccess : WeightedNeighborAccess edgeView
  weightedNeighborCost : G → V → Nat

namespace ResourceModel

variable {G : Type u} {V : Type v}

open Filter Asymptotics

/-- Number of vertices in the selected finite enumeration. -/
def vertexCount (model : ResourceModel G V) (g : G) : Nat :=
  (model.vertexEnumeration.vertices g).length

/-- Sum of the lengths of all executable adjacency lists. -/
def adjacencyEntryCount (model : ResourceModel G V) (g : G) : Nat :=
  ((model.vertexEnumeration.vertices g).map fun u ↦
    (model.neighborAccess.outNeighbors g u).length).sum

/-- Cost of asking for the neighbors of every vertex once. -/
def totalNeighborCost (model : ResourceModel G V) (g : G) : Nat :=
  ((model.vertexEnumeration.vertices g).map fun u ↦ model.neighborCost g u).sum

/-- Every duplicate-free neighbor list is bounded by the finite vertex enumeration. -/
theorem neighborList_length_le_vertexCount
    (model : ResourceModel G V) (g : G) (vertex : V) :
    (model.neighborAccess.outNeighbors g vertex).length ≤ model.vertexCount g := by
  classical
  change (model.neighborAccess.outNeighbors g vertex).length ≤
    (model.vertexEnumeration.vertices g).length
  have hsubset :
      (model.neighborAccess.outNeighbors g vertex).toFinset ⊆
        (model.vertexEnumeration.vertices g).toFinset := by
    intro candidate hcandidate
    rw [List.mem_toFinset] at hcandidate ⊢
    exact model.vertexEnumeration.complete
      (model.neighborAccess.target_mem hcandidate)
  rw [← List.toFinset_card_of_nodup (model.neighborAccess.nodup g vertex),
    ← List.toFinset_card_of_nodup (model.vertexEnumeration.nodup g)]
  exact Finset.card_le_card hsubset

/-- At most `n²` distinct adjacency entries can be returned across `n` vertices. -/
theorem adjacencyEntryCount_le_square (model : ResourceModel G V) (g : G) :
    model.adjacencyEntryCount g ≤ model.vertexCount g * model.vertexCount g := by
  unfold adjacencyEntryCount
  calc
    ((model.vertexEnumeration.vertices g).map fun vertex ↦
        (model.neighborAccess.outNeighbors g vertex).length).sum
        ≤ ((model.vertexEnumeration.vertices g).map fun _ ↦ model.vertexCount g).sum := by
          apply List.sum_le_sum
          intro vertex _
          exact neighborList_length_le_vertexCount model g vertex
    _ = model.vertexCount g * model.vertexCount g := by
      simp [vertexCount]

/-- A duplicate-free sublist has bounded length and bounded sum of nonnegative weights. -/
theorem nodup_sublist_length_and_sum_le (selected available : List V) (weight : V → Nat)
    (hselected : selected.Nodup) (havailable : available.Nodup)
    (hsubset : ∀ vertex ∈ selected, vertex ∈ available) :
    selected.length ≤ available.length ∧
      (selected.map weight).sum ≤ (available.map weight).sum := by
  classical
  have hfinset : selected.toFinset ⊆ available.toFinset := by
    intro vertex hvertex
    rw [List.mem_toFinset] at hvertex ⊢
    exact hsubset vertex hvertex
  constructor
  · rw [← List.toFinset_card_of_nodup hselected,
      ← List.toFinset_card_of_nodup havailable]
    exact Finset.card_le_card hfinset
  · rw [← List.sum_toFinset weight hselected, ← List.sum_toFinset weight havailable]
    exact Finset.sum_le_sum_of_subset_of_nonneg hfinset (fun _ _ _ ↦ Nat.zero_le _)

/-- Number of cells in an `n × n` adjacency matrix. -/
def adjacencyMatrixSpace (n : Nat) : Nat :=
  n * n

/--
Storage for an undirected adjacency list with `n` vertex records and `m` edges.

Each edge contributes two adjacency-list entries by equation (3.9).
-/
def adjacencyListSpace (n m : Nat) : Nat :=
  n + 2 * m

/-- Equation (3.9) turns `n` vertex records plus all adjacency lists into `n + 2m`. -/
theorem vertexCount_add_sum_degrees_eq_adjacencyListSpace
    {Vertex : Type u} {Edge : Type v} [Fintype Vertex] [Fintype Edge]
    (Incident : Vertex → Edge → Prop) [DecidableRel Incident] {m : Nat}
    (edge_card : Fintype.card Edge = m)
    (two_endpoints : ∀ edge, (incidentVertices Incident edge).card = 2) :
    Fintype.card Vertex + (∑ vertex : Vertex, incidenceDegree Incident vertex) =
      adjacencyListSpace (Fintype.card Vertex) m := by
  rw [sum_degrees_eq_two_mul_edges Incident edge_card two_endpoints]
  rfl

/--
Build the usual adjacency-list resource model: a query costs the length of the returned
list, and graph storage is `n` plus the total number of adjacency-list entries.
-/
def ofAdjacencyList (Γ : Interface G V) (vertices : VertexEnumeration Γ)
    (neighbors : NeighborAccess Γ) : ResourceModel G V where
  interface := Γ
  vertexEnumeration := vertices
  neighborAccess := neighbors
  neighborCost := fun g u ↦ (neighbors.outNeighbors g u).length
  graphSpace := fun g ↦
    (vertices.vertices g).length +
      ((vertices.vertices g).map fun u ↦ (neighbors.outNeighbors g u).length).sum

/-- Enumerate one adjacency-matrix row by scanning every vertex. -/
def matrixOutNeighbors (Γ : Interface G V) (vertices : VertexEnumeration Γ)
    (edge : G → V → V → Bool) (g : G) (u : V) : List V :=
  (vertices.vertices g).filter fun v ↦ edge g u v

/-- Verify that filtering a matrix row implements semantic neighbor access. -/
def matrixNeighborAccess (Γ : Interface G V) (vertices : VertexEnumeration Γ)
    (edge : G → V → V → Bool)
    (edge_iff : ∀ g u v, edge g u v = true ↔ Γ.Adj g u v) : NeighborAccess Γ where
  outNeighbors := matrixOutNeighbors Γ vertices edge
  nodup := by
    intro g u
    exact (vertices.nodup g).filter _
  sound := by
    intro g u v hv
    have hedge : edge g u v = true := (List.mem_filter.mp hv).2
    exact (edge_iff g u v).mp hedge
  complete := by
    intro g u v huv
    apply List.mem_filter.mpr
    exact ⟨vertices.complete (Γ.adj_target_mem huv), (edge_iff g u v).mpr huv⟩

/--
Build the usual adjacency-matrix resource model: every query scans `n` cells, and graph
storage is `n²`.
-/
def ofAdjacencyMatrix (Γ : Interface G V) (vertices : VertexEnumeration Γ)
    (edge : G → V → V → Bool)
    (edge_iff : ∀ g u v, edge g u v = true ↔ Γ.Adj g u v) : ResourceModel G V where
  interface := Γ
  vertexEnumeration := vertices
  neighborAccess := matrixNeighborAccess Γ vertices edge edge_iff
  neighborCost := fun g _ ↦ (vertices.vertices g).length
  graphSpace := fun g ↦ adjacencyMatrixSpace (vertices.vertices g).length

@[simp]
theorem ofAdjacencyList_graphSpace (Γ : Interface G V) (vertices : VertexEnumeration Γ)
    (neighbors : NeighborAccess Γ) (g : G) :
    (ofAdjacencyList Γ vertices neighbors).graphSpace g =
      (ofAdjacencyList Γ vertices neighbors).vertexCount g +
        (ofAdjacencyList Γ vertices neighbors).adjacencyEntryCount g := rfl

@[simp]
theorem ofAdjacencyMatrix_graphSpace (Γ : Interface G V) (vertices : VertexEnumeration Γ)
    (edge : G → V → V → Bool)
    (edge_iff : ∀ g u v, edge g u v = true ↔ Γ.Adj g u v) (g : G) :
    (ofAdjacencyMatrix Γ vertices edge edge_iff).graphSpace g =
      adjacencyMatrixSpace (vertices.vertices g).length := rfl

/-- Scanning every adjacency list once visits exactly all stored adjacency entries. -/
@[simp]
theorem ofAdjacencyList_totalNeighborCost (Γ : Interface G V)
    (vertices : VertexEnumeration Γ) (neighbors : NeighborAccess Γ) (g : G) :
    (ofAdjacencyList Γ vertices neighbors).totalNeighborCost g =
      (ofAdjacencyList Γ vertices neighbors).adjacencyEntryCount g := rfl

/-- Scanning every adjacency-matrix row once examines exactly `n²` cells. -/
@[simp]
theorem ofAdjacencyMatrix_totalNeighborCost (Γ : Interface G V)
    (vertices : VertexEnumeration Γ) (edge : G → V → V → Bool)
    (edge_iff : ∀ g u v, edge g u v = true ↔ Γ.Adj g u v) (g : G) :
    (ofAdjacencyMatrix Γ vertices edge edge_iff).totalNeighborCost g =
      adjacencyMatrixSpace (vertices.vertices g).length := by
  simp [totalNeighborCost, ofAdjacencyMatrix, adjacencyMatrixSpace]

/--
An adjacency-list model has exact storage `n + 2m` once equation (3.9) identifies its total
number of adjacency entries as `2m`.
-/
theorem ofAdjacencyList_graphSpace_eq_adjacencyListSpace
    (Γ : Interface G V) (vertices : VertexEnumeration Γ) (neighbors : NeighborAccess Γ)
    (g : G) {m : Nat}
    (hentries : (ofAdjacencyList Γ vertices neighbors).adjacencyEntryCount g = 2 * m) :
    (ofAdjacencyList Γ vertices neighbors).graphSpace g =
      adjacencyListSpace ((ofAdjacencyList Γ vertices neighbors).vertexCount g) m := by
  rw [ofAdjacencyList_graphSpace, hentries]
  rfl

/-- Adjacency-matrix storage is `O(n²)`. -/
theorem adjacencyMatrixSpace_isBigO :
    (fun n : Nat ↦ (adjacencyMatrixSpace n : Real)) =O[atTop]
      fun n ↦ (n : Real) ^ 2 := by
  simpa only [adjacencyMatrixSpace, Nat.cast_mul, pow_two] using
    isBigO_refl (fun n : Nat ↦ (n : Real) * n) atTop

/-- Undirected adjacency-list storage is `O(m + n)`. -/
theorem adjacencyListSpace_isBigO :
    (fun nm : Nat × Nat ↦ (adjacencyListSpace nm.1 nm.2 : Real)) =O[atTop]
      fun nm ↦ (nm.2 : Real) + nm.1 := by
  refine IsBigO.of_bound 2 (Eventually.of_forall fun nm ↦ ?_)
  simp only [adjacencyListSpace, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Real.norm_eq_abs]
  rw [abs_of_nonneg, abs_of_nonneg]
  · have hn : (0 : Real) ≤ nm.1 := by positivity
    linarith
  · positivity
  · positivity

/--
Kleinberg theorem (3.10): adjacency matrices use `O(n²)` space, while undirected adjacency
lists use `O(m + n)` space.
-/
theorem adjacency_representation_space_isBigO :
    ((fun n : Nat ↦ (adjacencyMatrixSpace n : Real)) =O[atTop]
      fun n ↦ (n : Real) ^ 2) ∧
    ((fun nm : Nat × Nat ↦ (adjacencyListSpace nm.1 nm.2 : Real)) =O[atTop]
      fun nm ↦ (nm.2 : Real) + nm.1) :=
  ⟨adjacencyMatrixSpace_isBigO, adjacencyListSpace_isBigO⟩

end ResourceModel

namespace WeightedResourceModel

variable {G : Type u} {V : Type v} {Edge : Type w} {Weight : Type x}

/-- Sum of the lengths of all ordered weighted outgoing rows. -/
def weightedAdjacencyEntryCount (model : WeightedResourceModel G V Edge Weight)
    (g : G) : Nat :=
  ((model.base.vertexEnumeration.vertices g).map fun source ↦
    (model.weightedNeighborAccess.outEdges g source).length).sum

/-- All directed edge occurrences, paired with the source row in which they occur. -/
def directedEdgeOccurrences (model : WeightedResourceModel G V Edge Weight)
    (g : G) : List (V × OutgoingEdge Edge V Weight) :=
  (model.base.vertexEnumeration.vertices g).flatMap fun source ↦
    (model.weightedNeighborAccess.outEdges g source).map fun outgoing ↦ (source, outgoing)

/-- Number of directed edge occurrences in all selected outgoing rows. -/
def directedEdgeOccurrenceCount (model : WeightedResourceModel G V Edge Weight)
    (g : G) : Nat :=
  (model.directedEdgeOccurrences g).length

/-- Cost of querying every weighted outgoing row once. -/
def totalWeightedNeighborCost (model : WeightedResourceModel G V Edge Weight)
    (g : G) : Nat :=
  ((model.base.vertexEnumeration.vertices g).map fun source ↦
    model.weightedNeighborCost g source).sum

/-- Concatenating the outgoing rows counts the same entries as summing their lengths. -/
@[simp]
theorem directedEdgeOccurrenceCount_eq_weightedAdjacencyEntryCount
    (model : WeightedResourceModel G V Edge Weight) (g : G) :
    model.directedEdgeOccurrenceCount g = model.weightedAdjacencyEntryCount g := by
  simp [directedEdgeOccurrenceCount, directedEdgeOccurrences, weightedAdjacencyEntryCount]

/-- Every semantic weighted arc occurs in the selected row for its source. -/
theorem arc_mem_source_row (model : WeightedResourceModel G V Edge Weight)
    {g edge source target weight}
    (h : model.edgeView.Arc g edge source target weight) :
    (⟨edge, target, weight⟩ : OutgoingEdge Edge V Weight) ∈
      model.weightedNeighborAccess.outEdges g source :=
  model.weightedNeighborAccess.complete h

/-- Every semantic weighted arc is counted among all directed edge occurrences. -/
theorem arc_mem_directedEdgeOccurrences
    (model : WeightedResourceModel G V Edge Weight)
    {g edge source target weight}
    (h : model.edgeView.Arc g edge source target weight) :
    (source, ⟨edge, target, weight⟩) ∈ model.directedEdgeOccurrences g := by
  apply List.mem_flatMap.mpr
  refine ⟨source, model.base.vertexEnumeration.complete (model.edgeView.source_mem h), ?_⟩
  apply List.mem_map.mpr
  exact ⟨⟨edge, target, weight⟩, model.weightedNeighborAccess.complete h, rfl⟩

/-- Every counted directed edge occurrence is sound for the weighted semantic view. -/
theorem directedEdgeOccurrences_sound
    (model : WeightedResourceModel G V Edge Weight)
    {g source outgoing}
    (h : (source, outgoing) ∈ model.directedEdgeOccurrences g) :
    model.edgeView.Arc g outgoing.edge source outgoing.target outgoing.weight := by
  rcases List.mem_flatMap.mp h with ⟨rowSource, _, hrow⟩
  rcases List.mem_map.mp hrow with ⟨rowOutgoing, hmem, heq⟩
  cases heq
  exact model.weightedNeighborAccess.sound hmem

/--
Build the unit adjacency-list scan model for weighted outgoing rows.

The base model, including its unweighted access and graph-space accounting, is reused
unchanged.  One weighted row query costs exactly the number of edge occurrences returned.
-/
def ofAdjacencyList (base : ResourceModel G V)
    (edgeView : WeightedEdgeView base.interface Edge Weight)
    (weightedNeighbors : WeightedNeighborAccess edgeView) :
    WeightedResourceModel G V Edge Weight where
  base := base
  edgeView := edgeView
  weightedNeighborAccess := weightedNeighbors
  weightedNeighborCost := fun g source ↦ (weightedNeighbors.outEdges g source).length

/-- Scanning every weighted outgoing row once costs exactly the number of its entries. -/
@[simp]
theorem ofAdjacencyList_totalWeightedNeighborCost
    (base : ResourceModel G V)
    (edgeView : WeightedEdgeView base.interface Edge Weight)
    (weightedNeighbors : WeightedNeighborAccess edgeView) (g : G) :
    (ofAdjacencyList base edgeView weightedNeighbors).totalWeightedNeighborCost g =
      (ofAdjacencyList base edgeView weightedNeighbors).weightedAdjacencyEntryCount g := rfl

/--
Under the unit adjacency-list scan model, scanning every source row once costs exactly the
directed edge-occurrence count `m`.
-/
theorem ofAdjacencyList_totalWeightedNeighborCost_eq
    (base : ResourceModel G V)
    (edgeView : WeightedEdgeView base.interface Edge Weight)
    (weightedNeighbors : WeightedNeighborAccess edgeView) (g : G) {m : Nat}
    (hcount :
      (ofAdjacencyList base edgeView weightedNeighbors).directedEdgeOccurrenceCount g = m) :
    (ofAdjacencyList base edgeView weightedNeighbors).totalWeightedNeighborCost g = m := by
  rw [ofAdjacencyList_totalWeightedNeighborCost,
    ← directedEdgeOccurrenceCount_eq_weightedAdjacencyEntryCount, hcount]

end WeightedResourceModel

end ResourceAware.Graph
