/-
Copyright (c) 2026 Jiyuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan
-/
import ResourceAware.Foundations.Graph.Interface
import ThirdParty.Graph
import Mathlib.Data.Sym.Sym2

/-!
# Adapter for the graph definitions proposed in CSLib PR #503

Keep this file, or its eventual successor, as the only file that imports the experimental
concrete graph API. BFS and resource theorems should import `ResourceAware.Graph.Interface`
instead.

This file tracks the definitions visible in PR #503 at the time of writing. If the PR lands,
only this adapter should switch to the official CSLib module.
-/

namespace ResourceAware.Graph.Adapter.PR503

universe u v w

/-- Adapter for PR #503 undirected multigraphs. -/
def graphInterface (α : Type u) (β : Type v) :
    ResourceAware.Graph.Interface (ResourceAware.Graph.Concrete.Graph α β) α where
  vertexSet := ResourceAware.Graph.Concrete.Graph.vertexSet
  Adj G x y := ∃ e, e ∈ G.edgeSet ∧ e.endpoints = Sym2.mk x y
  adj_source_mem := by
    intro G x y h
    rcases h with ⟨e, he, hend⟩
    exact G.incidence' e he x (by
      rw [hend]
      exact Sym2.mem_mk_left x y)
  adj_target_mem := by
    intro G x y h
    rcases h with ⟨e, he, hend⟩
    exact G.incidence' e he y (by
      rw [hend]
      exact Sym2.mem_mk_right x y)

/-- Adapter for PR #503 simple undirected graphs. -/
def simpleGraphInterface (α : Type u) :
    ResourceAware.Graph.Interface (ResourceAware.Graph.Concrete.SimpleGraph α) α where
  vertexSet := ResourceAware.Graph.Concrete.SimpleGraph.vertexSet
  Adj G x y := Sym2.mk x y ∈ G.edgeSet
  adj_source_mem := by
    intro G x y h
    exact G.incidence' (Sym2.mk x y) h x (Sym2.mem_mk_left x y)
  adj_target_mem := by
    intro G x y h
    exact G.incidence' (Sym2.mk x y) h y (Sym2.mem_mk_right x y)

/-- Adapter for PR #503 directed multigraphs. -/
def diGraphInterface (α : Type u) (β : Type v) :
    ResourceAware.Graph.Interface (ResourceAware.Graph.Concrete.DiGraph α β) α where
  vertexSet := ResourceAware.Graph.Concrete.DiGraph.vertexSet
  Adj G x y := ∃ e, e ∈ G.edgeSet ∧ e.endpoints = (x, y)
  adj_source_mem := by
    intro G x y h
    rcases h with ⟨e, he, hend⟩
    exact show x ∈ G.vertexSet from by
      simpa [hend] using (G.incidence' e he).1
  adj_target_mem := by
    intro G x y h
    rcases h with ⟨e, he, hend⟩
    exact show y ∈ G.vertexSet from by
      simpa [hend] using (G.incidence' e he).2

/-! ### Weighted directed-graph adapter -/

/-- Interpret one concrete directed arc as the outgoing-edge record used by algorithms. -/
def outgoingEdgeOfArc {α : Type u} {β : Type v} {Weight : Type w}
    (weightOf : β → Weight) (edge : ResourceAware.Graph.Concrete.Arc α β) :
    OutgoingEdge (ResourceAware.Graph.Concrete.Arc α β) α Weight :=
  ⟨edge, edge.endpoints.2, weightOf edge.endpointsLabel⟩

/--
Weighted semantic view of the existing concrete `DiGraph`.

The edge occurrence identifier is the complete concrete `Arc`; the supplied function only
interprets its label as a weight.  Since `DiGraph.edgeSet` is a set, labels must differ when
parallel occurrences with the same endpoints and derived weight must remain distinct.  A
`WeightedLabel EdgeId Weight` with distinct identifiers is one convenient choice.
-/
def diGraphWeightedEdgeView (α : Type u) (β : Type v) (Weight : Type w)
    (weightOf : β → Weight) :
    WeightedEdgeView (diGraphInterface α β)
      (ResourceAware.Graph.Concrete.Arc α β) Weight where
  Arc G edge source target weight :=
    edge ∈ G.edgeSet ∧
      edge.endpoints = (source, target) ∧
      weight = weightOf edge.endpointsLabel
  arc_adj := by
    rintro G edge source target weight ⟨hedge, hendpoints, _⟩
    exact ⟨edge, hedge, hendpoints⟩
  adj_has_arc := by
    rintro G source target ⟨edge, hedge, hendpoints⟩
    exact ⟨edge, weightOf edge.endpointsLabel, hedge, hendpoints, rfl⟩
  edge_unique := by
    rintro G edge source target weight source' target' weight'
      ⟨_, hendpoints, hweight⟩ ⟨_, hendpoints', hweight'⟩
    have hpairs : (source, target) = (source', target') :=
      hendpoints.symm.trans hendpoints'
    exact ⟨congrArg Prod.fst hpairs, congrArg Prod.snd hpairs,
      hweight.trans hweight'.symm⟩

/--
Verify a selected executable outgoing-arc enumeration against the concrete semantic edge set.

The adapter maps the supplied list without sorting or deduplicating it, so occurrence order is
preserved.  `outgoingArcs_nodup` concerns concrete arc identities, not target vertices, and
therefore permits parallel arcs.  No executable enumeration is derived from `DiGraph.edgeSet`
automatically because that field is a `Set`.
-/
def diGraphWeightedNeighborAccess {α : Type u} {β : Type v} {Weight : Type w}
    (weightOf : β → Weight)
    (outgoingArcs :
      ResourceAware.Graph.Concrete.DiGraph α β → α →
        List (ResourceAware.Graph.Concrete.Arc α β))
    (outgoingArcs_nodup : ∀ G source, (outgoingArcs G source).Nodup)
    (outgoingArcs_sound : ∀ {G source edge}, edge ∈ outgoingArcs G source →
      edge ∈ G.edgeSet ∧ edge.endpoints.1 = source)
    (outgoingArcs_complete : ∀ {G edge}, edge ∈ G.edgeSet →
      edge ∈ outgoingArcs G edge.endpoints.1) :
    WeightedNeighborAccess (diGraphWeightedEdgeView α β Weight weightOf) where
  outEdges := fun G source ↦
    (outgoingArcs G source).map (outgoingEdgeOfArc weightOf)
  edge_nodup := by
    intro G source
    simpa [outgoingEdgeOfArc, List.map_map, Function.comp_def] using
      outgoingArcs_nodup G source
  sound := by
    intro G source outgoing houtgoing
    rcases List.mem_map.mp houtgoing with ⟨edge, hedge, rfl⟩
    rcases outgoingArcs_sound hedge with ⟨hmem, hsource⟩
    exact ⟨hmem, Prod.ext hsource rfl, rfl⟩
  complete := by
    intro G edge source target weight harc
    rcases harc with ⟨hmem, hendpoints, hweight⟩
    apply List.mem_map.mpr
    refine ⟨edge, ?_, ?_⟩
    · simpa [hendpoints] using outgoingArcs_complete hmem
    · change OutgoingEdge.mk edge edge.endpoints.2
          (weightOf edge.endpointsLabel) = OutgoingEdge.mk edge target weight
      congr
      · exact congrArg Prod.snd hendpoints
      · exact hweight.symm

/-- Adapter for PR #503 simple directed graphs. -/
def simpleDiGraphInterface (α : Type u) :
    ResourceAware.Graph.Interface (ResourceAware.Graph.Concrete.SimpleDiGraph α) α where
  vertexSet := ResourceAware.Graph.Concrete.SimpleDiGraph.vertexSet
  Adj G x y := (x, y) ∈ G.edgeSet
  adj_source_mem := by
    intro G x y h
    exact (G.incidence' (x, y) h).1
  adj_target_mem := by
    intro G x y h
    exact (G.incidence' (x, y) h).2

end ResourceAware.Graph.Adapter.PR503
