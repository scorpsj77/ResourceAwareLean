/-
Copyright (c) 2026 Jiyuan (Chai Yuen) Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan (Chai Yuen) Ji
-/
import ResourceAware.Foundations.Graph.GraphAdapters
import ResourceAware.Foundations.Graph.ResourceModel

/-!
# Infrastructure example: weighted graphs

This executable fixture specializes one concrete `DiGraph` to a singleton graph family so its
chosen finite vertex, neighbor, and outgoing-arc lists can be packaged as the abstract access
capabilities.  The concrete graph itself remains the semantic source for both the unweighted and
weighted views.
-/

namespace ResourceAware.Graph.Test

open Adapter.PR503

inductive Vertex where
  | source
  | middle
  | sink
deriving DecidableEq, Repr

abbrev Label := WeightedLabel Nat Nat
abbrev Arc := Concrete.Arc Vertex Label

def ordinary : Arc := ⟨⟨0, 7⟩, (.source, .middle)⟩
def zero : Arc := ⟨⟨1, 0⟩, (.source, .sink)⟩
def shorterParallel : Arc := ⟨⟨2, 3⟩, (.source, .middle)⟩
def sameWeightParallel : Arc := ⟨⟨3, 3⟩, (.source, .middle)⟩
def loop : Arc := ⟨⟨4, 2⟩, (.middle, .middle)⟩

def allArcs : List Arc :=
  [ordinary, zero, shorterParallel, sameWeightParallel, loop]

def graph : Concrete.DiGraph Vertex Label where
  vertexSet := Set.univ
  edgeSet := { edge | edge ∈ allArcs }
  incidence' := by simp

def unweightedView : Interface (Concrete.DiGraph Vertex Label) Vertex :=
  diGraphInterface Vertex Label

def concreteWeightedView :
    WeightedEdgeView unweightedView Arc Nat :=
  diGraphWeightedEdgeView Vertex Label Nat WeightedLabel.weight

/-- The selected occurrence order intentionally puts the longer parallel arc first. -/
def orderedOutgoingArcs : Vertex → List Arc
  | .source => [ordinary, zero, shorterParallel, sameWeightParallel]
  | .middle => [loop]
  | .sink => []

theorem orderedOutgoingArcs_nodup (rowSource : Vertex) :
    (orderedOutgoingArcs rowSource).Nodup := by
  cases rowSource <;> decide

theorem orderedOutgoingArcs_sound {rowSource : Vertex} {edge : Arc}
    (h : edge ∈ orderedOutgoingArcs rowSource) :
    edge ∈ graph.edgeSet ∧ edge.endpoints.1 = rowSource := by
  cases rowSource with
  | source =>
      simp only [orderedOutgoingArcs, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl <;>
        simp [graph, allArcs, ordinary, zero, shorterParallel, sameWeightParallel, loop]
  | middle =>
      simp only [orderedOutgoingArcs, List.mem_cons, List.not_mem_nil, or_false] at h
      subst edge
      simp [graph, allArcs, loop]
  | sink =>
      simp only [orderedOutgoingArcs, List.not_mem_nil] at h

theorem orderedOutgoingArcs_complete {edge : Arc} (h : edge ∈ graph.edgeSet) :
    edge ∈ orderedOutgoingArcs edge.endpoints.1 := by
  change edge ∈ allArcs at h
  simp only [allArcs, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;>
    simp [orderedOutgoingArcs, ordinary, zero, shorterParallel, sameWeightParallel, loop]

/--
Specialize the concrete graph to one executable fixture.  This is test scaffolding, not a
second graph representation: both relations below are exactly the relations of `graph`.
-/
def fixtureInterface : Interface Unit Vertex where
  vertexSet _ := unweightedView.vertexSet graph
  Adj _ := unweightedView.Adj graph
  adj_source_mem := unweightedView.adj_source_mem
  adj_target_mem := unweightedView.adj_target_mem

def fixtureWeightedView : WeightedEdgeView fixtureInterface Arc Nat where
  Arc _ := concreteWeightedView.Arc graph
  arc_adj := concreteWeightedView.arc_adj
  adj_has_arc := concreteWeightedView.adj_has_arc
  edge_unique := concreteWeightedView.edge_unique

def fixtureVertices : VertexEnumeration fixtureInterface where
  vertices _ := [.source, .middle, .sink]
  nodup := by decide
  sound := by simp [fixtureInterface, unweightedView, diGraphInterface, graph]
  complete := by
    intro _ vertex _
    cases vertex <;> simp

/-- Package any fixture vertex with its (trivial) graph-membership evidence. -/
def fixtureGraphVertex (vertex : Vertex) : GraphVertex fixtureInterface () :=
  ⟨vertex, by simp [Interface.IsVertex, fixtureInterface, unweightedView, diGraphInterface, graph]⟩

/--
The fixture's prepared dense index.  Both directions use direct pattern matching rather than
searching `fixtureVertices.vertices`.
-/
def fixtureVertexIndex : VertexIndex fixtureInterface fixtureVertices () where
  toFun
    | ⟨.source, _⟩ => ⟨0, by decide⟩
    | ⟨.middle, _⟩ => ⟨1, by decide⟩
    | ⟨.sink, _⟩ => ⟨2, by decide⟩
  invFun identifier :=
    fixtureGraphVertex <|
      match identifier.1 with
      | 0 => .source
      | 1 => .middle
      | _ => .sink
  left_inv := by
    rintro ⟨vertex, hvertex⟩
    cases vertex <;> rfl
  right_inv := by
    rintro ⟨identifier, hidentifier⟩
    cases identifier with
    | zero => rfl
    | succ identifier =>
        cases identifier with
        | zero => rfl
        | succ identifier =>
            cases identifier with
            | zero => rfl
            | succ identifier =>
                simp [fixtureVertices] at hidentifier
                omega

def fixtureNeighbors : NeighborAccess fixtureInterface where
  outNeighbors _ :=
    fun
    | .source => [.middle, .sink]
    | .middle => [.middle]
    | .sink => []
  nodup := by
    intro _ rowSource
    cases rowSource <;> decide
  sound := by
    intro _ rowSource target h
    cases rowSource <;> cases target <;>
      simp_all [fixtureInterface, unweightedView, diGraphInterface, graph, allArcs,
        ordinary, zero, shorterParallel, sameWeightParallel, loop]
  complete := by
    intro _ rowSource target h
    cases rowSource <;> cases target <;>
      simp_all [fixtureInterface, unweightedView, diGraphInterface, graph, allArcs,
        ordinary, zero, shorterParallel, sameWeightParallel, loop]

def fixtureWeightedNeighbors : WeightedNeighborAccess fixtureWeightedView where
  outEdges _ rowSource :=
    (orderedOutgoingArcs rowSource).map (outgoingEdgeOfArc WeightedLabel.weight)
  edge_nodup := by
    intro _ rowSource
    simpa [outgoingEdgeOfArc, List.map_map, Function.comp_def] using
      orderedOutgoingArcs_nodup rowSource
  sound := by
    intro _ rowSource outgoing h
    rcases List.mem_map.mp h with ⟨edge, hedge, rfl⟩
    rcases orderedOutgoingArcs_sound hedge with ⟨hmem, hrowSource⟩
    exact ⟨hmem, Prod.ext hrowSource rfl, rfl⟩
  complete := by
    intro _ edge arcSource target weight h
    rcases h with ⟨hmem, hendpoints, hweight⟩
    apply List.mem_map.mpr
    refine ⟨edge, ?_, ?_⟩
    · simpa [hendpoints] using orderedOutgoingArcs_complete hmem
    · change OutgoingEdge.mk edge edge.endpoints.2
          edge.endpointsLabel.weight = OutgoingEdge.mk edge target weight
      congr
      · exact congrArg Prod.snd hendpoints
      · exact hweight.symm

def baseModel : ResourceModel Unit Vertex :=
  ResourceModel.ofAdjacencyList fixtureInterface fixtureVertices fixtureNeighbors

def weightedModel : WeightedResourceModel Unit Vertex Arc Nat :=
  WeightedResourceModel.ofAdjacencyList
    baseModel fixtureWeightedView fixtureWeightedNeighbors

/-! The concrete weighted view covers ordinary, zero-weight, parallel, and loop arcs. -/

theorem ordinary_arc : concreteWeightedView.Arc graph ordinary .source .middle 7 := by
  simp [concreteWeightedView, diGraphWeightedEdgeView, graph, allArcs, ordinary]

theorem zero_arc : concreteWeightedView.Arc graph zero .source .sink 0 := by
  simp [concreteWeightedView, diGraphWeightedEdgeView, graph, allArcs, zero]

theorem shorterParallel_arc :
    concreteWeightedView.Arc graph shorterParallel .source .middle 3 := by
  simp [concreteWeightedView, diGraphWeightedEdgeView, graph, allArcs, shorterParallel]

theorem sameWeightParallel_arc :
    concreteWeightedView.Arc graph sameWeightParallel .source .middle 3 := by
  simp [concreteWeightedView, diGraphWeightedEdgeView, graph, allArcs, sameWeightParallel]

theorem loop_arc : concreteWeightedView.Arc graph loop .middle .middle 2 := by
  simp [concreteWeightedView, diGraphWeightedEdgeView, graph, allArcs, loop]

example : shorterParallel ≠ sameWeightParallel := by decide

/-! Weighted arcs and the existing unweighted adjacency adapter agree. -/

example {arcSource target : Vertex} :
    unweightedView.Adj graph arcSource target ↔
      ∃ edge weight, concreteWeightedView.Arc graph edge arcSource target weight :=
  ⟨concreteWeightedView.adj_has_arc,
    fun ⟨_, _, harc⟩ ↦ concreteWeightedView.arc_adj harc⟩

example : baseModel.interface.Adj () .source .middle :=
  concreteWeightedView.arc_adj ordinary_arc

example : weightedModel.edgeView.Arc () shorterParallel .source .middle 3 :=
  shorterParallel_arc

example : weightedModel.base = baseModel := rfl

/-! The prepared vertex index uses the fixture's stable dense identifiers. -/

example : fixtureVertexIndex.encode (fixtureGraphVertex .source) =
    (⟨0, by decide⟩ : Fin (fixtureVertices.vertices ()).length) := rfl
example : fixtureVertexIndex.encode (fixtureGraphVertex .middle) =
    (⟨1, by decide⟩ : Fin (fixtureVertices.vertices ()).length) := rfl
example : fixtureVertexIndex.encode (fixtureGraphVertex .sink) =
    (⟨2, by decide⟩ : Fin (fixtureVertices.vertices ()).length) := rfl

example : fixtureVertexIndex.decode
    (⟨0, by decide⟩ : Fin (fixtureVertices.vertices ()).length) =
      fixtureGraphVertex .source := rfl
example : fixtureVertexIndex.decode
    (⟨1, by decide⟩ : Fin (fixtureVertices.vertices ()).length) =
      fixtureGraphVertex .middle := rfl
example : fixtureVertexIndex.decode
    (⟨2, by decide⟩ : Fin (fixtureVertices.vertices ()).length) =
      fixtureGraphVertex .sink := rfl

example (vertex : GraphVertex fixtureInterface ()) :
    fixtureVertexIndex.decode (fixtureVertexIndex.encode vertex) = vertex :=
  VertexIndex.decode_encode fixtureVertexIndex vertex

example (identifier : Fin (fixtureVertices.vertices ()).length) :
    fixtureVertexIndex.encode (fixtureVertexIndex.decode identifier) = identifier :=
  VertexIndex.encode_decode fixtureVertexIndex identifier

example : Function.Injective fixtureVertexIndex.encode :=
  VertexIndex.encode_injective fixtureVertexIndex

example : Function.Injective fixtureVertexIndex.decode :=
  VertexIndex.decode_injective fixtureVertexIndex

example (identifier : Fin (fixtureVertices.vertices ()).length) :
    (fixtureVertexIndex.decode identifier).1 ∈ fixtureInterface.vertexSet () :=
  (fixtureVertexIndex.decode identifier).2

/-! The weighted row preserves occurrence order and repeated targets. -/

example :
    fixtureWeightedNeighbors.outEdges () .source =
      [outgoingEdgeOfArc WeightedLabel.weight ordinary,
        outgoingEdgeOfArc WeightedLabel.weight zero,
        outgoingEdgeOfArc WeightedLabel.weight shorterParallel,
        outgoingEdgeOfArc WeightedLabel.weight sameWeightParallel] := rfl

example :
    (fixtureWeightedNeighbors.outEdges () .source).map OutgoingEdge.target =
      [.middle, .sink, .middle, .middle] := rfl

example :
    (fixtureWeightedNeighbors.outEdges () .source).map OutgoingEdge.weight =
      [7, 0, 3, 3] := rfl

example :
    (fixtureWeightedNeighbors.outEdges () .source).map OutgoingEdge.edge |>.Nodup := by
  decide

/-! Completeness is occurrence-sensitive, including equal-weight arcs with distinct IDs. -/

example :
    (⟨shorterParallel, .middle, 3⟩ : OutgoingEdge Arc Vertex Nat) ∈
      fixtureWeightedNeighbors.outEdges () .source :=
  fixtureWeightedNeighbors.complete shorterParallel_arc

example :
    (⟨sameWeightParallel, .middle, 3⟩ : OutgoingEdge Arc Vertex Nat) ∈
      fixtureWeightedNeighbors.outEdges () .source :=
  fixtureWeightedNeighbors.complete sameWeightParallel_arc

/-! Exact row counts and the unit adjacency-list scan accounting. -/

example : (fixtureWeightedNeighbors.outEdges () .source).length = 4 := by decide
example : (fixtureWeightedNeighbors.outEdges () .middle).length = 1 := by decide
example : (fixtureWeightedNeighbors.outEdges () .sink).length = 0 := by decide

example : weightedModel.weightedAdjacencyEntryCount () = 5 := by decide
example : weightedModel.directedEdgeOccurrenceCount () = 5 := by decide
example : weightedModel.totalWeightedNeighborCost () = 5 := by decide
example : weightedModel.base.graphSpace () = 6 := by decide

example : weightedModel.totalWeightedNeighborCost () =
    weightedModel.directedEdgeOccurrenceCount () := by decide

example :
    (.source, ⟨shorterParallel, .middle, 3⟩) ∈
      weightedModel.directedEdgeOccurrences () :=
  weightedModel.arc_mem_directedEdgeOccurrences shorterParallel_arc

#eval (fixtureWeightedNeighbors.outEdges () .source).map fun outgoing ↦
  (outgoing.edge.endpointsLabel.id, outgoing.target, outgoing.weight)
#eval weightedModel.directedEdgeOccurrenceCount ()
#eval weightedModel.totalWeightedNeighborCost ()

end ResourceAware.Graph.Test
