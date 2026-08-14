/-
Copyright (c) 2026 Jiyuan (Chai Yuen) Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan (Chai Yuen) Ji
-/
import Cslib.Init
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

/-!
# Stable graph interface for resource-aware graph algorithms

This file is intentionally independent of CSLib's concrete graph definitions.  Graph
algorithms such as BFS should depend on this file, not on a particular `Graph`,
`SimpleGraph`, `DiGraph`, `SimpleDiGraph`, quiver, `Set`-based, or `Finset`-based API.

The split is deliberate:

* `Interface` is the mathematical graph view: vertices and adjacency.
* `NeighborAccess` is the operational view used by executable traversals.
* `VertexEnumeration` supplies a finite executable vertex collection when needed.
* `VertexIndex` optionally gives that collection dense, graph-owned identifiers.

When CSLib's graph API lands or changes, add or update adapter definitions in one
separate file that produce these records.
-/

namespace ResourceAware.Graph

universe u v w x

/-! ## Finite undirected graphs -/

/-- The degree of a vertex, defined as the number of edges incident to it. -/
def incidenceDegree {V : Type u} {E : Type v} [Fintype E] (Incident : V → E → Prop)
    [DecidableRel Incident] (vertex : V) : Nat :=
  (Finset.univ.filter (Incident vertex)).card

/-- The vertices incident to an edge. -/
def incidentVertices {V : Type u} {E : Type v} [Fintype V] (Incident : V → E → Prop)
    [DecidableRel Incident] (edge : E) : Finset V :=
  Finset.univ.filter fun vertex ↦ Incident vertex edge

/--
Kleinberg equation (3.9): in a finite undirected graph with `m` edges, the sum of the
degrees is `2 * m`.

The vertex and edge types are abstract, so the result does not depend on a graph representation.
The hypothesis `two_endpoints` expresses the textbook assumption that each edge has exactly two
incident vertices.
-/
theorem sum_degrees_eq_two_mul_edges {V : Type u} {E : Type v} [Fintype V] [Fintype E]
    (Incident : V → E → Prop) [DecidableRel Incident] {m : Nat}
    (edge_card : Fintype.card E = m)
    (two_endpoints : ∀ edge, (incidentVertices Incident edge).card = 2) :
    (∑ vertex : V, incidenceDegree Incident vertex) = 2 * m := by
  subst m
  simp only [incidenceDegree, Finset.card_filter]
  rw [Finset.sum_comm]
  simp only [Finset.sum_boole (R := Nat), Nat.cast_id]
  change (∑ edge : E, (incidentVertices Incident edge).card) = 2 * Fintype.card E
  simp [two_endpoints, Nat.mul_comm]

/--
A stable mathematical view of a directed graph-like object.

For an undirected graph, instantiate `Adj` as the symmetric adjacency relation and add a
`Symmetric` instance/proof.  BFS and reachability generally do not need to know whether the
concrete graph was represented by edge sets, adjacency matrices, adjacency lists, quivers,
`Sym2`, labels, or finite sets.
-/
structure Interface (G : Type u) (V : Type v) where
  /-- The vertices present in the graph. -/
  vertexSet : G → Set V
  /-- Directed adjacency.  Undirected graphs should expose this as a symmetric relation. -/
  Adj : G → V → V → Prop
  /-- The source of an adjacency fact is a vertex. -/
  adj_source_mem : ∀ {g : G} {x y : V}, Adj g x y → x ∈ vertexSet g
  /-- The target of an adjacency fact is a vertex. -/
  adj_target_mem : ∀ {g : G} {x y : V}, Adj g x y → y ∈ vertexSet g

namespace Interface

variable {G : Type u} {V : Type v} (Γ : Interface G V)

/-- Stable spelling for vertex membership. -/
def IsVertex (g : G) (x : V) : Prop := x ∈ Γ.vertexSet g

@[simp] theorem isVertex_iff {g : G} {x : V} :
    Γ.IsVertex g x ↔ x ∈ Γ.vertexSet g := Iff.rfl

theorem src_mem {g : G} {x y : V} (h : Γ.Adj g x y) : Γ.IsVertex g x :=
  Γ.adj_source_mem h

theorem dst_mem {g : G} {x y : V} (h : Γ.Adj g x y) : Γ.IsVertex g y :=
  Γ.adj_target_mem h

end Interface

/--
Operational neighbor access used by executable traversals.

This is intentionally not part of `Interface`: a set-based graph API may give a clean
mathematical graph view but no canonical executable neighbor enumeration.  For BFS, use
`NeighborAccess` as the primitive operation and prove it sound/complete against `Adj`.
-/
structure NeighborAccess {G : Type u} {V : Type v} (Γ : Interface G V) where
  /-- The finite list returned by one neighbor query. -/
  outNeighbors : G → V → List V
  /-- No vertex is returned more than once by a neighbor query. -/
  nodup : ∀ g x, (outNeighbors g x).Nodup
  /-- Every returned neighbor is semantically adjacent. -/
  sound : ∀ {g : G} {x y : V}, y ∈ outNeighbors g x → Γ.Adj g x y
  /-- Every semantic neighbor is returned by the query. -/
  complete : ∀ {g : G} {x y : V}, Γ.Adj g x y → y ∈ outNeighbors g x

namespace NeighborAccess

variable {G : Type u} {V : Type v} {Γ : Interface G V} (A : NeighborAccess Γ)

theorem target_mem {g : G} {x y : V} (h : y ∈ A.outNeighbors g x) :
    y ∈ Γ.vertexSet g :=
  Γ.adj_target_mem (A.sound h)

theorem source_mem {g : G} {x y : V} (h : y ∈ A.outNeighbors g x) :
    x ∈ Γ.vertexSet g :=
  Γ.adj_source_mem (A.sound h)

end NeighborAccess

/-! ## Weighted directed-edge capabilities -/

/--
A convenient edge label when the label must carry both an occurrence identifier and a weight.

The concrete `Graph` and `DiGraph` edge sets are sets.  Consequently, callers should choose
distinct `id` values for parallel edge occurrences whose endpoints and weights are otherwise
identical.  Algorithms are not required to use this label type: an adapter may interpret any
label with a function `Label → Weight`.
-/
structure WeightedLabel (EdgeId : Type w) (Weight : Type x) where
  id : EdgeId
  weight : Weight
deriving DecidableEq, Repr

/--
The data needed to relax one edge leaving a known source vertex.

Keeping the edge identifier, rather than returning only the target and weight, lets a
shortest-path algorithm remember the exact edge responsible for a successful relaxation.
-/
structure OutgoingEdge (Edge : Type w) (V : Type v) (Weight : Type x) where
  edge : Edge
  target : V
  weight : Weight
deriving DecidableEq, Repr

/--
A weighted directed-edge view extending an existing semantic graph interface.

`Arc g edge source target weight` gives an edge occurrence its identity, endpoints, and
weight.  The view neither constrains the weight type nor imposes nonnegativity; those are
algorithm-level concerns.  `edge_unique` makes an edge identifier suitable for predecessor
records by requiring it to determine one source, target, and weight in a graph.
-/
structure WeightedEdgeView {G : Type u} {V : Type v} (Γ : Interface G V)
    (Edge : Type w) (Weight : Type x) where
  Arc : G → Edge → V → V → Weight → Prop
  arc_adj : ∀ {g edge source target weight},
    Arc g edge source target weight → Γ.Adj g source target
  adj_has_arc : ∀ {g source target}, Γ.Adj g source target →
    ∃ edge weight, Arc g edge source target weight
  edge_unique : ∀ {g edge source target weight source' target' weight'},
    Arc g edge source target weight →
    Arc g edge source' target' weight' →
    source = source' ∧ target = target' ∧ weight = weight'

namespace WeightedEdgeView

variable {G : Type u} {V : Type v} {Edge : Type w} {Weight : Type x}
  {Γ : Interface G V} (Ω : WeightedEdgeView Γ Edge Weight)

/-- The source of every weighted arc belongs to the underlying graph. -/
theorem source_mem {g edge source target weight}
    (h : Ω.Arc g edge source target weight) :
    source ∈ Γ.vertexSet g :=
  Γ.adj_source_mem (Ω.arc_adj h)

/-- The target of every weighted arc belongs to the underlying graph. -/
theorem target_mem {g edge source target weight}
    (h : Ω.Arc g edge source target weight) :
    target ∈ Γ.vertexSet g :=
  Γ.adj_target_mem (Ω.arc_adj h)

end WeightedEdgeView

/--
Ordered executable access to outgoing weighted edge occurrences.

Unlike `NeighborAccess`, this capability permits repeated target vertices: parallel edges are
distinct occurrences.  Completeness is therefore stated for the entire edge record, not just
for its target.  `edge_nodup` prevents one edge identifier from appearing twice in a source
row, while the `List` result preserves the enumeration's selected occurrence order.
-/
structure WeightedNeighborAccess {G : Type u} {V : Type v} {Edge : Type w}
    {Weight : Type x} {Γ : Interface G V} (Ω : WeightedEdgeView Γ Edge Weight) where
  outEdges : G → V → List (OutgoingEdge Edge V Weight)
  edge_nodup : ∀ g source, ((outEdges g source).map OutgoingEdge.edge).Nodup
  sound : ∀ {g source outgoing}, outgoing ∈ outEdges g source →
    Ω.Arc g outgoing.edge source outgoing.target outgoing.weight
  complete : ∀ {g edge source target weight},
    Ω.Arc g edge source target weight →
      (⟨edge, target, weight⟩ : OutgoingEdge Edge V Weight) ∈ outEdges g source

namespace WeightedNeighborAccess

variable {G : Type u} {V : Type v} {Edge : Type w} {Weight : Type x}
  {Γ : Interface G V} {Ω : WeightedEdgeView Γ Edge Weight}
  (A : WeightedNeighborAccess Ω)

/-- A returned outgoing occurrence has a source in the underlying graph. -/
theorem source_mem {g source outgoing} (h : outgoing ∈ A.outEdges g source) :
    source ∈ Γ.vertexSet g :=
  Ω.source_mem (A.sound h)

/-- A returned outgoing occurrence has a target in the underlying graph. -/
theorem target_mem {g source outgoing} (h : outgoing ∈ A.outEdges g source) :
    outgoing.target ∈ Γ.vertexSet g :=
  Ω.target_mem (A.sound h)

end WeightedNeighborAccess

/--
A duplicate-free executable enumeration of the vertices in a semantic graph.

This is separate from `Interface` because the semantic interface also supports graphs for
which no finite enumeration has been selected.  Finite algorithms and resource analyses
can request this additional structure explicitly.
-/
structure VertexEnumeration {G : Type u} {V : Type v} (Γ : Interface G V) where
  vertices : G → List V
  nodup : ∀ g, (vertices g).Nodup
  sound : ∀ {g v}, v ∈ vertices g → v ∈ Γ.vertexSet g
  complete : ∀ {g v}, v ∈ Γ.vertexSet g → v ∈ vertices g

/-- A vertex together with evidence that it belongs to a particular graph. -/
abbrev GraphVertex {G : Type u} {V : Type v} (Γ : Interface G V) (g : G) :=
  {v : V // Γ.IsVertex g v}

/--
A prepared bijection between a graph's vertices and dense identifiers.

This is optional representation infrastructure supplied by a graph backend.  In particular,
it does not require every ambient vertex type to be a `Fin` type.
-/
abbrev VertexIndex {G : Type u} {V : Type v} (Γ : Interface G V)
    (enumeration : VertexEnumeration Γ) (g : G) :=
  GraphVertex Γ g ≃ Fin (enumeration.vertices g).length

namespace VertexIndex

variable {G : Type u} {V : Type v} {Γ : Interface G V}
  {enumeration : VertexEnumeration Γ} {g : G}

/-- Encode a graph vertex as its dense identifier. -/
abbrev encode (index : VertexIndex Γ enumeration g) :
    GraphVertex Γ g → Fin (enumeration.vertices g).length :=
  index

/-- Decode a dense identifier to the corresponding graph vertex. -/
abbrev decode (index : VertexIndex Γ enumeration g) :
    Fin (enumeration.vertices g).length → GraphVertex Γ g :=
  index.symm

/-- Decoding an encoded graph vertex returns the original vertex. -/
@[simp]
theorem decode_encode (index : VertexIndex Γ enumeration g) (vertex : GraphVertex Γ g) :
    index.decode (index.encode vertex) = vertex :=
  index.symm_apply_apply vertex

/-- Encoding a decoded dense identifier returns the original identifier. -/
@[simp]
theorem encode_decode (index : VertexIndex Γ enumeration g)
    (identifier : Fin (enumeration.vertices g).length) :
    index.encode (index.decode identifier) = identifier :=
  index.apply_symm_apply identifier

/-- Vertex encoding is injective. -/
theorem encode_injective (index : VertexIndex Γ enumeration g) :
    Function.Injective index.encode :=
  index.injective

/-- Vertex decoding is injective. -/
theorem decode_injective (index : VertexIndex Γ enumeration g) :
    Function.Injective index.decode :=
  index.symm.injective

end VertexIndex

/--
A stable reachability predicate for BFS correctness statements.

BFS can prove correctness against this predicate without mentioning any concrete graph API.
-/
inductive Reachable {G : Type u} {V : Type v} (Γ : Interface G V) (g : G) : V → V → Prop
  | refl {x : V} : x ∈ Γ.vertexSet g → Reachable Γ g x x
  | step {x y z : V} : Γ.Adj g x y → Reachable Γ g y z → Reachable Γ g x z

namespace Reachable

variable {G : Type u} {V : Type v} {Γ : Interface G V} {g : G}

/-- Reachability is transitive: concatenate a path from `x` to `y` with one from `y` to `z`. -/
theorem trans {x y z : V} (hxy : Reachable Γ g x y) (hyz : Reachable Γ g y z) :
    Reachable Γ g x z := by
  induction hxy with
  | refl _ => exact hyz
  | step hxy hy hih => exact Reachable.step hxy (hih hyz)

end Reachable

/-! ## Directed graph properties -/

namespace Interface

variable {G : Type u} {V : Type v} (Γ : Interface G V) (g : G)

/-- Two vertices are mutually reachable if each can reach the other by a directed path. -/
def MutuallyReachable (x y : V) : Prop :=
  Reachable Γ g x y ∧ Reachable Γ g y x

/-- The strong component containing `source`: all vertices mutually reachable with it. -/
def StrongComponent (source : V) : Set V :=
  { vertex | Γ.MutuallyReachable g source vertex }

variable {Γ} {g}

/-- Mutual reachability is symmetric. -/
theorem mutuallyReachable_symm {x y : V} (h : Γ.MutuallyReachable g x y) :
    Γ.MutuallyReachable g y x :=
  ⟨h.2, h.1⟩

/--
Kleinberg theorem (3.16): if `u` and `v` are mutually reachable, and `v` and `w` are
mutually reachable, then `u` and `w` are mutually reachable.
-/
theorem mutuallyReachable_trans {u v w : V}
    (huv : Γ.MutuallyReachable g u v) (hvw : Γ.MutuallyReachable g v w) :
    Γ.MutuallyReachable g u w :=
  ⟨Reachable.trans huv.1 hvw.1, Reachable.trans hvw.2 huv.2⟩

/-- Mutually reachable vertices have identical strong components. -/
theorem strongComponent_eq_of_mutuallyReachable {s t : V}
    (hst : Γ.MutuallyReachable g s t) :
    Γ.StrongComponent g s = Γ.StrongComponent g t := by
  ext vertex
  constructor
  · intro hsv
    exact mutuallyReachable_trans (mutuallyReachable_symm hst) hsv
  · intro htv
    exact mutuallyReachable_trans hst htv

/--
Kleinberg theorem (3.17): for any two vertices `s` and `t`, their strong components are
either identical or disjoint.
-/
theorem strongComponents_eq_or_disjoint (s t : V) :
    Γ.StrongComponent g s = Γ.StrongComponent g t ∨
      Γ.StrongComponent g s ∩ Γ.StrongComponent g t = ∅ := by
  by_cases hst : Γ.MutuallyReachable g s t
  · exact Or.inl (strongComponent_eq_of_mutuallyReachable hst)
  · right
    ext vertex
    constructor
    · intro hvertex
      rcases hvertex with ⟨hsv, htv⟩
      exact False.elim (hst (mutuallyReachable_trans hsv (mutuallyReachable_symm htv)))
    · intro hvertex
      exact False.elim hvertex

end Interface

/-! ## Undirected graph properties -/

namespace Interface

variable {G : Type u} {V : Type v} (Γ : Interface G V)

/-- Evidence that an interface presents an undirected simple graph. -/
structure IsUndirected (g : G) : Prop where
  symmetric : Std.Symm (Γ.Adj g)
  loopless : Std.Irrefl (Γ.Adj g)

namespace IsUndirected

/-- A proof-only `SimpleGraph` view of a representation-independent graph interface. -/
def toSimpleGraph {g : G} (h : Γ.IsUndirected g) : SimpleGraph V where
  Adj := Γ.Adj g
  symm := h.symmetric
  loopless := h.loopless

end IsUndirected

/-- A two-coloring in which the endpoints of every edge have different colors. -/
def IsBipartite (g : G) : Prop :=
  ∃ color : V → Fin 2, ∀ ⦃x y⦄, Γ.Adj g x y → color x ≠ color y

/-- The graph contains a simple cycle with an odd number of edges. -/
def ContainsOddCycle {g : G} (h : Γ.IsUndirected g) : Prop :=
  ∃ vertex, ∃ cycle : h.toSimpleGraph.Walk vertex vertex,
    cycle.IsCycle ∧ Odd cycle.length

/--
Kleinberg theorem (3.14): a bipartite graph cannot contain an odd cycle.

The proof follows the textbook coloring argument: colors alternate along every edge of a walk,
so returning to the starting color requires an even number of edges.
-/
theorem bipartite_has_no_odd_cycle {g : G} (h : Γ.IsUndirected g)
    (hbipartite : Γ.IsBipartite g) : ¬ Γ.ContainsOddCycle h := by
  classical
  /- Toward a contradiction, suppose there is an odd cycle. Extracts the starting vertex,
  the closed walk, and the fact that its length is odd. -/
  rintro ⟨vertex, cycle, _, hodd⟩
  /- Extract the bipartite coloring. -/
  rcases hbipartite with ⟨color, hcolor⟩
  /- Package it as mathlib's SimpleGraph.Coloring (Fin 2)-/
  let coloringFin : h.toSimpleGraph.Coloring (Fin 2) := ⟨color, by
    intro x y hadj
    simpa using hcolor hadj⟩
  /- Convert two colors from Fin 2 to Bool, which allows us to use the lemma that
  an odd walk has opposite-colored endpoints. -/
  let coloring : h.toSimpleGraph.Coloring Bool :=
    SimpleGraph.recolorOfEquiv h.toSimpleGraph finTwoEquiv coloringFin
  have hcontra := (coloring.odd_length_iff_not_congr cycle).mp hodd
  /- But cycle begins and ends at the same vertex, which is now said to have different colors,
  hence impossible.-/
  tauto

end Interface

end ResourceAware.Graph
