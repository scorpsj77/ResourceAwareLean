/-
Copyright (c) 2026 Jiyuan (Chai Yuen) Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan (Chai Yuen) Ji
-/
import ResourceAware.Foundations.Graph.Interface

/-!
# Shared specifications for graph traversals

These predicates describe correctness properties shared by traversal algorithms without fixing a
particular control structure, interpreter, or resource model.  BFS and DFS may prove additional
algorithm-specific properties in their own `Correctness.lean` files.
-/

universe u v

namespace ResourceAware.Algorithms.GraphTraversal

open ResourceAware.Graph

/-- A traversal visits exactly the vertices reachable from its source. -/
def VisitsExactlyReachable {G : Type u} {Vertex : Type v} (graphInterface : Interface G Vertex)
    (graph : G) (source : Vertex) (visited : Vertex → Prop) : Prop :=
  ∀ vertex, visited vertex ↔ Reachable graphInterface graph source vertex

/-- Every edge recorded by a traversal-tree representation is an edge of the input graph. -/
def TreeEdgesValid {G : Type u} {Vertex : Type v} (graphInterface : Interface G Vertex)
    (graph : G) (treeEdge : Vertex → Vertex → Prop) : Prop :=
  ∀ ⦃parent child⦄, treeEdge parent child → graphInterface.Adj graph parent child

/-- Every non-root visited vertex has a recorded parent that is also visited. -/
def TreeSpansVisited {Vertex : Type v} (source : Vertex) (visited : Vertex → Prop)
    (treeEdge : Vertex → Vertex → Prop) : Prop :=
  ∀ ⦃vertex⦄, visited vertex → vertex ≠ source →
    ∃ parent, visited parent ∧ treeEdge parent vertex

/-- Source inclusion, reachability soundness, and edge closure imply exact reachability. -/
theorem visitsExactlyReachable_of_closed {G : Type u} {Vertex : Type v}
    (graphInterface : Interface G Vertex) (graph : G) (source : Vertex)
    (visited : Vertex → Prop) (hsource : visited source)
    (hsound : ∀ {vertex}, visited vertex → Reachable graphInterface graph source vertex)
    (hclosed : ∀ {parent child}, visited parent → graphInterface.Adj graph parent child →
      visited child) :
    VisitsExactlyReachable graphInterface graph source visited := by
  intro vertex
  refine ⟨hsound, fun hreachable ↦ ?_⟩
  have follow : ∀ {start target}, Reachable graphInterface graph start target →
      visited start → visited target := by
    intro start target h
    induction h with
    | refl => exact id
    | step hedge _ ih => exact fun hstart ↦ ih (hclosed hstart hedge)
  exact follow hreachable hsource

end ResourceAware.Algorithms.GraphTraversal
