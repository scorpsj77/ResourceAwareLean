/-
Copyright (c) 2026 Jiyuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan
-/
import ResourceAware.Algorithms.GraphTraversal.Language

/-!
# Kleinberg's layer-based breadth-first search

This file specializes breadth-first search to the presentation used by Kleinberg and Tardos.
The program keeps the current layer and constructs the next layer explicitly, but reuses the
shared graph-traversal signature.  Queue-based BFS and DFS can therefore request the same graph,
visited-state, level, and tree operations while choosing different control structures.

`AbstractBFS.lean` remains available as the more general, frontier-based experiment.  This
file intentionally gives the case study its own algorithm instead of making a backend
simulate layers behind an abstract frontier.
-/

universe u

namespace KleinbergBFS

open ResourceAware ResourceAware.Algorithms

/-- Kleinberg BFS programs use the shared graph-traversal free monad. -/
abbrev Program (Vertex : Type u) (α : Type u) : Type u :=
  ResourceAware.Algorithms.GraphTraversal.Program Vertex α

variable {Vertex : Type u}

/-! ## Layer-based algorithm -/

/--
Inspect the neighbors of one vertex and return exactly the vertices newly discovered from
it.  A vertex is marked before recursion continues, so a later occurrence will be skipped.
-/
def processNeighbors (u : Vertex) (nextLevel : Nat) :
    List Vertex → Program Vertex (List Vertex)
  | [] => pure []
  | v :: rest => do
      let seen ← GraphTraversal.isVisited v
      if seen.down then
        processNeighbors u nextLevel rest
      else
        GraphTraversal.markVisited v
        GraphTraversal.recordLevel v nextLevel
        GraphTraversal.addTreeEdge u v
        let fresh ← processNeighbors u nextLevel rest
        pure (v :: fresh)

/-- Process every vertex in one layer and construct the following layer. -/
def processLayer (level : Nat) : List Vertex → Program Vertex (List Vertex)
  | [] => pure []
  | u :: rest => do
      let ns ← GraphTraversal.neighbors u
      let fromU ← processNeighbors u (level + 1) ns
      let fromRest ← processLayer level rest
      pure (fromU ++ fromRest)

/--
Repeatedly construct the next layer, stopping at the first empty layer or when fuel is
exhausted.  A vertex-count upper bound supplies enough fuel for any finite simple path.
-/
def bfsLoop : Nat → Nat → List Vertex → Program Vertex PUnit
  /- fuel is exhausted and current layer is empty. final check is counted. -/
  | 0, level, [] => do
      GraphTraversal.checkLayerEmpty level
      pure .unit
  /- fuel is exhausted and current layer is nonempty. check is not charged.
  this is an error that the fuel bound is too small. -/
  | 0, _, _ => pure .unit
  /- fuel remains and current layer is empty. normal final check is counted. -/
  | _ + 1, level, [] => do
      GraphTraversal.checkLayerEmpty level
      pure .unit
  /- fuel remains and current layer is nonempty. -/
  | fuel + 1, level, current => do
      GraphTraversal.checkLayerEmpty level
      let next ← processLayer level current
      /- fuel  is included because Lean cannot see that the newly computed layer
      is making progress. Fuel is the number of vertices in the graph so that we
      can traverse at most n vertices. -/
      bfsLoop fuel (level + 1) next

/--
Run Kleinberg's BFS from `source` with explicit current and next layers.

`vertexBound` is supplied by the finite graph representation.  It is used only as
termination fuel; the current layer starts as `[source]`, and discovered vertices are
recorded by the chosen model.
-/
def bfs (vertexBound : Nat) (source : Vertex) : Program Vertex PUnit := do
  GraphTraversal.clearVisited (Vertex := Vertex)
  GraphTraversal.clearLevels (Vertex := Vertex)
  GraphTraversal.clearTree (Vertex := Vertex)
  GraphTraversal.markVisited source
  GraphTraversal.recordLevel source 0
  bfsLoop vertexBound 0 [source]

end KleinbergBFS
