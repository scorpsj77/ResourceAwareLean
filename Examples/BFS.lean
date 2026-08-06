/-
Copyright (c) 2026 Jiyuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan
-/
import TextbookAlgorithms.KleinbergTardos.Chapter03.BFS.Complexity
import TextbookAlgorithms.KleinbergTardos.Chapter03.BFS.Correctness

/-!
# Executable toy test for Kleinberg BFS

This file is intentionally small and concrete. It gives a four-vertex graph, runs the
generic measured Kleinberg BFS model, and exposes the final state, ordered events, and
exact measured cost with `#eval`.
-/

namespace KleinbergBFSTest

open ResourceAware ResourceAware.Algorithms
open ResourceAware.Graph

inductive V where
  | s
  | a
  | b
  | c
deriving Repr, DecidableEq

open V

/-- The toy graph: `s -> a`, `s -> b`, `a -> c`, and `b -> c`. -/
def toyNeighbors : V → List V
  | s => [a, b]
  | a => [c]
  | b => [c]
  | c => []

def toyInterface : Interface Unit V where
  vertexSet := fun _ => Set.univ
  Adj := fun _ u v => v ∈ toyNeighbors u
  adj_source_mem := by
    intro
    simp
  adj_target_mem := by
    intro
    simp

def toyVertices : VertexEnumeration toyInterface where
  vertices := fun _ => [s, a, b, c]
  nodup := by
    intro
    simp
  sound := by
    intro _ v _
    exact Set.mem_univ v
  complete := by
    intro _ v _
    cases v <;> simp

def toyAccess : NeighborAccess toyInterface where
  outNeighbors := fun _ u => toyNeighbors u
  nodup := by
    intro _ u
    cases u <;> simp [toyNeighbors]
  sound := by
    intro _ _ _ h
    exact h
  complete := by
    intro _ _ _ h
    exact h

def toyAdjListModel : ResourceModel Unit V :=
  ResourceModel.ofAdjacencyList toyInterface toyVertices toyAccess

def toyMatrixEdge (_ : Unit) (u v : V) : Bool :=
  if v ∈ toyNeighbors u then true else false

theorem toyMatrixEdge_iff (g : Unit) (u v : V) :
    toyMatrixEdge g u v = true ↔ toyInterface.Adj g u v := by
  simp [toyMatrixEdge, toyInterface]

def toyAdjMatrixModel : ResourceModel Unit V :=
  ResourceModel.ofAdjacencyMatrix toyInterface toyVertices toyMatrixEdge toyMatrixEdge_iff

/--
Run BFS with:
* adjacency-list graph costs,
* Boolean-table visited state,
* vertex-indexed level table,
* edge-list tree output.
-/
def resultAdjList :=
  KleinbergBFS.Interpreter.run toyAdjListModel ()
    GraphTraversal.ControlCostModel.unit
    GraphTraversal.VisitedModel.booleanTable
    GraphTraversal.LevelModel.table
    GraphTraversal.TreeModel.edgeList
    s

def resultAdjMatrix :=
  KleinbergBFS.Interpreter.run toyAdjMatrixModel ()
    GraphTraversal.ControlCostModel.unit
    GraphTraversal.VisitedModel.booleanTable
    GraphTraversal.LevelModel.table
    GraphTraversal.TreeModel.edgeList
    s

def result := resultAdjList

def finalState := result.ret.2

def eventCostsOf (computation : TraceM (KleinbergBFS.Event V) α) :
    List (GraphTraversal.Op V × Nat) :=
  (TraceM.events computation).map fun event => (event.operation, event.measurement)

def eventCosts := eventCostsOf resultAdjList

def matrixEventCosts := eventCostsOf resultAdjMatrix

def adjListSpace :=
  KleinbergBFS.spaceUsage toyAdjListModel ()
    GraphTraversal.VisitedModel.booleanTable
    GraphTraversal.LevelModel.table
    GraphTraversal.TreeModel.edgeList

def adjMatrixSpace :=
  KleinbergBFS.spaceUsage toyAdjMatrixModel ()
    GraphTraversal.VisitedModel.booleanTable
    GraphTraversal.LevelModel.table
    GraphTraversal.TreeModel.edgeList

-- Final BFS output.
#eval finalState.visited s
#eval finalState.visited a
#eval finalState.visited b
#eval finalState.visited c
#eval finalState.levels s
#eval finalState.levels a
#eval finalState.levels b
#eval finalState.levels c
#eval finalState.tree

-- Ordered events, each paired with its measured cost contribution in adjacency list representation.
#eval eventCosts

-- Total exact cost: this is the sum of all second components in `eventCosts`.
#eval KleinbergBFS.exactCost result

-- Same BFS, same final output, but adjacency-matrix neighbor queries scan every vertex.
#eval matrixEventCosts
#eval KleinbergBFS.exactCost resultAdjMatrix

-- Graph representation space: adjacency list stores n + m, matrix stores n * n.
#eval adjListSpace.graphStorage
#eval adjMatrixSpace.graphStorage

-- Total traversal working storage for the selected visited/level/tree/layer representations.
#eval adjListSpace.traversalWorkingStorage
#eval adjMatrixSpace.traversalWorkingStorage

example : finalState.visited c = true := by decide
example : finalState.levels s = some 0 := by decide
example : finalState.levels a = some 1 := by decide
example : finalState.levels b = some 1 := by decide
example : finalState.levels c = some 2 := by decide
example : finalState.tree = [(a, c), (s, b), (s, a)] := by decide
example : KleinbergBFS.exactCost result = (eventCosts.map Prod.snd).sum := by decide
example : resultAdjList.ret.2.levels c = resultAdjMatrix.ret.2.levels c := by decide
example : KleinbergBFS.exactCost resultAdjList = 32 := by decide
example : KleinbergBFS.exactCost resultAdjMatrix = 44 := by decide
example : adjListSpace.graphStorage = 8 := by decide
example : adjMatrixSpace.graphStorage = 16 := by decide

end KleinbergBFSTest
