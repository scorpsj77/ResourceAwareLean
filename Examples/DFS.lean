/-
Copyright (c) 2026 Jiyuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan
-/
import TextbookAlgorithms.KleinbergTardos.Chapter03.DFS.Complexity
import TextbookAlgorithms.KleinbergTardos.Chapter03.DFS.Correctness

/-!
# Executable toy test for Kleinberg DFS

This file runs the stack-based DFS model on a four-vertex graph with both adjacency-list
and adjacency-matrix resource models.  The `#eval`s expose final explored state, ordered events,
exact measured work, and representation space.
-/

namespace KleinbergDFSTest

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

def resultAdjList :=
  KleinbergDFS.Interpreter.run toyAdjListModel ()
    GraphTraversal.ControlCostModel.unit
    GraphTraversal.VisitedModel.booleanTable
    s

def resultAdjMatrix :=
  KleinbergDFS.Interpreter.run toyAdjMatrixModel ()
    GraphTraversal.ControlCostModel.unit
    GraphTraversal.VisitedModel.booleanTable
    s

def finalState := resultAdjList.ret.2

def eventCostsOf (computation : TraceM (KleinbergDFS.Event V) α) :
    List (GraphTraversal.Op V × Nat) :=
  (TraceM.events computation).map fun event => (event.operation, event.measurement)

def adjListEventCosts := eventCostsOf resultAdjList

def adjMatrixEventCosts := eventCostsOf resultAdjMatrix

def adjListSpace :=
  KleinbergDFS.spaceUsage toyAdjListModel ()
    GraphTraversal.VisitedModel.booleanTable

def adjMatrixSpace :=
  KleinbergDFS.spaceUsage toyAdjMatrixModel ()
    GraphTraversal.VisitedModel.booleanTable

-- Final explored-state output.
#eval finalState.visited s
#eval finalState.visited a
#eval finalState.visited b
#eval finalState.visited c

-- Ordered adjacency-list DFS events, each paired with its measured cost contribution.
#eval adjListEventCosts
#eval KleinbergDFS.exactCost resultAdjList

-- Same DFS, but adjacency-matrix neighbor queries scan every vertex.
#eval adjMatrixEventCosts
#eval KleinbergDFS.exactCost resultAdjMatrix

-- Graph representation space and DFS working-storage bound.
#eval adjListSpace.graphStorage
#eval adjMatrixSpace.graphStorage
#eval adjListSpace.traversalWorkingStorage
#eval adjMatrixSpace.traversalWorkingStorage

example : finalState.visited s = true := by decide
example : finalState.visited a = true := by decide
example : finalState.visited b = true := by decide
example : finalState.visited c = true := by decide
example : resultAdjList.ret.2.visited c = resultAdjMatrix.ret.2.visited c := by decide
example : KleinbergDFS.exactCost resultAdjList = 23 := by decide
example : KleinbergDFS.exactCost resultAdjMatrix = 35 := by decide
example : adjListSpace.graphStorage = 8 := by decide
example : adjMatrixSpace.graphStorage = 16 := by decide
example : adjListSpace.traversalWorkingStorage = 9 := by decide
example : adjMatrixSpace.traversalWorkingStorage = 9 := by decide

end KleinbergDFSTest
