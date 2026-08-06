/-
Copyright (c) 2026 Jiyuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan
-/
import ResourceAware.Algorithms.GraphTraversal.Language
import ResourceAware.Foundations.Graph.ResourceModel
import ResourceAware.Program.Cost
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic.Linarith

/-!
# Generic graph-traversal model

This module contains the reusable state backends, resource choices, state transitions, and
measurements supplied to the generic `ResourceAware.Program` interpreter. BFS, DFS, and future
traversal algorithms share the language and select values from this model.
-/

universe u v

namespace ResourceAware.Algorithms.GraphTraversal

/-- One traversal operation annotated by its measured primitive work. -/
abbrev Event (Vertex : Type v) := ResourceAware.Program.Event (Op Vertex) Nat

/-- Implementation of discovery state, independent of its resource model. -/
structure VisitedBackend (Vertex : Type u) (VisitedState : Type v) where
  empty : VisitedState
  isVisited : VisitedState → Vertex → Bool
  markVisited : VisitedState → Vertex → VisitedState

/-- Implementation of optional vertex-level output, independent of its resource model. -/
structure LevelBackend (Vertex : Type u) (LevelState : Type v) where
  empty : LevelState
  recordLevel : LevelState → Vertex → Nat → LevelState

/-- Implementation of optional traversal-tree output, independent of its resource model. -/
structure TreeBackend (Vertex : Type u) (TreeState : Type v) where
  empty : TreeState
  addTreeEdge : TreeState → Vertex → Vertex → TreeState

variable {Vertex : Type u}

/-- Functional update of one vertex-indexed table entry. -/
def update [DecidableEq Vertex] {Value : Type v}
    (table : Vertex → Value) (vertex : Vertex) (value : Value) : Vertex → Value :=
  fun candidate ↦ if candidate = vertex then value else table candidate

namespace VisitedBackend

/-- Boolean-table discovery state. -/
def booleanTable [DecidableEq Vertex] : VisitedBackend Vertex (Vertex → Bool) where
  empty := fun _ ↦ false
  isVisited := fun table vertex ↦ table vertex
  markVisited := fun table vertex ↦ update table vertex true

end VisitedBackend

namespace LevelBackend

/-- Store every discovered level in a vertex-indexed table. -/
def table [DecidableEq Vertex] : LevelBackend Vertex (Vertex → Option Nat) where
  empty := fun _ ↦ none
  recordLevel := fun levels vertex level ↦ update levels vertex (some level)

/-- Discard level output when a traversal needs only visited or tree information. -/
def discard : LevelBackend Vertex PUnit where
  empty := .unit
  recordLevel := fun state _ _ ↦ state

end LevelBackend

namespace TreeBackend

/-- Store traversal-tree edges in discovery order, newest first. -/
def edgeList : TreeBackend Vertex (List (Vertex × Vertex)) where
  empty := []
  addTreeEdge := fun edges parent child ↦ (parent, child) :: edges

/-- Discard tree output for traversals that need only visited information. -/
def discard : TreeBackend Vertex PUnit where
  empty := .unit
  addTreeEdge := fun state _ _ ↦ state

end TreeBackend

/-- Time model for traversal control checks. -/
structure ControlCostModel where
  checkLayerEmptyCost : Nat → Nat
  checkStackEmptyCost : Nat

/-- Time model for discovery-state operations. -/
structure VisitedCostModel (Vertex : Type u) (VisitedState : Type v) where
  clearCost : Nat → Nat
  isVisitedCost : VisitedState → Vertex → Nat
  markVisitedCost : VisitedState → Vertex → Nat

/-- Time model for level-output operations. -/
structure LevelCostModel (Vertex : Type u) (LevelState : Type v) where
  clearCost : Nat → Nat
  recordLevelCost : LevelState → Vertex → Nat → Nat

/-- Time model for traversal-tree operations. -/
structure TreeCostModel (Vertex : Type u) (TreeState : Type v) where
  clearCost : Nat → Nat
  addTreeEdgeCost : TreeState → Vertex → Vertex → Nat

/-- Static working-storage model for a selected state representation. -/
structure SpaceModel where
  space : Nat → Nat

/-- A visited implementation with independently selected time and space models. -/
structure VisitedModel (Vertex : Type u) (VisitedState : Type v) where
  backend : VisitedBackend Vertex VisitedState
  cost : VisitedCostModel Vertex VisitedState
  space : SpaceModel

/-- A level implementation with independently selected time and space models. -/
structure LevelModel (Vertex : Type u) (LevelState : Type v) where
  backend : LevelBackend Vertex LevelState
  cost : LevelCostModel Vertex LevelState
  space : SpaceModel

/-- A tree implementation with independently selected time and space models. -/
structure TreeModel (Vertex : Type u) (TreeState : Type v) where
  backend : TreeBackend Vertex TreeState
  cost : TreeCostModel Vertex TreeState
  space : SpaceModel

namespace SpaceModel

/-- One state cell per graph vertex. -/
def linear : SpaceModel where
  space := id

/-- No retained state. -/
def discard : SpaceModel where
  space := fun _ ↦ 0

end SpaceModel

namespace ControlCostModel

/-- Unit-cost traversal control checks. -/
def unit : ControlCostModel where
  checkLayerEmptyCost := fun _ ↦ 1
  checkStackEmptyCost := 1

end ControlCostModel

namespace VisitedCostModel

/-- Unit-cost random access with eager initialization of all `n` table entries. -/
def booleanTable : VisitedCostModel Vertex (Vertex → Bool) where
  clearCost := id
  isVisitedCost := fun _ _ ↦ 1
  markVisitedCost := fun _ _ ↦ 1

end VisitedCostModel

namespace LevelCostModel

/-- Unit-cost writes with eager initialization of an `n`-entry level table. -/
def table : LevelCostModel Vertex (Vertex → Option Nat) where
  clearCost := id
  recordLevelCost := fun _ _ _ ↦ 1

/-- Zero cost for discarded level output. -/
def discard : LevelCostModel Vertex PUnit where
  clearCost := fun _ ↦ 0
  recordLevelCost := fun _ _ _ ↦ 0

end LevelCostModel

namespace TreeCostModel

/-- Constant-time clearing and insertion at the head of an edge list. -/
def edgeList : TreeCostModel Vertex (List (Vertex × Vertex)) where
  clearCost := fun _ ↦ 1
  addTreeEdgeCost := fun _ _ _ ↦ 1

/-- Zero cost for discarded tree output. -/
def discard : TreeCostModel Vertex PUnit where
  clearCost := fun _ ↦ 0
  addTreeEdgeCost := fun _ _ _ ↦ 0

end TreeCostModel

namespace VisitedModel

/-- Standard Boolean-table implementation and RAM resource model. -/
def booleanTable [DecidableEq Vertex] : VisitedModel Vertex (Vertex → Bool) where
  backend := VisitedBackend.booleanTable
  cost := VisitedCostModel.booleanTable
  space := SpaceModel.linear

end VisitedModel

namespace LevelModel

/-- Standard vertex-indexed level table. -/
def table [DecidableEq Vertex] : LevelModel Vertex (Vertex → Option Nat) where
  backend := LevelBackend.table
  cost := LevelCostModel.table
  space := SpaceModel.linear

/-- Discard all level output and charge no resources for it. -/
def discard : LevelModel Vertex PUnit where
  backend := LevelBackend.discard
  cost := LevelCostModel.discard
  space := SpaceModel.discard

end LevelModel

namespace TreeModel

/-- Standard edge-list traversal tree. -/
def edgeList : TreeModel Vertex (List (Vertex × Vertex)) where
  backend := TreeBackend.edgeList
  cost := TreeCostModel.edgeList
  space := SpaceModel.linear

/-- Discard all tree output and charge no resources for it. -/
def discard : TreeModel Vertex PUnit where
  backend := TreeBackend.discard
  cost := TreeCostModel.discard
  space := SpaceModel.discard

end TreeModel

namespace TimeComplexity

open Filter Asymptotics

/-- `O(n)` initialization plus the two adjacency-list entries of every undirected edge. -/
def adjacencyList (n m : Nat) : Nat :=
  n + 2 * m

/-- `O(n)` initialization plus at most `n` scans of matrix rows of length `n`. -/
def adjacencyMatrix (n : Nat) : Nat :=
  n + n * n

/-- The adjacency-list traversal accounting is `O(m + n)`. -/
theorem adjacencyList_isBigO :
    (fun nm : Nat × Nat ↦ (adjacencyList nm.1 nm.2 : Real)) =O[atTop]
      fun nm ↦ (nm.2 : Real) + nm.1 := by
  refine IsBigO.of_bound 2 (Eventually.of_forall fun nm ↦ ?_)
  simp only [adjacencyList, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Real.norm_eq_abs]
  rw [abs_of_nonneg, abs_of_nonneg]
  · have hn : (0 : Real) ≤ nm.1 := by positivity
    linarith
  · positivity
  · positivity

/-- The adjacency-matrix traversal accounting is `O(n²)`. -/
theorem adjacencyMatrix_isBigO :
    (fun n : Nat ↦ (adjacencyMatrix n : Real)) =O[atTop]
      fun n ↦ (n : Real) ^ 2 := by
  refine IsBigO.of_bound 2 (Filter.eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩)
  simp only [adjacencyMatrix, Nat.cast_add, Nat.cast_mul, Real.norm_eq_abs]
  rw [abs_of_nonneg, abs_of_nonneg]
  · have hn' : (1 : Real) ≤ n := by exact_mod_cast hn
    nlinarith
  · positivity
  · positivity

end TimeComplexity
end ResourceAware.Algorithms.GraphTraversal

namespace ResourceAware.Algorithms.GraphTraversal.Model

open Cslib.Algorithms.Lean
open ResourceAware
open ResourceAware.Graph
open ResourceAware.Algorithms.GraphTraversal

structure State (VisitedState LevelState TreeState : Type v) where
  visited : VisitedState
  levels : LevelState
  tree : TreeState

variable {Vertex VisitedState LevelState TreeState : Type v}

structure IsBoundedBy {G : Type u} (graphModel : ResourceModel G Vertex) (graph : G)
    (control : ControlCostModel) (visited : VisitedModel Vertex VisitedState)
    (levels : LevelModel Vertex LevelState) (tree : TreeModel Vertex TreeState)
    (charge : Op Vertex → Nat) : Prop where
  checkLayerEmpty : ∀ level,
    control.checkLayerEmptyCost level ≤ charge (.checkLayerEmpty level)
  checkStackEmpty : control.checkStackEmptyCost ≤ charge .checkStackEmpty
  clearVisited : visited.cost.clearCost (graphModel.vertexCount graph) ≤ charge .clearVisited
  clearLevels : levels.cost.clearCost (graphModel.vertexCount graph) ≤ charge .clearLevels
  clearTree : tree.cost.clearCost (graphModel.vertexCount graph) ≤ charge .clearTree
  neighbors : ∀ vertex, graphModel.neighborCost graph vertex ≤ charge (.neighbors vertex)
  isVisited : ∀ state vertex,
    visited.cost.isVisitedCost state vertex ≤ charge (.isVisited vertex)
  markVisited : ∀ state vertex,
    visited.cost.markVisitedCost state vertex ≤ charge (.markVisited vertex)
  recordLevel : ∀ state vertex level,
    levels.cost.recordLevelCost state vertex level ≤ charge (.recordLevel vertex level)
  addTreeEdge : ∀ state parent child,
    tree.cost.addTreeEdgeCost state parent child ≤ charge (.addTreeEdge parent child)

def initialState (visited : VisitedModel Vertex VisitedState)
    (levels : LevelModel Vertex LevelState) (tree : TreeModel Vertex TreeState) :
    State VisitedState LevelState TreeState where
  visited := visited.backend.empty
  levels := levels.backend.empty
  tree := tree.backend.empty

def semantics {G : Type u} (graphModel : ResourceModel G Vertex) (graph : G)
    (visited : VisitedBackend Vertex VisitedState) (levels : LevelBackend Vertex LevelState)
    (tree : TreeBackend Vertex TreeState) :
    ResourceAware.Program.Semantics (Signature Vertex)
      (State VisitedState LevelState TreeState) where
  initialState :=
    { visited := visited.empty
      levels := levels.empty
      tree := tree.empty }
  step operation state :=
    match operation with
    | .checkLayerEmpty _ => (.unit, state)
    | .checkStackEmpty => (.unit, state)
    | .clearVisited => (.unit, { state with visited := visited.empty })
    | .clearLevels => (.unit, { state with levels := levels.empty })
    | .clearTree => (.unit, { state with tree := tree.empty })
    | .neighbors vertex => (graphModel.neighborAccess.outNeighbors graph vertex, state)
    | .isVisited vertex => (ULift.up (visited.isVisited state.visited vertex), state)
    | .markVisited vertex =>
        (.unit, { state with visited := visited.markVisited state.visited vertex })
    | .recordLevel vertex level =>
        (.unit, { state with levels := levels.recordLevel state.levels vertex level })
    | .addTreeEdge parent child =>
        (.unit, { state with tree := tree.addTreeEdge state.tree parent child })

def costModel {G : Type u} (graphModel : ResourceModel G Vertex) (graph : G)
    (control : ControlCostModel) (visited : VisitedModel Vertex VisitedState)
    (levels : LevelModel Vertex LevelState) (tree : TreeModel Vertex TreeState) :
    ResourceAware.Program.CostModel (Signature Vertex)
      (State VisitedState LevelState TreeState) Nat where
  measure operation state _ _ :=
    match operation with
    | .checkLayerEmpty level => control.checkLayerEmptyCost level
    | .checkStackEmpty => control.checkStackEmptyCost
    | .clearVisited => visited.cost.clearCost (graphModel.vertexCount graph)
    | .clearLevels => levels.cost.clearCost (graphModel.vertexCount graph)
    | .clearTree => tree.cost.clearCost (graphModel.vertexCount graph)
    | .neighbors vertex => graphModel.neighborCost graph vertex
    | .isVisited vertex => visited.cost.isVisitedCost state.visited vertex
    | .markVisited vertex => visited.cost.markVisitedCost state.visited vertex
    | .recordLevel vertex level =>
        levels.cost.recordLevelCost state.levels vertex level
    | .addTreeEdge parent child =>
        tree.cost.addTreeEdgeCost state.tree parent child

private def interpretOperationsFrom {G : Type u} (program : Program Vertex α)
    (graphModel : ResourceModel G Vertex) (graph : G)
    (visited : VisitedBackend Vertex VisitedState) (levels : LevelBackend Vertex LevelState)
    (tree : TreeBackend Vertex TreeState) (state : State VisitedState LevelState TreeState) :
    TraceM (Op Vertex) (α × State VisitedState LevelState TreeState) :=
  ResourceAware.Program.runOperationsFrom
    (semantics graphModel graph visited levels tree) program state

def interpretFrom {G : Type u} (program : Program Vertex α)
    (graphModel : ResourceModel G Vertex) (graph : G)
    (control : ControlCostModel) (visited : VisitedModel Vertex VisitedState)
    (levels : LevelModel Vertex LevelState) (tree : TreeModel Vertex TreeState)
    (state : State VisitedState LevelState TreeState) :
    TraceM (Event Vertex) (α × State VisitedState LevelState TreeState) :=
  ResourceAware.Program.runFrom
    (semantics graphModel graph visited.backend levels.backend tree.backend)
    (costModel graphModel graph control visited levels tree) program state

theorem interpretFrom_bind {G : Type u} (program : Program Vertex α)
    (next : α → Program Vertex β) (graphModel : ResourceModel G Vertex) (graph : G)
    (control : ControlCostModel) (visited : VisitedModel Vertex VisitedState)
    (levels : LevelModel Vertex LevelState) (tree : TreeModel Vertex TreeState)
    (state : State VisitedState LevelState TreeState) :
    interpretFrom (program >>= next) graphModel graph control visited levels tree state = (do
      let (result, state') ←
        interpretFrom program graphModel graph control visited levels tree state
      interpretFrom (next result) graphModel graph control visited levels tree state') :=
  ResourceAware.Program.runFrom_bind _ _ program next state

private theorem mapEvents_interpretFrom {G : Type u} (program : Program Vertex α)
    (graphModel : ResourceModel G Vertex) (graph : G)
    (control : ControlCostModel) (visited : VisitedModel Vertex VisitedState)
    (levels : LevelModel Vertex LevelState) (tree : TreeModel Vertex TreeState)
    (state : State VisitedState LevelState TreeState) :
    TraceM.mapEvents ResourceAware.Program.Event.erase
      (interpretFrom program graphModel graph control visited levels tree state) =
    interpretOperationsFrom program graphModel graph visited.backend levels.backend tree.backend
      state :=
  ResourceAware.Program.mapEvents_runFrom _ _ program state

private theorem mapEvents_interpretFrom_eq_of_backend_eq {G : Type u}
    (program : Program Vertex α)
    (graphModel : ResourceModel G Vertex) (graph : G)
    (control₁ control₂ : ControlCostModel)
    (visited₁ visited₂ : VisitedModel Vertex VisitedState)
    (levels₁ levels₂ : LevelModel Vertex LevelState)
    (tree₁ tree₂ : TreeModel Vertex TreeState)
    (hVisited : visited₁.backend = visited₂.backend)
    (hLevels : levels₁.backend = levels₂.backend)
    (hTree : tree₁.backend = tree₂.backend)
    (state : State VisitedState LevelState TreeState) :
    TraceM.mapEvents ResourceAware.Program.Event.erase
      (interpretFrom program graphModel graph control₁ visited₁ levels₁ tree₁ state) =
    TraceM.mapEvents ResourceAware.Program.Event.erase
      (interpretFrom program graphModel graph control₂ visited₂ levels₂ tree₂ state) := by
  rw [mapEvents_interpretFrom, mapEvents_interpretFrom, hVisited, hLevels, hTree]

theorem operationTrace_interpretFrom_eq_of_backend_eq {G : Type u}
    (program : Program Vertex α) (graphModel : ResourceModel G Vertex) (graph : G)
    (control₁ control₂ : ControlCostModel)
    (visited₁ visited₂ : VisitedModel Vertex VisitedState)
    (levels₁ levels₂ : LevelModel Vertex LevelState)
    (tree₁ tree₂ : TreeModel Vertex TreeState)
    (hVisited : visited₁.backend = visited₂.backend)
    (hLevels : levels₁.backend = levels₂.backend)
    (hTree : tree₁.backend = tree₂.backend)
    (state : State VisitedState LevelState TreeState) :
    ResourceAware.Program.operationTrace
        (interpretFrom program graphModel graph control₁ visited₁ levels₁ tree₁ state) =
      ResourceAware.Program.operationTrace
        (interpretFrom program graphModel graph control₂ visited₂ levels₂ tree₂ state) := by
  have h := mapEvents_interpretFrom_eq_of_backend_eq program graphModel graph
    control₁ control₂ visited₁ visited₂ levels₁ levels₂ tree₁ tree₂
    hVisited hLevels hTree state
  simpa [ResourceAware.Program.operationTrace, TraceM.projectedEvents] using
    congrArg TraceM.events h

theorem ret_interpretFrom_eq_of_backend_eq {G : Type u} (program : Program Vertex α)
    (graphModel : ResourceModel G Vertex) (graph : G)
    (control₁ control₂ : ControlCostModel)
    (visited₁ visited₂ : VisitedModel Vertex VisitedState)
    (levels₁ levels₂ : LevelModel Vertex LevelState)
    (tree₁ tree₂ : TreeModel Vertex TreeState)
    (hVisited : visited₁.backend = visited₂.backend)
    (hLevels : levels₁.backend = levels₂.backend)
    (hTree : tree₁.backend = tree₂.backend)
    (state : State VisitedState LevelState TreeState) :
    (interpretFrom program graphModel graph control₁ visited₁ levels₁ tree₁ state).ret =
      (interpretFrom program graphModel graph control₂ visited₂ levels₂ tree₂ state).ret := by
  have h := mapEvents_interpretFrom_eq_of_backend_eq program graphModel graph
    control₁ control₂ visited₁ visited₂ levels₁ levels₂ tree₁ tree₂
    hVisited hLevels hTree state
  simpa using congrArg (fun computation ↦ computation.ret) h

def interpret {G : Type u} (program : Program Vertex α)
    (graphModel : ResourceModel G Vertex) (graph : G)
    (control : ControlCostModel) (visited : VisitedModel Vertex VisitedState)
    (levels : LevelModel Vertex LevelState) (tree : TreeModel Vertex TreeState) :
    TraceM (Event Vertex) (α × State VisitedState LevelState TreeState) :=
  interpretFrom program graphModel graph control visited levels tree
    (initialState visited levels tree)

theorem exactCost_interpretFrom_le_weightedOperationCost {G : Type u}
    (program : Program Vertex α) (graphModel : ResourceModel G Vertex) (graph : G)
    (control : ControlCostModel) (visited : VisitedModel Vertex VisitedState)
    (levels : LevelModel Vertex LevelState) (tree : TreeModel Vertex TreeState)
    (charge : Op Vertex → Nat)
    (hbounded : IsBoundedBy graphModel graph control visited levels tree charge)
    (state : State VisitedState LevelState TreeState) :
    ResourceAware.Program.exactCost
        (interpretFrom program graphModel graph control visited levels tree state) ≤
      ResourceAware.Program.weightedOperationCost charge
        (interpretFrom program graphModel graph control visited levels tree state) := by
  apply ResourceAware.Program.exactCost_runFrom_le_weightedOperationCost
  intro operation current
  cases operation with
  | checkLayerEmpty level => exact hbounded.checkLayerEmpty level
  | checkStackEmpty => exact hbounded.checkStackEmpty
  | clearVisited => exact hbounded.clearVisited
  | clearLevels => exact hbounded.clearLevels
  | clearTree => exact hbounded.clearTree
  | neighbors vertex => exact hbounded.neighbors vertex
  | isVisited vertex => exact hbounded.isVisited current.visited vertex
  | markVisited vertex => exact hbounded.markVisited current.visited vertex
  | recordLevel vertex level => exact hbounded.recordLevel current.levels vertex level
  | addTreeEdge parent child => exact hbounded.addTreeEdge current.tree parent child

def backendSpace (vertexCount : Nat) (visited : VisitedModel Vertex VisitedState)
    (levels : LevelModel Vertex LevelState) (tree : TreeModel Vertex TreeState) : Nat :=
  visited.space.space vertexCount + levels.space.space vertexCount +
    tree.space.space vertexCount

end ResourceAware.Algorithms.GraphTraversal.Model
