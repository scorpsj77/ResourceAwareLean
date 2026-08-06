/-
Copyright (c) 2026 Jiyuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan
-/
import TextbookAlgorithms.KleinbergTardos.Chapter03.BFS.Algorithm
import ResourceAware.Algorithms.GraphTraversal.Model
import ResourceAware.Foundations.Graph.ResourceModel

/-!
# Resource model for Kleinberg breadth-first search

This module selects semantics and resource models for the abstract BFS program. The free-monad
fold is supplied by the generic resource-aware interpreter; this file contains only the thin
algorithm runner and the BFS-specific space model. Time bounds remain in `Complexity.lean`.
-/

universe u v

namespace KleinbergBFS

open ResourceAware ResourceAware.Algorithms
open ResourceAware.Graph

/-- Ordered measured events produced by the shared traversal model. -/
abbrev Event (Vertex : Type v) := GraphTraversal.Event Vertex

/-- Product state assembled from the selected shared traversal backends. -/
abbrev State (VisitedState LevelState TreeState : Type v) :=
  GraphTraversal.Model.State VisitedState LevelState TreeState

namespace Interpreter

variable {Vertex VisitedState LevelState TreeState : Type v}

/-- Run Kleinberg BFS with explicit fuel and independently selected components. -/
def runWithBound {G : Type u} (model : ResourceModel G Vertex) (graph : G)
    (control : GraphTraversal.ControlCostModel)
    (visited : GraphTraversal.VisitedModel Vertex VisitedState)
    (levels : GraphTraversal.LevelModel Vertex LevelState)
    (tree : GraphTraversal.TreeModel Vertex TreeState)
    (vertexBound : Nat) (source : Vertex) :
    TraceM (Event Vertex) (PUnit × State VisitedState LevelState TreeState) :=
  GraphTraversal.Model.interpret (bfs vertexBound source)
    model graph control visited levels tree

/-- Use the graph model's verified vertex count as termination fuel. -/
def run {G : Type u} (model : ResourceModel G Vertex) (graph : G)
    (control : GraphTraversal.ControlCostModel)
    (visited : GraphTraversal.VisitedModel Vertex VisitedState)
    (levels : GraphTraversal.LevelModel Vertex LevelState)
    (tree : GraphTraversal.TreeModel Vertex TreeState) (source : Vertex) :
    TraceM (Event Vertex) (PUnit × State VisitedState LevelState TreeState) :=
  runWithBound model graph control visited levels tree (model.vertexCount graph) source

end Interpreter

/-- Sum the measured primitive work in a completed BFS trace. -/
def exactCost (computation : TraceM (Event Vertex) α) : Nat :=
  ResourceAware.Program.exactCost computation

/-- Static graph storage and Kleinberg BFS working storage. -/
structure SpaceUsage where
  graphStorage : Nat
  traversalWorkingStorage : Nat

namespace SpaceUsage

def total (space : SpaceUsage) : Nat :=
  space.graphStorage + space.traversalWorkingStorage

end SpaceUsage

/-- Add active-layer storage to the selected visited, level, and tree backend storage. -/
def spaceUsage {G : Type u} (model : ResourceModel G Vertex) (graph : G)
    (visited : GraphTraversal.VisitedModel Vertex VisitedState)
    (levels : GraphTraversal.LevelModel Vertex LevelState)
    (tree : GraphTraversal.TreeModel Vertex TreeState) : SpaceUsage :=
  let n := model.vertexCount graph
  { graphStorage := model.graphSpace graph
    traversalWorkingStorage :=
      GraphTraversal.Model.backendSpace n visited levels tree + n }

end KleinbergBFS
