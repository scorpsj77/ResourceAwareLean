/-
Copyright (c) 2026 Jiyuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan
-/
import TextbookAlgorithms.KleinbergTardos.Chapter03.DFS.Algorithm
import ResourceAware.Algorithms.GraphTraversal.Model
import ResourceAware.Foundations.Graph.ResourceModel

/-!
# Resource model for Kleinberg depth-first search

This module selects semantics and resource models for the abstract DFS program. The free-monad
fold is supplied by the generic resource-aware interpreter; this file contains only the thin
algorithm runner and the DFS-specific fuel and space models.
-/

universe u v

namespace KleinbergDFS

open ResourceAware ResourceAware.Algorithms
open ResourceAware.Graph

/-- Ordered measured events produced by the shared traversal model. -/
abbrev Event (Vertex : Type v) := GraphTraversal.Event Vertex

/-- Product state used by DFS; level and tree components are discarded. -/
abbrev State (VisitedState : Type v) :=
  GraphTraversal.Model.State VisitedState PUnit PUnit

/-- A finite upper bound on stack pops for the textbook DFS variant. -/
def stackPopBound {G : Type u} (model : ResourceModel G Vertex) (graph : G) : Nat :=
  model.adjacencyEntryCount graph + 1

namespace Interpreter

variable {Vertex VisitedState : Type v}

/-- Run Kleinberg DFS with explicit stack-pop fuel. -/
def runWithBound {G : Type u} (model : ResourceModel G Vertex) (graph : G)
    (control : GraphTraversal.ControlCostModel)
    (visited : GraphTraversal.VisitedModel Vertex VisitedState)
    (stackPopBound : Nat) (source : Vertex) :
    TraceM (Event Vertex) (PUnit × State VisitedState) :=
  GraphTraversal.Model.interpret (dfs stackPopBound source)
    model graph control visited GraphTraversal.LevelModel.discard GraphTraversal.TreeModel.discard

/-- Use `1 + m` from the graph model as termination fuel. -/
def run {G : Type u} (model : ResourceModel G Vertex) (graph : G)
    (control : GraphTraversal.ControlCostModel)
    (visited : GraphTraversal.VisitedModel Vertex VisitedState) (source : Vertex) :
    TraceM (Event Vertex) (PUnit × State VisitedState) :=
  runWithBound model graph control visited (KleinbergDFS.stackPopBound model graph) source

end Interpreter

/-- Sum the measured primitive work in a completed DFS trace. -/
def exactCost (computation : TraceM (Event Vertex) α) : Nat :=
  ResourceAware.Program.exactCost computation

/-- Static graph storage and a stack-capacity bound for DFS working storage. -/
structure SpaceUsage where
  graphStorage : Nat
  traversalWorkingStorage : Nat

namespace SpaceUsage

def total (space : SpaceUsage) : Nat :=
  space.graphStorage + space.traversalWorkingStorage

end SpaceUsage

/-- Add explored-state storage to the conservative `1 + m` stack-storage bound. -/
def spaceUsage {G : Type u} (model : ResourceModel G Vertex) (graph : G)
    (visited : GraphTraversal.VisitedModel Vertex VisitedState) : SpaceUsage :=
  let n := model.vertexCount graph
  { graphStorage := model.graphSpace graph
    traversalWorkingStorage := visited.space.space n + stackPopBound model graph }

end KleinbergDFS
