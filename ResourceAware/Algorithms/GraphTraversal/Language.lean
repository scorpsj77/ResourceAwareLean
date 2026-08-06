/-
Copyright (c) 2026 Jiyuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan
-/
import ResourceAware.Program.Model

/-!
# Shared language for graph traversal algorithms

This module contains the primitive requests shared by graph traversals.  A BFS or DFS program
chooses its control structure—layers, a queue, or recursion—but uses the same requests for
textbook loop checks, graph access, discovery state, level output, and tree output.

Execution choices are supplied separately by `GraphTraversal.Model` through
`ResourceAware.Program.Semantics` and `ResourceAware.Program.CostModel`.
-/

universe u

namespace ResourceAware.Algorithms.GraphTraversal

/-- Representation-independent operations used by graph traversal programs. -/
inductive Op (Vertex : Type u) : Type u where
  | checkLayerEmpty (level : Nat)
  | checkStackEmpty
  | clearVisited
  | clearLevels
  | clearTree
  | neighbors (u : Vertex)
  | isVisited (v : Vertex)
  | markVisited (v : Vertex)
  | recordLevel (v : Vertex) (level : Nat)
  | addTreeEdge (u v : Vertex)
deriving Repr, DecidableEq

/-- The response supplied by an interpreter for each traversal operation. -/
abbrev Response {Vertex : Type u} : Op Vertex → Type u
  | .checkLayerEmpty _ => PUnit
  | .checkStackEmpty => PUnit
  | .clearVisited => PUnit
  | .clearLevels => PUnit
  | .clearTree => PUnit
  | .neighbors _ => List Vertex
  | .isVisited _ => ULift Bool
  | .markVisited _ => PUnit
  | .recordLevel _ _ => PUnit
  | .addTreeEdge _ _ => PUnit

/-- Polynomial signature for shared graph-traversal effects. -/
def Signature (Vertex : Type u) : ResourceAware.Program.Signature.{u, u} where
  A := Op Vertex
  B := fun op ↦ Response op

/-- Syntax trees for representation-independent graph traversals. -/
abbrev Program (Vertex : Type u) (α : Type u) : Type u :=
  ResourceAware.Program.Free (Signature Vertex) α

variable {Vertex : Type u}

/-- Lift one traversal request into the free monad. -/
def request (op : Op Vertex) : Program Vertex (Response op) :=
  ResourceAware.Program.request (signature := Signature Vertex) op

def checkLayerEmpty (level : Nat) : Program Vertex PUnit := request (.checkLayerEmpty level)

def checkStackEmpty : Program Vertex PUnit := request .checkStackEmpty

def clearVisited : Program Vertex PUnit := request .clearVisited

def clearLevels : Program Vertex PUnit := request .clearLevels

def clearTree : Program Vertex PUnit := request .clearTree

def neighbors (u : Vertex) : Program Vertex (List Vertex) := request (.neighbors u)

def isVisited (v : Vertex) : Program Vertex (ULift Bool) := request (.isVisited v)

def markVisited (v : Vertex) : Program Vertex PUnit := request (.markVisited v)

def recordLevel (v : Vertex) (level : Nat) : Program Vertex PUnit :=
  request (.recordLevel v level)

def addTreeEdge (u v : Vertex) : Program Vertex PUnit := request (.addTreeEdge u v)
end ResourceAware.Algorithms.GraphTraversal
