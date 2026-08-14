/-
Copyright (c) 2026 Jiyuan (Chai Yuen) Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan (Chai Yuen) Ji
-/
import ResourceAware.Algorithms.GraphTraversal.Language

/-!
# Kleinberg's stack-based depth-first search

This file formalizes the iterative DFS presentation from Kleinberg and Tardos.  The stack is
kept as ordinary algorithm control state, while graph access and explored-state operations use
the shared graph-traversal signature.
-/

universe u

namespace KleinbergDFS

open ResourceAware ResourceAware.Algorithms

/-- Kleinberg DFS programs use the shared graph-traversal free monad. -/
abbrev Program (Vertex : Type u) (α : Type u) : Type u :=
  ResourceAware.Algorithms.GraphTraversal.Program Vertex α

variable {Vertex : Type u}

/-! ## Stack-based algorithm -/

/--
Push every neighbor onto the stack.

The head of the list is the stack top.  Processing neighbors left-to-right with cons-style
pushes means the last neighbor in the list is popped first.
-/
def pushNeighbors : List Vertex → List Vertex → List Vertex
  | [], stack => stack
  | v :: rest, stack => pushNeighbors rest (v :: stack)

/--
Repeatedly pop a vertex from the stack.  If it has not been explored, mark it explored and
push all of its neighbors.  Fuel is a stack-pop bound supplied by a finite graph model.
-/
def dfsLoop : Nat → List Vertex → Program Vertex PUnit
  /- fuel is exhausted and current layer is empty. check counted. -/
  | 0, [] => do
      GraphTraversal.checkStackEmpty
      pure .unit
  /- fuel is exhausted but current layer is nonempty. check not counted.
  this is an error. -/
  | 0, _ => pure .unit
  /- fuel remains and current layer is empty. -/
  | _ + 1, [] => do
      GraphTraversal.checkStackEmpty
      pure .unit
  /- fuel remains and current layer is nonempty. -/
  | fuel + 1, u :: stack => do
      GraphTraversal.checkStackEmpty
      let seen ← GraphTraversal.isVisited u
      if seen.down then
        dfsLoop fuel stack
      else
        GraphTraversal.markVisited u
        let ns ← GraphTraversal.neighbors u
        dfsLoop fuel (pushNeighbors ns stack)

/--
Run Kleinberg's DFS from `source`.

`stackPopBound` is termination fuel.  For a finite graph, `1 + m` is enough for this textbook
variant because each explored vertex pushes its outgoing adjacency list once.
-/
def dfs (stackPopBound : Nat) (source : Vertex) : Program Vertex PUnit := do
  GraphTraversal.clearVisited (Vertex := Vertex)
  dfsLoop stackPopBound [source]

end KleinbergDFS
