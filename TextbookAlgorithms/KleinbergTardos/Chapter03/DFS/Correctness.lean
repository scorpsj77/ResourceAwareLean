/-
Copyright (c) 2026 Jiyuan (Chai Yuen) Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan (Chai Yuen) Ji
-/
import TextbookAlgorithms.KleinbergTardos.Chapter03.DFS.Complexity
import ResourceAware.Algorithms.GraphTraversal.Specification
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Structural correctness lemmas for Kleinberg depth-first search

These lemmas certify the concrete stack helper, the final visited set, and the structural
ancestor property of depth-first trees.
-/

namespace KleinbergDFS

open ResourceAware ResourceAware.Algorithms
open ResourceAware.Graph

/-- Pushing neighbors left-to-right places their reverse in front of the old stack. -/
theorem pushNeighbors_eq_reverse_append (neighbors stack : List Vertex) :
    pushNeighbors neighbors stack = neighbors.reverse ++ stack := by
  induction neighbors generalizing stack with
  | nil => rfl
  | cons vertex rest ih =>
      simp [pushNeighbors, ih, List.reverse_cons, List.append_assoc]

/-- Pushing neighbors increases stack length by exactly the number of neighbors. -/
theorem length_pushNeighbors (neighbors stack : List Vertex) :
    (pushNeighbors neighbors stack).length = neighbors.length + stack.length := by
  rw [pushNeighbors_eq_reverse_append, List.length_append, List.length_reverse]

universe u v

/-- The public Boolean-table runner has the pure visited-state recurrence used below. -/
theorem run_visited_eq_loopResult {G : Type u} {V : Type v} [DecidableEq V]
    (model : ResourceModel G V) (graph : G) (source : V) :
    (Interpreter.run model graph GraphTraversal.ControlCostModel.unit
      GraphTraversal.VisitedModel.booleanTable source).ret.2.visited =
      (Operational.loopResult model graph (stackPopBound model graph) [source]
        (fun _ ↦ false)).visited := by
  let initial : Operational.State V := GraphTraversal.Model.initialState
    GraphTraversal.VisitedModel.booleanTable GraphTraversal.LevelModel.discard
      GraphTraversal.TreeModel.discard
  change (Operational.execute model graph (dfs (stackPopBound model graph) source)
    initial).ret.2.visited = _
  rw [show dfs (stackPopBound model graph) source = (do
    GraphTraversal.clearVisited
    dfsLoop (stackPopBound model graph) [source]) by rfl]
  simp only [Operational.execute_bind, Operational.execute_clearVisited]
  exact (Operational.dfsLoop_weightedOperationCost_le model graph 0 0 0
    (stackPopBound model graph) [source]
    { visited := fun _ ↦ false, levels := .unit, tree := .unit } (fun _ ↦ 0)).1

namespace Operational

/-- Stack remaining when DFS stops, including premature fuel exhaustion. -/
def finalStack {G : Type u} {V : Type v} [DecidableEq V]
    (model : ResourceModel G V) (graph : G) :
    Nat → List V → (V → Bool) → List V
  | 0, stack, _ => stack
  | _ + 1, [], _ => []
  | fuel + 1, vertex :: stack, visited =>
      if visited vertex then
        finalStack model graph fuel stack visited
      else
        finalStack model graph fuel
          (pushNeighbors (model.neighborAccess.outNeighbors graph vertex) stack)
          (GraphTraversal.update visited vertex true)

/-- DFS only preserves old bits and marks the vertices in its query list. -/
theorem loopResult_visited_iff_initial_or_queried {G : Type u} {V : Type v}
    [DecidableEq V] (model : ResourceModel G V) (graph : G)
    (fuel : Nat) (stack : List V) (visited : V → Bool) (vertex : V) :
    (loopResult model graph fuel stack visited).visited vertex = true ↔
      visited vertex = true ∨ vertex ∈ (loopResult model graph fuel stack visited).queried := by
  induction fuel generalizing stack visited with
  | zero => cases stack <;> simp [loopResult]
  | succ fuel ih =>
      cases stack with
      | nil => simp [loopResult]
      | cons head tail =>
          by_cases hhead : visited head
          · simpa [loopResult, hhead] using ih tail visited
          · by_cases hvertex : vertex = head
            · subst head
              simp [loopResult, hhead, ih, GraphTraversal.update]
            · simp [loopResult, hhead, ih, GraphTraversal.update, hvertex]

/-- Every initially pending vertex is eventually visited or remains on the terminal stack. -/
theorem mem_stack_visited_or_finalStack {G : Type u} {V : Type v}
    [DecidableEq V] (model : ResourceModel G V) (graph : G)
    (fuel : Nat) (stack : List V) (visited : V → Bool) {vertex : V}
    (hvertex : vertex ∈ stack) :
    (loopResult model graph fuel stack visited).visited vertex = true ∨
      vertex ∈ finalStack model graph fuel stack visited := by
  induction fuel generalizing stack visited with
  | zero => exact Or.inr (by simpa [finalStack] using hvertex)
  | succ fuel ih =>
      cases stack with
      | nil => simp at hvertex
      | cons head tail =>
          by_cases hhead : visited head
          · rcases List.mem_cons.mp hvertex with rfl | hvertex
            · left
              have hvisited :=
                (loopResult_visited_and_nodup model graph fuel tail visited).1 _ hhead
              simpa [loopResult, hhead] using hvisited
            · simpa [loopResult, finalStack, hhead] using ih tail visited hvertex
          · let visited' := GraphTraversal.update visited head true
            let next := pushNeighbors (model.neighborAccess.outNeighbors graph head) tail
            rcases List.mem_cons.mp hvertex with rfl | hvertex
            · left
              have hvisited := (loopResult_visited_and_nodup model graph fuel next visited').1
                vertex (by simp [visited', GraphTraversal.update])
              simpa [loopResult, hhead, visited', next] using hvisited
            · have hnext : vertex ∈ next := by
                rw [mem_pushNeighbors]
                exact Or.inr hvertex
              rcases ih next visited' hnext with hvisited | hfinal
              · exact Or.inl (by simpa [loopResult, hhead, visited', next] using hvisited)
              · exact Or.inr (by simpa [finalStack, hhead, visited', next] using hfinal)

/-- Every queried vertex is reachable when the initial stack and bits are reachable. -/
theorem loopResult_reachable {G : Type u} {V : Type v} [DecidableEq V]
    (model : ResourceModel G V) (graph : G) (source : V)
    (fuel : Nat) (stack : List V) (visited : V → Bool)
    (hvisited : ∀ {vertex}, visited vertex = true →
      Reachable model.interface graph source vertex)
    (hstack : ∀ {vertex}, vertex ∈ stack →
      Reachable model.interface graph source vertex) :
    ∀ {vertex}, (loopResult model graph fuel stack visited).visited vertex = true →
      Reachable model.interface graph source vertex := by
  induction fuel generalizing stack visited with
  | zero =>
      intro vertex hvertex
      exact hvisited (by cases stack <;> simpa [loopResult] using hvertex)
  | succ fuel ih =>
      cases stack with
      | nil =>
          intro vertex hvertex
          exact hvisited (by simpa [loopResult] using hvertex)
      | cons head tail =>
          intro vertex hvertex
          by_cases hhead : visited head
          · apply ih tail visited hvisited (fun {_} hvertex ↦
              hstack (List.mem_cons_of_mem head hvertex))
            simpa [loopResult, hhead] using hvertex
          · let visited' := GraphTraversal.update visited head true
            let next := pushNeighbors (model.neighborAccess.outNeighbors graph head) tail
            apply ih next visited'
            · intro vertex hvertex
              by_cases hvh : vertex = head
              · subst head
                exact hstack List.mem_cons_self
              · exact hvisited (by simpa [visited', GraphTraversal.update, hvh] using hvertex)
            · intro vertex hvertex
              rw [mem_pushNeighbors] at hvertex
              rcases hvertex with hneighbor | htail
              · exact Reachable.trans (hstack List.mem_cons_self)
                  (.step (model.neighborAccess.sound hneighbor)
                    (.refl (model.neighborAccess.target_mem hneighbor)))
              · exact hstack (List.mem_cons_of_mem head htail)
            · simpa [loopResult, hhead, visited', next] using hvertex

/-- A nonempty terminal stack accounts exactly for all fuel-consuming pops. -/
theorem fuel_add_finalStack_length {G : Type u} {V : Type v} [DecidableEq V]
    (model : ResourceModel G V) (graph : G)
    (fuel : Nat) (stack : List V) (visited : V → Bool)
    (hnonempty : finalStack model graph fuel stack visited ≠ []) :
    fuel + (finalStack model graph fuel stack visited).length =
      stack.length + ((loopResult model graph fuel stack visited).queried.map fun vertex ↦
        (model.neighborAccess.outNeighbors graph vertex).length).sum := by
  induction fuel generalizing stack visited with
  | zero => cases stack <;> simp [finalStack, loopResult]
  | succ fuel ih =>
      cases stack with
      | nil => simp [finalStack] at hnonempty
      | cons head tail =>
          by_cases hhead : visited head
          · have hrest := ih tail visited (by simpa [finalStack, hhead] using hnonempty)
            simp [finalStack, loopResult, hhead]
            omega
          · let visited' := GraphTraversal.update visited head true
            let next := pushNeighbors (model.neighborAccess.outNeighbors graph head) tail
            have hrest := ih next visited'
              (by simpa [finalStack, hhead, visited', next] using hnonempty)
            dsimp [visited', next] at hrest
            rw [length_pushNeighbors] at hrest
            simp [finalStack, loopResult, hhead]
            omega

/-- The textbook `1 + m` pop bound cannot leave a nonempty DFS stack. -/
theorem finalStack_eq_nil {G : Type u} {V : Type v} [DecidableEq V]
    (model : ResourceModel G V) (graph : G) (source : V)
    (hsource : source ∈ model.interface.vertexSet graph) :
    finalStack model graph (stackPopBound model graph) [source] (fun _ ↦ false) = [] := by
  let result := loopResult model graph (stackPopBound model graph) [source]
    (fun _ ↦ false)
  let final := finalStack model graph (stackPopBound model graph) [source]
    (fun _ ↦ false)
  by_contra hne
  have heq := fuel_add_finalStack_length model graph (stackPopBound model graph)
    [source] (fun _ ↦ false) (by simpa [final] using hne)
  have hinvariants := loopResult_visited_and_nodup model graph
    (stackPopBound model graph) [source] (fun _ ↦ false)
  have hvertices := loopResult_queried_mem_vertices model graph
    (stackPopBound model graph) [source] (fun _ ↦ false)
    (by simpa using model.vertexEnumeration.complete hsource)
  have hsum := (ResourceModel.nodup_sublist_length_and_sum_le result.queried
    (model.vertexEnumeration.vertices graph)
    (fun vertex ↦ (model.neighborAccess.outNeighbors graph vertex).length)
    hinvariants.2.2 (model.vertexEnumeration.nodup graph) hvertices).2
  have hfinalLength : 0 < final.length := List.length_pos_iff.mpr (by simpa [final] using hne)
  dsimp [result, final] at heq hsum hfinalLength
  unfold stackPopBound ResourceModel.adjacencyEntryCount at heq hsum hfinalLength
  omega

/-- Once the terminal stack is empty, all neighbors of every queried vertex are visited. -/
theorem loopResult_visits_queried_neighbors {G : Type u} {V : Type v}
    [DecidableEq V] (model : ResourceModel G V) (graph : G)
    (fuel : Nat) (stack : List V) (visited : V → Bool) {parent child : V}
    (hfinal : finalStack model graph fuel stack visited = [])
    (hparent : parent ∈ (loopResult model graph fuel stack visited).queried)
    (hchild : child ∈ model.neighborAccess.outNeighbors graph parent) :
    (loopResult model graph fuel stack visited).visited child = true := by
  induction fuel generalizing stack visited with
  | zero =>
      cases stack <;> simp [loopResult] at hparent
  | succ fuel ih =>
      cases stack with
      | nil => simp [loopResult] at hparent
      | cons head tail =>
          by_cases hhead : visited head
          · have hvisited := ih tail visited
              (by simpa [finalStack, hhead] using hfinal)
              (by simpa [loopResult, hhead] using hparent)
            simpa [loopResult, hhead] using hvisited
          · let visited' := GraphTraversal.update visited head true
            let next := pushNeighbors (model.neighborAccess.outNeighbors graph head) tail
            have hfinal' : finalStack model graph fuel next visited' = [] := by
              simpa [finalStack, hhead, visited', next] using hfinal
            have hparent' : parent = head ∨
                parent ∈ (loopResult model graph fuel next visited').queried := by
              simpa [loopResult, hhead, visited', next] using hparent
            rcases hparent' with rfl | hparent
            · have hnext : child ∈ next := by
                rw [mem_pushNeighbors]
                exact Or.inl hchild
              rcases mem_stack_visited_or_finalStack model graph fuel next visited' hnext with
                hvisited | hremaining
              · simpa [loopResult, hhead, visited', next] using hvisited
              · rw [hfinal'] at hremaining
                contradiction
            · have hvisited := ih next visited' hfinal' hparent
              simpa [loopResult, hhead, visited', next] using hvisited

/-- The Boolean-table DFS recurrence visits exactly the vertices reachable from its source. -/
theorem loopResult_visitsExactlyReachable {G : Type u} {V : Type v} [DecidableEq V]
    (model : ResourceModel G V) (graph : G) (source : V)
    (hsource : source ∈ model.interface.vertexSet graph) :
    GraphTraversal.VisitsExactlyReachable model.interface graph source fun vertex ↦
      (loopResult model graph (stackPopBound model graph) [source]
        (fun _ ↦ false)).visited vertex = true := by
  let result := loopResult model graph (stackPopBound model graph) [source]
    (fun _ ↦ false)
  have hfinal := finalStack_eq_nil model graph source hsource
  apply ResourceAware.Algorithms.GraphTraversal.visitsExactlyReachable_of_closed
  · rcases mem_stack_visited_or_finalStack model graph (stackPopBound model graph)
      [source] (fun _ ↦ false) (show source ∈ [source] by simp) with hvisited | hremaining
    · exact hvisited
    · rw [hfinal] at hremaining
      contradiction
  · intro vertex hvertex
    apply loopResult_reachable model graph source (stackPopBound model graph)
      [source] (fun _ ↦ false)
    · simp
    · intro candidate hcandidate
      have : candidate = source := by simpa using hcandidate
      subst candidate
      exact .refl hsource
    · exact hvertex
  · intro parent child hparent hedge
    have hquery : parent ∈ result.queried :=
      (loopResult_visited_iff_initial_or_queried model graph
        (stackPopBound model graph) [source] (fun _ ↦ false) parent).1 hparent |>.resolve_left
        (by simp)
    exact loopResult_visits_queried_neighbors model graph (stackPopBound model graph)
      [source] (fun _ ↦ false) hfinal hquery (model.neighborAccess.complete hedge)

end Operational

/-- Executable DFS with the standard Boolean table visits exactly the reachable vertices. -/
theorem run_visitsExactlyReachable {G : Type u} {V : Type v} [DecidableEq V]
    (model : ResourceModel G V) (graph : G) (source : V)
    (hsource : source ∈ model.interface.vertexSet graph) :
    GraphTraversal.VisitsExactlyReachable model.interface graph source fun vertex ↦
      (Interpreter.run model graph GraphTraversal.ControlCostModel.unit
        GraphTraversal.VisitedModel.booleanTable source).ret.2.visited vertex = true := by
  rw [run_visited_eq_loopResult]
  exact Operational.loopResult_visitsExactlyReachable model graph source hsource

/-! ## Recursive DFS trees -/

variable {G : Type u} {V : Type v} {Γ : Interface G V} {g : G}

/-- A vertex is an ancestor when it lies on a simple tree path from the root. -/
def IsAncestor (tree : SimpleGraph V) (root ancestor descendant : V) : Prop :=
  ∃ path : tree.Walk root descendant, path.IsPath ∧ ancestor ∈ path.support

/-- Semantic facts exposed by a completed execution of recursive depth-first search. -/
structure RecursiveTreeCertificate (h : Γ.IsUndirected g) (root : V) where
  tree : SimpleGraph V
  tree_le : tree ≤ h.toSimpleGraph
  isTree : tree.IsTree
  discovered : V → Nat
  returned : V → Nat
  discovered_injective : Function.Injective discovered
  discovered_before_returned : ∀ vertex, discovered vertex < returned vertex
  discovered_during_is_descendant : ∀ {ancestor descendant},
    discovered ancestor ≤ discovered descendant → discovered descendant < returned ancestor →
      IsAncestor tree root ancestor descendant
  edge_target_discovered_before_return : ∀ {x y},
    Γ.Adj g x y → discovered x < discovered y → discovered y < returned x

/-- Every graph edge in a recursive DFS tree joins an ancestor-descendant pair. -/
theorem RecursiveTreeCertificate.edge_ancestor {h : Γ.IsUndirected g} {root x y : V}
    (dfs : RecursiveTreeCertificate h root) (hxy : Γ.Adj g x y) :
    IsAncestor dfs.tree root x y ∨ IsAncestor dfs.tree root y x := by
  have hxy' : h.toSimpleGraph.Adj x y := hxy
  have hxyne : x ≠ y := hxy'.ne
  have htime : dfs.discovered x ≠ dfs.discovered y := fun hEq ↦
    hxyne (dfs.discovered_injective hEq)
  rcases lt_or_gt_of_ne htime with hbefore | hbefore
  · exact Or.inl (dfs.discovered_during_is_descendant hbefore.le
      (dfs.edge_target_discovered_before_return hxy hbefore))
  · exact Or.inr (dfs.discovered_during_is_descendant hbefore.le
      (dfs.edge_target_discovered_before_return hxy'.symm hbefore))

/-- Kleinberg--Tardos theorem 3.7 for a non-tree edge of a recursive DFS tree. -/
theorem RecursiveTreeCertificate.nonTreeEdge_ancestor {h : Γ.IsUndirected g}
    {root x y : V} (dfs : RecursiveTreeCertificate h root)
    (hxy : Γ.Adj g x y) (_hnotTree : ¬dfs.tree.Adj x y) :
    IsAncestor dfs.tree root x y ∨ IsAncestor dfs.tree root y x :=
  dfs.edge_ancestor hxy

end KleinbergDFS
