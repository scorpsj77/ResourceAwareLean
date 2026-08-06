/-
Copyright (c) 2026 Jiyuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan
-/
import TextbookAlgorithms.KleinbergTardos.Chapter03.BFS.Complexity
import ResourceAware.Algorithms.GraphTraversal.Specification
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Correctness of Kleinberg's breadth-first search

This module proves exact reachability for executable layer-based BFS, constructs canonical
shortest-path-tree certificates for finite connected graphs, and proves Kleinberg's
bipartiteness application.
-/

universe u v

namespace KleinbergBFS

open ResourceAware ResourceAware.Algorithms
open ResourceAware.Graph

variable {G : Type u} {V : Type v} {Γ : Interface G V} {g : G}

/-! ## Executable visited-state semantics -/

/-- The public Boolean-table runner has the pure visited-state recurrence used below. -/
theorem run_visited_eq_loopResult [DecidableEq V]
    (model : ResourceModel G V) (graph : G) (source : V) :
    (Interpreter.run model graph GraphTraversal.ControlCostModel.unit
        GraphTraversal.VisitedModel.booleanTable GraphTraversal.LevelModel.table
        GraphTraversal.TreeModel.edgeList source).ret.2.visited =
      (Operational.loopResult model graph (model.vertexCount graph) 0 [source]
        (Operational.startVisited source)).visited := by
  let initial : Operational.State V := GraphTraversal.Model.initialState
    GraphTraversal.VisitedModel.booleanTable GraphTraversal.LevelModel.table
      GraphTraversal.TreeModel.edgeList
  change
    (Operational.execute model graph
      (bfs (model.vertexCount graph) source) initial).ret.2.visited = _
  rw [show bfs (model.vertexCount graph) source = (do
    GraphTraversal.clearVisited
    GraphTraversal.clearLevels
    GraphTraversal.clearTree
    GraphTraversal.markVisited source
    GraphTraversal.recordLevel source 0
    bfsLoop (model.vertexCount graph) 0 [source]) by rfl]
  simp only [Operational.execute_bind, Operational.execute_clearVisited,
    Operational.execute_clearLevels, Operational.execute_clearTree,
    Operational.execute_markVisited, Operational.execute_recordLevel]
  exact (Operational.bfsLoop_weightedOperationCost_le model graph 0 0 0 0 0
    (fun _ ↦ 0) (model.vertexCount graph) 0 [source]
    { visited := Operational.startVisited source
      levels := GraphTraversal.update (fun _ ↦ none) source (some 0)
      tree := [] }).1

namespace Operational

/-- A neighbor scan changes exactly the bits belonging to the scanned list. -/
theorem neighborResult_visited_iff [DecidableEq V]
    (visited : V → Bool) (neighbors : List V) (vertex : V) :
    (neighborResult visited neighbors).visited vertex = true ↔
      visited vertex = true ∨ vertex ∈ neighbors := by
  induction neighbors generalizing visited with
  | nil => simp [neighborResult]
  | cons head tail ih =>
      by_cases hhead : visited head
      · by_cases hvertex : vertex = head
        · subst head
          simp [neighborResult, hhead, ih]
        · simp [neighborResult, hhead, ih, hvertex]
      · by_cases hvertex : vertex = head
        · subst head
          simp [neighborResult, hhead, ih, GraphTraversal.update]
        · simp [neighborResult, hhead, ih, GraphTraversal.update, hvertex]

/-- A neighbor scan preserves old bits and sets precisely its fresh output bits. -/
theorem neighborResult_visited_iff_initial_or_fresh [DecidableEq V]
    (visited : V → Bool) (neighbors : List V) (vertex : V) :
    (neighborResult visited neighbors).visited vertex = true ↔
      visited vertex = true ∨ vertex ∈ (neighborResult visited neighbors).fresh := by
  induction neighbors generalizing visited with
  | nil => simp [neighborResult]
  | cons head tail ih =>
      by_cases hhead : visited head
      · simpa [neighborResult, hhead] using ih visited
      · by_cases hvertex : vertex = head
        · subst head
          simp [neighborResult, hhead, ih, GraphTraversal.update]
        · simp [neighborResult, hhead, ih, GraphTraversal.update, hvertex]

/-- A whole layer preserves old bits and sets precisely the vertices in its fresh output. -/
theorem layerResult_visited_iff_initial_or_fresh [DecidableEq V]
    (model : ResourceModel G V) (graph : G) (level : Nat)
    (current : List V) (visited : V → Bool) (vertex : V) :
    (layerResult model graph level current visited).visited vertex = true ↔
      visited vertex = true ∨ vertex ∈ (layerResult model graph level current visited).fresh := by
  induction current generalizing visited with
  | nil => simp [layerResult]
  | cons parent rest ih =>
      rw [show (layerResult model graph level (parent :: rest) visited).visited =
        (layerResult model graph level rest
          (neighborResult visited
            (model.neighborAccess.outNeighbors graph parent)).visited).visited by rfl]
      rw [ih, neighborResult_visited_iff_initial_or_fresh]
      change _ ↔ visited vertex = true ∨ vertex ∈
        (neighborResult visited (model.neighborAccess.outNeighbors graph parent)).fresh ++
          (layerResult model graph level rest
            (neighborResult visited
              (model.neighborAccess.outNeighbors graph parent)).visited).fresh
      simp only [List.mem_append]
      tauto

/-- A layer scan visits every neighbor of every vertex in that layer. -/
theorem layerResult_visits_neighbors [DecidableEq V]
    (model : ResourceModel G V) (graph : G) (level : Nat)
    (current : List V) (visited : V → Bool) {parent child : V}
    (hparent : parent ∈ current)
    (hchild : child ∈ model.neighborAccess.outNeighbors graph parent) :
    (layerResult model graph level current visited).visited child = true := by
  induction current generalizing visited with
  | nil => simp at hparent
  | cons head tail ih =>
      let scanned := neighborResult visited
        (model.neighborAccess.outNeighbors graph head)
      rcases List.mem_cons.mp hparent with rfl | hparent
      · change (layerResult model graph level tail scanned.visited).visited child = true
        exact (layerResult_properties model graph level tail scanned.visited).monotone child
          ((neighborResult_visited_iff visited
            (model.neighborAccess.outNeighbors graph parent) child).2 (Or.inr hchild))
      · change (layerResult model graph level tail scanned.visited).visited child = true
        exact ih scanned.visited hparent

/-- A BFS-loop recurrence only turns visited bits on. -/
theorem loopResult_monotone [DecidableEq V]
    (model : ResourceModel G V) (graph : G) (fuel level : Nat)
    (current : List V) (visited : V → Bool) {vertex : V}
    (hvertex : visited vertex = true) :
    (loopResult model graph fuel level current visited).visited vertex = true := by
  induction fuel generalizing level current visited with
  | zero => cases current <;> simpa [loopResult]
  | succ fuel ih =>
      cases current with
      | nil => simpa [loopResult]
      | cons head tail =>
          apply ih
          exact (layerResult_properties model graph level (head :: tail) visited).monotone
            vertex hvertex

/-- The frontier left when the BFS loop stops, including premature fuel exhaustion. -/
def finalFrontier [DecidableEq V] (model : ResourceModel G V) (graph : G) :
    Nat → Nat → List V → (V → Bool) → List V
  | 0, _, current, _ => current
  | _ + 1, _, [], _ => []
  | fuel + 1, level, current@(_ :: _), visited =>
      let layer := layerResult model graph level current visited
      finalFrontier model graph fuel (level + 1) layer.fresh layer.visited

/-- Final visited bits are exactly the initial bits plus all loop discoveries. -/
theorem loopResult_visited_iff_initial_or_discovered [DecidableEq V]
    (model : ResourceModel G V) (graph : G) (fuel level : Nat)
    (current : List V) (visited : V → Bool) (vertex : V) :
    (loopResult model graph fuel level current visited).visited vertex = true ↔
      visited vertex = true ∨
        vertex ∈ (loopResult model graph fuel level current visited).discovered := by
  induction fuel generalizing level current visited with
  | zero => cases current <;> simp [loopResult]
  | succ fuel ih =>
      cases current with
      | nil => simp [loopResult]
      | cons head tail =>
          rw [show (loopResult model graph (fuel + 1) level (head :: tail) visited).visited =
            (loopResult model graph fuel (level + 1)
              (layerResult model graph level (head :: tail) visited).fresh
              (layerResult model graph level (head :: tail) visited).visited).visited by rfl]
          rw [ih, layerResult_visited_iff_initial_or_fresh]
          change _ ↔ visited vertex = true ∨ vertex ∈
            (layerResult model graph level (head :: tail) visited).fresh ++
              (loopResult model graph fuel (level + 1)
                (layerResult model graph level (head :: tail) visited).fresh
                (layerResult model graph level (head :: tail) visited).visited).discovered
          simp only [List.mem_append]
          tauto

/-- Every initial or discovered frontier vertex is eventually queried or remains at termination. -/
theorem mem_queried_or_finalFrontier [DecidableEq V]
    (model : ResourceModel G V) (graph : G) (fuel level : Nat)
    (current : List V) (visited : V → Bool) {vertex : V}
    (hvertex : vertex ∈ current ∨
      vertex ∈ (loopResult model graph fuel level current visited).discovered) :
    vertex ∈ (loopResult model graph fuel level current visited).queried ∨
      vertex ∈ finalFrontier model graph fuel level current visited := by
  induction fuel generalizing level current visited with
  | zero =>
      cases current with
      | nil => simp [loopResult] at hvertex
      | cons head tail => simpa [loopResult, finalFrontier] using hvertex
  | succ fuel ih =>
      cases current with
      | nil => simp [loopResult] at hvertex
      | cons head tail =>
          let layer := layerResult model graph level (head :: tail) visited
          let rest := loopResult model graph fuel (level + 1) layer.fresh layer.visited
          change vertex ∈ head :: tail ∨ vertex ∈ layer.fresh ++ rest.discovered at hvertex
          change vertex ∈ (head :: tail) ++ rest.queried ∨
            vertex ∈ finalFrontier model graph fuel (level + 1) layer.fresh layer.visited
          rcases hvertex with hcurrent | hdiscovered
          · exact Or.inl (List.mem_append_left _ hcurrent)
          · rcases List.mem_append.mp hdiscovered with hfresh | hrest
            · rcases ih (level + 1) layer.fresh layer.visited (Or.inl hfresh) with h | h
              · exact Or.inl (List.mem_append_right _ h)
              · exact Or.inr h
            · rcases ih (level + 1) layer.fresh layer.visited (Or.inr hrest) with h | h
              · exact Or.inl (List.mem_append_right _ h)
              · exact Or.inr h

/-- Every neighbor of a queried vertex is visited when the loop finishes. -/
theorem loopResult_visits_queried_neighbors [DecidableEq V]
    (model : ResourceModel G V) (graph : G) (fuel level : Nat)
    (current : List V) (visited : V → Bool) {parent child : V}
    (hparent : parent ∈ (loopResult model graph fuel level current visited).queried)
    (hchild : child ∈ model.neighborAccess.outNeighbors graph parent) :
    (loopResult model graph fuel level current visited).visited child = true := by
  induction fuel generalizing level current visited with
  | zero => cases current <;> simp [loopResult] at hparent
  | succ fuel ih =>
      cases current with
      | nil => simp [loopResult] at hparent
      | cons head tail =>
          let layer := layerResult model graph level (head :: tail) visited
          let rest := loopResult model graph fuel (level + 1) layer.fresh layer.visited
          change parent ∈ (head :: tail) ++ rest.queried at hparent
          change rest.visited child = true
          rcases List.mem_append.mp hparent with hcurrent | hrest
          · exact loopResult_monotone model graph fuel (level + 1) layer.fresh layer.visited
              (layerResult_visits_neighbors model graph level (head :: tail) visited
                hcurrent hchild)
          · exact ih (level + 1) layer.fresh layer.visited hrest

/-- Facts needed to rule out premature BFS fuel exhaustion. -/
structure FinalFrontierProperties (model : ResourceModel G V) (graph : G)
    (fuel : Nat) (previous : List V) (result : LoopResult V) (frontier : List V) : Prop where
  frontier_nodup : frontier.Nodup
  previous_disjoint_frontier : previous.Disjoint frontier
  queried_disjoint_frontier : result.queried.Disjoint frontier
  frontier_vertices : ∀ vertex ∈ frontier,
    vertex ∈ model.vertexEnumeration.vertices graph
  frontier_visited : ∀ vertex ∈ frontier, result.visited vertex = true
  fuel_le_queried_length : frontier ≠ [] → fuel ≤ result.queried.length

/-- A nonempty terminal frontier would contain an additional distinct graph vertex. -/
theorem finalFrontier_properties [DecidableEq V]
    (model : ResourceModel G V) (graph : G) (fuel level : Nat)
    (previous current : List V) (visited : V → Bool)
    (hprevious : previous.Nodup) (hcurrent : current.Nodup)
    (hdisjoint : previous.Disjoint current)
    (hpreviousVisited : ∀ vertex ∈ previous, visited vertex = true)
    (hcurrentVisited : ∀ vertex ∈ current, visited vertex = true)
    (hcurrentVertices : ∀ vertex ∈ current,
      vertex ∈ model.vertexEnumeration.vertices graph) :
    FinalFrontierProperties model graph fuel previous
      (loopResult model graph fuel level current visited)
      (finalFrontier model graph fuel level current visited) := by
  induction fuel generalizing level previous current visited with
  | zero =>
      cases current <;> constructor <;> simp_all [loopResult, finalFrontier]
  | succ fuel ih =>
      cases current with
      | nil => constructor <;> simp [loopResult, finalFrontier]
      | cons head tail =>
          let current := head :: tail
          let layer := layerResult model graph level current visited
          let prior := previous ++ current
          have hlayer := layerResult_properties model graph level current visited
          have hpriorNodup : prior.Nodup := hprevious.append hcurrent hdisjoint
          have hpriorVisited : ∀ vertex ∈ prior, layer.visited vertex = true := by
            intro vertex hvertex
            apply hlayer.monotone vertex
            rcases List.mem_append.mp hvertex with hvertex | hvertex
            · exact hpreviousVisited vertex hvertex
            · exact hcurrentVisited vertex hvertex
          have hpriorFresh : prior.Disjoint layer.fresh := by
            rw [List.disjoint_iff_ne]
            rintro vertex hvertex _ hfresh rfl
            have hvisited : visited vertex = true := by
              rcases List.mem_append.mp hvertex with hvertex | hvertex
              · exact hpreviousVisited vertex hvertex
              · exact hcurrentVisited vertex hvertex
            rw [hlayer.fresh_unvisited vertex hfresh] at hvisited
            contradiction
          have hrest := ih (level + 1) prior layer.fresh layer.visited
            hpriorNodup hlayer.fresh_nodup hpriorFresh hpriorVisited
            hlayer.fresh_visited hlayer.fresh_vertices
          let rest := loopResult model graph fuel (level + 1) layer.fresh layer.visited
          let frontier := finalFrontier model graph fuel (level + 1)
            layer.fresh layer.visited
          change FinalFrontierProperties model graph (fuel + 1) previous
            { visited := rest.visited
              queried := current ++ rest.queried
              discovered := layer.fresh ++ rest.discovered } frontier
          have hpriorFrontier := List.disjoint_append_left.mp
            hrest.previous_disjoint_frontier
          constructor
          · exact hrest.frontier_nodup
          · exact hpriorFrontier.1
          · exact List.disjoint_append_left.mpr
              ⟨hpriorFrontier.2, hrest.queried_disjoint_frontier⟩
          · exact hrest.frontier_vertices
          · exact hrest.frontier_visited
          · intro hfrontier
            have hle := hrest.fuel_le_queried_length hfrontier
            change fuel ≤ rest.queried.length at hle
            have hcurrentLength : 0 < current.length := by simp [current]
            change fuel + 1 ≤ (current ++ rest.queried).length
            rw [List.length_append]
            omega

/-- With one unit of fuel per enumerated vertex, BFS cannot stop on a nonempty layer. -/
theorem finalFrontier_eq_nil [DecidableEq V]
    (model : ResourceModel G V) (graph : G) (source : V)
    (hsource : source ∈ model.interface.vertexSet graph) :
    finalFrontier model graph (model.vertexCount graph) 0 [source]
      (startVisited source) = [] := by
  let result := loopResult model graph (model.vertexCount graph) 0 [source]
    (startVisited source)
  let frontier := finalFrontier model graph (model.vertexCount graph) 0 [source]
    (startVisited source)
  have hproperties := loopResult_properties model graph (model.vertexCount graph) 0
    [] [source] (startVisited source) (by simp) (by simp) (by simp)
    (by simp) (by simp [startVisited, GraphTraversal.update])
    (by simpa using model.vertexEnumeration.complete hsource)
  have hfrontier := finalFrontier_properties model graph (model.vertexCount graph) 0
    [] [source] (startVisited source) (by simp) (by simp) (by simp)
    (by simp) (by simp [startVisited, GraphTraversal.update])
    (by simpa using model.vertexEnumeration.complete hsource)
  by_contra hne
  have hnonempty : frontier ≠ [] := by simpa [frontier]
  have hcombined : (result.queried ++ frontier).Nodup :=
    hproperties.queried_nodup.append hfrontier.frontier_nodup
      hfrontier.queried_disjoint_frontier
  have hvertices : ∀ vertex ∈ result.queried ++ frontier,
      vertex ∈ model.vertexEnumeration.vertices graph := by
    intro vertex hvertex
    rcases List.mem_append.mp hvertex with hvertex | hvertex
    · exact hproperties.queried_vertices vertex hvertex
    · exact hfrontier.frontier_vertices vertex hvertex
  have hlength := (ResourceModel.nodup_sublist_length_and_sum_le
    (result.queried ++ frontier) (model.vertexEnumeration.vertices graph)
    (fun _ ↦ 0) hcombined (model.vertexEnumeration.nodup graph) hvertices).1
  have hfuel := hfrontier.fuel_le_queried_length hnonempty
  have hfrontierLength : 0 < frontier.length := List.length_pos_iff.mpr hnonempty
  dsimp [result, frontier] at hlength hfuel hfrontierLength
  unfold ResourceModel.vertexCount at hlength hfuel hfrontierLength
  simp only [List.length_append] at hlength
  omega

/-- Processing a reachable layer cannot mark an unreachable vertex. -/
theorem layerResult_reachable [DecidableEq V]
    (model : ResourceModel G V) (graph : G) (source : V) (level : Nat)
    (current : List V) (visited : V → Bool)
    (hvisited : ∀ {vertex}, visited vertex = true →
      Reachable model.interface graph source vertex)
    (hcurrent : ∀ {vertex}, vertex ∈ current →
      Reachable model.interface graph source vertex) :
    ∀ {vertex}, (layerResult model graph level current visited).visited vertex = true →
      Reachable model.interface graph source vertex := by
  induction current generalizing visited with
  | nil =>
      intro vertex hvertex
      exact hvisited (by simpa [layerResult] using hvertex)
  | cons parent rest ih =>
      intro vertex hvertex
      let neighbors := model.neighborAccess.outNeighbors graph parent
      let scanned := neighborResult visited neighbors
      apply ih scanned.visited
      · intro candidate hcandidate
        rw [neighborResult_visited_iff] at hcandidate
        rcases hcandidate with hcandidate | hcandidate
        · exact hvisited hcandidate
        · exact Reachable.trans (hcurrent List.mem_cons_self)
            (.step (model.neighborAccess.sound hcandidate)
              (.refl (model.neighborAccess.target_mem hcandidate)))
      · intro candidate hcandidate
        exact hcurrent (List.mem_cons_of_mem parent hcandidate)
      · simpa [layerResult, neighbors, scanned] using hvertex

/-- Every bit set by a BFS-loop recurrence denotes a vertex reachable from the source. -/
theorem loopResult_reachable [DecidableEq V]
    (model : ResourceModel G V) (graph : G) (source : V)
    (fuel level : Nat) (current : List V) (visited : V → Bool)
    (hvisited : ∀ {vertex}, visited vertex = true →
      Reachable model.interface graph source vertex)
    (hcurrent : ∀ {vertex}, vertex ∈ current →
      Reachable model.interface graph source vertex) :
    ∀ {vertex}, (loopResult model graph fuel level current visited).visited vertex = true →
      Reachable model.interface graph source vertex := by
  induction fuel generalizing level current visited with
  | zero =>
      intro vertex hvertex
      exact hvisited (by cases current <;> simpa [loopResult] using hvertex)
  | succ fuel ih =>
      cases current with
      | nil =>
          intro vertex hvertex
          exact hvisited (by simpa [loopResult] using hvertex)
      | cons parent rest =>
          let layer := layerResult model graph level (parent :: rest) visited
          apply ih (level + 1) layer.fresh layer.visited
          · exact layerResult_reachable model graph source level (parent :: rest) visited
              hvisited hcurrent
          · intro vertex hvertex
            exact layerResult_reachable model graph source level (parent :: rest) visited
              hvisited hcurrent ((layerResult_properties model graph level
                (parent :: rest) visited).fresh_visited vertex hvertex)

/-- The Boolean-table BFS recurrence visits exactly the vertices reachable from its source. -/
theorem loopResult_visitsExactlyReachable [DecidableEq V]
    (model : ResourceModel G V) (graph : G) (source : V)
    (hsource : source ∈ model.interface.vertexSet graph) :
    GraphTraversal.VisitsExactlyReachable model.interface graph source fun vertex ↦
      (loopResult model graph (model.vertexCount graph) 0 [source]
        (startVisited source)).visited vertex = true := by
  let result := loopResult model graph (model.vertexCount graph) 0 [source]
    (startVisited source)
  apply ResourceAware.Algorithms.GraphTraversal.visitsExactlyReachable_of_closed
  · exact loopResult_monotone model graph (model.vertexCount graph) 0 [source]
      (startVisited source) (by simp [startVisited, GraphTraversal.update])
  · intro vertex hvertex
    apply loopResult_reachable model graph source (model.vertexCount graph) 0
      [source] (startVisited source)
    · intro candidate hcandidate
      have : candidate = source := by
        simpa [startVisited, GraphTraversal.update] using hcandidate
      subst candidate
      exact .refl hsource
    · intro candidate hcandidate
      have : candidate = source := by simpa using hcandidate
      subst candidate
      exact .refl hsource
    · exact hvertex
  · intro parent child hparent hedge
    have hinitialOrDiscovered :=
      (loopResult_visited_iff_initial_or_discovered model graph
        (model.vertexCount graph) 0 [source] (startVisited source) parent).1 hparent
    have hcurrentOrDiscovered : parent ∈ [source] ∨ parent ∈ result.discovered := by
      rcases hinitialOrDiscovered with hinitial | hdiscovered
      · left
        have : parent = source := by
          simpa [startVisited, GraphTraversal.update] using hinitial
        simp [this]
      · exact Or.inr hdiscovered
    have hqueryOrFinal := mem_queried_or_finalFrontier model graph
      (model.vertexCount graph) 0 [source] (startVisited source) hcurrentOrDiscovered
    have hquery : parent ∈ result.queried := by
      rcases hqueryOrFinal with hquery | hfinal
      · exact hquery
      · rw [finalFrontier_eq_nil model graph source hsource] at hfinal
        contradiction
    exact loopResult_visits_queried_neighbors model graph (model.vertexCount graph) 0
      [source] (startVisited source) hquery (model.neighborAccess.complete hedge)

end Operational

/-- Executable BFS with the standard Boolean table visits exactly the reachable vertices. -/
theorem run_visitsExactlyReachable [DecidableEq V]
    (model : ResourceModel G V) (graph : G) (source : V)
    (hsource : source ∈ model.interface.vertexSet graph) :
    GraphTraversal.VisitsExactlyReachable model.interface graph source fun vertex ↦
      (Interpreter.run model graph GraphTraversal.ControlCostModel.unit
        GraphTraversal.VisitedModel.booleanTable GraphTraversal.LevelModel.table
        GraphTraversal.TreeModel.edgeList source).ret.2.visited vertex = true := by
  rw [run_visited_eq_loopResult]
  exact Operational.loopResult_visitsExactlyReachable model graph source hsource

/-! ## Shortest-path trees -/

namespace ShortestPathTree

variable (graph : SimpleGraph V) (connected : graph.Connected) (source : V)

include connected in
/-- Every non-root vertex has a neighbor one step closer to the root. -/
theorem exists_predecessor (vertex : V) (hne : vertex ≠ source) :
    ∃ predecessor, graph.Adj predecessor vertex ∧
      graph.dist source vertex = graph.dist source predecessor + 1 := by
  obtain ⟨path, _, hlength⟩ :=
    SimpleGraph.Connected.exists_path_of_dist connected source vertex
  have hnotNil : ¬path.Nil := SimpleGraph.Walk.not_nil_of_ne hne.symm
  refine ⟨path.penultimate, path.adj_penultimate hnotNil, ?_⟩
  have hdrop : path.dropLast.length = graph.dist source path.penultimate :=
    SimpleGraph.length_eq_dist_of_subwalk hlength (SimpleGraph.Walk.isSubwalk_rfl path).dropLast
  rw [← hlength, ← hdrop]
  exact (path.length_dropLast_add_one hnotNil).symm

variable [DecidableEq V]

include connected in
/-- Choose the predecessor used by the canonical shortest-path tree. -/
noncomputable def parent (vertex : V) : V :=
  if hne : vertex = source then source
  else (exists_predecessor graph connected source vertex hne).choose

include connected in
theorem parent_spec {vertex : V} (hne : vertex ≠ source) :
    graph.Adj (parent graph connected source vertex) vertex ∧
      graph.dist source vertex =
        graph.dist source (parent graph connected source vertex) + 1 := by
  simpa [parent, hne] using (exists_predecessor graph connected source vertex hne).choose_spec

include connected in
/-- The graph containing the chosen predecessor edge of every non-root vertex. -/
noncomputable def tree : SimpleGraph V where
  Adj x y :=
    (x ≠ source ∧ parent graph connected source x = y) ∨
      (y ≠ source ∧ parent graph connected source y = x)
  symm := ⟨by tauto⟩
  loopless := ⟨by
    intro vertex hloop
    rcases hloop with hloop | hloop
    · exact (parent_spec graph connected source hloop.1).1.ne hloop.2
    · exact (parent_spec graph connected source hloop.1).1.ne hloop.2⟩

include connected in
theorem tree_adj {x y : V} : (tree graph connected source).Adj x y ↔
    (x ≠ source ∧ parent graph connected source x = y) ∨
      (y ≠ source ∧ parent graph connected source y = x) := Iff.rfl

include connected in
theorem tree_le : tree graph connected source ≤ graph := by
  intro x y hxy
  rcases hxy with ⟨hx, rfl⟩ | ⟨hy, rfl⟩
  · exact (parent_spec graph connected source hx).1.symm
  · exact (parent_spec graph connected source hy).1

include connected in
/-- The chosen-parent edges give a root-to-vertex walk of graph-shortest length. -/
theorem exists_walk_length_dist (vertex : V) :
    ∃ walk : (tree graph connected source).Walk source vertex,
      walk.length = graph.dist source vertex := by
  generalize hn : graph.dist source vertex = n
  induction n using Nat.strong_induction_on generalizing vertex with
  | h n ih =>
      by_cases hroot : vertex = source
      · subst vertex
        simp only [SimpleGraph.dist_self] at hn
        subst n
        exact ⟨.nil, rfl⟩
      · have hspec := parent_spec graph connected source hroot
        have hpred : graph.dist source (parent graph connected source vertex) < n := by omega
        obtain ⟨walk, hlength⟩ :=
          ih _ hpred (parent graph connected source vertex) rfl
        have hedge : (tree graph connected source).Adj
            (parent graph connected source vertex) vertex :=
          (tree_adj graph connected source).2 (Or.inr ⟨hroot, rfl⟩)
        refine ⟨walk.concat hedge, ?_⟩
        simp [SimpleGraph.Walk.length_concat, hlength, ← hn, hspec.2]

include connected in
theorem tree_connected : (tree graph connected source).Connected := by
  letI : Nonempty V := ⟨source⟩
  refine SimpleGraph.Connected.mk fun x y ↦ ?_
  have hx := (exists_walk_length_dist graph connected source x).choose.reachable
  have hy := (exists_walk_length_dist graph connected source y).choose.reachable
  exact hx.symm.trans hy

include connected in
/-- The selected edge belonging to a non-root vertex. -/
noncomputable def parentEdge (vertex : { vertex : V // vertex ≠ source }) :
    (tree graph connected source).edgeSet :=
  ⟨s(parent graph connected source vertex, vertex), by
    rw [SimpleGraph.mem_edgeSet]
    exact (tree_adj graph connected source).2 (Or.inr ⟨vertex.property, rfl⟩)⟩

include connected in
theorem parentEdge_injective :
    Function.Injective (parentEdge graph connected source) := by
  intro x y hxy
  apply Subtype.ext
  have hedge := congrArg Subtype.val hxy
  change s(parent graph connected source x, x) =
    s(parent graph connected source y, y) at hedge
  rw [Sym2.eq_iff] at hedge
  rcases hedge with hedge | hedge
  · exact hedge.2
  · have hx := parent_spec graph connected source x.property
    have hy := parent_spec graph connected source y.property
    rw [hedge.1] at hx
    rw [← hedge.2] at hy
    omega

include connected in
theorem parentEdge_surjective :
    Function.Surjective (parentEdge graph connected source) := by
  rintro ⟨edge, hedge⟩
  induction edge using Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeSet, tree_adj] at hedge
      rcases hedge with hedge | hedge
      · refine ⟨⟨x, hedge.1⟩, Subtype.ext ?_⟩
        change s(parent graph connected source x, x) = s(x, y)
        rw [hedge.2, Sym2.eq_swap]
      · refine ⟨⟨y, hedge.1⟩, Subtype.ext ?_⟩
        change s(parent graph connected source y, y) = s(x, y)
        rw [hedge.2]

include connected in
theorem tree_isTree [Finite V] : (tree graph connected source).IsTree := by
  letI : Fintype V := Fintype.ofFinite V
  letI : Nonempty V := ⟨source⟩
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨tree_connected graph connected source, ?_⟩
  have hcard := Nat.card_congr (Equiv.ofBijective (parentEdge graph connected source)
    ⟨parentEdge_injective graph connected source,
      parentEdge_surjective graph connected source⟩)
  rw [← hcard]
  simp only [Nat.card_eq_fintype_card]
  simp only [Fintype.card_subtype_compl]
  have heqcard : Fintype.card { vertex : V // vertex = source } = 1 := by simp
  rw [heqcard]
  have hpos : 0 < Fintype.card V := Fintype.card_pos
  omega

include connected in
theorem preservesDistance (vertex : V) :
    (tree graph connected source).dist source vertex = graph.dist source vertex := by
  obtain ⟨walk, hlength⟩ := exists_walk_length_dist graph connected source vertex
  apply le_antisymm
  · exact (SimpleGraph.dist_le walk).trans_eq hlength
  · exact walk.reachable.dist_anti (tree_le graph connected source)

end ShortestPathTree

/-- Layer `i` consists of the vertices at distance `i` from the BFS source. -/
def Layer (h : Γ.IsUndirected g) (source : V) (i : Nat) : Set V :=
  { vertex | h.toSimpleGraph.dist source vertex = i }

/-- Some graph edge has both endpoints in the same BFS layer. -/
def HasSameLayerEdge (h : Γ.IsUndirected g) (source : V) : Prop :=
  ∃ i x y, x ∈ Layer h source i ∧ y ∈ Layer h source i ∧ Γ.Adj g x y

/-- Color even-numbered BFS layers red and odd-numbered layers blue. -/
noncomputable def layerColor (h : Γ.IsUndirected g) (source vertex : V) : Fin 2 :=
  Fin.ofNat 2 (h.toSimpleGraph.dist source vertex)

/-- The parity coloring of the BFS layers is a proper graph coloring. -/
def IsValidLayerColoring (h : Γ.IsUndirected g) (source : V) : Prop :=
  ∀ ⦃x y⦄, Γ.Adj g x y → layerColor h source x ≠ layerColor h source y

/--
A semantic certificate for the tree produced by BFS: it is a spanning tree contained in the
graph, and its root-to-vertex distances equal the corresponding graph distances.
-/
structure TreeCertificate (h : Γ.IsUndirected g) (source : V) where
  tree : SimpleGraph V
  tree_le : tree ≤ h.toSimpleGraph
  isTree : tree.IsTree
  preservesDistance : ∀ vertex, tree.dist source vertex = h.toSimpleGraph.dist source vertex

/-- Every finite connected graph has the canonical shortest-path-tree certificate rooted at
`source`. -/
noncomputable def TreeCertificate.ofConnected [DecidableEq V] [Fintype V]
    (h : Γ.IsUndirected g) (source : V) (connected : h.toSimpleGraph.Connected) :
    TreeCertificate h source where
  tree := ShortestPathTree.tree h.toSimpleGraph connected source
  tree_le := ShortestPathTree.tree_le h.toSimpleGraph connected source
  isTree := ShortestPathTree.tree_isTree h.toSimpleGraph connected source
  preservesDistance := ShortestPathTree.preservesDistance h.toSimpleGraph connected source

/-- Representation-independent correctness evidence for a completed standard BFS run. -/
structure RunCertificate [DecidableEq V] (model : ResourceModel G V) (graph : G)
    (h : model.interface.IsUndirected graph) (source : V) where
  visitsExactlyReachable : GraphTraversal.VisitsExactlyReachable model.interface graph source
    fun vertex ↦
      (Interpreter.run model graph GraphTraversal.ControlCostModel.unit
        GraphTraversal.VisitedModel.booleanTable GraphTraversal.LevelModel.table
        GraphTraversal.TreeModel.edgeList source).ret.2.visited vertex = true
  shortestPathTree : TreeCertificate h source

/-- Executable BFS yields exact reachability together with its shortest-path-tree certificate. -/
noncomputable def run_certificate [DecidableEq V] [Fintype V]
    (model : ResourceModel G V) (graph : G)
    (h : model.interface.IsUndirected graph) (source : V)
    (hsource : source ∈ model.interface.vertexSet graph)
    (connected : h.toSimpleGraph.Connected) : RunCertificate model graph h source where
  visitsExactlyReachable := run_visitsExactlyReachable model graph source hsource
  shortestPathTree := TreeCertificate.ofConnected h source connected

/-- A certified BFS tree entails the textbook connected-graph hypothesis. -/
theorem TreeCertificate.graphConnected {h : Γ.IsUndirected g} {source : V}
    (bfs : TreeCertificate h source) : h.toSimpleGraph.Connected :=
  SimpleGraph.Connected.mono bfs.tree_le bfs.isTree.connected

/-- If no edge stays within one layer, BFS layer parity gives a proper two-coloring. -/
theorem layerColoring_valid_of_no_sameLayerEdge (h : Γ.IsUndirected g) (source : V)
    (hno : ¬ HasSameLayerEdge h source) : IsValidLayerColoring h source := by
  intro x y hxy
  have hxy' : h.toSimpleGraph.Adj x y := hxy
  have hne : h.toSimpleGraph.dist source x ≠ h.toSimpleGraph.dist source y := fun he ↦
    hno ⟨_, x, y, rfl, he.symm, hxy⟩
  have hstep :
      h.toSimpleGraph.dist source x = h.toSimpleGraph.dist source y + 1 ∨
      h.toSimpleGraph.dist source y = h.toSimpleGraph.dist source x + 1 := by
    rcases hxy'.diff_dist_adj (u := source) with h | h | h <;>
      rcases hxy'.symm.diff_dist_adj (u := source) with h' | h' | h' <;> omega
  apply Fin.ne_of_val_ne
  change h.toSimpleGraph.dist source x % 2 ≠ h.toSimpleGraph.dist source y % 2
  rcases hstep with h | h <;> omega

/--
A same-layer edge closes the even-length tree path between its endpoints into an odd cycle.
This is the textbook lowest-common-ancestor construction expressed via the unique tree path.
-/
theorem TreeCertificate.oddCycle_of_sameLayerEdge {h : Γ.IsUndirected g} {source : V}
    (bfs : TreeCertificate h source) (hsame : HasSameLayerEdge h source) :
    Γ.ContainsOddCycle h := by
  classical
  rcases hsame with ⟨_, x, y, hx, hy, hxy⟩
  have hlevel : bfs.tree.dist source x = bfs.tree.dist source y := by
    rw [bfs.preservesDistance x, bfs.preservesDistance y, hx, hy]
  obtain ⟨p, hp, _⟩ := bfs.isTree.existsUnique_path y x
  let coloringFin := bfs.isTree.coloringTwoOfVert source
  let coloring : bfs.tree.Coloring Bool :=
    SimpleGraph.recolorOfEquiv bfs.tree finTwoEquiv coloringFin
  have hfin : coloringFin y = coloringFin x :=
    Fin.ext (congrArg (· % 2) hlevel.symm)
  have hpEven : Even p.length := (coloring.even_length_iff_congr p).2 <| by
    have : coloring y = coloring x := congrArg finTwoEquiv hfin
    simp [this]
  let path : h.toSimpleGraph.Path y x := ⟨p.mapLe bfs.tree_le, hp.mapLe bfs.tree_le⟩
  have hedge : s(x, y) ∉ (path : h.toSimpleGraph.Walk y x).edges := by
    intro hedge
    change s(x, y) ∈ (p.mapLe bfs.tree_le).edges at hedge
    rw [SimpleGraph.Walk.edges_mapLe_eq_edges, Sym2.eq_swap] at hedge
    exact Nat.not_even_one ((hp.length_eq_one_of_mem_edges hedge) ▸ hpEven)
  let cycle : h.toSimpleGraph.Walk x x := .cons hxy path
  refine ⟨x, cycle, path.cons_isCycle hxy hedge, ?_⟩
  change Odd ((p.mapLe bfs.tree_le).length + 1)
  have hlength : (p.mapLe bfs.tree_le).length = p.length := by
    change (p.map (SimpleGraph.Hom.ofLE bfs.tree_le)).length = p.length
    exact p.length_map _
  rw [hlength]
  exact hpEven.add_one

/-- Case (i) of theorem (3.15). -/
def ProperLayerCase (h : Γ.IsUndirected g) (source : V) : Prop :=
  ¬ HasSameLayerEdge h source ∧ IsValidLayerColoring h source ∧ Γ.IsBipartite g

/-- Case (ii) of theorem (3.15). -/
def OddCycleCase (h : Γ.IsUndirected g) (source : V) : Prop :=
  HasSameLayerEdge h source ∧ Γ.ContainsOddCycle h ∧ ¬ Γ.IsBipartite g

/--
Kleinberg theorem (3.15): exactly one of the proper-layer and odd-cycle cases holds for BFS.
-/
theorem bfs_bipartite_or_contains_odd_cycle {h : Γ.IsUndirected g} {source : V}
    (bfs : TreeCertificate h source) :
    Xor (ProperLayerCase h source) (OddCycleCase h source) := by
  by_cases hsame : HasSameLayerEdge h source
  · have hodd := bfs.oddCycle_of_sameLayerEdge hsame
    have hnotBipartite : ¬ Γ.IsBipartite g := fun hbipartite ↦
      Γ.bipartite_has_no_odd_cycle h hbipartite hodd
    exact Or.inr
      ⟨⟨hsame, hodd, hnotBipartite⟩, fun hproper ↦ hproper.1 hsame⟩
  · have hvalid := layerColoring_valid_of_no_sameLayerEdge h source hsame
    have hbipartite : Γ.IsBipartite g := ⟨layerColor h source, hvalid⟩
    exact Or.inl
      ⟨⟨hsame, hvalid, hbipartite⟩, fun hodd ↦ hsame hodd.1⟩

end KleinbergBFS
