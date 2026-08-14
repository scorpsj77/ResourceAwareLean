/-
Copyright (c) 2026 Jiyuan (Chai Yuen) Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan (Chai Yuen) Ji
-/
import TextbookAlgorithms.KleinbergTardos.Chapter03.DFS.ResourceModel

/-!
# Resource analysis of Kleinberg's depth-first search

This module connects the measured trace emitted by stack-based DFS to the textbook aggregate
bounds. Static and working-space accounting and the thin runner live in `ResourceModel.lean`;
generic execution and trace collection come from `ResourceAware.Program`.
-/

namespace KleinbergDFS

open ResourceAware ResourceAware.Algorithms
open ResourceAware.Graph
open Cslib.Algorithms.Lean
open Filter Asymptotics

/-! ## Cost-independent operation-profile accounting -/

namespace Operational

universe u v

set_option linter.unusedSimpArgs false

/-- Interpreter state selected by the textbook DFS resource model. -/
abbrev State (Vertex : Type v) :=
  GraphTraversal.Model.State (Vertex → Bool) PUnit PUnit

/-- Execute a DFS program from an arbitrary Boolean-table interpreter state. -/
def execute {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G)
    (program : GraphTraversal.Program Vertex α) (state : State Vertex) :
    TraceM (GraphTraversal.Event Vertex) (α × State Vertex) :=
  GraphTraversal.Model.interpretFrom program model graph
    GraphTraversal.ControlCostModel.unit GraphTraversal.VisitedModel.booleanTable
    GraphTraversal.LevelModel.discard GraphTraversal.TreeModel.discard state

@[simp]
theorem execute_pure {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (value : α) (state : State Vertex) :
    execute model graph (pure value) state = pure (value, state) := by
  rfl

theorem execute_bind {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G)
    (program : GraphTraversal.Program Vertex α) (next : α → GraphTraversal.Program Vertex β)
    (state : State Vertex) :
    execute model graph (program >>= next) state = (do
      let (result, state') ← execute model graph program state
      execute model graph (next result) state') := by
  exact GraphTraversal.Model.interpretFrom_bind program next model graph _ _ _ _ state

@[simp]
theorem execute_checkStackEmpty {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (state : State Vertex) :
    execute model graph GraphTraversal.checkStackEmpty state =
      ⟨(.unit, state), EventTrace.singleton ⟨.checkStackEmpty, 1⟩⟩ := by
  rfl

@[simp]
theorem execute_isVisited {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (vertex : Vertex) (state : State Vertex) :
    execute model graph (GraphTraversal.isVisited vertex) state =
      ⟨(ULift.up (state.visited vertex), state),
        EventTrace.singleton ⟨.isVisited vertex, 1⟩⟩ := by
  rfl

@[simp]
theorem execute_markVisited {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (vertex : Vertex) (state : State Vertex) :
    execute model graph (GraphTraversal.markVisited vertex) state =
      ⟨(.unit, { state with visited := GraphTraversal.update state.visited vertex true }),
        EventTrace.singleton ⟨.markVisited vertex, 1⟩⟩ := by
  rfl

@[simp]
theorem execute_neighbors {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (vertex : Vertex) (state : State Vertex) :
    execute model graph (GraphTraversal.neighbors vertex) state =
      ⟨(model.neighborAccess.outNeighbors graph vertex, state),
        EventTrace.singleton ⟨.neighbors vertex, model.neighborCost graph vertex⟩⟩ := by
  rfl

@[simp]
theorem execute_clearVisited {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (state : State Vertex) :
    execute model graph GraphTraversal.clearVisited state =
      ⟨(.unit, { state with visited := fun _ ↦ false }),
        EventTrace.singleton ⟨.clearVisited, model.vertexCount graph⟩⟩ := by
  rfl

/-- Pure summary of one DFS-loop execution. -/
structure LoopResult (Vertex : Type v) where
  visited : Vertex → Bool
  queried : List Vertex

/-- The semantic recurrence implemented by Boolean-table DFS trace interpretation. -/
def loopResult {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) :
    Nat → List Vertex → (Vertex → Bool) → LoopResult Vertex
  | 0, [], visited => ⟨visited, []⟩
  | 0, _ :: _, visited => ⟨visited, []⟩
  | _ + 1, [], visited => ⟨visited, []⟩
  | fuel + 1, vertex :: stack, visited =>
      if visited vertex then
        let rest := loopResult model graph fuel stack visited
        ⟨rest.visited, rest.queried⟩
      else
        let visited' := GraphTraversal.update visited vertex true
        let neighbors := model.neighborAccess.outNeighbors graph vertex
        let rest := loopResult model graph fuel (pushNeighbors neighbors stack) visited'
        ⟨rest.visited, vertex :: rest.queried⟩

/-- Cost-independent weights used to summarize a DFS-loop operation profile. -/
def loopOperationCharge {G : Type u} (model : ResourceModel G Vertex) (graph : G)
    (checkStackEmpty isVisited markVisited : Nat) (other : GraphTraversal.Op Vertex → Nat) :
    GraphTraversal.Op Vertex → Nat
  | .checkStackEmpty => checkStackEmpty
  | .isVisited _ => isVisited
  | .markVisited _ => markVisited
  | .neighbors vertex => model.neighborCost graph vertex
  | operation => other operation

set_option linter.flexible false in
/-- One cost-independent DFS operation-profile proof, reusable under every bounded cost model. -/
theorem dfsLoop_weightedOperationCost_le {G : Type u} {Vertex : Type v}
    [DecidableEq Vertex] (model : ResourceModel G Vertex) (graph : G)
    (checkStackEmpty isVisited markVisited : Nat) (fuel : Nat) (stack : List Vertex)
    (state : State Vertex) (other : GraphTraversal.Op Vertex → Nat) :
    let expected := loopResult model graph fuel stack state.visited
    let actual := execute model graph (dfsLoop fuel stack) state
    actual.ret.2.visited = expected.visited ∧
      ResourceAware.Program.weightedOperationCost
          (loopOperationCharge model graph checkStackEmpty isVisited markVisited other) actual ≤
        (checkStackEmpty + isVisited) * fuel + checkStackEmpty +
          markVisited * expected.queried.length +
            (expected.queried.map fun vertex ↦ model.neighborCost graph vertex).sum := by
  induction fuel generalizing stack state with
  | zero =>
      cases stack <;>
        simp [dfsLoop, loopResult, execute_bind, loopOperationCharge,
          ResourceAware.Program.weightedOperationCost, TraceM.projectedCost, TraceM.cost,
          ResourceAware.Program.Event.erase]
  | succ fuel ih =>
      cases stack with
      | nil =>
          simp [dfsLoop, loopResult, execute_bind, loopOperationCharge,
            ResourceAware.Program.weightedOperationCost, TraceM.projectedCost, TraceM.cost,
            ResourceAware.Program.Event.erase, Nat.add_mul]
      | cons vertex stack =>
          rw [show dfsLoop (fuel + 1) (vertex :: stack) = (do
            GraphTraversal.checkStackEmpty
            let seen ← GraphTraversal.isVisited vertex
            if seen.down then
              dfsLoop fuel stack
            else do
              GraphTraversal.markVisited vertex
              let neighbors ← GraphTraversal.neighbors vertex
              dfsLoop fuel (pushNeighbors neighbors stack)) by rfl]
          rw [execute_bind, execute_checkStackEmpty]
          simp [execute_bind, loopOperationCharge,
            ResourceAware.Program.weightedOperationCost, TraceM.projectedCost, TraceM.cost,
            ResourceAware.Program.Event.erase]
          by_cases hseen : state.visited vertex
          · simp [hseen, loopResult]
            have hrest := ih stack state
            refine ⟨hrest.1, ?_⟩
            simp only [ResourceAware.Program.weightedOperationCost, TraceM.projectedCost,
              TraceM.cost] at hrest
            simp [Nat.add_mul, Nat.mul_add] at hrest ⊢
            omega
          · simp [hseen, loopResult]
            rw [execute_bind, execute_markVisited]
            simp [loopOperationCharge, ResourceAware.Program.Event.erase]
            rw [execute_bind, execute_neighbors]
            simp [loopOperationCharge, ResourceAware.Program.Event.erase, Nat.add_assoc]
            let nextState : State Vertex :=
              { state with visited := GraphTraversal.update state.visited vertex true }
            have hrest := ih
              (pushNeighbors (model.neighborAccess.outNeighbors graph vertex) stack) nextState
            dsimp [nextState] at hrest
            refine ⟨hrest.1, ?_⟩
            simp only [ResourceAware.Program.weightedOperationCost, TraceM.projectedCost,
              TraceM.cost] at hrest
            simp [Nat.add_mul, Nat.mul_add] at hrest ⊢
            omega

/-- Membership after pushing neighbors is membership in the neighbors or the old stack. -/
theorem mem_pushNeighbors {vertex : Vertex} (neighbors stack : List Vertex) :
    vertex ∈ pushNeighbors neighbors stack ↔ vertex ∈ neighbors ∨ vertex ∈ stack := by
  induction neighbors generalizing stack with
  | nil => simp [pushNeighbors]
  | cons head tail ih =>
      rw [pushNeighbors, ih]
      simp only [List.mem_cons]
      tauto

set_option linter.flexible false in
/-- DFS only turns visited bits on; queried vertices were initially unvisited and are unique. -/
theorem loopResult_visited_and_nodup {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (fuel : Nat) (stack : List Vertex)
    (visited : Vertex → Bool) :
    let result := loopResult model graph fuel stack visited
    (∀ vertex, visited vertex = true → result.visited vertex = true) ∧
      (∀ vertex ∈ result.queried, visited vertex = false) ∧ result.queried.Nodup := by
  induction fuel generalizing stack visited with
  | zero =>
      cases stack <;> simp [loopResult]
  | succ fuel ih =>
      cases stack with
      | nil => simp [loopResult]
      | cons vertex stack =>
          by_cases hseen : visited vertex
          · simpa [loopResult, hseen] using ih stack visited
          · simp [loopResult, hseen]
            let visited' := GraphTraversal.update visited vertex true
            let nextStack :=
              pushNeighbors (model.neighborAccess.outNeighbors graph vertex) stack
            have hrest := ih nextStack visited'
            refine ⟨?_, ?_, ?_⟩
            · intro candidate hcand
              exact hrest.1 candidate (by simp [visited', GraphTraversal.update, hcand])
            · intro candidate hcand
              refine Bool.eq_false_iff.mpr fun hcandTrue ↦ ?_
              have := hrest.2.1 candidate hcand
              simp [visited', GraphTraversal.update, hcandTrue] at this
            · refine ⟨?_, hrest.2.2⟩
              intro hmem
              simpa [visited', GraphTraversal.update] using hrest.2.1 vertex hmem

set_option linter.flexible false in
/-- Every queried vertex belongs to the verified finite vertex enumeration. -/
theorem loopResult_queried_mem_vertices {G : Type u} {Vertex : Type v}
    [DecidableEq Vertex] (model : ResourceModel G Vertex) (graph : G)
    (fuel : Nat) (stack : List Vertex) (visited : Vertex → Bool)
    (hstack : ∀ vertex ∈ stack, vertex ∈ model.vertexEnumeration.vertices graph) :
    ∀ vertex ∈ (loopResult model graph fuel stack visited).queried,
      vertex ∈ model.vertexEnumeration.vertices graph := by
  induction fuel generalizing stack visited with
  | zero =>
      cases stack <;> simp [loopResult]
  | succ fuel ih =>
      cases stack with
      | nil => simp [loopResult]
      | cons vertex stack =>
          by_cases hseen : visited vertex
          · simpa [loopResult, hseen] using ih stack visited (fun candidate hcand ↦
              hstack candidate (List.mem_cons_of_mem vertex hcand))
          · simp [loopResult, hseen]
            refine ⟨hstack vertex (List.mem_cons_self), ?_⟩
            apply ih
            intro candidate hcand
            rw [mem_pushNeighbors] at hcand
            rcases hcand with hcand | hcand
            · exact model.vertexEnumeration.complete
                (model.neighborAccess.target_mem hcand)
            · exact hstack candidate (List.mem_cons_of_mem vertex hcand)

end Operational

/-! ## Cost-parametric operational accounting -/

namespace BoundedOperational

universe u v

/-- Arbitrary costs for the standard Boolean-table DFS backend and control checks. -/
structure CostModel (Vertex : Type v) where
  control : GraphTraversal.ControlCostModel
  visited : GraphTraversal.VisitedCostModel Vertex (Vertex → Bool)

/-- Uniform upper bounds for every primitive operation used by DFS on one graph. -/
structure CostBounds where
  checkStackEmpty : Nat
  clearVisited : Nat
  isVisited : Nat
  markVisited : Nat

/-- The selected DFS operation costs respect the supplied upper bounds. -/
structure CostModel.IsBoundedBy {Vertex : Type v} (costs : CostModel Vertex)
    (bounds : CostBounds) (vertexCount : Nat) : Prop where
  checkStackEmpty : costs.control.checkStackEmptyCost ≤ bounds.checkStackEmpty
  clearVisited : costs.visited.clearCost vertexCount ≤ bounds.clearVisited
  isVisited : ∀ state vertex, costs.visited.isVisitedCost state vertex ≤ bounds.isVisited
  markVisited : ∀ state vertex,
    costs.visited.markVisitedCost state vertex ≤ bounds.markVisited

/-- Standard Boolean-table semantics equipped with arbitrary visited-operation costs. -/
def visitedModel [DecidableEq Vertex] (costs : CostModel Vertex) :
    GraphTraversal.VisitedModel Vertex (Vertex → Bool) :=
  { GraphTraversal.VisitedModel.booleanTable with
      cost := costs.visited }

/-- Execute DFS with the standard backend and arbitrary operation costs. -/
def execute {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (costs : CostModel Vertex)
    (program : GraphTraversal.Program Vertex α) (state : Operational.State Vertex) :
    TraceM (GraphTraversal.Event Vertex) (α × Operational.State Vertex) :=
  GraphTraversal.Model.interpretFrom program model graph costs.control
    (visitedModel costs) GraphTraversal.LevelModel.discard
    GraphTraversal.TreeModel.discard state

/-- Upper-bound cost of the check and visited test performed on every stack pop. -/
def popCost (bounds : CostBounds) : Nat :=
  bounds.checkStackEmpty + bounds.isVisited

/-- Weights for all operations; the DFS profile uses only the four bounded cases and neighbors. -/
def otherOperationCharge (costs : CostModel Vertex) (bounds : CostBounds) :
    GraphTraversal.Op Vertex → Nat
  | .checkLayerEmpty level => costs.control.checkLayerEmptyCost level
  | .clearVisited => bounds.clearVisited
  | .clearLevels => 0
  | .clearTree => 0
  | .recordLevel _ _ => 0
  | .addTreeEdge _ _ => 0
  | _ => 0

/-- The operation weights used to reinterpret the cost-independent DFS profile. -/
def operationCharge {G : Type u} (model : ResourceModel G Vertex) (graph : G)
    (costs : CostModel Vertex) (bounds : CostBounds) : GraphTraversal.Op Vertex → Nat :=
  Operational.loopOperationCharge model graph bounds.checkStackEmpty bounds.isVisited
    bounds.markVisited (otherOperationCharge costs bounds)

/-- Primitive cost assumptions are discharged once when constructing the generic interpreter
bound, rather than inside every recursive DFS proof. -/
theorem interpreter_isBoundedBy {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (costs : CostModel Vertex)
    (bounds : CostBounds) (hbounds : costs.IsBoundedBy bounds (model.vertexCount graph)) :
    GraphTraversal.Model.IsBoundedBy model graph costs.control
      (visitedModel costs) GraphTraversal.LevelModel.discard GraphTraversal.TreeModel.discard
      (operationCharge model graph costs bounds) := by
  constructor
  · intro level
    simp [operationCharge, Operational.loopOperationCharge, otherOperationCharge]
  · simpa [operationCharge, Operational.loopOperationCharge] using hbounds.checkStackEmpty
  · simpa [operationCharge, Operational.loopOperationCharge, otherOperationCharge,
      visitedModel] using hbounds.clearVisited
  · simp [operationCharge, Operational.loopOperationCharge, otherOperationCharge,
      GraphTraversal.LevelModel.discard, GraphTraversal.LevelCostModel.discard]
  · simp [operationCharge, Operational.loopOperationCharge, otherOperationCharge,
      GraphTraversal.TreeModel.discard, GraphTraversal.TreeCostModel.discard]
  · intro vertex
    simp [operationCharge, Operational.loopOperationCharge]
  · intro state vertex
    simpa [operationCharge, Operational.loopOperationCharge, visitedModel] using
      hbounds.isVisited state vertex
  · intro state vertex
    simpa [operationCharge, Operational.loopOperationCharge, visitedModel] using
      hbounds.markVisited state vertex
  · intro state vertex level
    simp [operationCharge, Operational.loopOperationCharge, otherOperationCharge,
      GraphTraversal.LevelModel.discard, GraphTraversal.LevelCostModel.discard]
  · intro state parent child
    simp [operationCharge, Operational.loopOperationCharge, otherOperationCharge,
      GraphTraversal.TreeModel.discard, GraphTraversal.TreeCostModel.discard]

/-- The public DFS runner obeys arbitrary supplied upper bounds for primitive costs. -/
theorem exactCost_run_le {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (costs : CostModel Vertex)
    (bounds : CostBounds) (hbounds : costs.IsBoundedBy bounds (model.vertexCount graph))
    (source : Vertex) :
    let result := Operational.loopResult model graph (stackPopBound model graph) [source]
      (fun _ ↦ false)
    KleinbergDFS.exactCost
        (KleinbergDFS.Interpreter.run model graph costs.control (visitedModel costs) source) ≤
      bounds.clearVisited + popCost bounds * stackPopBound model graph +
        bounds.checkStackEmpty + bounds.markVisited * result.queried.length +
          (result.queried.map fun vertex ↦ model.neighborCost graph vertex).sum := by
  let initial : Operational.State Vertex := GraphTraversal.Model.initialState
    (visitedModel costs) GraphTraversal.LevelModel.discard GraphTraversal.TreeModel.discard
  let program := dfs (stackPopBound model graph) source
  let charge := operationCharge model graph costs bounds
  let actual := execute model graph costs program initial
  let standard := Operational.execute model graph program initial
  change ResourceAware.Program.exactCost actual ≤ _
  have hcost : ResourceAware.Program.exactCost actual ≤
      ResourceAware.Program.weightedOperationCost charge actual := by
    simpa [actual, program, initial, charge, execute] using
      GraphTraversal.Model.exactCost_interpretFrom_le_weightedOperationCost
        program model graph costs.control (visitedModel costs) GraphTraversal.LevelModel.discard
        GraphTraversal.TreeModel.discard charge
        (interpreter_isBoundedBy model graph costs bounds hbounds) initial
  have htrace : ResourceAware.Program.operationTrace actual =
      ResourceAware.Program.operationTrace standard := by
    simpa [actual, standard, execute, Operational.execute, initial,
      ResourceAware.Program.operationTrace] using
      GraphTraversal.Model.operationTrace_interpretFrom_eq_of_backend_eq
        program model graph costs.control GraphTraversal.ControlCostModel.unit
        (visitedModel costs) GraphTraversal.VisitedModel.booleanTable
        GraphTraversal.LevelModel.discard GraphTraversal.LevelModel.discard
        GraphTraversal.TreeModel.discard GraphTraversal.TreeModel.discard rfl rfl rfl initial
  have hweighted : ResourceAware.Program.weightedOperationCost charge actual =
      ResourceAware.Program.weightedOperationCost charge standard :=
    ResourceAware.Program.weightedOperationCost_eq_of_operationTrace_eq charge htrace
  have hloop := Operational.dfsLoop_weightedOperationCost_le model graph
    bounds.checkStackEmpty bounds.isVisited bounds.markVisited (stackPopBound model graph)
    [source] ({ visited := fun _ ↦ false, levels := .unit, tree := .unit } :
      Operational.State Vertex) (otherOperationCharge costs bounds)
  have hstandard : ResourceAware.Program.weightedOperationCost charge standard ≤
      bounds.clearVisited + popCost bounds * stackPopBound model graph +
        bounds.checkStackEmpty +
          bounds.markVisited *
            (Operational.loopResult model graph (stackPopBound model graph) [source]
              (fun _ ↦ false)).queried.length +
          ((Operational.loopResult model graph (stackPopBound model graph) [source]
              (fun _ ↦ false)).queried.map fun vertex ↦
                model.neighborCost graph vertex).sum := by
    dsimp [standard, program]
    rw [show dfs (stackPopBound model graph) source = (do
      GraphTraversal.clearVisited
      dfsLoop (stackPopBound model graph) [source]) by rfl]
    rw [Operational.execute_bind, Operational.execute_clearVisited]
    simp only [ResourceAware.Program.weightedOperationCost_bind]
    change bounds.clearVisited + ResourceAware.Program.weightedOperationCost charge
      (Operational.execute model graph (dfsLoop (stackPopBound model graph) [source])
        ({ visited := fun _ ↦ false, levels := .unit, tree := .unit } :
          Operational.State Vertex)) ≤ _
    have hloopCost : ResourceAware.Program.weightedOperationCost charge
        (Operational.execute model graph (dfsLoop (stackPopBound model graph) [source])
          ({ visited := fun _ ↦ false, levels := .unit, tree := .unit } :
            Operational.State Vertex)) ≤
        popCost bounds * stackPopBound model graph + bounds.checkStackEmpty +
          bounds.markVisited *
            (Operational.loopResult model graph (stackPopBound model graph) [source]
              (fun _ ↦ false)).queried.length +
          ((Operational.loopResult model graph (stackPopBound model graph) [source]
              (fun _ ↦ false)).queried.map fun vertex ↦
                model.neighborCost graph vertex).sum := by
      simpa [charge, operationCharge, popCost] using hloop.2
    omega
  exact hcost.trans (hweighted.le.trans hstandard)

/-- Unit-cost instance used only to recover the traditional concrete DFS corollaries. -/
def unitCostModel [DecidableEq Vertex] : CostModel Vertex where
  control := GraphTraversal.ControlCostModel.unit
  visited := GraphTraversal.VisitedCostModel.booleanTable

/-- Bounds realized by the standard unit-cost DFS backends on an `n`-vertex graph. -/
def unitCostBounds (n : Nat) : CostBounds where
  checkStackEmpty := 1
  clearVisited := n
  isVisited := 1
  markVisited := 1

/-- The standard DFS models satisfy their unit-cost bounds. -/
theorem unitCostModel_isBoundedBy [DecidableEq Vertex] (n : Nat) :
    (unitCostModel : CostModel Vertex).IsBoundedBy (unitCostBounds n) n := by
  constructor <;> simp [unitCostModel, unitCostBounds,
    GraphTraversal.ControlCostModel.unit, GraphTraversal.VisitedCostModel.booleanTable]

/-- Graph-wide DFS work expressed using arbitrary primitive-operation bounds. -/
def modelWorkBound {G : Type u} (bounds : CostBounds) (model : ResourceModel G Vertex)
    (graph : G) : Nat :=
  bounds.clearVisited + popCost bounds * stackPopBound model graph +
    bounds.checkStackEmpty + bounds.markVisited * model.vertexCount graph +
      model.totalNeighborCost graph

/-- A single constant dominating all per-vertex and per-entry DFS work. -/
def textbookConstant (bounds : CostBounds) : Nat :=
  popCost bounds + bounds.markVisited + 1

end BoundedOperational

/-! ## Time complexity -/

/-- The exact DFS trace is bounded under any operation costs satisfying `bounds`. -/
theorem exactCost_le_modelWork {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G)
    (costs : BoundedOperational.CostModel Vertex) (bounds : BoundedOperational.CostBounds)
    (hbounds : costs.IsBoundedBy bounds (model.vertexCount graph))
    (source : Vertex) (hsource : source ∈ model.interface.vertexSet graph) :
    exactCost (Interpreter.run model graph costs.control
        (BoundedOperational.visitedModel costs) source) ≤
      BoundedOperational.modelWorkBound bounds model graph := by
  let result := Operational.loopResult model graph (stackPopBound model graph) [source]
    (fun _ ↦ false)
  have hinvariants := Operational.loopResult_visited_and_nodup model graph
    (stackPopBound model graph) [source] (fun _ ↦ false)
  have hmembership := Operational.loopResult_queried_mem_vertices model graph
    (stackPopBound model graph) [source] (fun _ ↦ false)
    (by simpa using model.vertexEnumeration.complete hsource)
  have hsums := ResourceModel.nodup_sublist_length_and_sum_le result.queried
    (model.vertexEnumeration.vertices graph) (model.neighborCost graph)
    hinvariants.2.2 (model.vertexEnumeration.nodup graph) hmembership
  have hrun := BoundedOperational.exactCost_run_le model graph costs bounds hbounds source
  change exactCost (Interpreter.run model graph costs.control
      (BoundedOperational.visitedModel costs) source) ≤
    bounds.clearVisited + BoundedOperational.popCost bounds * stackPopBound model graph +
      bounds.checkStackEmpty + bounds.markVisited * result.queried.length +
        (result.queried.map fun vertex ↦ model.neighborCost graph vertex).sum at hrun
  have hqueryWork : bounds.markVisited * result.queried.length ≤
      bounds.markVisited * model.vertexCount graph :=
    Nat.mul_le_mul_left bounds.markVisited (by
      simpa [ResourceModel.vertexCount] using hsums.1)
  have hneighborSum :
      (result.queried.map fun vertex ↦ model.neighborCost graph vertex).sum ≤
        model.totalNeighborCost graph := hsums.2
  apply hrun.trans
  unfold BoundedOperational.modelWorkBound
  omega

/-- The previous concrete bound is the unit-cost specialization of the generic theorem. -/
theorem unitCost_le_modelWork {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (model : ResourceModel G Vertex) (graph : G) (source : Vertex)
    (hsource : source ∈ model.interface.vertexSet graph) :
    exactCost (Interpreter.run model graph GraphTraversal.ControlCostModel.unit
        GraphTraversal.VisitedModel.booleanTable source) ≤
      2 * model.vertexCount graph + 2 * model.adjacencyEntryCount graph +
        model.totalNeighborCost graph + 3 := by
  have hbound := exactCost_le_modelWork model graph
    (BoundedOperational.unitCostModel : BoundedOperational.CostModel Vertex)
    (BoundedOperational.unitCostBounds (model.vertexCount graph))
    (BoundedOperational.unitCostModel_isBoundedBy (model.vertexCount graph))
    source hsource
  change exactCost (Interpreter.run model graph GraphTraversal.ControlCostModel.unit
      GraphTraversal.VisitedModel.booleanTable source) ≤
    BoundedOperational.modelWorkBound
      (BoundedOperational.unitCostBounds (model.vertexCount graph)) model graph at hbound
  simp [BoundedOperational.modelWorkBound, BoundedOperational.unitCostBounds,
    BoundedOperational.popCost, stackPopBound] at hbound
  omega

/-- Adjacency-list DFS under arbitrary bounded primitive-operation costs. -/
theorem adjacencyList_exactCost_le {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (Γ : Interface G Vertex) (vertices : VertexEnumeration Γ) (neighbors : NeighborAccess Γ)
    (graph : G) (source : Vertex) (hsource : source ∈ Γ.vertexSet graph)
    (costs : BoundedOperational.CostModel Vertex) (bounds : BoundedOperational.CostBounds)
    (hbounds : costs.IsBoundedBy bounds
      ((ResourceModel.ofAdjacencyList Γ vertices neighbors).vertexCount graph))
    {m : Nat}
    (hentries : (ResourceModel.ofAdjacencyList Γ vertices neighbors).adjacencyEntryCount graph =
      2 * m) :
    exactCost (Interpreter.run (ResourceModel.ofAdjacencyList Γ vertices neighbors) graph
        costs.control (BoundedOperational.visitedModel costs) source) ≤
      bounds.clearVisited + BoundedOperational.popCost bounds * (2 * m + 1) +
        bounds.checkStackEmpty + bounds.markVisited *
          (ResourceModel.ofAdjacencyList Γ vertices neighbors).vertexCount graph + 2 * m := by
  simpa only [BoundedOperational.modelWorkBound, stackPopBound,
    ResourceModel.ofAdjacencyList_totalNeighborCost, hentries] using
    exactCost_le_modelWork (ResourceModel.ofAdjacencyList Γ vertices neighbors) graph
      costs bounds hbounds source hsource

/-- Adjacency-matrix DFS under arbitrary bounded primitive-operation costs. -/
theorem adjacencyMatrix_exactCost_le {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (Γ : Interface G Vertex) (vertices : VertexEnumeration Γ)
    (edge : G → Vertex → Vertex → Bool)
    (edge_iff : ∀ graph source target, edge graph source target = true ↔
      Γ.Adj graph source target)
    (graph : G) (source : Vertex) (hsource : source ∈ Γ.vertexSet graph)
    (costs : BoundedOperational.CostModel Vertex) (bounds : BoundedOperational.CostBounds)
    (hbounds : costs.IsBoundedBy bounds
      ((ResourceModel.ofAdjacencyMatrix Γ vertices edge edge_iff).vertexCount graph)) :
    let model := ResourceModel.ofAdjacencyMatrix Γ vertices edge edge_iff
    exactCost (Interpreter.run model graph costs.control
        (BoundedOperational.visitedModel costs) source) ≤
      bounds.clearVisited +
        BoundedOperational.popCost bounds *
          (model.vertexCount graph * model.vertexCount graph + 1) +
        bounds.checkStackEmpty + bounds.markVisited * model.vertexCount graph +
          model.vertexCount graph * model.vertexCount graph := by
  let model := ResourceModel.ofAdjacencyMatrix Γ vertices edge edge_iff
  have hbound := exactCost_le_modelWork model graph costs bounds hbounds source hsource
  unfold BoundedOperational.modelWorkBound stackPopBound at hbound
  have hpopEntries := Nat.mul_le_mul_left (BoundedOperational.popCost bounds)
    (Nat.add_le_add_right (ResourceModel.adjacencyEntryCount_le_square model graph) 1)
  have hqueries : model.totalNeighborCost graph =
      model.vertexCount graph * model.vertexCount graph :=
    ResourceModel.ofAdjacencyMatrix_totalNeighborCost Γ vertices edge edge_iff graph
  simp only [model] at hbound hpopEntries hqueries ⊢
  rw [hqueries] at hbound
  omega

/-- Unit-cost corollary for an undirected adjacency list. -/
theorem adjacencyList_unitCost_le {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (Γ : Interface G Vertex) (vertices : VertexEnumeration Γ) (neighbors : NeighborAccess Γ)
    (graph : G) (source : Vertex) (hsource : source ∈ Γ.vertexSet graph) {m : Nat}
    (hentries : (ResourceModel.ofAdjacencyList Γ vertices neighbors).adjacencyEntryCount graph =
      2 * m) :
    exactCost (Interpreter.run (ResourceModel.ofAdjacencyList Γ vertices neighbors) graph
        GraphTraversal.ControlCostModel.unit GraphTraversal.VisitedModel.booleanTable source) ≤
      2 * (ResourceModel.ofAdjacencyList Γ vertices neighbors).vertexCount graph +
        6 * m + 3 := by
  have hbound := unitCost_le_modelWork
    (ResourceModel.ofAdjacencyList Γ vertices neighbors) graph source hsource
  rw [ResourceModel.ofAdjacencyList_totalNeighborCost, hentries] at hbound
  omega

/-- Unit-cost corollary for an adjacency matrix. -/
theorem adjacencyMatrix_unitCost_le {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (Γ : Interface G Vertex) (vertices : VertexEnumeration Γ)
    (edge : G → Vertex → Vertex → Bool)
    (edge_iff : ∀ graph source target, edge graph source target = true ↔
      Γ.Adj graph source target)
    (graph : G) (source : Vertex) (hsource : source ∈ Γ.vertexSet graph) :
    let model := ResourceModel.ofAdjacencyMatrix Γ vertices edge edge_iff
    exactCost (Interpreter.run model graph GraphTraversal.ControlCostModel.unit
        GraphTraversal.VisitedModel.booleanTable source) ≤
      2 * model.vertexCount graph +
        3 * (model.vertexCount graph * model.vertexCount graph) + 3 := by
  let model := ResourceModel.ofAdjacencyMatrix Γ vertices edge edge_iff
  have hbound := unitCost_le_modelWork model graph source hsource
  have hentries := ResourceModel.adjacencyEntryCount_le_square model graph
  have hqueries : model.totalNeighborCost graph =
      model.vertexCount graph * model.vertexCount graph :=
    ResourceModel.ofAdjacencyMatrix_totalNeighborCost Γ vertices edge edge_iff graph
  simp only [model] at hbound hentries hqueries ⊢
  rw [hqueries] at hbound
  omega

/-- DFS accounting for an adjacency list: initialization plus work linear in its entries. -/
def adjacencyListTime (n m : Nat) : Nat :=
  GraphTraversal.TimeComplexity.adjacencyList n m

/-- DFS accounting for an adjacency matrix: initialization plus at most `n` row scans. -/
def adjacencyMatrixTime (n : Nat) : Nat :=
  GraphTraversal.TimeComplexity.adjacencyMatrix n

/-- The arbitrary-cost adjacency-list trace is bounded by textbook work and supplied constants. -/
theorem adjacencyList_exactCost_le_textbook
    {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (Γ : Interface G Vertex) (vertices : VertexEnumeration Γ) (neighbors : NeighborAccess Γ)
    (graph : G) (source : Vertex) (hsource : source ∈ Γ.vertexSet graph)
    (costs : BoundedOperational.CostModel Vertex) (bounds : BoundedOperational.CostBounds)
    (hbounds : costs.IsBoundedBy bounds
      ((ResourceModel.ofAdjacencyList Γ vertices neighbors).vertexCount graph))
    {m : Nat}
    (hentries : (ResourceModel.ofAdjacencyList Γ vertices neighbors).adjacencyEntryCount graph =
      2 * m) :
    exactCost (Interpreter.run (ResourceModel.ofAdjacencyList Γ vertices neighbors) graph
        costs.control (BoundedOperational.visitedModel costs) source) ≤
      bounds.clearVisited +
        BoundedOperational.textbookConstant bounds * adjacencyListTime
          ((ResourceModel.ofAdjacencyList Γ vertices neighbors).vertexCount graph) m +
        BoundedOperational.popCost bounds + bounds.checkStackEmpty := by
  have hbound := adjacencyList_exactCost_le Γ vertices neighbors graph source hsource
    costs bounds hbounds hentries
  simp [BoundedOperational.popCost, adjacencyListTime,
    GraphTraversal.TimeComplexity.adjacencyList, BoundedOperational.textbookConstant,
    Nat.add_mul, Nat.mul_add] at hbound ⊢
  omega

/-- Unit-cost specialization of the adjacency-list textbook bound. -/
theorem adjacencyList_unitCost_le_textbook
    {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (Γ : Interface G Vertex) (vertices : VertexEnumeration Γ) (neighbors : NeighborAccess Γ)
    (graph : G) (source : Vertex) (hsource : source ∈ Γ.vertexSet graph) {m : Nat}
    (hentries : (ResourceModel.ofAdjacencyList Γ vertices neighbors).adjacencyEntryCount graph =
      2 * m) :
    exactCost (Interpreter.run (ResourceModel.ofAdjacencyList Γ vertices neighbors) graph
        GraphTraversal.ControlCostModel.unit GraphTraversal.VisitedModel.booleanTable source) ≤
      3 * adjacencyListTime
        ((ResourceModel.ofAdjacencyList Γ vertices neighbors).vertexCount graph) m + 3 := by
  have hbound := adjacencyList_unitCost_le Γ vertices neighbors graph source hsource hentries
  unfold adjacencyListTime GraphTraversal.TimeComplexity.adjacencyList
  omega

/-- The arbitrary-cost matrix trace is bounded by textbook work and supplied constants. -/
theorem adjacencyMatrix_exactCost_le_textbook
    {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (Γ : Interface G Vertex) (vertices : VertexEnumeration Γ)
    (edge : G → Vertex → Vertex → Bool)
    (edge_iff : ∀ graph source target, edge graph source target = true ↔
      Γ.Adj graph source target)
    (graph : G) (source : Vertex) (hsource : source ∈ Γ.vertexSet graph)
    (costs : BoundedOperational.CostModel Vertex) (bounds : BoundedOperational.CostBounds)
    (hbounds : costs.IsBoundedBy bounds
      ((ResourceModel.ofAdjacencyMatrix Γ vertices edge edge_iff).vertexCount graph)) :
    let model := ResourceModel.ofAdjacencyMatrix Γ vertices edge edge_iff
    exactCost (Interpreter.run model graph costs.control
        (BoundedOperational.visitedModel costs) source) ≤
      bounds.clearVisited + BoundedOperational.textbookConstant bounds *
        adjacencyMatrixTime (model.vertexCount graph) +
          BoundedOperational.popCost bounds + bounds.checkStackEmpty := by
  have hbound := adjacencyMatrix_exactCost_le Γ vertices edge edge_iff graph source hsource
    costs bounds hbounds
  simp [BoundedOperational.popCost, adjacencyMatrixTime,
    GraphTraversal.TimeComplexity.adjacencyMatrix, BoundedOperational.textbookConstant,
    Nat.add_mul, Nat.mul_add] at hbound ⊢
  omega

/-- Unit-cost specialization of the adjacency-matrix textbook bound. -/
theorem adjacencyMatrix_unitCost_le_textbook
    {G : Type u} {Vertex : Type v} [DecidableEq Vertex]
    (Γ : Interface G Vertex) (vertices : VertexEnumeration Γ)
    (edge : G → Vertex → Vertex → Bool)
    (edge_iff : ∀ graph source target, edge graph source target = true ↔
      Γ.Adj graph source target)
    (graph : G) (source : Vertex) (hsource : source ∈ Γ.vertexSet graph) :
    let model := ResourceModel.ofAdjacencyMatrix Γ vertices edge edge_iff
    exactCost (Interpreter.run model graph GraphTraversal.ControlCostModel.unit
        GraphTraversal.VisitedModel.booleanTable source) ≤
      3 * adjacencyMatrixTime (model.vertexCount graph) + 3 := by
  have hbound := adjacencyMatrix_unitCost_le Γ vertices edge edge_iff graph source hsource
  unfold adjacencyMatrixTime GraphTraversal.TimeComplexity.adjacencyMatrix
  omega

/-- Kleinberg theorem (3.13): adjacency-list DFS runs in `O(m + n)` time. -/
theorem adjacencyListTime_isBigO :
    (fun nm : Nat × Nat ↦ (adjacencyListTime nm.1 nm.2 : Real)) =O[atTop]
      fun nm ↦ (nm.2 : Real) + nm.1 := by
  simpa only [adjacencyListTime] using GraphTraversal.TimeComplexity.adjacencyList_isBigO

/-- With an adjacency matrix, DFS runs in `O(n²)` time. -/
theorem adjacencyMatrixTime_isBigO :
    (fun n : Nat ↦ (adjacencyMatrixTime n : Real)) =O[atTop]
      fun n ↦ (n : Real) ^ 2 := by
  simpa only [adjacencyMatrixTime] using GraphTraversal.TimeComplexity.adjacencyMatrix_isBigO

/-- The adjacency-list and adjacency-matrix DFS bounds, packaged together. -/
theorem timeComplexities :
    ((fun nm : Nat × Nat ↦ (adjacencyListTime nm.1 nm.2 : Real)) =O[atTop]
      fun nm ↦ (nm.2 : Real) + nm.1) ∧
    ((fun n : Nat ↦ (adjacencyMatrixTime n : Real)) =O[atTop]
      fun n ↦ (n : Real) ^ 2) :=
  ⟨adjacencyListTime_isBigO, adjacencyMatrixTime_isBigO⟩

end KleinbergDFS
