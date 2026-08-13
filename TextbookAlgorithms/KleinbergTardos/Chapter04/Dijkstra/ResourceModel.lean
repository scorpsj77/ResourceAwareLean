/-
Copyright (c) 2026 Daya Kumaran. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daya Kumaran
-/
import TextbookAlgorithms.KleinbergTardos.Chapter04.Dijkstra.Algorithm
import ResourceAware.Foundations.Graph.ResourceModel
import ResourceAware.Foundations.PriorityQueue.ResourceModel
import ResourceAware.Program.Cost

/-!
# Semantic and resource models for Kleinberg--Tardos Dijkstra

This module interprets the abstract requests using a graph-owned dense vertex index, the named
heap from the Chapter 2 foundation, and fixed-length result arrays. Semantics are independent of
the two source-level cost profiles.

`initializationUnitCost` charges aggregate setup as `4n + 1`. `initializationHeapCost` replaces
the unit insertion component by the exact repeated-insertion heap profile. Outgoing-row events
use the selected weighted graph model, candidate inspection costs one, and heap events aggregate
their internal reads, writes, comparisons, swaps, and repairs.
-/

universe u v w x

namespace KleinbergDijkstra

open ResourceAware
open ResourceAware.Graph

namespace Model

/-- Semantic state: active heap, persistent result tables, and extraction order. -/
structure State (n : Nat) (Edge : Type w) (Weight : Type x) where
  heap : KleinbergPriorityQueue.Heap n (Distance Weight)
  distances : Array (Distance Weight)
  predecessors : Array (Option (Predecessor n Edge Weight))
  settled : List (Fin n)
  distances_size : distances.size = n
  predecessors_size : predecessors.size = n

/-- Empty pre-initialization state used by generic interpreters. -/
def initialState (n : Nat) (Edge : Type w) (Weight : Type x) [Zero Weight] :
    State n Edge Weight where
  heap := KleinbergPriorityQueue.Heap.startHeap n (Distance Weight)
  distances := Array.replicate n ⊤
  predecessors := Array.replicate n none
  settled := []
  distances_size := by simp
  predecessors_size := by simp

/-- Initial heap entries: source key zero and every other key infinity. -/
def initialEntries (Weight : Type x) [Zero Weight] (n : Nat) (source : Fin n) :
    List (KleinbergPriorityQueue.Entry n (Distance Weight)) :=
  (List.finRange n).map fun name =>
    { name
      key := if name = source then 0 else ⊤ }

/-- Execute the aggregate initialization request. -/
def initializeState (n : Nat) (Edge : Type w) (Weight : Type x)
    [AddCommMonoid Weight] [LinearOrder Weight] (source : Fin n) :
    Bool × State n Edge Weight :=
  let inserted :=
    (KleinbergPriorityQueue.Heap.startHeap n (Distance Weight)).insertAll
      (initialEntries Weight n source)
  let distances :=
    (Array.replicate n (⊤ : Distance Weight)).setIfInBounds source.val 0
  (inserted.2,
    { heap := inserted.1
      distances
      predecessors := Array.replicate n none
      settled := []
      distances_size := by simp [distances]
      predecessors_size := by simp })

/-- Encode one selected weighted outgoing row without changing its occurrence order. -/
def indexedOutgoingEdges {G : Type u} {V : Type v} {Edge : Type w} {Weight : Type x}
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length) :
    List (IndexedOutgoingEdge
      (model.base.vertexEnumeration.vertices graph).length Edge Weight) :=
  let decoded := index.decode source
  let row := model.weightedNeighborAccess.outEdges graph decoded.val
  row.attach.map fun outgoing =>
    let target : GraphVertex model.base.interface graph :=
      ⟨outgoing.val.target,
        by
          have arc := model.weightedNeighborAccess.sound
            (g := graph) (source := decoded.val) outgoing.property
          exact model.edgeView.target_mem arc⟩
    { edge := outgoing.val.edge
      target := index.encode target
      weight := outgoing.val.weight }

/-- Representation-independent semantics assembled from a weighted graph model and dense index. -/
def semantics {G : Type u} {V : Type v} {Edge : Type w} {Weight : Type x}
    [AddCommMonoid Weight] [LinearOrder Weight] [CanonicallyOrderedAdd Weight]
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph) :
    ResourceAware.Program.Semantics
      (Signature (model.base.vertexEnumeration.vertices graph).length Edge Weight)
      (State (model.base.vertexEnumeration.vertices graph).length Edge Weight) where
  initialState :=
    Model.initialState (model.base.vertexEnumeration.vertices graph).length Edge Weight
  step := fun operation state =>
    match operation with
    | .initialize source =>
        let initialized := initializeState _ Edge Weight source
        (ULift.up initialized.1, initialized.2)
    | .extractMin =>
        let extracted := state.heap.extractMin
        let settled :=
          match extracted.2 with
          | none => state.settled
          | some entry => state.settled ++ [entry.name]
        (ULift.up extracted.2, { state with heap := extracted.1, settled })
    | .outgoingEdges source =>
        (indexedOutgoingEdges model graph index source, state)
    | .relaxationCandidate sourceDistance outgoing =>
        let candidate := sourceDistance + (outgoing.weight : Distance Weight)
        let result :=
          match state.heap.contents outgoing.target with
          | none => none
          | some current => if candidate < current then some candidate else none
        (ULift.up result, state)
    | .changeKey predecessor candidate =>
        let changed := state.heap.changeKey predecessor.target candidate
        if changed.2 then
          let distances :=
            state.distances.setIfInBounds predecessor.target.val candidate
          let predecessors :=
            state.predecessors.setIfInBounds predecessor.target.val (some predecessor)
          (ULift.up true,
            { heap := changed.1
              distances
              predecessors
              settled := state.settled
              distances_size := by simpa [distances] using state.distances_size
              predecessors_size := by
                simpa [predecessors] using state.predecessors_size })
        else
          (ULift.up false, state)

end Model

/-! ## Exact source-level cost choices -/

/-- Unit-profile setup: heap start, `n` inserts, two `n`-cell arrays, and source write. -/
def initializationUnitCost (n : Nat) : Nat :=
  4 * n + 1

/--
Heap-profile setup: two result arrays and source write, plus reserved heap setup and the exact
cost of the repository's repeated insertion implementation.
-/
def initializationHeapCost (n : Nat) : Nat :=
  3 * n + 1 + KleinbergPriorityQueue.repeatedInsertionCost 0 n

namespace Model

/-- Claim (4.15) decomposition with unit aggregate priority-queue operations. -/
def decompositionCostModel {G : Type u} {V : Type v} {Edge : Type w} {Weight : Type x}
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph) :
    ResourceAware.Program.CostModel
      (Signature (model.base.vertexEnumeration.vertices graph).length Edge Weight)
      (State (model.base.vertexEnumeration.vertices graph).length Edge Weight) Nat where
  measure := fun operation _ _ _ =>
    match operation with
    | .initialize _ =>
        initializationUnitCost (model.base.vertexEnumeration.vertices graph).length
    | .extractMin => 1
    | .outgoingEdges source =>
        model.weightedNeighborCost graph (index.decode source).val
    | .relaxationCandidate _ _ => 1
    | .changeKey _ _ => 1

/-- Logarithmic heap profile with the same graph and candidate-inspection costs. -/
def heapCostModel {G : Type u} {V : Type v} {Edge : Type w} {Weight : Type x}
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph) :
    ResourceAware.Program.CostModel
      (Signature (model.base.vertexEnumeration.vertices graph).length Edge Weight)
      (State (model.base.vertexEnumeration.vertices graph).length Edge Weight) Nat where
  measure := fun operation before _ _ =>
    match operation with
    | .initialize _ =>
        initializationHeapCost (model.base.vertexEnumeration.vertices graph).length
    | .extractMin =>
        KleinbergPriorityQueue.Operation.cost (.extractMin before.heap.size)
    | .outgoingEdges source =>
        model.weightedNeighborCost graph (index.decode source).val
    | .relaxationCandidate _ _ => 1
    | .changeKey _ _ =>
        KleinbergPriorityQueue.Operation.cost (.changeKey before.heap.size)

@[simp] theorem decompositionCostModel_initialize {G : Type u} {V : Type v}
    {Edge : Type w} {Weight : Type x}
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length) (before after)
    (response : Response (Edge := Edge) (Weight := Weight) (Op.initialize source)) :
    (decompositionCostModel model graph index).measure (.initialize source)
      before response after =
        initializationUnitCost (model.base.vertexEnumeration.vertices graph).length := by
  simp [decompositionCostModel]

@[simp] theorem heapCostModel_initialize {G : Type u} {V : Type v}
    {Edge : Type w} {Weight : Type x}
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length) (before after)
    (response : Response (Edge := Edge) (Weight := Weight) (Op.initialize source)) :
    (heapCostModel model graph index).measure (.initialize source)
      before response after =
        initializationHeapCost (model.base.vertexEnumeration.vertices graph).length := by
  simp [heapCostModel]

@[simp] theorem decompositionCostModel_relaxationCandidate
    {G : Type u} {V : Type v} {Edge : Type w} {Weight : Type x}
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (distance : Distance Weight)
    (outgoing : IndexedOutgoingEdge
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (before after)
    (response : Response (Weight := Weight) (Op.relaxationCandidate distance outgoing)) :
    (decompositionCostModel model graph index).measure
      (.relaxationCandidate distance outgoing) before response after = 1 := by
  simp [decompositionCostModel]

@[simp] theorem heapCostModel_relaxationCandidate
    {G : Type u} {V : Type v} {Edge : Type w} {Weight : Type x}
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (distance : Distance Weight)
    (outgoing : IndexedOutgoingEdge
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (before after)
    (response : Response (Weight := Weight) (Op.relaxationCandidate distance outgoing)) :
    (heapCostModel model graph index).measure
      (.relaxationCandidate distance outgoing) before response after = 1 := by
  simp [heapCostModel]

end Model

/-! ## Thin generic runners -/

abbrev Event (n : Nat) (Edge : Type w) (Weight : Type x) :=
  ResourceAware.Program.Event (Op n Edge Weight) Nat

namespace Interpreter

variable {G : Type u} {V : Type v} {Edge : Type w} {Weight : Type x}
variable [AddCommMonoid Weight] [LinearOrder Weight] [CanonicallyOrderedAdd Weight]

/-- Pure semantic execution with vertex-count fuel derived by `dijkstra`. -/
def eval (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length) :=
  ResourceAware.Program.Semantics.eval (Model.semantics model graph index)
    (dijkstra (model.base.vertexEnumeration.vertices graph).length source)

/-- Execute while retaining the ordered operations and erasing measurements. -/
def runOperations (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length) :=
  ResourceAware.Program.runOperations (Model.semantics model graph index)
    (dijkstra (model.base.vertexEnumeration.vertices graph).length source)

/-- Execute under the unit-profile decomposition of claim (4.15). -/
def runDecomposition (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length) :=
  ResourceAware.Program.run (Model.semantics model graph index)
    (Model.decompositionCostModel model graph index)
    (dijkstra (model.base.vertexEnumeration.vertices graph).length source)

/-- Execute under the repeated-insertion and logarithmic heap profile. -/
def runHeap (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length) :=
  ResourceAware.Program.run (Model.semantics model graph index)
    (Model.heapCostModel model graph index)
    (dijkstra (model.base.vertexEnumeration.vertices graph).length source)

/-- Operation-only instrumentation preserves the pure semantic result and final state. -/
@[simp] theorem runOperations_ret (model : WeightedResourceModel G V Edge Weight)
    (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length) :
    (runOperations model graph index source).ret = (eval model graph index source) := by
  have h := ResourceAware.Program.mapEvents_runFrom
    (Model.semantics model graph index)
    (Model.decompositionCostModel model graph index)
    (dijkstra (model.base.vertexEnumeration.vertices graph).length source)
    (Model.semantics model graph index).initialState
  calc
    (runOperations model graph index source).ret =
      (TraceM.mapEvents ResourceAware.Program.Event.erase
          (runDecomposition model graph index source)).ret :=
      (congrArg (fun computation ↦ computation.ret) h).symm
    _ = (runDecomposition model graph index source).ret := rfl
    _ = (eval model graph index source) := by
      apply ResourceAware.Program.runFrom_ret

/-- Unit-profile instrumentation preserves the pure semantic result and final state. -/
@[simp] theorem runDecomposition_ret (model : WeightedResourceModel G V Edge Weight)
    (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length) :
    (runDecomposition model graph index source).ret = (eval model graph index source) := by
  apply ResourceAware.Program.runFrom_ret

/-- Heap-profile instrumentation preserves the pure semantic result and final state. -/
@[simp] theorem runHeap_ret (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length) :
    (runHeap model graph index source).ret = (eval model graph index source) := by
  apply ResourceAware.Program.runFrom_ret

/-- Erasing unit-profile measurements yields the operation-only execution order. -/
theorem events_runOperations_eq_operationTrace_runDecomposition
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length) :
    TraceM.events (runOperations model graph index source) =
      ResourceAware.Program.operationTrace
        (runDecomposition model graph index source) := by
  have h := ResourceAware.Program.mapEvents_runFrom
    (Model.semantics model graph index)
    (Model.decompositionCostModel model graph index)
    (dijkstra (model.base.vertexEnumeration.vertices graph).length source)
    (Model.semantics model graph index).initialState
  exact (congrArg TraceM.events h).symm

/-- Changing only the cost backend preserves the complete erased operation trace. -/
theorem operationTrace_runDecomposition_eq_runHeap
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length) :
    ResourceAware.Program.operationTrace
        (runDecomposition model graph index source) =
      ResourceAware.Program.operationTrace (runHeap model graph index source) := by
  have h := ResourceAware.Program.mapEvents_runFrom_eq
    (Model.semantics model graph index)
    (Model.decompositionCostModel model graph index)
    (Model.heapCostModel model graph index)
    (dijkstra (model.base.vertexEnumeration.vertices graph).length source)
    (Model.semantics model graph index).initialState
  exact congrArg TraceM.events h

end Interpreter

/-- Sum the ordered event measurements of a completed Dijkstra run. -/
def exactCost (computation : TraceM (Event n Edge Weight) α) : Nat :=
  ResourceAware.Program.exactCost computation

/-! ## Static graph and algorithm working space -/

/-- Source-level storage components, separated from the selected graph representation. -/
structure SpaceUsage where
  graphStorage : Nat
  heapArray : Nat
  positionTable : Nat
  distanceTable : Nat
  predecessorTable : Nat
  settledList : Nat
deriving Repr, DecidableEq

namespace SpaceUsage

/-- Working storage excludes the static graph representation. -/
def working (usage : SpaceUsage) : Nat :=
  usage.heapArray + usage.positionTable + usage.distanceTable +
    usage.predecessorTable + usage.settledList

def total (usage : SpaceUsage) : Nat :=
  usage.graphStorage + usage.working

end SpaceUsage

/-- Reserve one cell per vertex for each heap/table/list component. -/
def spaceUsage {G : Type u} {V : Type v} {Edge : Type w} {Weight : Type x}
    (model : WeightedResourceModel G V Edge Weight) (graph : G) : SpaceUsage :=
  let n := model.base.vertexCount graph
  { graphStorage := model.base.graphSpace graph
    heapArray := n
    positionTable := n
    distanceTable := n
    predecessorTable := n
    settledList := n }

end KleinbergDijkstra
