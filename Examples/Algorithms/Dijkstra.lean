/-
Copyright (c) 2026 Lechen Wang, Daya Kumaran. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lechen Wang, Daya Kumaran
-/
import TextbookAlgorithms.KleinbergTardos.Chapter04.Dijkstra.Correctness
import TextbookAlgorithms.KleinbergTardos.Chapter04.Dijkstra.Complexity
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.NNRat.Order

/-!
# Algorithm example: Dijkstra

The fixtures instantiate one generic algorithm and semantic model at three weight types. Nat/ENat
provides the full executable regressions, NNRat/WithTop NNRat exercises a fractional edge, and
NNReal/ENNReal provides the proof-oriented Stage 2 specialization.
-/

namespace KleinbergDijkstraTest

open ResourceAware
open ResourceAware.Graph

set_option linter.style.nativeDecide false

/-- Finite toy input sufficient to package both unweighted and weighted graph capabilities. -/
structure Fixture (Weight : Type) (n m : Nat) where
  neighbors : Fin n → List (Fin n)
  rows : Fin n → List (OutgoingEdge (Fin m) (Fin n) Weight)
  neighbors_nodup : ∀ source, (neighbors source).Nodup
  rows_edge_nodup : ∀ source, ((rows source).map OutgoingEdge.edge).Nodup
  row_target_mem : ∀ source outgoing,
    outgoing ∈ rows source → outgoing.target ∈ neighbors source
  neighbor_has_row : ∀ source target,
    target ∈ neighbors source →
      ∃ outgoing ∈ rows source, outgoing.target = target
  edge_unique : ∀ {edge source target weight source' target' weight'},
    (⟨edge, target, weight⟩ : OutgoingEdge (Fin m) (Fin n) Weight) ∈ rows source →
    (⟨edge, target', weight'⟩ : OutgoingEdge (Fin m) (Fin n) Weight) ∈ rows source' →
      source = source' ∧ target = target' ∧ weight = weight'

namespace Fixture

def interface (fixture : Fixture Weight n m) : Interface Unit (Fin n) where
  vertexSet := fun _ => Set.univ
  Adj := fun _ source target => target ∈ fixture.neighbors source
  adj_source_mem := by simp
  adj_target_mem := by simp

def vertices (fixture : Fixture Weight n m) : VertexEnumeration fixture.interface where
  vertices := fun _ => List.finRange n
  nodup := fun _ => List.nodup_finRange n
  sound := by
    intro _ _ _
    exact Set.mem_univ _
  complete := by
    intro
    simp

def neighborAccess (fixture : Fixture Weight n m) : NeighborAccess fixture.interface where
  outNeighbors := fun _ source => fixture.neighbors source
  nodup := fun _ => fixture.neighbors_nodup
  sound := fun h => h
  complete := fun h => h

def baseModel (fixture : Fixture Weight n m) : ResourceModel Unit (Fin n) :=
  ResourceModel.ofAdjacencyList fixture.interface fixture.vertices fixture.neighborAccess

def edgeView (fixture : Fixture Weight n m) :
    WeightedEdgeView fixture.interface (Fin m) Weight where
  Arc := fun _ edge source target weight =>
    (⟨edge, target, weight⟩ : OutgoingEdge (Fin m) (Fin n) Weight) ∈ fixture.rows source
  arc_adj := fixture.row_target_mem _ _
  adj_has_arc := by
    intro _ source target adjacent
    rcases fixture.neighbor_has_row source target adjacent with
      ⟨outgoing, hrow, htarget⟩
    refine ⟨outgoing.edge, outgoing.weight, ?_⟩
    cases htarget
    exact hrow
  edge_unique := fixture.edge_unique

def weightedAccess (fixture : Fixture Weight n m) : WeightedNeighborAccess fixture.edgeView where
  outEdges := fun _ source => fixture.rows source
  edge_nodup := fun _ => fixture.rows_edge_nodup
  sound := fun h => h
  complete := fun h => h

def weightedModel (fixture : Fixture Weight n m) :
    WeightedResourceModel Unit (Fin n) (Fin m) Weight :=
  WeightedResourceModel.ofAdjacencyList fixture.baseModel fixture.edgeView fixture.weightedAccess

def index (fixture : Fixture Weight n m) :
    VertexIndex fixture.interface fixture.vertices () where
  toFun := fun vertex =>
    Fin.cast (by
      change n = (List.finRange n).length
      simp) vertex.val
  invFun := fun identifier =>
    ⟨Fin.cast (by
      change (List.finRange n).length = n
      simp) identifier, Set.mem_univ _⟩
  left_inv := by
    intro vertex
    apply Subtype.ext
    apply Fin.ext
    rfl
  right_inv := by
    intro identifier
    apply Fin.ext
    rfl

def source (fixture : Fixture Weight n m) (vertex : Fin n) :
    Fin (fixture.vertices.vertices ()).length :=
  fixture.index ⟨vertex, Set.mem_univ vertex⟩

end Fixture

def outgoing (edge : Fin m) (target : Fin n) (weight : Weight) :
    OutgoingEdge (Fin m) (Fin n) Weight :=
  ⟨edge, target, weight⟩

/-! ## Five-vertex repeated-improvement fixture -/

def improvementNeighbors : Fin 5 → List (Fin 5)
  | ⟨0, _⟩ => [1, 2, 3, 4]
  | ⟨1, _⟩ => [2, 3]
  | ⟨2, _⟩ => [3, 4]
  | ⟨3, _⟩ => [4, 2]
  | ⟨4, _⟩ => [1]

def improvementRows : Fin 5 → List (OutgoingEdge (Fin 11) (Fin 5) Nat)
  | ⟨0, _⟩ =>
      [outgoing 0 1 2, outgoing 1 2 9, outgoing 2 3 7, outgoing 3 4 20]
  | ⟨1, _⟩ => [outgoing 4 2 3, outgoing 5 3 10]
  | ⟨2, _⟩ => [outgoing 6 3 1, outgoing 7 4 7]
  | ⟨3, _⟩ => [outgoing 8 4 2, outgoing 9 2 4]
  | ⟨4, _⟩ => [outgoing 10 1 1]

def improvementModel : Fixture Nat 5 11 where
  neighbors := improvementNeighbors
  rows := improvementRows
  neighbors_nodup := by native_decide
  rows_edge_nodup := by native_decide
  row_target_mem := by native_decide
  neighbor_has_row := by native_decide
  edge_unique := by
    intro edge source target weight source' target' weight' h h'
    fin_cases source <;> fin_cases source' <;>
      simp [improvementRows, outgoing] at h h' ⊢ <;> aesop

def pureResult :=
  KleinbergDijkstra.Interpreter.eval improvementModel.weightedModel ()
    improvementModel.index (improvementModel.source 0)

def operationResult :=
  KleinbergDijkstra.Interpreter.runOperations improvementModel.weightedModel ()
    improvementModel.index (improvementModel.source 0)

def decompositionResult :=
  KleinbergDijkstra.Interpreter.runDecomposition improvementModel.weightedModel ()
    improvementModel.index (improvementModel.source 0)

def heapResult :=
  KleinbergDijkstra.Interpreter.runHeap improvementModel.weightedModel ()
    improvementModel.index (improvementModel.source 0)

def finalDistances := decompositionResult.ret.2.distances.toList
def finalPredecessors := decompositionResult.ret.2.predecessors.toList
def finalSettled := decompositionResult.ret.2.settled

/-! ## Parallel-edge, zero-weight, and equal-distance fixture -/

def parallelZeroNeighbors : Fin 3 → List (Fin 3)
  | ⟨0, _⟩ => [1, 2]
  | ⟨1, _⟩ => []
  | ⟨2, _⟩ => [1]

def parallelZeroRows : Fin 3 → List (OutgoingEdge (Fin 4) (Fin 3) Nat)
  | ⟨0, _⟩ => [outgoing 0 1 5, outgoing 1 1 2, outgoing 2 2 2]
  | ⟨1, _⟩ => []
  | ⟨2, _⟩ => [outgoing 3 1 0]

def parallelZeroModel : Fixture Nat 3 4 where
  neighbors := parallelZeroNeighbors
  rows := parallelZeroRows
  neighbors_nodup := by native_decide
  rows_edge_nodup := by native_decide
  row_target_mem := by native_decide
  neighbor_has_row := by native_decide
  edge_unique := by
    intro edge source target weight source' target' weight' h h'
    fin_cases source <;> fin_cases source' <;>
      simp [parallelZeroRows, outgoing] at h h' ⊢ <;> aesop

def parallelPureResult :=
  KleinbergDijkstra.Interpreter.eval parallelZeroModel.weightedModel ()
    parallelZeroModel.index (parallelZeroModel.source 0)

def parallelOperationResult :=
  KleinbergDijkstra.Interpreter.runOperations parallelZeroModel.weightedModel ()
    parallelZeroModel.index (parallelZeroModel.source 0)

def parallelDecompositionResult :=
  KleinbergDijkstra.Interpreter.runDecomposition parallelZeroModel.weightedModel ()
    parallelZeroModel.index (parallelZeroModel.source 0)

def parallelHeapResult :=
  KleinbergDijkstra.Interpreter.runHeap parallelZeroModel.weightedModel ()
    parallelZeroModel.index (parallelZeroModel.source 0)

/-! ## Single-vertex fixture -/

def singletonModel : Fixture Nat 1 0 where
  neighbors := fun _ => []
  rows := fun _ => []
  neighbors_nodup := by simp
  rows_edge_nodup := by simp
  row_target_mem := by simp
  neighbor_has_row := by simp
  edge_unique := by simp

def singletonPureResult :=
  KleinbergDijkstra.Interpreter.eval singletonModel.weightedModel ()
    singletonModel.index (singletonModel.source 0)

def singletonOperationResult :=
  KleinbergDijkstra.Interpreter.runOperations singletonModel.weightedModel ()
    singletonModel.index (singletonModel.source 0)

def singletonDecompositionResult :=
  KleinbergDijkstra.Interpreter.runDecomposition singletonModel.weightedModel ()
    singletonModel.index (singletonModel.source 0)

def singletonHeapResult :=
  KleinbergDijkstra.Interpreter.runHeap singletonModel.weightedModel ()
    singletonModel.index (singletonModel.source 0)

/-! ## Trace profiles -/

def countOperations (predicate : KleinbergDijkstra.Op n Edge Weight → Bool)
    (operations : List (KleinbergDijkstra.Op n Edge Weight)) : Nat :=
  (operations.filter predicate).length

def extractMinCount (operations : List (KleinbergDijkstra.Op n Edge Weight)) : Nat :=
  countOperations (fun operation =>
    match operation with
    | .extractMin => true
    | _ => false) operations

def outgoingEdgesCount (operations : List (KleinbergDijkstra.Op n Edge Weight)) : Nat :=
  countOperations (fun operation =>
    match operation with
    | .outgoingEdges _ => true
    | _ => false) operations

def relaxationCandidateCount (operations : List (KleinbergDijkstra.Op n Edge Weight)) : Nat :=
  countOperations (fun operation =>
    match operation with
    | .relaxationCandidate _ _ => true
    | _ => false) operations

def changeKeyCount (operations : List (KleinbergDijkstra.Op n Edge Weight)) : Nat :=
  countOperations (fun operation =>
    match operation with
    | .changeKey _ _ => true
    | _ => false) operations

def improvementOperations := ResourceAware.Program.operationTrace decompositionResult
def parallelOperations := ResourceAware.Program.operationTrace parallelDecompositionResult
def singletonOperations := ResourceAware.Program.operationTrace singletonDecompositionResult

-- Small executable snapshots; the assertions below remain the authoritative checks.
#eval finalDistances
#eval parallelDecompositionResult.ret.2.distances.toList

/-! ## Nat/ENat executable regressions -/

example : finalDistances = [0, 2, 5, 6, 8] := by native_decide
example : finalSettled.map Fin.val = [0, 1, 2, 3, 4] := by native_decide
example : decompositionResult.ret.2.heap.H.toList = [] := by native_decide
example : finalPredecessors[0]? = some none := by native_decide
example : (finalPredecessors[1]?.join.map fun predecessor => predecessor.edge) = some 0 := by
  native_decide
example : (finalPredecessors[2]?.join.map fun predecessor => predecessor.edge) = some 4 := by
  native_decide
example : (finalPredecessors[3]?.join.map fun predecessor => predecessor.edge) = some 6 := by
  native_decide
example : (finalPredecessors[4]?.join.map fun predecessor => predecessor.edge) = some 8 := by
  native_decide

example : extractMinCount improvementOperations = 5 := by native_decide
example : outgoingEdgesCount improvementOperations = 5 := by native_decide
example : relaxationCandidateCount improvementOperations = 11 := by native_decide
example : changeKeyCount improvementOperations = 8 := by native_decide
example : KleinbergDijkstra.exactCost decompositionResult = 56 := by native_decide
example : KleinbergDijkstra.exactCost heapResult = 83 := by native_decide

/-- The executable fixture instantiates the proved exact decomposition in claim (4.15). -/
example :
    let model := improvementModel.weightedModel
    let run := KleinbergDijkstra.Interpreter.runDecomposition model ()
      improvementModel.index (improvementModel.source 0)
    let m := model.directedEdgeOccurrenceCount ()
    let n := improvementModel.vertices.vertices () |>.length
    KleinbergDijkstra.Complexity.operationProfile
        (KleinbergDijkstra.Complexity.outgoingRowWorkCharge
          model () improvementModel.index) run = m ∧
      KleinbergDijkstra.Complexity.operationProfile
        KleinbergDijkstra.Complexity.relaxationCandidateCharge run = m ∧
      KleinbergDijkstra.Complexity.operationProfile
          (KleinbergDijkstra.Complexity.outgoingRowWorkCharge
            model () improvementModel.index) run +
          KleinbergDijkstra.Complexity.operationProfile
            KleinbergDijkstra.Complexity.relaxationCandidateCharge run = 2 * m ∧
      KleinbergDijkstra.Complexity.operationProfile
        KleinbergDijkstra.Complexity.extractMinCharge run = n ∧
      KleinbergDijkstra.Complexity.operationProfile
        KleinbergDijkstra.Complexity.changeKeyCharge run ≤ m :=
  KleinbergDijkstra.Complexity.claim_4_15_adjacencyList
    improvementModel.baseModel improvementModel.edgeView improvementModel.weightedAccess ()
    improvementModel.index (improvementModel.source 0)

/-- The same fixture instantiates the actual-run heap upper bound. -/
example :
    let model := improvementModel.weightedModel
    let n := improvementModel.vertices.vertices () |>.length
    let m := model.directedEdgeOccurrenceCount ()
    KleinbergDijkstra.Complexity.heapExactCost
        (KleinbergDijkstra.Interpreter.runHeap model ()
          improvementModel.index (improvementModel.source 0)) ≤
      KleinbergDijkstra.Complexity.heapCostUpperBound n m :=
  KleinbergDijkstra.Complexity.claim_4_15_heap_exact_bound
    improvementModel.baseModel improvementModel.edgeView improvementModel.weightedAccess ()
    improvementModel.index (improvementModel.source 0)

example : operationResult.ret.2.distances = pureResult.2.distances := by native_decide
example : decompositionResult.ret.2.distances = pureResult.2.distances := by native_decide
example : heapResult.ret.2.distances = pureResult.2.distances := by native_decide
example : operationResult.ret.2.predecessors = pureResult.2.predecessors := by native_decide
example : decompositionResult.ret.2.settled = pureResult.2.settled := by native_decide
example : heapResult.ret.2.heap.H = pureResult.2.heap.H := by native_decide
example : operationResult.ret = pureResult :=
  KleinbergDijkstra.Interpreter.runOperations_ret
    improvementModel.weightedModel () improvementModel.index
      (improvementModel.source 0)
example :
    TraceM.events operationResult =
      ResourceAware.Program.operationTrace decompositionResult :=
  KleinbergDijkstra.Interpreter.events_runOperations_eq_operationTrace_runDecomposition
    improvementModel.weightedModel () improvementModel.index
      (improvementModel.source 0)
example :
    ResourceAware.Program.operationTrace decompositionResult =
      ResourceAware.Program.operationTrace heapResult :=
  KleinbergDijkstra.Interpreter.operationTrace_runDecomposition_eq_runHeap
    improvementModel.weightedModel () improvementModel.index
      (improvementModel.source 0)

example : parallelDecompositionResult.ret.2.distances.toList = [0, 2, 2] := by
  native_decide
example :
    (parallelDecompositionResult.ret.2.predecessors.toList[1]?.join.map
      fun predecessor => predecessor.edge) = some 1 := by
  native_decide
example : extractMinCount parallelOperations = 3 := by native_decide
example : outgoingEdgesCount parallelOperations = 3 := by native_decide
example : relaxationCandidateCount parallelOperations = 4 := by native_decide
example : changeKeyCount parallelOperations = 3 := by native_decide
example : KleinbergDijkstra.exactCost parallelDecompositionResult = 27 := by native_decide
example : KleinbergDijkstra.exactCost parallelHeapResult = 36 := by native_decide
example : parallelOperationResult.ret = parallelPureResult :=
  KleinbergDijkstra.Interpreter.runOperations_ret
    parallelZeroModel.weightedModel () parallelZeroModel.index
      (parallelZeroModel.source 0)
example : parallelDecompositionResult.ret = parallelPureResult :=
  KleinbergDijkstra.Interpreter.runDecomposition_ret
    parallelZeroModel.weightedModel () parallelZeroModel.index
      (parallelZeroModel.source 0)
example : parallelHeapResult.ret = parallelPureResult :=
  KleinbergDijkstra.Interpreter.runHeap_ret
    parallelZeroModel.weightedModel () parallelZeroModel.index
      (parallelZeroModel.source 0)
example :
    TraceM.events parallelOperationResult =
      ResourceAware.Program.operationTrace parallelDecompositionResult :=
  KleinbergDijkstra.Interpreter.events_runOperations_eq_operationTrace_runDecomposition
    parallelZeroModel.weightedModel () parallelZeroModel.index
      (parallelZeroModel.source 0)
example :
    ResourceAware.Program.operationTrace parallelDecompositionResult =
      ResourceAware.Program.operationTrace parallelHeapResult :=
  KleinbergDijkstra.Interpreter.operationTrace_runDecomposition_eq_runHeap
    parallelZeroModel.weightedModel () parallelZeroModel.index
      (parallelZeroModel.source 0)

example : singletonDecompositionResult.ret.2.distances.toList = [0] := by native_decide
example : singletonDecompositionResult.ret.2.predecessors.toList = [none] := by native_decide
example : singletonDecompositionResult.ret.2.settled.map Fin.val = [0] := by native_decide
example : singletonDecompositionResult.ret.2.heap.H.toList = [] := by native_decide
example : extractMinCount singletonOperations = 1 := by native_decide
example : outgoingEdgesCount singletonOperations = 1 := by native_decide
example : relaxationCandidateCount singletonOperations = 0 := by native_decide
example : changeKeyCount singletonOperations = 0 := by native_decide
example : KleinbergDijkstra.exactCost singletonDecompositionResult = 6 := by native_decide
example : KleinbergDijkstra.exactCost singletonHeapResult = 7 := by native_decide
example : singletonOperationResult.ret = singletonPureResult :=
  KleinbergDijkstra.Interpreter.runOperations_ret
    singletonModel.weightedModel () singletonModel.index (singletonModel.source 0)
example : singletonDecompositionResult.ret = singletonPureResult :=
  KleinbergDijkstra.Interpreter.runDecomposition_ret
    singletonModel.weightedModel () singletonModel.index (singletonModel.source 0)
example : singletonHeapResult.ret = singletonPureResult :=
  KleinbergDijkstra.Interpreter.runHeap_ret
    singletonModel.weightedModel () singletonModel.index (singletonModel.source 0)
example :
    TraceM.events singletonOperationResult =
      ResourceAware.Program.operationTrace singletonDecompositionResult :=
  KleinbergDijkstra.Interpreter.events_runOperations_eq_operationTrace_runDecomposition
    singletonModel.weightedModel () singletonModel.index (singletonModel.source 0)
example :
    ResourceAware.Program.operationTrace singletonDecompositionResult =
      ResourceAware.Program.operationTrace singletonHeapResult :=
  KleinbergDijkstra.Interpreter.operationTrace_runDecomposition_eq_runHeap
    singletonModel.weightedModel () singletonModel.index (singletonModel.source 0)

/-! ## NNRat/WithTop NNRat executable fractional fixture -/

def halfNNRat : NNRat := 1 / 2

def fractionalNeighbors : Fin 2 → List (Fin 2)
  | ⟨0, _⟩ => [1]
  | ⟨1, _⟩ => []

def fractionalRows : Fin 2 → List (OutgoingEdge (Fin 1) (Fin 2) NNRat)
  | ⟨0, _⟩ => [outgoing 0 1 halfNNRat]
  | ⟨1, _⟩ => []

def fractionalModel : Fixture NNRat 2 1 where
  neighbors := fractionalNeighbors
  rows := fractionalRows
  neighbors_nodup := by native_decide
  rows_edge_nodup := by native_decide
  row_target_mem := by native_decide
  neighbor_has_row := by native_decide
  edge_unique := by
    intro edge source target weight source' target' weight' h h'
    fin_cases source <;> fin_cases source' <;>
      simp [fractionalRows, outgoing] at h h' ⊢; aesop

def fractionalResult :=
  KleinbergDijkstra.Interpreter.eval fractionalModel.weightedModel ()
    fractionalModel.index (fractionalModel.source 0)

#eval fractionalResult.2.distances.toList ==
  [0, (halfNNRat : WithTop NNRat)]

example :
    fractionalResult.2.distances.toList =
      [0, (halfNNRat : WithTop NNRat)] := by
  native_decide

/-! ## NNReal/ENNReal proof-oriented Stage 2 smoke tests -/

section NNRealSmokeTests

noncomputable section

/-- A genuinely non-integral edge weight accepted by the Stage 2 input domain. -/
def halfWeight : NNReal :=
  NNReal.mk ((1 : Real) / 2) (by norm_num)

def fractionalOutgoing : OutgoingEdge (Fin 1) (Fin 2) NNReal :=
  outgoing 0 1 halfWeight

example : fractionalOutgoing.weight = halfWeight := rfl

/-- Two finite half-weight path segments add to one in the stored ENNReal distance domain. -/
example : (halfWeight : ENNReal) + halfWeight = 1 := by
  have h : halfWeight + halfWeight = (1 : NNReal) := by
    ext
    norm_num [halfWeight, NNReal.coe_add]
  simpa only [ENNReal.coe_add, ENNReal.coe_one] using
    congrArg ENNReal.ofNNReal h

/-- An unreachable source distance remains unreachable after extending it by a finite edge. -/
example : (⊤ : ENNReal) + halfWeight = ⊤ := by
  simp

def nnrealRows : Fin 2 → List (OutgoingEdge (Fin 1) (Fin 2) NNReal)
  | ⟨0, _⟩ => [fractionalOutgoing]
  | ⟨1, _⟩ => []

def nnrealModel : Fixture NNReal 2 1 where
  neighbors := fractionalNeighbors
  rows := nnrealRows
  neighbors_nodup := by native_decide
  rows_edge_nodup := by
    intro source
    fin_cases source <;> simp [nnrealRows]
  row_target_mem := by
    intro source outgoingEdge h
    fin_cases source
    · simp [nnrealRows] at h
      subst outgoingEdge
      simp [fractionalOutgoing, fractionalNeighbors, outgoing]
    · simp [nnrealRows] at h
  neighbor_has_row := by
    intro source target
    fin_cases source <;> fin_cases target <;>
      simp [nnrealRows, fractionalOutgoing, fractionalNeighbors, outgoing]
  edge_unique := by
    intro edge source target weight source' target' weight' h h'
    fin_cases source <;> fin_cases source' <;>
      simp [nnrealRows, fractionalOutgoing, outgoing] at h h' ⊢; aesop

def nnrealPureResult :=
  KleinbergDijkstra.Interpreter.eval nnrealModel.weightedModel ()
    nnrealModel.index (nnrealModel.source 0)

def nnrealOperationResult :=
  KleinbergDijkstra.Interpreter.runOperations nnrealModel.weightedModel ()
    nnrealModel.index (nnrealModel.source 0)

def nnrealDecompositionResult :=
  KleinbergDijkstra.Interpreter.runDecomposition nnrealModel.weightedModel ()
    nnrealModel.index (nnrealModel.source 0)

def nnrealHeapResult :=
  KleinbergDijkstra.Interpreter.runHeap nnrealModel.weightedModel ()
    nnrealModel.index (nnrealModel.source 0)

example : nnrealDecompositionResult.ret = nnrealPureResult :=
  KleinbergDijkstra.Interpreter.runDecomposition_ret
    nnrealModel.weightedModel () nnrealModel.index (nnrealModel.source 0)

example : nnrealHeapResult.ret = nnrealPureResult :=
  KleinbergDijkstra.Interpreter.runHeap_ret
    nnrealModel.weightedModel () nnrealModel.index (nnrealModel.source 0)

example : nnrealOperationResult.ret = nnrealPureResult :=
  KleinbergDijkstra.Interpreter.runOperations_ret
    nnrealModel.weightedModel () nnrealModel.index (nnrealModel.source 0)

example :
    TraceM.events nnrealOperationResult =
      ResourceAware.Program.operationTrace nnrealDecompositionResult :=
  KleinbergDijkstra.Interpreter.events_runOperations_eq_operationTrace_runDecomposition
    nnrealModel.weightedModel () nnrealModel.index (nnrealModel.source 0)

end

end NNRealSmokeTests

/-! ## Correctness theorem weight instantiations -/

section CorrectnessInstantiationTests

universe u v w

variable {G : Type u} {V : Type v} {Edge : Type w}

example
    (model : WeightedResourceModel G V Edge Nat) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length)
    (hallReachable : ∀ name,
      Reachable model.base.interface graph (index.decode source).val
        (index.decode name).val) :
    let final := (KleinbergDijkstra.Interpreter.eval model graph index source).2
    ∀ name, name ∈ final.settled →
      KleinbergDijkstra.Correctness.PredecessorReconstructedShortest
        model graph index source name final :=
  KleinbergDijkstra.Correctness.claim_4_14 model graph index source hallReachable

example
    (model : WeightedResourceModel G V Edge NNRat) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length)
    (hallReachable : ∀ name,
      Reachable model.base.interface graph (index.decode source).val
        (index.decode name).val) :
    let final := (KleinbergDijkstra.Interpreter.eval model graph index source).2
    ∀ name, name ∈ final.settled →
      KleinbergDijkstra.Correctness.PredecessorReconstructedShortest
        model graph index source name final :=
  KleinbergDijkstra.Correctness.claim_4_14 model graph index source hallReachable

example
    (model : WeightedResourceModel G V Edge NNReal) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length)
    (hallReachable : ∀ name,
      Reachable model.base.interface graph (index.decode source).val
        (index.decode name).val) :
    let final := (KleinbergDijkstra.Interpreter.eval model graph index source).2
    ∀ name, name ∈ final.settled →
      KleinbergDijkstra.Correctness.PredecessorReconstructedShortest
        model graph index source name final :=
  KleinbergDijkstra.Correctness.claim_4_14 model graph index source hallReachable

end CorrectnessInstantiationTests

end KleinbergDijkstraTest
