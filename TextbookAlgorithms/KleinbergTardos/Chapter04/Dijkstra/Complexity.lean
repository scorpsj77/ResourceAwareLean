/-
Copyright (c) 2026 Dayakumaran Ramalingam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dayakumaran Ramalingam
-/
import TextbookAlgorithms.KleinbergTardos.Chapter04.Dijkstra.Correctness
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Tactic

/-!
# Complexity of Kleinberg--Tardos Dijkstra

This file proves the exact operation decomposition in claim (4.15) before lifting the
logarithmic named-heap profile to the textbook asymptotic corollary.
-/

universe u v w x

namespace KleinbergDijkstra

open ResourceAware
open ResourceAware.Graph
open Filter Asymptotics

namespace Complexity

variable {G : Type u} {V : Type v} {Edge : Type w} {Weight : Type x}
variable [AddCommMonoid Weight] [LinearOrder Weight] [CanonicallyOrderedAdd Weight]

/-- Indicator for priority-queue extraction requests. -/
def extractMinCharge : (Signature n Edge Weight).A → Nat
  | .extractMin => 1
  | _ => 0

/-- Indicator for weighted outgoing-row requests. -/
def outgoingEdgesCharge : (Signature n Edge Weight).A → Nat
  | .outgoingEdges _ => 1
  | _ => 0

/-- Charge one outgoing-row request by the selected graph representation's row-query cost. -/
def outgoingRowWorkCharge
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph) :
    (Signature (model.base.vertexEnumeration.vertices graph).length Edge Weight).A → Nat
  | .outgoingEdges source =>
      model.weightedNeighborCost graph (index.decode source).val
  | _ => 0

/-- Indicator for one inspected edge occurrence. -/
def relaxationCandidateCharge : (Signature n Edge Weight).A → Nat
  | .relaxationCandidate _ _ => 1
  | _ => 0

/-- Indicator for successful strict-improvement requests. -/
def changeKeyCharge : (Signature n Edge Weight).A → Nat
  | .changeKey _ _ => 1
  | _ => 0

/-- Monotonicity of the closed heap-height charge used by the Chapter 2 backend. -/
theorem logarithmicCost_mono {left right : Nat} (h : left ≤ right) :
    KleinbergPriorityQueue.logarithmicCost left ≤
      KleinbergPriorityQueue.logarithmicCost right := by
  unfold KleinbergPriorityQueue.logarithmicCost
  apply Nat.add_le_add_left
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  exact Nat.log_mono_right (Nat.add_le_add_right h 1)

/-- The exact repeated-insertion setup cost is bounded by `count` final-height charges. -/
theorem repeatedInsertionCost_le (initialSize count : Nat) :
    KleinbergPriorityQueue.repeatedInsertionCost initialSize count ≤
      count * KleinbergPriorityQueue.logarithmicCost (initialSize + count) := by
  induction count generalizing initialSize with
  | zero => simp [KleinbergPriorityQueue.repeatedInsertionCost]
  | succ count ih =>
      rw [KleinbergPriorityQueue.repeatedInsertionCost]
      have hhead :
          KleinbergPriorityQueue.logarithmicCost initialSize ≤
            KleinbergPriorityQueue.logarithmicCost (initialSize + (count + 1)) := by
        apply logarithmicCost_mono
        omega
      have htail := ih (initialSize + 1)
      have hindex : initialSize + 1 + count = initialSize + (count + 1) := by omega
      rw [hindex] at htail
      calc
        KleinbergPriorityQueue.logarithmicCost initialSize +
              KleinbergPriorityQueue.repeatedInsertionCost (initialSize + 1) count
            ≤ KleinbergPriorityQueue.logarithmicCost (initialSize + (count + 1)) +
                count *
                  KleinbergPriorityQueue.logarithmicCost
                    (initialSize + (count + 1)) :=
          Nat.add_le_add hhead htail
        _ = (count + 1) *
              KleinbergPriorityQueue.logarithmicCost (initialSize + (count + 1)) := by
          rw [Nat.add_mul]
          simp [Nat.add_comm]

/-- The initialization backend is bounded by its arrays plus `n` final-height insertions. -/
theorem initializationHeapCost_le (n : Nat) :
    initializationHeapCost n ≤
      3 * n + 1 + n * KleinbergPriorityQueue.logarithmicCost n := by
  unfold initializationHeapCost
  apply Nat.add_le_add_left
  simpa using repeatedInsertionCost_le 0 n

/-- Count all operations selected by an indicator, independent of event measurements. -/
def operationProfile {Operation : Type*} (charge : Operation → Nat)
    (computation : TraceM (ResourceAware.Program.Event Operation Nat) α) : Nat :=
  ResourceAware.Program.weightedOperationCost charge computation

@[simp] theorem operationProfile_bind {Operation : Type*}
    (charge : Operation → Nat)
    (computation : TraceM (ResourceAware.Program.Event Operation Nat) α)
    (next : α → TraceM (ResourceAware.Program.Event Operation Nat) β) :
    operationProfile charge (computation >>= next) =
      operationProfile charge computation +
        operationProfile charge (next computation.ret) := by
  exact ResourceAware.Program.weightedOperationCost_bind _ _ _

@[simp] theorem operationProfile_pure {Operation : Type*}
    (charge : Operation → Nat) (value : α) :
    operationProfile charge
      (pure value : TraceM (ResourceAware.Program.Event Operation Nat) α) = 0 := by
  exact ResourceAware.Program.weightedOperationCost_pure _ _

theorem operationProfile_congr {Operation : Type*}
    {left right : Operation → Nat}
    (h : ∀ operation, left operation = right operation)
    (computation : TraceM (ResourceAware.Program.Event Operation Nat) α) :
    operationProfile left computation = operationProfile right computation := by
  congr 1
  funext operation
  exact h operation

theorem operationProfile_add {Operation : Type*}
    (left right : Operation → Nat)
    (computation : TraceM (ResourceAware.Program.Event Operation Nat) α) :
    operationProfile (fun operation => left operation + right operation) computation =
      operationProfile left computation + operationProfile right computation := by
  simp only [operationProfile,
    ResourceAware.Program.weightedOperationCost_eq_foldr]
  induction ResourceAware.Program.operationTrace computation with
  | nil => rfl
  | cons operation operations ih =>
      simp only [List.foldr_cons]
      rw [ih]
      omega

theorem operationProfile_mul {Operation : Type*}
    (factor : Nat) (charge : Operation → Nat)
    (computation : TraceM (ResourceAware.Program.Event Operation Nat) α) :
    operationProfile (fun operation => factor * charge operation) computation =
      factor * operationProfile charge computation := by
  simp only [operationProfile,
    ResourceAware.Program.weightedOperationCost_eq_foldr]
  induction ResourceAware.Program.operationTrace computation with
  | nil => simp
  | cons operation operations ih =>
      simp only [List.foldr_cons]
      rw [ih, Nat.mul_add]

/-- Measured execution from an explicit state under the claim-(4.15) unit profile. -/
abbrev runFrom
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (program : Program
      (model.base.vertexEnumeration.vertices graph).length Edge Weight α)
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight) :=
  ResourceAware.Program.runFrom (Model.semantics model graph index)
    (Model.decompositionCostModel model graph index) program state

/-- Measured execution from an explicit state under the logarithmic heap profile. -/
abbrev heapRunFrom
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (program : Program
      (model.base.vertexEnumeration.vertices graph).length Edge Weight α)
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight) :=
  ResourceAware.Program.runFrom (Model.semantics model graph index)
    (Model.heapCostModel model graph index) program state

theorem runFrom_bind
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (program : Program
      (model.base.vertexEnumeration.vertices graph).length Edge Weight α)
    (next : α → Program
      (model.base.vertexEnumeration.vertices graph).length Edge Weight β)
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight) :
    runFrom model graph index (program >>= next) state =
      runFrom model graph index program state >>= fun result =>
        runFrom model graph index (next result.1) result.2 := by
  exact ResourceAware.Program.runFrom_bind _ _ _ _ _

theorem heapRunFrom_bind
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (program : Program
      (model.base.vertexEnumeration.vertices graph).length Edge Weight α)
    (next : α → Program
      (model.base.vertexEnumeration.vertices graph).length Edge Weight β)
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight) :
    heapRunFrom model graph index (program >>= next) state =
      heapRunFrom model graph index program state >>= fun result =>
        heapRunFrom model graph index (next result.1) result.2 := by
  exact ResourceAware.Program.runFrom_bind _ _ _ _ _

/-- Sum the measurements of an explicit-state heap-profile execution. -/
def heapExactCost
    (computation : TraceM
      (ResourceAware.Program.Event
        (Signature n Edge Weight).A Nat) α) : Nat :=
  ResourceAware.Program.exactCost computation

@[simp] theorem heapExactCost_bind
    (computation : TraceM
      (ResourceAware.Program.Event
        (Signature n Edge Weight).A Nat) α)
    (next : α → TraceM
      (ResourceAware.Program.Event
        (Signature n Edge Weight).A Nat) β) :
    heapExactCost (computation >>= next) =
      heapExactCost computation + heapExactCost (next computation.ret) := by
  exact TraceM.cost_bind _ _ _

/-- Static envelope for every post-initialization heap-profile operation. -/
def heapLoopUpperCharge
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph) :
    (Signature (model.base.vertexEnumeration.vertices graph).length Edge Weight).A → Nat
  | .initialize _ => 0
  | .extractMin =>
      KleinbergPriorityQueue.logarithmicCost
        (model.base.vertexEnumeration.vertices graph).length
  | .outgoingEdges source =>
      model.weightedNeighborCost graph (index.decode source).val
  | .relaxationCandidate _ _ => 1
  | .changeKey _ _ =>
      KleinbergPriorityQueue.logarithmicCost
        (model.base.vertexEnumeration.vertices graph).length

@[simp] theorem operationProfile_relaxationCandidate
    (sourceDistance : Distance Weight)
    (outgoing : IndexedOutgoingEdge
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight) :
    operationProfile relaxationCandidateCharge
      (runFrom model graph index
        (relaxationCandidate sourceDistance outgoing) state) = 1 := by
  rfl

@[simp] theorem operationProfile_changeKey
    (predecessor : Predecessor
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (candidate : Distance Weight)
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight) :
    operationProfile relaxationCandidateCharge
      (runFrom model graph index (changeKey predecessor candidate) state) = 0 := by
  rfl

/-- Under the ChangeKey indicator, a candidate inspection contributes zero. -/
@[simp] theorem changeProfile_relaxationCandidate
    (sourceDistance : Distance Weight)
    (outgoing : IndexedOutgoingEdge
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight) :
    operationProfile changeKeyCharge
      (runFrom model graph index
        (relaxationCandidate sourceDistance outgoing) state) = 0 := by
  rfl

/-- Under the ChangeKey indicator, one ChangeKey request contributes one. -/
@[simp] theorem changeProfile_changeKey
    (predecessor : Predecessor
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (candidate : Distance Weight)
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight) :
    operationProfile changeKeyCharge
      (runFrom model graph index (changeKey predecessor candidate) state) = 1 := by
  rfl

/-- Every returned row occurrence causes exactly one relaxation inspection. -/
theorem processEdges_relaxationCandidate_profile
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length)
    (sourceDistance : Distance Weight)
    (row : List (IndexedOutgoingEdge
      (model.base.vertexEnumeration.vertices graph).length Edge Weight))
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight) :
    operationProfile relaxationCandidateCharge
      (runFrom model graph index
        (processEdges source sourceDistance row) state) = row.length := by
  induction row generalizing state with
  | nil => rfl
  | cons outgoing rest ih =>
      simp only [processEdges]
      rw [runFrom_bind, operationProfile_bind]
      rw [operationProfile_relaxationCandidate]
      simp only [ResourceAware.Program.runFrom_ret]
      simp only [Model.semantics]
      split
      · rw [ih]
        simp only [List.length_cons]
        omega
      · rename_i _ value _
        rw [runFrom_bind, operationProfile_bind]
        rw [operationProfile_changeKey]
        simp only [ResourceAware.Program.runFrom_ret]
        rw [ih]
        simp only [List.length_cons]
        omega

/-- A row can request `ChangeKey` at most once for each inspected occurrence. -/
theorem processEdges_changeKey_profile_le
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length)
    (sourceDistance : Distance Weight)
    (row : List (IndexedOutgoingEdge
      (model.base.vertexEnumeration.vertices graph).length Edge Weight))
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight) :
    operationProfile changeKeyCharge
      (runFrom model graph index
        (processEdges source sourceDistance row) state) ≤ row.length := by
  induction row generalizing state with
  | nil => exact Nat.zero_le _
  | cons outgoing rest ih =>
      simp only [processEdges]
      rw [runFrom_bind, operationProfile_bind]
      rw [changeProfile_relaxationCandidate]
      simp only [Nat.zero_add, ResourceAware.Program.runFrom_ret, Model.semantics]
      split
      · change operationProfile changeKeyCharge
          (runFrom model graph index
            (processEdges source sourceDistance rest) state) ≤
            (outgoing :: rest).length
        have htail := ih state
        simp only [List.length_cons]
        omega
      · rename_i _ value _
        rw [runFrom_bind, operationProfile_bind]
        rw [changeProfile_changeKey]
        simp only [ResourceAware.Program.runFrom_ret]
        change 1 + operationProfile changeKeyCharge
          (runFrom model graph index
            (processEdges source sourceDistance rest)
            ((Model.semantics model graph index).step
              (.changeKey
                ⟨source, outgoing.target, outgoing.edge, outgoing.weight⟩ value)
              state).2) ≤ (outgoing :: rest).length
        have htail := ih
          ((Model.semantics model graph index).step
            (.changeKey
              ⟨source, outgoing.target, outgoing.edge, outgoing.weight⟩ value) state).2
        simp only [List.length_cons]
        omega

/-- Any profile that charges neither row primitive assigns zero to `processEdges`. -/
theorem processEdges_profile_eq_zero
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (charge : (Signature
      (model.base.vertexEnumeration.vertices graph).length Edge Weight).A → Nat)
    (hrelax : ∀ distance outgoing,
      charge (.relaxationCandidate distance outgoing) = 0)
    (hchange : ∀ predecessor candidate,
      charge (.changeKey predecessor candidate) = 0)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length)
    (sourceDistance : Distance Weight)
    (row : List (IndexedOutgoingEdge
      (model.base.vertexEnumeration.vertices graph).length Edge Weight))
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight) :
    operationProfile charge
      (runFrom model graph index
        (processEdges source sourceDistance row) state) = 0 := by
  induction row generalizing state with
  | nil => rfl
  | cons outgoing rest ih =>
      simp only [processEdges]
      rw [runFrom_bind, operationProfile_bind]
      change charge (.relaxationCandidate sourceDistance outgoing) +
        operationProfile charge
          (runFrom model graph index
            (match
              (runFrom model graph index
                (relaxationCandidate sourceDistance outgoing) state).ret.1.down with
            | none => processEdges source sourceDistance rest
            | some value => do
                let _ ← changeKey
                  ⟨source, outgoing.target, outgoing.edge, outgoing.weight⟩ value
                processEdges source sourceDistance rest)
            (runFrom model graph index
              (relaxationCandidate sourceDistance outgoing) state).ret.2) = 0
      rw [hrelax]
      simp only [Nat.zero_add, ResourceAware.Program.runFrom_ret, Model.semantics]
      split
      · exact ih state
      · rename_i _ value _
        rw [runFrom_bind, operationProfile_bind]
        change charge
            (.changeKey
              ⟨source, outgoing.target, outgoing.edge, outgoing.weight⟩ value) +
            operationProfile charge
              (runFrom model graph index
                (processEdges source sourceDistance rest)
                (runFrom model graph index
                  (changeKey
                    ⟨source, outgoing.target, outgoing.edge, outgoing.weight⟩ value)
                  state).ret.2) = 0
        rw [hchange]
        simp only [Nat.zero_add, ResourceAware.Program.runFrom_ret]
        exact ih _

/--
The actual heap measurements of a row are bounded by the static post-initialization
operation envelope. Queue well-formedness supplies the active-size bound for `ChangeKey`.
-/
theorem processEdges_heapExactCost_le_upperProfile
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length)
    (sourceDistance : Distance Weight)
    (row : List (IndexedOutgoingEdge
      (model.base.vertexEnumeration.vertices graph).length Edge Weight))
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (hinvariant : Operational.QueueInvariant state) :
    heapExactCost
        (heapRunFrom model graph index
          (processEdges source sourceDistance row) state) ≤
      operationProfile (heapLoopUpperCharge model graph index)
        (runFrom model graph index
          (processEdges source sourceDistance row) state) := by
  induction row generalizing state with
  | nil => exact Nat.le_refl 0
  | cons outgoing rest ih =>
      simp only [processEdges]
      rw [heapRunFrom_bind, heapExactCost_bind]
      rw [runFrom_bind, operationProfile_bind]
      have hrelaxExact :
          heapExactCost
            (heapRunFrom model graph index
              (relaxationCandidate sourceDistance outgoing) state) = 1 := by
        rfl
      have hrelaxProfile :
          operationProfile (heapLoopUpperCharge model graph index)
            (runFrom model graph index
              (relaxationCandidate sourceDistance outgoing) state) = 1 := by
        rfl
      rw [hrelaxExact, hrelaxProfile]
      simp only [ResourceAware.Program.runFrom_ret]
      rw [show (Model.semantics model graph index).evalFrom
          (relaxationCandidate sourceDistance outgoing) state =
        (Model.semantics model graph index).step
          (.relaxationCandidate sourceDistance outgoing) state by rfl]
      simp only [Model.semantics]
      split
      · exact Nat.add_le_add_left (ih state hinvariant) 1
      · rename_i _ value _
        rw [heapRunFrom_bind, heapExactCost_bind]
        rw [runFrom_bind, operationProfile_bind]
        let predecessor : Predecessor
            (model.base.vertexEnumeration.vertices graph).length Edge Weight :=
          ⟨source, outgoing.target, outgoing.edge, outgoing.weight⟩
        have hstep : Operational.QueueInvariant
            ((Model.semantics model graph index).step
              (.changeKey predecessor value) state).2 := by
          dsimp [Model.semantics, predecessor]
          split
          · constructor
            · exact KleinbergPriorityQueue.Heap.changeKey_wellFormed
                state.heap hinvariant.wellFormed _ _
            · intro name
              rw [KleinbergPriorityQueue.Heap.changeKey_contains]
              exact hinvariant.active_iff_not_settled name
            · exact hinvariant.settled_nodup
          · exact hinvariant
        have hchangeExact :
            heapExactCost
              (heapRunFrom model graph index
                (changeKey predecessor value) state) =
              KleinbergPriorityQueue.logarithmicCost state.heap.H.size := by
          rfl
        have hchangeProfile :
            operationProfile (heapLoopUpperCharge model graph index)
              (runFrom model graph index
                (changeKey predecessor value) state) =
              KleinbergPriorityQueue.logarithmicCost
                (model.base.vertexEnumeration.vertices graph).length := by
          rfl
        have hchangeExact' :
            heapExactCost
              (heapRunFrom model graph index
                (changeKey
                  ⟨source, outgoing.target, outgoing.edge, outgoing.weight⟩ value)
                state) =
              KleinbergPriorityQueue.logarithmicCost state.heap.H.size := by
          simpa [predecessor] using hchangeExact
        have hchangeProfile' :
            operationProfile (heapLoopUpperCharge model graph index)
              (runFrom model graph index
                (changeKey
                  ⟨source, outgoing.target, outgoing.edge, outgoing.weight⟩ value)
                state) =
              KleinbergPriorityQueue.logarithmicCost
                (model.base.vertexEnumeration.vertices graph).length := by
          simpa [predecessor] using hchangeProfile
        rw [hchangeExact', hchangeProfile']
        simp only [ResourceAware.Program.runFrom_ret]
        have hsize :
            KleinbergPriorityQueue.logarithmicCost state.heap.H.size ≤
              KleinbergPriorityQueue.logarithmicCost
                (model.base.vertexEnumeration.vertices graph).length :=
          logarithmicCost_mono hinvariant.wellFormed.1
        have htail := ih
          ((Model.semantics model graph index).step
            (.changeKey predecessor value) state).2 hstep
        have htail' :
            heapExactCost
                (heapRunFrom model graph index
                  (processEdges source sourceDistance rest)
                  ((Model.semantics model graph index).step
                    (.changeKey
                      ⟨source, outgoing.target, outgoing.edge, outgoing.weight⟩ value)
                    state).2) ≤
              operationProfile (heapLoopUpperCharge model graph index)
                (runFrom model graph index
                  (processEdges source sourceDistance rest)
                  ((Model.semantics model graph index).step
                    (.changeKey
                      ⟨source, outgoing.target, outgoing.edge, outgoing.weight⟩ value)
                    state).2) := by
          simpa [predecessor] using htail
        exact Nat.add_le_add_left (Nat.add_le_add hsize htail') 1

theorem processEdges_extractMin_profile
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length)
    (sourceDistance : Distance Weight)
    (row : List (IndexedOutgoingEdge
      (model.base.vertexEnumeration.vertices graph).length Edge Weight))
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight) :
    operationProfile extractMinCharge
      (runFrom model graph index
        (processEdges source sourceDistance row) state) = 0 := by
  apply processEdges_profile_eq_zero model graph index
  · intros
    rfl
  · intros
    rfl

theorem processEdges_outgoingEdges_profile
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length)
    (sourceDistance : Distance Weight)
    (row : List (IndexedOutgoingEdge
      (model.base.vertexEnumeration.vertices graph).length Edge Weight))
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight) :
    operationProfile outgoingEdgesCharge
      (runFrom model graph index
        (processEdges source sourceDistance row) state) = 0 := by
  apply processEdges_profile_eq_zero model graph index
  · intros
    rfl
  · intros
    rfl

/-- Every available unit of loop fuel produces exactly one `ExtractMin` request. -/
theorem dijkstraLoop_extractMin_profile
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (fuel : Nat)
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (hinvariant : Operational.QueueInvariant state)
    (hfuel : fuel ≤ state.heap.H.size) :
    operationProfile extractMinCharge
      (runFrom model graph index
        (dijkstraLoop (Edge := Edge) (Weight := Weight) fuel) state) = fuel := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      have hne : 0 < state.heap.H.size := by omega
      let extracted := state.heap.H[0]
      let afterExtract :=
        ((Model.semantics model graph index).step (.extractMin) state).2
      have hextract :=
        Operational.extractMin_queueInvariant model graph index state hinvariant hne
      dsimp only at hextract
      rcases hextract with
        ⟨hresponse, hafterInvariant, hafterSize, hafterSettled⟩
      change Operational.QueueInvariant afterExtract at hafterInvariant
      change afterExtract.heap.H.size + 1 = state.heap.H.size at hafterSize
      simp only [dijkstraLoop]
      rw [runFrom_bind, operationProfile_bind]
      have hextractProfile :
          operationProfile extractMinCharge
            (runFrom model graph index
              (extractMin (Edge := Edge) (Weight := Weight)) state) = 1 := by
        rfl
      rw [hextractProfile]
      simp only [ResourceAware.Program.runFrom_ret]
      have hstep :
          (Model.semantics model graph index).step
              (.extractMin : Op
                (model.base.vertexEnumeration.vertices graph).length Edge Weight) state =
            (ULift.up (some extracted), afterExtract) := by
        apply Prod.ext
        · simpa [extracted] using hresponse
        · rfl
      rw [show (Model.semantics model graph index).evalFrom
          (extractMin (Edge := Edge) (Weight := Weight)) state =
        (Model.semantics model graph index).step (.extractMin) state by rfl]
      rw [hstep]
      simp only
      rw [runFrom_bind, operationProfile_bind]
      change 1 + (0 + operationProfile extractMinCharge
        (runFrom model graph index
          (do
            processEdges extracted.name extracted.key
              (runFrom model graph index (outgoingEdges extracted.name) afterExtract).ret.1
            dijkstraLoop fuel)
          (runFrom model graph index (outgoingEdges extracted.name) afterExtract).ret.2)) =
        fuel + 1
      simp only [ResourceAware.Program.runFrom_ret]
      rw [show (Model.semantics model graph index).evalFrom
          (outgoingEdges extracted.name) afterExtract =
        (Model.indexedOutgoingEdges model graph index extracted.name, afterExtract) by rfl]
      simp only
      rw [runFrom_bind, operationProfile_bind]
      rw [processEdges_extractMin_profile]
      simp only [Nat.zero_add, ResourceAware.Program.runFrom_ret]
      let afterRow := (Operational.execute model graph index
        (processEdges extracted.name extracted.key
          (Model.indexedOutgoingEdges model graph index extracted.name)) afterExtract).2
      have hrowInvariant : Operational.QueueInvariant afterRow :=
        Operational.processEdges_queueInvariant model graph index
          extracted.name extracted.key
          (Model.indexedOutgoingEdges model graph index extracted.name)
          afterExtract hafterInvariant
      have hrowFuel : fuel ≤ afterRow.heap.H.size := by
        rw [Operational.processEdges_heap_size]
        omega
      change 1 + operationProfile extractMinCharge
        (runFrom model graph index
          (dijkstraLoop (Edge := Edge) (Weight := Weight) fuel) afterRow) = fuel + 1
      rw [ih afterRow hrowInvariant hrowFuel]
      omega

/--
The exact measurements of the logarithmic heap backend are bounded by the static operation
envelope on every queue-valid loop prefix.
-/
theorem dijkstraLoop_heapExactCost_le_upperProfile
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (fuel : Nat)
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (hinvariant : Operational.QueueInvariant state)
    (hfuel : fuel ≤ state.heap.H.size) :
    heapExactCost
        (heapRunFrom model graph index
          (dijkstraLoop (Edge := Edge) (Weight := Weight) fuel) state) ≤
      operationProfile (heapLoopUpperCharge model graph index)
        (runFrom model graph index
          (dijkstraLoop (Edge := Edge) (Weight := Weight) fuel) state) := by
  induction fuel generalizing state with
  | zero => exact Nat.le_refl 0
  | succ fuel ih =>
      have hne : 0 < state.heap.H.size := by omega
      let extracted := state.heap.H[0]
      let afterExtract :=
        ((Model.semantics model graph index).step (.extractMin) state).2
      have hextract :=
        Operational.extractMin_queueInvariant model graph index state hinvariant hne
      dsimp only at hextract
      rcases hextract with
        ⟨hresponse, hafterInvariant, hafterSize, _⟩
      change Operational.QueueInvariant afterExtract at hafterInvariant
      change afterExtract.heap.H.size + 1 = state.heap.H.size at hafterSize
      have hstep :
          (Model.semantics model graph index).step
              (.extractMin : Op
                (model.base.vertexEnumeration.vertices graph).length Edge Weight) state =
            (ULift.up (some extracted), afterExtract) := by
        apply Prod.ext
        · simpa [extracted] using hresponse
        · rfl
      simp only [dijkstraLoop]
      rw [heapRunFrom_bind, heapExactCost_bind]
      rw [runFrom_bind, operationProfile_bind]
      have hextractExact :
          heapExactCost
            (heapRunFrom model graph index
              (extractMin (Edge := Edge) (Weight := Weight)) state) =
            KleinbergPriorityQueue.logarithmicCost state.heap.H.size := by
        rfl
      have hextractProfile :
          operationProfile (heapLoopUpperCharge model graph index)
            (runFrom model graph index
              (extractMin (Edge := Edge) (Weight := Weight)) state) =
            KleinbergPriorityQueue.logarithmicCost
              (model.base.vertexEnumeration.vertices graph).length := by
        rfl
      rw [hextractExact, hextractProfile]
      simp only [ResourceAware.Program.runFrom_ret]
      rw [show (Model.semantics model graph index).evalFrom
          (extractMin (Edge := Edge) (Weight := Weight)) state =
        (Model.semantics model graph index).step (.extractMin) state by rfl]
      rw [hstep]
      simp only
      rw [heapRunFrom_bind, heapExactCost_bind]
      rw [runFrom_bind, operationProfile_bind]
      have houtgoingExact :
          heapExactCost
            (heapRunFrom model graph index
              (outgoingEdges extracted.name) afterExtract) =
            model.weightedNeighborCost graph (index.decode extracted.name).val := by
        rfl
      have houtgoingProfile :
          operationProfile (heapLoopUpperCharge model graph index)
            (runFrom model graph index
              (outgoingEdges extracted.name) afterExtract) =
            model.weightedNeighborCost graph (index.decode extracted.name).val := by
        rfl
      rw [houtgoingExact, houtgoingProfile]
      simp only [ResourceAware.Program.runFrom_ret]
      rw [show (Model.semantics model graph index).evalFrom
          (outgoingEdges extracted.name) afterExtract =
        (Model.indexedOutgoingEdges model graph index extracted.name, afterExtract) by rfl]
      simp only
      rw [heapRunFrom_bind, heapExactCost_bind]
      rw [runFrom_bind, operationProfile_bind]
      let afterRow := (Operational.execute model graph index
        (processEdges extracted.name extracted.key
          (Model.indexedOutgoingEdges model graph index extracted.name)) afterExtract).2
      have hprocess :=
        processEdges_heapExactCost_le_upperProfile model graph index
          extracted.name extracted.key
          (Model.indexedOutgoingEdges model graph index extracted.name)
          afterExtract hafterInvariant
      have hrowInvariant : Operational.QueueInvariant afterRow :=
        Operational.processEdges_queueInvariant model graph index
          extracted.name extracted.key
          (Model.indexedOutgoingEdges model graph index extracted.name)
          afterExtract hafterInvariant
      have hrowFuel : fuel ≤ afterRow.heap.H.size := by
        rw [Operational.processEdges_heap_size]
        omega
      have htail := ih afterRow hrowInvariant hrowFuel
      have hsize :
          KleinbergPriorityQueue.logarithmicCost state.heap.H.size ≤
            KleinbergPriorityQueue.logarithmicCost
              (model.base.vertexEnumeration.vertices graph).length :=
        logarithmicCost_mono hinvariant.wellFormed.1
      have hheapAfter :
          (heapRunFrom model graph index
            (processEdges extracted.name extracted.key
              (Model.indexedOutgoingEdges model graph index extracted.name))
            afterExtract).ret.2 = afterRow := by
        rw [ResourceAware.Program.runFrom_ret]
      have hdecompositionAfter :
          (runFrom model graph index
            (processEdges extracted.name extracted.key
              (Model.indexedOutgoingEdges model graph index extracted.name))
            afterExtract).ret.2 = afterRow := by
        rw [ResourceAware.Program.runFrom_ret]
      rw [hheapAfter, hdecompositionAfter]
      change KleinbergPriorityQueue.logarithmicCost state.heap.H.size +
            (model.weightedNeighborCost graph (index.decode extracted.name).val +
              (heapExactCost
                  (heapRunFrom model graph index
                    (processEdges extracted.name extracted.key
                      (Model.indexedOutgoingEdges model graph index extracted.name))
                    afterExtract) +
                heapExactCost
                  (heapRunFrom model graph index
                    (dijkstraLoop (Edge := Edge) (Weight := Weight) fuel) afterRow))) ≤
        KleinbergPriorityQueue.logarithmicCost
              (model.base.vertexEnumeration.vertices graph).length +
            (model.weightedNeighborCost graph (index.decode extracted.name).val +
              (operationProfile (heapLoopUpperCharge model graph index)
                  (runFrom model graph index
                    (processEdges extracted.name extracted.key
                      (Model.indexedOutgoingEdges model graph index extracted.name))
                    afterExtract) +
                operationProfile (heapLoopUpperCharge model graph index)
                  (runFrom model graph index
                    (dijkstraLoop (Edge := Edge) (Weight := Weight) fuel) afterRow)))
      exact Nat.add_le_add hsize
        (Nat.add_le_add_left (Nat.add_le_add hprocess htail) _)

/-- Number of indexed occurrences in the row selected by one dense vertex name. -/
def indexedRowLength
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (name : Fin (model.base.vertexEnumeration.vertices graph).length) : Nat :=
  (Model.indexedOutgoingEdges model graph index name).length

/-- Candidate inspections are exactly the row lengths of the newly settled suffix. -/
theorem dijkstraLoop_relaxationCandidate_profile
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (fuel : Nat)
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (hinvariant : Operational.QueueInvariant state)
    (hfuel : fuel ≤ state.heap.H.size) :
    operationProfile relaxationCandidateCharge
        (runFrom model graph index
          (dijkstraLoop (Edge := Edge) (Weight := Weight) fuel) state) =
      (((Operational.execute model graph index
          (dijkstraLoop (Edge := Edge) (Weight := Weight) fuel) state).2.settled.drop
            state.settled.length).map (indexedRowLength model graph index)).sum := by
  induction fuel generalizing state with
  | zero => simp [dijkstraLoop]
  | succ fuel ih =>
      have hne : 0 < state.heap.H.size := by omega
      let extracted := state.heap.H[0]
      let afterExtract :=
        ((Model.semantics model graph index).step (.extractMin) state).2
      have hextract :=
        Operational.extractMin_queueInvariant model graph index state hinvariant hne
      dsimp only at hextract
      rcases hextract with
        ⟨hresponse, hafterInvariant, hafterSize, hafterSettled⟩
      change Operational.QueueInvariant afterExtract at hafterInvariant
      change afterExtract.heap.H.size + 1 = state.heap.H.size at hafterSize
      change afterExtract.settled =
        state.settled ++ [extracted.name] at hafterSettled
      have hstep :
          (Model.semantics model graph index).step
              (.extractMin : Op
                (model.base.vertexEnumeration.vertices graph).length Edge Weight) state =
            (ULift.up (some extracted), afterExtract) := by
        apply Prod.ext
        · simpa [extracted] using hresponse
        · rfl
      simp only [dijkstraLoop]
      rw [runFrom_bind, operationProfile_bind]
      have hextractProfile :
          operationProfile relaxationCandidateCharge
            (runFrom model graph index
              (extractMin (Edge := Edge) (Weight := Weight)) state) = 0 := by
        rfl
      rw [hextractProfile]
      simp only [Nat.zero_add, ResourceAware.Program.runFrom_ret]
      rw [show (Model.semantics model graph index).evalFrom
          (extractMin (Edge := Edge) (Weight := Weight)) state =
        (Model.semantics model graph index).step (.extractMin) state by rfl]
      rw [hstep]
      simp only
      rw [runFrom_bind, operationProfile_bind]
      have houtgoingProfile :
          operationProfile relaxationCandidateCharge
            (runFrom model graph index
              (outgoingEdges extracted.name) afterExtract) = 0 := by
        rfl
      rw [houtgoingProfile]
      simp only [Nat.zero_add, ResourceAware.Program.runFrom_ret]
      rw [show (Model.semantics model graph index).evalFrom
          (outgoingEdges extracted.name) afterExtract =
        (Model.indexedOutgoingEdges model graph index extracted.name, afterExtract) by rfl]
      simp only
      rw [runFrom_bind, operationProfile_bind]
      rw [processEdges_relaxationCandidate_profile]
      simp only [ResourceAware.Program.runFrom_ret]
      let afterRow := (Operational.execute model graph index
        (processEdges extracted.name extracted.key
          (Model.indexedOutgoingEdges model graph index extracted.name)) afterExtract).2
      have hrowInvariant : Operational.QueueInvariant afterRow :=
        Operational.processEdges_queueInvariant model graph index
          extracted.name extracted.key
          (Model.indexedOutgoingEdges model graph index extracted.name)
          afterExtract hafterInvariant
      have hrowFuel : fuel ≤ afterRow.heap.H.size := by
        rw [Operational.processEdges_heap_size]
        omega
      have hrowSettled : afterRow.settled =
          state.settled ++ [extracted.name] := by
        rw [Operational.processEdges_settled, hafterSettled]
      have htail := ih afterRow hrowInvariant hrowFuel
      have htailOperational :=
        Operational.dijkstraLoop_queueInvariant model graph index fuel afterRow
          hrowInvariant hrowFuel
      dsimp only at htailOperational
      rcases htailOperational.2.2.2 with ⟨suffix, hsuffix⟩
      have hOperational :
          (Operational.execute model graph index
            (dijkstraLoop (Edge := Edge) (Weight := Weight) (fuel + 1)) state).2 =
          (Operational.execute model graph index
            (dijkstraLoop (Edge := Edge) (Weight := Weight) fuel) afterRow).2 := by
        simp only [dijkstraLoop]
        rw [Operational.execute_bind]
        rw [show Operational.execute model graph index
            (extractMin (Edge := Edge) (Weight := Weight)) state =
          (Model.semantics model graph index).step (.extractMin) state by rfl]
        rw [hstep]
        simp only
        rw [Operational.execute_bind]
        rw [show Operational.execute model graph index
            (outgoingEdges extracted.name) afterExtract =
          (Model.indexedOutgoingEdges model graph index extracted.name,
            afterExtract) by rfl]
        simp only
        rw [Operational.execute_bind]
      have hafterRowEval :
          ((Model.semantics model graph index).evalFrom
            (processEdges extracted.name extracted.key
            (Model.indexedOutgoingEdges model graph index extracted.name))
            afterExtract).2 = afterRow := rfl
      have hloopUnfold := congrArg
        (fun program : Program
            (model.base.vertexEnumeration.vertices graph).length Edge Weight PUnit =>
          (Operational.execute model graph index program state).2.settled)
        (dijkstraLoop.eq_2
          (n := (model.base.vertexEnumeration.vertices graph).length)
          (Edge := Edge) (Weight := Weight) fuel).symm
      have hOperationalSettled := congrArg Model.State.settled hOperational
      rw [hloopUnfold, hOperationalSettled, hafterRowEval]
      change indexedRowLength model graph index extracted.name +
          operationProfile relaxationCandidateCharge
            (runFrom model graph index
              (dijkstraLoop (Edge := Edge) (Weight := Weight) fuel) afterRow) =
        (((Operational.execute model graph index
          (dijkstraLoop (Edge := Edge) (Weight := Weight) fuel) afterRow).2.settled.drop
            state.settled.length).map (indexedRowLength model graph index)).sum
      rw [htail, ← hsuffix, hrowSettled]
      simp [indexedRowLength]

/-- Across every loop execution, `ChangeKey` requests are bounded by inspected occurrences. -/
theorem dijkstraLoop_changeKey_profile_le_relaxationCandidate
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (fuel : Nat)
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight) :
    operationProfile changeKeyCharge
        (runFrom model graph index
          (dijkstraLoop (Edge := Edge) (Weight := Weight) fuel) state) ≤
      operationProfile relaxationCandidateCharge
        (runFrom model graph index
          (dijkstraLoop (Edge := Edge) (Weight := Weight) fuel) state) := by
  induction fuel generalizing state with
  | zero => exact Nat.le_refl 0
  | succ fuel ih =>
      simp only [dijkstraLoop]
      conv_lhs => rw [runFrom_bind, operationProfile_bind]
      conv_rhs => rw [runFrom_bind, operationProfile_bind]
      have hextractChange :
          operationProfile changeKeyCharge
            (runFrom model graph index
              (extractMin (Edge := Edge) (Weight := Weight)) state) = 0 := by
        rfl
      have hextractCandidate :
          operationProfile relaxationCandidateCharge
            (runFrom model graph index
              (extractMin (Edge := Edge) (Weight := Weight)) state) = 0 := by
        rfl
      rw [hextractChange, hextractCandidate]
      simp only [Nat.zero_add, ResourceAware.Program.runFrom_ret]
      rw [show (Model.semantics model graph index).evalFrom
          (extractMin (Edge := Edge) (Weight := Weight)) state =
        (Model.semantics model graph index).step (.extractMin) state by rfl]
      split
      · exact Nat.le_refl 0
      · rename_i entry _
        conv_lhs => rw [runFrom_bind, operationProfile_bind]
        conv_rhs => rw [runFrom_bind, operationProfile_bind]
        have houtgoingChange :
            operationProfile changeKeyCharge
              (runFrom model graph index
                (outgoingEdges entry.name)
                ((Model.semantics model graph index).step (.extractMin) state).2) = 0 := by
          rfl
        have houtgoingCandidate :
            operationProfile relaxationCandidateCharge
              (runFrom model graph index
                (outgoingEdges entry.name)
                ((Model.semantics model graph index).step (.extractMin) state).2) = 0 := by
          rfl
        rw [houtgoingChange, houtgoingCandidate]
        simp only [Nat.zero_add, ResourceAware.Program.runFrom_ret]
        rw [show (Model.semantics model graph index).evalFrom
            (outgoingEdges entry.name)
            ((Model.semantics model graph index).step (.extractMin) state).2 =
          (Model.indexedOutgoingEdges model graph index entry.name,
            ((Model.semantics model graph index).step (.extractMin) state).2) by rfl]
        simp only
        conv_lhs => rw [runFrom_bind, operationProfile_bind]
        conv_rhs => rw [runFrom_bind, operationProfile_bind]
        have hrow := processEdges_changeKey_profile_le model graph index
          entry.name entry.key
          (Model.indexedOutgoingEdges model graph index entry.name)
          ((Model.semantics model graph index).step (.extractMin) state).2
        rw [processEdges_relaxationCandidate_profile]
        simp only [ResourceAware.Program.runFrom_ret]
        let afterRow := (Operational.execute model graph index
          (processEdges entry.name entry.key
            (Model.indexedOutgoingEdges model graph index entry.name))
          ((Model.semantics model graph index).step (.extractMin) state).2).2
        change operationProfile changeKeyCharge
              (runFrom model graph index
                (processEdges entry.name entry.key
                  (Model.indexedOutgoingEdges model graph index entry.name))
                ((Model.semantics model graph index).step (.extractMin) state).2) +
            operationProfile changeKeyCharge
              (runFrom model graph index
                (dijkstraLoop (Edge := Edge) (Weight := Weight) fuel) afterRow) ≤
          (Model.indexedOutgoingEdges model graph index entry.name).length +
            operationProfile relaxationCandidateCharge
              (runFrom model graph index
                (dijkstraLoop (Edge := Edge) (Weight := Weight) fuel) afterRow)
        exact Nat.add_le_add hrow (ih afterRow)

/--
If a representation charges an outgoing-row request by its returned row length, its complete
row-query work is exactly the number of relaxation inspections. This is the exact trace bridge
needed by claim (4.15).
-/
theorem dijkstraLoop_outgoingRowWork_eq_relaxationCandidate
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (hrow : ∀ name,
      model.weightedNeighborCost graph (index.decode name).val =
        indexedRowLength model graph index name)
    (fuel : Nat)
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight) :
    operationProfile (outgoingRowWorkCharge model graph index)
        (runFrom model graph index
          (dijkstraLoop (Edge := Edge) (Weight := Weight) fuel) state) =
      operationProfile relaxationCandidateCharge
        (runFrom model graph index
          (dijkstraLoop (Edge := Edge) (Weight := Weight) fuel) state) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      simp only [dijkstraLoop]
      conv_lhs => rw [runFrom_bind, operationProfile_bind]
      conv_rhs => rw [runFrom_bind, operationProfile_bind]
      have hextractRow :
          operationProfile (outgoingRowWorkCharge model graph index)
            (runFrom model graph index
              (extractMin (Edge := Edge) (Weight := Weight)) state) = 0 := by
        rfl
      have hextractCandidate :
          operationProfile relaxationCandidateCharge
            (runFrom model graph index
              (extractMin (Edge := Edge) (Weight := Weight)) state) = 0 := by
        rfl
      rw [hextractRow, hextractCandidate]
      simp only [Nat.zero_add, ResourceAware.Program.runFrom_ret]
      rw [show (Model.semantics model graph index).evalFrom
          (extractMin (Edge := Edge) (Weight := Weight)) state =
        (Model.semantics model graph index).step (.extractMin) state by rfl]
      split
      · rfl
      · rename_i entry _
        conv_lhs => rw [runFrom_bind, operationProfile_bind]
        conv_rhs => rw [runFrom_bind, operationProfile_bind]
        change model.weightedNeighborCost graph (index.decode entry.name).val +
            operationProfile (outgoingRowWorkCharge model graph index)
              (runFrom model graph index
                (do
                  processEdges entry.name entry.key
                    (runFrom model graph index (outgoingEdges entry.name)
                      ((Model.semantics model graph index).step
                        (.extractMin) state).2).ret.1
                  dijkstraLoop fuel)
                (runFrom model graph index (outgoingEdges entry.name)
                  ((Model.semantics model graph index).step
                    (.extractMin) state).2).ret.2) =
          0 + operationProfile relaxationCandidateCharge
            (runFrom model graph index
              (do
                processEdges entry.name entry.key
                  (runFrom model graph index (outgoingEdges entry.name)
                    ((Model.semantics model graph index).step
                      (.extractMin) state).2).ret.1
                dijkstraLoop fuel)
              (runFrom model graph index (outgoingEdges entry.name)
                ((Model.semantics model graph index).step
                  (.extractMin) state).2).ret.2)
        simp only [Nat.zero_add, ResourceAware.Program.runFrom_ret]
        rw [show (Model.semantics model graph index).evalFrom
            (outgoingEdges entry.name)
            ((Model.semantics model graph index).step (.extractMin) state).2 =
          (Model.indexedOutgoingEdges model graph index entry.name,
            ((Model.semantics model graph index).step (.extractMin) state).2) by rfl]
        simp only
        conv_lhs => rw [runFrom_bind, operationProfile_bind]
        conv_rhs => rw [runFrom_bind, operationProfile_bind]
        rw [processEdges_profile_eq_zero model graph index
          (outgoingRowWorkCharge model graph index)
          (fun _ _ => rfl) (fun _ _ => rfl)]
        rw [processEdges_relaxationCandidate_profile]
        simp only [Nat.zero_add, ResourceAware.Program.runFrom_ret]
        rw [hrow entry.name]
        apply congrArg
        exact ih _

/-- Decoding all dense names enumerates every represented graph vertex exactly once. -/
theorem decoded_finRange_perm_vertices
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph) :
    List.Perm
      ((List.finRange (model.base.vertexEnumeration.vertices graph).length).map
        (fun name => (index.decode name).val))
      (model.base.vertexEnumeration.vertices graph) := by
  apply (List.perm_ext_iff_of_nodup
    ((List.nodup_finRange _).map ?_)
    (model.base.vertexEnumeration.nodup graph)).2
  · intro vertex
    constructor
    · intro hvertex
      rcases List.mem_map.mp hvertex with ⟨name, _, rfl⟩
      exact model.base.vertexEnumeration.complete (index.decode name).property
    · intro hvertex
      let graphVertex : GraphVertex model.base.interface graph :=
        ⟨vertex, model.base.vertexEnumeration.sound hvertex⟩
      apply List.mem_map.mpr
      refine ⟨index.encode graphVertex, List.mem_finRange _, ?_⟩
      simp [graphVertex]
  · intro left right heq
    apply VertexIndex.decode_injective index
    exact Subtype.ext heq

/-- Every non-reflexive reachable vertex has an incoming semantic edge. -/
theorem reachable_exists_incoming
    {Γ : Interface G V} {graph : G} {source target : V}
    (hreachable : Reachable Γ graph source target)
    (hne : source ≠ target) :
    ∃ parent, Γ.Adj graph parent target := by
  induction hreachable with
  | refl _ => exact False.elim (hne rfl)
  | @step source middle target hedge _ ih =>
      by_cases hmiddle : middle = target
      · subst middle
        exact ⟨source, hedge⟩
      · exact ih hmiddle

/--
If every enumerated vertex is reachable from the source, choosing one incoming occurrence
for every non-source vertex injects those vertices into the directed occurrence list.
-/
theorem vertexCount_le_directedEdgeOccurrenceCount_add_one_of_reachable
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (source : GraphVertex model.base.interface graph)
    (hreachable : ∀ vertex ∈ model.base.vertexEnumeration.vertices graph,
      Reachable model.base.interface graph source.val vertex) :
    (model.base.vertexEnumeration.vertices graph).length ≤
      model.directedEdgeOccurrenceCount graph + 1 := by
  classical
  let vertices := model.base.vertexEnumeration.vertices graph
  let occurrences := model.directedEdgeOccurrences graph
  let remaining := vertices.erase source.val
  have hincoming :
      ∀ vertex : {vertex // vertex ∈ remaining},
        ∃ position : Fin occurrences.length,
          (occurrences.get position).2.target = vertex.val := by
    intro vertex
    have hvertextFacts : vertex.val ≠ source.val ∧ vertex.val ∈ vertices := by
      have heraseEq :
          remaining = vertices.filter (fun candidate => candidate != source.val) := by
        exact (model.base.vertexEnumeration.nodup graph).erase_eq_filter source.val
      have hmember :
          vertex.val ∈ vertices.filter (fun candidate => candidate != source.val) :=
        (congrArg (fun list => vertex.val ∈ list) heraseEq).mp vertex.property
      rcases List.mem_filter.mp hmember with ⟨hvertices, hne⟩
      exact ⟨by simpa using hne, hvertices⟩
    have hincomingEdge := reachable_exists_incoming
      (hreachable vertex.val hvertextFacts.2) (Ne.symm hvertextFacts.1)
    rcases hincomingEdge with ⟨parent, hparent⟩
    rcases model.edgeView.adj_has_arc hparent with ⟨edge, weight, harc⟩
    have hmem :
        (parent, ⟨edge, vertex.val, weight⟩) ∈ occurrences := by
      exact WeightedResourceModel.arc_mem_directedEdgeOccurrences model harc
    rcases List.mem_iff_get.mp hmem with ⟨position, hposition⟩
    refine ⟨position, ?_⟩
    simpa using congrArg (fun occurrence => occurrence.2.target) hposition
  let incomingPosition :
      {vertex // vertex ∈ remaining} → Fin occurrences.length :=
    fun vertex => (hincoming vertex).choose
  have hincomingPosition (vertex : {vertex // vertex ∈ remaining}) :
      (occurrences.get (incomingPosition vertex)).2.target = vertex.val :=
    (hincoming vertex).choose_spec
  have hinjective : Function.Injective incomingPosition := by
    intro left right heq
    apply Subtype.ext
    calc
      left.val = (occurrences.get (incomingPosition left)).2.target :=
        (hincomingPosition left).symm
      _ = (occurrences.get (incomingPosition right)).2.target := by rw [heq]
      _ = right.val := hincomingPosition right
  have hremainingNodup : remaining.Nodup := by
    exact (model.base.vertexEnumeration.nodup graph).erase source.val
  let fromRemaining : Fin remaining.length → Fin occurrences.length :=
    fun position =>
      incomingPosition ⟨remaining.get position, List.get_mem remaining position⟩
  have hfromRemaining : Function.Injective fromRemaining := by
    intro left right heq
    have hsubtype :
        (⟨remaining.get left, List.get_mem remaining left⟩ :
            {vertex // vertex ∈ remaining}) =
          ⟨remaining.get right, List.get_mem remaining right⟩ :=
      hinjective heq
    apply (hremainingNodup.get_inj_iff).mp
    exact congrArg Subtype.val hsubtype
  have hlength : remaining.length ≤ occurrences.length := by
    simpa using Fintype.card_le_of_injective fromRemaining hfromRemaining
  have hsource : source.val ∈ vertices := by
    exact model.base.vertexEnumeration.complete source.property
  have herase : remaining.length + 1 = vertices.length := by
    exact List.length_erase_add_one hsource
  change vertices.length ≤ occurrences.length + 1
  omega

/-- Summing indexed row lengths is exactly the directed edge-occurrence count `m`. -/
theorem sum_indexedRowLength_finRange
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph) :
    ((List.finRange (model.base.vertexEnumeration.vertices graph).length).map
        (indexedRowLength model graph index)).sum =
      model.directedEdgeOccurrenceCount graph := by
  rw [WeightedResourceModel.directedEdgeOccurrenceCount_eq_weightedAdjacencyEntryCount]
  unfold WeightedResourceModel.weightedAdjacencyEntryCount indexedRowLength
  have hperm := (decoded_finRange_perm_vertices model graph index).map
    (fun vertex =>
      (model.weightedNeighborAccess.outEdges graph vertex).length)
  simpa [Model.indexedOutgoingEdges, List.map_map, Function.comp_def] using hperm.sum_eq

/-- A complete loop settles every dense name, in an unspecified tie-compatible order. -/
theorem completeLoop_settled_perm_finRange
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length) :
    let initial := Model.initializeState
      (model.base.vertexEnumeration.vertices graph).length Edge Weight source |>.2
    let final := (Operational.execute model graph index
      (dijkstraLoop (Edge := Edge) (Weight := Weight)
        (model.base.vertexEnumeration.vertices graph).length) initial).2
    List.Perm final.settled
      (List.finRange (model.base.vertexEnumeration.vertices graph).length) := by
  let n := (model.base.vertexEnumeration.vertices graph).length
  let initial := (Model.initializeState n Edge Weight source).2
  let final := (Operational.execute model graph index
    (dijkstraLoop (Edge := Edge) (Weight := Weight) n) initial).2
  have hinitial : Operational.QueueInvariant initial :=
    Operational.initializeState_queueInvariant (Edge := Edge) n source
  have hinitialSize : initial.heap.H.size = n :=
    Operational.initializeState_heap_size (Edge := Edge) n source
  have hloop := Operational.dijkstraLoop_queueInvariant
    model graph index n initial hinitial (by omega)
  dsimp only at hloop
  have hfinalInvariant : Operational.QueueInvariant final := hloop.1
  have hfinalSize : final.heap.H.size = 0 := by
    have hsize := hloop.2.1
    change final.heap.H.size + n = initial.heap.H.size at hsize
    omega
  have hall : ∀ name : Fin n, name ∈ final.settled := by
    intro name
    by_contra hnot
    have hactive := (hfinalInvariant.active_iff_not_settled name).2 hnot
    have hcontents :=
      (KleinbergPriorityQueue.Heap.contains_eq_true_iff_exists_contents
        final.heap hfinalInvariant.wellFormed.2.2 name).1 hactive
    rcases hcontents with ⟨key, hkey⟩
    unfold KleinbergPriorityQueue.Heap.contents at hkey
    cases hposition : final.heap.Position name with
    | none => simp [hposition] at hkey
    | some position =>
        have hlt := KleinbergPriorityQueue.Heap.position_lt_size
          final.heap hfinalInvariant.wellFormed.2.2 hposition
        omega
  apply (List.perm_ext_iff_of_nodup hfinalInvariant.settled_nodup
    (List.nodup_finRange n)).2
  intro name
  simp [hall name]

/-- A complete initialized loop inspects exactly all `m` directed edge occurrences. -/
theorem completeLoop_relaxationCandidate_count
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length) :
    let initial := Model.initializeState
      (model.base.vertexEnumeration.vertices graph).length Edge Weight source |>.2
    operationProfile relaxationCandidateCharge
        (runFrom model graph index
          (dijkstraLoop (Edge := Edge) (Weight := Weight)
            (model.base.vertexEnumeration.vertices graph).length) initial) =
      model.directedEdgeOccurrenceCount graph := by
  let n := (model.base.vertexEnumeration.vertices graph).length
  let initial := (Model.initializeState n Edge Weight source).2
  dsimp only
  have hinitial : Operational.QueueInvariant initial :=
    Operational.initializeState_queueInvariant (Edge := Edge) n source
  have hinitialSize : initial.heap.H.size = n :=
    Operational.initializeState_heap_size (Edge := Edge) n source
  rw [dijkstraLoop_relaxationCandidate_profile
    model graph index n initial hinitial (by omega)]
  have hperm := completeLoop_settled_perm_finRange model graph index source
  dsimp only at hperm
  rw [show initial.settled = [] by rfl]
  simp only [List.length_nil, List.drop_zero]
  rw [(hperm.map (indexedRowLength model graph index)).sum_eq]
  exact sum_indexedRowLength_finRange model graph index

/-- A complete initialized loop performs exactly `n` extractions. -/
theorem completeLoop_extractMin_count
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length) :
    let n := (model.base.vertexEnumeration.vertices graph).length
    let initial := (Model.initializeState n Edge Weight source).2
    operationProfile extractMinCharge
      (runFrom model graph index
        (dijkstraLoop (Edge := Edge) (Weight := Weight) n) initial) = n := by
  let n := (model.base.vertexEnumeration.vertices graph).length
  let initial := (Model.initializeState n Edge Weight source).2
  dsimp only
  apply dijkstraLoop_extractMin_profile
    model graph index n initial
    (Operational.initializeState_queueInvariant (Edge := Edge) n source)
  rw [Operational.initializeState_heap_size (Edge := Edge) n source]

/-- A complete initialized loop requests at most `m` key changes. -/
theorem completeLoop_changeKey_count_le
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length) :
    let n := (model.base.vertexEnumeration.vertices graph).length
    let initial := (Model.initializeState n Edge Weight source).2
    operationProfile changeKeyCharge
        (runFrom model graph index
          (dijkstraLoop (Edge := Edge) (Weight := Weight) n) initial) ≤
      model.directedEdgeOccurrenceCount graph := by
  let n := (model.base.vertexEnumeration.vertices graph).length
  let initial := (Model.initializeState n Edge Weight source).2
  dsimp only
  exact (dijkstraLoop_changeKey_profile_le_relaxationCandidate
    model graph index n initial).trans_eq
      (completeLoop_relaxationCandidate_count model graph index source)

/-- Initialization has zero weight in any profile satisfying the displayed hypothesis. -/
theorem dijkstra_profile_eq_loop
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length)
    (charge : (Signature
      (model.base.vertexEnumeration.vertices graph).length Edge Weight).A → Nat)
    (hinitialize : charge (.initialize source) = 0) :
    operationProfile charge
        (runFrom model graph index
          (dijkstra (model.base.vertexEnumeration.vertices graph).length source)
          (Model.semantics model graph index).initialState) =
      operationProfile charge
        (runFrom model graph index
          (dijkstraLoop (Edge := Edge) (Weight := Weight)
            (model.base.vertexEnumeration.vertices graph).length)
          (Model.initializeState
            (model.base.vertexEnumeration.vertices graph).length Edge Weight source).2) := by
  simp only [dijkstra]
  rw [runFrom_bind, operationProfile_bind]
  have hprofile :
      operationProfile charge
        (runFrom model graph index («initialize» source)
          (Model.semantics model graph index).initialState) =
        charge (.initialize source) := by
    rfl
  rw [hprofile, hinitialize]
  simp only [Nat.zero_add, ResourceAware.Program.runFrom_ret]
  rw [show (Model.semantics model graph index).evalFrom
      («initialize» source) (Model.semantics model graph index).initialState =
    (Model.semantics model graph index).step
      (.initialize source) (Model.semantics model graph index).initialState by rfl]
  rw [show (Model.semantics model graph index).step
      (.initialize source) (Model.semantics model graph index).initialState =
    (ULift.up true,
      (Model.initializeState
        (model.base.vertexEnumeration.vertices graph).length Edge Weight source).2) by
    dsimp [Model.semantics]
    rw [Operational.initializeState_success (Edge := Edge)]
    rfl]
  rfl

/-- The complete profile splits into its single initialization event and initialized loop. -/
theorem dijkstra_profile_eq_initialize_add_loop
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length)
    (charge : (Signature
      (model.base.vertexEnumeration.vertices graph).length Edge Weight).A → Nat) :
    operationProfile charge
        (runFrom model graph index
          (dijkstra (model.base.vertexEnumeration.vertices graph).length source)
          (Model.semantics model graph index).initialState) =
      charge (.initialize source) +
        operationProfile charge
          (runFrom model graph index
            (dijkstraLoop (Edge := Edge) (Weight := Weight)
              (model.base.vertexEnumeration.vertices graph).length)
            (Model.initializeState
              (model.base.vertexEnumeration.vertices graph).length Edge Weight source).2) := by
  simp only [dijkstra]
  rw [runFrom_bind, operationProfile_bind]
  have hprofile :
      operationProfile charge
        (runFrom model graph index («initialize» source)
          (Model.semantics model graph index).initialState) =
        charge (.initialize source) := by
    rfl
  rw [hprofile]
  simp only [ResourceAware.Program.runFrom_ret]
  rw [show (Model.semantics model graph index).evalFrom
      («initialize» source) (Model.semantics model graph index).initialState =
    (Model.semantics model graph index).step
      (.initialize source) (Model.semantics model graph index).initialState by rfl]
  rw [show (Model.semantics model graph index).step
      (.initialize source) (Model.semantics model graph index).initialState =
    (ULift.up true,
      (Model.initializeState
        (model.base.vertexEnumeration.vertices graph).length Edge Weight source).2) by
    dsimp [Model.semantics]
    rw [Operational.initializeState_success (Edge := Edge)]
    rfl]
  rfl

/-- The actual heap-profile cost splits into exact initialization and initialized-loop costs. -/
theorem dijkstra_heapExactCost_eq_initialize_add_loop
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length) :
    heapExactCost (Interpreter.runHeap model graph index source) =
      initializationHeapCost (model.base.vertexEnumeration.vertices graph).length +
        heapExactCost
          (heapRunFrom model graph index
            (dijkstraLoop (Edge := Edge) (Weight := Weight)
              (model.base.vertexEnumeration.vertices graph).length)
            (Model.initializeState
              (model.base.vertexEnumeration.vertices graph).length Edge Weight source).2) := by
  dsimp only [Interpreter.runHeap, ResourceAware.Program.run]
  simp only [dijkstra]
  rw [ResourceAware.Program.runFrom_bind, heapExactCost_bind]
  have hinitialize :
      heapExactCost
        (heapRunFrom model graph index («initialize» source)
          (Model.semantics model graph index).initialState) =
        initializationHeapCost
          (model.base.vertexEnumeration.vertices graph).length := by
    rfl
  rw [hinitialize]
  simp only [ResourceAware.Program.runFrom_ret]
  rw [show (Model.semantics model graph index).evalFrom
      («initialize» source) (Model.semantics model graph index).initialState =
    (Model.semantics model graph index).step
      (.initialize source) (Model.semantics model graph index).initialState by rfl]
  rw [show (Model.semantics model graph index).step
      (.initialize source) (Model.semantics model graph index).initialState =
    (ULift.up true,
      (Model.initializeState
        (model.base.vertexEnumeration.vertices graph).length Edge Weight source).2) by
    dsimp [Model.semantics]
    rw [Operational.initializeState_success (Edge := Edge)]
    rfl]
  rfl

/--
The exact cost of the actual heap-measured runner is bounded by initialization plus the
static operation envelope on the actual decomposition trace.
-/
theorem runHeap_exactCost_le_upperProfile
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length) :
    heapExactCost (Interpreter.runHeap model graph index source) ≤
      initializationHeapCost (model.base.vertexEnumeration.vertices graph).length +
        operationProfile (heapLoopUpperCharge model graph index)
          (Interpreter.runDecomposition model graph index source) := by
  rw [dijkstra_heapExactCost_eq_initialize_add_loop model graph index source]
  apply Nat.add_le_add_left
  have hloop := dijkstraLoop_heapExactCost_le_upperProfile
    model graph index
    (model.base.vertexEnumeration.vertices graph).length
    (Model.initializeState
      (model.base.vertexEnumeration.vertices graph).length Edge Weight source).2
    (Operational.initializeState_queueInvariant (Edge := Edge)
      (model.base.vertexEnumeration.vertices graph).length source)
    (by rw [Operational.initializeState_heap_size (Edge := Edge)])
  rw [show Interpreter.runDecomposition model graph index source =
    runFrom model graph index
      (dijkstra (model.base.vertexEnumeration.vertices graph).length source)
      (Model.semantics model graph index).initialState by rfl]
  rw [dijkstra_profile_eq_loop model graph index source
    (heapLoopUpperCharge model graph index) (by rfl)]
  exact hloop

/--
Kleinberg--Tardos claim (4.15), pages 141--142: the actual decomposition runner performs
exactly `n` `ExtractMin` requests and one candidate inspection per directed occurrence, with at
most one `ChangeKey` request per occurrence.
-/
theorem claim_4_15_operation_counts
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length) :
    let run := Interpreter.runDecomposition model graph index source
    operationProfile extractMinCharge run =
        (model.base.vertexEnumeration.vertices graph).length ∧
      operationProfile relaxationCandidateCharge run =
        model.directedEdgeOccurrenceCount graph ∧
      operationProfile changeKeyCharge run ≤
        model.directedEdgeOccurrenceCount graph := by
  dsimp only [Interpreter.runDecomposition, ResourceAware.Program.run]
  constructor
  · rw [dijkstra_profile_eq_loop model graph index source extractMinCharge (by rfl)]
    exact completeLoop_extractMin_count model graph index source
  constructor
  · rw [dijkstra_profile_eq_loop model graph index source
      relaxationCandidateCharge (by rfl)]
    exact completeLoop_relaxationCandidate_count model graph index source
  · rw [dijkstra_profile_eq_loop model graph index source changeKeyCharge (by rfl)]
    exact completeLoop_changeKey_count_le model graph index source

/-- In the textbook adjacency-list representation, one row request costs its row length. -/
theorem adjacencyList_indexedRowCost
    (base : ResourceModel G V)
    (edgeView : WeightedEdgeView base.interface Edge Weight)
    (neighbors : WeightedNeighborAccess edgeView)
    (graph : G)
    (index : VertexIndex base.interface base.vertexEnumeration graph)
    (name : Fin (base.vertexEnumeration.vertices graph).length) :
    let model := WeightedResourceModel.ofAdjacencyList base edgeView neighbors
    model.weightedNeighborCost graph (index.decode name).val =
      indexedRowLength model graph index name := by
  simp [WeightedResourceModel.ofAdjacencyList, indexedRowLength,
    Model.indexedOutgoingEdges]

/--
The exact claim-(4.15) decomposition for any representation whose row cost is its row length.
-/
theorem claim_4_15_unitRowCost
    (model : WeightedResourceModel G V Edge Weight)
    (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length)
    (hrowCost : ∀ name,
      model.weightedNeighborCost graph (index.decode name).val =
        indexedRowLength model graph index name) :
    let run := Interpreter.runDecomposition model graph index source
    let m := model.directedEdgeOccurrenceCount graph
    let n := model.base.vertexEnumeration.vertices graph |>.length
    operationProfile (outgoingRowWorkCharge model graph index) run = m ∧
      operationProfile relaxationCandidateCharge run = m ∧
      operationProfile (outgoingRowWorkCharge model graph index) run +
          operationProfile relaxationCandidateCharge run = 2 * m ∧
      operationProfile extractMinCharge run = n ∧
      operationProfile changeKeyCharge run ≤ m := by
  let run := Interpreter.runDecomposition model graph index source
  let m := model.directedEdgeOccurrenceCount graph
  let n := model.base.vertexEnumeration.vertices graph |>.length
  have hcounts := claim_4_15_operation_counts model graph index source
  have hrowLoop :
      operationProfile (outgoingRowWorkCharge model graph index)
          (runFrom model graph index
            (dijkstraLoop (Edge := Edge) (Weight := Weight) n)
            (Model.initializeState n Edge Weight source).2) =
        operationProfile relaxationCandidateCharge
          (runFrom model graph index
            (dijkstraLoop (Edge := Edge) (Weight := Weight) n)
            (Model.initializeState n Edge Weight source).2) := by
    apply dijkstraLoop_outgoingRowWork_eq_relaxationCandidate
    exact hrowCost
  have hrow : operationProfile (outgoingRowWorkCharge model graph index) run = m := by
    rw [show run =
      runFrom model graph index (dijkstra n source)
        (Model.semantics model graph index).initialState by rfl]
    rw [dijkstra_profile_eq_loop model graph index source
      (outgoingRowWorkCharge model graph index) (by rfl)]
    rw [hrowLoop]
    exact completeLoop_relaxationCandidate_count model graph index source
  dsimp only at hcounts
  rcases hcounts with ⟨hextract, hcandidate, hchange⟩
  refine ⟨hrow, hcandidate, ?_, hextract, hchange⟩
  rw [hrow, hcandidate]
  omega

/--
Kleinberg--Tardos claim (4.15), pages 141--142, for the named adjacency-list
representation: after initialization, the actual interpreted run performs exactly `m`
row-scan work and `m` relaxation inspections, hence `2m` non-queue work, exactly `n`
`ExtractMin` requests, and at most `m` `ChangeKey` requests.
-/
theorem claim_4_15_adjacencyList
    (base : ResourceModel G V)
    (edgeView : WeightedEdgeView base.interface Edge Weight)
    (neighbors : WeightedNeighborAccess edgeView)
    (graph : G)
    (index : VertexIndex base.interface base.vertexEnumeration graph)
    (source : Fin (base.vertexEnumeration.vertices graph).length) :
    let model := WeightedResourceModel.ofAdjacencyList base edgeView neighbors
    let run := Interpreter.runDecomposition model graph index source
    let m := model.directedEdgeOccurrenceCount graph
    let n := base.vertexEnumeration.vertices graph |>.length
    operationProfile (outgoingRowWorkCharge model graph index) run = m ∧
      operationProfile relaxationCandidateCharge run = m ∧
      operationProfile (outgoingRowWorkCharge model graph index) run +
          operationProfile relaxationCandidateCharge run = 2 * m ∧
      operationProfile extractMinCharge run = n ∧
      operationProfile changeKeyCharge run ≤ m := by
  apply claim_4_15_unitRowCost
  intro name
  exact adjacencyList_indexedRowCost base edgeView neighbors graph index name

/-- Decompose the static heap envelope into the four post-initialization source metrics. -/
theorem heapLoopUpperProfile_eq_components
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (computation : TraceM
      (ResourceAware.Program.Event
        (Signature
          (model.base.vertexEnumeration.vertices graph).length Edge Weight).A Nat) α) :
    operationProfile (heapLoopUpperCharge model graph index) computation =
      KleinbergPriorityQueue.logarithmicCost
          (model.base.vertexEnumeration.vertices graph).length *
        operationProfile extractMinCharge computation +
      (operationProfile (outgoingRowWorkCharge model graph index) computation +
        (operationProfile relaxationCandidateCharge computation +
          KleinbergPriorityQueue.logarithmicCost
              (model.base.vertexEnumeration.vertices graph).length *
            operationProfile changeKeyCharge computation)) := by
  let logarithmic :=
    KleinbergPriorityQueue.logarithmicCost
      (model.base.vertexEnumeration.vertices graph).length
  calc
    operationProfile (heapLoopUpperCharge model graph index) computation =
        operationProfile
          (fun operation =>
            logarithmic * extractMinCharge operation +
              (outgoingRowWorkCharge model graph index operation +
                (relaxationCandidateCharge operation +
                  logarithmic * changeKeyCharge operation)))
          computation := by
            apply operationProfile_congr
            intro operation
            cases operation <;>
              simp [heapLoopUpperCharge, extractMinCharge, outgoingRowWorkCharge,
                relaxationCandidateCharge, changeKeyCharge, logarithmic]
    _ = operationProfile (fun operation =>
          logarithmic * extractMinCharge operation) computation +
        operationProfile
          (fun operation =>
            outgoingRowWorkCharge model graph index operation +
              (relaxationCandidateCharge operation +
                logarithmic * changeKeyCharge operation))
          computation := operationProfile_add _ _ _
    _ = logarithmic * operationProfile extractMinCharge computation +
        operationProfile
          (fun operation =>
            outgoingRowWorkCharge model graph index operation +
              (relaxationCandidateCharge operation +
                logarithmic * changeKeyCharge operation))
          computation := by rw [operationProfile_mul]
    _ = logarithmic * operationProfile extractMinCharge computation +
        (operationProfile (outgoingRowWorkCharge model graph index) computation +
          operationProfile
            (fun operation =>
              relaxationCandidateCharge operation +
                logarithmic * changeKeyCharge operation)
            computation) := by rw [operationProfile_add]
    _ = logarithmic * operationProfile extractMinCharge computation +
        (operationProfile (outgoingRowWorkCharge model graph index) computation +
          (operationProfile relaxationCandidateCharge computation +
            operationProfile
              (fun operation => logarithmic * changeKeyCharge operation)
              computation)) := by rw [operationProfile_add]
    _ = logarithmic * operationProfile extractMinCharge computation +
        (operationProfile (outgoingRowWorkCharge model graph index) computation +
          (operationProfile relaxationCandidateCharge computation +
            logarithmic * operationProfile changeKeyCharge computation)) := by
              rw [operationProfile_mul]

/--
Closed finite upper bound connected to the actual logarithmic-heap runner. This is the
implementation-to-asymptotic bridge for the heap corollary following claim (4.15).
-/
def heapCostUpperBound (n m : Nat) : Nat :=
  initializationHeapCost n +
    n * KleinbergPriorityQueue.logarithmicCost n +
    2 * m +
    m * KleinbergPriorityQueue.logarithmicCost n

/--
The actual heap-measured adjacency-list run is bounded by initialization, `n` logarithmic
extractions, `2m` non-queue work, and at most `m` logarithmic key changes.
-/
theorem claim_4_15_heap_exact_bound
    (base : ResourceModel G V)
    (edgeView : WeightedEdgeView base.interface Edge Weight)
    (neighbors : WeightedNeighborAccess edgeView)
    (graph : G)
    (index : VertexIndex base.interface base.vertexEnumeration graph)
    (source : Fin (base.vertexEnumeration.vertices graph).length) :
    let model := WeightedResourceModel.ofAdjacencyList base edgeView neighbors
    let n := base.vertexEnumeration.vertices graph |>.length
    let m := model.directedEdgeOccurrenceCount graph
    heapExactCost (Interpreter.runHeap model graph index source) ≤
      heapCostUpperBound n m := by
  let model := WeightedResourceModel.ofAdjacencyList base edgeView neighbors
  let n := base.vertexEnumeration.vertices graph |>.length
  let m := model.directedEdgeOccurrenceCount graph
  let run := Interpreter.runDecomposition model graph index source
  have hrun := runHeap_exactCost_le_upperProfile model graph index source
  have hclaim := claim_4_15_adjacencyList
    base edgeView neighbors graph index source
  dsimp only at hclaim
  rcases hclaim with ⟨hrow, hcandidate, _, hextract, hchange⟩
  have hprofile := heapLoopUpperProfile_eq_components model graph index run
  have hchangeLog :=
    Nat.mul_le_mul_left (KleinbergPriorityQueue.logarithmicCost n) hchange
  rw [hprofile, hextract, hrow, hcandidate] at hrun
  unfold heapCostUpperBound
  dsimp only
  let logarithmic := KleinbergPriorityQueue.logarithmicCost n
  let changes := operationProfile changeKeyCharge run
  have hcomponents :
      logarithmic * n + (m + (m + logarithmic * changes)) ≤
        n * logarithmic + 2 * m + m * logarithmic := by
    calc
      logarithmic * n + (m + (m + logarithmic * changes))
          ≤ logarithmic * n + (m + (m + logarithmic * m)) :=
        Nat.add_le_add_left
          (Nat.add_le_add_left (Nat.add_le_add_left hchangeLog m) m)
          (logarithmic * n)
      _ = n * logarithmic + 2 * m + m * logarithmic := by
        simp only [Nat.two_mul]
        ac_rfl
  apply hrun.trans
  simpa only [model, n, m, logarithmic, changes,
    WeightedResourceModel.ofAdjacencyList, Nat.add_assoc] using
    Nat.add_le_add_left hcomponents (initializationHeapCost n)

theorem one_le_logarithmicCost (n : Nat) :
    1 ≤ KleinbergPriorityQueue.logarithmicCost n := by
  simp [KleinbergPriorityQueue.logarithmicCost]

/-- A convenient uniform constant bound for nonempty vertex sets. -/
theorem heapCostUpperBound_le_six_mul (n m : Nat) (hn : 1 ≤ n) :
    heapCostUpperBound n m ≤
      6 * ((n + m) * KleinbergPriorityQueue.logarithmicCost n) := by
  let logarithmic := KleinbergPriorityQueue.logarithmicCost n
  have hlog : 1 ≤ logarithmic := one_le_logarithmicCost n
  have hnlog : n ≤ n * logarithmic := by
    simpa using Nat.mul_le_mul_left n hlog
  have hmlog : m ≤ m * logarithmic := by
    simpa using Nat.mul_le_mul_left m hlog
  have honelog : 1 ≤ n * logarithmic := hn.trans hnlog
  have hinitialize := initializationHeapCost_le n
  unfold heapCostUpperBound
  dsimp only [logarithmic] at hnlog hmlog honelog ⊢
  nlinarith

/-- Real comparison function for the `O((m+n) log(n+1))` heap envelope. -/
def heapCostReference (input : Nat × Nat) : Real :=
  ((input.1 + input.2) *
    KleinbergPriorityQueue.logarithmicCost input.1 : Nat)

/--
The finite envelope connected to `runHeap` above is
`O((m+n) log(n+1))` in mathlib's asymptotic notation.
-/
theorem heapCostUpperBound_isBigO :
    (fun input : Nat × Nat =>
      (heapCostUpperBound input.1 input.2 : Real)) =O[atTop]
        heapCostReference := by
  refine IsBigO.of_bound 6 ?_
  filter_upwards [eventually_ge_atTop ((1, 0) : Nat × Nat)] with input hinput
  have hbound := heapCostUpperBound_le_six_mul input.1 input.2 hinput.1
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  have hupperNonnegative :
      (0 : Real) ≤ heapCostUpperBound input.1 input.2 := by positivity
  have hrefNonnegative : (0 : Real) ≤ heapCostReference input := by
    unfold heapCostReference
    positivity
  rw [abs_of_nonneg hupperNonnegative, abs_of_nonneg hrefNonnegative]
  unfold heapCostReference
  exact_mod_cast hbound

/--
For nontrivial reachable-input sizes, `n ≤ m + 1` absorbs the `n` term into `m`.
-/
theorem heapCostUpperBound_le_eighteen_mul (n m : Nat)
    (hn : 2 ≤ n) (hnm : n ≤ m + 1) :
    heapCostUpperBound n m ≤
      18 * (m * KleinbergPriorityQueue.logarithmicCost n) := by
  have hm : 1 ≤ m := by omega
  have hsum : n + m ≤ 3 * m := by omega
  calc
    heapCostUpperBound n m
        ≤ 6 * ((n + m) * KleinbergPriorityQueue.logarithmicCost n) :=
      heapCostUpperBound_le_six_mul n m (by omega)
    _ ≤ 6 * ((3 * m) * KleinbergPriorityQueue.logarithmicCost n) :=
      Nat.mul_le_mul_left 6
        (Nat.mul_le_mul_right
          (KleinbergPriorityQueue.logarithmicCost n) hsum)
    _ = 18 * (m * KleinbergPriorityQueue.logarithmicCost n) := by ring

/-- Size pairs satisfying the nontrivial reachable-graph edge-count inequality. -/
def reachableInputSet : Set (Nat × Nat) :=
  {input | 2 ≤ input.1 ∧ input.1 ≤ input.2 + 1}

/-- The at-top filter restricted to the textbook's reachable, nontrivial input sizes. -/
def reachableInputFilter : Filter (Nat × Nat) :=
  atTop ⊓ Filter.principal reachableInputSet

/-- Real comparison function for the textbook `m log n` form. -/
def reachableHeapCostReference (input : Nat × Nat) : Real :=
  (input.2 * KleinbergPriorityQueue.logarithmicCost input.1 : Nat)

/--
Heap corollary following Kleinberg--Tardos claim (4.15), page 142: on nontrivial
reachable-input sizes (`n ≤ m + 1`), the run-connected finite envelope is `O(m log n)`.
-/
theorem claim_4_15_heapCostUpperBound_isBigO :
    (fun input : Nat × Nat =>
      (heapCostUpperBound input.1 input.2 : Real)) =O[reachableInputFilter]
        reachableHeapCostReference := by
  refine IsBigO.of_bound 18 ?_
  rw [reachableInputFilter, eventually_inf_principal]
  exact Eventually.of_forall fun input hinput => by
    have hbound := heapCostUpperBound_le_eighteen_mul
      input.1 input.2 hinput.1 hinput.2
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have hupperNonnegative :
        (0 : Real) ≤ heapCostUpperBound input.1 input.2 := by positivity
    have hrefNonnegative : (0 : Real) ≤ reachableHeapCostReference input := by
      unfold reachableHeapCostReference
      positivity
    rw [abs_of_nonneg hupperNonnegative, abs_of_nonneg hrefNonnegative]
    unfold reachableHeapCostReference
    exact_mod_cast hbound

/--
End-to-end heap corollary following Kleinberg--Tardos claim (4.15), page 142.

Reachability derives `n ≤ m + 1`; together with `2 ≤ n`, it places the actual run's
finite bound in the restricted input family for the proved `O(m log n)` theorem.
-/
theorem claim_4_15_heap_corollary
    (base : ResourceModel G V)
    (edgeView : WeightedEdgeView base.interface Edge Weight)
    (neighbors : WeightedNeighborAccess edgeView)
    (graph : G)
    (index : VertexIndex base.interface base.vertexEnumeration graph)
    (source : Fin (base.vertexEnumeration.vertices graph).length)
    (hreachable : ∀ vertex ∈ base.vertexEnumeration.vertices graph,
      Reachable base.interface graph (index.decode source).val vertex)
    (hnontrivial : 2 ≤ (base.vertexEnumeration.vertices graph).length) :
    let model := WeightedResourceModel.ofAdjacencyList base edgeView neighbors
    let n := (base.vertexEnumeration.vertices graph).length
    let m := model.directedEdgeOccurrenceCount graph
    heapExactCost (Interpreter.runHeap model graph index source) ≤
        heapCostUpperBound n m ∧
      (n, m) ∈ reachableInputSet ∧
      ((fun input : Nat × Nat =>
          (heapCostUpperBound input.1 input.2 : Real)) =O[reachableInputFilter]
        reachableHeapCostReference) := by
  let model := WeightedResourceModel.ofAdjacencyList base edgeView neighbors
  let n := (base.vertexEnumeration.vertices graph).length
  let m := model.directedEdgeOccurrenceCount graph
  have hexact := claim_4_15_heap_exact_bound
    base edgeView neighbors graph index source
  have hnm : n ≤ m + 1 := by
    apply vertexCount_le_directedEdgeOccurrenceCount_add_one_of_reachable
      model graph (index.decode source)
    exact hreachable
  exact ⟨hexact, ⟨hnontrivial, hnm⟩, claim_4_15_heapCostUpperBound_isBigO⟩

end Complexity

end KleinbergDijkstra
