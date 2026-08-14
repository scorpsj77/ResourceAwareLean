/-
Copyright (c) 2026 Daya Kumaran. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daya Kumaran
-/
import TextbookAlgorithms.KleinbergTardos.Chapter04.Dijkstra.ResourceModel
import ResourceAware.Algorithms.ShortestPaths.Specification
import ResourceAware.Foundations.PriorityQueue.Correctness
import Mathlib.Combinatorics.Quiver.Path.Decomposition
import Mathlib.Combinatorics.Quiver.Path.Vertices

/-!
# Correctness of Kleinberg--Tardos Dijkstra

This file proves the operational queue and active/settled invariants, the settled-prefix cut
argument, exact predecessor reconstruction, and the end-to-end form of claim (4.14). The final
theorems cover the pure runner and both cost-instrumented runners under the stated generic weight
and all-vertices-reachable assumptions.
-/

universe u v w x

namespace KleinbergDijkstra

open ResourceAware
open ResourceAware.Graph
open ResourceAware.Algorithms.ShortestPaths

namespace Operational

variable {G : Type u} {V : Type v} {Edge : Type w} {Weight : Type x}
variable [AddCommMonoid Weight] [LinearOrder Weight] [CanonicallyOrderedAdd Weight]

/-- Pure execution from an explicit Dijkstra state. -/
abbrev execute (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (program : Program
      (model.base.vertexEnumeration.vertices graph).length Edge Weight α)
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight) :=
  ResourceAware.Program.Semantics.evalFrom (Model.semantics model graph index)
    program state

theorem execute_bind
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (program : Program
      (model.base.vertexEnumeration.vertices graph).length Edge Weight α)
    (next : α → Program
      (model.base.vertexEnumeration.vertices graph).length Edge Weight β)
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight) :
    execute model graph index (program >>= next) state =
      let (result, state') := execute model graph index program state
      execute model graph index (next result) state' :=
  ResourceAware.Program.Semantics.evalFrom_bind _ _ _ _

/-- Heap representation and active/settled partition used by both proof passes. -/
structure QueueInvariant
    (state : Model.State n Edge Weight) : Prop where
  wellFormed : state.heap.WellFormed
  active_iff_not_settled : ∀ name,
    state.heap.contains name = true ↔ name ∉ state.settled
  settled_nodup : state.settled.Nodup

omit [LinearOrder Weight] [CanonicallyOrderedAdd Weight] in
private theorem initialEntries_names (n : Nat) (source : Fin n) :
    ((Model.initialEntries Weight n source).map
      KleinbergPriorityQueue.Entry.name) = List.finRange n := by
  simp [Model.initialEntries, Function.comp_def]

omit [CanonicallyOrderedAdd Weight] in
theorem initializeState_success (n : Nat) (source : Fin n) :
    (Model.initializeState n Edge Weight source).1 = true := by
  apply KleinbergPriorityQueue.Heap.insertAll_eligible_success
  · change 0 + (Model.initialEntries Weight n source).length ≤ n
    simp [Model.initialEntries]
  · simpa [initialEntries_names] using List.nodup_finRange n
  · simp [KleinbergPriorityQueue.Heap.startHeap, KleinbergPriorityQueue.Heap.contains]

omit [CanonicallyOrderedAdd Weight] in
private theorem initializeState_wellFormed (n : Nat) (source : Fin n) :
    (Model.initializeState n Edge Weight source).2.heap.WellFormed := by
  apply KleinbergPriorityQueue.Heap.insertAll_success_wellFormed
  · exact KleinbergPriorityQueue.Heap.startHeap_wellFormed n (Distance Weight)
  · exact initializeState_success (Edge := Edge) n source

omit [CanonicallyOrderedAdd Weight] in
private theorem initializeState_contents (n : Nat) (source name : Fin n) :
    (Model.initializeState n Edge Weight source).2.heap.contents name =
      some (if name = source then 0 else ⊤) := by
  let entry : KleinbergPriorityQueue.Entry n (Distance Weight) :=
    { name
      key := if name = source then 0 else ⊤ }
  change
    ((KleinbergPriorityQueue.Heap.startHeap n (Distance Weight)).insertAll
      (Model.initialEntries Weight n source)).1.contents name = some entry.key
  simpa [entry] using
    KleinbergPriorityQueue.Heap.insertAll_eligible_contents
      (KleinbergPriorityQueue.Heap.startHeap n (Distance Weight))
      (KleinbergPriorityQueue.Heap.startHeap_wellFormed n (Distance Weight)).2.2
      (Model.initialEntries Weight n source)
      (by
        change 0 + (Model.initialEntries Weight n source).length ≤ n
        simp [Model.initialEntries])
      (by simpa [initialEntries_names] using List.nodup_finRange n)
      (by
        simp [KleinbergPriorityQueue.Heap.startHeap,
          KleinbergPriorityQueue.Heap.contains])
      entry
      (by simp [entry, Model.initialEntries])

omit [CanonicallyOrderedAdd Weight] in
/-- Successful initialization establishes a well-formed full queue and empty settled set. -/
theorem initializeState_queueInvariant (n : Nat) (source : Fin n) :
    QueueInvariant (Model.initializeState n Edge Weight source).2 := by
  constructor
  · exact initializeState_wellFormed (Edge := Edge) n source
  · intro name
    constructor
    · intro
      simp [Model.initializeState]
    · intro
      apply (KleinbergPriorityQueue.Heap.contains_eq_true_iff_exists_contents
        _ (initializeState_wellFormed (Edge := Edge) n source).2.2 name).2
      exact ⟨_, initializeState_contents (Edge := Edge) n source name⟩
  · simp [Model.initializeState]

omit [CanonicallyOrderedAdd Weight] in
/-- Initialization inserts all `n` dense names. -/
theorem initializeState_heap_size (n : Nat) (source : Fin n) :
    (Model.initializeState n Edge Weight source).2.heap.H.size = n := by
  change
    ((KleinbergPriorityQueue.Heap.startHeap n (Distance Weight)).insertAll
      (Model.initialEntries Weight n source)).1.H.size = n
  rw [KleinbergPriorityQueue.Heap.insertAll_success_size _ _
    (initializeState_success (Edge := Edge) n source)]
  simp [KleinbergPriorityQueue.Heap.startHeap, Model.initialEntries]

/-- Row processing never changes the active-name set or settlement order. -/
theorem processEdges_queueInvariant
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length)
    (sourceDistance : Distance Weight)
    (row : List (IndexedOutgoingEdge
      (model.base.vertexEnumeration.vertices graph).length Edge Weight))
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (hinvariant : QueueInvariant state) :
    QueueInvariant
      (execute model graph index (processEdges source sourceDistance row) state).2 := by
  induction row generalizing state with
  | nil => simpa [processEdges]
  | cons outgoing rest ih =>
      simp only [processEdges]
      rw [execute_bind]
      rw [show execute model graph index
          (relaxationCandidate sourceDistance outgoing) state =
        (Model.semantics model graph index).step
          (.relaxationCandidate sourceDistance outgoing) state by rfl]
      simp only [Model.semantics]
      split
      · exact ih state hinvariant
      · rename_i _ value _
        rw [execute_bind]
        let predecessor : Predecessor
            (model.base.vertexEnumeration.vertices graph).length Edge Weight :=
          ⟨source, outgoing.target, outgoing.edge, outgoing.weight⟩
        have hstep : QueueInvariant
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
        rw [show execute model graph index
            (changeKey predecessor value) state =
          (Model.semantics model graph index).step
            (.changeKey predecessor value) state by rfl]
        exact ih _ hstep

/-- Row processing changes keys but not the number of active names. -/
theorem processEdges_heap_size
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length)
    (sourceDistance : Distance Weight)
    (row : List (IndexedOutgoingEdge
      (model.base.vertexEnumeration.vertices graph).length Edge Weight))
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight) :
    (execute model graph index
      (processEdges source sourceDistance row) state).2.heap.H.size =
        state.heap.H.size := by
  induction row generalizing state with
  | nil => rfl
  | cons outgoing rest ih =>
      simp only [processEdges]
      rw [execute_bind]
      rw [show execute model graph index
          (relaxationCandidate sourceDistance outgoing) state =
        (Model.semantics model graph index).step
          (.relaxationCandidate sourceDistance outgoing) state by rfl]
      simp only [Model.semantics]
      split
      · exact ih state
      · rename_i _ value _
        rw [execute_bind]
        let predecessor : Predecessor
            (model.base.vertexEnumeration.vertices graph).length Edge Weight :=
          ⟨source, outgoing.target, outgoing.edge, outgoing.weight⟩
        rw [show execute model graph index (changeKey predecessor value) state =
          (Model.semantics model graph index).step
            (.changeKey predecessor value) state by rfl]
        rw [ih]
        dsimp [Model.semantics, predecessor]
        split
        · exact KleinbergPriorityQueue.Heap.changeKey_size _ _ _
        · rfl

/-- Row processing does not add a settled vertex. -/
theorem processEdges_settled
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length)
    (sourceDistance : Distance Weight)
    (row : List (IndexedOutgoingEdge
      (model.base.vertexEnumeration.vertices graph).length Edge Weight))
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight) :
    (execute model graph index
      (processEdges source sourceDistance row) state).2.settled = state.settled := by
  induction row generalizing state with
  | nil => rfl
  | cons outgoing rest ih =>
      simp only [processEdges]
      rw [execute_bind]
      rw [show execute model graph index
          (relaxationCandidate sourceDistance outgoing) state =
        (Model.semantics model graph index).step
          (.relaxationCandidate sourceDistance outgoing) state by rfl]
      simp only [Model.semantics]
      split
      · exact ih state
      · rename_i _ value _
        rw [execute_bind]
        let predecessor : Predecessor
            (model.base.vertexEnumeration.vertices graph).length Edge Weight :=
          ⟨source, outgoing.target, outgoing.edge, outgoing.weight⟩
        rw [show execute model graph index (changeKey predecessor value) state =
          (Model.semantics model graph index).step
            (.changeKey predecessor value) state by rfl]
        rw [ih]
        dsimp [Model.semantics, predecessor]
        split <;> rfl

/-- A nonempty semantic extraction preserves the queue partition and appends its root once. -/
theorem extractMin_queueInvariant
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (hinvariant : QueueInvariant state) (hne : 0 < state.heap.H.size) :
    let extracted := state.heap.H[0]
    let next := ((Model.semantics model graph index).step (.extractMin) state).2
    ((Model.semantics model graph index).step (.extractMin) state).1 =
        ULift.up (some extracted) ∧
      QueueInvariant next ∧
      next.heap.H.size + 1 = state.heap.H.size ∧
      next.settled = state.settled ++ [extracted.name] := by
  let extracted := state.heap.H[0]
  have hresult :=
    KleinbergPriorityQueue.Heap.extractMin_nonempty_result state.heap hne
  have hrootActive : state.heap.contains extracted.name = true := by
    apply (KleinbergPriorityQueue.Heap.contains_eq_true_iff_exists_contents
      state.heap hinvariant.wellFormed.2.2 extracted.name).2
    refine ⟨extracted.key, ?_⟩
    have hposition := hinvariant.wellFormed.2.2.1 ⟨0, hne⟩
    have hposition' : state.heap.Position extracted.name = some 0 := by
      simpa [extracted] using hposition
    simp [KleinbergPriorityQueue.Heap.contents, hposition', extracted,
      Array.getElem?_eq_getElem hne]
  have hrootFresh : extracted.name ∉ state.settled :=
    (hinvariant.active_iff_not_settled extracted.name).1 hrootActive
  dsimp [Model.semantics]
  rw [hresult]
  constructor
  · rfl
  constructor
  · constructor
    · exact KleinbergPriorityQueue.Heap.extractMin_wellFormed
        state.heap hinvariant.wellFormed hne
    · intro name
      rw [KleinbergPriorityQueue.Heap.extractMin_contains_eq_true_iff
        state.heap hinvariant.wellFormed hne name]
      rw [hinvariant.active_iff_not_settled name]
      simp
      tauto
    · exact hinvariant.settled_nodup.append
        (by simp) (by simpa [List.disjoint_singleton] using hrootFresh)
  constructor
  · exact KleinbergPriorityQueue.Heap.extractMin_nonempty_size state.heap hne
  · rfl

private theorem execute_dijkstraLoop_succ
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (fuel : Nat)
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (hne : 0 < state.heap.H.size) :
    let extracted := state.heap.H[0]
    let afterExtract :=
      ((Model.semantics model graph index).step (.extractMin) state).2
    let afterRow := (execute model graph index
      (processEdges extracted.name extracted.key
        (Model.indexedOutgoingEdges model graph index extracted.name)) afterExtract).2
    execute model graph index
      (dijkstraLoop (Edge := Edge) (Weight := Weight) (fuel + 1)) state =
        execute model graph index
          (dijkstraLoop (Edge := Edge) (Weight := Weight) fuel) afterRow := by
  let extracted := state.heap.H[0]
  let afterExtract :=
    ((Model.semantics model graph index).step (.extractMin) state).2
  have hresult := KleinbergPriorityQueue.Heap.extractMin_nonempty_result state.heap hne
  simp only [dijkstraLoop]
  rw [execute_bind]
  rw [show execute model graph index
      (extractMin (Edge := Edge) (Weight := Weight)) state =
    (Model.semantics model graph index).step (.extractMin) state by rfl]
  have hstep : (Model.semantics model graph index).step
      (.extractMin : Op
        (model.base.vertexEnumeration.vertices graph).length Edge Weight) state =
        (ULift.up (some extracted), afterExtract) := by
    apply Prod.ext
    · dsimp [Model.semantics, extracted]
      rw [hresult]
    · rfl
  rw [hstep]
  simp only
  rw [execute_bind]
  rw [show execute model graph index (outgoingEdges extracted.name) afterExtract =
    (Model.semantics model graph index).step
      (.outgoingEdges extracted.name) afterExtract by rfl]
  rw [show (Model.semantics model graph index).step
      (.outgoingEdges extracted.name) afterExtract =
    (Model.indexedOutgoingEdges model graph index extracted.name, afterExtract) by rfl]
  simp only
  rw [execute_bind]

/--
Vertex-count fuel cannot encounter an empty queue early: every iteration extracts one new name,
and row processing preserves the active-name partition.
-/
theorem dijkstraLoop_queueInvariant
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (fuel : Nat)
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (hinvariant : QueueInvariant state) (hfuel : fuel ≤ state.heap.H.size) :
    let final := (execute model graph index
      (dijkstraLoop (Edge := Edge) (Weight := Weight) fuel) state).2
    QueueInvariant final ∧
      final.heap.H.size + fuel = state.heap.H.size ∧
      final.settled.length = state.settled.length + fuel ∧
      state.settled.IsPrefix final.settled := by
  induction fuel generalizing state with
  | zero => simp [dijkstraLoop, hinvariant]
  | succ fuel ih =>
      have hne : 0 < state.heap.H.size := by omega
      let extracted := state.heap.H[0]
      let afterExtract :=
        ((Model.semantics model graph index).step (.extractMin) state).2
      have hextract := extractMin_queueInvariant model graph index state hinvariant hne
      dsimp only at hextract
      rcases hextract with
        ⟨hresponse, hafterInvariant, hafterSize, hafterSettled⟩
      change QueueInvariant afterExtract at hafterInvariant
      change afterExtract.heap.H.size + 1 = state.heap.H.size at hafterSize
      change afterExtract.settled =
        state.settled ++ [extracted.name] at hafterSettled
      rw [execute_dijkstraLoop_succ model graph index fuel state hne]
      let afterRow := (execute model graph index
        (processEdges extracted.name extracted.key
          (Model.indexedOutgoingEdges model graph index extracted.name)) afterExtract).2
      have hrowInvariant : QueueInvariant afterRow :=
        processEdges_queueInvariant model graph index extracted.name extracted.key
          (Model.indexedOutgoingEdges model graph index extracted.name)
          afterExtract hafterInvariant
      have hrowFuel : fuel ≤ afterRow.heap.H.size := by
        rw [processEdges_heap_size]
        omega
      have hrowSettled : afterRow.settled = state.settled ++ [extracted.name] := by
        rw [processEdges_settled, hafterSettled]
      have hrowSizeEq : afterRow.heap.H.size = afterExtract.heap.H.size :=
        processEdges_heap_size model graph index extracted.name extracted.key
          (Model.indexedOutgoingEdges model graph index extracted.name) afterExtract
      have hfinal := ih afterRow hrowInvariant hrowFuel
      dsimp only at hfinal ⊢
      refine ⟨hfinal.1, ?_, ?_, ?_⟩
      · change
          (execute model graph index
            (dijkstraLoop (Edge := Edge) (Weight := Weight) fuel) afterRow).2.heap.H.size +
              (fuel + 1) = state.heap.H.size
        omega
      · rw [hfinal.2.2.1, hrowSettled, List.length_append]
        simp
        omega
      · exact (by
          change state.settled.IsPrefix
            (execute model graph index
              (dijkstraLoop (Edge := Edge) (Weight := Weight) fuel) afterRow).2.settled
          have hp : state.settled.IsPrefix afterRow.settled := by
            rw [hrowSettled]
            exact List.prefix_append _ _
          exact hp.trans hfinal.2.2.2)

end Operational

/-! ## Shortest-path representation bridges -/

namespace Correctness

variable {G : Type u} {V : Type v} {Edge : Type w} {Weight : Type x}
variable [AddCommMonoid Weight] [LinearOrder Weight] [CanonicallyOrderedAdd Weight]

/-- Read one distance-table cell through the state's fixed-size certificate. -/
def storedDistance (state : Model.State n Edge Weight) (name : Fin n) : Distance Weight :=
  state.distances[name.val]?.getD ⊤

/-- Read one predecessor-table cell through the state's fixed-size certificate. -/
def storedPredecessor (state : Model.State n Edge Weight) (name : Fin n) :
    Option (Predecessor n Edge Weight) :=
  state.predecessors[name.val]?.getD none

omit [AddCommMonoid Weight] [LinearOrder Weight] [CanonicallyOrderedAdd Weight] in
/-- Every indexed outgoing occurrence denotes the corresponding exact network arc. -/
theorem indexedOutgoingEdges_sound
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length)
    (outgoing : IndexedOutgoingEdge
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (hmem : outgoing ∈ Model.indexedOutgoingEdges model graph index source) :
    model.edgeView.Arc graph outgoing.edge (index.decode source).val
      (index.decode outgoing.target).val outgoing.weight := by
  simp only [Model.indexedOutgoingEdges, List.mem_map] at hmem
  rcases hmem with ⟨attached, _, rfl⟩
  simpa using model.weightedNeighborAccess.sound attached.property

omit [AddCommMonoid Weight] [LinearOrder Weight] [CanonicallyOrderedAdd Weight] in
/-- Every exact network arc appears in the indexed outgoing row of its encoded source. -/
theorem indexedOutgoingEdges_complete
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source target : Fin (model.base.vertexEnumeration.vertices graph).length)
    (edge : Edge) (weight : Weight)
    (harc : model.edgeView.Arc graph edge (index.decode source).val
      (index.decode target).val weight) :
    ({ edge := edge, target := target, weight := weight } :
        IndexedOutgoingEdge
          (model.base.vertexEnumeration.vertices graph).length Edge Weight) ∈
      Model.indexedOutgoingEdges model graph index source := by
  let raw : OutgoingEdge Edge V Weight :=
    ⟨edge, (index.decode target).val, weight⟩
  have hraw : raw ∈ model.weightedNeighborAccess.outEdges graph (index.decode source).val :=
    model.weightedNeighborAccess.complete harc
  simp only [Model.indexedOutgoingEdges, List.mem_map]
  refine ⟨⟨raw, hraw⟩, by simp, ?_⟩
  simp [raw]

/-- The root key is no larger than a key obtained through the logical contents map. -/
theorem heap_root_le_contents
    (heap : KleinbergPriorityQueue.Heap n Key) [LinearOrder Key]
    (hwf : heap.WellFormed) (hne : 0 < heap.H.size)
    (name : Fin n) (key : Key) (hcontents : heap.contents name = some key) :
    heap.H[0].key ≤ key := by
  cases hposition : heap.Position name with
  | none => simp [KleinbergPriorityQueue.Heap.contents, hposition] at hcontents
  | some i =>
      have hi := KleinbergPriorityQueue.Heap.position_lt_size heap hwf.2.2 hposition
      have hkey : heap.H[i].key = key := by
        simpa [KleinbergPriorityQueue.Heap.contents, hposition,
          Array.getElem?_eq_getElem hi] using hcontents
      rw [← hkey]
      exact KleinbergPriorityQueue.Heap.heapOrdered_root_le heap hwf.2.1 hne hi

/-- The logical contents map returns the physical root entry under the root's name. -/
theorem heap_root_contents
    (heap : KleinbergPriorityQueue.Heap n Key) [LinearOrder Key]
    (hwf : heap.WellFormed) (hne : 0 < heap.H.size) :
    heap.contents heap.H[0].name = some heap.H[0].key := by
  have hposition := hwf.2.2.1 ⟨0, hne⟩
  have hposition' : heap.Position heap.H[0].name = some 0 := by
    simpa using hposition
  simp [KleinbergPriorityQueue.Heap.contents, hposition',
    Array.getElem?_eq_getElem hne]

/-! ### Claim (4.14) semantic predicates -/

/-- The additive weight of an exact network path, with all graph parameters explicit. -/
def networkPathWeight
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    {source target : V}
    (path : NetworkPath model.edgeView graph source target) : Weight :=
  @pathWeight G V Edge Weight model.base.interface model.edgeView graph
    inferInstance source target path

/-- Transport only the target endpoint of a network path. -/
def castNetworkPathTarget
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    {source left right : V} (h : left = right)
    (path : NetworkPath model.edgeView graph source left) :
    NetworkPath model.edgeView graph source right :=
  h ▸ path

omit [LinearOrder Weight] [CanonicallyOrderedAdd Weight] in
@[simp] theorem networkPathWeight_castNetworkPathTarget
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    {source left right : V} (h : left = right)
    (path : NetworkPath model.edgeView graph source left) :
    networkPathWeight (Weight := Weight) model graph (castNetworkPathTarget model graph h path) =
      networkPathWeight (Weight := Weight) model graph path := by
  subst right
  rfl

/-- A network path realizes the distance stored for one dense vertex name. -/
def RealizesDistance
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source name : Fin (model.base.vertexEnumeration.vertices graph).length)
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (path : NetworkPath model.edgeView graph
      (index.decode source).val (index.decode name).val) : Prop :=
  (networkPathWeight (Weight := Weight) model graph path : Distance Weight) =
    storedDistance state name

/-- A stored label is witnessed by an exact occurrence-preserving network path. -/
def HasPathWitness
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source name : Fin (model.base.vertexEnumeration.vertices graph).length)
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight) : Prop :=
  ∃ path : NetworkPath model.edgeView graph
      (index.decode source).val (index.decode name).val,
    RealizesDistance model graph index source name state path

/-- The textbook conclusion for one settled name: its stored label is realized by a shortest
path. -/
def SettledShortest
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source name : Fin (model.base.vertexEnumeration.vertices graph).length)
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight) : Prop :=
  ∃ path : NetworkPath model.edgeView graph
      (index.decode source).val (index.decode name).val,
    RealizesDistance model graph index source name state path ∧
      IsShortestPath model.edgeView graph path

/-- Heap keys and persistent distance-table cells agree for every active name. -/
def ActiveLabelsAgree
    (state : Model.State n Edge Weight) : Prop :=
  ∀ name : Fin n, state.heap.contains name = true →
    state.heap.contents name = some (storedDistance state name)

/-- Every outgoing occurrence of a settled name has been relaxed against every active target. -/
def SettledEdgesRelaxed
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight) : Prop :=
  ∀ settledName, settledName ∈ state.settled →
    ∀ outgoing, outgoing ∈ Model.indexedOutgoingEdges model graph index settledName →
      state.heap.contains outgoing.target = true →
        storedDistance state outgoing.target ≤
          storedDistance state settledName + (outgoing.weight : Distance Weight)

/--
The predecessor table recursively reconstructs a source-to-name walk. Every recursive parent is
already settled, and every stored predecessor occurrence carries both an exact graph arc and the
distance equality established by its successful relaxation.
-/
inductive PredecessorReaches
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length)
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight) :
    Fin (model.base.vertexEnumeration.vertices graph).length → Prop
  | source
      (hpredecessor : storedPredecessor state source = none)
      (hdistance : storedDistance state source = 0) :
      PredecessorReaches model graph index source state source
  | step
      (parent : Fin (model.base.vertexEnumeration.vertices graph).length)
      (outgoing : IndexedOutgoingEdge
        (model.base.vertexEnumeration.vertices graph).length Edge Weight)
      (hparent : PredecessorReaches model graph index source state parent)
      (hparentSettled : parent ∈ state.settled)
      (houtgoing : outgoing ∈
        Model.indexedOutgoingEdges model graph index parent)
      (hpredecessor : storedPredecessor state outgoing.target = some
        ⟨parent, outgoing.target, outgoing.edge, outgoing.weight⟩)
      (hdistance : storedDistance state outgoing.target =
        storedDistance state parent + (outgoing.weight : Distance Weight)) :
      PredecessorReaches model graph index source state outgoing.target

omit [LinearOrder Weight] [CanonicallyOrderedAdd Weight] in
/-- A certified predecessor chain denotes an exact occurrence-preserving path of the stored
weight. -/
theorem predecessorReaches_path
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length)
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    {name : Fin (model.base.vertexEnumeration.vertices graph).length}
    (hreaches : PredecessorReaches model graph index source state name) :
    HasPathWitness model graph index source name state := by
  induction hreaches with
  | source hpredecessor hdistance =>
      letI := weightedArcQuiver model.edgeView graph
      refine ⟨Quiver.Path.nil, ?_⟩
      unfold RealizesDistance
      simp [networkPathWeight, pathWeight, hdistance]
  | step parent outgoing hparent hparentSettled houtgoing hpredecessor hdistance ih =>
      rcases ih with ⟨path, hpath⟩
      have harc := indexedOutgoingEdges_sound model graph index parent outgoing houtgoing
      let arc : WeightedArc model.edgeView graph (index.decode parent).val
          (index.decode outgoing.target).val :=
        ⟨outgoing.edge, outgoing.weight, harc⟩
      letI := weightedArcQuiver model.edgeView graph
      refine ⟨path.cons arc, ?_⟩
      unfold RealizesDistance at hpath ⊢
      rw [hdistance, ← hpath]
      simp [networkPathWeight, pathWeight, arc]

omit [LinearOrder Weight] [CanonicallyOrderedAdd Weight] in
/-- A predecessor chain for an unchanged name transports across one active-target update. -/
theorem predecessorReaches_transport_other
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source updated : Fin
      (model.base.vertexEnumeration.vertices graph).length)
    (before after : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (hsettled : after.settled = before.settled)
    (hsourceSettled : source ∈ before.settled)
    (hupdatedFresh : updated ∉ before.settled)
    (hpredecessorOther : ∀ name, name ≠ updated →
      storedPredecessor after name = storedPredecessor before name)
    (hdistanceOther : ∀ name, name ≠ updated →
      storedDistance after name = storedDistance before name)
    {name : Fin (model.base.vertexEnumeration.vertices graph).length}
    (hreaches : PredecessorReaches model graph index source before name)
    (hname : name ≠ updated) :
    PredecessorReaches model graph index source after name := by
  induction hreaches with
  | source hpredecessor hdistance =>
      have hsourceNe : source ≠ updated := by
        intro heq
        subst updated
        exact hupdatedFresh hsourceSettled
      apply PredecessorReaches.source
      · rw [hpredecessorOther source hsourceNe]
        exact hpredecessor
      · rw [hdistanceOther source hsourceNe]
        exact hdistance
  | step parent outgoing hparent hparentSettled houtgoing hpredecessor hdistance ih =>
      have hparentNe : parent ≠ updated := by
        intro heq
        subst updated
        exact hupdatedFresh hparentSettled
      apply PredecessorReaches.step parent outgoing (ih hparentNe)
      · simpa [hsettled] using hparentSettled
      · exact houtgoing
      · rw [hpredecessorOther outgoing.target hname]
        exact hpredecessor
      · rw [hdistanceOther outgoing.target hname,
          hdistanceOther parent hparentNe]
        exact hdistance

omit [LinearOrder Weight] [CanonicallyOrderedAdd Weight] in
/-- Predecessor reconstruction transports when tables agree and settlement only grows. -/
theorem predecessorReaches_transport_tables
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length)
    (before after : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (hsettled : ∀ name, name ∈ before.settled → name ∈ after.settled)
    (hpredecessor : ∀ name,
      storedPredecessor after name = storedPredecessor before name)
    (hdistance : ∀ name,
      storedDistance after name = storedDistance before name)
    {name : Fin (model.base.vertexEnumeration.vertices graph).length}
    (hreaches : PredecessorReaches model graph index source before name) :
    PredecessorReaches model graph index source after name := by
  induction hreaches with
  | source hpred hdist =>
      exact .source (by simpa [hpredecessor] using hpred)
        (by simpa [hdistance] using hdist)
  | step parent outgoing hparent hparentSettled houtgoing hpred hdist ih =>
      apply PredecessorReaches.step parent outgoing ih
      · exact hsettled parent hparentSettled
      · exact houtgoing
      · simpa [hpredecessor] using hpred
      · simpa [hdistance] using hdist

/--
The semantic loop invariant used for claim (4.14). Besides the operational queue invariant, it
records executable-label agreement, path witnesses for finite labels, shortestness of settled
labels, and the fact that all rows belonging to settled vertices have been relaxed.
-/
structure ShortestPathInvariant
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length)
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight) : Prop where
  queue : Operational.QueueInvariant state
  source_settled : source ∈ state.settled
  activeLabels : ActiveLabelsAgree state
  finiteWitness : ∀ name,
    storedDistance state name ≠ ⊤ → HasPathWitness model graph index source name state
  settledShortest : ∀ name, name ∈ state.settled →
    SettledShortest model graph index source name state
  relaxed : SettledEdgesRelaxed model graph index state

/-- Claim (4.14)'s complete invariant, including executable predecessor reconstruction. -/
structure FullInvariant
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length)
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight) : Prop where
  shortest : ShortestPathInvariant model graph index source state
  predecessorWitness : ∀ name, storedDistance state name ≠ ⊤ →
    PredecessorReaches model graph index source state name

/-- Ambient vertices represented by the current dense settled-name list. -/
def decodedSettledSet
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight) : Set V :=
  { vertex | ∃ hvertex : model.base.interface.IsVertex graph vertex,
      index.encode ⟨vertex, hvertex⟩ ∈ state.settled }

omit [AddCommMonoid Weight] [LinearOrder Weight] [CanonicallyOrderedAdd Weight] in
@[simp] theorem decode_mem_decodedSettledSet
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (name : Fin (model.base.vertexEnumeration.vertices graph).length) :
    (index.decode name).val ∈ decodedSettledSet model graph index state ↔
      name ∈ state.settled := by
  simp [decodedSettledSet]

omit [AddCommMonoid Weight] [LinearOrder Weight] [CanonicallyOrderedAdd Weight] in
/-- Semantic reachability supplies an exact occurrence-preserving weighted network path. -/
theorem reachable_has_networkPath
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    {source target : V}
    (hreachable : Reachable model.base.interface graph source target) :
    Nonempty (NetworkPath model.edgeView graph source target) := by
  letI := weightedArcQuiver model.edgeView graph
  induction hreachable with
  | refl _ => exact ⟨Quiver.Path.nil⟩
  | @step x y z hadj _ ih =>
      rcases model.edgeView.adj_has_arc hadj with ⟨edge, weight, harc⟩
      rcases ih with ⟨path⟩
      let arc : WeightedArc model.edgeView graph x y := ⟨edge, weight, harc⟩
      exact ⟨(Quiver.Hom.toPath arc).comp path⟩

/--
Textbook cut lemma: under the semantic invariant, the current heap root's label is no larger than
the weight of any alternative path to that root.
-/
theorem rootLabel_le_path
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length)
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (hinvariant : ShortestPathInvariant model graph index source state)
    (hne : 0 < state.heap.H.size)
    (alternative : NetworkPath model.edgeView graph (index.decode source).val
      (index.decode state.heap.H[0].name).val) :
    storedDistance state state.heap.H[0].name ≤
      (networkPathWeight (Weight := Weight) model graph alternative : Distance Weight) := by
  let rootName := state.heap.H[0].name
  have hrootPosition : state.heap.Position rootName = some 0 := by
    simpa [rootName] using hinvariant.queue.wellFormed.2.2.1 ⟨0, hne⟩
  have hrootActive : state.heap.contains rootName = true := by
    simp [KleinbergPriorityQueue.Heap.contains, hrootPosition]
  have hrootFresh : rootName ∉ state.settled :=
    (hinvariant.queue.active_iff_not_settled rootName).1 hrootActive
  let settledSet := decodedSettledSet model graph index state
  have hsourceSet : (index.decode source).val ∈ settledSet := by
    simpa [settledSet] using hinvariant.source_settled
  have hrootNotSet : (index.decode rootName).val ∉ settledSet := by
    simpa [settledSet] using hrootFresh
  letI := weightedArcQuiver model.edgeView graph
  obtain ⟨u, huSet, v, hvNotSet, arc, pathPrefix, suffix, halt⟩ :=
    Quiver.Path.exists_mem_notMem_hom_path_path_of_notMem_mem
      alternative settledSet hsourceSet hrootNotSet
  rcases huSet with ⟨huVertex, huSettled⟩
  let uName := index.encode
    (⟨u, huVertex⟩ : GraphVertex model.base.interface graph)
  have huDecode : (index.decode uName).val = u := by simp [uName]
  let vName := index.encode
    (⟨v, model.edgeView.target_mem arc.valid⟩ :
      GraphVertex model.base.interface graph)
  have huNameSettled : uName ∈ state.settled := by
    simpa [uName] using huSettled
  have hvNameFresh : vName ∉ state.settled := by
    rw [← decode_mem_decodedSettledSet model graph index state]
    simpa [vName] using hvNotSet
  have hvActive : state.heap.contains vName = true :=
    (hinvariant.queue.active_iff_not_settled vName).2 hvNameFresh
  let outgoing : IndexedOutgoingEdge
      (model.base.vertexEnumeration.vertices graph).length Edge Weight :=
    { edge := arc.edge, target := vName, weight := arc.weight }
  have houtgoing : outgoing ∈ Model.indexedOutgoingEdges model graph index uName := by
    apply indexedOutgoingEdges_complete
    simpa [outgoing, uName, vName] using arc.valid
  have hrelaxed := hinvariant.relaxed uName huNameSettled outgoing houtgoing hvActive
  have hrootKey : state.heap.H[0].key = storedDistance state rootName := by
    exact Option.some.inj ((heap_root_contents state.heap
      hinvariant.queue.wellFormed hne).symm.trans
        (hinvariant.activeLabels rootName hrootActive))
  have hvContents := hinvariant.activeLabels vName hvActive
  have hminimum := heap_root_le_contents state.heap hinvariant.queue.wellFormed
    hne vName (storedDistance state vName) hvContents
  have hrootLeV : storedDistance state rootName ≤ storedDistance state vName := by
    simpa [hrootKey] using hminimum
  obtain ⟨shortestToU, hrealizesU, hshortestU⟩ :=
    hinvariant.settledShortest uName huNameSettled
  let prefixToU : NetworkPath model.edgeView graph (index.decode source).val
      (index.decode uName).val :=
    castNetworkPathTarget model graph huDecode.symm pathPrefix
  have hprefixBound : storedDistance state uName ≤
      (networkPathWeight (Weight := Weight) model graph pathPrefix : Distance Weight) := by
    have hshort := hshortestU prefixToU
    unfold RealizesDistance at hrealizesU
    rw [← hrealizesU]
    have hshort' :
        (networkPathWeight (Weight := Weight) model graph shortestToU : Distance Weight) ≤
          (networkPathWeight (Weight := Weight) model graph prefixToU : Distance Weight) := by
      apply WithTop.coe_le_coe.mpr
      simpa [networkPathWeight] using hshort
    simpa [prefixToU] using hshort'
  have haltWeight :
      (networkPathWeight (Weight := Weight) model graph alternative : Distance Weight) =
        (networkPathWeight (Weight := Weight) model graph pathPrefix : Distance Weight) +
          (arc.weight : Distance Weight) +
            (networkPathWeight (Weight := Weight) model graph suffix : Distance Weight) := by
    rw [halt]
    simp [networkPathWeight, pathWeight, Quiver.Hom.toPath, add_assoc]
  calc
    storedDistance state rootName ≤ storedDistance state vName := hrootLeV
    _ ≤ storedDistance state uName + (arc.weight : Distance Weight) := by
      simpa [outgoing] using hrelaxed
    _ ≤ (networkPathWeight (Weight := Weight) model graph pathPrefix : Distance Weight) +
          (arc.weight : Distance Weight) := add_le_add hprefixBound le_rfl
    _ ≤ (networkPathWeight (Weight := Weight) model graph alternative : Distance Weight) := by
      rw [haltWeight]
      apply le_add_of_nonneg_right
      apply WithTop.coe_le_coe.mpr
      simp

/-- A reachable heap root is represented by a shortest path before it is settled. -/
theorem root_settledShortest
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length)
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (hinvariant : ShortestPathInvariant model graph index source state)
    (hne : 0 < state.heap.H.size)
    (hreachable : Reachable model.base.interface graph (index.decode source).val
      (index.decode state.heap.H[0].name).val) :
    SettledShortest model graph index source state.heap.H[0].name state := by
  rcases reachable_has_networkPath model graph hreachable with ⟨reachablePath⟩
  have hfiniteBound := rootLabel_le_path model graph index source state
    hinvariant hne reachablePath
  have hfinite : storedDistance state state.heap.H[0].name ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top hfiniteBound
  rcases hinvariant.finiteWitness state.heap.H[0].name hfinite with
    ⟨selectedPath, hrealizes⟩
  refine ⟨selectedPath, hrealizes, ?_⟩
  intro alternative
  have hbound := rootLabel_le_path model graph index source state
    hinvariant hne alternative
  unfold RealizesDistance at hrealizes
  rw [← hrealizes] at hbound
  exact WithTop.coe_le_coe.mp hbound

/-! ### Executable relaxation preservation -/

/-- An active `changeKey` request succeeds and performs exactly the advertised logical writes. -/
theorem changeKey_step_of_active
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (hinvariant : Operational.QueueInvariant state)
    (predecessor : Predecessor
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (candidate : Distance Weight)
    (hactive : state.heap.contains predecessor.target = true) :
    let step := (Model.semantics model graph index).step
      (.changeKey predecessor candidate) state
    step.1 = ULift.up true ∧
      step.2.settled = state.settled ∧
      storedDistance step.2 predecessor.target = candidate ∧
      (∀ query, query ≠ predecessor.target →
        storedDistance step.2 query = storedDistance state query) ∧
      step.2.heap.contents predecessor.target = some candidate ∧
      (∀ query, query ≠ predecessor.target →
        step.2.heap.contents query = state.heap.contents query) ∧
      Operational.QueueInvariant step.2 := by
  cases hposition : state.heap.Position predecessor.target with
  | none =>
      simp [KleinbergPriorityQueue.Heap.contains, hposition] at hactive
  | some position =>
      have hsuccess := KleinbergPriorityQueue.Heap.changeKey_active_success
        state.heap hinvariant.wellFormed.2.2 predecessor.target candidate hposition
      have hself := KleinbergPriorityQueue.Heap.changeKey_contents_self
        state.heap hinvariant.wellFormed.2.2 predecessor.target candidate hposition
      have hwellFormed := KleinbergPriorityQueue.Heap.changeKey_wellFormed
        state.heap hinvariant.wellFormed predecessor.target candidate
      dsimp [Model.semantics]
      rw [hsuccess]
      simp only [if_pos True.intro]
      refine ⟨True.intro, True.intro, ?_, ?_, hself, ?_, ?_⟩
      · simp [storedDistance, state.distances_size, predecessor.target.isLt]
      · intro query hquery
        have hqueryVal : query.val ≠ predecessor.target.val := by
          intro heq
          exact hquery (Fin.ext heq)
        simp [storedDistance, Ne.symm hqueryVal]
      · intro query hquery
        exact KleinbergPriorityQueue.Heap.changeKey_contents_other
          state.heap hinvariant.wellFormed.2.2 predecessor.target query candidate
          hquery hposition
      · constructor
        · exact hwellFormed
        · intro name
          rw [KleinbergPriorityQueue.Heap.changeKey_contains]
          exact hinvariant.active_iff_not_settled name
        · exact hinvariant.settled_nodup

/-- A successful active `changeKey` writes exactly one predecessor-table cell. -/
theorem changeKey_predecessor_step_of_active
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (hinvariant : Operational.QueueInvariant state)
    (predecessor : Predecessor
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (candidate : Distance Weight)
    (hactive : state.heap.contains predecessor.target = true) :
    let next := ((Model.semantics model graph index).step
      (.changeKey predecessor candidate) state).2
    storedPredecessor next predecessor.target = some predecessor ∧
      ∀ query, query ≠ predecessor.target →
        storedPredecessor next query = storedPredecessor state query := by
  cases hposition : state.heap.Position predecessor.target with
  | none =>
      simp [KleinbergPriorityQueue.Heap.contains, hposition] at hactive
  | some position =>
      have hsuccess := KleinbergPriorityQueue.Heap.changeKey_active_success
        state.heap hinvariant.wellFormed.2.2 predecessor.target candidate hposition
      dsimp [Model.semantics]
      rw [hsuccess]
      simp only [if_pos True.intro]
      constructor
      · simp [storedPredecessor, state.predecessors_size,
          predecessor.target.isLt]
      · intro query hquery
        have hqueryVal : query.val ≠ predecessor.target.val := by
          intro heq
          exact hquery (Fin.ext heq)
        simp [storedPredecessor, Ne.symm hqueryVal]

omit [LinearOrder Weight] [CanonicallyOrderedAdd Weight] in
/-- Extend a realized source label along one indexed outgoing edge occurrence. -/
theorem extend_pathWitness
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length)
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (settledName : Fin (model.base.vertexEnumeration.vertices graph).length)
    (outgoing : IndexedOutgoingEdge
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (houtgoing : outgoing ∈
      Model.indexedOutgoingEdges model graph index settledName)
    (hwitness : HasPathWitness model graph index source settledName state) :
    ∃ path : NetworkPath model.edgeView graph (index.decode source).val
        (index.decode outgoing.target).val,
      (networkPathWeight (Weight := Weight) model graph path : Distance Weight) =
        storedDistance state settledName +
          (outgoing.weight : Distance Weight) := by
  rcases hwitness with ⟨path, hpath⟩
  have harc := indexedOutgoingEdges_sound model graph index settledName outgoing houtgoing
  let arc : WeightedArc model.edgeView graph (index.decode settledName).val
      (index.decode outgoing.target).val :=
    ⟨outgoing.edge, outgoing.weight, harc⟩
  letI := weightedArcQuiver model.edgeView graph
  refine ⟨path.cons arc, ?_⟩
  unfold RealizesDistance at hpath
  rw [← hpath]
  simp [networkPathWeight, pathWeight, arc]

/-- Facts supplied by a complete execution of one outgoing row. -/
structure ProcessEdgesFacts
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length)
    (settledName : Fin (model.base.vertexEnumeration.vertices graph).length)
    (sourceDistance : Distance Weight)
    (row : List (IndexedOutgoingEdge
      (model.base.vertexEnumeration.vertices graph).length Edge Weight))
    (before after : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight) : Prop where
  queue : Operational.QueueInvariant after
  settled : after.settled = before.settled
  activeLabels : ActiveLabelsAgree after
  finiteWitness : ∀ name, storedDistance after name ≠ ⊤ →
    HasPathWitness model graph index source name after
  distance_mono : ∀ name,
    storedDistance after name ≤ storedDistance before name
  settled_distance : ∀ name, name ∈ before.settled →
    storedDistance after name = storedDistance before name
  row_relaxed : ∀ outgoing, outgoing ∈ row →
    after.heap.contains outgoing.target = true →
      storedDistance after outgoing.target ≤
        storedDistance after settledName + (outgoing.weight : Distance Weight)

/-- The one-edge fragment used by `processEdges`. -/
def processOne (source : Fin n) (sourceDistance : Distance Weight)
    (outgoing : IndexedOutgoingEdge n Edge Weight) : Program n Edge Weight PUnit := do
  let candidate ← relaxationCandidate sourceDistance outgoing
  match candidate.down with
  | none => pure .unit
  | some value =>
      let predecessor : Predecessor n Edge Weight :=
        ⟨source, outgoing.target, outgoing.edge, outgoing.weight⟩
      let _ ← changeKey predecessor value
      pure .unit

/-- State transition facts for inspecting and, when necessary, relaxing one occurrence. -/
structure ProcessOneFacts
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length)
    (settledName : Fin (model.base.vertexEnumeration.vertices graph).length)
    (outgoing : IndexedOutgoingEdge
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (before after : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight) : Prop where
  queue : Operational.QueueInvariant after
  settled : after.settled = before.settled
  activeLabels : ActiveLabelsAgree after
  finiteWitness : ∀ name, storedDistance after name ≠ ⊤ →
    HasPathWitness model graph index source name after
  distance_mono : ∀ name,
    storedDistance after name ≤ storedDistance before name
  settled_distance : ∀ name, name ∈ before.settled →
    storedDistance after name = storedDistance before name
  edge_relaxed : after.heap.contains outgoing.target = true →
    storedDistance after outgoing.target ≤
      storedDistance after settledName + (outgoing.weight : Distance Weight)

omit [LinearOrder Weight] [CanonicallyOrderedAdd Weight] in
/-- A path witness transports across an unchanged distance-table cell. -/
theorem hasPathWitness_of_distance_eq
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source name : Fin (model.base.vertexEnumeration.vertices graph).length)
    (before after : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (heq : storedDistance after name = storedDistance before name)
    (hwitness : HasPathWitness model graph index source name before) :
    HasPathWitness model graph index source name after := by
  simpa [HasPathWitness, RealizesDistance, heq] using hwitness

private theorem extractMin_activeLabels
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (hqueue : Operational.QueueInvariant state)
    (hactiveLabels : ActiveLabelsAgree state) (hne : 0 < state.heap.H.size) :
    ActiveLabelsAgree
      ((Model.semantics model graph index).step (.extractMin) state).2 := by
  let after := ((Model.semantics model graph index).step (.extractMin) state).2
  change ActiveLabelsAgree after
  intro name hactive
  have hactiveIff := KleinbergPriorityQueue.Heap.extractMin_contains_eq_true_iff
    state.heap hqueue.wellFormed hne name
  have hactive' : state.heap.extractMin.1.contains name = true := by
    simpa [after, Model.semantics] using hactive
  have hparts := hactiveIff.1 hactive'
  have hcontents := (KleinbergPriorityQueue.Heap.extractMin_contents
    state.heap hqueue.wellFormed hne).2 name hparts.1
  change state.heap.extractMin.1.contents name =
    some (storedDistance after name)
  rw [hcontents]
  have hafterDistance : storedDistance after name = storedDistance state name := by rfl
  rw [hafterDistance]
  exact hactiveLabels name hparts.2

omit [LinearOrder Weight] [CanonicallyOrderedAdd Weight] in
private theorem finiteWitness_of_distances_eq
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length)
    (before after : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (hdistance : ∀ name, storedDistance after name = storedDistance before name)
    (hfiniteWitness : ∀ name, storedDistance before name ≠ ⊤ →
      HasPathWitness model graph index source name before) :
    ∀ name, storedDistance after name ≠ ⊤ →
      HasPathWitness model graph index source name after := by
  intro name hfinite
  apply hasPathWitness_of_distance_eq model graph index source name before after
    (hdistance name)
  exact hfiniteWitness name (by simpa [hdistance name] using hfinite)

/-- Executing the fragment for one real outgoing occurrence preserves all label witnesses. -/
theorem processOne_facts
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source settledName : Fin
      (model.base.vertexEnumeration.vertices graph).length)
    (sourceDistance : Distance Weight)
    (outgoing : IndexedOutgoingEdge
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (hqueue : Operational.QueueInvariant state)
    (hactiveLabels : ActiveLabelsAgree state)
    (hfiniteWitness : ∀ name, storedDistance state name ≠ ⊤ →
      HasPathWitness model graph index source name state)
    (hsettled : settledName ∈ state.settled)
    (hsourceDistance : sourceDistance = storedDistance state settledName)
    (hsourceWitness : HasPathWitness model graph index source settledName state)
    (houtgoing : outgoing ∈
      Model.indexedOutgoingEdges model graph index settledName) :
    ProcessOneFacts model graph index source settledName outgoing state
      (Operational.execute model graph index
        (processOne settledName sourceDistance outgoing) state).2 := by
  let candidate : Distance Weight :=
    sourceDistance + (outgoing.weight : Distance Weight)
  cases hcontents : state.heap.contents outgoing.target with
  | none =>
      have hinactive : state.heap.contains outgoing.target = false :=
        (KleinbergPriorityQueue.Heap.contains_eq_false_iff_contents_eq_none
          state.heap hqueue.wellFormed.2.2 outgoing.target).2 hcontents
      have hexecute : Operational.execute model graph index
          (processOne settledName sourceDistance outgoing) state = (.unit, state) := by
        simp only [processOne]
        rw [Operational.execute_bind]
        rw [show Operational.execute model graph index
            (relaxationCandidate sourceDistance outgoing) state =
          (Model.semantics model graph index).step
            (.relaxationCandidate sourceDistance outgoing) state by rfl]
        simp [Model.semantics, hcontents]
      rw [hexecute]
      refine ⟨hqueue, rfl, hactiveLabels, hfiniteWitness,
        fun _ => le_rfl, fun _ _ => rfl, ?_⟩
      intro hactive
      simp [hinactive] at hactive
  | some current =>
      have hactive : state.heap.contains outgoing.target = true :=
        (KleinbergPriorityQueue.Heap.contains_eq_true_iff_exists_contents
          state.heap hqueue.wellFormed.2.2 outgoing.target).2 ⟨current, hcontents⟩
      have hcurrent : current = storedDistance state outgoing.target := by
        exact Option.some.inj (hcontents.symm.trans (hactiveLabels _ hactive))
      by_cases himprove : candidate < current
      · let predecessor : Predecessor
            (model.base.vertexEnumeration.vertices graph).length Edge Weight :=
          ⟨settledName, outgoing.target, outgoing.edge, outgoing.weight⟩
        let next := ((Model.semantics model graph index).step
          (.changeKey predecessor candidate) state).2
        have hchange := changeKey_step_of_active model graph index state hqueue
          predecessor candidate hactive
        dsimp only at hchange
        have hexecute : Operational.execute model graph index
            (processOne settledName sourceDistance outgoing) state = (.unit, next) := by
          simp only [processOne]
          rw [Operational.execute_bind]
          rw [show Operational.execute model graph index
              (relaxationCandidate sourceDistance outgoing) state =
            (Model.semantics model graph index).step
              (.relaxationCandidate sourceDistance outgoing) state by rfl]
          simp only [Model.semantics, hcontents]
          rw [if_pos (by simpa [candidate] using himprove)]
          rw [Operational.execute_bind]
          rw [show Operational.execute model graph index
              (changeKey predecessor candidate) state =
            (Model.semantics model graph index).step
              (.changeKey predecessor candidate) state by rfl]
          rw [show (Model.semantics model graph index).step
              (.changeKey predecessor candidate) state =
                (ULift.up true, next) from Prod.ext hchange.1 rfl]
          rfl
        rw [hexecute]
        have hnextSettled : next.settled = state.settled := hchange.2.1
        have hnextTarget : storedDistance next outgoing.target = candidate := hchange.2.2.1
        have hnextOther := hchange.2.2.2.1
        have hnextContents : next.heap.contents outgoing.target = some candidate :=
          hchange.2.2.2.2.1
        have hnextContentsOther := hchange.2.2.2.2.2.1
        have hnextQueue := hchange.2.2.2.2.2.2
        have htargetFresh : outgoing.target ∉ state.settled :=
          (hqueue.active_iff_not_settled outgoing.target).1 hactive
        have hnewPath := extend_pathWitness model graph index source state settledName
          outgoing houtgoing hsourceWitness
        refine ⟨hnextQueue, hnextSettled, ?_, ?_, ?_, ?_, ?_⟩
        · intro name hnameActive
          by_cases hname : name = outgoing.target
          · subst name
            simpa [hnextTarget] using hnextContents
          · rw [hnextContentsOther name hname, hnextOther name hname]
            apply hactiveLabels name
            rw [hqueue.active_iff_not_settled, ← hnextSettled,
              ← hnextQueue.active_iff_not_settled]
            exact hnameActive
        · intro name hfinite
          by_cases hname : name = outgoing.target
          · subst name
            rcases hnewPath with ⟨path, hpath⟩
            refine ⟨path, ?_⟩
            unfold RealizesDistance
            rw [hnextTarget]
            simpa [candidate, hsourceDistance] using hpath
          · apply hasPathWitness_of_distance_eq model graph index source name state next
              (hnextOther name hname)
            exact hfiniteWitness name fun htop =>
              hfinite ((hnextOther name hname).trans htop)
        · intro name
          by_cases hname : name = outgoing.target
          · subst name
            rw [hnextTarget, ← hcurrent]
            exact himprove.le
          · rw [hnextOther name hname]
        · intro name hnameSettled
          have hname : name ≠ outgoing.target := fun heq =>
            htargetFresh (heq ▸ hnameSettled)
          exact hnextOther name hname
        · intro _
          have hsourceTarget : settledName ≠ outgoing.target := fun heq =>
            htargetFresh (heq ▸ hsettled)
          rw [hnextTarget, hnextOther settledName hsourceTarget]
          simp [candidate, hsourceDistance]
      · have hexecute : Operational.execute model graph index
            (processOne settledName sourceDistance outgoing) state = (.unit, state) := by
          simp only [processOne]
          rw [Operational.execute_bind]
          rw [show Operational.execute model graph index
              (relaxationCandidate sourceDistance outgoing) state =
            (Model.semantics model graph index).step
              (.relaxationCandidate sourceDistance outgoing) state by rfl]
          simp only [Model.semantics, hcontents]
          rw [if_neg (by simpa [candidate] using himprove)]
          rfl
        rw [hexecute]
        refine ⟨hqueue, rfl, hactiveLabels, hfiniteWitness,
          fun _ => le_rfl, fun _ _ => rfl, ?_⟩
        intro _
        rw [← hcurrent, ← hsourceDistance]
        exact le_of_not_gt himprove

/-- One executable relaxation preserves recursive predecessor reconstruction for every finite
label. -/
theorem processOne_predecessorWitness
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source settledName : Fin
      (model.base.vertexEnumeration.vertices graph).length)
    (sourceDistance : Distance Weight)
    (outgoing : IndexedOutgoingEdge
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (hqueue : Operational.QueueInvariant state)
    (_hactiveLabels : ActiveLabelsAgree state)
    (_hfiniteWitness : ∀ name, storedDistance state name ≠ ⊤ →
      HasPathWitness model graph index source name state)
    (hsourceSettled : source ∈ state.settled)
    (hsettledShortest : SettledShortest model graph index source settledName state)
    (hpredecessorWitness : ∀ name, storedDistance state name ≠ ⊤ →
      PredecessorReaches model graph index source state name)
    (hsettled : settledName ∈ state.settled)
    (hsourceDistance : sourceDistance = storedDistance state settledName)
    (houtgoing : outgoing ∈
      Model.indexedOutgoingEdges model graph index settledName) :
    let after := (Operational.execute model graph index
      (processOne settledName sourceDistance outgoing) state).2
    ∀ name, storedDistance after name ≠ ⊤ →
      PredecessorReaches model graph index source after name := by
  dsimp only
  let candidate : Distance Weight :=
    sourceDistance + (outgoing.weight : Distance Weight)
  have hparentReach := hpredecessorWitness settledName <| by
    rcases hsettledShortest with ⟨path, hrealizes, _⟩
    unfold RealizesDistance at hrealizes
    rw [← hrealizes]
    exact WithTop.coe_ne_top
  cases hcontents : state.heap.contents outgoing.target with
  | none =>
      have hexecute : Operational.execute model graph index
          (processOne settledName sourceDistance outgoing) state = (.unit, state) := by
        simp only [processOne]
        rw [Operational.execute_bind]
        rw [show Operational.execute model graph index
            (relaxationCandidate sourceDistance outgoing) state =
          (Model.semantics model graph index).step
            (.relaxationCandidate sourceDistance outgoing) state by rfl]
        simp [Model.semantics, hcontents]
      rw [hexecute]
      exact hpredecessorWitness
  | some current =>
      have hactive : state.heap.contains outgoing.target = true :=
        (KleinbergPriorityQueue.Heap.contains_eq_true_iff_exists_contents
          state.heap hqueue.wellFormed.2.2 outgoing.target).2
          ⟨current, hcontents⟩
      by_cases himprove : candidate < current
      · let predecessor : Predecessor
            (model.base.vertexEnumeration.vertices graph).length Edge Weight :=
          ⟨settledName, outgoing.target, outgoing.edge, outgoing.weight⟩
        let next := ((Model.semantics model graph index).step
          (.changeKey predecessor candidate) state).2
        have hchange := changeKey_step_of_active model graph index state
          hqueue predecessor candidate hactive
        dsimp only at hchange
        have hpredChange := changeKey_predecessor_step_of_active model graph index
          state hqueue predecessor candidate hactive
        dsimp only at hpredChange
        have hexecute : Operational.execute model graph index
            (processOne settledName sourceDistance outgoing) state = (.unit, next) := by
          simp only [processOne]
          rw [Operational.execute_bind]
          rw [show Operational.execute model graph index
              (relaxationCandidate sourceDistance outgoing) state =
            (Model.semantics model graph index).step
              (.relaxationCandidate sourceDistance outgoing) state by rfl]
          simp only [Model.semantics, hcontents]
          rw [if_pos (by simpa [candidate] using himprove)]
          rw [Operational.execute_bind]
          rw [show Operational.execute model graph index
              (changeKey predecessor candidate) state =
            (Model.semantics model graph index).step
              (.changeKey predecessor candidate) state by rfl]
          rw [show (Model.semantics model graph index).step
              (.changeKey predecessor candidate) state =
                (ULift.up true, next) from Prod.ext hchange.1 rfl]
          rfl
        rw [hexecute]
        intro name hfinite
        have htargetFresh : outgoing.target ∉ state.settled :=
          (hqueue.active_iff_not_settled outgoing.target).1 hactive
        have hparentNe : settledName ≠ outgoing.target := fun heq =>
          htargetFresh (heq ▸ hsettled)
        have hparentNext := predecessorReaches_transport_other model graph index
          source outgoing.target state next hchange.2.1 hsourceSettled
          htargetFresh hpredChange.2 hchange.2.2.2.1 hparentReach hparentNe
        by_cases hname : name = outgoing.target
        · subst name
          apply PredecessorReaches.step settledName outgoing hparentNext
          · rw [hchange.2.1]
            exact hsettled
          · exact houtgoing
          · exact hpredChange.1
          · rw [hchange.2.2.1, hchange.2.2.2.1 settledName hparentNe]
            simp [candidate, hsourceDistance]
        · apply predecessorReaches_transport_other model graph index
            source outgoing.target state next hchange.2.1 hsourceSettled
            htargetFresh hpredChange.2 hchange.2.2.2.1
            (hpredecessorWitness name fun htop =>
              hfinite ((hchange.2.2.2.1 name hname).trans htop)) hname
      · have hexecute : Operational.execute model graph index
            (processOne settledName sourceDistance outgoing) state = (.unit, state) := by
          simp only [processOne]
          rw [Operational.execute_bind]
          rw [show Operational.execute model graph index
              (relaxationCandidate sourceDistance outgoing) state =
            (Model.semantics model graph index).step
              (.relaxationCandidate sourceDistance outgoing) state by rfl]
          simp only [Model.semantics, hcontents]
          rw [if_neg (by simpa [candidate] using himprove)]
          rfl
        rw [hexecute]
        exact hpredecessorWitness

/-- The head of `processEdges` has exactly the semantics of `processOne`. -/
theorem processEdges_cons_execute
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (settledName : Fin (model.base.vertexEnumeration.vertices graph).length)
    (sourceDistance : Distance Weight)
    (outgoing : IndexedOutgoingEdge
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (rest : List (IndexedOutgoingEdge
      (model.base.vertexEnumeration.vertices graph).length Edge Weight))
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight) :
    Operational.execute model graph index
        (processEdges settledName sourceDistance (outgoing :: rest)) state =
      Operational.execute model graph index
        (processEdges settledName sourceDistance rest)
        (Operational.execute model graph index
          (processOne settledName sourceDistance outgoing) state).2 := by
  simp only [processEdges, processOne]
  rw [Operational.execute_bind, Operational.execute_bind]
  rw [show Operational.execute model graph index
      (relaxationCandidate sourceDistance outgoing) state =
    (Model.semantics model graph index).step
      (.relaxationCandidate sourceDistance outgoing) state by rfl]
  cases hcandidate : (Model.semantics model graph index).step
      (.relaxationCandidate sourceDistance outgoing) state with
  | mk response afterCandidate =>
      cases response with
      | up candidate =>
          cases candidate with
          | none => rfl
          | some value =>
              simp only
              rw [Operational.execute_bind, Operational.execute_bind]
              rw [show Operational.execute model graph index
                  (changeKey
                    ⟨settledName, outgoing.target, outgoing.edge, outgoing.weight⟩
                    value) afterCandidate =
                (Model.semantics model graph index).step
                  (.changeKey
                    ⟨settledName, outgoing.target, outgoing.edge, outgoing.weight⟩
                    value) afterCandidate by rfl]
              cases (Model.semantics model graph index).step
                (.changeKey
                  ⟨settledName, outgoing.target, outgoing.edge, outgoing.weight⟩
                  value) afterCandidate
              rfl

/-- Processing an actual outgoing-row prefix preserves witnesses and relaxes that prefix. -/
theorem processEdges_facts
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source settledName : Fin
      (model.base.vertexEnumeration.vertices graph).length)
    (sourceDistance : Distance Weight)
    (row : List (IndexedOutgoingEdge
      (model.base.vertexEnumeration.vertices graph).length Edge Weight))
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (hqueue : Operational.QueueInvariant state)
    (hactiveLabels : ActiveLabelsAgree state)
    (hfiniteWitness : ∀ name, storedDistance state name ≠ ⊤ →
      HasPathWitness model graph index source name state)
    (hsettled : settledName ∈ state.settled)
    (hsourceDistance : sourceDistance = storedDistance state settledName)
    (hsourceWitness : HasPathWitness model graph index source settledName state)
    (hrow : ∀ outgoing, outgoing ∈ row → outgoing ∈
      Model.indexedOutgoingEdges model graph index settledName) :
    ProcessEdgesFacts model graph index source settledName sourceDistance row state
      (Operational.execute model graph index
        (processEdges settledName sourceDistance row) state).2 := by
  induction row generalizing state with
  | nil =>
      simp only [processEdges]
      refine ⟨hqueue, rfl, hactiveLabels, hfiniteWitness,
        fun _ => le_rfl, fun _ _ => rfl, ?_⟩
      simp
  | cons outgoing rest ih =>
      let afterOne := (Operational.execute model graph index
        (processOne settledName sourceDistance outgoing) state).2
      have hone := processOne_facts model graph index source settledName sourceDistance
        outgoing state hqueue hactiveLabels hfiniteWitness hsettled hsourceDistance
        hsourceWitness (hrow outgoing (by simp))
      change ProcessOneFacts model graph index source settledName outgoing state afterOne at hone
      have hsettledAfter : settledName ∈ afterOne.settled := by
        simpa [hone.settled] using hsettled
      have hrest := ih afterOne hone.queue hone.activeLabels hone.finiteWitness
        hsettledAfter
        (hsourceDistance.trans (hone.settled_distance settledName hsettled).symm)
        (hasPathWitness_of_distance_eq model graph index source settledName state afterOne
          (hone.settled_distance settledName hsettled) hsourceWitness)
        (fun edge hedge => hrow edge (by simp [hedge]))
      let final := (Operational.execute model graph index
        (processEdges settledName sourceDistance rest) afterOne).2
      change ProcessEdgesFacts model graph index source settledName sourceDistance rest
        afterOne final at hrest
      rw [processEdges_cons_execute model graph index settledName sourceDistance
        outgoing rest state]
      refine ⟨hrest.queue, hrest.settled.trans hone.settled,
        hrest.activeLabels, hrest.finiteWitness,
        fun name => (hrest.distance_mono name).trans (hone.distance_mono name),
        fun name hnameSettled => (hrest.settled_distance name (by
          simpa [hone.settled] using hnameSettled)).trans
            (hone.settled_distance name hnameSettled), ?_⟩
      intro edge hedge hactive
      rcases List.mem_cons.mp hedge with rfl | hedge
      · calc
          storedDistance final edge.target ≤
              storedDistance afterOne edge.target := hrest.distance_mono _
          _ ≤ storedDistance afterOne settledName +
              (edge.weight : Distance Weight) := hone.edge_relaxed <| by
                exact (hone.queue.active_iff_not_settled _).2 <| by
                  have hfresh := (hrest.queue.active_iff_not_settled _).1 hactive
                  simpa [hrest.settled] using hfresh
          _ = storedDistance final settledName +
              (edge.weight : Distance Weight) := by
                rw [hrest.settled_distance settledName hsettledAfter]
      · exact hrest.row_relaxed edge hedge hactive

omit [CanonicallyOrderedAdd Weight] in
/-- A shortest-path certificate transports across an unchanged distance-table cell. -/
theorem settledShortest_of_distance_eq
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source name : Fin (model.base.vertexEnumeration.vertices graph).length)
    (before after : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (heq : storedDistance after name = storedDistance before name)
    (hshortest : SettledShortest model graph index source name before) :
    SettledShortest model graph index source name after := by
  simpa [SettledShortest, RealizesDistance, heq] using hshortest

/-- A complete row scan preserves recursive predecessor reconstruction for all finite labels. -/
theorem processEdges_predecessorWitness
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source settledName : Fin
      (model.base.vertexEnumeration.vertices graph).length)
    (sourceDistance : Distance Weight)
    (row : List (IndexedOutgoingEdge
      (model.base.vertexEnumeration.vertices graph).length Edge Weight))
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (hqueue : Operational.QueueInvariant state)
    (hactiveLabels : ActiveLabelsAgree state)
    (hfiniteWitness : ∀ name, storedDistance state name ≠ ⊤ →
      HasPathWitness model graph index source name state)
    (hsourceSettled : source ∈ state.settled)
    (hsettled : settledName ∈ state.settled)
    (hsettledShortest : SettledShortest model graph index source settledName state)
    (hpredecessorWitness : ∀ name, storedDistance state name ≠ ⊤ →
      PredecessorReaches model graph index source state name)
    (hsourceDistance : sourceDistance = storedDistance state settledName)
    (hrow : ∀ outgoing, outgoing ∈ row → outgoing ∈
      Model.indexedOutgoingEdges model graph index settledName) :
    let after := (Operational.execute model graph index
      (processEdges settledName sourceDistance row) state).2
    ∀ name, storedDistance after name ≠ ⊤ →
      PredecessorReaches model graph index source after name := by
  dsimp only
  induction row generalizing state with
  | nil =>
      simpa [processEdges] using hpredecessorWitness
  | cons outgoing rest ih =>
      let afterOne := (Operational.execute model graph index
        (processOne settledName sourceDistance outgoing) state).2
      have honeFacts := processOne_facts model graph index source settledName
        sourceDistance outgoing state hqueue hactiveLabels hfiniteWitness hsettled
        hsourceDistance (hsettledShortest.elim fun path hpath => ⟨path, hpath.1⟩)
        (hrow outgoing (by simp))
      change ProcessOneFacts model graph index source settledName outgoing state afterOne
        at honeFacts
      have honePred := processOne_predecessorWitness model graph index source
        settledName sourceDistance outgoing state hqueue hactiveLabels hfiniteWitness
        hsourceSettled hsettledShortest hpredecessorWitness hsettled hsourceDistance
        (hrow outgoing (by simp))
      change ∀ name, storedDistance afterOne name ≠ ⊤ →
        PredecessorReaches model graph index source afterOne name at honePred
      have hrest := ih afterOne honeFacts.queue honeFacts.activeLabels
        honeFacts.finiteWitness (by simpa [honeFacts.settled] using hsourceSettled)
        (by simpa [honeFacts.settled] using hsettled)
        (settledShortest_of_distance_eq model graph index source settledName state afterOne
          (honeFacts.settled_distance settledName hsettled) hsettledShortest)
        honePred
        (hsourceDistance.trans (honeFacts.settled_distance settledName hsettled).symm)
        (fun edge hedge => hrow edge (by simp [hedge]))
      rw [processEdges_cons_execute model graph index settledName sourceDistance
        outgoing rest state]
      exact hrest

/-- One nonempty extraction followed by its full outgoing row preserves the textbook invariant. -/
theorem extractMin_processEdges_invariant
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length)
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (hinvariant : ShortestPathInvariant model graph index source state)
    (hne : 0 < state.heap.H.size)
    (hreachable : Reachable model.base.interface graph (index.decode source).val
      (index.decode state.heap.H[0].name).val) :
    let extracted := state.heap.H[0]
    let afterExtract :=
      ((Model.semantics model graph index).step (.extractMin) state).2
    let afterRow := (Operational.execute model graph index
      (processEdges extracted.name extracted.key
        (Model.indexedOutgoingEdges model graph index extracted.name)) afterExtract).2
    ShortestPathInvariant model graph index source afterRow := by
  let extracted := state.heap.H[0]
  let afterExtract :=
    ((Model.semantics model graph index).step (.extractMin) state).2
  let row := Model.indexedOutgoingEdges model graph index extracted.name
  let afterRow := (Operational.execute model graph index
    (processEdges extracted.name extracted.key row) afterExtract).2
  have hextract := Operational.extractMin_queueInvariant model graph index state
    hinvariant.queue hne
  dsimp only at hextract
  rcases hextract with ⟨_, hafterQueue, _, hafterSettled⟩
  change Operational.QueueInvariant afterExtract at hafterQueue
  change afterExtract.settled = state.settled ++ [extracted.name] at hafterSettled
  have hafterDistance (name : Fin
      (model.base.vertexEnumeration.vertices graph).length) :
      storedDistance afterExtract name = storedDistance state name := by
    rfl
  have hsettledAfterExtract {name} (hname : name ∈ state.settled) :
      name ∈ afterExtract.settled := by
    rw [hafterSettled]
    exact List.mem_append_left _ hname
  have hrootActive : state.heap.contains extracted.name = true := by
    exact (KleinbergPriorityQueue.Heap.contains_eq_true_iff_exists_contents
      state.heap hinvariant.queue.wellFormed.2.2 extracted.name).2 ⟨extracted.key,
      heap_root_contents state.heap hinvariant.queue.wellFormed hne⟩
  have hrootLabel : extracted.key = storedDistance state extracted.name := by
    exact Option.some.inj ((heap_root_contents state.heap
      hinvariant.queue.wellFormed hne).symm.trans
        (hinvariant.activeLabels extracted.name hrootActive))
  have hrootShortest := root_settledShortest model graph index source state
    hinvariant hne hreachable
  have hafterActiveLabels := extractMin_activeLabels model graph index state
    hinvariant.queue hinvariant.activeLabels hne
  change ActiveLabelsAgree afterExtract at hafterActiveLabels
  have hafterFinite := finiteWitness_of_distances_eq model graph index source
    state afterExtract hafterDistance hinvariant.finiteWitness
  have hrootWitnessAfter :
      HasPathWitness model graph index source extracted.name afterExtract := by
    exact hrootShortest.elim fun path hpath => ⟨path, by
      simpa [RealizesDistance, hafterDistance] using hpath.1⟩
  have hrowFacts := processEdges_facts model graph index source extracted.name
    extracted.key row afterExtract hafterQueue hafterActiveLabels hafterFinite
    (by simp [hafterSettled])
    (by rw [hafterDistance]; exact hrootLabel)
    hrootWitnessAfter (by intro outgoing houtgoing; exact houtgoing)
  change ProcessEdgesFacts model graph index source extracted.name extracted.key row
    afterExtract afterRow at hrowFacts
  refine ⟨hrowFacts.queue, ?_, hrowFacts.activeLabels,
    hrowFacts.finiteWitness, ?_, ?_⟩
  · rw [hrowFacts.settled]
    exact hsettledAfterExtract hinvariant.source_settled
  · intro name hnameSettled
    rw [hrowFacts.settled, hafterSettled] at hnameSettled
    simp only [List.mem_append, List.mem_singleton] at hnameSettled
    rcases hnameSettled with hnameOld | hnameRoot
    · apply settledShortest_of_distance_eq model graph index source name state afterRow
      · exact (hrowFacts.settled_distance name (hsettledAfterExtract hnameOld)).trans
          (hafterDistance name)
      · exact hinvariant.settledShortest name hnameOld
    · subst name
      apply settledShortest_of_distance_eq model graph index source extracted.name state afterRow
      · exact (hrowFacts.settled_distance extracted.name (by
            simp [hafterSettled])).trans (hafterDistance extracted.name)
      · exact hrootShortest
  · intro settledName hnameSettled outgoing houtgoing htargetActive
    rw [hrowFacts.settled, hafterSettled] at hnameSettled
    simp only [List.mem_append, List.mem_singleton] at hnameSettled
    rcases hnameSettled with hnameOld | hnameRoot
    · have htargetFreshAfter : outgoing.target ∉ afterExtract.settled := by
        have htargetFreshFinal :=
          (hrowFacts.queue.active_iff_not_settled outgoing.target).1 htargetActive
        simpa [hrowFacts.settled] using htargetFreshFinal
      have htargetActiveAfter :=
        (hafterQueue.active_iff_not_settled outgoing.target).2 htargetFreshAfter
      have htargetActiveBefore : state.heap.contains outgoing.target = true := by
        apply ((KleinbergPriorityQueue.Heap.extractMin_contains_eq_true_iff
          state.heap hinvariant.queue.wellFormed hne outgoing.target).1 ?_).2
        simpa [afterExtract, Model.semantics] using htargetActiveAfter
      calc
        storedDistance afterRow outgoing.target ≤
            storedDistance afterExtract outgoing.target := hrowFacts.distance_mono _
        _ = storedDistance state outgoing.target := hafterDistance _
        _ ≤ storedDistance state settledName +
            (outgoing.weight : Distance Weight) :=
          hinvariant.relaxed settledName hnameOld outgoing houtgoing htargetActiveBefore
        _ = storedDistance afterRow settledName +
            (outgoing.weight : Distance Weight) := by
          rw [hrowFacts.settled_distance settledName (hsettledAfterExtract hnameOld)]
          rw [hafterDistance]
    · subst settledName
      exact hrowFacts.row_relaxed outgoing houtgoing htargetActive

/-- Extraction and its row scan preserve both shortestness and predecessor reconstruction. -/
theorem extractMin_processEdges_fullInvariant
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length)
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (hinvariant : FullInvariant model graph index source state)
    (hne : 0 < state.heap.H.size)
    (hreachable : Reachable model.base.interface graph (index.decode source).val
      (index.decode state.heap.H[0].name).val) :
    let extracted := state.heap.H[0]
    let afterExtract :=
      ((Model.semantics model graph index).step (.extractMin) state).2
    let row := Model.indexedOutgoingEdges model graph index extracted.name
    let afterRow := (Operational.execute model graph index
      (processEdges extracted.name extracted.key row) afterExtract).2
    FullInvariant model graph index source afterRow := by
  dsimp only
  let extracted := state.heap.H[0]
  let afterExtract :=
    ((Model.semantics model graph index).step (.extractMin) state).2
  let row := Model.indexedOutgoingEdges model graph index extracted.name
  let afterRow := (Operational.execute model graph index
    (processEdges extracted.name extracted.key row) afterExtract).2
  have hshortest := extractMin_processEdges_invariant model graph index source state
    hinvariant.shortest hne hreachable
  change ShortestPathInvariant model graph index source afterRow at hshortest
  have hextract := Operational.extractMin_queueInvariant model graph index state
    hinvariant.shortest.queue hne
  dsimp only at hextract
  rcases hextract with ⟨_, hafterQueue, _, hafterSettled⟩
  change Operational.QueueInvariant afterExtract at hafterQueue
  change afterExtract.settled = state.settled ++ [extracted.name] at hafterSettled
  have hafterDistance (name : Fin
      (model.base.vertexEnumeration.vertices graph).length) :
      storedDistance afterExtract name = storedDistance state name := by rfl
  have hafterPredecessor (name : Fin
      (model.base.vertexEnumeration.vertices graph).length) :
      storedPredecessor afterExtract name = storedPredecessor state name := by rfl
  have hrootActive : state.heap.contains extracted.name = true := by
    exact (KleinbergPriorityQueue.Heap.contains_eq_true_iff_exists_contents
      state.heap hinvariant.shortest.queue.wellFormed.2.2 extracted.name).2 ⟨extracted.key,
      heap_root_contents state.heap hinvariant.shortest.queue.wellFormed hne⟩
  have hrootLabel : extracted.key = storedDistance state extracted.name := by
    exact Option.some.inj ((heap_root_contents state.heap
      hinvariant.shortest.queue.wellFormed hne).symm.trans
        (hinvariant.shortest.activeLabels extracted.name hrootActive))
  have hafterActive := extractMin_activeLabels model graph index state
    hinvariant.shortest.queue hinvariant.shortest.activeLabels hne
  change ActiveLabelsAgree afterExtract at hafterActive
  have hafterFinite := finiteWitness_of_distances_eq model graph index source
    state afterExtract hafterDistance hinvariant.shortest.finiteWitness
  have hafterPred : ∀ name, storedDistance afterExtract name ≠ ⊤ →
      PredecessorReaches model graph index source afterExtract name := by
    intro name hfinite
    apply predecessorReaches_transport_tables model graph index source state afterExtract
    · intro settledName hsettled
      rw [hafterSettled]
      exact List.mem_append_left _ hsettled
    · exact hafterPredecessor
    · exact hafterDistance
    · exact hinvariant.predecessorWitness name fun htop =>
        hfinite ((hafterDistance name).trans htop)
  have hrowPred := processEdges_predecessorWitness model graph index source
    extracted.name extracted.key row afterExtract hafterQueue hafterActive hafterFinite
    (by
      rw [hafterSettled]
      exact List.mem_append_left _ hinvariant.shortest.source_settled)
    (by simp [hafterSettled])
    (settledShortest_of_distance_eq model graph index source extracted.name state
      afterExtract (hafterDistance extracted.name)
      (root_settledShortest model graph index source state hinvariant.shortest hne hreachable))
    hafterPred
    (by rw [hafterDistance]; exact hrootLabel)
    (by intro outgoing houtgoing; exact houtgoing)
  change ∀ name, storedDistance afterRow name ≠ ⊤ →
    PredecessorReaches model graph index source afterRow name at hrowPred
  exact ⟨hshortest, hrowPred⟩

/-- Every executable loop prefix preserves Claim (4.14)'s shortest-path invariant. -/
theorem dijkstraLoop_invariant
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length)
    (fuel : Nat)
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (hinvariant : ShortestPathInvariant model graph index source state)
    (hfuel : fuel ≤ state.heap.H.size)
    (hallReachable : ∀ name,
      Reachable model.base.interface graph (index.decode source).val
        (index.decode name).val) :
    ShortestPathInvariant model graph index source
      (Operational.execute model graph index
        (dijkstraLoop (Edge := Edge) (Weight := Weight) fuel) state).2 := by
  induction fuel generalizing state with
  | zero => simpa [dijkstraLoop]
  | succ fuel ih =>
      have hne : 0 < state.heap.H.size := by omega
      let extracted := state.heap.H[0]
      let afterExtract :=
        ((Model.semantics model graph index).step (.extractMin) state).2
      let row := Model.indexedOutgoingEdges model graph index extracted.name
      let afterRow := (Operational.execute model graph index
        (processEdges extracted.name extracted.key row) afterExtract).2
      have hstep := extractMin_processEdges_invariant model graph index source state
        hinvariant hne (hallReachable extracted.name)
      change ShortestPathInvariant model graph index source afterRow at hstep
      have hremaining : fuel ≤ afterRow.heap.H.size := by
        rw [Operational.processEdges_heap_size]
        have hafterSize := (Operational.extractMin_queueInvariant model graph index
          state hinvariant.queue hne).2.2.1
        change afterExtract.heap.H.size + 1 = state.heap.H.size at hafterSize
        omega
      have hfinal := ih afterRow hstep hremaining
      rw [Operational.execute_dijkstraLoop_succ model graph index fuel state hne]
      exact hfinal

/-- Every executable loop prefix preserves shortestness and predecessor reconstruction together. -/
theorem dijkstraLoop_fullInvariant
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length)
    (fuel : Nat)
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (hinvariant : FullInvariant model graph index source state)
    (hfuel : fuel ≤ state.heap.H.size)
    (hallReachable : ∀ name,
      Reachable model.base.interface graph (index.decode source).val
        (index.decode name).val) :
    FullInvariant model graph index source
      (Operational.execute model graph index
        (dijkstraLoop (Edge := Edge) (Weight := Weight) fuel) state).2 := by
  induction fuel generalizing state with
  | zero => simpa [dijkstraLoop]
  | succ fuel ih =>
      have hne : 0 < state.heap.H.size := by omega
      let extracted := state.heap.H[0]
      let afterExtract :=
        ((Model.semantics model graph index).step (.extractMin) state).2
      let row := Model.indexedOutgoingEdges model graph index extracted.name
      let afterRow := (Operational.execute model graph index
        (processEdges extracted.name extracted.key row) afterExtract).2
      have hstep := extractMin_processEdges_fullInvariant model graph index source state
        hinvariant hne (hallReachable extracted.name)
      change FullInvariant model graph index source afterRow at hstep
      have hremaining : fuel ≤ afterRow.heap.H.size := by
        rw [Operational.processEdges_heap_size]
        have hafterSize := (Operational.extractMin_queueInvariant model graph index
          state hinvariant.shortest.queue hne).2.2.1
        change afterExtract.heap.H.size + 1 = state.heap.H.size at hafterSize
        omega
      have hfinal := ih afterRow hstep hremaining
      rw [Operational.execute_dijkstraLoop_succ model graph index fuel state hne]
      exact hfinal

/-! ### Concrete initialization and end-to-end Claim (4.14) -/

omit [CanonicallyOrderedAdd Weight] in
@[simp] theorem initializeState_storedDistance
    (n : Nat) (source name : Fin n) :
    storedDistance (Model.initializeState n Edge Weight source).2 name =
      if name = source then 0 else ⊤ := by
  by_cases hname : name = source
  · subst name
    simp [storedDistance, Model.initializeState]
  · have hvals : source.val ≠ name.val := by
      intro heq
      exact hname (Fin.ext heq.symm)
    simp [storedDistance, Model.initializeState, hname, hvals]

omit [CanonicallyOrderedAdd Weight] in
@[simp] theorem initializeState_storedPredecessor
    (n : Nat) (source name : Fin n) :
    storedPredecessor (Model.initializeState n Edge Weight source).2 name = none := by
  simp [storedPredecessor, Model.initializeState]

omit [CanonicallyOrderedAdd Weight] in
/-- Initialization's logical heap map contains exactly the advertised initial labels. -/
theorem initializeState_heap_contents
    (n : Nat) (source name : Fin n) :
    (Model.initializeState n Edge Weight source).2.heap.contents name =
      some (if name = source then 0 else ⊤) := by
  exact Operational.initializeState_contents (Edge := Edge) n source name

omit [CanonicallyOrderedAdd Weight] in
/-- Heap keys and the persistent distance table agree immediately after initialization. -/
theorem initializeState_activeLabels (n : Nat) (source : Fin n) :
    ActiveLabelsAgree (Model.initializeState n Edge Weight source).2 := by
  intro name _
  rw [initializeState_heap_contents, initializeState_storedDistance]

/-- The unique finite initial key forces the first heap root to be the source at distance zero. -/
theorem initializeState_root (n : Nat) (source : Fin n) :
    let state := (Model.initializeState n Edge Weight source).2
    ∃ hne : 0 < state.heap.H.size,
      state.heap.H[0].name = source ∧ state.heap.H[0].key = 0 := by
  let state := (Model.initializeState n Edge Weight source).2
  have hne : 0 < state.heap.H.size := by
    rw [show state.heap.H.size = n from
      Operational.initializeState_heap_size (Edge := Edge) n source]
    exact lt_of_le_of_lt (Nat.zero_le source.val) source.isLt
  have hwellFormed : state.heap.WellFormed :=
    (Operational.initializeState_queueInvariant (Edge := Edge) n source).wellFormed
  have hsourceContents : state.heap.contents source = some 0 := by
    simpa [state] using
      initializeState_heap_contents (Edge := Edge) (Weight := Weight) n source source
  have hrootLe : state.heap.H[0].key ≤ 0 :=
    heap_root_le_contents state.heap hwellFormed hne source 0 hsourceContents
  have hrootNonnegative : (0 : Distance Weight) ≤ state.heap.H[0].key := by
    simp
  have hrootKey : state.heap.H[0].key = 0 :=
    le_antisymm hrootLe hrootNonnegative
  have hrootContents := heap_root_contents state.heap hwellFormed hne
  have hlogical :=
    initializeState_heap_contents (Edge := Edge) (Weight := Weight) n source
      state.heap.H[0].name
  have hrootInitial :
      (if state.heap.H[0].name = source then
        (0 : Distance Weight) else (⊤ : Distance Weight)) =
        state.heap.H[0].key := Option.some.inj (hlogical.symm.trans hrootContents)
  have hrootName : state.heap.H[0].name = source := by
    by_contra hneSource
    rw [if_neg hneSource, hrootKey] at hrootInitial
    exact WithTop.top_ne_zero hrootInitial
  exact ⟨hne, hrootName, hrootKey⟩

/-- The empty source path realizes the initialized zero label and is shortest. -/
theorem initializeState_source_shortest
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length) :
    SettledShortest model graph index source source
      (Model.initializeState
        (model.base.vertexEnumeration.vertices graph).length Edge Weight source).2 := by
  letI := weightedArcQuiver model.edgeView graph
  refine ⟨Quiver.Path.nil, ?_, ?_⟩
  · unfold RealizesDistance
    simp [networkPathWeight, pathWeight]
  · intro alternative
    simp [pathWeight]

/-- Initialization followed by the first extraction and row scan establishes the loop invariant. -/
theorem initialize_firstIteration_invariant
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length) :
    let initial := (Model.initializeState
      (model.base.vertexEnumeration.vertices graph).length Edge Weight source).2
    let afterExtract :=
      ((Model.semantics model graph index).step (.extractMin) initial).2
    let row := Model.indexedOutgoingEdges model graph index source
    let afterRow := (Operational.execute model graph index
      (processEdges source 0 row) afterExtract).2
    ShortestPathInvariant model graph index source afterRow := by
  let n := (model.base.vertexEnumeration.vertices graph).length
  let initial := (Model.initializeState n Edge Weight source).2
  let afterExtract :=
    ((Model.semantics model graph index).step (.extractMin) initial).2
  let row := Model.indexedOutgoingEdges model graph index source
  let afterRow := (Operational.execute model graph index
    (processEdges source 0 row) afterExtract).2
  have hinitialQueue :=
    Operational.initializeState_queueInvariant (Edge := Edge) (Weight := Weight) n source
  change Operational.QueueInvariant initial at hinitialQueue
  have hinitialSize := Operational.initializeState_heap_size
    (Edge := Edge) (Weight := Weight) n source
  change initial.heap.H.size = n at hinitialSize
  obtain ⟨hne, hrootName, hrootKey⟩ :=
    initializeState_root (Edge := Edge) (Weight := Weight) n source
  change 0 < initial.heap.H.size at hne
  have hroot : initial.heap.H[0].name = source ∧ initial.heap.H[0].key = 0 := by
    exact ⟨hrootName, hrootKey⟩
  have hextract := Operational.extractMin_queueInvariant model graph index initial
    hinitialQueue hne
  dsimp only at hextract
  have hafterQueue := hextract.2.1
  have hafterSettled := hextract.2.2.2
  change Operational.QueueInvariant afterExtract at hafterQueue
  change afterExtract.settled = initial.settled ++ [initial.heap.H[0].name]
    at hafterSettled
  have hafterSettledSource : afterExtract.settled = [source] := by
    rw [hafterSettled]
    have hinitialSettled : initial.settled = [] := by rfl
    rw [hinitialSettled, hroot.1]
    rfl
  have hafterDistance (name : Fin n) :
      storedDistance afterExtract name = storedDistance initial name := by
    rfl
  have hinitialActive :=
    initializeState_activeLabels (Edge := Edge) (Weight := Weight) n source
  change ActiveLabelsAgree initial at hinitialActive
  have hafterActive : ActiveLabelsAgree afterExtract := by
    intro name hactive
    have hactiveIff := KleinbergPriorityQueue.Heap.extractMin_contains_eq_true_iff
      initial.heap hinitialQueue.wellFormed hne name
    have hactive' : initial.heap.extractMin.1.contains name = true := by
      simpa [afterExtract, Model.semantics] using hactive
    have hparts := hactiveIff.1 hactive'
    have hcontents := (KleinbergPriorityQueue.Heap.extractMin_contents
      initial.heap hinitialQueue.wellFormed hne).2 name hparts.1
    change initial.heap.extractMin.1.contents name =
      some (storedDistance afterExtract name)
    rw [hcontents, hafterDistance]
    exact hinitialActive name hparts.2
  have hinitialFinite : ∀ name, storedDistance initial name ≠ ⊤ →
      HasPathWitness model graph index source name initial := by
    intro name hfinite
    have hdistance :=
      initializeState_storedDistance (Edge := Edge) (Weight := Weight) n source name
    change storedDistance initial name = if name = source then 0 else ⊤ at hdistance
    by_cases hname : name = source
    · subst name
      rcases initializeState_source_shortest model graph index source with
        ⟨path, hrealizes, _⟩
      exact ⟨path, hrealizes⟩
    · exfalso
      apply hfinite
      rw [hdistance, if_neg hname]
  have hafterFinite : ∀ name, storedDistance afterExtract name ≠ ⊤ →
      HasPathWitness model graph index source name afterExtract := by
    intro name hfinite
    apply hasPathWitness_of_distance_eq model graph index source name initial afterExtract
      (hafterDistance name)
    apply hinitialFinite name
    intro htop
    apply hfinite
    rw [hafterDistance, htop]
  have hsourceWitness : HasPathWitness model graph index source source afterExtract := by
    apply hafterFinite source
    rw [hafterDistance]
    simp [initial]
  have hrowFacts := processEdges_facts model graph index source source 0 row afterExtract
    hafterQueue hafterActive hafterFinite (by simp [hafterSettledSource])
    (by rw [hafterDistance]; simp [initial])
    hsourceWitness (by intro outgoing houtgoing; exact houtgoing)
  change ProcessEdgesFacts model graph index source source 0 row afterExtract afterRow
    at hrowFacts
  refine ⟨hrowFacts.queue, ?_, hrowFacts.activeLabels,
    hrowFacts.finiteWitness, ?_, ?_⟩
  · rw [hrowFacts.settled, hafterSettledSource]
    simp
  · intro name hnameSettled
    rw [hrowFacts.settled, hafterSettledSource] at hnameSettled
    simp only [List.mem_singleton] at hnameSettled
    subst name
    apply settledShortest_of_distance_eq model graph index source source initial afterRow
    · rw [hrowFacts.settled_distance source (by simp [hafterSettledSource])]
      exact hafterDistance source
    · exact initializeState_source_shortest model graph index source
  · intro settledName hnameSettled outgoing houtgoing htargetActive
    rw [hrowFacts.settled, hafterSettledSource] at hnameSettled
    simp only [List.mem_singleton] at hnameSettled
    subst settledName
    exact hrowFacts.row_relaxed outgoing houtgoing htargetActive

/-- The first initialized iteration also establishes exact predecessor reconstruction. -/
theorem initialize_firstIteration_fullInvariant
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length) :
    let initial := (Model.initializeState
      (model.base.vertexEnumeration.vertices graph).length Edge Weight source).2
    let afterExtract :=
      ((Model.semantics model graph index).step (.extractMin) initial).2
    let row := Model.indexedOutgoingEdges model graph index source
    let afterRow := (Operational.execute model graph index
      (processEdges source 0 row) afterExtract).2
    FullInvariant model graph index source afterRow := by
  dsimp only
  let n := (model.base.vertexEnumeration.vertices graph).length
  let initial := (Model.initializeState n Edge Weight source).2
  let afterExtract :=
    ((Model.semantics model graph index).step (.extractMin) initial).2
  let row := Model.indexedOutgoingEdges model graph index source
  let afterRow := (Operational.execute model graph index
    (processEdges source 0 row) afterExtract).2
  have hinitialQueue := Operational.initializeState_queueInvariant
    (Edge := Edge) (Weight := Weight) n source
  change Operational.QueueInvariant initial at hinitialQueue
  obtain ⟨hne, hrootName, _⟩ :=
    initializeState_root (Edge := Edge) (Weight := Weight) n source
  change 0 < initial.heap.H.size at hne
  have hextract := Operational.extractMin_queueInvariant model graph index initial
    hinitialQueue hne
  dsimp only at hextract
  rcases hextract with ⟨_, hafterQueue, _, hafterSettled⟩
  change Operational.QueueInvariant afterExtract at hafterQueue
  change afterExtract.settled = initial.settled ++ [initial.heap.H[0].name]
    at hafterSettled
  have hafterSettledSource : afterExtract.settled = [source] := by
    rw [hafterSettled, hrootName]
    rfl
  have hafterDistance (name : Fin n) :
      storedDistance afterExtract name = storedDistance initial name := by rfl
  have hafterPredecessor (name : Fin n) :
      storedPredecessor afterExtract name = storedPredecessor initial name := by rfl
  have hinitialActive :=
    initializeState_activeLabels (Edge := Edge) (Weight := Weight) n source
  change ActiveLabelsAgree initial at hinitialActive
  have hafterActive := extractMin_activeLabels model graph index initial
    hinitialQueue hinitialActive hne
  change ActiveLabelsAgree afterExtract at hafterActive
  have hinitialFinite : ∀ name, storedDistance initial name ≠ ⊤ →
      HasPathWitness model graph index source name initial := by
    intro name hfinite
    by_cases hname : name = source
    · subst name
      exact (initializeState_source_shortest model graph index source).elim
        fun path hpath => ⟨path, hpath.1⟩
    · simp [initial, hname] at hfinite
  have hafterFinite := finiteWitness_of_distances_eq model graph index source
    initial afterExtract hafterDistance hinitialFinite
  have hsourceShortestAfter := settledShortest_of_distance_eq model graph index
    source source initial afterExtract (hafterDistance source)
      (initializeState_source_shortest model graph index source)
  have hsourceWitness : HasPathWitness model graph index source source afterExtract :=
    hsourceShortestAfter.elim fun path hpath => ⟨path, hpath.1⟩
  have hsourceDistanceAfter : (0 : Distance Weight) = storedDistance afterExtract source := by
    rw [hafterDistance]
    simp [initial]
  have hrowFacts := processEdges_facts model graph index source source 0 row afterExtract
    hafterQueue hafterActive hafterFinite (by simp [hafterSettledSource])
    hsourceDistanceAfter
    hsourceWitness (by intro outgoing houtgoing; exact houtgoing)
  change ProcessEdgesFacts model graph index source source 0 row afterExtract afterRow
    at hrowFacts
  have hshortest : ShortestPathInvariant model graph index source afterRow := by
    refine ⟨hrowFacts.queue, ?_, hrowFacts.activeLabels,
      hrowFacts.finiteWitness, ?_, ?_⟩
    · simp [hrowFacts.settled, hafterSettledSource]
    · intro name hnameSettled
      simp only [hrowFacts.settled, hafterSettledSource, List.mem_singleton]
        at hnameSettled
      subst name
      exact settledShortest_of_distance_eq model graph index source source afterExtract
        afterRow (hrowFacts.settled_distance source (by simp [hafterSettledSource]))
        hsourceShortestAfter
    · intro settledName hnameSettled outgoing houtgoing htargetActive
      simp only [hrowFacts.settled, hafterSettledSource, List.mem_singleton]
        at hnameSettled
      subst settledName
      exact hrowFacts.row_relaxed outgoing houtgoing htargetActive
  have hinitialPred : ∀ name, storedDistance initial name ≠ ⊤ →
      PredecessorReaches model graph index source initial name := by
    intro name hfinite
    by_cases hname : name = source
    · subst name
      exact PredecessorReaches.source
        (initializeState_storedPredecessor
          (Edge := Edge) (Weight := Weight) n source source)
        (hsourceDistanceAfter.trans (hafterDistance source)).symm
    · simp [initial, hname] at hfinite
  have hafterPred : ∀ name, storedDistance afterExtract name ≠ ⊤ →
      PredecessorReaches model graph index source afterExtract name := by
    intro name hfinite
    apply predecessorReaches_transport_tables model graph index source initial afterExtract
    · intro settledName hsettled
      simp [initial, Model.initializeState] at hsettled
    · exact hafterPredecessor
    · exact hafterDistance
    · exact hinitialPred name fun htop =>
        hfinite ((hafterDistance name).trans htop)
  have hrowPred := processEdges_predecessorWitness model graph index source source 0
    row afterExtract hafterQueue hafterActive hafterFinite
    (by simp [hafterSettledSource]) (by simp [hafterSettledSource])
    hsourceShortestAfter hafterPred
    hsourceDistanceAfter
    (by intro outgoing houtgoing; exact houtgoing)
  change ∀ name, storedDistance afterRow name ≠ ⊤ →
    PredecessorReaches model graph index source afterRow name at hrowPred
  exact ⟨hshortest, hrowPred⟩

/-- The vertex-count loop started from the concrete initialized state satisfies the invariant. -/
theorem initialized_dijkstraLoop_invariant
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length)
    (hallReachable : ∀ name,
      Reachable model.base.interface graph (index.decode source).val
        (index.decode name).val) :
    let n := (model.base.vertexEnumeration.vertices graph).length
    let initial := (Model.initializeState n Edge Weight source).2
    ShortestPathInvariant model graph index source
      (Operational.execute model graph index
        (dijkstraLoop (Edge := Edge) (Weight := Weight) n) initial).2 := by
  let n := (model.base.vertexEnumeration.vertices graph).length
  let initial := (Model.initializeState n Edge Weight source).2
  let afterExtract :=
    ((Model.semantics model graph index).step (.extractMin) initial).2
  let row := Model.indexedOutgoingEdges model graph index source
  let afterRow := (Operational.execute model graph index
    (processEdges source 0 row) afterExtract).2
  have hbootstrap := initialize_firstIteration_invariant model graph index source
  change ShortestPathInvariant model graph index source afterRow at hbootstrap
  obtain ⟨hne, hrootName, hrootKey⟩ :=
    initializeState_root (Edge := Edge) (Weight := Weight) n source
  change 0 < initial.heap.H.size at hne
  have hroot : initial.heap.H[0].name = source ∧ initial.heap.H[0].key = 0 :=
    ⟨hrootName, hrootKey⟩
  have hinitialQueue := Operational.initializeState_queueInvariant
    (Edge := Edge) (Weight := Weight) n source
  change Operational.QueueInvariant initial at hinitialQueue
  have hextract := Operational.extractMin_queueInvariant model graph index initial
    hinitialQueue hne
  dsimp only at hextract
  have hresponse := hextract.1
  have hafterSize := hextract.2.2.1
  change afterExtract.heap.H.size + 1 = initial.heap.H.size at hafterSize
  have hinitialSize := Operational.initializeState_heap_size
    (Edge := Edge) (Weight := Weight) n source
  change initial.heap.H.size = n at hinitialSize
  have hrowSize : afterRow.heap.H.size = afterExtract.heap.H.size := by
    exact Operational.processEdges_heap_size model graph index source 0 row afterExtract
  have hremaining : n - 1 ≤ afterRow.heap.H.size := by omega
  have hrest := dijkstraLoop_invariant model graph index source (n - 1) afterRow
    hbootstrap hremaining hallReachable
  have hnSucc : n = (n - 1) + 1 := by
    have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le source.val) source.isLt
    omega
  change ShortestPathInvariant model graph index source
    (Operational.execute model graph index
      (dijkstraLoop (Edge := Edge) (Weight := Weight) n) initial).2
  rw [hnSucc]
  simp only [dijkstraLoop]
  rw [Operational.execute_bind]
  rw [show Operational.execute model graph index
      (extractMin (Edge := Edge) (Weight := Weight)) initial =
    (Model.semantics model graph index).step (.extractMin) initial by rfl]
  have hextractEq : (Model.semantics model graph index).step
      (.extractMin : Op n Edge Weight) initial =
        (ULift.up (some initial.heap.H[0]), afterExtract) := by
    apply Prod.ext
    · exact hresponse
    · rfl
  rw [hextractEq]
  simp only
  rw [Operational.execute_bind]
  rw [show Operational.execute model graph index
      (outgoingEdges initial.heap.H[0].name) afterExtract =
    (Model.semantics model graph index).step
      (.outgoingEdges initial.heap.H[0].name) afterExtract by rfl]
  rw [show (Model.semantics model graph index).step
      (.outgoingEdges initial.heap.H[0].name) afterExtract = (row, afterExtract) by
        change (Model.indexedOutgoingEdges model graph index
          initial.heap.H[0].name, afterExtract) = (row, afterExtract)
        rw [hroot.1]]
  simp only
  rw [Operational.execute_bind]
  simpa [hroot.1, hroot.2] using hrest

/-- The concrete initialized vertex-count loop satisfies the complete Claim (4.14) invariant. -/
theorem initialized_dijkstraLoop_fullInvariant
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length)
    (hallReachable : ∀ name,
      Reachable model.base.interface graph (index.decode source).val
        (index.decode name).val) :
    let n := (model.base.vertexEnumeration.vertices graph).length
    let initial := (Model.initializeState n Edge Weight source).2
    FullInvariant model graph index source
      (Operational.execute model graph index
        (dijkstraLoop (Edge := Edge) (Weight := Weight) n) initial).2 := by
  let n := (model.base.vertexEnumeration.vertices graph).length
  let initial := (Model.initializeState n Edge Weight source).2
  let afterExtract :=
    ((Model.semantics model graph index).step (.extractMin) initial).2
  let row := Model.indexedOutgoingEdges model graph index source
  let afterRow := (Operational.execute model graph index
    (processEdges source 0 row) afterExtract).2
  have hbootstrap := initialize_firstIteration_fullInvariant model graph index source
  change FullInvariant model graph index source afterRow at hbootstrap
  obtain ⟨hne, hrootName, hrootKey⟩ :=
    initializeState_root (Edge := Edge) (Weight := Weight) n source
  change 0 < initial.heap.H.size at hne
  have hroot : initial.heap.H[0].name = source ∧ initial.heap.H[0].key = 0 :=
    ⟨hrootName, hrootKey⟩
  have hinitialQueue := Operational.initializeState_queueInvariant
    (Edge := Edge) (Weight := Weight) n source
  change Operational.QueueInvariant initial at hinitialQueue
  have hextract := Operational.extractMin_queueInvariant model graph index initial
    hinitialQueue hne
  dsimp only at hextract
  have hresponse := hextract.1
  have hafterSize := hextract.2.2.1
  change afterExtract.heap.H.size + 1 = initial.heap.H.size at hafterSize
  have hinitialSize := Operational.initializeState_heap_size
    (Edge := Edge) (Weight := Weight) n source
  change initial.heap.H.size = n at hinitialSize
  have hrowSize : afterRow.heap.H.size = afterExtract.heap.H.size := by
    exact Operational.processEdges_heap_size model graph index source 0 row afterExtract
  have hremaining : n - 1 ≤ afterRow.heap.H.size := by omega
  have hrest := dijkstraLoop_fullInvariant model graph index source (n - 1) afterRow
    hbootstrap hremaining hallReachable
  have hnSucc : n = (n - 1) + 1 := by
    have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le source.val) source.isLt
    omega
  change FullInvariant model graph index source
    (Operational.execute model graph index
      (dijkstraLoop (Edge := Edge) (Weight := Weight) n) initial).2
  rw [hnSucc]
  simp only [dijkstraLoop]
  rw [Operational.execute_bind]
  rw [show Operational.execute model graph index
      (extractMin (Edge := Edge) (Weight := Weight)) initial =
    (Model.semantics model graph index).step (.extractMin) initial by rfl]
  have hextractEq : (Model.semantics model graph index).step
      (.extractMin : Op n Edge Weight) initial =
        (ULift.up (some initial.heap.H[0]), afterExtract) := by
    apply Prod.ext
    · exact hresponse
    · rfl
  rw [hextractEq]
  simp only
  rw [Operational.execute_bind]
  rw [show Operational.execute model graph index
      (outgoingEdges initial.heap.H[0].name) afterExtract =
    (Model.semantics model graph index).step
      (.outgoingEdges initial.heap.H[0].name) afterExtract by rfl]
  rw [show (Model.semantics model graph index).step
      (.outgoingEdges initial.heap.H[0].name) afterExtract = (row, afterExtract) by
        change (Model.indexedOutgoingEdges model graph index
          initial.heap.H[0].name, afterExtract) = (row, afterExtract)
        rw [hroot.1]]
  simp only
  rw [Operational.execute_bind]
  simpa [hroot.1, hroot.2] using hrest

/-- End-to-end complete invariant for the actual pure Dijkstra runner. -/
theorem dijkstra_fullInvariant
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length)
    (hallReachable : ∀ name,
      Reachable model.base.interface graph (index.decode source).val
        (index.decode name).val) :
    FullInvariant model graph index source
      (Interpreter.eval model graph index source).2 := by
  let n := (model.base.vertexEnumeration.vertices graph).length
  let initial := (Model.initializeState n Edge Weight source).2
  have hloop := initialized_dijkstraLoop_fullInvariant model graph index source
    hallReachable
  change FullInvariant model graph index source
    (Operational.execute model graph index
      (dijkstraLoop (Edge := Edge) (Weight := Weight) n) initial).2 at hloop
  change FullInvariant model graph index source
    (Operational.execute model graph index
      (dijkstra (Edge := Edge) (Weight := Weight) n source)
      (Model.initialState n Edge Weight)).2
  simp only [dijkstra]
  rw [Operational.execute_bind]
  rw [show Operational.execute model graph index
      (KleinbergDijkstra.initialize (Edge := Edge) (Weight := Weight) source)
        (Model.initialState n Edge Weight) =
    (Model.semantics model graph index).step (.initialize source)
      (Model.initialState n Edge Weight) by rfl]
  have hinitialize : (Model.semantics model graph index).step (.initialize source)
      (Model.initialState n Edge Weight) = (ULift.up true, initial) := by
    apply Prod.ext
    · change ULift.up (Model.initializeState n Edge Weight source).1 = ULift.up true
      congr 1
      exact Operational.initializeState_success
        (Edge := Edge) (Weight := Weight) n source
    · rfl
  rw [hinitialize]
  simp only [if_pos]
  exact hloop

/-- End-to-end invariant for the actual pure Dijkstra runner. -/
theorem dijkstra_invariant
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length)
    (hallReachable : ∀ name,
      Reachable model.base.interface graph (index.decode source).val
        (index.decode name).val) :
    ShortestPathInvariant model graph index source
      (Interpreter.eval model graph index source).2 :=
  (dijkstra_fullInvariant model graph index source hallReachable).shortest

/--
The predecessor table reconstructs an exact stored-weight path, and every path realizing that
stored weight is shortest. The universal second component applies in particular to the path
constructed by `predecessorReaches_path`.
-/
def PredecessorReconstructedShortest
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source name : Fin (model.base.vertexEnumeration.vertices graph).length)
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight) : Prop :=
  PredecessorReaches model graph index source state name ∧
    ∀ path : NetworkPath model.edgeView graph
        (index.decode source).val (index.decode name).val,
      RealizesDistance model graph index source name state path →
        IsShortestPath model.edgeView graph path

omit [CanonicallyOrderedAdd Weight] in
/-- Extract the concrete shortest path denoted by a predecessor-reconstruction certificate. -/
theorem predecessorReconstructedShortest_path
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source name : Fin (model.base.vertexEnumeration.vertices graph).length)
    (state : Model.State
      (model.base.vertexEnumeration.vertices graph).length Edge Weight)
    (hcorrect : PredecessorReconstructedShortest model graph index source name state) :
    ∃ path : NetworkPath model.edgeView graph
        (index.decode source).val (index.decode name).val,
      RealizesDistance model graph index source name state path ∧
        IsShortestPath model.edgeView graph path := by
  rcases predecessorReaches_path model graph index source state hcorrect.1 with
    ⟨path, hrealizes⟩
  exact ⟨path, hrealizes, hcorrect.2 path hrealizes⟩

/--
Claim (4.14): every name settled by the actual Dijkstra execution has a shortest source path
reconstructed from the final predecessor array, using exact edge occurrences and stored weight.
-/
theorem claim_4_14
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length)
    (hallReachable : ∀ name,
      Reachable model.base.interface graph (index.decode source).val
        (index.decode name).val) :
    let final := (Interpreter.eval model graph index source).2
    ∀ name, name ∈ final.settled →
      PredecessorReconstructedShortest model graph index source name final := by
  intro final name hsettled
  have hinvariant := dijkstra_fullInvariant model graph index source hallReachable
  rcases hinvariant.shortest.settledShortest name hsettled with
    ⟨selectedPath, hselectedRealizes, hselectedShortest⟩
  have hfinite : storedDistance final name ≠ ⊤ := by
    unfold RealizesDistance at hselectedRealizes
    rw [← hselectedRealizes]
    exact WithTop.coe_ne_top
  refine ⟨hinvariant.predecessorWitness name hfinite, ?_⟩
  intro path hrealizes alternative
  have heq : networkPathWeight (Weight := Weight) model graph path =
      networkPathWeight (Weight := Weight) model graph selectedPath := by
    unfold RealizesDistance at hrealizes hselectedRealizes
    exact WithTop.coe_injective (hrealizes.trans hselectedRealizes.symm)
  change networkPathWeight (Weight := Weight) model graph path ≤
    networkPathWeight (Weight := Weight) model graph alternative
  rw [heq]
  exact hselectedShortest alternative

/-- Unit-profile instrumentation has exactly the same Claim (4.14) result state. -/
theorem claim_4_14_runDecomposition
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length)
    (hallReachable : ∀ name,
      Reachable model.base.interface graph (index.decode source).val
        (index.decode name).val) :
    let final := (Interpreter.runDecomposition model graph index source).ret.2
    ∀ name, name ∈ final.settled →
      PredecessorReconstructedShortest model graph index source name final := by
  simpa using claim_4_14 model graph index source hallReachable

/-- Heap-profile instrumentation has exactly the same Claim (4.14) result state. -/
theorem claim_4_14_runHeap
    (model : WeightedResourceModel G V Edge Weight) (graph : G)
    (index : VertexIndex model.base.interface model.base.vertexEnumeration graph)
    (source : Fin (model.base.vertexEnumeration.vertices graph).length)
    (hallReachable : ∀ name,
      Reachable model.base.interface graph (index.decode source).val
        (index.decode name).val) :
    let final := (Interpreter.runHeap model graph index source).ret.2
    ∀ name, name ∈ final.settled →
      PredecessorReconstructedShortest model graph index source name final := by
  simpa using claim_4_14 model graph index source hallReachable

end Correctness

end KleinbergDijkstra
