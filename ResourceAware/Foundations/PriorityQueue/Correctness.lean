/-
Copyright (c) 2026 Jiyuan (Chai Yuen) Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan (Chai Yuen) Ji
-/
import ResourceAware.Foundations.PriorityQueue.Complexity

/-!
# Correctness of the bounded named heap

The public results in this file focus on representation-independent behavior: empty-heap
well-formedness, the root-minimum property, active-name uniqueness, preservation of active names
by swaps and heapification, and correctness of the direct textbook mutations.
-/

universe u

namespace KleinbergPriorityQueue

namespace Heap

variable {capacity : Nat} {Key : Type u} [LinearOrder Key]

set_option linter.unusedSectionVars false

/-! ## Basic representation consequences -/

@[simp] theorem startHeap_wellFormed (capacity : Nat) (Key : Type u)
    [LinearOrder Key] :
    (startHeap capacity Key).WellFormed := by
  constructor
  · simp [startHeap]
  constructor
  · intro i
    exact Fin.elim0 i
  · constructor
    · intro i
      exact Fin.elim0 i
    · intro name
      simp [startHeap]

private theorem positionInverse_iff (heap : Heap capacity Key) :
    heap.PositionInverse ↔ ∀ name i, heap.Position name = some i ↔
      ∃ hi : i < heap.H.size, heap.H[i].name = name := by
  constructor
  · intro hinverse name i
    constructor
    · intro hposition
      simpa [hposition, Option.map_eq_some_iff, Array.getElem?_eq_some_iff]
        using hinverse.2 name
    · rintro ⟨hi, hname⟩
      simpa [hname] using hinverse.1 ⟨i, hi⟩
  · intro h
    constructor
    · intro i
      exact (h heap.H[i].name i).2 ⟨i.isLt, rfl⟩
    · intro name
      cases hposition : heap.Position name with
      | none => simp
      | some i =>
          obtain ⟨hi, hname⟩ := (h name i).1 hposition
          simp [Array.getElem?_eq_getElem hi, hname]

/-- Under a Position inverse, active Position cells are exactly the named array entries. -/
theorem position_eq_some_iff (heap : Heap capacity Key) (hinverse : heap.PositionInverse)
    {name : Fin capacity} {i : Nat} :
    heap.Position name = some i ↔
      ∃ hi : i < heap.H.size, heap.H[i].name = name :=
  (positionInverse_iff heap).1 hinverse _ _

/-- The Position inverse implies that active heap-array names are unique. -/
theorem active_name_unique (heap : Heap capacity Key) (hinverse : heap.PositionInverse)
    {i j : Nat} (hi : i < heap.H.size) (hj : j < heap.H.size)
    (hname : heap.H[i].name = heap.H[j].name) :
    i = j := by
  have hleft := (position_eq_some_iff heap hinverse).2 ⟨hi, rfl⟩
  have hright := (position_eq_some_iff heap hinverse).2 ⟨hj, hname.symm⟩
  exact Option.some.inj (hleft.symm.trans hright)

/-- Every active Position cell contains an in-bounds heap-array index. -/
theorem position_lt_size (heap : Heap capacity Key) (hinverse : heap.PositionInverse)
    {name : Fin capacity} {i : Nat} (hposition : heap.Position name = some i) :
    i < heap.H.size :=
  ((position_eq_some_iff heap hinverse).1 hposition).choose

/-- A Position lookup retrieves an entry carrying exactly the queried name. -/
theorem position_name (heap : Heap capacity Key) (hinverse : heap.PositionInverse)
    {name : Fin capacity} {i : Nat} (hposition : heap.Position name = some i) :
    (heap.H[i]?).map Entry.name = some name := by
  obtain ⟨hi, hname⟩ := (position_eq_some_iff heap hinverse).1 hposition
  simp [Array.getElem?_eq_getElem hi, hname]

/-- A valid Position inverse makes the local checked lookup succeed at the recorded index. -/
theorem validPosition?_eq_some (heap : Heap capacity Key) (hinverse : heap.PositionInverse)
    {name : Fin capacity} {i : Nat} (hposition : heap.Position name = some i) :
    heap.validPosition? name = some i := by
  obtain ⟨hi, hname⟩ := (position_eq_some_iff heap hinverse).1 hposition
  simp [validPosition?, hposition, Array.getElem?_eq_getElem hi, hname]

/-- On a valid representation, `contains` is the domain predicate of logical `contents`. -/
theorem contains_eq_true_iff_exists_contents (heap : Heap capacity Key)
    (hinverse : heap.PositionInverse) (name : Fin capacity) :
    heap.contains name = true ↔ ∃ key, heap.contents name = some key := by
  cases hposition : heap.Position name with
  | none => simp [contains, contents, hposition]
  | some i =>
      have hi := position_lt_size heap hinverse hposition
      simp [contains, contents, hposition, Array.getElem?_eq_getElem hi]

@[simp] theorem contains_eq_false_iff_contents_eq_none (heap : Heap capacity Key)
    (hinverse : heap.PositionInverse) (name : Fin capacity) :
    heap.contains name = false ↔ heap.contents name = none := by
  cases hposition : heap.Position name with
  | none => simp [contains, contents, hposition]
  | some i =>
      have hi := position_lt_size heap hinverse hposition
      simp [contains, contents, hposition, Array.getElem?_eq_getElem hi]

/-! ## Swaps and local repair preserve representation-independent membership -/

@[simp] theorem swapEntries_size (heap : Heap capacity Key) (i j : Nat) :
    (heap.swapEntries i j).H.size = heap.H.size := by
  simp only [swapEntries]
  split
  · split
    · exact Array.size_swap
    · rfl
  · rfl

@[simp] theorem swapEntries_contains (heap : Heap capacity Key) (i j : Nat)
    (name : Fin capacity) :
    (heap.swapEntries i j).contains name = heap.contains name := by
  simp only [swapEntries]
  split
  · split
    · simp only [contains]
      cases hposition : heap.Position name with
      | none => simp [swapPosition, hposition]
      | some position =>
          by_cases hfirst : position = i
          · simp [swapPosition, hposition, hfirst]
          · by_cases hsecond : position = j
            · subst position
              simp [swapPosition, hposition, hfirst]
            · simp [swapPosition, hposition, hfirst, hsecond]
    · rfl
  · rfl

private theorem swapPosition_eq_some_iff
    (position : Fin capacity → Option Nat) (name : Fin capacity) (i j k : Nat) :
    swapPosition position i j name = some k ↔
      (position name = some i ∧ j = k) ∨
      (i ≠ j ∧ position name = some j ∧ i = k) ∨
      (position name = some k ∧ k ≠ i ∧ k ≠ j) := by
  cases hposition : position name with
  | none => simp [swapPosition, hposition]
  | some n =>
      by_cases hni : n = i
      · subst n
        simp_all [swapPosition, eq_comm]
      · by_cases hnj : n = j
        · subst n
          simp_all [swapPosition, eq_comm]
        · simp_all [swapPosition, eq_comm]

/-- A valid array swap, together with its two Position writes, preserves mutual inversion. -/
theorem swapEntries_positionInverse (heap : Heap capacity Key)
    (hinverse : heap.PositionInverse) (i j : Nat) :
    (heap.swapEntries i j).PositionInverse := by
  by_cases hi : i < heap.H.size
  · by_cases hj : j < heap.H.size
    · rw [swapEntries, dif_pos hi, dif_pos hj]
      rw [positionInverse_iff]
      intro name k
      rw [swapPosition_eq_some_iff]
      simp_rw [position_eq_some_iff heap hinverse]
      by_cases hki : k = i
      · subst k
        by_cases hij : i = j
        · subst j
          simp_all [eq_comm]
        · simp_all [eq_comm]
      · by_cases hkj : k = j
        · subst k
          simp_all [eq_comm]
        · simp_all [eq_comm]
    · simpa [swapEntries, hi, hj] using hinverse
  · simpa [swapEntries, hi] using hinverse

@[simp] theorem swapEntries_contents (heap : Heap capacity Key) (i j : Nat)
    (name : Fin capacity) :
    (heap.swapEntries i j).contents name = heap.contents name := by
  by_cases hi : i < heap.H.size
  · by_cases hj : j < heap.H.size
    · rw [swapEntries, dif_pos hi, dif_pos hj]
      cases hposition : heap.Position name with
      | none => simp [contents, swapPosition, hposition]
      | some k =>
          by_cases hki : k = i
          · subst k
            simp [contents, swapPosition, hposition, Array.getElem?_swap,
              Array.getElem?_eq_getElem hi]
          · by_cases hkj : k = j
            · subst k
              simp [contents, swapPosition, hposition, hki, Array.getElem?_swap,
                Array.getElem?_eq_getElem hj]
            · simp [contents, swapPosition, hposition, hki, hkj, Ne.symm hki,
                Ne.symm hkj, Array.getElem?_swap]
    · simp [swapEntries, hi, hj]
  · simp [swapEntries, hi]

private structure RepairPreserves (after before : Heap capacity Key) : Prop where
  size_eq : after.H.size = before.H.size
  contains_eq : ∀ name, after.contains name = before.contains name
  contents_eq : ∀ name, after.contents name = before.contents name
  positionInverse : before.PositionInverse → after.PositionInverse

private theorem RepairPreserves.refl (heap : Heap capacity Key) :
    RepairPreserves heap heap :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, id⟩

private theorem RepairPreserves.trans {first middle last : Heap capacity Key}
    (hfirst : RepairPreserves first middle) (hlast : RepairPreserves middle last) :
    RepairPreserves first last :=
  ⟨hfirst.size_eq.trans hlast.size_eq,
    fun name => (hfirst.contains_eq name).trans (hlast.contains_eq name),
    fun name => (hfirst.contents_eq name).trans (hlast.contents_eq name),
    fun hinverse => hfirst.positionInverse (hlast.positionInverse hinverse)⟩

private theorem swapEntries_preserves (heap : Heap capacity Key) (i j : Nat) :
    RepairPreserves (heap.swapEntries i j) heap :=
  ⟨swapEntries_size heap i j, swapEntries_contains heap i j,
    swapEntries_contents heap i j, fun hinverse =>
      swapEntries_positionInverse heap hinverse i j⟩

private theorem heapifyUp_preserves (heap : Heap capacity Key) (i : Nat) :
    RepairPreserves (heap.heapifyUp i) heap := by
  induction i using Nat.strong_induction_on generalizing heap with
  | h i ih =>
      rw [heapifyUp]
      split
      next hi =>
        split
        next => exact .refl heap
        next hroot =>
          dsimp only
          split
          next =>
            exact (ih (parent i) (parent_lt_self hroot)
                (heap.swapEntries i (parent i))).trans
              (swapEntries_preserves heap i (parent i))
          next => exact .refl heap
      next => exact .refl heap

@[simp] theorem heapifyUp_size (heap : Heap capacity Key) (i : Nat) :
    (heap.heapifyUp i).H.size = heap.H.size :=
  (heapifyUp_preserves heap i).size_eq

@[simp] theorem heapifyUp_contains (heap : Heap capacity Key) (i : Nat)
    (name : Fin capacity) :
    (heap.heapifyUp i).contains name = heap.contains name :=
  (heapifyUp_preserves heap i).contains_eq name

theorem heapifyUp_positionInverse (heap : Heap capacity Key) (i : Nat)
    (hinverse : heap.PositionInverse) :
    (heap.heapifyUp i).PositionInverse :=
  (heapifyUp_preserves heap i).positionInverse hinverse

@[simp] theorem heapifyUp_contents (heap : Heap capacity Key) (i : Nat)
    (name : Fin capacity) :
    (heap.heapifyUp i).contents name = heap.contents name :=
  (heapifyUp_preserves heap i).contents_eq name

private theorem heapifyDownLoop_preserves (fuel : Nat) (heap : Heap capacity Key) (i : Nat) :
    RepairPreserves (heapifyDownLoop fuel heap i) heap := by
  induction fuel generalizing heap i with
  | zero => exact .refl heap
  | succ fuel ih =>
      rw [heapifyDownLoop]
      cases hchild : heap.smallerChild? i with
      | none => exact .refl heap
      | some child =>
          simp only
          cases hhere : heap.H[i]? with
          | none => exact .refl heap
          | some here =>
              cases hbelow : heap.H[child]? with
              | none => exact .refl heap
              | some below =>
                  by_cases hless : below.key < here.key
                  · simp only [hless, if_true]
                    exact (ih (heap.swapEntries i child) child).trans
                      (swapEntries_preserves heap i child)
                  · simp only [hless, if_false]
                    exact .refl heap

@[simp] theorem heapifyDownLoop_size (fuel : Nat) (heap : Heap capacity Key) (i : Nat) :
    (heapifyDownLoop fuel heap i).H.size = heap.H.size :=
  (heapifyDownLoop_preserves fuel heap i).size_eq

@[simp] theorem heapifyDownLoop_contains (fuel : Nat) (heap : Heap capacity Key)
    (i : Nat) (name : Fin capacity) :
    (heapifyDownLoop fuel heap i).contains name = heap.contains name :=
  (heapifyDownLoop_preserves fuel heap i).contains_eq name

theorem heapifyDownLoop_positionInverse (fuel : Nat) (heap : Heap capacity Key)
    (i : Nat) (hinverse : heap.PositionInverse) :
    (heapifyDownLoop fuel heap i).PositionInverse :=
  (heapifyDownLoop_preserves fuel heap i).positionInverse hinverse

@[simp] theorem heapifyDownLoop_contents (fuel : Nat) (heap : Heap capacity Key)
    (i : Nat) (name : Fin capacity) :
    (heapifyDownLoop fuel heap i).contents name = heap.contents name :=
  (heapifyDownLoop_preserves fuel heap i).contents_eq name

@[simp] theorem heapifyDown_size (heap : Heap capacity Key) (i : Nat) :
    (heap.heapifyDown i).H.size = heap.H.size :=
  heapifyDownLoop_size heap.H.size heap i

@[simp] theorem heapifyDown_contains (heap : Heap capacity Key) (i : Nat)
    (name : Fin capacity) :
    (heap.heapifyDown i).contains name = heap.contains name :=
  heapifyDownLoop_contains heap.H.size heap i name

theorem heapifyDown_positionInverse (heap : Heap capacity Key) (i : Nat)
    (hinverse : heap.PositionInverse) :
    (heap.heapifyDown i).PositionInverse :=
  heapifyDownLoop_positionInverse heap.H.size heap i hinverse

@[simp] theorem heapifyDown_contents (heap : Heap capacity Key) (i : Nat)
    (name : Fin capacity) :
    (heap.heapifyDown i).contents name = heap.contents name :=
  heapifyDownLoop_contents heap.H.size heap i name

/-! ## Textbook heap-order restoration -/

/-- The key observed at `k`, with one distinguished index read as `replacement`. -/
def keyAtWith (heap : Heap capacity Key) (focus : Nat) (replacement : Key)
    (k : Nat) (hk : k < heap.H.size) : Key :=
  if k = focus then replacement else heap.H[k].key

/-- Heap order after logically replacing one key, without changing the executable heap. -/
def HeapOrderedWithKey (heap : Heap capacity Key) (focus : Nat) (replacement : Key) : Prop :=
  ∀ k (hk : k < heap.H.size),
    k = 0 ∨
      keyAtWith heap focus replacement (parent k) (parent_lt_size hk) ≤
        keyAtWith heap focus replacement k hk

@[simp] theorem keyAtWith_self (heap : Heap capacity Key) {i : Nat}
    (hi : i < heap.H.size) (k : Nat) (hk : k < heap.H.size) :
    keyAtWith heap i heap.H[i].key k hk = heap.H[k].key := by
  by_cases hki : k = i <;> simp [keyAtWith, hki]

theorem heapOrderedWithKey_self (heap : Heap capacity Key) {i : Nat}
    (hi : i < heap.H.size) :
    HeapOrderedWithKey heap i heap.H[i].key ↔ heap.HeapOrdered := by
  constructor
  · intro h k
    simpa [HeapOrderedWithKey, keyAtWith_self heap hi] using h k.val k.isLt
  · intro h k hk
    simpa [HeapOrderedWithKey, keyAtWith_self heap hi] using h ⟨k, hk⟩

/-- Textbook precondition for moving one key toward the root. -/
def AlmostHeapUp (heap : Heap capacity Key) (i : Nat) : Prop :=
  ∃ hi : i < heap.H.size, ∃ replacement : Key,
    heap.H[i].key ≤ replacement ∧
      HeapOrderedWithKey heap i replacement

/-- Textbook precondition for moving one key toward the leaves. -/
def AlmostHeapDown (heap : Heap capacity Key) (i : Nat) : Prop :=
  ∃ hi : i < heap.H.size, ∃ replacement : Key,
    replacement ≤ heap.H[i].key ∧
      HeapOrderedWithKey heap i replacement

private theorem heapOrderedWithKey_outgoing (heap : Heap capacity Key) {i k : Nat}
    {replacement : Key} (hordered : HeapOrderedWithKey heap i replacement)
    (hk : k < heap.H.size) (hkroot : k ≠ 0) (hparent : parent k = i) :
    replacement ≤ heap.H[k].key := by
  have hki : k ≠ i := fun h => (parent_lt_self hkroot).ne (hparent.trans h.symm)
  simpa [keyAtWith, hki, hparent] using (hordered k hk).resolve_left hkroot

theorem heapOrderedWithKey_of_edges (heap : Heap capacity Key) {i : Nat}
    (hi : i < heap.H.size) {oldKey newKey : Key}
    (hordered : HeapOrderedWithKey heap i oldKey)
    (hincoming : i = 0 ∨
      (heap.H[parent i]'(parent_lt_size hi)).key ≤ newKey)
    (houtgoing : ∀ k (hk : k < heap.H.size), k ≠ 0 → parent k = i →
      newKey ≤ heap.H[k].key) :
    HeapOrderedWithKey heap i newKey := by
  intro k hk
  by_cases hkroot : k = 0
  · exact Or.inl hkroot
  · right
    by_cases hki : k = i
    · subst i
      simpa [keyAtWith, (parent_lt_self hkroot).ne] using
        hincoming.resolve_left hkroot
    · by_cases hparent : parent k = i
      · simpa [keyAtWith, hki, hparent] using
          houtgoing k hk hkroot hparent
      · simpa [keyAtWith, hki, hparent] using
          (hordered k hk).resolve_left hkroot

theorem heapOrdered_of_heapOrderedWithKey_edges (heap : Heap capacity Key) {i : Nat}
    (hi : i < heap.H.size) {replacement : Key}
    (hordered : HeapOrderedWithKey heap i replacement)
    (hincoming : i = 0 ∨
      (heap.H[parent i]'(parent_lt_size hi)).key ≤ heap.H[i].key)
    (houtgoing : ∀ k (hk : k < heap.H.size), k ≠ 0 → parent k = i →
      heap.H[i].key ≤ heap.H[k].key) :
    heap.HeapOrdered :=
  (heapOrderedWithKey_self heap hi).1
    (heapOrderedWithKey_of_edges heap hi hordered hincoming houtgoing)

theorem heapOrdered_of_almostUp_noViolation (heap : Heap capacity Key) {i : Nat}
    (hi : i < heap.H.size) {replacement : Key}
    (hcurrent : heap.H[i].key ≤ replacement)
    (hordered : HeapOrderedWithKey heap i replacement)
    (hincoming : i = 0 ∨
      (heap.H[parent i]'(parent_lt_size hi)).key ≤ heap.H[i].key) :
    heap.HeapOrdered := by
  exact heapOrdered_of_heapOrderedWithKey_edges heap hi hordered hincoming
    fun k hk hkroot hparent => hcurrent.trans
      (heapOrderedWithKey_outgoing heap hordered hk hkroot hparent)

theorem keyAtWith_swap_move (heap : Heap capacity Key) {i j k : Nat}
    (hi : i < heap.H.size) (hj : j < heap.H.size) (hij : i ≠ j)
    (hk : k < heap.H.size) :
    keyAtWith (heap.swapEntries i j) j heap.H[j].key k
        (by simpa [swapEntries, hi, hj] using hk) =
      keyAtWith heap i heap.H[j].key k hk := by
  by_cases hki : k = i <;> by_cases hkj : k = j <;>
    simp_all [keyAtWith, swapEntries]

theorem heapOrderedWithKey_swap_move (heap : Heap capacity Key) {i j : Nat}
    (hi : i < heap.H.size) (hj : j < heap.H.size) (hij : i ≠ j)
    (hordered : HeapOrderedWithKey heap i heap.H[j].key) :
    HeapOrderedWithKey (heap.swapEntries i j) j heap.H[j].key := by
  intro k hk
  have hk' : k < heap.H.size := by
    simpa [swapEntries, hi, hj] using hk
  simpa only [keyAtWith_swap_move heap hi hj hij (parent_lt_size hk'),
    keyAtWith_swap_move heap hi hj hij hk'] using hordered k hk'

theorem almostHeapUp_swap (heap : Heap capacity Key) {i : Nat}
    (hi : i < heap.H.size) (hroot : i ≠ 0)
    (hless : heap.H[i].key <
      (heap.H[parent i]'(parent_lt_size hi)).key)
    (halmost : AlmostHeapUp heap i) :
    AlmostHeapUp (heap.swapEntries i (parent i)) (parent i) := by
  rcases halmost with ⟨_, replacement, hcurrent, hordered⟩
  let p := parent i
  have hp : p < heap.H.size := parent_lt_size hi
  have hip : i ≠ p := (parent_lt_self hroot).ne'
  have hbetaReplacement : heap.H[p].key ≤ replacement := by
    simpa [keyAtWith, p, (parent_lt_self hroot).ne] using
      (hordered i hi).resolve_left hroot
  have horderedBeta : HeapOrderedWithKey heap i heap.H[p].key := by
    apply heapOrderedWithKey_of_edges heap hi hordered (Or.inr (by simp [p]))
    intro k hk hkroot hparent
    exact hbetaReplacement.trans
      (heapOrderedWithKey_outgoing heap hordered hk hkroot hparent)
  refine ⟨by simpa using hp, heap.H[p].key, ?_, ?_⟩
  · simpa [swapEntries, hi, hp, p, Ne.symm hip, Array.getElem_swap] using hless.le
  · exact heapOrderedWithKey_swap_move heap hi hp hip horderedBeta

/-- Heapify-up restores heap order from the textbook's localized too-small condition. -/
theorem heapifyUp_heapOrdered (heap : Heap capacity Key) (i : Nat)
    (halmost : AlmostHeapUp heap i) :
    (heap.heapifyUp i).HeapOrdered := by
  induction i using Nat.strong_induction_on generalizing heap with
  | h i ih =>
      rcases halmost with ⟨hi, replacement, hcurrent, hordered⟩
      rw [heapifyUp, dif_pos hi]
      split
      · next hroot =>
        exact heapOrdered_of_almostUp_noViolation heap hi hcurrent hordered (Or.inl hroot)
      · next hroot =>
        dsimp only
        split
        · next hless =>
          apply ih (parent i) (parent_lt_self hroot)
          exact almostHeapUp_swap heap hi hroot hless
            ⟨hi, replacement, hcurrent, hordered⟩
        · next hless =>
          exact heapOrdered_of_almostUp_noViolation heap hi hcurrent hordered
            (Or.inr (le_of_not_gt hless))

theorem eq_leftChild_or_rightChild_of_parent_eq {i k : Nat}
    (hk : k ≠ 0) (hparent : parent k = i) :
    k = leftChild i ∨ k = rightChild i := by
  unfold parent leftChild rightChild at *
  omega

theorem smallerChild?_eq_some_iff (heap : Heap capacity Key) {i child : Nat} :
    heap.smallerChild? i = some child ↔
      (∃ hleft : leftChild i < heap.H.size,
        child = leftChild i ∧
          (¬ rightChild i < heap.H.size ∨
            ∃ hright : rightChild i < heap.H.size,
              heap.H[leftChild i].key ≤ heap.H[rightChild i].key)) ∨
      (∃ hleft : leftChild i < heap.H.size,
        ∃ hright : rightChild i < heap.H.size,
          child = rightChild i ∧
            heap.H[rightChild i].key < heap.H[leftChild i].key) := by
  simp only [smallerChild?]
  split
  · split
    · split <;> simp_all [not_le, eq_comm]
    · simp_all [eq_comm]
  · simp_all

theorem smallerChild?_some_lt (heap : Heap capacity Key) {i child : Nat}
    (hchild : heap.smallerChild? i = some child) :
    child < heap.H.size := by
  rcases (smallerChild?_eq_some_iff heap).1 hchild with
    ⟨hleft, rfl, _⟩ | ⟨_, hright, rfl, _⟩ <;> assumption

theorem smallerChild?_parent (heap : Heap capacity Key) {i child : Nat}
    (hchild : heap.smallerChild? i = some child) :
    parent child = i := by
  rcases (smallerChild?_eq_some_iff heap).1 hchild with
    ⟨_, rfl, _⟩ | ⟨_, _, rfl, _⟩ <;>
    simp only [parent, leftChild, rightChild] <;> omega

theorem smallerChild?_ne_zero (heap : Heap capacity Key) {i child : Nat}
    (hchild : heap.smallerChild? i = some child) :
    child ≠ 0 := by
  rcases (smallerChild?_eq_some_iff heap).1 hchild with
    ⟨_, rfl, _⟩ | ⟨_, _, rfl, _⟩ <;>
    simp only [leftChild, rightChild] <;> omega

theorem smallerChild?_minimum (heap : Heap capacity Key) {i child k : Nat}
    (hchild : heap.smallerChild? i = some child)
    (hk : k < heap.H.size) (hkroot : k ≠ 0) (hparent : parent k = i) :
    (heap.H[child]'(smallerChild?_some_lt heap hchild)).key ≤ heap.H[k].key := by
  rcases (smallerChild?_eq_some_iff heap).1 hchild with
      ⟨_, rfl, hright⟩ | ⟨_, _, rfl, hsmaller⟩ <;>
    rcases eq_leftChild_or_rightChild_of_parent_eq hkroot hparent with
      rfl | rfl
  · exact le_rfl
  · rcases hright with hright | ⟨_, hle⟩
    · exact (hright hk).elim
    · exact hle
  · exact hsmaller.le
  · exact le_rfl

theorem heapOrdered_of_almostDown_noViolation (heap : Heap capacity Key) {i : Nat}
    (hi : i < heap.H.size) {replacement : Key}
    (hreplacement : replacement ≤ heap.H[i].key)
    (hordered : HeapOrderedWithKey heap i replacement)
    (hchildren : ∀ k (hk : k < heap.H.size), k ≠ 0 → parent k = i →
      heap.H[i].key ≤ heap.H[k].key) :
    heap.HeapOrdered := by
  apply heapOrdered_of_heapOrderedWithKey_edges heap hi hordered ?_ hchildren
  exact (eq_or_ne i 0).elim Or.inl fun hroot =>
    Or.inr ((show (heap.H[parent i]'(parent_lt_size hi)).key ≤ replacement by
      simpa [keyAtWith, (parent_lt_self hroot).ne] using
        (hordered i hi).resolve_left hroot).trans hreplacement)

theorem almostHeapDown_swap (heap : Heap capacity Key) {i child : Nat}
    (hi : i < heap.H.size) (hchild : heap.smallerChild? i = some child)
    (hless : (heap.H[child]'(smallerChild?_some_lt heap hchild)).key < heap.H[i].key)
    (halmost : AlmostHeapDown heap i) :
    AlmostHeapDown (heap.swapEntries i child) child := by
  rcases halmost with ⟨_, replacement, hreplacement, hordered⟩
  have hc : child < heap.H.size := smallerChild?_some_lt heap hchild
  have hparent : parent child = i := smallerChild?_parent heap hchild
  have hchildRoot : child ≠ 0 := smallerChild?_ne_zero heap hchild
  have hic : i ≠ child := hparent ▸ (parent_lt_self hchildRoot).ne
  have hreplacementChild :=
    heapOrderedWithKey_outgoing heap hordered hc hchildRoot hparent
  have horderedChild : HeapOrderedWithKey heap i heap.H[child].key := by
    apply heapOrderedWithKey_of_edges heap hi hordered
    · exact (eq_or_ne i 0).elim Or.inl fun hroot =>
        Or.inr ((show (heap.H[parent i]'(parent_lt_size hi)).key ≤ replacement by
          simpa [keyAtWith, (parent_lt_self hroot).ne] using
            (hordered i hi).resolve_left hroot).trans hreplacementChild)
    · intro k hk hkroot hkparent
      exact smallerChild?_minimum heap hchild hk hkroot hkparent
  refine ⟨by simpa using hc, heap.H[child].key, ?_, ?_⟩
  · simpa [swapEntries, hi, hc, hic, Array.getElem_swap] using hless.le
  · exact heapOrderedWithKey_swap_move heap hi hc hic horderedChild

theorem heapifyDownLoop_heapOrdered (fuel : Nat) (heap : Heap capacity Key)
    (i : Nat) (halmost : AlmostHeapDown heap i)
    (hbudget : heap.H.size - i ≤ fuel) :
    (heapifyDownLoop fuel heap i).HeapOrdered := by
  induction fuel generalizing heap i with
  | zero =>
      rcases halmost with ⟨hi, replacement, hreplacement, hordered⟩
      simp only [heapifyDownLoop]
      omega
  | succ fuel ih =>
      rcases halmost with ⟨hi, replacement, hreplacement, hordered⟩
      rw [heapifyDownLoop]
      cases hchild : heap.smallerChild? i with
      | none =>
          have hleft : ¬ leftChild i < heap.H.size := by
            intro hleft
            simp only [smallerChild?, dif_pos hleft] at hchild
            split at hchild
            · split at hchild <;> simp_all
            · simp_all
          apply heapOrdered_of_almostDown_noViolation heap hi hreplacement hordered
          intro k hk hkroot hkparent
          rcases eq_leftChild_or_rightChild_of_parent_eq hkroot hkparent with rfl | rfl
          · exact (hleft hk).elim
          · exact (hleft (by simp only [leftChild, rightChild] at *; omega)).elim
      | some child =>
          have hc : child < heap.H.size := smallerChild?_some_lt heap hchild
          simp only [Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem hc]
          split
          · next hless =>
            apply ih (heap.swapEntries i child) child
            · exact almostHeapDown_swap heap hi hchild hless
                ⟨hi, replacement, hreplacement, hordered⟩
            · rw [swapEntries_size]
              have hgt := parent_lt_self (smallerChild?_ne_zero heap hchild)
              rw [smallerChild?_parent heap hchild] at hgt
              omega
          · next hless =>
            exact heapOrdered_of_almostDown_noViolation heap hi hreplacement hordered
              fun k hk hkroot hkparent => (le_of_not_gt hless).trans
                (smallerChild?_minimum heap hchild hk hkroot hkparent)

/-- Heapify-down restores heap order from the textbook's localized too-big condition. -/
theorem heapifyDown_heapOrdered (heap : Heap capacity Key) (i : Nat)
    (halmost : AlmostHeapDown heap i) :
    (heap.heapifyDown i).HeapOrdered := by
  exact heapifyDownLoop_heapOrdered heap.H.size heap i halmost (by omega)

/-! ## One local key replacement -/

/--
Proof-only view of the local write performed by `changeKey`.

The executable operation still uses the entry obtained from its checked array lookup.  Packaging
the valid index as a `Fin` here makes the subsequent local-repair proofs independent of that
control-flow detail.
-/
private def withKey (heap : Heap capacity Key) (i : Fin heap.H.size) (newKey : Key) :
    Heap capacity Key :=
  { heap with
    H := heap.H.setIfInBounds i.val { heap.H[i] with key := newKey } }

@[simp] private theorem withKey_size (heap : Heap capacity Key) (i : Fin heap.H.size)
    (newKey : Key) :
    (withKey heap i newKey).H.size = heap.H.size := by
  simp [withKey]

private theorem withKey_name (heap : Heap capacity Key) (i : Fin heap.H.size)
    (newKey : Key) (k : Nat) (hk : k < heap.H.size) :
    ((withKey heap i newKey).H[k]'(by simpa [withKey] using hk)).name =
      heap.H[k].name := by
  change ((heap.H.setIfInBounds i.val { heap.H[i] with key := newKey })[k]'
      (by simpa using hk)).name = heap.H[k].name
  rw [Array.getElem_setIfInBounds hk]
  split <;> simp_all

/-- Replacing a key leaves entry names and their Position table mutually inverse. -/
private theorem withKey_positionInverse (heap : Heap capacity Key)
    (hinverse : heap.PositionInverse) (i : Fin heap.H.size)
    (newKey : Key) :
    (withKey heap i newKey).PositionInverse := by
  rw [positionInverse_iff]
  intro name k
  change heap.Position name = some k ↔
    ∃ hk : k < (withKey heap i newKey).H.size,
      (withKey heap i newKey).H[k].name = name
  rw [position_eq_some_iff heap hinverse]
  simp only [withKey_size]
  constructor <;> rintro ⟨hk, hname⟩
  · exact ⟨hk, (withKey_name heap i newKey k hk).trans hname⟩
  · exact ⟨hk, (withKey_name heap i newKey k hk).symm.trans hname⟩

private theorem keyAtWith_withKey (heap : Heap capacity Key) (i : Fin heap.H.size)
    (newKey replacement : Key)
    (k : Nat) (hk : k < (withKey heap i newKey).H.size) :
    keyAtWith (withKey heap i newKey) i.val replacement k hk =
      keyAtWith heap i.val replacement k (by simpa [withKey] using hk) := by
  by_cases hki : k = i.val
  · simp [keyAtWith, hki]
  · simp only [keyAtWith, hki, if_false]
    have hkOld : k < heap.H.size := by simpa [withKey] using hk
    change ((heap.H.setIfInBounds i.val { heap.H[i] with key := newKey })[k]'
      (by simpa using hkOld)).key = heap.H[k].key
    rw [Array.getElem_setIfInBounds hkOld]
    simp [Ne.symm hki]

private theorem heapOrderedWithKey_withKey (heap : Heap capacity Key)
    (i : Fin heap.H.size) (newKey replacement : Key) :
    HeapOrderedWithKey (withKey heap i newKey) i.val replacement ↔
      HeapOrderedWithKey heap i.val replacement := by
  constructor <;> intro h k hk
  · have hk' : k < (withKey heap i newKey).H.size := by
      simpa [withKey] using hk
    simpa only [keyAtWith_withKey heap i] using h k hk'
  · have hk' : k < heap.H.size := by
      simpa [withKey] using hk
    simpa only [keyAtWith_withKey heap i] using h k hk'

private theorem withKey_almostHeapUp (heap : Heap capacity Key) (i : Fin heap.H.size)
    (horder : heap.HeapOrdered) (newKey : Key)
    (hdecrease : newKey ≤ heap.H[i].key) :
    AlmostHeapUp (withKey heap i newKey) i.val := by
  have hi' : i.val < (withKey heap i newKey).H.size := by
    simp [withKey]
  refine ⟨hi', heap.H[i].key, ?_, ?_⟩
  · simpa [withKey] using hdecrease
  · rw [heapOrderedWithKey_withKey heap i]
    exact (heapOrderedWithKey_self heap i.isLt).2 horder

private theorem withKey_almostHeapDown (heap : Heap capacity Key) (i : Fin heap.H.size)
    (horder : heap.HeapOrdered) (newKey : Key)
    (hincrease : heap.H[i].key ≤ newKey) :
    AlmostHeapDown (withKey heap i newKey) i.val := by
  have hi' : i.val < (withKey heap i newKey).H.size := by
    simp [withKey]
  refine ⟨hi', heap.H[i].key, ?_, ?_⟩
  · simpa [withKey] using hincrease
  · rw [heapOrderedWithKey_withKey heap i]
    exact (heapOrderedWithKey_self heap i.isLt).2 horder

@[simp] private theorem withKey_same (heap : Heap capacity Key) (i : Fin heap.H.size) :
    withKey heap i heap.H[i].key = heap := by
  cases heap with
  | mk H Position =>
      have hentry :
          ({ H[i] with key := H[i].key } : Entry capacity Key) = H[i] := by
        cases H[i]
        rfl
      change
        ({ H := H.setIfInBounds i.val { H[i] with key := H[i].key }
           Position := Position } : Heap capacity Key) =
        ({ H := H, Position := Position } : Heap capacity Key)
      congr 1
      rw [Array.setIfInBounds_def, dif_pos i.isLt, hentry]
      exact Array.set_getElem_self i.isLt

private theorem withKey_heapifyUp_wellFormed (heap : Heap capacity Key)
    (hwf : heap.WellFormed) (i : Fin heap.H.size) (newKey : Key)
    (hdecrease : newKey ≤ heap.H[i].key) :
    ((withKey heap i newKey).heapifyUp i.val).WellFormed := by
  exact ⟨by simpa using hwf.1,
    heapifyUp_heapOrdered _ _
      (withKey_almostHeapUp heap i hwf.2.1 newKey hdecrease),
    heapifyUp_positionInverse _ _
      (withKey_positionInverse heap hwf.2.2 i newKey)⟩

private theorem withKey_heapifyDown_wellFormed (heap : Heap capacity Key)
    (hwf : heap.WellFormed) (i : Fin heap.H.size) (newKey : Key)
    (hincrease : heap.H[i].key ≤ newKey) :
    ((withKey heap i newKey).heapifyDown i.val).WellFormed := by
  exact ⟨by simpa using hwf.1,
    heapifyDown_heapOrdered _ _
      (withKey_almostHeapDown heap i hwf.2.1 newKey hincrease),
    heapifyDown_positionInverse _ _
      (withKey_positionInverse heap hwf.2.2 i newKey)⟩

/-! ## Minimum correctness -/

/-- In a heap-ordered nonempty array, the root key is no larger than any active key. -/
theorem heapOrdered_root_le (heap : Heap capacity Key) (horder : heap.HeapOrdered)
    (hne : 0 < heap.H.size) {i : Nat} (hi : i < heap.H.size) :
    (heap.H[0]'hne).key ≤ heap.H[i].key := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      by_cases hroot : i = 0
      · subst i
        rfl
      · have hp_lt : parent i < i := parent_lt_self hroot
        have hp_size : parent i < heap.H.size := hp_lt.trans hi
        have hparent := ih (parent i) hp_lt hp_size
        have hedge := (horder ⟨i, hi⟩).resolve_left hroot
        exact hparent.trans hedge

/-- `FindMin` returns an active entry whose key is minimal among all active entries. -/
theorem findMin_minimum (heap : Heap capacity Key) (hwf : heap.WellFormed)
    {minimum : Entry capacity Key} (hfind : heap.findMin = some minimum) :
    minimum ∈ heap.H ∧
      ∀ candidate ∈ heap.H, minimum.key ≤ candidate.key := by
  have hne : 0 < heap.H.size := by
    by_contra hempty
    have hnone := Array.getElem?_eq_none (Nat.le_of_not_gt hempty)
    simp [findMin, hnone] at hfind
  have hroot : heap.H[0]'hne = minimum := by
    simpa [findMin, Array.getElem?_eq_getElem hne] using hfind
  constructor
  · rw [← hroot]
    exact Array.getElem_mem hne
  · intro candidate hcandidate
    rw [Array.mem_iff_getElem] at hcandidate
    rcases hcandidate with ⟨i, hi, rfl⟩
    rw [← hroot]
    exact heapOrdered_root_le heap hwf.2.1 hne hi

/-! ## Root removal and extraction repair -/

/--
Proof-level decomposition of removing the last array entry and marking its name inactive.

`delete` performs these two writes inline. Naming the intermediate state lets the proofs separate
the array truncation argument from the subsequent local heap repair.
-/
private def removeLast (heap : Heap capacity Key) (hne : 0 < heap.H.size) :
    Heap capacity Key :=
  let last := heap.H.size - 1
  let removed := heap.H[last]'(by omega)
  { H := heap.H.pop
    Position := Function.update heap.Position removed.name none }

@[simp] private theorem removeLast_size (heap : Heap capacity Key)
    (hne : 0 < heap.H.size) :
    (removeLast heap hne).H.size = heap.H.size - 1 := by
  simp [removeLast]

/-- Removing the final array cell and its Position entry preserves mutual inversion. -/
private theorem removeLast_positionInverse (heap : Heap capacity Key)
    (hinverse : heap.PositionInverse) (hne : 0 < heap.H.size) :
    (removeLast heap hne).PositionInverse := by
  let last := heap.H.size - 1
  have hlast : last < heap.H.size := by
    dsimp [last]
    omega
  let removed := heap.H[last]'hlast
  rw [positionInverse_iff]
  intro name i
  change Function.update heap.Position removed.name none name = some i ↔
    ∃ hi : i < heap.H.pop.size, heap.H.pop[i].name = name
  by_cases hiPop : i < heap.H.pop.size
  · have hiBefore : i < heap.H.size - 1 := by simpa using hiPop
    have hi : i < heap.H.size := by omega
    have hiLast : i ≠ last := by simp at hiPop; dsimp [last]; omega
    have hiName : heap.H[i].name ≠ removed.name := fun heq =>
      hiLast (active_name_unique heap hinverse hi hlast heq)
    by_cases hname : name = removed.name
    · subst name
      simp [Function.update, hiBefore, hiName]
    · simpa [Function.update, hname, hiBefore, hi] using
        position_eq_some_iff heap hinverse (name := name) (i := i)
  · constructor
    · intro hupdated
      by_cases hname : name = removed.name
      · simp [Function.update, hname] at hupdated
      · have hposition : heap.Position name = some i := by
          simpa [Function.update, hname] using hupdated
        obtain ⟨hi, hiName⟩ := (position_eq_some_iff heap hinverse).1 hposition
        have hiLast : i = last := by simp at hiPop; dsimp [last]; omega
        subst i
        exact (hname hiName.symm).elim
    · rintro ⟨hi, _⟩
      exact (hiPop hi).elim

/-- Move the last entry to the root and remove the old root, before Heapify-down. -/
private def removeRoot (heap : Heap capacity Key) (hne : 0 < heap.H.size) :
    Heap capacity Key :=
  let last := heap.H.size - 1
  removeLast (heap.swapEntries 0 last) (by simpa using hne)

@[simp] private theorem removeRoot_size (heap : Heap capacity Key)
    (hne : 0 < heap.H.size) :
    (removeRoot heap hne).H.size = heap.H.size - 1 := by
  simp [removeRoot, removeLast]

private theorem removeRoot_positionInverse (heap : Heap capacity Key)
    (hinverse : heap.PositionInverse) (hne : 0 < heap.H.size) :
    (removeRoot heap hne).PositionInverse :=
  removeLast_positionInverse
    (heap.swapEntries 0 (heap.H.size - 1))
    (swapEntries_positionInverse heap hinverse 0 (heap.H.size - 1))
    (by simpa using hne)

private theorem swapRoot_last_getLast (heap : Heap capacity Key)
    (hne : 0 < heap.H.size) :
    let last := heap.H.size - 1
    (heap.swapEntries 0 last).H[last]'(by
        simpa using (show last < heap.H.size by omega)) = heap.H[0] := by
  dsimp only
  have hlast : heap.H.size - 1 < heap.H.size := by omega
  simp [swapEntries, hne, hlast]

/-- `removeRoot` is exactly the shortened state constructed inline by `delete 0`. -/
private theorem removeRoot_eq_shortened (heap : Heap capacity Key)
    (hne : 0 < heap.H.size) :
    removeRoot heap hne =
      let last := heap.H.size - 1
      let moved := heap.swapEntries 0 last
      { H := moved.H.pop
        Position := Function.update moved.Position heap.H[0].name none } := by
  simp only [removeRoot, removeLast]
  rw [show
    ((heap.swapEntries 0 (heap.H.size - 1)).H[
        (heap.swapEntries 0 (heap.H.size - 1)).H.size - 1]'(by
          simpa using (show heap.H.size - 1 < heap.H.size by omega))).name =
      heap.H[0].name by
      simpa using congrArg Entry.name (swapRoot_last_getLast heap hne)]

private theorem removeLast_contents_removed (heap : Heap capacity Key)
    (hne : 0 < heap.H.size) :
    let last := heap.H.size - 1
    let removed := heap.H[last]'(by omega)
    (removeLast heap hne).contents removed.name = none := by
  simp [removeLast, contents, Function.update]

private theorem removeLast_contents_other (heap : Heap capacity Key)
    (hinverse : heap.PositionInverse) (hne : 0 < heap.H.size)
    (query : Fin capacity)
    (hquery : query ≠ (heap.H[heap.H.size - 1]'(by omega)).name) :
    (removeLast heap hne).contents query = heap.contents query := by
  let last := heap.H.size - 1
  cases hposition : heap.Position query with
  | none =>
      simp [removeLast, contents, Function.update, hposition, hquery]
  | some k =>
      obtain ⟨hk, hname⟩ := (position_eq_some_iff heap hinverse).1 hposition
      have hkLast : k ≠ last := by
        intro heq
        subst k
        exact hquery hname.symm
      have hkPop : k < heap.H.size - 1 := by omega
      simp [removeLast, contents, Function.update, hposition, hquery,
        Array.getElem?_pop, hkPop]

private theorem removeRoot_removed_name_none (heap : Heap capacity Key)
    (hne : 0 < heap.H.size) :
    (removeRoot heap hne).contents heap.H[0].name = none := by
  let last := heap.H.size - 1
  let moved := heap.swapEntries 0 last
  have hmovedNe : 0 < moved.H.size := by
    simpa [moved] using hne
  have hlastName : moved.H[moved.H.size - 1].name = heap.H[0].name := by
    simpa [moved] using congrArg Entry.name (swapRoot_last_getLast heap hne)
  change (removeLast moved hmovedNe).contents heap.H[0].name = none
  simpa [hlastName] using removeLast_contents_removed moved hmovedNe

private theorem removeRoot_contents_other (heap : Heap capacity Key)
    (hinverse : heap.PositionInverse) (hne : 0 < heap.H.size)
    (query : Fin capacity) (hquery : query ≠ heap.H[0].name) :
    (removeRoot heap hne).contents query = heap.contents query := by
  let last := heap.H.size - 1
  let moved := heap.swapEntries 0 last
  have hmovedNe : 0 < moved.H.size := by
    simpa [moved] using hne
  have hmovedInverse : moved.PositionInverse :=
    swapEntries_positionInverse heap hinverse 0 last
  have hlastName : moved.H[moved.H.size - 1].name = heap.H[0].name := by
    simpa [moved, last] using congrArg Entry.name (swapRoot_last_getLast heap hne)
  change (removeLast moved hmovedNe).contents query = heap.contents query
  rw [removeLast_contents_other moved hmovedInverse hmovedNe query
    (by simpa [hlastName] using hquery)]
  exact swapEntries_contents heap 0 last query

private theorem removeRoot_getElem (heap : Heap capacity Key)
    (hne : 0 < heap.H.size) (k : Nat) (hk : k < (removeRoot heap hne).H.size) :
    (removeRoot heap hne).H[k] =
      if k = 0 then heap.H[heap.H.size - 1]'(by omega)
      else heap.H[k]'(by
        have hkShort : k < heap.H.size - 1 := by
          simpa [removeRoot, removeLast] using hk
        omega) := by
  have hkShort : k < heap.H.size - 1 := by
    simpa [removeRoot, removeLast] using hk
  have hkOld : k < heap.H.size := by omega
  have hlast : heap.H.size - 1 < heap.H.size := by omega
  have hkLast : k ≠ heap.H.size - 1 := by omega
  change (heap.swapEntries 0 (heap.H.size - 1)).H.pop[k] = _
  rw [Array.getElem_pop]
  simp only [swapEntries, dif_pos hne, dif_pos hlast]
  rw [Array.getElem_swap hne hlast]
  by_cases hkRoot : k = 0 <;> simp [hkRoot, hkLast]

private theorem keyAtWith_removeRoot (heap : Heap capacity Key)
    (hne : 0 < heap.H.size) (k : Nat)
    (hk : k < (removeRoot heap hne).H.size) :
    keyAtWith (removeRoot heap hne) 0 heap.H[0].key k hk =
      (heap.H[k]'(by
        have hkShort : k < heap.H.size - 1 := by
          simpa [removeRoot, removeLast] using hk
        omega)).key := by
  by_cases hkRoot : k = 0
  · subst k
    simp [keyAtWith]
  · simp only [keyAtWith, hkRoot, if_false]
    simp [removeRoot_getElem heap hne k hk, hkRoot]

private theorem removeRoot_almostHeapDown (heap : Heap capacity Key)
    (horder : heap.HeapOrdered) (hgt : 1 < heap.H.size) :
    AlmostHeapDown (removeRoot heap (by omega)) 0 := by
  have hne : 0 < heap.H.size := by omega
  have hroot : 0 < (removeRoot heap hne).H.size := by simpa using hgt
  have hlast : heap.H.size - 1 < heap.H.size := by omega
  refine ⟨hroot, heap.H[0].key, ?_, ?_⟩
  · simpa [removeRoot_getElem heap hne 0 hroot] using
      heapOrdered_root_le heap horder hne hlast
  · intro k hk
    by_cases hkRoot : k = 0
    · exact Or.inl hkRoot
    · right
      have hkOld : k < heap.H.size := by
        have hkShort : k < heap.H.size - 1 := by simpa using hk
        omega
      have hedge := (horder ⟨k, hkOld⟩).resolve_left hkRoot
      rw [keyAtWith_removeRoot heap hne (parent k) (parent_lt_size hk)]
      rw [keyAtWith_removeRoot heap hne k hk]
      exact hedge

/-- The one local Heapify-down following a nonempty root removal. -/
private def repairRoot (heap : Heap capacity Key) (hne : 0 < heap.H.size) :
    Heap capacity Key :=
  let shortened := removeRoot heap hne
  if 0 < shortened.H.size then shortened.heapifyDown 0 else shortened

private theorem repairRoot_wellFormed (heap : Heap capacity Key)
    (hwf : heap.WellFormed) (hne : 0 < heap.H.size) :
    (repairRoot heap hne).WellFormed := by
  let shortened := removeRoot heap hne
  by_cases hshort : 0 < shortened.H.size
  · rw [repairRoot, if_pos hshort]
    have hgt : 1 < heap.H.size := by simpa [shortened] using hshort
    refine ⟨?_, ?_, ?_⟩
    · simpa [shortened] using (Nat.sub_le heap.H.size 1).trans hwf.1
    · apply heapifyDown_heapOrdered
      simpa [shortened] using removeRoot_almostHeapDown heap hwf.2.1 hgt
    · apply heapifyDown_positionInverse
      simpa [shortened] using removeRoot_positionInverse heap hwf.2.2 hne
  · rw [repairRoot, if_neg hshort]
    refine ⟨?_, ?_, ?_⟩
    · simpa [shortened] using (Nat.sub_le heap.H.size 1).trans hwf.1
    · intro i
      exact (hshort (Nat.zero_lt_of_lt i.isLt)).elim
    · simpa [shortened] using removeRoot_positionInverse heap hwf.2.2 hne

/-- The root-specialized decomposition of the executable `delete` control flow. -/
private theorem extractMin_eq_repairRoot (heap : Heap capacity Key)
    (hne : 0 < heap.H.size) :
    heap.extractMin = (repairRoot heap hne, some heap.H[0]) := by
  rw [extractMin, delete, Array.getElem?_eq_getElem hne]
  dsimp only
  simp_rw [← removeRoot_eq_shortened heap hne]
  simp [repairRoot]

@[simp] private theorem repairRoot_contents (heap : Heap capacity Key)
    (hne : 0 < heap.H.size) (query : Fin capacity) :
    (repairRoot heap hne).contents query =
      (removeRoot heap hne).contents query := by
  simp only [repairRoot]
  split <;> simp_all

/-! ## Direct public-operation behavior -/

/-- Proof-only name for the local append performed by `insert`. -/
private def appendEntry (heap : Heap capacity Key) (entry : Entry capacity Key) :
    Heap capacity Key :=
  { H := heap.H.push entry
    Position := Function.update heap.Position entry.name (some heap.H.size) }

@[simp] private theorem appendEntry_size (heap : Heap capacity Key)
    (entry : Entry capacity Key) :
    (appendEntry heap entry).H.size = heap.H.size + 1 := by
  simp [appendEntry]

/-- Appending a fresh name preserves the mutual inverse before Heapify-up. -/
private theorem appendEntry_positionInverse (heap : Heap capacity Key)
    (hinverse : heap.PositionInverse) (entry : Entry capacity Key)
    (hfresh : heap.contains entry.name = false) :
    (appendEntry heap entry).PositionInverse := by
  rw [positionInverse_iff]
  intro name i
  change Function.update heap.Position entry.name (some heap.H.size) name = some i ↔
    ∃ hi : i < (heap.H.push entry).size, (heap.H.push entry)[i].name = name
  have hfresh' : heap.Position entry.name = none := by
    simpa [contains] using hfresh
  by_cases hi : i < heap.H.size
  · by_cases hname : name = entry.name
    · subst name
      have hentry : heap.H[i].name ≠ entry.name := by
        intro heq
        have hactive := (position_eq_some_iff heap hinverse).2 ⟨hi, heq⟩
        simp [hfresh'] at hactive
      simp [Function.update, hi, Array.getElem_push_lt, hentry, Nat.ne_of_gt hi]
    · simp [Function.update, hname, hi, Array.getElem_push_lt,
        position_eq_some_iff heap hinverse]; omega
  · have hposition : heap.Position name ≠ some i := fun h =>
      hi (position_lt_size heap hinverse h)
    by_cases hlast : i = heap.H.size
    · subst i
      by_cases hname : name = entry.name
      · simp [Function.update, hname]
      · simp [Function.update, hname, Ne.symm hname, hposition]
    · have hle : ¬i ≤ heap.H.size := by omega
      by_cases hname : name = entry.name
      · simp [Function.update, hname, Ne.symm hlast, hle]
      · simp [Function.update, hname, hposition, hle]

/-- An append creates only the possible parent violation repaired by Heapify-up. -/
private theorem appendEntry_almostHeapUp (heap : Heap capacity Key)
    (hordered : heap.HeapOrdered) (entry : Entry capacity Key) :
    AlmostHeapUp (appendEntry heap entry) heap.H.size := by
  have hi : heap.H.size < (appendEntry heap entry).H.size := by simp [appendEntry]
  let replacement : Key :=
    if hroot : heap.H.size = 0 then entry.key
    else
      max entry.key
        ((appendEntry heap entry).H[parent heap.H.size]'
          (parent_lt_size hi)).key
  refine ⟨hi, replacement, ?_, ?_⟩
  · have hlast : (appendEntry heap entry).H[heap.H.size].key = entry.key := by
      simp [appendEntry]
    rw [hlast]
    by_cases hroot : heap.H.size = 0 <;> simp [replacement, hroot]
  · intro k hk
    by_cases hkroot : k = 0
    · exact Or.inl hkroot
    · right
      by_cases hknew : k = heap.H.size
      · subst k
        have hpOld : parent heap.H.size < heap.H.size :=
          parent_lt_self hkroot
        simp [keyAtWith, replacement, hkroot, hpOld.ne, appendEntry,
          Array.getElem_push_lt hpOld]
      · have hkOld : k < heap.H.size := by
          simp [appendEntry] at hk
          omega
        have hpOld : parent k < heap.H.size :=
          (parent_lt_self hkroot).trans hkOld
        simpa [keyAtWith, appendEntry, hknew, Nat.ne_of_lt hpOld,
          Array.getElem_push_lt hkOld, Array.getElem_push_lt hpOld] using
          (hordered ⟨k, hkOld⟩).resolve_left hkroot

/-- Insertion succeeds exactly when capacity remains and the name is fresh. -/
theorem insert_success_iff (heap : Heap capacity Key) (entry : Entry capacity Key) :
    (heap.insert entry).2 = true ↔
      heap.H.size < capacity ∧ heap.contains entry.name = false := by
  by_cases hcapacity : heap.H.size < capacity
  · cases hactive : heap.contains entry.name <;> simp [insert, hcapacity, hactive]
  · simp [insert, hcapacity]

private theorem insert_eq_of_success (heap : Heap capacity Key)
    (entry : Entry capacity Key) (hsuccess : (heap.insert entry).2 = true) :
    heap.insert entry =
      ((appendEntry heap entry).heapifyUp heap.H.size, true) := by
  obtain ⟨hcapacity, hfresh⟩ := (insert_success_iff heap entry).1 hsuccess
  simp [insert, appendEntry, hcapacity, hfresh]

/-- An eligible insertion reports success without running a global invariant scan. -/
theorem insert_eligible_success (heap : Heap capacity Key) (entry : Entry capacity Key)
    (hcapacity : heap.H.size < capacity) (hfresh : heap.contains entry.name = false) :
    (heap.insert entry).2 = true := by
  exact (insert_success_iff heap entry).2 ⟨hcapacity, hfresh⟩

/-- A duplicate name is rejected and leaves the heap unchanged. -/
theorem insert_duplicate_failure (heap : Heap capacity Key) (entry : Entry capacity Key)
    (hactive : heap.contains entry.name = true) :
    heap.insert entry = (heap, false) := by
  simp [insert, hactive]

/-- A full heap rejects insertion and is left unchanged. -/
theorem insert_capacity_failure (heap : Heap capacity Key) (entry : Entry capacity Key)
    (hcapacity : capacity ≤ heap.H.size) :
    heap.insert entry = (heap, false) := by
  simp [insert, Nat.not_lt.mpr hcapacity]

/-- Every failed insertion leaves the heap unchanged. -/
theorem insert_failure_eq (heap : Heap capacity Key) (entry : Entry capacity Key)
    (hfailure : (heap.insert entry).2 = false) :
    heap.insert entry = (heap, false) := by
  by_cases hcapacity : heap.H.size < capacity
  · cases hactive : heap.contains entry.name <;>
      simp [insert, hcapacity, hactive] at hfailure ⊢
  · simp [insert, hcapacity]

/-- A successful insertion grows the active heap array by exactly one. -/
theorem insert_success_size (heap : Heap capacity Key) (entry : Entry capacity Key)
    (hsuccess : (heap.insert entry).2 = true) :
    (heap.insert entry).1.H.size = heap.H.size + 1 := by
  rw [insert_eq_of_success heap entry hsuccess, heapifyUp_size, appendEntry_size]

/-- `insert` preserves all representation invariants. -/
theorem insert_wellFormed (heap : Heap capacity Key) (hwf : heap.WellFormed)
    (entry : Entry capacity Key) :
    (heap.insert entry).1.WellFormed := by
  by_cases hsuccess : (heap.insert entry).2 = true
  · obtain ⟨hcapacity, hfresh⟩ := (insert_success_iff heap entry).1 hsuccess
    rw [insert_eq_of_success heap entry hsuccess]
    exact ⟨by simpa using hcapacity,
      heapifyUp_heapOrdered _ _ (appendEntry_almostHeapUp heap hwf.2.1 entry),
      heapifyUp_positionInverse _ _
        (appendEntry_positionInverse heap hwf.2.2 entry hfresh)⟩
  · rw [insert_failure_eq heap entry (Bool.eq_false_of_not_eq_true hsuccess)]
    exact hwf

/-- `insert` preserves the mutual inverse independently of heap order. -/
theorem insert_positionInverse (heap : Heap capacity Key)
    (hinverse : heap.PositionInverse) (entry : Entry capacity Key) :
    (heap.insert entry).1.PositionInverse := by
  by_cases hsuccess : (heap.insert entry).2 = true
  · have hfresh := (insert_success_iff heap entry).1 hsuccess |>.2
    rw [insert_eq_of_success heap entry hsuccess]
    exact heapifyUp_positionInverse _ _
      (appendEntry_positionInverse heap hinverse entry hfresh)
  · rw [insert_failure_eq heap entry (Bool.eq_false_of_not_eq_true hsuccess)]
    exact hinverse

/-- A successful insertion stores exactly the requested key under the inserted name. -/
theorem insert_contents_self (heap : Heap capacity Key) (entry : Entry capacity Key)
    (hsuccess : (heap.insert entry).2 = true) :
    (heap.insert entry).1.contents entry.name = some entry.key := by
  rw [insert_eq_of_success heap entry hsuccess, heapifyUp_contents]
  simp [appendEntry, contents, Function.update]

/-- A successful insertion leaves every other name's logical contents unchanged. -/
theorem insert_contents_other (heap : Heap capacity Key)
    (hinverse : heap.PositionInverse) (entry : Entry capacity Key)
    (hsuccess : (heap.insert entry).2 = true) (query : Fin capacity)
    (hquery : query ≠ entry.name) :
    (heap.insert entry).1.contents query = heap.contents query := by
  rw [insert_eq_of_success heap entry hsuccess, heapifyUp_contents]
  cases hposition : heap.Position query with
  | none =>
      simp [appendEntry, contents, Function.update, hquery, hposition]
  | some i =>
      have hi := position_lt_size heap hinverse hposition
      simp [appendEntry, contents, Function.update, hquery, hposition,
        Array.getElem?_push_lt hi, Array.getElem?_eq_getElem hi]

/-- Successful insertion adds the requested name and leaves every other active-name bit alone. -/
theorem insert_success_contains (heap : Heap capacity Key) (entry : Entry capacity Key)
    (hsuccess : (heap.insert entry).2 = true) (query : Fin capacity) :
    (heap.insert entry).1.contains query =
      if query = entry.name then true else heap.contains query := by
  rw [insert_eq_of_success heap entry hsuccess, heapifyUp_contains]
  by_cases hquery : query = entry.name <;>
    simp [appendEntry, contains, Function.update, hquery]

/-! ## Derived repeated insertion -/

private theorem insertAll_fold_failed (heap : Heap capacity Key)
    (entries : List (Entry capacity Key)) :
    entries.foldl
      (fun (state : Heap capacity Key × Bool) entry =>
        if state.2 then state.1.insert entry else state)
      (heap, false) = (heap, false) := by
  induction entries generalizing heap <;> simp_all

private theorem insertAll_cons (heap : Heap capacity Key)
    (entry : Entry capacity Key) (entries : List (Entry capacity Key)) :
    heap.insertAll (entry :: entries) =
      if (heap.insert entry).2 then
        (heap.insert entry).1.insertAll entries
      else
        (heap, false) := by
  simp only [insertAll, List.foldl_cons, if_true]
  by_cases hsuccess : (heap.insert entry).2 = true
  · rw [if_pos hsuccess,
      show heap.insert entry = ((heap.insert entry).1, true) from
        Prod.ext rfl hsuccess]
  · rw [if_neg hsuccess, insert_failure_eq heap entry
      (Bool.eq_false_of_not_eq_true hsuccess)]
    exact insertAll_fold_failed heap entries

private theorem insertAll_success_transport
    (P : Heap capacity Key → List (Entry capacity Key) → Heap capacity Key → Prop)
    (hnil : ∀ heap, P heap [] heap)
    (hcons : ∀ heap entry entries final,
      (heap.insert entry).2 = true →
      P (heap.insert entry).1 entries final →
      P heap (entry :: entries) final)
    (heap : Heap capacity Key) (entries : List (Entry capacity Key))
    (hsuccess : (heap.insertAll entries).2 = true) :
    P heap entries (heap.insertAll entries).1 := by
  induction entries generalizing heap with
  | nil => simpa [insertAll] using hnil heap
  | cons entry entries ih =>
      rw [insertAll_cons] at hsuccess ⊢
      by_cases hfirst : (heap.insert entry).2 = true
      · simp only [hfirst, if_true] at hsuccess ⊢
        exact hcons heap entry entries _ hfirst (ih _ hsuccess)
      · simp [hfirst] at hsuccess

/-- Successful repeated insertion grows the heap by the number of entries. -/
theorem insertAll_success_size (heap : Heap capacity Key)
    (entries : List (Entry capacity Key))
    (hsuccess : (heap.insertAll entries).2 = true) :
    (heap.insertAll entries).1.H.size = heap.H.size + entries.length := by
  apply insertAll_success_transport
    (P := fun initial inserted final =>
      final.H.size = initial.H.size + inserted.length)
    (fun _ => by simp) ?_ heap entries hsuccess
  intro initial entry tail final hfirst htail
  rw [insert_success_size initial entry hfirst] at htail
  simp only [List.length_cons]
  omega

/-- Successful repeated insertion preserves all representation invariants. -/
theorem insertAll_success_wellFormed (heap : Heap capacity Key)
    (hwf : heap.WellFormed) (entries : List (Entry capacity Key))
    (hsuccess : (heap.insertAll entries).2 = true) :
    (heap.insertAll entries).1.WellFormed := by
  exact (insertAll_success_transport
    (P := fun initial _ final => initial.WellFormed → final.WellFormed)
    (fun _ => id)
    (fun initial entry _ _ _ htail hinitial =>
      htail (insert_wellFormed initial hinitial entry))
    heap entries hsuccess) hwf

/-- Successful repeated insertion preserves the Position inverse. -/
theorem insertAll_success_positionInverse (heap : Heap capacity Key)
    (hinverse : heap.PositionInverse) (entries : List (Entry capacity Key))
    (hsuccess : (heap.insertAll entries).2 = true) :
    (heap.insertAll entries).1.PositionInverse := by
  exact (insertAll_success_transport
    (P := fun initial _ final => initial.PositionInverse → final.PositionInverse)
    (fun _ => id)
    (fun initial entry _ _ _ htail hinitial =>
      htail (insert_positionInverse initial hinitial entry))
    heap entries hsuccess) hinverse

/--
Distinct fresh entries that fit in the remaining capacity all insert successfully.
-/
theorem insertAll_eligible_success (heap : Heap capacity Key)
    (entries : List (Entry capacity Key))
    (hcapacity : heap.H.size + entries.length ≤ capacity)
    (hnames : (entries.map Entry.name).Nodup)
    (hfresh : ∀ entry ∈ entries, heap.contains entry.name = false) :
    (heap.insertAll entries).2 = true := by
  induction entries generalizing heap with
  | nil => simp [insertAll]
  | cons entry entries ih =>
      have hnames' := (List.nodup_cons.mp hnames)
      simp only [List.length_cons] at hcapacity
      have hentryCapacity : heap.H.size < capacity := by omega
      have hfirst : (heap.insert entry).2 = true :=
        insert_eligible_success heap entry hentryCapacity
          (hfresh entry (by simp))
      have htailCapacity :
          (heap.insert entry).1.H.size + entries.length ≤ capacity := by
        rw [insert_success_size heap entry hfirst]
        omega
      have htailFresh :
          ∀ next ∈ entries,
            (heap.insert entry).1.contains next.name = false := by
        intro next hnext
        have hne : next.name ≠ entry.name := by
          intro heq
          exact hnames'.1 (by
            rw [← heq]
            exact List.mem_map.mpr ⟨next, hnext, rfl⟩)
        rw [insert_success_contains heap entry hfirst next.name]
        simp [hne, hfresh next (by simp [hnext])]
      rw [insertAll_cons, if_pos hfirst]
      exact ih (heap.insert entry).1 htailCapacity hnames'.2 htailFresh

/-- Repeated insertion leaves every name absent from the input list unchanged. -/
theorem insertAll_success_contents_other (heap : Heap capacity Key)
    (hinverse : heap.PositionInverse) (entries : List (Entry capacity Key))
    (hsuccess : (heap.insertAll entries).2 = true) (query : Fin capacity)
    (hquery : query ∉ entries.map Entry.name) :
    (heap.insertAll entries).1.contents query = heap.contents query := by
  exact insertAll_success_transport
    (P := fun initial inserted final => initial.PositionInverse →
      ∀ query, query ∉ inserted.map Entry.name →
        final.contents query = initial.contents query)
    (fun _ _ _ _ => rfl) (by
      intro initial entry tail _ hfirst htail hinitial query hquery
      have hquery' : query ≠ entry.name ∧ query ∉ tail.map Entry.name := by
        simpa using hquery
      rw [htail (insert_positionInverse initial hinitial entry) query hquery'.2]
      exact insert_contents_other initial hinitial entry hfirst query hquery'.1)
    heap entries hsuccess hinverse query hquery

/-- Every distinctly named entry in a successful repeated insertion has its requested key. -/
theorem insertAll_success_contents (heap : Heap capacity Key)
    (hinverse : heap.PositionInverse) (entries : List (Entry capacity Key))
    (hnames : (entries.map Entry.name).Nodup)
    (hsuccess : (heap.insertAll entries).2 = true)
    (entry : Entry capacity Key) (hentry : entry ∈ entries) :
    (heap.insertAll entries).1.contents entry.name = some entry.key := by
  induction entries generalizing heap with
  | nil => simp at hentry
  | cons first entries ih =>
      have hnames' := List.nodup_cons.mp hnames
      rw [insertAll_cons] at hsuccess ⊢
      by_cases hfirst : (heap.insert first).2 = true
      · rw [if_pos hfirst] at hsuccess ⊢
        rcases List.mem_cons.mp hentry with rfl | htail
        · rw [insertAll_success_contents_other (heap.insert entry).1
            (insert_positionInverse heap hinverse entry) entries hsuccess
            entry.name hnames'.1]
          exact insert_contents_self heap entry hfirst
        · exact ih (heap.insert first).1
            (insert_positionInverse heap hinverse first) hnames'.2
            hsuccess htail
      · simp [hfirst] at hsuccess

/-- Every entry in an eligible repeated insertion receives exactly its requested key. -/
theorem insertAll_eligible_contents (heap : Heap capacity Key)
    (hinverse : heap.PositionInverse) (entries : List (Entry capacity Key))
    (hcapacity : heap.H.size + entries.length ≤ capacity)
    (hnames : (entries.map Entry.name).Nodup)
    (hfresh : ∀ entry ∈ entries, heap.contains entry.name = false)
    (entry : Entry capacity Key) (hentry : entry ∈ entries) :
    (heap.insertAll entries).1.contents entry.name = some entry.key := by
  exact insertAll_success_contents heap hinverse entries hnames
    (insertAll_eligible_success heap entries hcapacity hnames hfresh) entry hentry

/-- Positional deletion returns exactly the entry formerly stored at that position. -/
theorem delete_returned_at (heap next : Heap capacity Key) (i : Nat)
    {removed : Entry capacity Key}
    (hsuccess : heap.delete i = (next, some removed)) :
    heap.H[i]? = some removed := by
  cases hentry : heap.H[i]? with
  | none =>
      simp [delete, hentry] at hsuccess
  | some entry =>
    rw [delete, hentry] at hsuccess
    have hsecond := congrArg Prod.snd hsuccess
    simp only at hsecond
    rw [Option.some.inj hsecond]

/-- Deleting a valid position succeeds without running a global invariant scan. -/
theorem delete_valid_success (heap : Heap capacity Key) {i : Nat} (hi : i < heap.H.size) :
    (heap.delete i).2.isSome = true := by
  rw [delete, Array.getElem?_eq_getElem hi]
  simp

/-- Extracting from a nonempty heap succeeds. -/
theorem extractMin_nonempty_success (heap : Heap capacity Key) (hne : 0 < heap.H.size) :
    heap.extractMin.2.isSome = true := by
  simpa [extractMin] using delete_valid_success (heap := heap) hne

/-- A nonempty extraction returns the old root entry. -/
theorem extractMin_nonempty_result (heap : Heap capacity Key) (hne : 0 < heap.H.size) :
    heap.extractMin.2 = some heap.H[0] := by
  simp [extractMin, delete, hne]

/-- A nonempty extraction removes exactly one active array entry. -/
theorem extractMin_nonempty_size (heap : Heap capacity Key) (hne : 0 < heap.H.size) :
    heap.extractMin.1.H.size + 1 = heap.H.size := by
  simp [extractMin, delete, hne]
  split <;> simp_all <;> omega

/-- Extracting from a well-formed nonempty heap preserves all representation invariants. -/
theorem extractMin_wellFormed (heap : Heap capacity Key)
    (hwf : heap.WellFormed) (hne : 0 < heap.H.size) :
    heap.extractMin.1.WellFormed := by
  rw [extractMin_eq_repairRoot heap hne]
  exact repairRoot_wellFormed heap hwf hne

/--
Extraction removes exactly the root's name from the logical contents map.

Together with `extractMin_returns_minimum`, this states the representation-independent removal law
needed by Dijkstra.
-/
theorem extractMin_contents (heap : Heap capacity Key)
    (hwf : heap.WellFormed) (hne : 0 < heap.H.size) :
    heap.extractMin.1.contents heap.H[0].name = none ∧
      ∀ query : Fin capacity, query ≠ heap.H[0].name →
        heap.extractMin.1.contents query = heap.contents query := by
  rw [extractMin_eq_repairRoot heap hne]
  simpa only [repairRoot_contents] using
    And.intro (removeRoot_removed_name_none heap hne)
      (removeRoot_contents_other heap hwf.2.2 hne)

/-- Extraction removes precisely the returned root name from the active-name set. -/
theorem extractMin_contains_eq_true_iff (heap : Heap capacity Key)
    (hwf : heap.WellFormed) (hne : 0 < heap.H.size) (query : Fin capacity) :
    heap.extractMin.1.contains query = true ↔
      query ≠ heap.H[0].name ∧ heap.contains query = true := by
  have hnext := extractMin_wellFormed heap hwf hne
  have hcontents := extractMin_contents heap hwf hne
  rw [contains_eq_true_iff_exists_contents heap.extractMin.1 hnext.2.2 query,
    contains_eq_true_iff_exists_contents heap hwf.2.2 query]
  constructor
  · rintro ⟨key, hkey⟩
    have hneName : query ≠ heap.H[0].name := by
      rintro rfl
      simp [hcontents.1] at hkey
    refine ⟨hneName, key, ?_⟩
    rwa [← hcontents.2 query hneName]
  · rintro ⟨hneName, key, hkey⟩
    refine ⟨key, ?_⟩
    rwa [hcontents.2 query hneName]

/-- The entry returned by `ExtractMin` was a minimum active entry in the input heap. -/
theorem extractMin_returns_minimum (heap next : Heap capacity Key)
    (hwf : heap.WellFormed) {removed : Entry capacity Key}
    (hextract : heap.extractMin = (next, some removed)) :
    removed ∈ heap.H ∧
      ∀ candidate ∈ heap.H, removed.key ≤ candidate.key := by
  apply findMin_minimum heap hwf
  simpa [findMin] using
    delete_returned_at heap next 0 (by simpa [extractMin] using hextract)

/-- Changing an active name succeeds on a heap with a valid Position inverse. -/
theorem changeKey_active_success (heap : Heap capacity Key) (hinverse : heap.PositionInverse)
    (name : Fin capacity) (newKey : Key) {i : Nat}
    (hposition : heap.Position name = some i) :
    (heap.changeKey name newKey).2 = true := by
  have hi := position_lt_size heap hinverse hposition
  have hvalid := validPosition?_eq_some heap hinverse hposition
  simp [changeKey, hvalid, Array.getElem?_eq_getElem hi]

/-- `ChangeKey` never changes the number of active heap entries. -/
@[simp] theorem changeKey_size (heap : Heap capacity Key) (name : Fin capacity)
    (newKey : Key) :
    (heap.changeKey name newKey).1.H.size = heap.H.size := by
  simp only [changeKey]
  split <;> try rfl
  split <;> try rfl
  dsimp only
  split
  · simp
  · split <;> simp

/--
`ChangeKey` preserves well-formedness without consulting the executable invariant checker.

The proof follows the same branch as the program: a decrease establishes the localized
Heapify-up precondition, an increase establishes the Heapify-down precondition, and an equal key
is the identity write.
-/
theorem changeKey_wellFormed (heap : Heap capacity Key)
    (hwf : heap.WellFormed) (name : Fin capacity) (newKey : Key) :
    (heap.changeKey name newKey).1.WellFormed := by
  cases hposition : heap.Position name with
  | none => simpa [changeKey, validPosition?, hposition] using hwf
  | some i =>
      have hi := position_lt_size heap hwf.2.2 hposition
      have hvalid := validPosition?_eq_some heap hwf.2.2 hposition
      simp only [changeKey, hvalid]
      rw [Array.getElem?_eq_getElem hi]
      dsimp only
      let fi : Fin heap.H.size := ⟨i, hi⟩
      split
      · next hdecrease =>
        simpa [withKey, fi] using
          withKey_heapifyUp_wellFormed heap hwf fi newKey hdecrease.le
      · next hdecrease =>
        split
        · next hincrease =>
          simpa [withKey, fi] using
            withKey_heapifyDown_wellFormed heap hwf fi newKey hincrease.le
        · next hincrease =>
          have heq : newKey = heap.H[i].key :=
            le_antisymm (le_of_not_gt hincrease) (le_of_not_gt hdecrease)
          subst newKey
          change (withKey heap fi heap.H[fi].key).WellFormed
          rw [withKey_same]
          exact hwf

private theorem changeKey_contents_of_active (heap : Heap capacity Key)
    (hinverse : heap.PositionInverse) (name : Fin capacity) (newKey : Key)
    {i : Nat} (hposition : heap.Position name = some i) (query : Fin capacity) :
    (heap.changeKey name newKey).1.contents query =
      if query = name then some newKey else heap.contents query := by
  obtain ⟨hi, hname⟩ := (position_eq_some_iff heap hinverse).1 hposition
  let updated : Heap capacity Key :=
    { heap with H := heap.H.setIfInBounds i { heap.H[i] with key := newKey } }
  have hupdated : updated.contents query =
      if query = name then some newKey else heap.contents query := by
    by_cases hquery : query = name
    · subst query
      simp [updated, contents, hposition,
        Array.getElem?_setIfInBounds_self_of_lt hi]
    · cases hqueryPosition : heap.Position query with
      | none => simp [updated, contents, hquery, hqueryPosition]
      | some k =>
          obtain ⟨_, hqueryName⟩ :=
            (position_eq_some_iff heap hinverse).1 hqueryPosition
          have hki : k ≠ i := fun h =>
            hquery (hqueryName.symm.trans (h ▸ hname))
          simp [updated, contents, hquery, hqueryPosition, Ne.symm hki,
            Array.getElem?_setIfInBounds_ne]
  have hvalid := validPosition?_eq_some heap hinverse hposition
  simp only [changeKey, hvalid]
  rw [Array.getElem?_eq_getElem hi]
  dsimp only
  split
  · simpa [updated] using hupdated
  · split <;> simpa [updated] using hupdated

/-- `ChangeKey` stores the requested key for an active name. -/
theorem changeKey_contents_self (heap : Heap capacity Key) (hinverse : heap.PositionInverse)
    (name : Fin capacity) (newKey : Key) {i : Nat}
    (hposition : heap.Position name = some i) :
    (heap.changeKey name newKey).1.contents name = some newKey := by
  simpa using changeKey_contents_of_active heap hinverse name newKey hposition name

/-- `ChangeKey` leaves every other name's logical contents unchanged. -/
theorem changeKey_contents_other (heap : Heap capacity Key) (hinverse : heap.PositionInverse)
    (name query : Fin capacity) (newKey : Key) (hquery : query ≠ name) {i : Nat}
    (hposition : heap.Position name = some i) :
    (heap.changeKey name newKey).1.contents query = heap.contents query := by
  simpa [hquery] using
    changeKey_contents_of_active heap hinverse name newKey hposition query

/-- `ChangeKey` preserves exactly the active-name set. -/
theorem changeKey_contains (heap : Heap capacity Key) (name : Fin capacity)
    (newKey : Key) (query : Fin capacity) :
    (heap.changeKey name newKey).1.contains query = heap.contains query := by
  simp only [changeKey]
  split <;> try rfl
  split <;> try rfl
  dsimp only
  split
  · simpa [contains] using (heapifyUp_contains _ _ query)
  · split
    · simpa [contains] using (heapifyDown_contains _ _ query)
    · rfl

end Heap

end KleinbergPriorityQueue
