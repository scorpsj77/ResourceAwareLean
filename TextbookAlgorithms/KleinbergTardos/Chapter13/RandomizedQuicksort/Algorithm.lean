/-
Copyright (c) 2026 Jiyuan (Chai Yuen) Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan (Chai Yuen) Ji
-/

import ResourceAware.Algorithms.Sorting.Model
import Mathlib.Data.List.Perm.Basic

/-!
# Kleinberg--Tardos randomized Quicksort as an abstract program

This file follows Chapter 13, Section 13.5 of Kleinberg and Tardos.  The algorithm is represented
only as a polynomial free-monad program.  In particular, choosing a uniformly random pivot and
answering key comparisons are abstract requests here; interpreters provide their semantics later.

The base-case marker, pivot-selection frame, and individual comparisons are separate operations.
Consequently, a cost model can vary their charges independently.  This file assigns no charges
and does not run the recursion in a concrete cost monad.
-/

universe u

namespace KleinbergRandomizedQuicksort

open ResourceAware ResourceAware.Algorithms

/--
Operations requested by randomized Quicksort.

`choosePivotIndex tailLength` asks for an index in a nonempty list of length
`tailLength + 1`.  Its source-faithful interpreter samples that finite type uniformly.
-/
inductive Op (α : Type u) : Type u where
  | comparison (operation : Sorting.ComparisonOp α)
  | baseCase (size : Nat)
  | choosePivotIndex (tailLength : Nat)
deriving Repr, DecidableEq

/-- The response supplied by an interpreter for each Quicksort operation. -/
abbrev Response {α : Type u} : Op α → Type u
  | .comparison operation => Sorting.ComparisonResponse operation
  | .baseCase _ => PUnit
  | .choosePivotIndex tailLength => ULift (Fin (tailLength + 1))

/-- Polynomial signature for randomized Quicksort. -/
def Signature (α : Type u) : ResourceAware.Program.Signature.{u, u} where
  A := Op α
  B := fun operation ↦ Response operation

/-- Syntax trees for representation-, probability-, and cost-independent Quicksort programs. -/
abbrev Program (α : Type u) (β : Type u) : Type u :=
  ResourceAware.Program.Free (Signature α) β

variable {α : Type u}

/-- Lift one Quicksort operation into the free monad. -/
def request (operation : Op α) : Program α (Response operation) :=
  ResourceAware.Program.request (signature := Signature α) operation

/-- Mark a textbook constant-size base case without assigning it a resource charge. -/
def markBaseCase (size : Nat) : Program α PUnit :=
  request (.baseCase size)

/-- Request a pivot index for a list whose length is `tailLength + 1`. -/
def choosePivotIndex (tailLength : Nat) : Program α (ULift (Fin (tailLength + 1))) :=
  request (.choosePivotIndex tailLength)

/-- Request one `left ≤ right` comparison. -/
def compareLE (left right : α) : Program α (ULift Bool) :=
  request (.comparison (.le left right))

/-! ## Syntactic pivot freedom -/

/-- A free program is pivot-free when none of its possible continuations requests a pivot. -/
def PivotFree : Program α β -> Prop
  | .pure _ => True
  | .liftBind operation next =>
      (match operation with
        | .choosePivotIndex _ => False
        | _ => True) ∧
      forall response, PivotFree (next response)

namespace PivotFree

@[simp] theorem pure (value : β) :
    PivotFree (pure value : Program α β) :=
  trivial

theorem bind (program : Program α β) (next : β -> Program α γ)
    (hProgram : PivotFree program) (hNext : forall value, PivotFree (next value)) :
    PivotFree (program >>= next) := by
  induction program with
  | pure value => exact hNext value
  | liftBind operation continuation ih =>
      have hBind :
          PFunctor.FreeM.liftBind operation continuation >>= next =
            PFunctor.FreeM.liftBind operation
              (fun response => continuation response >>= next) := rfl
      rw [hBind]
      unfold PivotFree at hProgram ⊢
      cases operation with
      | comparison operation =>
          exact ⟨trivial, fun response => ih response (hProgram.2 response)⟩
      | baseCase size =>
          exact ⟨trivial, fun response => ih response (hProgram.2 response)⟩
      | choosePivotIndex tailLength =>
          exact hProgram.1.elim

@[simp] theorem markBaseCase (size : Nat) :
    PivotFree (KleinbergRandomizedQuicksort.markBaseCase (α := α) size) := by
  unfold KleinbergRandomizedQuicksort.markBaseCase request ResourceAware.Program.request
  unfold PFunctor.FreeM.lift
  exact ⟨trivial, fun _ => trivial⟩

@[simp] theorem compareLE (left right : α) :
    PivotFree (KleinbergRandomizedQuicksort.compareLE left right) := by
  unfold KleinbergRandomizedQuicksort.compareLE request ResourceAware.Program.request
  unfold PFunctor.FreeM.lift
  exact ⟨trivial, fun _ => trivial⟩

end PivotFree

/-! ## Certified partitioning -/

/--
The two lists produced by partitioning `input`, together with the permutation certificate needed
to justify that both recursive subproblems are smaller than the original problem.
-/
structure PartitionResult (input : List α) where
  lower : List α
  upper : List α
  perm : List.Perm (lower ++ upper) input

/--
Partition a pivot-free list around `pivot`.

Exactly one abstract comparison is requested for every input element.  With the ascending
linear-order interpreter and a duplicate-free input, `left ≤ pivot` is equivalent to the
textbook's strict lower-side test because the selected pivot has already been removed.
-/
def partitionProgram (pivot : α) : (input : List α) → Program α (PartitionResult input)
  | [] => pure ⟨[], [], .refl []⟩
  | value :: rest => do
      let goesLower ← compareLE value pivot
      let parts ← partitionProgram pivot rest
      if goesLower.down then
        pure {
          lower := value :: parts.lower
          upper := parts.upper
          perm := by simpa using parts.perm.cons value
        }
      else
        pure {
          lower := parts.lower
          upper := value :: parts.upper
          perm := by
            exact List.perm_middle.trans (parts.perm.cons value)
        }

theorem PivotFree.partitionProgram (pivot : α) (input : List α) :
    PivotFree (partitionProgram pivot input) := by
  induction input with
  | nil => exact PivotFree.pure _
  | cons value rest ih =>
      rw [KleinbergRandomizedQuicksort.partitionProgram]
      refine PivotFree.bind _ _ (PivotFree.compareLE value pivot) ?_
      intro goesLower
      refine PivotFree.bind _ _ ih ?_
      intro parts
      split <;> exact PivotFree.pure _

/-! ## Constant-size sorting network -/

/-- Sort two values using exactly one abstract comparison. -/
def compareSwap (left right : α) : Program α (α × α) := do
  let ordered ← compareLE left right
  if ordered.down then pure (left, right) else pure (right, left)

theorem PivotFree.compareSwap (left right : α) :
    PivotFree (compareSwap left right) := by
  unfold KleinbergRandomizedQuicksort.compareSwap
  refine PivotFree.bind _ _ (PivotFree.compareLE left right) ?_
  intro ordered
  split <;> exact PivotFree.pure _

/--
Implement the textbook's unspecified `Sort S` base case by a fixed sorting network.

Lists of length zero or one use no comparisons, length two uses one, and length three uses three.
The final fallback makes the helper total but is unreachable from `quicksortProgram`.
-/
def sortSmallProgram : List α → Program α (List α)
  | [] => do
      markBaseCase 0
      pure []
  | [value] => do
      markBaseCase 1
      pure [value]
  | [first, second] => do
      markBaseCase 2
      let (least, greatest) ← compareSwap first second
      pure [least, greatest]
  | [first, second, third] => do
      markBaseCase 3
      let (first, second) ← compareSwap first second
      let (second, third) ← compareSwap second third
      let (first, second) ← compareSwap first second
      pure [first, second, third]
  | input => pure input

theorem PivotFree.sortSmallProgram (input : List α) :
    PivotFree (sortSmallProgram input) := by
  cases input with
  | nil =>
      rw [KleinbergRandomizedQuicksort.sortSmallProgram]
      refine PivotFree.bind _ _ (PivotFree.markBaseCase 0) ?_
      intro _
      exact PivotFree.pure _
  | cons first rest =>
      cases rest with
      | nil =>
          rw [KleinbergRandomizedQuicksort.sortSmallProgram]
          refine PivotFree.bind _ _ (PivotFree.markBaseCase 1) ?_
          intro _
          exact PivotFree.pure _
      | cons second rest =>
          cases rest with
          | nil =>
              rw [KleinbergRandomizedQuicksort.sortSmallProgram]
              refine PivotFree.bind _ _ (PivotFree.markBaseCase 2) ?_
              intro _
              refine PivotFree.bind _ _ (PivotFree.compareSwap first second) ?_
              intro _
              exact PivotFree.pure _
          | cons third rest =>
              cases rest with
              | nil =>
                  rw [KleinbergRandomizedQuicksort.sortSmallProgram]
                  refine PivotFree.bind _ _ (PivotFree.markBaseCase 3) ?_
                  intro _
                  refine PivotFree.bind _ _ (PivotFree.compareSwap first second) ?_
                  intro firstPair
                  refine PivotFree.bind _ _
                    (PivotFree.compareSwap firstPair.2 third) ?_
                  intro secondPair
                  refine PivotFree.bind _ _
                    (PivotFree.compareSwap firstPair.1 secondPair.1) ?_
                  intro _
                  exact PivotFree.pure _
              | cons fourth rest =>
                  change PivotFree
                    (PFunctor.FreeM.pure (first :: second :: third :: fourth :: rest) :
                      Program α (List α))
                  exact PivotFree.pure _

/-! ## Randomized Quicksort -/

/--
Kleinberg--Tardos randomized Quicksort.

The pivot request supplies an index into the current list.  The pivot is removed before
partitioning, both certified partitions are recursively sorted, and the results are glued around
the pivot.  Termination is by list length and holds for every response an interpreter can provide.
-/
def quicksortProgram : (input : List α) → Program α (List α)
  | [] => sortSmallProgram []
  | first :: rest => do
      if (first :: rest).length ≤ 3 then
        sortSmallProgram (first :: rest)
      else
        let sampledIndex ← choosePivotIndex rest.length
        let pivot := (first :: rest).get sampledIndex.down
        let remainder := (first :: rest).eraseIdx sampledIndex.down
        let parts ← partitionProgram pivot remainder
        let sortedLower ← quicksortProgram parts.lower
        let sortedUpper ← quicksortProgram parts.upper
        pure (sortedLower ++ pivot :: sortedUpper)
termination_by input => input.length
decreasing_by
  all_goals
    have hErase :
        ((first :: rest).eraseIdx sampledIndex.down).length + 1 =
          (first :: rest).length :=
      List.length_eraseIdx_add_one sampledIndex.down.isLt
    have hParts :
        parts.lower.length + parts.upper.length =
          ((first :: rest).eraseIdx sampledIndex.down).length := by
      simpa using parts.perm.length_eq
    omega

theorem PivotFree.quicksortProgram_of_length_le_three (input : List α)
    (hLength : input.length <= 3) :
    PivotFree (quicksortProgram input) := by
  cases input with
  | nil =>
      rw [quicksortProgram]
      exact PivotFree.sortSmallProgram []
  | cons first rest =>
      rw [quicksortProgram, if_pos hLength]
      exact PivotFree.sortSmallProgram (first :: rest)

end KleinbergRandomizedQuicksort
