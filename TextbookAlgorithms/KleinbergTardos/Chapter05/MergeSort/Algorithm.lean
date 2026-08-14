/-
Copyright (c) 2026 Jiyuan (Chai Yuen) Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan (Chai Yuen) Ji
-/
import ResourceAware.Algorithms.Sorting.Model

/-!
# Kleinberg's merge sort as an abstract program

This version follows Section 5.1 of Kleinberg and Tardos.  It stops the divide-and-conquer
recursion at lists of size at most two and leaves the costs of the abstract split and merge
operations to the selected structural backend.  Key comparisons remain separate requests, so a
cost model can charge structural data movement and value comparisons independently.
-/

universe u

namespace KleinbergMergeSort

open ResourceAware ResourceAware.Algorithms

/-- Merge-sort-specific operations together with the shared sorting comparison operation. -/
inductive Op (α : Type u) : Type u where
  | comparison (op : Sorting.ComparisonOp α)
  | baseCase (size : Nat)
  | split (size : Nat)
  | merge (size : Nat)
deriving Repr, DecidableEq

/-- Response supplied by an interpreter for each abstract merge-sort operation. -/
abbrev Response {α : Type u} : Op α → Type u
  | .comparison op => Sorting.ComparisonResponse op
  | .baseCase _ => PUnit
  | .split _ => PUnit
  | .merge _ => PUnit

/-- Polynomial signature for Kleinberg merge sort. -/
def Signature (α : Type u) : ResourceAware.Program.Signature.{u, u} where
  A := Op α
  B := fun op ↦ Response op

/-- Syntax trees for representation- and cost-independent merge-sort programs. -/
abbrev Program (α : Type u) (β : Type u) : Type u :=
  ResourceAware.Program.Free (Signature α) β

variable {α : Type u}

/-- Lift one merge-sort request into the free monad. -/
def request (op : Op α) : Program α (Response op) :=
  ResourceAware.Program.request (signature := Signature α) op

/-! ## Algorithm -/

/-- Merge two sorted lists, requesting one abstract key comparison at every comparison step. -/
def mergeCore : List α → List α → Program α (List α)
  | [], ys => pure ys
  | xs, [] => pure xs
  | x :: xs, y :: ys => do
      let ordered ← request (.comparison (.le x y))
      if ordered.down then
        let rest ← mergeCore xs (y :: ys)
        pure (x :: rest)
      else
        let rest ← mergeCore (x :: xs) ys
        pure (y :: rest)

/-- Request structural recombination, then execute its separately observed key comparisons. -/
def merge (xs ys : List α) : Program α (List α) := do
  request (.merge (xs.length + ys.length))
  mergeCore xs ys

/-- Sort Kleinberg's constant-size base cases. -/
def sortBase : List α → Program α (List α)
  | [] => do
      request (.baseCase 0)
      pure []
  | [x] => do
      request (.baseCase 1)
      pure [x]
  | [x, y] => do
      request (.baseCase 2)
      let ordered ← request (.comparison (.le x y))
      if ordered.down then pure [x, y] else pure [y, x]
  | xs => pure xs

/--
Kleinberg's merge sort.  Unlike CSLib's original comparison-counting version, this formulation
bottoms out at size two and explicitly observes division, recombination, and every key comparison.
-/
def mergeSort (xs : List α) : Program α (List α) := do
  if xs.length ≤ 2 then
    sortBase xs
  else
    request (.split xs.length)
    let half := xs.length / 2
    let left := xs.take half
    let right := xs.drop half
    let sortedLeft ← mergeSort left
    let sortedRight ← mergeSort right
    merge sortedLeft sortedRight
termination_by xs.length
decreasing_by
  all_goals simp_wf
  · have : 0 < xs.length / 2 := by omega
    simpa only [List.length_take, Nat.min_eq_left (Nat.div_le_self xs.length 2)] using
      (Nat.div_lt_self (by omega : 0 < xs.length) (by omega : 1 < 2))
  · have : 0 < xs.length / 2 := by omega
    omega

end KleinbergMergeSort
