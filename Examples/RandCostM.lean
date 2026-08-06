/-
Copyright (c) 2026 James Needham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Needham
-/

module

public import ResourceAware.Program.RandCostM
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Tactic

/-!
# Initial tests for `RandCostM`

This file exercises five increasingly substantial examples:

1. a fair coin with branch-dependent costs;
2. randomized search without replacement on three positions;
3. the two random choices used by Fisher--Yates on three elements;
4. random-pivot quicksort on three distinct elements;
5. random-pivot quickselect for the minimum of three distinct elements.
-/

@[expose] public section

namespace CslibTests.RandCostM

universe u v

open ResourceAware.Program
open ResourceAware.Program.RandCostM

noncomputable section

/-- Two independent uniform samples form the uniform distribution on the product. -/
private theorem uniform_prod {α β : Type u}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] :
    (do
      let a ← PMF.uniformOfFintype α
      let b ← PMF.uniformOfFintype β
      PMF.pure (a, b)) =
      PMF.uniformOfFintype (α × β) := by
  classical
  ext p
  rcases p with ⟨a, b⟩

  change
    ((PMF.uniformOfFintype α).bind fun a' =>
      (PMF.uniformOfFintype β).bind fun b' =>
        PMF.pure (a', b')) (a, b) =
      (PMF.uniformOfFintype (α × β)) (a, b)

  simp only [
    PMF.bind_apply,
    PMF.uniformOfFintype_apply,
    PMF.pure_apply,
    Prod.mk.injEq,
    mul_ite,
    mul_one,
    mul_zero,
    Fintype.card_prod,
    Nat.cast_mul
  ]

  have inner_sum (a₁ : α) :
      (∑' a₂ : β,
        if a = a₁ ∧ b = a₂ then
          (↑(Fintype.card β) : ENNReal)⁻¹
        else
          0)
        =
      if a = a₁ then
        (↑(Fintype.card β) : ENNReal)⁻¹
      else
        0 := by
    by_cases h : a = a₁
    · subst a₁
      simp
    · simp [h]

  calc
    (∑' a₁ : α,
        (↑(Fintype.card α) : ENNReal)⁻¹ *
          ∑' a₂ : β,
            if a = a₁ ∧ b = a₂ then
              (↑(Fintype.card β) : ENNReal)⁻¹
            else
              0)
        =
      ∑' a₁ : α,
        (↑(Fintype.card α) : ENNReal)⁻¹ *
          if a = a₁ then
            (↑(Fintype.card β) : ENNReal)⁻¹
          else
            0 := by
          apply tsum_congr
          intro a₁
          rw [inner_sum a₁]

    _ =
      (↑(Fintype.card α) : ENNReal)⁻¹ *
        (↑(Fintype.card β) : ENNReal)⁻¹ := by
          simp

    _ =
      (↑(Fintype.card α) * ↑(Fintype.card β) : ENNReal)⁻¹ := by
      exact (ENNReal.mul_inv
        (a := (↑(Fintype.card α) : ENNReal))
        (b := (↑(Fintype.card β) : ENNReal))
        (by simp)
        (by simp)).symm

/-- A bijection transports a uniform finite distribution to a uniform distribution. -/
private theorem map_uniform_of_bijective {α : Type u} {β : Type v}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (f : α → β) (hf : Function.Bijective f) :
    PMF.map f (PMF.uniformOfFintype α) =
      PMF.uniformOfFintype β := by
  classical
  ext b

  simp only [
    PMF.map_apply,
    PMF.uniformOfFintype_apply
  ]

  rw [Fintype.card_of_bijective hf]

  obtain ⟨a, ha⟩ := hf.2 b

  calc
    (∑' x : α,
        if b = f x then
          (↑(Fintype.card β) : ENNReal)⁻¹
        else
          0)
        =
      ∑' x : α,
        if x = a then
          (↑(Fintype.card β) : ENNReal)⁻¹
        else
          0 := by
      apply tsum_congr
      intro x
      by_cases hxa : x = a
      · subst x
        simp [ha]
      · have hbx : b ≠ f x := by
          intro h
          apply hxa
          apply hf.1
          calc
            f x = b := h.symm
            _ = f a := ha.symm
        simp [hxa, hbx]

    _ = (↑(Fintype.card β) : ENNReal)⁻¹ := by
      simp

/-- Fixed-cost sampling has that same fixed expected cost. -/
@[simp] private theorem expectedCost_sampleAtCost_test
    (p : PMF α) (c : ℕ) :
    (sampleAtCost p c).expectedCost = (c : ENNReal) := by
  simp [sampleAtCost]

/-! ## Test 1: branch-dependent cost after a fair coin -/

/-- The fair distribution on booleans. -/
def fairCoin : PMF Bool :=
  PMF.uniformOfFintype Bool

/-- The `true` branch costs one unit; the `false` branch costs three. -/
def coinCost : Bool → ℕ
  | true => 1
  | false => 3

/-- A fair coin whose two outcomes carry different costs. -/
def coinBranch : RandCostM ℕ Bool :=
  sampleWithCost fairCoin coinCost

@[simp] theorem coinBranch_ret :
    coinBranch.ret = fairCoin := by
  simp [coinBranch]

@[simp] theorem coinBranch_time :
    coinBranch.time = fairCoin.map coinCost := by
  simp [coinBranch]

/-- The exact expected cost is `(1 + 3) / 2 = 2`. -/
theorem coinBranch_expectedCost :
    coinBranch.expectedCost = 2 := by
  simp only [coinBranch, expectedCost_sampleWithCost]
  norm_num [weightedSum, fairCoin, coinCost,
    PMF.uniformOfFintype_apply, tsum_fintype, Fintype.sum_bool]

  calc
    (2 : ENNReal)⁻¹ + 2⁻¹ * 3
        = (2⁻¹ + 2⁻¹) + (2⁻¹ + 2⁻¹) := by
            ring
    _ = 1 + 1 := by
          simp only [ENNReal.inv_two_add_inv_two]
    _ = 2 := by
          norm_num

/-! ## Test 2: randomized search without replacement -/

/-- A target's rank in a uniformly random ordering of three positions. -/
def uniformFin3 : PMF (Fin 3) :=
  PMF.uniformOfFintype (Fin 3)

/-- A zero-based rank `i` requires `i + 1` probes. -/
def probeCount (i : Fin 3) : ℕ :=
  i.val + 1

/--
Search a three-element collection in a uniformly random order.

For one fixed target, its rank in a uniformly random permutation is uniform on
`Fin 3`; attaching cost `rank + 1` therefore exactly models the number of
probes.  The algorithm always returns `PUnit.unit` because the unique target is
always eventually found.
-/
def searchWithoutReplacement3 : RandCostM ℕ PUnit :=
  (fun _ : Fin 3 => PUnit.unit) <$>
    sampleWithCost uniformFin3 probeCount

@[simp] theorem searchWithoutReplacement3_ret :
    searchWithoutReplacement3.ret = PMF.pure PUnit.unit := by
  simp only [searchWithoutReplacement3, ret_map, ret_sampleWithCost]
  change PMF.map (Function.const (Fin 3) PUnit.unit) uniformFin3 =
    PMF.pure PUnit.unit
  exact PMF.map_const uniformFin3 PUnit.unit

@[simp] theorem searchWithoutReplacement3_time :
    searchWithoutReplacement3.time = uniformFin3.map probeCount := by
  simp [searchWithoutReplacement3]

/-- The probe count is uniform on `1, 2, 3`, hence has expectation `2`. -/
theorem searchWithoutReplacement3_expectedCost :
    searchWithoutReplacement3.expectedCost = 2 := by
  simp only [searchWithoutReplacement3, expectedCost_map,
    expectedCost_sampleWithCost]
  norm_num [weightedSum, uniformFin3, probeCount,
    PMF.uniformOfFintype_apply, tsum_fintype, Fin.sum_univ_succ]

  calc
    (3 : ENNReal)⁻¹ +
        ((3 : ENNReal)⁻¹ * 2 + (3 : ENNReal)⁻¹ * 3)
        =
      ((3 : ENNReal)⁻¹ + (3 : ENNReal)⁻¹ + (3 : ENNReal)⁻¹) +
      ((3 : ENNReal)⁻¹ + (3 : ENNReal)⁻¹ + (3 : ENNReal)⁻¹) := by
        ring
    _ = 1 + 1 := by
      rw [ENNReal.inv_three_add_inv_three]
    _ = 2 := by
      norm_num

/-! ## Test 3: Fisher--Yates on three elements -/

/-- The second Fisher--Yates choice has two possible indices. -/
def uniformFin2 : PMF (Fin 2) :=
  PMF.uniformOfFintype (Fin 2)

/--
The two random indices used by descending Fisher--Yates on three elements:
first an index in `Fin 3`, then an index in `Fin 2`.
-/
abbrev Shuffle3Seed := Fin 3 × Fin 2

/-- The six permutations produced by Fisher--Yates on three elements. -/
inductive Perm3
  | p120
  | p210
  | p201
  | p021
  | p102
  | p012
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- Decode the two Fisher--Yates random choices into the resulting permutation. -/
def seedToPerm3 (s : Shuffle3Seed) : Perm3 :=
  if s.1 = 0 then
    if s.2 = 0 then .p120 else .p210
  else if s.1 = 1 then
    if s.2 = 0 then .p201 else .p021
  else
    if s.2 = 0 then .p102 else .p012

private theorem seedToPerm3_bijective :
    Function.Bijective seedToPerm3 := by
  constructor
  · rintro ⟨i, j⟩ ⟨i', j'⟩ h
    fin_cases i <;> fin_cases j <;>
      fin_cases i' <;> fin_cases j' <;>
      simp [seedToPerm3] at h ⊢
  · intro σ
    cases σ with
    | p120 => exact ⟨(0, 0), by simp [seedToPerm3]⟩
    | p210 => exact ⟨(0, 1), by simp [seedToPerm3]⟩
    | p201 => exact ⟨(1, 0), by simp [seedToPerm3]⟩
    | p021 => exact ⟨(1, 1), by simp [seedToPerm3]⟩
    | p102 => exact ⟨(2, 0), by simp [seedToPerm3]⟩
    | p012 => exact ⟨(2, 1), by simp [seedToPerm3]⟩

/--
Generate the two Fisher--Yates indices sequentially, charging one unit for each
random choice.
-/
def fisherYates3Seed : RandCostM ℕ Shuffle3Seed := do
  let i ← sampleAtCost uniformFin3 1
  let j ← sampleAtCost uniformFin2 1
  pure (i, j)

/-- Decode the random seed into one of the six permutations. -/
def fisherYates3 : RandCostM ℕ Perm3 :=
  seedToPerm3 <$> fisherYates3Seed

/-- The sequential choices produce the uniform distribution on all six seeds. -/
@[simp] theorem fisherYates3Seed_ret :
    fisherYates3Seed.ret = PMF.uniformOfFintype Shuffle3Seed := by
  simp only [
    fisherYates3Seed,
    ret_bind,
    ret_sampleAtCost,
    ret_pure
  ]

  unfold uniformFin3 uniformFin2

  change
    ((PMF.uniformOfFintype (Fin 3)).bind fun i =>
      (PMF.uniformOfFintype (Fin 2)).bind fun j =>
        PMF.pure (i, j)) =
      PMF.uniformOfFintype (Fin 3 × Fin 2)

  exact uniform_prod (α := Fin 3) (β := Fin 2)

/-- Fisher--Yates therefore produces each of the six permutations uniformly. -/
@[simp] theorem fisherYates3_ret :
    fisherYates3.ret = PMF.uniformOfFintype Perm3 := by
  rw [fisherYates3, ret_map, fisherYates3Seed_ret]
  exact map_uniform_of_bijective seedToPerm3 seedToPerm3_bijective

/-- Two random choices, each charged one unit, have total expected cost two. -/
@[simp] theorem fisherYates3Seed_expectedCost :
    fisherYates3Seed.expectedCost = 2 := by
  simp [fisherYates3Seed, expectedCost_bind_split]
  norm_num


/-- Decoding the seed does not alter the cost. -/
@[simp] theorem fisherYates3_expectedCost :
    fisherYates3.expectedCost = 2 := by
  simp [fisherYates3]


/-! ## Test 4: random-pivot quicksort on three elements -/

/--
After the first partition of three distinct elements, random-pivot quicksort
has one further comparison exactly when the pivot is an endpoint.  Choosing
the middle pivot leaves two singleton subproblems and therefore incurs no
further comparison.
-/
def quicksort3RemainingCost (pivot : Fin 3) : ℕ :=
  if pivot = 1 then 0 else 1

/--
The cost-relevant trace of random-pivot quicksort on a fixed three-element
input.

The first partition compares the pivot with the other two elements and is
charged cost `2`.  The deterministic continuation summarizes the only
possible recursive work: an endpoint pivot leaves a two-element subproblem,
whose sort costs one additional comparison.
-/
def randomPivotQuicksort3Trace : RandCostM ℕ (Fin 3) := do
  let pivot ← sampleAtCost uniformFin3 2
  deterministic pivot (quicksort3RemainingCost pivot)

/--
The corresponding sorting computation.  Regardless of the sampled pivot, the
fixed three-element input is returned in sorted order.
-/
def randomPivotQuicksort3 : RandCostM ℕ Perm3 :=
  (fun _ : Fin 3 => Perm3.p012) <$> randomPivotQuicksort3Trace

/-- Adding the recursive comparison cost does not change the pivot distribution. -/
@[simp] theorem randomPivotQuicksort3Trace_ret :
    randomPivotQuicksort3Trace.ret = uniformFin3 := by
  simp [randomPivotQuicksort3Trace]

/-- Random-pivot quicksort returns the sorted permutation with probability one. -/
@[simp] theorem randomPivotQuicksort3_ret :
    randomPivotQuicksort3.ret = PMF.pure Perm3.p012 := by
  rw [randomPivotQuicksort3, ret_map]
  change
    PMF.map (Function.const (Fin 3) Perm3.p012)
        randomPivotQuicksort3Trace.ret =
      PMF.pure Perm3.p012
  exact PMF.map_const randomPivotQuicksort3Trace.ret Perm3.p012

/--
The expected comparison count is

`2 + (1 / 3 + 1 / 3) = 8 / 3`:

the first partition always costs two, and either endpoint pivot produces one
additional comparison.
-/
@[simp] theorem randomPivotQuicksort3Trace_expectedCost :
    randomPivotQuicksort3Trace.expectedCost =
      2 + ((3 : ENNReal)⁻¹ + (3 : ENNReal)⁻¹) := by
  simp only [
    randomPivotQuicksort3Trace,
    expectedCost_bind_split,
    expectedCost_sampleAtCost_test,
    ret_sampleAtCost,
    expectedCost_deterministic
  ]
  norm_num [
    weightedSum,
    uniformFin3,
    quicksort3RemainingCost,
    PMF.uniformOfFintype_apply,
    tsum_fintype,
    Fin.sum_univ_succ
  ] <;> ring
  trivial

/-- Mapping the trace to the sorted output does not change its expected cost. -/
@[simp] theorem randomPivotQuicksort3_expectedCost :
    randomPivotQuicksort3.expectedCost =
      2 + ((3 : ENNReal)⁻¹ + (3 : ENNReal)⁻¹) := by
  simpa [randomPivotQuicksort3] using
    randomPivotQuicksort3Trace_expectedCost

/-! ## Test 5: random-pivot quickselect on three elements -/

/--
When selecting the minimum of three distinct elements, a pivot of rank `0`
finds the answer immediately, and a pivot of rank `1` leaves only a singleton
left subproblem.  A pivot of rank `2` alone leaves a two-element subproblem,
which requires one additional comparison.
-/
def quickselect3MinRemainingCost (pivot : Fin 3) : ℕ :=
  if pivot = 2 then 1 else 0

/--
The cost-relevant trace of random-pivot quickselect for the minimum of a fixed
three-element input.

The initial partition always costs two comparisons.  The continuation cost
depends on the sampled pivot rank and represents the recursively selected
subproblem.
-/
def randomPivotQuickselect3MinTrace : RandCostM ℕ (Fin 3) := do
  let pivot ← sampleAtCost uniformFin3 2
  deterministic pivot (quickselect3MinRemainingCost pivot)

/-- The quickselect computation always returns the minimum, represented by rank `0`. -/
def randomPivotQuickselect3Min : RandCostM ℕ (Fin 3) :=
  (fun _ : Fin 3 => (0 : Fin 3)) <$> randomPivotQuickselect3MinTrace

/-- Cost instrumentation does not change the first-pivot distribution. -/
@[simp] theorem randomPivotQuickselect3MinTrace_ret :
    randomPivotQuickselect3MinTrace.ret = uniformFin3 := by
  simp [randomPivotQuickselect3MinTrace]

/-- Quickselect returns the minimum with probability one. -/
@[simp] theorem randomPivotQuickselect3Min_ret :
    randomPivotQuickselect3Min.ret = PMF.pure (0 : Fin 3) := by
  rw [randomPivotQuickselect3Min, ret_map]
  change
    PMF.map (Function.const (Fin 3) (0 : Fin 3))
        randomPivotQuickselect3MinTrace.ret =
      PMF.pure (0 : Fin 3)
  exact PMF.map_const randomPivotQuickselect3MinTrace.ret (0 : Fin 3)

/--
The expected comparison count is

`2 + 1 / 3 = 7 / 3`:

only the largest first pivot leaves a nontrivial recursive subproblem.
-/
@[simp] theorem randomPivotQuickselect3MinTrace_expectedCost :
    randomPivotQuickselect3MinTrace.expectedCost =
      2 + (3 : ENNReal)⁻¹ := by
  simp only [
    randomPivotQuickselect3MinTrace,
    expectedCost_bind_split,
    expectedCost_sampleAtCost_test,
    ret_sampleAtCost,
    expectedCost_deterministic
  ]
  norm_num [
    weightedSum,
    uniformFin3,
    quickselect3MinRemainingCost,
    PMF.uniformOfFintype_apply,
    tsum_fintype,
    Fin.sum_univ_succ
  ] <;> ring

/-- Mapping the trace to the selected minimum does not change expected cost. -/
@[simp] theorem randomPivotQuickselect3Min_expectedCost :
    randomPivotQuickselect3Min.expectedCost =
      2 + (3 : ENNReal)⁻¹ := by
  simpa [randomPivotQuickselect3Min] using
    randomPivotQuickselect3MinTrace_expectedCost

end

end CslibTests.RandCostM
