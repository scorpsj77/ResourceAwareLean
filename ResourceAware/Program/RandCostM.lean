/-
Copyright (c) 2026 James Needham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Needham
-/

module

public import Cslib.Init
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# RandCostM: probabilistic cost semantics

`RandCostM T α` is a probability mass function on result-cost pairs `α × T`.
An outcome `(a, c)` means that one execution returns `a` and incurs cost `c`.

The cost assumptions are staged in the same way as `TimeM`:

* `pure` needs `Zero T`, because returning a value has cost `0`;
* `bind` needs `Add T`, because sequential costs are added pathwise;
* the lawful monad instance needs `AddMonoid T`.

The joint distribution is essential.  A value of type `PMF α × PMF T` would
forget correlations between the returned result and the incurred cost.
-/

@[expose] public section

namespace ResourceAware.Program

universe u v w

/-- A discrete probabilistic computation carrying a cost on every execution branch. -/
@[ext]
structure RandCostM (T : Type*) (α : Type*) where
  /-- The joint probability distribution of return values and costs. -/
  joint : PMF (α × T)

namespace RandCostM

noncomputable section

/-! ## Monad structure -/

/-- Return `a` with probability `1` and cost `0`.

Prefer the ordinary `pure` notation. -/
protected def pure [Zero T] {α : Type*} (a : α) : RandCostM T α :=
  ⟨PMF.pure (a, 0)⟩

@[implicit_reducible] instance [Zero T] : Pure (RandCostM T) where
  pure := RandCostM.pure

/-- Sequentially compose probabilistic cost computations.

First sample `(a, c₁)` from `m`, then sample `(b, c₂)` from `f a`, and
return `(b, c₁ + c₂)`.  Cost is therefore accumulated separately on each
probabilistic execution branch. -/
protected def bind {α β : Type u} [Add T]
    (m : RandCostM T α) (f : α → RandCostM T β) : RandCostM T β :=
  ⟨m.joint.bind fun x =>
      (f x.1).joint.bind fun y =>
        PMF.pure (y.1, x.2 + y.2)⟩

@[implicit_reducible] instance [Add T] : Bind (RandCostM T) where
  bind := RandCostM.bind

/-- Map the return value while leaving every branch cost unchanged. -/
protected def map {α β : Type u} (f : α → β) (m : RandCostM T α) : RandCostM T β :=
  ⟨m.joint.map fun x => (f x.1, x.2)⟩

@[implicit_reducible] instance : Functor (RandCostM T) where
  map := RandCostM.map

/-- The remaining applicative operations use Lean's standard monadic defaults. -/
@[implicit_reducible] instance [AddZero T] : Monad (RandCostM T) where
  pure := Pure.pure
  bind := Bind.bind
  map := Functor.map

@[simp, grind =] theorem joint_pure {α : Type*} [Zero T] (a : α) :
    (pure a : RandCostM T α).joint = PMF.pure (a, 0) := rfl

@[simp, grind =] theorem joint_bind {α β : Type u} [Add T]
    (m : RandCostM T α) (f : α → RandCostM T β) :
    (m >>= f).joint =
      m.joint.bind fun x =>
        (f x.1).joint.bind fun y =>
          PMF.pure (y.1, x.2 + y.2) := rfl

@[simp, grind =] theorem joint_map {α β : Type u} (f : α → β) (m : RandCostM T α) :
    (f <$> m).joint = m.joint.map fun x => (f x.1, x.2) := rfl

/-- `RandCostM` is lawful when branch costs form an additive monoid. -/
instance [AddMonoid T] : LawfulMonad (RandCostM T) := .mk'
  (id_map := fun m => by
    apply RandCostM.ext
    change m.joint.map (fun x => (id x.1, x.2)) = m.joint
    rw [show (fun x : _ => (id x.1, x.2)) = id by
      funext x
      exact Prod.eta x]
    exact PMF.map_id m.joint)
  (pure_bind := fun a f => by
    apply RandCostM.ext
    change (PMF.pure (a, 0)).bind
      (fun x =>
        (f x.1).joint.bind fun y =>
          PMF.pure (y.1, x.2 + y.2)) =
      (f a).joint
    rw [PMF.pure_bind]
    simpa only [zero_add, Prod.eta] using
      PMF.bind_pure (f a).joint)
  (bind_assoc := fun m f g => by
    apply RandCostM.ext
    simp only [
      joint_bind,
      PMF.bind_bind,
      PMF.pure_bind,
      add_assoc
    ])
    (bind_pure_comp := fun {α β} g x => by
    apply RandCostM.ext
    simp only [joint_bind, joint_pure, joint_map, PMF.pure_bind, add_zero]
    change
      x.joint.bind
          (PMF.pure ∘
            (fun z : α × T => (g z.1, z.2))) =
        PMF.map
          (fun z : α × T => (g z.1, z.2))
          x.joint
    exact PMF.bind_pure_comp
      (fun z : α × T => (g z.1, z.2))
      x.joint)

/-! ## Marginal distributions -/

/-- The marginal distribution of return values, obtained by erasing costs. -/
def ret (m : RandCostM T α) : PMF α :=
  m.joint.map Prod.fst

/-- The marginal distribution of costs, obtained by erasing return values. -/
def time (m : RandCostM T α) : PMF T :=
  m.joint.map Prod.snd

/-- A descriptive alias for `ret`. -/
abbrev resultDist (m : RandCostM T α) : PMF α := m.ret

/-- A descriptive alias for `time`. -/
abbrev costDist (m : RandCostM T α) : PMF T := m.time

/-- A descriptive alias emphasizing that `ret` erases the cost annotation. -/
abbrev eraseCost (m : RandCostM T α) : PMF α := m.ret

@[simp, grind =] theorem ret_pure {α : Type*} [Zero T] (a : α) :
    (pure a : RandCostM T α).ret = PMF.pure a := by
  simp [ret, PMF.pure_map]

@[simp, grind =] theorem time_pure {α : Type*} [Zero T] (a : α) :
    (pure a : RandCostM T α).time = PMF.pure 0 := by
  simp [time, PMF.pure_map]

@[simp, grind =] theorem ret_map {α β : Type u} (f : α → β) (m : RandCostM T α) :
    (f <$> m).ret = m.ret.map f := by
  simp [ret, PMF.map_comp, Function.comp_def]

@[simp, grind =] theorem time_map {α β : Type u} (f : α → β) (m : RandCostM T α) :
    (f <$> m).time = m.time := by
  simp [time, PMF.map_comp, Function.comp_def]

/-- Erasing costs commutes with bind.

This is the central behavioral-erasure theorem: interpreting a program in
`RandCostM` and then forgetting cost gives the same probabilistic sequencing
as interpreting its operations directly in `PMF`. -/
@[simp] theorem ret_bind {α β : Type u} [Add T]
    (m : RandCostM T α) (f : α → RandCostM T β) :
    (m >>= f).ret = m.ret.bind fun a => (f a).ret := by
  simp [ret, PMF.map, Function.comp_def]

/-- The cost marginal of bind.

The first computation's result and cost remain joint because the continuation
cost distribution may depend on the sampled result. -/
@[simp] theorem time_bind {α β : Type u} [Add T]
    (m : RandCostM T α) (f : α → RandCostM T β) :
    (m >>= f).time =
      m.joint.bind fun x =>
        (f x.1).time.map fun c₂ => x.2 + c₂ := by
  simp [time, PMF.map, Function.comp_def]

/-! ## Primitive constructors -/

/-- Return `a` deterministically at exactly cost `c`. -/
def deterministic (a : α) (c : T) : RandCostM T α :=
  ⟨PMF.pure (a, c)⟩

@[simp] theorem joint_deterministic (a : α) (c : T) :
    (deterministic a c).joint = PMF.pure (a, c) := rfl

@[simp] theorem ret_deterministic (a : α) (c : T) :
    (deterministic a c).ret = PMF.pure a := by
  simp [ret, deterministic, PMF.pure_map]

@[simp] theorem time_deterministic (a : α) (c : T) :
    (deterministic a c).time = PMF.pure c := by
  simp [time, deterministic, PMF.pure_map]

@[simp] theorem pure_eq_deterministic [Zero T] (a : α) :
    (pure a : RandCostM T α) = deterministic a 0 := rfl

/-- Sample `a` from `p` and attach the branch-dependent cost `cost a`. -/
def sampleWithCost (p : PMF α) (cost : α → T) : RandCostM T α :=
  ⟨p.map fun a => (a, cost a)⟩

@[simp] theorem joint_sampleWithCost (p : PMF α) (cost : α → T) :
    (sampleWithCost p cost).joint = p.map fun a => (a, cost a) := rfl

@[simp] theorem ret_sampleWithCost (p : PMF α) (cost : α → T) :
    (sampleWithCost p cost).ret = p := by
  simp only [ret, sampleWithCost, PMF.map_comp]
  change p.map id = p
  exact PMF.map_id p

@[simp] theorem time_sampleWithCost (p : PMF α) (cost : α → T) :
    (sampleWithCost p cost).time = p.map cost := by
  simp only [time, sampleWithCost, PMF.map_comp]
  rfl

/-- Sample from `p`, charging the same cost `c` on every branch. -/
def sampleAtCost (p : PMF α) (c : T) : RandCostM T α :=
  sampleWithCost p fun _ => c

@[simp] theorem ret_sampleAtCost (p : PMF α) (c : T) :
    (sampleAtCost p c).ret = p := by
  simp [sampleAtCost]

@[simp] theorem time_sampleAtCost (p : PMF α) (c : T) :
    (sampleAtCost p c).time = PMF.pure c := by
  rw [sampleAtCost, time_sampleWithCost]
  exact PMF.map_const p c

/-- Lift an ordinary probability mass function without charging cost. -/
def sample [Zero T] (p : PMF α) : RandCostM T α :=
  sampleAtCost p 0

@[simp] theorem joint_sample [Zero T] (p : PMF α) :
    (sample p : RandCostM T α).joint = p.map fun a => (a, 0) := rfl

@[simp] theorem ret_sample [Zero T] (p : PMF α) :
    (sample p : RandCostM T α).ret = p := by
  simp [sample]

@[simp] theorem time_sample [Zero T] (p : PMF α) :
    (sample p : RandCostM T α).time = PMF.pure 0 := by
  simp [sample]

@[simp] theorem sample_pure [Zero T] (a : α) :
    sample (PMF.pure a) = (pure a : RandCostM T α) := by
  apply RandCostM.ext
  simp [sample, sampleAtCost, sampleWithCost, PMF.pure_map]

/-- Zero-cost sampling preserves probabilistic bind. Thus `sample` is a
monad morphism from `PMF` into `RandCostM T`. -/
@[simp] theorem sample_bind [AddMonoid T] {α β : Type u}
    (p : PMF α) (f : α → PMF β) :
    sample (p.bind f) =
      (sample p >>= fun a => sample (f a) : RandCostM T β) := by
  apply RandCostM.ext
  simp only [joint_sample, joint_bind]
  -- Rewrite the left side:
  -- map zeroCost (p.bind f)
  --   = p.bind (fun a => map zeroCost (f a)).
  rw [PMF.map_bind p f (fun b : β => (b, 0))]
  -- Rewrite only the outer mapped bind on the right side.
  rw [PMF.bind_map p (fun a : α => (a, 0))]
  -- Both sides now bind `p`; compare their continuations pointwise.
  refine congrArg (fun k : α → PMF (β × T) => p.bind k) ?_
  funext a
  change
    PMF.map (fun b : β => (b, 0)) (f a) =
      (PMF.map (fun b : β => (b, 0)) (f a)).bind
        (fun y : β × T => PMF.pure (y.1, 0 + y.2))
  simpa only [zero_add, Prod.eta] using
    (PMF.bind_pure
      (PMF.map (fun b : β => (b, 0)) (f a))).symm

/-- Charge exactly `c` and return `PUnit`. -/
def tick (c : T) : RandCostM T PUnit :=
  deterministic .unit c

@[simp, grind =] theorem joint_tick (c : T) :
    (tick c).joint = PMF.pure (PUnit.unit, c) := rfl

@[simp, grind =] theorem ret_tick (c : T) :
    (tick c).ret = PMF.pure PUnit.unit := by
  simp [tick]

@[simp, grind =] theorem time_tick (c : T) :
    (tick c).time = PMF.pure c := by
  simp [tick]

/-! ## Nonnegative expectations -/

/-- The expectation of an `ENNReal`-valued function under a `PMF`.

Extended nonnegative reals also represent infinite expectation, so this
notion needs no integrability side condition. -/
def weightedSum (p : PMF α) (f : α → ENNReal) : ENNReal :=
  ∑' a, p a * f a

@[simp] theorem weightedSum_pure (a : α) (f : α → ENNReal) :
    weightedSum (PMF.pure a) f = f a := by
  classical
  simp [weightedSum, PMF.pure_apply]

/-- The tower law for nonnegative expectations under `PMF.bind`. -/
theorem weightedSum_bind (p : PMF α) (q : α → PMF β) (f : β → ENNReal) :
    weightedSum (p.bind q) f =
      weightedSum p fun a => weightedSum (q a) f := by
  calc
    weightedSum (p.bind q) f
        = ∑' b, (∑' a, p a * q a b) * f b := by
            simp only [weightedSum, PMF.bind_apply]
    _ = ∑' b, ∑' a, (p a * q a b) * f b := by
          apply tsum_congr
          intro b
          rw [← ENNReal.tsum_mul_right]
    _ = ∑' a, ∑' b, (p a * q a b) * f b := ENNReal.tsum_comm
    _ = ∑' a, p a * ∑' b, q a b * f b := by
          apply tsum_congr
          intro a
          calc
            (∑' b, (p a * q a b) * f b)
                = ∑' b, p a * (q a b * f b) := by
                    apply tsum_congr
                    intro b
                    rw [mul_assoc]
            _ = p a * ∑' b, q a b * f b := ENNReal.tsum_mul_left
    _ = weightedSum p fun a => weightedSum (q a) f := rfl

/-- Change of variables for a pushed-forward `PMF`. -/
theorem weightedSum_map (p : PMF α) (g : α → β) (f : β → ENNReal) :
    weightedSum (p.map g) f = weightedSum p (f ∘ g) := by
  rw [← PMF.bind_pure_comp, weightedSum_bind]
  simp [Function.comp_def]

@[simp] theorem weightedSum_const (p : PMF α) (c : ENNReal) :
    weightedSum p (fun _ => c) = c := by
  rw [weightedSum, ENNReal.tsum_mul_right, p.tsum_coe, one_mul]

/-- Linearity of nonnegative expectation over addition. -/
theorem weightedSum_add (p : PMF α) (f g : α → ENNReal) :
    weightedSum p (fun a => f a + g a) = weightedSum p f + weightedSum p g := by
  simp [weightedSum, mul_add, ENNReal.tsum_add]

/-! ## Expected-cost weakest preexpectations -/

/-- Monotonicity of nonnegative expectation. -/
theorem weightedSum_mono (p : PMF α) {f g : α → ENNReal}
    (h : ∀ a, f a ≤ g a) :
    weightedSum p f ≤ weightedSum p g := by
  apply ENNReal.tsum_le_tsum
  intro a
  exact mul_le_mul_right (h a) (p a)

/-- The expected-cost weakest preexpectation transformer.

For a computation whose joint result-cost distribution is `m.joint` and a
post-expectation `Φ`, `ecwp m Φ` is

`E[(a, c) ← m][c + Φ a]`.

Thus `ecwp` is an observer/proof layer on the exact `RandCostM` semantics, not
a separate monad. Extended nonnegative reals allow both the post-expectation
and the resulting expected cost to be infinite. -/
def ecwp (m : RandCostM ℕ α) (Φ : α → ENNReal) : ENNReal :=
  weightedSum m.joint fun x => (x.2 : ENNReal) + Φ x.1

@[simp] theorem ecwp_pure (a : α) (Φ : α → ENNReal) :
    ecwp (pure a : RandCostM ℕ α) Φ = Φ a := by
  simp [ecwp]

@[simp] theorem ecwp_map {α β : Type u} (f : α → β)
    (m : RandCostM ℕ α) (Φ : β → ENNReal) :
    ecwp (f <$> m) Φ = ecwp m (Φ ∘ f) := by
  simp [ecwp, weightedSum_map, Function.comp_def]

@[simp] theorem ecwp_deterministic (a : α) (c : ℕ) (Φ : α → ENNReal) :
    ecwp (deterministic a c) Φ = (c : ENNReal) + Φ a := by
  simp [ecwp, deterministic]

@[simp] theorem ecwp_sampleWithCost (p : PMF α) (cost : α → ℕ)
    (Φ : α → ENNReal) :
    ecwp (sampleWithCost p cost) Φ =
      weightedSum p fun a => (cost a : ENNReal) + Φ a := by
  simp [ecwp, sampleWithCost, weightedSum_map, Function.comp_def]

@[simp] theorem ecwp_sampleAtCost (p : PMF α) (c : ℕ)
    (Φ : α → ENNReal) :
    ecwp (sampleAtCost p c) Φ =
      weightedSum p fun a => (c : ENNReal) + Φ a := by
  simp [sampleAtCost]

@[simp] theorem ecwp_sample (p : PMF α) (Φ : α → ENNReal) :
    ecwp (sample p : RandCostM ℕ α) Φ = weightedSum p Φ := by
  simp [sample, sampleAtCost]

@[simp] theorem ecwp_tick (c : ℕ) (Φ : PUnit → ENNReal) :
    ecwp (tick c) Φ = (c : ENNReal) + Φ PUnit.unit := by
  simp [tick]

/-- The continuation-sensitive bind law for expected cost.

This is the quantitative analogue of the ordinary weakest-precondition bind
law: the post-expectation for the first stage is the expected cost of running
the continuation and then satisfying `Φ`. -/
theorem ecwp_bind {α β : Type u} (m : RandCostM ℕ α)
    (f : α → RandCostM ℕ β) (Φ : β → ENNReal) :
    ecwp (m >>= f) Φ = ecwp m (fun a => ecwp (f a) Φ) := by
  simp [ecwp, weightedSum_bind, weightedSum_add, add_assoc]

/-- `ecwp` is monotone in its post-expectation. -/
theorem ecwp_mono (m : RandCostM ℕ α) {Φ Ψ : α → ENNReal}
    (h : ∀ a, Φ a ≤ Ψ a) :
    ecwp m Φ ≤ ecwp m Ψ := by
  apply weightedSum_mono
  intro x
  exact add_le_add (le_refl (x.2 : ENNReal)) (h x.1)

/-- Local continuation bounds compose into a global expected-cost bound. -/
theorem ecwp_bind_le {α β : Type u} (m : RandCostM ℕ α)
    (f : α → RandCostM ℕ β) (Φ : β → ENNReal) (Ψ : α → ENNReal)
    (h : ∀ a, ecwp (f a) Φ ≤ Ψ a) :
    ecwp (m >>= f) Φ ≤ ecwp m Ψ := by
  rw [ecwp_bind]
  exact ecwp_mono m h

/-- Expected natural-number cost, equivalently obtained by using the zero
post-expectation in `ecwp`. It is valued in `ENNReal` so infinite expectation
is representable. -/
def expectedCost (m : RandCostM ℕ α) : ENNReal :=
  weightedSum m.joint fun x => (x.2 : ENNReal)

/-- Compatibility alias for cost models phrased as time. -/
abbrev expectedTime (m : RandCostM ℕ α) : ENNReal := m.expectedCost

/-- Expected cost is exactly `ecwp` with no remaining post-cost. -/
theorem expectedCost_eq_ecwp_zero (m : RandCostM ℕ α) :
    expectedCost m = ecwp m (fun _ => 0) := by
  simp [expectedCost, ecwp]

@[simp] theorem ecwp_zero (m : RandCostM ℕ α) :
    ecwp m (fun _ => 0) = expectedCost m :=
  (expectedCost_eq_ecwp_zero m).symm

@[simp] theorem expectedCost_pure (a : α) :
    expectedCost (pure a : RandCostM ℕ α) = 0 := by
  simp [expectedCost]

@[simp] theorem expectedCost_map {α β : Type u} (f : α → β) (m : RandCostM ℕ α) :
    expectedCost (f <$> m) = expectedCost m := by
  simp [expectedCost, weightedSum_map, Function.comp_def]

@[simp] theorem expectedCost_deterministic (a : α) (c : ℕ) :
    expectedCost (deterministic a c) = (c : ENNReal) := by
  simp [expectedCost, deterministic]

@[simp] theorem expectedCost_sampleWithCost (p : PMF α) (cost : α → ℕ) :
    expectedCost (sampleWithCost p cost) =
      weightedSum p fun a => (cost a : ENNReal) := by
  simp [expectedCost, sampleWithCost, weightedSum_map, Function.comp_def]

@[simp] theorem expectedCost_sample (p : PMF α) :
    expectedCost (sample p : RandCostM ℕ α) = 0 := by
  simp [expectedCost_sampleWithCost, sample, sampleAtCost]

@[simp] theorem expectedCost_tick (c : ℕ) :
    expectedCost (tick c) = (c : ENNReal) := by
  simp [tick]

/-- Conditional expected-cost bind law.

The outer expectation is over the first stage's joint result-cost distribution,
because the expected continuation cost may depend on the sampled result. -/
theorem expectedCost_bind {α β : Type u} (m : RandCostM ℕ α) (f : α → RandCostM ℕ β) :
    expectedCost (m >>= f) =
      weightedSum m.joint fun x =>
        (x.2 : ENNReal) + expectedCost (f x.1) := by
  simp [expectedCost, weightedSum_bind, weightedSum_add]

/-- Expected cost of sequential composition as

`E[cost of m] + E[a ← resultDist m][E[cost of f a]]`.
-/
theorem expectedCost_bind_split {α β : Type u} (m : RandCostM ℕ α) (f : α → RandCostM ℕ β) :
    expectedCost (m >>= f) =
      expectedCost m + weightedSum m.ret (fun a => expectedCost (f a)) := by
  rw [expectedCost_bind, weightedSum_add]
  change expectedCost m +
      weightedSum m.joint (fun x => expectedCost (f x.1)) =
    expectedCost m + weightedSum m.ret (fun a => expectedCost (f a))
  apply congrArg (fun z => expectedCost m + z)
  exact (weightedSum_map m.joint Prod.fst (fun a => expectedCost (f a))).symm

/-! ## The expected-cost evaluation algebra -/

/-- Collapse a random computation returning a future cost into its total
expected cost.

Categorically, this is the carrier map of an Eilenberg--Moore algebra for
`RandCostM ℕ`: it combines the cost already incurred with the returned
continuation cost. -/
def eval (m : RandCostM ℕ ENNReal) : ENNReal :=
  ecwp m id

/-- The unit law for the expected-cost evaluation algebra. -/
@[simp] theorem eval_pure (r : ENNReal) :
    eval (pure r : RandCostM ℕ ENNReal) = r := by
  simp [eval]

/-- The multiplication law for the expected-cost evaluation algebra.

Here `m >>= id` is monadic `join`: evaluating after flattening agrees with
first evaluating each inner computation and then evaluating the outer one. -/
theorem eval_join (m : RandCostM ℕ (RandCostM ℕ ENNReal)) :
    eval (m >>= id) = eval (eval <$> m) := by
  simp only [eval, ecwp_bind, id_eq, ecwp_map, CompTriple.comp_eq]
  change m.ecwp (fun a => a.ecwp id) =
    m.ecwp (fun a => a.ecwp id)
  rfl

end

end RandCostM
end ResourceAware.Program
