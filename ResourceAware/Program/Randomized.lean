/-
Copyright (c) 2026 James Needham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Needham
-/

import ResourceAware.Program.RandCostM
import Cslib.Algorithms.Lean.TimeM
import ResourceAware.Program.Model
import Mathlib.Probability.Distributions.Uniform

/-!
# Randomized abstract-program interpreters

This module folds a polynomial free program into either ordinary probabilistic semantics or
probabilistic cost semantics. The free program remains independent of both targets: in particular,
`RandCostM` is an interpreter target and is not used to define an algorithm's control flow.

The result-erasure theorem lifts an operationwise agreement between a probabilistic handler and a
cost-annotated handler to every complete free program.
-/

namespace ResourceAware.Program

open Cslib.Algorithms.Lean

universe u v

noncomputable section

/-- Interpret a free program using probabilistic operation semantics. -/
def evalPMF {signature : Signature.{u, u}} {alpha : Type u}
    (handler : (operation : signature.A) -> PMF (signature.B operation))
    (program : Free signature alpha) : PMF alpha :=
  program.liftM handler

/-- Interpret a free program using branch-specific probabilistic cost semantics. -/
def runRandCost {signature : Signature.{u, u}} {T : Type v} [AddMonoid T]
    {alpha : Type u}
    (handler : (operation : signature.A) -> RandCostM T (signature.B operation))
    (program : Free signature alpha) : RandCostM T alpha :=
  program.liftM handler

/-- Embed one deterministic cost computation as a singleton randomized branch. -/
def deterministicRandCost {T : Type v} {alpha : Type u}
    (computation : TimeM T alpha) : RandCostM T alpha :=
  RandCostM.deterministic computation.ret computation.time

/-- Interpret a free program using deterministic `TimeM` operation semantics. -/
def runTime {signature : Signature.{u, u}} {T : Type v} [AddMonoid T]
    {alpha : Type u}
    (handler : (operation : signature.A) -> TimeM T (signature.B operation))
    (program : Free signature alpha) : TimeM T alpha :=
  program.liftM handler

@[simp] theorem deterministicRandCost_pure {T : Type v} [AddMonoid T]
    {alpha : Type u} (value : alpha) :
    deterministicRandCost (pure value : TimeM T alpha) =
      (pure value : RandCostM T alpha) :=
  rfl

@[simp] theorem deterministicRandCost_bind {T : Type v} [AddMonoid T]
    {alpha beta : Type u} (computation : TimeM T alpha)
    (next : alpha -> TimeM T beta) :
    deterministicRandCost (computation >>= next) =
      (deterministicRandCost computation >>= fun value =>
        deterministicRandCost (next value)) := by
  apply RandCostM.ext
  simp [deterministicRandCost, RandCostM.deterministic]

/-- Folding deterministic operation costs into `RandCostM` produces one branch matching `TimeM`. -/
theorem runRandCost_deterministic_eq_runTime
    {signature : Signature.{u, u}} {T : Type v} [AddMonoid T]
    {alpha : Type u}
    (handler : (operation : signature.A) -> TimeM T (signature.B operation))
    (program : Free signature alpha) :
    runRandCost (fun operation => deterministicRandCost (handler operation)) program =
      deterministicRandCost (runTime handler program) := by
  induction program with
  | pure value => rfl
  | liftBind operation next ih =>
      simp only [runRandCost, runTime, PFunctor.FreeM.liftM]
      rw [deterministicRandCost_bind]
      congr
      funext response
      exact ih response

@[simp] theorem evalPMF_pure {signature : Signature.{u, u}} {alpha : Type u}
    (handler : (operation : signature.A) -> PMF (signature.B operation)) (value : alpha) :
    evalPMF handler (pure value) = PMF.pure value :=
  rfl

@[simp] theorem evalPMF_request {signature : Signature.{u, u}}
    (handler : (operation : signature.A) -> PMF (signature.B operation))
    (operation : signature.A) :
    evalPMF handler (request operation) = handler operation := by
  simp [evalPMF, request]

@[simp] theorem evalPMF_bind {signature : Signature.{u, u}} {alpha beta : Type u}
    (handler : (operation : signature.A) -> PMF (signature.B operation))
    (program : Free signature alpha) (next : alpha -> Free signature beta) :
    evalPMF handler (program >>= next) =
      (evalPMF handler program >>= fun value => evalPMF handler (next value)) := by
  exact PFunctor.FreeM.liftM_bind handler program next

@[simp] theorem runRandCost_pure {signature : Signature.{u, u}} {T : Type v}
    [AddMonoid T] {alpha : Type u}
    (handler : (operation : signature.A) -> RandCostM T (signature.B operation))
    (value : alpha) :
    runRandCost handler (pure value) = pure value :=
  rfl

@[simp] theorem runRandCost_request {signature : Signature.{u, u}} {T : Type v}
    [AddMonoid T]
    (handler : (operation : signature.A) -> RandCostM T (signature.B operation))
    (operation : signature.A) :
    runRandCost handler (request operation) = handler operation := by
  simp [runRandCost, request]

@[simp] theorem runRandCost_bind {signature : Signature.{u, u}} {T : Type v}
    [AddMonoid T] {alpha beta : Type u}
    (handler : (operation : signature.A) -> RandCostM T (signature.B operation))
    (program : Free signature alpha) (next : alpha -> Free signature beta) :
    runRandCost handler (program >>= next) =
      (runRandCost handler program >>= fun value => runRandCost handler (next value)) := by
  exact PFunctor.FreeM.liftM_bind handler program next

/-- If cost erasure agrees with a probabilistic handler for every operation, it agrees after
interpreting any complete free program. -/
theorem ret_runRandCost_eq_evalPMF {signature : Signature.{u, u}} {T : Type v}
    [AddMonoid T] {alpha : Type u}
    (semanticHandler : (operation : signature.A) -> PMF (signature.B operation))
    (measuredHandler : (operation : signature.A) -> RandCostM T (signature.B operation))
    (handler_ret : forall operation, (measuredHandler operation).ret = semanticHandler operation)
    (program : Free signature alpha) :
    (runRandCost measuredHandler program).ret = evalPMF semanticHandler program := by
  induction program with
  | pure value => simp
  | liftBind operation next ih =>
      simp only [PFunctor.FreeM.liftM, runRandCost, evalPMF, RandCostM.ret_bind]
      rw [handler_ret]
      congr 1
      funext response
      exact ih response

/-- Expectation under a uniform distribution on a nonempty finite type is its finite average. -/
theorem weightedSum_uniformOfFintype {index : Type u} [Fintype index] [Nonempty index]
    (weight : index -> ENNReal) :
    RandCostM.weightedSum (PMF.uniformOfFintype index) weight =
      (Fintype.card index : ENNReal)⁻¹ * Finset.univ.sum weight := by
  classical
  simp [RandCostM.weightedSum, PMF.uniformOfFintype_apply, tsum_fintype,
    Finset.mul_sum]

end
end ResourceAware.Program
