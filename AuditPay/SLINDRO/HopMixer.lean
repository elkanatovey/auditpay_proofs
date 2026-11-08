/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.SLINDRO.Reductions
import VCVio.EvalDist.Monad.Disagreement.Measure

/-!
# Theorem 2 with a random-oracle KDF, last hop: base-mixer unlinkability

Once both ciphertexts encrypt the dummy note under fresh keys and the proof is simulated, the
two worlds differ only in the base mixer. The reduction generates `V` itself and runs the
adversary with a lazily sampled KDF of its own.
-/

open OracleComp OracleSpec ENNReal

namespace AuditPay.SLINDRO

open KdfRO
open AuditPay.SLIND (distinct mixerExperiment mixerAdvantage)
open AuditPay.SLINDDrop (valid valid_distinct)

variable {F G Addr ρ E X Key Note DTx WCore C Proof σ : Type} {k n : ℕ}
  [Field F] [AddCommGroup G] [Module F G] [DecidableEq Addr]
  [SampleableType G] [Fintype Addr] [SampleableType Key] [SampleableType ρ] [DecidableEq X]

/-- A sample followed by a continuation that is, for every value, distributed as `my` is
distributed as `my`. -/
private theorem bind_eqd_of_forall {α β : Type} (mx : ProbComp α) (f : α → ProbComp β)
    (my : ProbComp β) (h : ∀ a, f a =ᵈ my) : (mx >>= f) =ᵈ my :=
  (EvalDistEq.bind_right mx h).trans (bind_const_eqd mx my)

/-- The base-mixer experiment run by `mixerReduction` for bit `b` is the all-dummy hybrid with
a simulated proof for bit `b`. -/
theorem mixerExperiment_eqd (S : Variant G ρ E X) (sel : Selection F Addr k n)
    (P : Params F G Addr ρ E Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr E X Key DTx WCore C Proof σ n) (b : Bool) :
    mixerExperiment P.mixer (mixerReduction S sel P A) b =ᵈ
      Prod.fst <$> hybrid S sel P A b true .dummy .dummy := by
  simp only [mixerExperiment, mixerReduction, hybrid, setup, bind_assoc, pure_bind, map_bind]
  refine EvalDistEq.bind_right _ fun H => EvalDistEq.bind_right _ fun z => ?_
  by_cases hv : valid sel P.pos P.coef z.1 = true
  · simp only [hv, valid_distinct hv, ite_true, bind_assoc, pure_bind, map_pure, tailS, tailC,
      tailR, tailD, keyQ, msg, stmt, finish, roRun_bind, roRun_liftM, bind_map_left, map_bind]
    simp only [map_eq_bind_pure_comp, Function.comp_def, EvalDistEq.refl]
  · by_cases hd : distinct z.1.d₀ z.1.d₁ z.1.wAddr = true
    · simp only [hv, hd, ite_true, ite_false, Bool.false_eq_true, pure_bind, map_pure]
      exact bind_eqd_of_forall _ _ _ fun _ => bind_eqd_of_forall _ _ _ fun _ =>
        bind_const_eqd _ _
    · simp only [hv, hd, ite_false, Bool.false_eq_true, pure_bind, map_pure]
      exact EvalDistEq.rfl

/-- With dummy ciphertexts and a simulated proof, distinguishing `b = 0` from `b = 1` costs
the base-mixer unlinkability advantage of `mixerReduction`. -/
theorem hop_mixer (S : Variant G ρ E X) (sel : Selection F Addr k n)
    (P : Params F G Addr ρ E Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr E X Key DTx WCore C Proof σ n) :
    𝒟[Prod.fst <$> hybrid S sel P A false true .dummy .dummy].boolDist
        𝒟[Prod.fst <$> hybrid S sel P A true true .dummy .dummy] ≤
      mixerAdvantage P.mixer (mixerReduction S sel P A) := by
  rw [mixerAdvantage, (mixerExperiment_eqd S sel P A false).evalDist_eq,
    (mixerExperiment_eqd S sel P A true).evalDist_eq]

end AuditPay.SLINDRO
