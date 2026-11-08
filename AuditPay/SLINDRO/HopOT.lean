/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.SLINDRO.Reductions
import VCVio.EvalDist.Monad.Disagreement.Measure

/-!
# Theorem 2 with a random-oracle KDF, one-time security hops: note → dummy note under a fresh key

In the hybrids where a ciphertext's key is fresh (`Mode.fresh`, `Mode.dummy`) the key is uniform
and used once, so the two plaintexts are told apart only by breaking the one-time security of
the cipher. The reductions run the adversary with a lazily sampled KDF of their own.
-/

open OracleComp OracleSpec ENNReal

namespace AuditPay.SLINDRO

open KdfRO
open AuditPay.SLIND (otExperiment otAdvantage)

variable {F G Addr ρ E X Key Note DTx WCore C Proof σ : Type} {k n : ℕ}
  [Field F] [AddCommGroup G] [Module F G] [DecidableEq Addr]
  [SampleableType G] [Fintype Addr] [SampleableType Key] [SampleableType ρ] [DecidableEq X]

/-- The one-time experiment of `otReductionS` is the hybrid with the sender's ciphertext under a
fresh key, encrypting the note (`bit = false`) or the dummy note (`bit = true`). -/
theorem otExperiment_otReductionS (S : Variant G ρ E X) (sel : Selection F Addr k n)
    (P : Params F G Addr ρ E Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr E X Key DTx WCore C Proof σ n) (b bit : Bool) :
    otExperiment P.senc (otReductionS S sel P A b) bit =ᵈ
      Prod.fst <$> hybrid S sel P A b true (if bit then .dummy else .fresh) .real := by
  simp only [otExperiment, otReductionS, hybrid, bind_assoc, map_bind]
  refine EvalDistEq.bind_right _ fun H => EvalDistEq.bind_right _ fun z =>
    EvalDistEq.bind_right _ fun ox => ?_
  cases ox with
  | none =>
    simp only [pure_bind, map_pure]
    exact bind_const_eqd _ _
  | some x =>
    cases bit <;>
      simp only [pure_bind, map_pure, tailS, keyQ, msg, roRun_liftM, bind_map_left, map_bind,
        bind_assoc, Bool.false_eq_true, ite_true, ite_false] <;>
      simp only [map_eq_bind_pure_comp, Function.comp_def, EvalDistEq.refl]

/-- The one-time experiment of `otReductionR` is the hybrid with the sender's ciphertext a dummy
and the recipient's under a fresh key, encrypting the note (`bit = false`) or the dummy note
(`bit = true`). -/
theorem otExperiment_otReductionR (S : Variant G ρ E X) (sel : Selection F Addr k n)
    (P : Params F G Addr ρ E Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr E X Key DTx WCore C Proof σ n) (b bit : Bool) :
    otExperiment P.senc (otReductionR S sel P A b) bit =ᵈ
      Prod.fst <$> hybrid S sel P A b true .dummy (if bit then .dummy else .fresh) := by
  simp only [otExperiment, otReductionR, hybrid, bind_assoc, map_bind]
  refine EvalDistEq.bind_right _ fun H => EvalDistEq.bind_right _ fun z =>
    EvalDistEq.bind_right _ fun ox => ?_
  cases ox with
  | none =>
    simp only [pure_bind, map_pure]
    exact bind_const_eqd _ _
  | some x =>
    cases bit <;>
      simp only [pure_bind, map_pure, tailS, tailC, tailR, keyQ, msg, roRun_bind, roRun_liftM,
        bind_map_left, map_bind, bind_assoc, Bool.false_eq_true, ite_true, ite_false] <;>
      simp only [map_eq_bind_pure_comp, Function.comp_def, EvalDistEq.refl]

/-- Sender's ciphertext: replacing the encrypted note by the dummy note under a fresh key costs
the one-time advantage of `otReductionS`. -/
theorem hop_otS (S : Variant G ρ E X) (sel : Selection F Addr k n)
    (P : Params F G Addr ρ E Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr E X Key DTx WCore C Proof σ n) (b : Bool) :
    𝒟[Prod.fst <$> hybrid S sel P A b true .fresh .real].boolDist
        𝒟[Prod.fst <$> hybrid S sel P A b true .dummy .real] ≤
      otAdvantage P.senc (otReductionS S sel P A b) := by
  have h₀ := (otExperiment_otReductionS S sel P A b false).symm.evalDist_eq
  have h₁ := (otExperiment_otReductionS S sel P A b true).symm.evalDist_eq
  simp only [Bool.false_eq_true, ite_false, ite_true] at h₀ h₁
  rw [otAdvantage, h₀, h₁]

/-- Recipient's ciphertext, with the sender's already a dummy. -/
theorem hop_otR (S : Variant G ρ E X) (sel : Selection F Addr k n)
    (P : Params F G Addr ρ E Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr E X Key DTx WCore C Proof σ n) (b : Bool) :
    𝒟[Prod.fst <$> hybrid S sel P A b true .dummy .fresh].boolDist
        𝒟[Prod.fst <$> hybrid S sel P A b true .dummy .dummy] ≤
      otAdvantage P.senc (otReductionR S sel P A b) := by
  have h₀ := (otExperiment_otReductionR S sel P A b false).symm.evalDist_eq
  have h₁ := (otExperiment_otReductionR S sel P A b true).symm.evalDist_eq
  simp only [Bool.false_eq_true, ite_false, ite_true] at h₀ h₁
  rw [otAdvantage, h₀, h₁]

end AuditPay.SLINDRO
