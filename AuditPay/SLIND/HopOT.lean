/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.SLIND.Reductions
import VCVio.EvalDist.Monad.Disagreement.Measure

/-!
# Theorem 2, one-time security hops: note → dummy note under a uniform key
-/

open OracleComp DiffieHellman ENNReal

namespace AuditPay.SLIND

variable {F G Addr HK Key Note DTx WCore C Proof σ : Type} {k n : ℕ}
  [Field F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G]
  [Fintype Addr] [DecidableEq Addr] [SampleableType HK] [SampleableType Key]

/-- The one-time experiment of `otReductionS` is the hybrid with the sender's ciphertext under a
uniform key, encrypting the note (`bit = false`) or the dummy note (`bit = true`). -/
theorem otExperiment_otReductionS (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b bit : Bool) :
    otExperiment P.senc (otReductionS P A b) bit =ᵈ
      hybrid P A b true (if bit then .dummy else .randSym) .real := by
  simp only [otExperiment, otReductionS, hybrid, bind_assoc]
  refine EvalDistEq.bind_right _ fun hk => ?_
  refine EvalDistEq.bind_right _ fun H => ?_
  refine EvalDistEq.bind_right _ fun ox => ?_
  cases ox with
  | none =>
    simp only [pure_bind]
    exact AuditPay.bind_const_eqd _ _
  | some x =>
    cases bit <;> simp only [slot, Bool.false_eq_true, ↓reduceIte, pure_bind, bind_assoc,
      bind_pure_comp, bind_map_left, EvalDistEq.refl]

/-- The one-time experiment of `otReductionR` is the hybrid with the sender's ciphertext a dummy
and the recipient's under a uniform key, encrypting the note (`bit = false`) or the dummy note
(`bit = true`). -/
theorem otExperiment_otReductionR (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b bit : Bool) :
    otExperiment P.senc (otReductionR P A b) bit =ᵈ
      hybrid P A b true .dummy (if bit then .dummy else .randSym) := by
  simp only [otExperiment, otReductionR, hybrid, bind_assoc]
  refine EvalDistEq.bind_right _ fun hk => ?_
  refine EvalDistEq.bind_right _ fun H => ?_
  refine EvalDistEq.bind_right _ fun ox => ?_
  cases ox with
  | none =>
    simp only [pure_bind]
    exact AuditPay.bind_const_eqd _ _
  | some x =>
    cases bit <;> simp only [slot, Bool.false_eq_true, ↓reduceIte, bind_assoc, bind_pure_comp,
      bind_map_left, EvalDistEq.refl]

/-- Sender's ciphertext: replacing the encrypted note by the dummy note under a uniform key costs
the one-time advantage of `otReductionS`. -/
theorem hop_otS (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) :
    𝒟[hybrid P A b true .randSym .real].boolDist 𝒟[hybrid P A b true .dummy .real] ≤
      otAdvantage P.senc (otReductionS P A b) := by
  have h₀ : 𝒟[hybrid P A b true .randSym .real] =
      𝒟[otExperiment P.senc (otReductionS P A b) false] :=
    (otExperiment_otReductionS P A b false).symm.evalDist_eq
  have h₁ : 𝒟[hybrid P A b true .dummy .real] =
      𝒟[otExperiment P.senc (otReductionS P A b) true] :=
    (otExperiment_otReductionS P A b true).symm.evalDist_eq
  rw [otAdvantage, h₀, h₁]

/-- Recipient's ciphertext, with the sender's already a dummy. -/
theorem hop_otR (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) :
    𝒟[hybrid P A b true .dummy .randSym].boolDist 𝒟[hybrid P A b true .dummy .dummy] ≤
      otAdvantage P.senc (otReductionR P A b) := by
  have h₀ : 𝒟[hybrid P A b true .dummy .randSym] =
      𝒟[otExperiment P.senc (otReductionR P A b) false] :=
    (otExperiment_otReductionR P A b false).symm.evalDist_eq
  have h₁ : 𝒟[hybrid P A b true .dummy .dummy] =
      𝒟[otExperiment P.senc (otReductionR P A b) true] :=
    (otExperiment_otReductionR P A b true).symm.evalDist_eq
  rw [otAdvantage, h₀, h₁]

end AuditPay.SLIND
