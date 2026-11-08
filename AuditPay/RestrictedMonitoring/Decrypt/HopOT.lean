/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.RestrictedMonitoring.Decrypt.Defs

/-!
# Theorem 3, decryption game, one-time security hop: the target's message becomes a dummy
-/

open OracleComp DiffieHellman ENNReal

namespace AuditPay.RestrictedMonitoring.Decrypt

open SLIND (Mode otExperiment otAdvantage)

variable {F G Addr HK Key Msg C σ : Type} {k n : ℕ}
  [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G]
  [Fintype Addr] [DecidableEq Addr] [SampleableType HK] [SampleableType Key]
  [DecidableEq Msg] [SampleableType Msg]

omit [Fintype F] in
/-- The one-time experiment of `otReduction` is the hybrid in which the target's ciphertext is
under a uniform key and encrypts its message (`bit = false`) or the dummy (`bit = true`). -/
theorem otExperiment_otReduction (P : Params F G Addr HK Key Msg C k n)
    (A : Adversary F G Addr HK Msg C σ n) (bit : Bool) :
    otExperiment P.senc (otReduction P A) bit =ᵈ
      hybrid P A (if bit then .dummy else .randSym) := by
  simp only [otExperiment, otReduction, hybrid, bind_assoc, pure_bind]
  cases bit <;> simp only [slot, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind,
    EvalDistEq.refl]

omit [Fintype F] in
/-- Replacing the target's message by the dummy message under a uniform key costs the one-time
advantage of `otReduction`. -/
theorem hop_ot (P : Params F G Addr HK Key Msg C k n) (A : Adversary F G Addr HK Msg C σ n) :
    𝒟[hybrid P A .randSym].boolDist 𝒟[hybrid P A .dummy] ≤
      otAdvantage P.senc (otReduction P A) := by
  have h₀ : 𝒟[hybrid P A .randSym] = 𝒟[otExperiment P.senc (otReduction P A) false] :=
    (otExperiment_otReduction P A false).symm.evalDist_eq
  have h₁ : 𝒟[hybrid P A .dummy] = 𝒟[otExperiment P.senc (otReduction P A) true] :=
    (otExperiment_otReduction P A true).symm.evalDist_eq
  rw [otAdvantage, h₀, h₁]

end AuditPay.RestrictedMonitoring.Decrypt
