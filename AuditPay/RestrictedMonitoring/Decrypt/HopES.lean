/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.RestrictedMonitoring.Decrypt.Defs

/-!
# Theorem 3, decryption game, entropy-smoothing hop: the target's symmetric key becomes uniform
-/

open OracleComp DiffieHellman ENNReal

namespace AuditPay.RestrictedMonitoring.Decrypt

open SLIND (Mode)

variable {F G Addr HK Key Msg C σ : Type} {k n : ℕ}
  [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G]
  [Fintype Addr] [DecidableEq Addr] [SampleableType HK] [SampleableType Key]
  [DecidableEq Msg] [SampleableType Msg]

omit [Fintype F] in
/-- Replacing `KDF(hk, K)` for a uniform Diffie–Hellman point `K` of the target by a uniform
symmetric key costs the entropy-smoothing advantage of `esReduction`. -/
theorem hop_es {P : Params F G Addr HK Key Msg C k n}
    (hg : Function.Bijective (· • P.g : F → G)) (A : Adversary F G Addr HK Msg C σ n) :
    𝒟[hybrid P A .randKey].boolDist 𝒟[hybrid P A .randSym] ≤
      EntropySmoothing.advantage F P.g P.kdf (esReduction P A) := by
  have h1 : EntropySmoothing.realExperiment F P.g P.kdf (esReduction P A) =ᵈ
      hybrid P A .randKey := by
    simp only [EntropySmoothing.realExperiment, esReduction, hybrid, slot, bind_assoc, pure_bind]
    refine EvalDistEq.bind_right _ fun hk => ?_
    refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun H => ?_)
    refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun c => ?_)
    refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun m => ?_)
    refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun r => ?_)
    refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun μ => ?_)
    refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun ρ => ?_)
    exact uniform_bind_bij (e := fun z : F => z • P.g) hg
      fun K => finish P A hk H c m r μ (P.senc (P.kdf hk K) μ, ρ • P.g)
  have h2 : EntropySmoothing.idealExperiment (esReduction P A) =ᵈ hybrid P A .randSym := by
    simp only [EntropySmoothing.idealExperiment, esReduction, hybrid, slot, bind_assoc, pure_bind]
    refine EvalDistEq.bind_right _ fun hk => ?_
    refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun H => ?_)
    refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun c => ?_)
    refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun m => ?_)
    refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun r => ?_)
    refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun μ => ?_)
    exact bind_swap_eqd _ _ _
  rw [EntropySmoothing.advantage, h1.evalDist_eq, h2.evalDist_eq]

end AuditPay.RestrictedMonitoring.Decrypt
