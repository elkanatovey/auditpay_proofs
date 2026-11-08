/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.SLIND.Reductions
import VCVio.EvalDist.Monad.Disagreement.Measure

/-!
# Theorem 2, entropy-smoothing hops: uniform DH point → uniform symmetric key
-/

open OracleComp DiffieHellman ENNReal

namespace AuditPay.SLIND

variable {F G Addr HK Key Note DTx WCore C Proof σ : Type} {k n : ℕ}
  [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G]
  [Fintype Addr] [DecidableEq Addr] [SampleableType HK] [SampleableType Key]
  [Inhabited Addr] [Inhabited WCore] [Inhabited C]
  [AddCommGroup Key] [DecidableEq Key]

omit [Fintype F] [Inhabited Addr] [Inhabited WCore] [Inhabited C] [AddCommGroup Key]
  [DecidableEq Key] in
/-- Sender's ciphertext: replacing `KDF(hk, K)` for a uniform `K` by a uniform key costs the
entropy-smoothing advantage of `esReductionS`. -/
theorem hop_esS {P : Params F G Addr HK Key Note DTx WCore C Proof k n}
    (hg : Function.Bijective (· • P.g : F → G))
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) :
    𝒟[hybrid P A b true .randKey .real].boolDist 𝒟[hybrid P A b true .randSym .real] ≤
      EntropySmoothing.advantage F P.g P.kdf (esReductionS P A b) := by
  have h1 : EntropySmoothing.realExperiment F P.g P.kdf (esReductionS P A b) =ᵈ
      hybrid P A b true .randKey .real := by
    simp only [EntropySmoothing.realExperiment, esReductionS, hybrid, slot, bind_assoc,
      pure_bind, ite_true]
    refine EvalDistEq.bind_right _ fun hk => ?_
    refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun H => ?_)
    refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun ox => ?_)
    cases ox with
    | none => exact bind_const_eqd _ _
    | some x =>
      refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun rS => ?_)
      refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun rR => ?_)
      refine EvalDistEq.symm ?_
      exact (uniform_bind_bij (e := fun z : F => z • P.g) hg _).symm
  have h2 : EntropySmoothing.idealExperiment (esReductionS P A b) =ᵈ
      hybrid P A b true .randSym .real := by
    simp only [EntropySmoothing.idealExperiment, esReductionS, hybrid, slot, bind_assoc,
      pure_bind, ite_true]
    refine EvalDistEq.bind_right _ fun hk => ?_
    refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun H => ?_)
    refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun ox => ?_)
    cases ox with
    | none => exact bind_const_eqd _ _
    | some x =>
      refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun rS => ?_)
      exact bind_swap_eqd _ _ _
  rw [EntropySmoothing.advantage, h1.evalDist_eq, h2.evalDist_eq]

omit [Fintype F] [Inhabited Addr] [Inhabited WCore] [Inhabited C] [AddCommGroup Key]
  [DecidableEq Key] in
/-- Recipient's ciphertext, with the sender's already a dummy. -/
theorem hop_esR {P : Params F G Addr HK Key Note DTx WCore C Proof k n}
    (hg : Function.Bijective (· • P.g : F → G))
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) :
    𝒟[hybrid P A b true .dummy .randKey].boolDist 𝒟[hybrid P A b true .dummy .randSym] ≤
      EntropySmoothing.advantage F P.g P.kdf (esReductionR P A b) := by
  have h1 : EntropySmoothing.realExperiment F P.g P.kdf (esReductionR P A b) =ᵈ
      hybrid P A b true .dummy .randKey := by
    simp only [EntropySmoothing.realExperiment, esReductionR, hybrid, slot, bind_assoc,
      pure_bind, ite_true]
    refine EvalDistEq.bind_right _ fun hk => ?_
    refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun H => ?_)
    refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun ox => ?_)
    cases ox with
    | none => exact bind_const_eqd _ _
    | some x =>
      refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun rS => ?_)
      refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun rR => ?_)
      refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun key => ?_)
      refine EvalDistEq.symm ?_
      exact (uniform_bind_bij (e := fun z : F => z • P.g) hg _).symm
  have h2 : EntropySmoothing.idealExperiment (esReductionR P A b) =ᵈ
      hybrid P A b true .dummy .randSym := by
    simp only [EntropySmoothing.idealExperiment, esReductionR, hybrid, slot, bind_assoc,
      pure_bind, ite_true]
    refine EvalDistEq.bind_right _ fun hk => ?_
    refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun H => ?_)
    refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun ox => ?_)
    cases ox with
    | none => exact bind_const_eqd _ _
    | some x =>
      refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun rS => ?_)
      refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun rR => ?_)
      exact bind_swap_eqd _ _ _
  rw [EntropySmoothing.advantage, h1.evalDist_eq, h2.evalDist_eq]

end AuditPay.SLIND
