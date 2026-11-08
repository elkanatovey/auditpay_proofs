/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.SLIND.Reductions
import VCVio.EvalDist.Monad.Disagreement.Measure

/-!
# Theorem 2, last hop: base-mixer unlinkability

Once both ciphertexts encrypt the dummy note under uniform keys and the proof is simulated,
the two worlds differ only in the base mixer.
-/

open OracleComp DiffieHellman ENNReal

namespace AuditPay.SLIND

variable {F G Addr HK Key Note DTx WCore C Proof σ : Type} {k n : ℕ}
  [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G]
  [Fintype Addr] [DecidableEq Addr] [SampleableType HK] [SampleableType Key]
  [Inhabited Addr] [Inhabited WCore] [Inhabited C]

/-- A sample followed by a continuation that is, for every value, distributed as `my` is
distributed as `my`. -/
private theorem bind_eqd_of_forall {α β : Type} (mx : ProbComp α) (f : α → ProbComp β)
    (my : ProbComp β) (h : ∀ a, f a =ᵈ my) : (mx >>= f) =ᵈ my :=
  (EvalDistEq.bind_right mx h).trans (bind_const_eqd mx my)

omit [Fintype F] [Inhabited Addr] [Inhabited WCore] [Inhabited C] in
/-- The base-mixer experiment run by `mixerReduction` for bit `b` is the all-dummy hybrid with
a simulated proof for bit `b`. -/
theorem mixerExperiment_eqd (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) :
    mixerExperiment P.mixer (mixerReduction P A) b =ᵈ hybrid P A b true .dummy .dummy := by
  simp only [mixerExperiment, mixerReduction, hybrid, setup, bind_assoc, pure_bind]
  refine EvalDistEq.bind_right _ fun hk => ?_
  refine EvalDistEq.bind_right _ fun H => ?_
  refine EvalDistEq.bind_right _ fun c => ?_
  by_cases hv : valid c = true
  · simp only [hv, valid_distinct hv, ↓reduceIte]
    cases hV : auditKeyVecGen P.g H P.pos P.coef c.1 c.2.1 with
    | none =>
      simp only [pure_bind]
      exact bind_eqd_of_forall _ _ _ fun _ => bind_eqd_of_forall _ _ _ fun _ =>
        bind_const_eqd _ _
    | some V =>
      simp only [bind_assoc, pure_bind, slot, stmt, finish]
      exact EvalDistEq.rfl
  · by_cases hd : distinct c.2.2.1 c.2.2.2.1 c.2.2.2.2.1 = true
    · simp only [hv, hd, ↓reduceIte]
      exact bind_eqd_of_forall _ _ _ fun _ => bind_eqd_of_forall _ _ _ fun _ =>
        bind_const_eqd _ _
    · simp only [hv, hd, ↓reduceIte, Bool.false_eq_true]
      exact EvalDistEq.rfl

omit [Fintype F] [Inhabited Addr] [Inhabited WCore] [Inhabited C] in
/-- With dummy ciphertexts and a simulated proof, distinguishing `b = 0` from `b = 1` costs
the base-mixer unlinkability advantage of `mixerReduction`. -/
theorem hop_mixer (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) :
    𝒟[hybrid P A false true .dummy .dummy].boolDist 𝒟[hybrid P A true true .dummy .dummy] ≤
      mixerAdvantage P.mixer (mixerReduction P A) := by
  rw [mixerAdvantage, (mixerExperiment_eqd P A false).evalDist_eq,
    (mixerExperiment_eqd P A true).evalDist_eq]

end AuditPay.SLIND
