/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.SLINDDrop.Reductions
import VCVio.EvalDist.Monad.Disagreement.Measure

/-!
# Theorem 2 for the never-failing generation, hop 1: real proof → simulated proof
-/

open OracleComp DiffieHellman ENNReal

namespace AuditPay.SLINDDrop

open AuditPay.SLIND (Params Mode slot zkExperiment zkAdvantage)

variable {F G Addr HK Key Note DTx WCore C Proof σ : Type} {k n : ℕ}
  [Field F] [Fintype F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G]
  [Fintype Addr] [DecidableEq Addr] [SampleableType HK] [SampleableType Key]
  [Inhabited Addr] [Inhabited WCore] [Inhabited C]

omit [Fintype F] in
/-- The ZK experiment run by `zkReduction` is the hybrid with a real (`sim = false`) or
simulated (`sim = true`) proof. -/
theorem zkExperiment_eqd (sel : Selection F Addr k n)
    (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b sim : Bool) :
    zkExperiment P.zk (zkReduction sel P A b) sim =ᵈ hybrid sel P A b sim .real .real := by
  simp only [zkExperiment, zkReduction, hybrid, bind_assoc]
  refine EvalDistEq.bind_right _ fun hk => ?_
  refine EvalDistEq.bind_right _ fun H => ?_
  refine EvalDistEq.bind_right _ fun ox => ?_
  cases ox with
  | none =>
    cases sim <;> simp only [pure_bind, ite_true, ite_false, Bool.false_eq_true] <;>
      exact bind_const_eqd _ _
  | some x =>
    simp only [bind_assoc, pure_bind]
    exact EvalDistEq.rfl

omit [Fintype F] in
/-- Replacing the real withdrawal proof by a simulated one costs the ZK advantage of
`zkReduction`. -/
theorem hop_zk (sel : Selection F Addr k n)
    (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) :
    𝒟[hybrid sel P A b false .real .real].boolDist 𝒟[hybrid sel P A b true .real .real] ≤
      zkAdvantage P.zk (zkReduction sel P A b) := by
  rw [zkAdvantage, (zkExperiment_eqd sel P A b false).evalDist_eq,
    (zkExperiment_eqd sel P A b true).evalDist_eq]

end AuditPay.SLINDDrop
