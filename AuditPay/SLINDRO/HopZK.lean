/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.SLINDRO.Reductions
import VCVio.EvalDist.Monad.Disagreement.Measure

/-!
# Theorem 2 with a random-oracle KDF, hop 1: real proof → simulated proof

The zero-knowledge reduction runs the adversary's two phases, and the challenger's two KDF
queries, against a lazily sampled KDF of its own; the zero-knowledge experiment it plays is the
hybrid with a real or simulated proof.
-/

open OracleComp OracleSpec ENNReal

namespace AuditPay.SLINDRO

open KdfRO
open AuditPay.SLIND (zkExperiment zkAdvantage)

variable {F G Addr ρ E X Key Note DTx WCore C Proof σ : Type} {k n : ℕ}
  [Field F] [AddCommGroup G] [Module F G] [DecidableEq Addr]
  [SampleableType G] [Fintype Addr] [SampleableType Key] [SampleableType ρ] [DecidableEq X]
  [Inhabited Addr] [Inhabited WCore] [Inhabited C]

/-- The ZK experiment run by `zkReduction` is the hybrid with a real (`sim = false`) or
simulated (`sim = true`) proof and two real ciphertexts. -/
theorem zkExperiment_eqd (S : Variant G ρ E X) (sel : Selection F Addr k n)
    (P : Params F G Addr ρ E Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr E X Key DTx WCore C Proof σ n) (b sim : Bool) :
    zkExperiment P.zk (zkReduction S sel P A b) sim =ᵈ
      Prod.fst <$> hybrid S sel P A b sim .real .real := by
  simp only [zkExperiment, zkReduction, hybrid, bind_assoc, map_bind]
  refine EvalDistEq.bind_right _ fun H => EvalDistEq.bind_right _ fun z =>
    EvalDistEq.bind_right _ fun ox => ?_
  cases ox with
  | none =>
    simp only [pure_bind, map_pure]
    refine (EvalDistEq.bind_right _ fun rS => (EvalDistEq.bind_right _ fun rR => ?_).trans
      (bind_const_eqd _ _)).trans (bind_const_eqd _ _)
    split_ifs <;> exact bind_const_eqd _ _
  | some x =>
    cases sim <;>
      simp only [pure_bind, map_pure, tailS, tailC, tailR, tailD, msg, roRun_bind, roRun_liftM,
        bind_map_left, map_bind, bind_assoc, Bool.false_eq_true, ite_true, ite_false] <;>
      simp only [map_eq_bind_pure_comp, Function.comp_def, EvalDistEq.refl]

/-- Replacing the real withdrawal proof by a simulated one costs the ZK advantage of
`zkReduction`. -/
theorem hop_zk (S : Variant G ρ E X) (sel : Selection F Addr k n)
    (P : Params F G Addr ρ E Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr E X Key DTx WCore C Proof σ n) (b : Bool) :
    𝒟[Prod.fst <$> hybrid S sel P A b false .real .real].boolDist
        𝒟[Prod.fst <$> hybrid S sel P A b true .real .real] ≤
      zkAdvantage P.zk (zkReduction S sel P A b) := by
  rw [zkAdvantage, (zkExperiment_eqd S sel P A b false).evalDist_eq,
    (zkExperiment_eqd S sel P A b true).evalDist_eq]

end AuditPay.SLINDRO
