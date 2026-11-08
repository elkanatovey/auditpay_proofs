/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.SLINDRO.Defs
import VCVio.EvalDist.Monad.Disagreement.Measure

/-!
# Theorem 2 with a random-oracle KDF: the random-oracle hops (real key → fresh key)

The replacement for the DDH and entropy-smoothing hops of `AuditPay.SLINDDrop`. The hybrid in
which a ciphertext's key is the KDF's answer at its shared point `K`, and the hybrid in which
it is a fresh uniform key, differ only in where that key comes from. A lazily sampled random
oracle answers a point that was never queried before with a fresh uniform key, so the two runs
are identical unless `K` is queried at some time (`KdfRO.prEvent_fresh_le_query`): by the
adversary, in either phase, or — for the sender's ciphertext — by the challenger's own query
for the recipient's ciphertext, should the two shared points coincide. The cost of the hop is
therefore the probability of that event in the fresh-key hybrid, `queryProbS`/`queryProbR`,
which the option files bound by a one-wayness game.
-/

open OracleComp OracleSpec ENNReal

namespace AuditPay.SLINDRO

open KdfRO

variable {F G Addr ρ E X Key Note DTx WCore C Proof σ : Type} {k n : ℕ}
  [Field F] [AddCommGroup G] [Module F G] [DecidableEq Addr]
  [SampleableType G] [Fintype Addr] [SampleableType Key] [SampleableType ρ] [DecidableEq X]
  (S : Variant G ρ E X) (sel : Selection F Addr k n)
  (P : Params F G Addr ρ E Key Note DTx WCore C Proof k n)
  (A : Adversary F G Addr E X Key DTx WCore C Proof σ n) (b : Bool)

/-! ## The sender's ciphertext -/

/-- An outcome of the fresh-key hybrid in which the sender's shared point was never queried is
at most as likely as the same outcome of the real-key hybrid. -/
theorem prEvent_freshS_le_real (v : Bool) :
    Pr{let x ← hybrid S sel P A b true .fresh .real}[x.1 = v ∧ ¬QueriedS S P.pos P.coef b x.2] ≤
      Pr{let x ← hybrid S sel P A b true .real .real}[x.1 = v] := by
  simp only [hybrid]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun H => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun z => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun ox => ?_
  cases ox with
  | none => exact prEvent_pure_le_pure _ _ _ _ fun h => h.1
  | some x =>
    refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun rS => ?_
    refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun rR => ?_
    refine (le_of_eq ?_).trans ((prEvent_fresh_le_query
      (S.pt rS (x.pt P.pos P.coef (x.sender b)))
      (fun key => tailC S P A b true .real x rS rR (P.senc key (x.note b), S.eph rS)) (· = v)
      z.2).trans (le_of_eq ?_))
    · simp only [keyQ, tailS, msg, roRun_liftM, bind_map_left, prEvent_norm]
      simp [QueriedS]
    · simp only [keyQ, tailS, msg, prEvent_norm]

/-- **The random-oracle hop for the sender's ciphertext.** The hybrids with the sender's key
real and fresh are within `queryProbS`, the probability that the sender's shared point is
queried in the fresh-key hybrid. -/
theorem hop_roS :
    𝒟[Prod.fst <$> hybrid S sel P A b true .real .real].boolDist
        𝒟[Prod.fst <$> hybrid S sel P A b true .fresh .real] ≤
      queryProbS S sel P A b := by
  rw [MeasureTheory.Measure.boolDist, ← prEvent_eq_evalDist_singleton,
    ← prEvent_eq_evalDist_singleton, prEvent_map, prEvent_map]
  refine ENNReal.absDiff_le_iff.2 ⟨?_, ?_⟩
  · rw [add_comm]
    refine prEvent_le_prEvent_add_of_prEvent_not_and_not_le (hybrid S sel P A b true .fresh .real)
      (hybrid S sel P A b true .real .real) (fun x => QueriedS S P.pos P.coef b x.2)
      (fun x => x.1 = true) (fun x => x.1 = true) ?_ ?_
    · rw [prEvent_true_eq_one, prEvent_true_eq_one]
    · have h := prEvent_freshS_le_real S sel P A b false
      simpa only [Bool.not_eq_true] using h
  · rw [add_comm]
    exact prEvent_le_prEvent_add_of_prEvent_and_not_le (hybrid S sel P A b true .fresh .real)
      (hybrid S sel P A b true .real .real) (fun x => QueriedS S P.pos P.coef b x.2)
      (fun x => x.1 = true) (fun x => x.1 = true) (prEvent_freshS_le_real S sel P A b true)

/-! ## The recipient's ciphertext -/

/-- An outcome of the fresh-key hybrid in which the recipient's shared point was never queried
is at most as likely as the same outcome of the real-key hybrid (the sender's ciphertext being
a dummy in both). -/
theorem prEvent_freshR_le_real (v : Bool) :
    Pr{let x ← hybrid S sel P A b true .dummy .fresh}[x.1 = v ∧ ¬QueriedR S P.pos P.coef x.2] ≤
      Pr{let x ← hybrid S sel P A b true .dummy .real}[x.1 = v] := by
  simp only [hybrid]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun H => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun z => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun ox => ?_
  cases ox with
  | none => exact prEvent_pure_le_pure _ _ _ _ fun h => h.1
  | some x =>
    refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun rS => ?_
    refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun rR => ?_
    simp only [keyQ, tailS, tailC, msg, roRun_liftM, roRun_bind, bind_map_left, bind_assoc]
    refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun keyS => ?_
    refine (le_of_eq ?_).trans ((prEvent_fresh_le_query
      (S.pt rR (x.pt P.pos P.coef x.c.wAddr))
      (fun key => tailR S P A b true .real x rS rR (P.senc keyS P.dummy, S.eph rS) key) (· = v)
      z.2).trans (le_of_eq ?_))
    · simp only [tailR, msg, prEvent_norm]
      simp [QueriedR]
    · simp only [prEvent_norm]

/-- **The random-oracle hop for the recipient's ciphertext**, with the sender's already a
dummy. -/
theorem hop_roR :
    𝒟[Prod.fst <$> hybrid S sel P A b true .dummy .real].boolDist
        𝒟[Prod.fst <$> hybrid S sel P A b true .dummy .fresh] ≤
      queryProbR S sel P A b := by
  rw [MeasureTheory.Measure.boolDist, ← prEvent_eq_evalDist_singleton,
    ← prEvent_eq_evalDist_singleton, prEvent_map, prEvent_map]
  refine ENNReal.absDiff_le_iff.2 ⟨?_, ?_⟩
  · rw [add_comm]
    refine prEvent_le_prEvent_add_of_prEvent_not_and_not_le (hybrid S sel P A b true .dummy .fresh)
      (hybrid S sel P A b true .dummy .real) (fun x => QueriedR S P.pos P.coef x.2)
      (fun x => x.1 = true) (fun x => x.1 = true) ?_ ?_
    · rw [prEvent_true_eq_one, prEvent_true_eq_one]
    · have h := prEvent_freshR_le_real S sel P A b false
      simpa only [Bool.not_eq_true] using h
  · rw [add_comm]
    exact prEvent_le_prEvent_add_of_prEvent_and_not_le (hybrid S sel P A b true .dummy .fresh)
      (hybrid S sel P A b true .dummy .real) (fun x => QueriedR S P.pos P.coef x.2)
      (fun x => x.1 = true) (fun x => x.1 = true) (prEvent_freshR_le_real S sel P A b true)

end AuditPay.SLINDRO
