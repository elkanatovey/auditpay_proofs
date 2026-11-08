/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.SLINDRO.HopZK
import AuditPay.SLINDRO.HopRO
import AuditPay.SLINDRO.HopOT
import AuditPay.SLINDRO.HopMixer

/-!
# Theorem 2 with a random-oracle KDF: the bound up to the query events

For any variant of selective encryption, the SL-IND advantage is at most

  `hopBound false + mixerAdvantage (mixerReduction A) + hopBound true`,

where, for the hidden bit `b`,

  `hopBound b = ZK(zkReduction A b) + queryProbS b + OT(otReductionS A b) +
                 queryProbR b + OT(otReductionR A b)`.

The hybrid order is that of `AuditPay.SLINDDrop`: the proof is simulated first, then the
sender's ciphertext is replaced (random-oracle hop, one-time hop), then the recipient's, and
finally the base mixer is invoked. Each DDH + entropy-smoothing pair of the DDH-based proof has
become one random-oracle hop, whose cost `queryProbS b`/`queryProbR b` is the probability that
the ciphertext's shared point is queried in the fresh-key hybrid. Bounding these probabilities
is where the variants differ: see `AuditPay.SLINDRO.StrongDH`, `AuditPay.SLINDRO.Twin` and
`AuditPay.SLINDRO.Guess`.
-/

open OracleComp OracleSpec ENNReal MeasureTheory

namespace AuditPay.SLINDRO

open KdfRO
open AuditPay.SLIND (zkAdvantage otAdvantage mixerAdvantage)

variable {F G Addr ρ E X Key Note DTx WCore C Proof σ : Type} {k n : ℕ}
  [Field F] [AddCommGroup G] [Module F G] [DecidableEq Addr]
  [SampleableType G] [Fintype Addr] [SampleableType Key] [SampleableType ρ] [DecidableEq X]
  [Inhabited Addr] [Inhabited WCore] [Inhabited C]
  (S : Variant G ρ E X) (sel : Selection F Addr k n)
  (P : Params F G Addr ρ E Key Note DTx WCore C Proof k n)
  (A : Adversary F G Addr E X Key DTx WCore C Proof σ n)

/-- The cost of moving from the SL-IND game for bit `b` to the hybrid with a simulated proof and
two dummy ciphertexts, with the two random-oracle hops counted by their query probabilities. -/
noncomputable def hopBound (b : Bool) : ℝ≥0∞ :=
  zkAdvantage P.zk (zkReduction S sel P A b) +
    queryProbS S sel P A b +
    otAdvantage P.senc (otReductionS S sel P A b) +
    queryProbR S sel P A b +
    otAdvantage P.senc (otReductionR S sel P A b)

/-- The game for bit `b` is within `hopBound b` of the all-dummy hybrid. -/
theorem experiment_dist_le (b : Bool) :
    𝒟[experiment S sel P A b].boolDist 𝒟[Prod.fst <$> hybrid S sel P A b true .dummy .dummy] ≤
      hopBound S sel P A b := by
  have t := Measure.boolDist_triangle
  rw [experiment_eq]
  calc 𝒟[Prod.fst <$> hybrid S sel P A b false .real .real].boolDist
        𝒟[Prod.fst <$> hybrid S sel P A b true .dummy .dummy]
      ≤ 𝒟[Prod.fst <$> hybrid S sel P A b false .real .real].boolDist
          𝒟[Prod.fst <$> hybrid S sel P A b true .real .real] +
        (𝒟[Prod.fst <$> hybrid S sel P A b true .real .real].boolDist
          𝒟[Prod.fst <$> hybrid S sel P A b true .fresh .real] +
        (𝒟[Prod.fst <$> hybrid S sel P A b true .fresh .real].boolDist
          𝒟[Prod.fst <$> hybrid S sel P A b true .dummy .real] +
        (𝒟[Prod.fst <$> hybrid S sel P A b true .dummy .real].boolDist
          𝒟[Prod.fst <$> hybrid S sel P A b true .dummy .fresh] +
        𝒟[Prod.fst <$> hybrid S sel P A b true .dummy .fresh].boolDist
          𝒟[Prod.fst <$> hybrid S sel P A b true .dummy .dummy]))) := by
        refine (t _ _ _).trans (add_le_add le_rfl ?_)
        refine (t _ _ _).trans (add_le_add le_rfl ?_)
        refine (t _ _ _).trans (add_le_add le_rfl ?_)
        exact t _ _ _
    _ ≤ hopBound S sel P A b := by
        rw [hopBound]
        have h1 := hop_zk S sel P A b
        have h2 := hop_roS S sel P A b
        have h3 := hop_otS S sel P A b
        have h4 := hop_roR S sel P A b
        have h5 := hop_otR S sel P A b
        calc _ ≤ _ := add_le_add h1 (add_le_add h2 (add_le_add h3 (add_le_add h4 h5)))
          _ = _ := by ring

/-- **Theorem 2 with a random-oracle KDF, up to the query events.** For any variant of selective
encryption and every selection rule, the SL-IND advantage is at most the base-mixer
unlinkability advantage of `mixerReduction` plus, for each value of the hidden bit, the
zero-knowledge advantage of `zkReduction`, the one-time advantages of `otReductionS` and
`otReductionR`, and the probabilities `queryProbS`, `queryProbR` that the shared point of the
sender's, respectively the recipient's, ciphertext is queried in the hybrid where its key is
fresh. -/
theorem advantage_le_queryProb :
    advantage S sel P A ≤
      hopBound S sel P A false + mixerAdvantage P.mixer (mixerReduction S sel P A) +
        hopBound S sel P A true := by
  have t := Measure.boolDist_triangle
  calc advantage S sel P A
      ≤ 𝒟[experiment S sel P A false].boolDist
          𝒟[Prod.fst <$> hybrid S sel P A false true .dummy .dummy] +
        (𝒟[Prod.fst <$> hybrid S sel P A false true .dummy .dummy].boolDist
          𝒟[Prod.fst <$> hybrid S sel P A true true .dummy .dummy] +
        𝒟[Prod.fst <$> hybrid S sel P A true true .dummy .dummy].boolDist
          𝒟[experiment S sel P A true]) :=
        (t _ _ _).trans (add_le_add le_rfl (t _ _ _))
    _ ≤ hopBound S sel P A false + (mixerAdvantage P.mixer (mixerReduction S sel P A) +
          hopBound S sel P A true) := by
        gcongr
        · exact experiment_dist_le S sel P A false
        · exact hop_mixer S sel P A
        · rw [Measure.boolDist_comm]
          exact experiment_dist_le S sel P A true
    _ = _ := by ring

end AuditPay.SLINDRO
