/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.SLIND.HopZK
import AuditPay.SLIND.HopDDH
import AuditPay.SLIND.HopES
import AuditPay.SLIND.HopOT
import AuditPay.SLIND.HopMixer

/-!
# Theorem 2: Selective Linkability (SL-IND)

The SL-IND advantage is bounded by the advantages of named reductions against: zero knowledge,
DDH (twice, plus `1/|F|` each), entropy smoothing of the KDF (twice), one-time security of the
cipher (twice), for each of the two values of the hidden bit, and base-mixer unlinkability once.
See `AuditPay.SLIND.Defs` for the game and the modeling choices.
-/

open OracleComp DiffieHellman ENNReal MeasureTheory

namespace AuditPay.SLIND

variable {F G Addr HK Key Note DTx WCore C Proof σ : Type} {k n : ℕ}
  [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G]
  [Fintype Addr] [DecidableEq Addr] [SampleableType HK] [SampleableType Key]
  [Inhabited Addr] [Inhabited WCore] [Inhabited C]

/-- The cost of moving from the SL-IND game for bit `b` to the hybrid with a simulated proof and
two dummy ciphertexts. -/
noncomputable def hopBound (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) : ℝ≥0∞ :=
  zkAdvantage P.zk (zkReduction P A b) +
    (ddhAdvantage P.g (ddhReductionS P A b) + (Fintype.card F : ℝ≥0∞)⁻¹) +
    EntropySmoothing.advantage F P.g P.kdf (esReductionS P A b) +
    otAdvantage P.senc (otReductionS P A b) +
    (ddhAdvantage P.g (ddhReductionR P A b) + (Fintype.card F : ℝ≥0∞)⁻¹) +
    EntropySmoothing.advantage F P.g P.kdf (esReductionR P A b) +
    otAdvantage P.senc (otReductionR P A b)

/-- The game for bit `b` is within `hopBound` of the all-dummy hybrid. -/
theorem experiment_dist_le {P : Params F G Addr HK Key Note DTx WCore C Proof k n}
    (hg : Function.Bijective (· • P.g : F → G))
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) :
    𝒟[experiment P A b].boolDist 𝒟[hybrid P A b true .dummy .dummy] ≤ hopBound P A b := by
  have t := Measure.boolDist_triangle
  calc 𝒟[experiment P A b].boolDist 𝒟[hybrid P A b true .dummy .dummy]
      ≤ 𝒟[hybrid P A b false .real .real].boolDist 𝒟[hybrid P A b true .real .real] +
        (𝒟[hybrid P A b true .real .real].boolDist 𝒟[hybrid P A b true .randKey .real] +
        (𝒟[hybrid P A b true .randKey .real].boolDist 𝒟[hybrid P A b true .randSym .real] +
        (𝒟[hybrid P A b true .randSym .real].boolDist 𝒟[hybrid P A b true .dummy .real] +
        (𝒟[hybrid P A b true .dummy .real].boolDist 𝒟[hybrid P A b true .dummy .randKey] +
        (𝒟[hybrid P A b true .dummy .randKey].boolDist 𝒟[hybrid P A b true .dummy .randSym] +
        𝒟[hybrid P A b true .dummy .randSym].boolDist
          𝒟[hybrid P A b true .dummy .dummy]))))) := by
        refine (t _ _ _).trans (add_le_add le_rfl ?_)
        refine (t _ _ _).trans (add_le_add le_rfl ?_)
        refine (t _ _ _).trans (add_le_add le_rfl ?_)
        refine (t _ _ _).trans (add_le_add le_rfl ?_)
        refine (t _ _ _).trans (add_le_add le_rfl ?_)
        exact t _ _ _
    _ ≤ hopBound P A b := by
        rw [hopBound]
        have h1 := hop_zk P A b
        have h2 := hop_ddhS hg A b
        have h3 := hop_esS hg A b
        have h4 := hop_otS P A b
        have h5 := hop_ddhR hg A b
        have h6 := hop_esR hg A b
        have h7 := hop_otR P A b
        calc _ ≤ _ := add_le_add h1 (add_le_add h2 (add_le_add h3 (add_le_add h4
                (add_le_add h5 (add_le_add h6 h7)))))
          _ = _ := by ring

/-- **Theorem 2** (SL-IND security). -/
theorem advantage_le {P : Params F G Addr HK Key Note DTx WCore C Proof k n}
    (hg : Function.Bijective (· • P.g : F → G))
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) :
    advantage P A ≤
      hopBound P A false + mixerAdvantage P.mixer (mixerReduction P A) + hopBound P A true := by
  have t := Measure.boolDist_triangle
  calc advantage P A
      ≤ 𝒟[experiment P A false].boolDist 𝒟[hybrid P A false true .dummy .dummy] +
        (𝒟[hybrid P A false true .dummy .dummy].boolDist 𝒟[hybrid P A true true .dummy .dummy] +
        𝒟[hybrid P A true true .dummy .dummy].boolDist 𝒟[experiment P A true]) :=
        (t _ _ _).trans (add_le_add le_rfl (t _ _ _))
    _ ≤ hopBound P A false + (mixerAdvantage P.mixer (mixerReduction P A) +
          hopBound P A true) := by
        gcongr
        · exact experiment_dist_le hg A false
        · exact hop_mixer P A
        · rw [Measure.boolDist_comm]
          exact experiment_dist_le hg A true
    _ = _ := by ring

end AuditPay.SLIND
