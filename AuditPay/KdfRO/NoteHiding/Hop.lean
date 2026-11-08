/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.KdfRO.NoteHiding.Defs
import VCVio.EvalDist.Monad.Disagreement.Measure

/-!
# Note hiding with a random-oracle KDF: the random-oracle hop and the one-time hop

For any variant of selective encryption, the note-hiding advantage is at most

  `queryProb false + otAdvantage (otReduction A) + queryProb true`,

where `queryProb b` is the probability that, in the *ideal* run for bit `b` (the note is
encrypted under a fresh uniform key), the adversary queries the KDF at the shared point.

* **Random-oracle hop** (`dist_game_idealRun_le`). The game and the ideal run differ only in
  where the symmetric key comes from: the KDF's answer at the shared point `K`, or a fresh
  uniform key. A lazily sampled random oracle answers a point that was never queried before with
  a fresh uniform key, so the two runs are identical unless the adversary queries `K` at some
  time, before or after the challenge (`KdfRO.prEvent_fresh_le_query`).
* **One-time hop** (`otExperiment_eqd`). In the ideal run the key is uniform and used once, so
  the two bits are told apart only by breaking the one-time security of the cipher.

Bounding `queryProb` is where the variants differ: see `AuditPay.NoteHiding.StrongDH`,
`AuditPay.NoteHiding.Twin` and `AuditPay.NoteHiding.Guess`.
-/

open OracleComp OracleSpec ENNReal

namespace AuditPay.NoteHiding

open KdfRO SLIND

variable {F G Addr ρ E X Key Note C σ τ : Type} [Field F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G]
  [Fintype Addr] [DecidableEq Addr] [SampleableType ρ] [DecidableEq X] [SampleableType Key]

/-! ## The random-oracle hop -/

/-- An outcome of the ideal run in which the adversary did not query the shared point is at most
as likely as the same outcome of the game. -/
theorem prEvent_idealRun_le_game (S : Variant G ρ E X) (g : G) (senc : Key → Note → C)
    (A : Adversary F G Addr E X Key Note C σ τ) (b v : Bool) :
    Pr{let x ← S.idealRun g senc A b}[x.1 = v ∧ ¬S.Queried x.2] ≤
      Pr{let y ← roExec (S.game g senc A b)}[y = v] := by
  rw [roExec_eq, prEvent_map]
  simp only [Variant.idealRun, Variant.game, roRun_bind, roRun_liftM, bind_map_left, roRun_ite,
    roRun_pure]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun H => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun z => ?_
  by_cases ha : z.1.1 = z.1.2.1
  · simp only [ha, ite_true]
    exact prEvent_pure_le_pure _ _ _ _ fun h => h.1
  · simp only [ha, ite_false]
    refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun sk => ?_
    refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun r => ?_
    refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun w => ?_
    refine le_trans (le_of_eq ?_) (prEvent_fresh_le_query
      (S.pt r (auditKey g sk (H z.1.1) - H z.1.2.1))
      (fun key => A.guess w.1.2.2 (senc key (if b then w.1.2.1 else w.1.1))) (· = v) w.2)
    simp only [prEvent_norm]
    simp [Variant.Queried]

/-- **The random-oracle hop.** The game for bit `b` and the ideal run for bit `b` (fresh key) are
within `queryProb b`, the probability that the adversary queries the KDF at the shared point in
the ideal run. -/
theorem dist_game_idealRun_le (S : Variant G ρ E X) (g : G) (senc : Key → Note → C)
    (A : Adversary F G Addr E X Key Note C σ τ) (b : Bool) :
    𝒟[roExec (S.game g senc A b)].boolDist 𝒟[Prod.fst <$> S.idealRun g senc A b] ≤
      S.queryProb g senc A b := by
  rw [MeasureTheory.Measure.boolDist, ← prEvent_eq_evalDist_singleton,
    ← prEvent_eq_evalDist_singleton, prEvent_map]
  refine ENNReal.absDiff_le_iff.2 ⟨?_, ?_⟩
  · rw [add_comm]
    refine prEvent_le_prEvent_add_of_prEvent_not_and_not_le (S.idealRun g senc A b)
      (roExec (S.game g senc A b)) (fun x => S.Queried x.2) (fun x => x.1 = true)
      (fun y => y = true) ?_ ?_
    · rw [prEvent_true_eq_one, prEvent_true_eq_one]
    · have h := prEvent_idealRun_le_game S g senc A b false
      simpa only [Bool.not_eq_true] using h
  · rw [add_comm]
    exact prEvent_le_prEvent_add_of_prEvent_and_not_le (S.idealRun g senc A b)
      (roExec (S.game g senc A b)) (fun x => S.Queried x.2) (fun x => x.1 = true)
      (fun y => y = true) (prEvent_idealRun_le_game S g senc A b true)

/-! ## The one-time hop -/

/-- The one-time experiment of `otReduction` for bit `b` is the ideal run for bit `b`. -/
theorem otExperiment_eqd [Inhabited Note] (S : Variant G ρ E X) (g : G) (senc : Key → Note → C)
    (A : Adversary F G Addr E X Key Note C σ τ) (b : Bool) :
    otExperiment senc (S.otReduction g A) b =ᵈ Prod.fst <$> S.idealRun g senc A b := by
  simp only [otExperiment, Variant.otReduction, Variant.idealRun, bind_assoc, map_bind]
  refine EvalDistEq.bind_right _ fun H => EvalDistEq.bind_right _ fun z => ?_
  by_cases ha : z.1.1 = z.1.2.1
  · simp only [ha, ite_true, pure_bind, map_pure]
    exact bind_const_eqd _ _
  · simp only [ha, ite_false, prEvent_norm]
    exact .rfl

/-! ## The bound -/

/-- **Note hiding, up to the query event.** For any variant, the note-hiding advantage is at most
the one-time advantage of `otReduction` plus, for each bit, the probability that the adversary
queries the KDF at the shared point in the ideal run. -/
theorem advantage_le_queryProb [Inhabited Note] (S : Variant G ρ E X) (g : G)
    (senc : Key → Note → C) (A : Adversary F G Addr E X Key Note C σ τ) :
    S.advantage g senc A ≤
      S.queryProb g senc A false + otAdvantage senc (S.otReduction g A) +
        S.queryProb g senc A true := by
  have t := MeasureTheory.Measure.boolDist_triangle
  have h₀ := dist_game_idealRun_le S g senc A false
  have h₁ := dist_game_idealRun_le S g senc A true
  rw [MeasureTheory.Measure.boolDist_comm] at h₁
  have hot : 𝒟[Prod.fst <$> S.idealRun g senc A false].boolDist
      𝒟[Prod.fst <$> S.idealRun g senc A true] = otAdvantage senc (S.otReduction g A) := by
    rw [otAdvantage, (otExperiment_eqd S g senc A false).evalDist_eq,
      (otExperiment_eqd S g senc A true).evalDist_eq]
  calc S.advantage g senc A
      ≤ 𝒟[roExec (S.game g senc A false)].boolDist 𝒟[Prod.fst <$> S.idealRun g senc A false] +
        (𝒟[Prod.fst <$> S.idealRun g senc A false].boolDist
            𝒟[Prod.fst <$> S.idealRun g senc A true] +
          𝒟[Prod.fst <$> S.idealRun g senc A true].boolDist
            𝒟[roExec (S.game g senc A true)]) :=
        (t _ _ _).trans (add_le_add le_rfl (t _ _ _))
    _ ≤ S.queryProb g senc A false + (otAdvantage senc (S.otReduction g A) +
          S.queryProb g senc A true) := by
        rw [hot]
        gcongr
    _ = _ := by ring

/-! ## The number of queried points -/

/-- In an ideal run of an adversary making at most `q₁ + q₂ + q₃` KDF queries, the final cache
holds at most that many points. -/
theorem length_cachedPoints_le_of_mem_support_idealRun [Finite X] (S : Variant G ρ E X) (g : G)
    (senc : Key → Note → C) {A : Adversary F G Addr E X Key Note C σ τ} {q₁ q₂ q₃ : ℕ}
    (hq : A.QueryBound q₁ q₂ q₃) (b : Bool) {x : Bool × Option (Outcome G ρ X Key)}
    (hx : x ∈ support (S.idealRun g senc A b)) {o : Outcome G ρ X Key} (ho : x.2 = some o) :
    (cachedPoints o.2.2).length ≤ q₁ + q₂ + q₃ := by
  simp only [Variant.idealRun, mem_support_bind_iff] at hx
  obtain ⟨H, -, z, hz, hx⟩ := hx
  by_cases ha : z.1.1 = z.1.2.1
  · simp only [ha, ite_true, support_pure, Set.mem_singleton_iff] at hx
    subst hx
    exact absurd ho (by simp)
  · simp only [ha, ite_false, mem_support_bind_iff] at hx
    obtain ⟨sk, -, r, -, w, hw, key, -, v, hv, hx⟩ := hx
    simp only [support_pure, Set.mem_singleton_iff] at hx
    subst hx
    simp only [Option.some.injEq] at ho
    subst ho
    have h1 := toSet_encard_le_of_mem_support_roRun (hq.choose H) hz
    have h2 := toSet_encard_le_of_mem_support_roRun (hq.notes _ _ _ _) hw
    have h3 := toSet_encard_le_of_mem_support_roRun (hq.guess _ _) hv
    have h4 := length_cachedPoints_le v.2
    rw [QueryCache.toSet_empty, Set.encard_empty, zero_add] at h1
    have : ((cachedPoints v.2).length : ℕ∞) ≤ ((q₁ + q₂ + q₃ : ℕ) : ℕ∞) := by
      push_cast
      calc ((cachedPoints v.2).length : ℕ∞) ≤ v.2.toSet.encard := h4
        _ ≤ w.2.toSet.encard + q₃ := h3
        _ ≤ z.2.toSet.encard + q₂ + q₃ := by gcongr
        _ ≤ q₁ + q₂ + q₃ := by gcongr
    exact_mod_cast this

end AuditPay.NoteHiding
