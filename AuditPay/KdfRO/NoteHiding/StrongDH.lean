/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.KdfRO.NoteHiding.Hop
import AuditPay.KdfRO.SharedKeyOW

/-!
# Note hiding for the paper's scheme under strong Diffie–Hellman (random-oracle KDF)

**Scheme unchanged, tight reduction.** For Algorithm 2 with a random-oracle key-derivation
function, the note-hiding advantage (`AuditPay.NoteHiding.advantage`) is at most

  `(SDH(sdhReduction A false) + 1/|F|) + OT(otReduction A) + (SDH(sdhReduction A true) + 1/|F|)`,

where `SDH` is the success probability in the strong Diffie–Hellman experiment
(`AuditPay.StrongDH`) and `OT` the one-time advantage against the cipher. No DDH assumption, no
entropy-smoothing assumption, and no dependence on the number of KDF queries.

By `AuditPay.NoteHiding.advantage_le_queryProb` it remains to bound the probability that the
adversary queries the KDF at the shared point `K = r • (AK_a - H(a*))` in the ideal run, where the
ciphertext is independent of `K`. An adversary that does so yields one that *outputs* `K` in the
one-wayness game with a decision oracle (`AuditPay.SharedKeyOW.strongExperiment`): run the
note-hiding adversary against a lazily sampled KDF, and then use the decision oracle to find
`K` among the queried points (one decision query `(AK_a - H(a*), Z)` per queried point `Z`).
`AuditPay.SharedKeyOW.strong_success_le` then gives the strong Diffie–Hellman bound.
-/

open OracleComp OracleSpec DiffieHellman ENNReal

namespace AuditPay.NoteHiding

open KdfRO SLIND

variable {F G Addr Key Note C σ τ : Type} [Field F] [Fintype F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]
  [Fintype Addr] [DecidableEq Addr] [SampleableType Key]

/-- The one-wayness adversary (with a decision oracle) built from a note-hiding adversary and a
bit `b`. It simulates the ideal run for `b` with a lazily sampled KDF of its own (the ciphertext
is an encryption under a fresh key), and then searches the points the adversary queried for the
shared point, with one decision query per point. Its state after the first phase is
`(H(a*), the adversary's state, the KDF cache)`. -/
noncomputable def owAdversary (senc : Key → Note → C)
    (A : Adversary F G Addr G G Key Note C σ τ) (b : Bool) :
    SharedKeyOW.StrongAdversary F G Addr (G × σ × (G →ₒ Key).QueryCache) where
  choose H := do
    let z ← roRun (A.choose H) ∅
    return (z.1.1, z.1.2.1, (H z.1.2.1, z.1.2.2, z.2))
  guess st sk ak R := do
    let w ← roRun (A.notes st.2.1 sk ak R) st.2.2
    let key ← $ᵗ Key
    let v ← roRun (A.guess w.1.2.2 (senc key (if b then w.1.2.1 else w.1.1))) w.2
    let hit ← StrongDH.scan (ak - st.1) (cachedPoints v.2)
    return hit.getD 0

/-- The strong Diffie–Hellman reduction for note hiding, for bit `b`. -/
noncomputable def sdhReduction (senc : Key → Note → C)
    (A : Adversary F G Addr G G Key Note C σ τ) (b : Bool) : StrongDH.Adversary F G :=
  SharedKeyOW.sdhReduction (owAdversary senc A b)

omit [SampleableType Key] in
/-- Searching the points of a cache for a cached point `K` finds `K`. -/
theorem find_cachedPoints_eq {c : (G →ₒ Key).QueryCache} {K : G} (h : (c K).isSome) :
    ((cachedPoints c).find? fun Z => decide (Z = K)).getD 0 = K := by
  classical
  have hsome : ((cachedPoints c).find? fun Z => decide (Z = K)).isSome :=
    List.find?_isSome.2 ⟨K, mem_cachedPoints.2 h, by simp⟩
  obtain ⟨Z, hZ⟩ := Option.isSome_iff_exists.1 hsome
  have := List.find?_some hZ
  rw [hZ, Option.getD_some]
  simpa using this

omit [Fintype F] in
/-- If the adversary queries the KDF at the shared point in the ideal run, the one-wayness
adversary `owAdversary` outputs the shared point. -/
theorem queryProb_le_strongExperiment (g : G) (senc : Key → Note → C)
    (A : Adversary F G Addr G G Key Note C σ τ) (b : Bool) :
    (single F g).queryProb g senc A b ≤
      𝒟[SharedKeyOW.strongExperiment g (owAdversary senc A b)] {true} := by
  rw [← prEvent_eq_evalDist_singleton]
  simp only [Variant.queryProb, Variant.idealRun, SharedKeyOW.strongExperiment, owAdversary,
    bind_assoc, pure_bind, simulateQ_bind, StrongDH.simulateQ_oracleImpl_liftM,
    StrongDH.simulateQ_oracleImpl_scan, simulateQ_pure]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun H => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun z => ?_
  by_cases ha : z.1.1 = z.1.2.1
  · simp [ha, Variant.Queried]
  · simp only [ha, ite_false]
    refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun sk => ?_
    refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun r => ?_
    refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun w => ?_
    refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun key => ?_
    refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun v => ?_
    refine prEvent_pure_le_pure _ _ _ _ fun hq => ?_
    obtain ⟨t, ht, hq⟩ := hq
    cases ht
    simp only [encPoint]
    exact decide_eq_true (find_cachedPoints_eq hq)

/-- In the ideal run, the adversary queries the KDF at the shared point with probability at most
the strong Diffie–Hellman success probability of `sdhReduction` plus `1/|F|`. -/
theorem queryProb_le {g : G} (hg : Function.Bijective (· • g : F → G)) (senc : Key → Note → C)
    (A : Adversary F G Addr G G Key Note C σ τ) (b : Bool) :
    (single F g).queryProb g senc A b ≤
      𝒟[StrongDH.experiment g (sdhReduction senc A b)] {true} + (Fintype.card F : ℝ≥0∞)⁻¹ :=
  (queryProb_le_strongExperiment g senc A b).trans
    (SharedKeyOW.strong_success_le hg (owAdversary senc A b))

/-- **Note hiding for a mismatched address, random-oracle KDF, scheme unchanged** (option 2).
For a generator `g`, the note-hiding advantage of any adversary against Algorithm 2 is at most
the one-time advantage of `otReduction` against the cipher plus, for each of the two bits, the
strong Diffie–Hellman success probability of `sdhReduction` plus `1/|F|`. The reduction is
tight and the bound does not depend on the number of KDF queries. -/
theorem advantage_le [Inhabited Note] {g : G} (hg : Function.Bijective (· • g : F → G))
    (senc : Key → Note → C) (A : Adversary F G Addr G G Key Note C σ τ) :
    advantage g senc A ≤
      (𝒟[StrongDH.experiment g (sdhReduction senc A false)] {true} + (Fintype.card F : ℝ≥0∞)⁻¹) +
        otAdvantage senc (otReduction g A) +
      (𝒟[StrongDH.experiment g (sdhReduction senc A true)] {true} + (Fintype.card F : ℝ≥0∞)⁻¹) := by
  rw [advantage_eq]
  refine (advantage_le_queryProb (single F g) g senc A).trans ?_
  gcongr
  · exact queryProb_le hg senc A false
  · exact le_rfl
  · exact queryProb_le hg senc A true

end AuditPay.NoteHiding
