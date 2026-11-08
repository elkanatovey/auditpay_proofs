/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.SLINDRO.Generic
import AuditPay.SLINDRO.OW
import AuditPay.SLINDRO.Single
import AuditPay.KdfRO.NoteHiding.StrongDH

/-!
# Theorem 2 with a random-oracle KDF, the paper's scheme: reduction to strong Diffie–Hellman

**Scheme unchanged (Algorithm 2), tight reduction, no DDH.** For the SL-IND game of
`AuditPay.SLINDRO` with the selective encryption of Algorithm 2 (`AuditPay.SLINDRO.Single.game`:
one ephemeral value, the key derived from `r • (RetrieveKey(V, a) - H(a))`), the advantage is at
most

  `hopBound false + Mixer(mixerReduction A) + hopBound true`,

with, for the hidden bit `b`,

  `hopBound b = ZK(zkReduction A b) + (sDH(sdhReductionS A b) + 1/|F|) + OT(otReductionS A b) +
                 (sDH(sdhReductionR A b) + 1/|F|) + OT(otReductionR A b)`,

where `sDH` is the success probability in the strong Diffie–Hellman experiment
(`AuditPay.StrongDH`). The bound does not depend on the number of KDF queries, and there is no
DDH and no entropy-smoothing term.

By `AuditPay.SLINDRO.advantage_le_queryProb` it remains to bound the probabilities that the
shared point of the sender's (`queryProbS`) or the recipient's (`queryProbR`) ciphertext is
queried in the hybrid where its key is fresh. An adversary that queries it yields one that
*outputs* it in the one-wayness game with a decision oracle (`AuditPay.SLINDRO.OW`): the
one-wayness adversary forwards the SL-IND adversary's choice with the sender (resp. the
recipient) as its target, receives `R = r • g`, simulates the rest of the hybrid itself — the
deposits, the base withdrawal, the other ciphertext (real, with the lazily sampled KDF of the
simulation), the ciphertext of the target under a fresh key with ephemeral point `R`, and the
simulated proof — and then finds the shared point among the queried points with the decision
oracle, one query `(RetrieveKey(V, a) - H(a), Z)` per point. `OW.strong_success_le` then gives
the strong Diffie–Hellman bound.
-/

open OracleComp OracleSpec DiffieHellman ENNReal

namespace AuditPay.SLINDRO.StrongDH

open KdfRO
open AuditPay.SLIND (zkAdvantage otAdvantage mixerAdvantage)
open AuditPay.SLINDDrop (Choice valid)

variable {F G Addr Key Note DTx WCore C Proof σ : Type} {k n : ℕ}
  [Field F] [Fintype F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]
  [Fintype Addr] [DecidableEq Addr] [SampleableType Key]
  (sel : Selection F Addr k n) (P : Params F G Addr F G Key Note DTx WCore C Proof k n)
  (A : Adversary F G Addr G G Key DTx WCore C Proof σ n)

/-! ## The one-wayness adversaries -/

/-- The state of the one-wayness adversaries after the first phase: `H`, the SL-IND adversary's
choice, and the KDF cache. -/
abbrev State (F G Addr Key σ : Type) (n : ℕ) :=
  (Addr → G) × Choice F Addr σ n × (G →ₒ Key).QueryCache

/-- The one-wayness adversary (with a decision oracle) for the sender's ciphertext and bit `b`.
It forwards the SL-IND adversary's choice with the sender `d_b` as target; given `R`, it
simulates the fresh-key hybrid (the recipient's ciphertext real, under its own lazily sampled
KDF; the sender's note under a fresh key with ephemeral point `R`; a simulated proof) and
searches the queried points for the sender's shared point with the decision oracle. -/
noncomputable def owAdversaryS (b : Bool) :
    OW.StrongAdversary F G Addr (State F G Addr Key σ n) n where
  choose H := do
    let z ← roRun (A.choose H) ∅
    return ⟨z.1.req, z.1.sk, z.1.fill, if b then z.1.d₁ else z.1.d₀, (H, z.1, z.2)⟩
  guess st R := do
    let ox ← setup sel P b st.1 st.2.1
    match ox with
    | none => return 0
    | some x => do
      let rR ← $ᵗ F
      let keyS ← $ᵗ Key
      let v ← roRun (tailC (single F P.g) P A b true .real x 0 rR (P.senc keyS (x.note b), R))
        st.2.2
      let hit ← AuditPay.StrongDH.scan (x.pt P.pos P.coef (x.sender b)) (cachedPoints v.2)
      return hit.getD 0

/-- The one-wayness adversary (with a decision oracle) for the recipient's ciphertext and bit
`b`, with the sender's ciphertext a dummy under a fresh key. -/
noncomputable def owAdversaryR (b : Bool) :
    OW.StrongAdversary F G Addr (State F G Addr Key σ n) n where
  choose H := do
    let z ← roRun (A.choose H) ∅
    return ⟨z.1.req, z.1.sk, z.1.fill, z.1.wAddr, (H, z.1, z.2)⟩
  guess st R := do
    let ox ← setup sel P b st.1 st.2.1
    match ox with
    | none => return 0
    | some x => do
      let rS ← $ᵗ F
      let keyS ← $ᵗ Key
      let keyR ← $ᵗ Key
      let v ← roRun (tailD P A b true x rS 0 (P.senc keyS P.dummy, rS • P.g)
        (P.senc keyR (x.note b), R)) st.2.2
      let hit ← AuditPay.StrongDH.scan (x.pt P.pos P.coef x.c.wAddr) (cachedPoints v.2)
      return hit.getD 0

/-- The strong Diffie–Hellman reduction for the sender's ciphertext and bit `b`. -/
noncomputable def sdhReductionS (b : Bool) : AuditPay.StrongDH.Adversary F G :=
  OW.sdhReduction P.pos P.coef sel (owAdversaryS sel P A b)

/-- The strong Diffie–Hellman reduction for the recipient's ciphertext and bit `b`. -/
noncomputable def sdhReductionR (b : Bool) : AuditPay.StrongDH.Adversary F G :=
  OW.sdhReduction P.pos P.coef sel (owAdversaryR sel P A b)

/-! ## The query events are won one-wayness games -/

omit [Fintype F] [SampleableType F] [AddCommGroup G] [Module F G] [SampleableType G]
  [DecidableEq G] [Fintype Addr] [SampleableType Key] in
/-- The sender of a valid choice is not selected (on choices). -/
theorem sender_not_mem_select {c : Choice F Addr σ n} (hv : valid sel P.pos P.coef c = true)
    (b : Bool) : (if b then c.d₁ else c.d₀) ∉ sel.select P.pos P.coef c.req := by
  have h := SLINDDrop.valid_excl hv
  cases b
  · exact h.1
  · exact h.2.1

omit [Fintype F] in
/-- If the sender's shared point is queried in the fresh-key hybrid, `owAdversaryS` outputs
it. -/
theorem queryProbS_le_strongExperiment (b : Bool) :
    queryProbS (single F P.g) sel P A b ≤
      𝒟[OW.strongExperiment P.g P.pos P.coef sel (owAdversaryS sel P A b)] {true} := by
  rw [← prEvent_eq_evalDist_singleton]
  simp only [queryProbS, hybrid, OW.strongExperiment, owAdversaryS, bind_assoc, pure_bind,
    simulateQ_bind, AuditPay.StrongDH.simulateQ_oracleImpl_liftM]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun H => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun z => ?_
  by_cases hsel : (if b then z.1.d₁ else z.1.d₀) ∈ sel.select P.pos P.coef z.1.req
  · have hv : ¬valid sel P.pos P.coef z.1 = true := fun hv =>
      sender_not_mem_select sel P hv b hsel
    simp [setup_of_not_valid hv, QueriedS]
  · simp only [OW.Choice.selected, hsel, ite_false]
    -- the one-wayness game samples `r` before the deposits; move it after them
    rw [(bind_swap_eqd _ _ _).prEvent_eq]
    refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun ox hox => ?_
    cases ox with
    | none => simp [QueriedS]
    | some x =>
      obtain ⟨hv, hH, hc, hV⟩ := setup_spec hox
      obtain ⟨H', c', V', dep₀, dep₁, core⟩ := x
      simp only at hH hc hV
      subst hH hc hV
      simp only [keyQ, tailS, tailC, tailR, tailD, msg, single, roRun_liftM, roRun_bind,
        bind_map_left, bind_assoc, pure_bind, ite_true, simulateQ_bind, simulateQ_pure,
        AuditPay.StrongDH.simulateQ_oracleImpl_liftM, AuditPay.StrongDH.simulateQ_oracleImpl_scan]
      refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun rS => ?_
      refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun rR => ?_
      refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun keyS => ?_
      refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun w => ?_
      refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun π => ?_
      refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun v => ?_
      refine prEvent_pure_le_pure _ _ _ _ fun hq => ?_
      simp only [QueriedS] at hq
      exact decide_eq_true (NoteHiding.find_cachedPoints_eq hq)

omit [Fintype F] in
/-- If the recipient's shared point is queried in the fresh-key hybrid (the sender's ciphertext
a dummy), `owAdversaryR` outputs it. -/
theorem queryProbR_le_strongExperiment (b : Bool) :
    queryProbR (single F P.g) sel P A b ≤
      𝒟[OW.strongExperiment P.g P.pos P.coef sel (owAdversaryR sel P A b)] {true} := by
  rw [← prEvent_eq_evalDist_singleton]
  simp only [queryProbR, hybrid, OW.strongExperiment, owAdversaryR, bind_assoc, pure_bind,
    simulateQ_bind, AuditPay.StrongDH.simulateQ_oracleImpl_liftM]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun H => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun z => ?_
  by_cases hsel : z.1.wAddr ∈ sel.select P.pos P.coef z.1.req
  · have hv : ¬valid sel P.pos P.coef z.1 = true := fun hv =>
      (SLINDDrop.valid_excl hv).2.2 hsel
    simp [setup_of_not_valid hv, QueriedR]
  · simp only [OW.Choice.selected, hsel, ite_false]
    -- the one-wayness game samples `r` before the deposits; move it after them
    rw [(bind_swap_eqd _ _ _).prEvent_eq]
    refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun ox hox => ?_
    cases ox with
    | none => simp [QueriedR]
    | some x =>
      obtain ⟨hv, hH, hc, hV⟩ := setup_spec hox
      obtain ⟨H', c', V', dep₀, dep₁, core⟩ := x
      simp only at hH hc hV
      subst hH hc hV
      simp only [keyQ, tailS, tailC, tailR, tailD, msg, single, roRun_liftM, roRun_bind,
        bind_map_left, bind_assoc, pure_bind, ite_true, simulateQ_bind, simulateQ_pure,
        AuditPay.StrongDH.simulateQ_oracleImpl_liftM, AuditPay.StrongDH.simulateQ_oracleImpl_scan]
      -- the hybrid samples `rS` before `rR`; the one-wayness game gives `rR` first
      refine le_of_eq_of_le ((bind_swap_eqd ($ᵗ F) ($ᵗ F) _).prEvent_eq _) ?_
      refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun rR => ?_
      refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun rS => ?_
      refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun keyS => ?_
      refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun keyR => ?_
      refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun π => ?_
      refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun v => ?_
      refine prEvent_pure_le_pure _ _ _ _ fun hq => ?_
      simp only [QueriedR] at hq
      exact decide_eq_true (NoteHiding.find_cachedPoints_eq hq)

/-! ## The bound -/

/-- The sender's shared point is queried in the fresh-key hybrid with probability at most the
strong Diffie–Hellman success probability of `sdhReductionS` plus `1/|F|`. -/
theorem queryProbS_le (hg : Function.Bijective (· • P.g : F → G)) (b : Bool) :
    queryProbS (single F P.g) sel P A b ≤
      𝒟[AuditPay.StrongDH.experiment P.g (sdhReductionS sel P A b)] {true} +
        (Fintype.card F : ℝ≥0∞)⁻¹ :=
  (queryProbS_le_strongExperiment sel P A b).trans
    (OW.strong_success_le P.g P.pos P.coef sel hg (owAdversaryS sel P A b))

/-- The recipient's shared point is queried in the fresh-key hybrid with probability at most
the strong Diffie–Hellman success probability of `sdhReductionR` plus `1/|F|`. -/
theorem queryProbR_le (hg : Function.Bijective (· • P.g : F → G)) (b : Bool) :
    queryProbR (single F P.g) sel P A b ≤
      𝒟[AuditPay.StrongDH.experiment P.g (sdhReductionR sel P A b)] {true} +
        (Fintype.card F : ℝ≥0∞)⁻¹ :=
  (queryProbR_le_strongExperiment sel P A b).trans
    (OW.strong_success_le P.g P.pos P.coef sel hg (owAdversaryR sel P A b))

variable [Inhabited Addr] [Inhabited WCore] [Inhabited C]

/-- The cost of moving from the SL-IND game for bit `b` to the hybrid with a simulated proof and
two dummy ciphertexts, under strong Diffie–Hellman. -/
noncomputable def hopBound (b : Bool) : ℝ≥0∞ :=
  zkAdvantage P.zk (zkReduction (single F P.g) sel P A b) +
    (𝒟[AuditPay.StrongDH.experiment P.g (sdhReductionS sel P A b)] {true} +
      (Fintype.card F : ℝ≥0∞)⁻¹) +
    otAdvantage P.senc (otReductionS (single F P.g) sel P A b) +
    (𝒟[AuditPay.StrongDH.experiment P.g (sdhReductionR sel P A b)] {true} +
      (Fintype.card F : ℝ≥0∞)⁻¹) +
    otAdvantage P.senc (otReductionR (single F P.g) sel P A b)

/-- **Theorem 2 (SL-IND) with a random-oracle KDF, the paper's scheme, under strong
Diffie–Hellman** (option 2). For a generator `g` and every selection rule, the SL-IND advantage
of any adversary is at most the base-mixer unlinkability advantage of `mixerReduction` plus,
for each value of the hidden bit, the zero-knowledge advantage of `zkReduction`, and, for each
of the two ciphertexts, the strong Diffie–Hellman success probability of the reduction
(`sdhReductionS`, `sdhReductionR`) plus `1/|F|` and the one-time advantage of the reduction
(`otReductionS`, `otReductionR`). The bound does not depend on the number of KDF queries. -/
theorem advantage_le (hg : Function.Bijective (· • P.g : F → G)) :
    Single.advantage sel P A ≤
      hopBound sel P A false +
        mixerAdvantage P.mixer (mixerReduction (single F P.g) sel P A) +
        hopBound sel P A true := by
  rw [Single.advantage_eq]
  refine (advantage_le_queryProb (single F P.g) sel P A).trans ?_
  simp only [SLINDRO.hopBound, hopBound]
  gcongr
  · exact queryProbS_le sel P A hg false
  · exact queryProbR_le sel P A hg false
  · exact queryProbS_le sel P A hg true
  · exact queryProbR_le sel P A hg true

end AuditPay.SLINDRO.StrongDH
