/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.KdfRO.Monitoring.Hop
import AuditPay.KdfRO.NoteHiding.Twin

/-!
# Theorem 3, decryption game with a random-oracle KDF, twin variant: reduction to CDH

For the two-ephemeral-value variant (`AuditPay.Twin`), the decryption game of Definition 3 with a
random-oracle key-derivation function reduces to the shared-secret game of
`AuditPay.RestrictedMonitoring.SharedSecret`, hence (tightly) to CDH, without the algebraic
group model and with no decision oracle.

The reduction `ssAdversary` plays the shared-secret game: it receives the first ephemeral points
`R₁ᵢ` and must output `r₁ᵢ • Pᵢ` for all `i`, where `Pᵢ = RetrieveKey(V, aᵢ) - H(aᵢ)`. It picks
trapdoors `(sᵢ, tᵢ)`, sets `R₂ᵢ = sᵢ • g - tᵢ • R₁ᵢ` (so `r₂ᵢ = sᵢ - tᵢ r₁ᵢ` is uniform and `tᵢ`
is hidden), encrypts under fresh keys `κᵢ` for the hidden indices (`Pᵢ ≠ 0`), answers the
adversary's KDF query at a pair `(Z₁, Z₂)` with `κⱼ` for the first hidden `j` whose trapdoor test
`tⱼ • Z₁ + Z₂ = sⱼ • Pⱼ` accepts, and finally outputs, for each hidden `i`, the first component of
the first logged pair accepted by test `i` (and `0` for the others).

Its simulation is the programmed run of `AuditPay.Monitoring.Hop` except at the *false
positives*: pairs `(Z₁, Z₂) ≠ Kⱼ` accepted by test `j`. A fixed wrong pair is accepted with
probability at most `1/|F|` over `tⱼ` (`AuditPay.NoteHiding.Twin.prob_test_le`), and the
adversary's view is independent of `t`, so over the at most `q₂` logged pairs (and the public
point `(0, 0)`) and the `n + 1` indices, a false positive occurs with probability at most
`(n + 1) (q₂ + 1) / |F|`. Without false positives, if the adversary queries every hidden `Kᵢ`, the
extraction is correct.
-/

open OracleComp OracleSpec DiffieHellman ENNReal

namespace AuditPay.Monitoring.Twin

open KdfRO SLIND RestrictedMonitoring

variable {F G Addr Key Msg C σ : Type} {k n : ℕ} [Field F] [Fintype F] [DecidableEq F]
  [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G] [Fintype G]
  [Fintype Addr] [DecidableEq Addr] [SampleableType Key] [SampleableType Msg] [DecidableEq Msg]
  (g : G) (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F) (senc : Key → Msg → C)
  (A : Adversary G Addr (G × G) (G × G) Key Msg C σ n)

/-- The trapdoor recognizer of index `i`: `Pᵢ ≠ 0` and the pair passes the trapdoor test with
trapdoor `(sᵢ, tᵢ)` for `Pᵢ`. -/
def trapRec (s t : Fin (n + 1) → F) (P : Fin (n + 1) → G) (i : Fin (n + 1)) (Z : G × G) : Bool :=
  decide (P i ≠ 0) && NoteHiding.Twin.test (s i) (t i) (P i) Z

/-- The reduction's KDF table: the first-phase cache, completed by `gB`, overridden by `κ j` at
the pairs that the trapdoor recognizer of the first accepting index `j` accepts. -/
def trapTable (cache : ((G × G) →ₒ Key).QueryCache) (gB : G × G → Key) (s t : Fin (n + 1) → F)
    (P : Fin (n + 1) → G) (κ : Fin (n + 1) → Key) : G × G → Key :=
  completeTable cache (overrideBy gB (trapRec s t P) κ)

/-- The reduction's output for index `i`: `0` if `Pᵢ = 0`, else the first component of the first
logged pair accepted by test `i` (or `0`). -/
def extract (s t : Fin (n + 1) → F) (P : Fin (n + 1) → G)
    (log : QueryLog (unifSpec + ((G × G) →ₒ Key))) (i : Fin (n + 1)) : G :=
  if P i = 0 then 0 else
    (((kdfPoints log).find? (NoteHiding.Twin.test (s i) (t i) (P i))).map Prod.fst).getD 0

/-- The state of the reduction after the first phase: `H`, the commitment and the KDF cache. -/
abbrev State (G Addr Key σ : Type) (n : ℕ) :=
  (Addr → G) × Commit G Addr σ n × ((G × G) →ₒ Key).QueryCache

/-- The shared-secret adversary built from a decryption adversary against the twin variant. -/
noncomputable def ssAdversary : SharedSecret.Adversary G Addr (State G Addr Key σ n) n where
  commit H := do
    let z ← roRun (A.commit H) ∅
    return (z.1.1, z.1.2.1, (H, z.1, z.2))
  respond st R₁ := do
    let s ← $ᵗ (Fin (n + 1) → F)
    let t ← $ᵗ (Fin (n + 1) → F)
    let m ← $ᵗ (Fin (n + 1) → Msg)
    let gB ← $ᵗ (G × G → Key)
    let κ ← $ᵗ (Fin (n + 1) → Key)
    let T := trapTable st.2.2 gB s t (pts pos coef st.1 st.2.1) κ
    let z ← tableRun T (A.respond st.2.1.2.2 fun i =>
      (senc (if pts pos coef st.1 st.2.1 i = 0 then T (0, 0) else κ i) (m i),
        (R₁ i, s i • g - t i • R₁ i))).withQueryLog
    return fun i => extract s t (pts pos coef st.1 st.2.1) z.2 i

/-- The CDH reduction for the decryption game of the twin variant. -/
noncomputable def cdhReduction : CDHAdversary F G :=
  SharedSecret.cdhReduction pos coef (ssAdversary g pos coef senc A)

/-! ## The reduction's run as a run of the programmed game -/

/-- The trapdoor `s` of the reduction, in terms of the ephemeral randomness and `t`:
`sᵢ = r₂ᵢ + tᵢ r₁ᵢ`. -/
def sOf (p : Pre G Addr (F × F) (G × G) Key Msg σ n) (t : Fin (n + 1) → F) (i : Fin (n + 1)) :
    F :=
  (p.r i).2 + t i * (p.r i).1

/-- The reduction's keys: `κ i` for hidden indices, the table's value at `(0, 0)` otherwise. -/
def trapKeys (p : Pre G Addr (F × F) (G × G) Key Msg σ n) (T : G × G → Key)
    (κ : Fin (n + 1) → Key) (i : Fin (n + 1)) : Key :=
  if p.P pos coef i = 0 then T (0, 0) else κ i

/-- The reduction's run, as a run of the programmed game with the trapdoor table: the prefix,
a table, keys, the trapdoor `t`, and the suffix. Returns the outcome and `t`. -/
noncomputable def trapRun :
    ProbComp (Outcome G Addr (F × F) (G × G) Key Msg σ n × (Fin (n + 1) → F)) :=
  prefixRun A >>= fun p => $ᵗ (G × G → Key) >>= fun gB => $ᵗ (Fin (n + 1) → Key) >>= fun κ =>
    $ᵗ (Fin (n + 1) → F) >>= fun t =>
      (fun z => ((p, z), t)) <$> suffixRun (twin F g) senc A p
        (trapTable p.cache gB (sOf p t) t (p.P pos coef) κ)
        (trapKeys pos coef p (trapTable p.cache gB (sOf p t) t (p.P pos coef) κ) κ)

/-- The programmed run with an independent trapdoor `t` drawn beside it. -/
noncomputable def progRunT :
    ProbComp (Outcome G Addr (F × F) (G × G) Key Msg σ n × (Fin (n + 1) → F)) :=
  prefixRun A >>= fun p => $ᵗ (G × G → Key) >>= fun gB => $ᵗ (Fin (n + 1) → Key) >>= fun κ =>
    $ᵗ (Fin (n + 1) → F) >>= fun t =>
      (fun z => ((p, z), t)) <$> suffixRun (twin F g) senc A p
        (progTable pos coef (twin F g) p gB κ)
        (keysOf (twin F g) pos coef p (progTable pos coef (twin F g) p gB κ))

/-- The reduction wins the shared-secret game. -/
def WinSS (x : Outcome G Addr (F × F) (G × G) Key Msg σ n × (Fin (n + 1) → F)) : Prop :=
  ∀ i, extract (sOf x.1.1 x.2) x.2 (x.1.1.P pos coef) x.1.2.2 i =
    (x.1.1.r i).1 • x.1.1.P pos coef i

/-- Merging two uniform vectors into a uniform vector of pairs. -/
theorem merge_eqd {β : Type} (f : (Fin (n + 1) → F × F) → ProbComp β) :
    (do let r₁ ← $ᵗ (Fin (n + 1) → F); let r₂ ← $ᵗ (Fin (n + 1) → F)
        f fun i => (r₁ i, r₂ i)) =ᵈ (($ᵗ (Fin (n + 1) → F × F)) >>= f) := by
  have h := uniform_bind_bij
    (e := fun q : (Fin (n + 1) → F) × (Fin (n + 1) → F) => fun i => (q.1 i, q.2 i))
    (Equiv.arrowProdEquivProdArrow (Fin (n + 1)) (fun _ => F) (fun _ => F)).symm.bijective f
  rw [SampleableType.uniformSample_prod_eq_bind] at h
  simpa only [bind_assoc, pure_bind] using h

/-- The reparametrization of the reduction's trapdoors: `(r₁, s, t)` with `r₂ = s - t r₁` is
`(r, t)` with `r` uniform. -/
theorem reparam_eqd {β : Type}
    (k : (Fin (n + 1) → F × F) → (Fin (n + 1) → F) → ProbComp β) :
    (do let r₁ ← $ᵗ (Fin (n + 1) → F); let s ← $ᵗ (Fin (n + 1) → F)
        let t ← $ᵗ (Fin (n + 1) → F)
        k (fun i => (r₁ i, s i - t i * r₁ i)) t) =ᵈ
      (do let r ← $ᵗ (Fin (n + 1) → F × F); let t ← $ᵗ (Fin (n + 1) → F); k r t) := by
  refine EvalDistEq.trans ?_ (merge_eqd fun r => $ᵗ (Fin (n + 1) → F) >>= fun t => k r t)
  refine EvalDistEq.bind_right _ fun r₁ => ?_
  refine (bind_swap_eqd _ _ _).trans ?_
  refine EvalDistEq.trans ?_ (bind_swap_eqd _ _ _).symm
  refine EvalDistEq.bind_right _ fun t => ?_
  exact uniform_bind_bij (e := fun s : Fin (n + 1) → F => fun i => s i - t i * r₁ i)
    (Equiv.piCongrRight fun i => Equiv.subRight (t i * r₁ i)).bijective
    fun r₂ => k (fun i => (r₁ i, r₂ i)) t

/-- The reduction's second phase and the final check, as a function of `H`, the commitment, the
ephemeral randomness and `t`. -/
noncomputable def kont (H : Addr → G) (z : Commit G Addr σ n × ((G × G) →ₒ Key).QueryCache)
    (r : Fin (n + 1) → F × F) (t : Fin (n + 1) → F) : ProbComp Bool := do
  let m ← $ᵗ (Fin (n + 1) → Msg)
  let gB ← $ᵗ (G × G → Key)
  let κ ← $ᵗ (Fin (n + 1) → Key)
  let T := trapTable z.2 gB (fun i => (r i).2 + t i * (r i).1) t (pts pos coef H z.1) κ
  let z' ← tableRun T (A.respond z.1.2.2 fun i =>
    (senc (if pts pos coef H z.1 i = 0 then T (0, 0) else κ i) (m i),
      ((r i).1 • g, (r i).2 • g))).withQueryLog
  return decide (∀ i, extract (fun i => (r i).2 + t i * (r i).1) t (pts pos coef H z.1) z'.2 i =
    encPoint (r i).1 (retrieveKey pos coef z.1.1 (z.1.2.1 i)) (H (z.1.2.1 i)))

/-- The shared-secret experiment, with the reduction's trapdoor `s` written as `r₂ + t r₁`. -/
theorem experiment_eqd_kont :
    SharedSecret.experiment g pos coef (ssAdversary g pos coef senc A) =ᵈ (do
      let H ← $ᵗ (Addr → G)
      let z ← roRun (A.commit H) ∅
      let r₁ ← $ᵗ (Fin (n + 1) → F)
      let s ← $ᵗ (Fin (n + 1) → F)
      let t ← $ᵗ (Fin (n + 1) → F)
      kont g pos coef senc A H z (fun i => (r₁ i, s i - t i * r₁ i)) t) := by
  simp only [SharedSecret.experiment, ssAdversary, kont, bind_assoc, pure_bind, sub_add_cancel,
    sub_smul, mul_smul]
  exact .rfl

/-- The shared-secret experiment of `ssAdversary` is the reduction's run followed by the check
that the extracted points are right. -/
theorem prob_experiment_eq_trapRun :
    𝒟[SharedSecret.experiment g pos coef (ssAdversary g pos coef senc A)] {true} =
      Pr{let x ← trapRun g pos coef senc A}[WinSS pos coef x] := by
  rw [← prEvent_eq_evalDist_singleton, (experiment_eqd_kont g pos coef senc A).prEvent_eq]
  have h2 : (do
      let H ← $ᵗ (Addr → G)
      let z ← roRun (A.commit H) ∅
      let r₁ ← $ᵗ (Fin (n + 1) → F)
      let s ← $ᵗ (Fin (n + 1) → F)
      let t ← $ᵗ (Fin (n + 1) → F)
      kont g pos coef senc A H z (fun i => (r₁ i, s i - t i * r₁ i)) t) =ᵈ (do
      let H ← $ᵗ (Addr → G)
      let z ← roRun (A.commit H) ∅
      let r ← $ᵗ (Fin (n + 1) → F × F)
      let t ← $ᵗ (Fin (n + 1) → F)
      kont g pos coef senc A H z r t) :=
    EvalDistEq.bind_right _ fun H => EvalDistEq.bind_right _ fun z =>
      reparam_eqd fun r t => kont g pos coef senc A H z r t
  rw [h2.prEvent_eq]
  simp only [kont, trapRun, prefixRun, bind_assoc, pure_bind, prEvent_norm, decide_eq_true_eq]
  refine prEvent_bind_congr' _ _ _ fun H => prEvent_bind_congr' _ _ _ fun z =>
    prEvent_bind_congr' _ _ _ fun r => ?_
  -- move `t` past the messages, the table and the keys
  rw [prEvent_bind_swap]
  refine prEvent_bind_congr' _ _ _ fun m => ?_
  rw [prEvent_bind_swap]
  refine prEvent_bind_congr' _ _ _ fun gB => ?_
  rw [prEvent_bind_swap]
  refine prEvent_bind_congr' _ _ _ fun κ => prEvent_bind_congr' _ _ _ fun t => ?_
  simp only [suffixRun, trapKeys, sOf, WinSS, Pre.P, twin, encPoint, pts]
  rfl

/-! ## False positives of the trapdoor tests -/

/-- The event of the generic bound (`hitProb`), read on the run with the trapdoor `t`. -/
def HitAll (x : Outcome G Addr (F × F) (G × G) Key Msg σ n × (Fin (n + 1) → F)) : Prop :=
  x.1.1.Good pos coef (twin F g) ∧
    ∀ i, x.1.1.hid pos coef i → Hit (x.1.1.K pos coef (twin F g) i) x.1.2

/-- The false positives: pairs at which some trapdoor recognizer disagrees with the exact
recognizer `Z = Kⱼ` (for hidden `j`). -/
def FP (p : Pre G Addr (F × F) (G × G) Key Msg σ n) (t : Fin (n + 1) → F) : Set (G × G) :=
  {Z | ∃ j, trapRec (sOf p t) t (p.P pos coef) j Z ≠
    (p.hid pos coef j && decide (p.K pos coef (twin F g) j = Z))}

/-- No false positive among the logged pairs and at the public point `(0, 0)`. -/
def NoFP (x : Outcome G Addr (F × F) (G × G) Key Msg σ n × (Fin (n + 1) → F)) : Prop :=
  LogAvoids (FP g pos coef x.1.1 x.2) x.1.2.2 ∧ (0, 0) ∉ FP g pos coef x.1.1 x.2

omit [Fintype F] [DecidableEq F] [SampleableType F] [SampleableType G] [Fintype G]
  [Fintype Addr] [DecidableEq Addr] [SampleableType Key] [SampleableType Msg] [DecidableEq Msg] in
/-- A false positive is a pair other than `Kⱼ` accepted by the test of a hidden `j`. -/
theorem of_mem_FP {p : Pre G Addr (F × F) (G × G) Key Msg σ n} {t : Fin (n + 1) → F}
    {Z : G × G} (hZ : Z ∈ FP g pos coef p t) :
    ∃ j, p.hid pos coef j ∧ NoteHiding.Twin.test (sOf p t j) (t j) (p.P pos coef j) Z = true ∧
      Z ≠ p.K pos coef (twin F g) j := by
  obtain ⟨j, hj⟩ := hZ
  simp only [trapRec, Pre.hid, ne_eq] at hj ⊢
  by_cases hP : p.P pos coef j = 0
  · simp [hP] at hj
  · refine ⟨j, by simpa using hP, ?_, ?_⟩
    · by_contra htest
      apply hj
      simp only [hP, not_false_eq_true, decide_true, Bool.true_and]
      rw [Bool.eq_false_iff.2 htest, eq_comm, decide_eq_false_iff_not]
      rintro rfl
      exact htest (NoteHiding.Twin.test_true (p.r j).1 (p.r j).2 (t j) (p.P pos coef j))
    · rintro rfl
      exact hj (by simp [hP, NoteHiding.Twin.test_true, sOf, Pre.K, twin])

omit [Fintype F] [DecidableEq F] [SampleableType F] [SampleableType G] [Fintype G]
  [Fintype Addr] [DecidableEq Addr] [SampleableType Key] [SampleableType Msg] [DecidableEq Msg] in
/-- Away from the false positives the trapdoor table is the programmed table. -/
theorem trapTable_eq_progTable {p : Pre G Addr (F × F) (G × G) Key Msg σ n}
    {t : Fin (n + 1) → F} (gB : G × G → Key) (κ : Fin (n + 1) → Key) {Z : G × G}
    (hZ : Z ∉ FP g pos coef p t) :
    trapTable p.cache gB (sOf p t) t (p.P pos coef) κ Z =
      progTable pos coef (twin F g) p gB κ Z := by
  simp only [trapTable, progTable, completeTable, override]
  congr 1
  refine overrideBy_congr _ _ fun j => ?_
  by_contra h
  exact hZ ⟨j, h⟩

/-- `hitProb` is the event `HitAll` of the programmed run with an independent trapdoor. -/
theorem hitProb_eq_progRunT :
    hitProb (twin F g) pos coef senc A = Pr{let x ← progRunT g pos coef senc A}[HitAll g pos coef x] := by
  simp only [hitProb, progRun, progRunT, prEvent_norm]
  refine prEvent_bind_congr' _ _ _ fun p => prEvent_bind_congr' _ _ _ fun gB =>
    prEvent_bind_congr' _ _ _ fun κ => ?_
  symm
  refine prEvent_bind_eq_of_forall _ _ fun t => ?_
  rfl

/-- A fixed pair other than `Kⱼ` passes the test of hidden `j` with probability at most `1/|F|`
over `tⱼ`. -/
theorem prob_fp_le (p : Pre G Addr (F × F) (G × G) Key Msg σ n) (Z : G × G) (j : Fin (n + 1)) :
    Pr{let t ← $ᵗ (Fin (n + 1) → F)}[p.hid pos coef j ∧
        NoteHiding.Twin.test (sOf p t j) (t j) (p.P pos coef j) Z = true ∧
          Z ≠ p.K pos coef (twin F g) j] ≤ (Fintype.card F : ℝ≥0∞)⁻¹ := by
  refine prEvent_uniform_fun_le_of_update j _ fun t => ?_
  simp only [sOf, Function.update_self, Pre.K, twin]
  by_cases hZ : Z.1 = (p.r j).1 • p.P pos coef j
  · refine le_of_eq_of_le (prEvent_eq_zero_of_forall_not _ _ fun x hx => ?_) zero_le
    refine hx.2.2 ?_
    have h := hx.2.1
    simp only [NoteHiding.Twin.test, decide_eq_true_eq, hZ] at h
    refine Prod.ext hZ ?_
    have : Z.2 = (x • ((p.r j).1 • p.P pos coef j) + Z.2) - (x * (p.r j).1) • p.P pos coef j := by
      module
    rw [this, h]
    module
  · exact (prEvent_mono _ _ _ fun x hx => hx.2.1).trans
      (NoteHiding.Twin.prob_test_le (p.r j).1 (p.r j).2 (p.P pos coef j) Z hZ)

/-- **False positives are rare.** For an adversary making at most `q₂` KDF queries in its
second phase, some logged pair or the point `(0, 0)` is a false positive with probability at
most `(n + 1) (q₂ + 1) / |F|`: the adversary's view does not depend on the trapdoor `t`. -/
theorem prob_not_noFP_le {q₁ q₂ : ℕ} (hq : A.QueryBound q₁ q₂) :
    Pr{let x ← progRunT g pos coef senc A}[¬NoFP g pos coef x] ≤
      ((n + 1) * (q₂ + 1) : ℕ) * (Fintype.card F : ℝ≥0∞)⁻¹ := by
  simp only [progRunT, prEvent_norm]
  refine prEvent_bind_le_of_forall _ _ fun p => prEvent_bind_le_of_forall _ _ fun gB =>
    prEvent_bind_le_of_forall _ _ fun κ => ?_
  rw [prEvent_bind_bind_swap_of_countable_left]
  refine prEvent_bind_le_of_forall_of_support _ _ fun z hz => ?_
  have hlen : (kdfPoints z.2).length ≤ q₂ :=
    length_kdfPoints_le_of_mem_support _ (hq.respond _ _) hz
  -- a false positive is a logged pair, or `(0, 0)`, accepted by the test of a hidden index
  refine le_trans (prEvent_mono _ _ (fun t => ∃ Z ∈ insert (0, 0) (kdfPoints z.2).toFinset,
    ∃ j, p.hid pos coef j ∧ NoteHiding.Twin.test (sOf p t j) (t j) (p.P pos coef j) Z = true ∧
      Z ≠ p.K pos coef (twin F g) j) fun t ht => ?_) ?_
  · simp only [NoFP, not_and_or, not_not] at ht
    rcases ht with ht | ht
    · simp only [LogAvoids, not_forall, exists_prop] at ht
      obtain ⟨e, he, Z, hZ, hFP⟩ := ht
      refine ⟨Z, Finset.mem_insert_of_mem (List.mem_toFinset.2 (mem_kdfPoints.2 ⟨?_, ?_⟩)),
        of_mem_FP g pos coef (not_not.1 hFP)⟩
      · exact cast (by rw [hZ]) e.2
      · obtain ⟨t', u⟩ := e
        cases hZ
        exact he
    · exact ⟨(0, 0), Finset.mem_insert_self _ _, of_mem_FP g pos coef ht⟩
  · refine (prEvent_exists_finset_le_card_mul _ _ _
      (ε := (n + 1 : ℕ) * (Fintype.card F : ℝ≥0∞)⁻¹) fun Z _ => ?_).trans ?_
    · exact (prEvent_exists_le_card_mul _ _ fun j => prob_fp_le g pos coef p Z j).trans
        (le_of_eq (by rw [Fintype.card_fin]))
    · have hcard : (insert (0, 0) (kdfPoints z.2).toFinset).card ≤ q₂ + 1 :=
        (Finset.card_insert_le _ _).trans (by
          have := (List.toFinset_card_le (kdfPoints z.2)).trans hlen
          omega)
      calc ((insert (0, 0) (kdfPoints z.2).toFinset).card : ℝ≥0∞) *
            ((n + 1 : ℕ) * (Fintype.card F : ℝ≥0∞)⁻¹)
          ≤ ((q₂ + 1 : ℕ) : ℝ≥0∞) * ((n + 1 : ℕ) * (Fintype.card F : ℝ≥0∞)⁻¹) := by
            gcongr
        _ = _ := by push_cast; ring

/-! ## The programmed run and the reduction's run agree without false positives -/

omit [Fintype F] [DecidableEq F] [SampleableType F] [SampleableType G] [Fintype G]
  [Fintype Addr] [DecidableEq Addr] [SampleableType Key] [SampleableType Msg] [DecidableEq Msg] in
/-- For a good prefix without a false positive at `(0, 0)`, the reduction's keys are the
programmed run's keys. -/
theorem trapKeys_eq_keysOf {p : Pre G Addr (F × F) (G × G) Key Msg σ n} {t : Fin (n + 1) → F}
    (hgood : p.Good pos coef (twin F g)) (h0 : (0, 0) ∉ FP g pos coef p t) (gB : G × G → Key)
    (κ : Fin (n + 1) → Key) :
    trapKeys pos coef p (trapTable p.cache gB (sOf p t) t (p.P pos coef) κ) κ =
      keysOf (twin F g) pos coef p (progTable pos coef (twin F g) p gB κ) := by
  funext i
  simp only [trapKeys, keysOf]
  by_cases hP : p.P pos coef i = 0
  · have hK : p.K pos coef (twin F g) i = (0, 0) := by simp [Pre.K, twin, hP]
    rw [if_pos hP, hK, trapTable_eq_progTable g pos coef gB κ h0]
  · have hinj : ∀ i j, p.hid pos coef i → p.hid pos coef j →
        p.K pos coef (twin F g) i = p.K pos coef (twin F g) j → i = j :=
      fun i j hi _ hij => by_contra fun hne => hgood.1 i j hi hne hij
    have hi : p.hid pos coef i := by simpa [Pre.hid] using hP
    rw [ite_eq_right hP]
    simp only [progTable, completeTable, hgood.2 i hi, Option.getD_none,
      override_hit _ _ _ _ hinj hi]

/-- Without false positives, the programmed run and the reduction's run agree. -/
theorem prob_progRunT_eq_trapRun :
    Pr{let x ← progRunT g pos coef senc A}[HitAll g pos coef x ∧ NoFP g pos coef x] =
      Pr{let x ← trapRun g pos coef senc A}[HitAll g pos coef x ∧ NoFP g pos coef x] := by
  simp only [progRunT, trapRun, prEvent_norm]
  refine prEvent_bind_congr' _ _ _ fun p => prEvent_bind_congr' _ _ _ fun gB =>
    prEvent_bind_congr' _ _ _ fun κ => prEvent_bind_congr' _ _ _ fun t => ?_
  by_cases hgood : p.Good pos coef (twin F g) ∧ (0, 0) ∉ FP g pos coef p t
  · rw [trapKeys_eq_keysOf g pos coef hgood.1 hgood.2]
    have h := tableRun_withQueryLog_eq_of_agree (S := FP g pos coef p t)
      (T := progTable pos coef (twin F g) p gB κ)
      (T' := trapTable p.cache gB (sOf p t) t (p.P pos coef) κ)
      (fun Z hZ => (trapTable_eq_progTable g pos coef gB κ hZ).symm)
      (A.respond p.c.2.2 fun i =>
        (senc (keysOf (twin F g) pos coef p (progTable pos coef (twin F g) p gB κ) i) (p.m i),
          (twin F g).eph (p.r i)))
      fun z => HitAll g pos coef ((p, z), t) ∧ (0, 0) ∉ FP g pos coef p t
    simp only [suffixRun]
    refine (prEvent_congr _ _ _ fun z => ?_).trans (h.trans (prEvent_congr _ _ _ fun z => ?_))
    · simp only [NoFP]
      tauto
    · simp only [NoFP]
      tauto
  · refine (prEvent_eq_zero_of_forall_not _ _ fun z hz => hgood ⟨hz.1.1, hz.2.2⟩).trans
      (prEvent_eq_zero_of_forall_not _ _ fun z hz => hgood ⟨hz.1.1, hz.2.2⟩).symm

/-- Without false positives, if every hidden point is queried the extraction is correct. -/
theorem winSS_of_hitAll {x : Outcome G Addr (F × F) (G × G) Key Msg σ n × (Fin (n + 1) → F)}
    (h : HitAll g pos coef x ∧ NoFP g pos coef x) : WinSS pos coef x := by
  obtain ⟨⟨p, z⟩, t⟩ := x
  obtain ⟨⟨hgood, hhit⟩, hlog, h0⟩ := h
  intro i
  simp only [extract]
  by_cases hP : p.P pos coef i = 0
  · simp [hP]
  · rw [ite_eq_right hP]
    have hi : p.hid pos coef i := by simpa [Pre.hid] using hP
    obtain ⟨u, hu⟩ := hhit i hi
    have hmem : p.K pos coef (twin F g) i ∈ kdfPoints z.2 := mem_kdfPoints.2 ⟨u, hu⟩
    have hsome : ((kdfPoints z.2).find?
        (NoteHiding.Twin.test (sOf p t i) (t i) (p.P pos coef i))).isSome :=
      List.find?_isSome.2 ⟨_, hmem, by
        simp [Pre.K, twin, sOf, NoteHiding.Twin.test_true]⟩
    obtain ⟨Z₀, hZ₀⟩ := Option.isSome_iff_exists.1 hsome
    have htest := List.find?_some hZ₀
    have hZ₀mem := List.mem_of_find?_eq_some hZ₀
    -- `Z₀` is logged, so it is not a false positive, so the recognizers agree at it
    have hnotFP : Z₀ ∉ FP g pos coef p t := by
      obtain ⟨u', hu'⟩ := mem_kdfPoints.1 hZ₀mem
      exact fun hFP => hlog _ hu' Z₀ rfl hFP
    have hagree : trapRec (sOf p t) t (p.P pos coef) i Z₀ =
        (p.hid pos coef i && decide (p.K pos coef (twin F g) i = Z₀)) := by
      by_contra h
      exact hnotFP ⟨i, h⟩
    simp only [trapRec, hP, ne_eq, not_false_eq_true, decide_true, Bool.true_and, htest, hi,
      true_eq_decide_iff] at hagree
    rw [hZ₀, Option.map_some, Option.getD_some, ← hagree]
    rfl

/-! ## The bound -/

/-- The twin variant is unpredictable: for `P ≠ 0` and uniform `(r₁, r₂)`, the pair
`(r₁ • P, r₂ • P)` takes any given value with probability at most `1/|F|`. -/
theorem twin_unpredictable : (twin F g).Unpredictable F := by
  intro P hP Z
  have hinj : Function.Injective fun r : F × F => ((twin F g).pt r P) := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    simp only [twin, Prod.mk.injEq] at h
    have h1 : (a - a') • P = 0 := by rw [sub_smul, h.1, sub_self]
    have h2 : (b - b') • P = 0 := by rw [sub_smul, h.2, sub_self]
    rw [Prod.mk.injEq]
    exact ⟨sub_eq_zero.1 ((smul_eq_zero.1 h1).resolve_right hP),
      sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right hP)⟩
  refine (SampleableType.prEvent_uniformSample_apply_eq_le hinj Z).trans ?_
  rw [Nat.card_prod, Nat.card_eq_fintype_card]
  refine ENNReal.inv_le_inv.2 ?_
  have : 1 ≤ Fintype.card F := Fintype.card_pos
  exact_mod_cast Nat.le_mul_of_pos_right _ this

/-- **The hit probability is bounded by the shared-secret game.** -/
theorem hitProb_le {q₁ q₂ : ℕ} (hq : A.QueryBound q₁ q₂) :
    hitProb (twin F g) pos coef senc A ≤
      𝒟[SharedSecret.experiment g pos coef (ssAdversary g pos coef senc A)] {true} +
        ((n + 1) * (q₂ + 1) : ℕ) * (Fintype.card F : ℝ≥0∞)⁻¹ := by
  rw [hitProb_eq_progRunT, prob_experiment_eq_trapRun]
  calc Pr{let x ← progRunT g pos coef senc A}[HitAll g pos coef x]
      = Pr{let x ← progRunT g pos coef senc A}[HitAll g pos coef x ∧ NoFP g pos coef x] +
          Pr{let x ← progRunT g pos coef senc A}[HitAll g pos coef x ∧ ¬NoFP g pos coef x] :=
        prEvent_eq_prEvent_and_add_prEvent_and_not _ _ _
    _ ≤ Pr{let x ← trapRun g pos coef senc A}[WinSS pos coef x] +
          ((n + 1) * (q₂ + 1) : ℕ) * (Fintype.card F : ℝ≥0∞)⁻¹ := by
        gcongr
        · rw [prob_progRunT_eq_trapRun]
          exact prEvent_mono _ _ _ fun x hx => winSS_of_hitAll g pos coef hx
        · exact (prEvent_and_le_right _ _ _).trans (prob_not_noFP_le g pos coef senc A hq)

/-- **Theorem 3 for the twin variant, decryption game, random-oracle KDF, no algebraic group
model** (option 3). For a generator `g`, an adversary that outputs an arbitrary vector `V` and
`n + 1` distinct addresses, makes at most `q₁` KDF queries before and `q₂` after receiving the
ciphertexts, decrypts all `n + 1` ciphertexts with probability at most
`((n + 1) q₁ + (n + 1) n) / |F|` (a bad prefix), plus the CDH success probability of
`cdhReduction` plus `1/|F|` plus `(n + 1)(q₂ + 1)/|F|` (the trapdoor tests), plus, for each
ciphertext, the one-time advantage of `otReduction` against the cipher plus `1/|Msg|`. -/
theorem experiment_le [Inhabited Msg] [Fintype Msg] {g : G}
    (hg : Function.Bijective (· • g : F → G)) {q₁ q₂ : ℕ} (hq : A.QueryBound q₁ q₂) :
    𝒟[Twin.experiment g pos coef senc A] {true} ≤
      ((n + 1) * q₁ + (n + 1) * n : ℕ) * (Fintype.card F : ℝ≥0∞)⁻¹ +
        (𝒟[cdhExperiment g (cdhReduction g pos coef senc A)] {true} +
          (Fintype.card F : ℝ≥0∞)⁻¹ + ((n + 1) * (q₂ + 1) : ℕ) * (Fintype.card F : ℝ≥0∞)⁻¹) +
        ∑ i, (otAdvantage senc (otReduction (twin F g) pos coef senc A i) +
          (Fintype.card Msg : ℝ≥0∞)⁻¹) := by
  refine (experiment_le_hitProb_add (twin F g) pos coef senc A (twin_unpredictable g) hq).trans ?_
  gcongr
  refine (hitProb_le g pos coef senc A hq).trans ?_
  gcongr
  exact SharedSecret.success_le hg pos coef (ssAdversary g pos coef senc A)

end AuditPay.Monitoring.Twin
