/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.KdfRO.Monitoring.Defs
import AuditPay.RestrictedMonitoring.Decrypt.Split
import VCVio.EvalDist.Monad.Disagreement.Measure

/-!
# Theorem 3, decryption game with a random-oracle KDF: the generic decomposition

For any variant of selective encryption, the probability of decrypting all `n + 1` ciphertexts
is at most

  `Pr[bad prefix] + hitProb + ∑ᵢ (OT(otReduction A i) + 1/|Msg|)`,

where `hitProb` is the probability, in the *programmed* run, that the adversary queries the KDF
at every hidden shared point. The programmed run replaces the KDF table at the hidden points
`Kᵢ` (those with `Pᵢ ≠ 0`) by fresh keys `κᵢ` and encrypts with them; for a good prefix it is the
real run (`prob_real_eq_prog`, by `KdfRO.override_uniform`), and it is the run that the
reductions of `AuditPay.Monitoring.StrongDH` and `AuditPay.Monitoring.Twin` simulate. A prefix is
*bad* if two shared points coincide (with one hidden) or a hidden point was already queried in
the first phase; both have probability `O(n (n + q₁) / |F|)` (`prob_not_good_le`).

If the adversary does not query a hidden `Kᵢ`, then `κᵢ` is used only in ciphertext `i`
(`prob_miss_le_fresh`, by `KdfRO.tableRun_withQueryLog_eq_of_agree`), and one-time security of
the cipher makes `mᵢ` unguessable (`prob_fresh_le_ot`).
-/

open OracleComp OracleSpec ENNReal

namespace AuditPay.Monitoring

open KdfRO SLIND

variable {F G Addr ρ E X Key Msg C σ : Type} {k n : ℕ} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq Msg]
  (S : Variant G ρ E X) (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F)
  (senc : Key → Msg → C) (A : Adversary G Addr E X Key Msg C σ n)

/-- The keys of the ciphertexts, read from a table. -/
def keysOf (p : Pre G Addr ρ X Key Msg σ n) (T : X → Key) : Fin (n + 1) → Key :=
  fun i => T (p.K pos coef S i)

/-! ## The experiment as a prefix and an eager suffix -/

/-- Against a table, the suffix of the game reads the keys from the table and runs the second
phase (logged). -/
theorem tableRun_suffix (T : X → Key) (p : Pre G Addr ρ X Key Msg σ n) :
    tableRun T (S.monitoringSuffix pos coef senc A p.H p.c p.r p.m) =
      (do let z ← suffixRun S senc A p T (keysOf S pos coef p T); pure (decide (Win p z))) := by
  simp only [Variant.monitoringSuffix, tableRun_bind, tableRun_queryFin, pure_bind, suffixRun]
  conv_lhs => rw [← loggingOracle.fst_map_run_simulateQ (A.respond _ _)]
  simp only [tableRun_map, bind_map_left]
  rfl

/-- The experiment is the prefix followed by the suffix against a uniform table completing the
prefix's cache. -/
theorem prob_experiment_eq [SampleableType G] [Fintype Addr] [DecidableEq Addr]
    [SampleableType ρ] [DecidableEq X] [Fintype X] [SampleableType Key] [SampleableType Msg] :
    𝒟[S.monitoringExperiment pos coef senc A] {true} =
      Pr{let p ← prefixRun A
         let g ← $ᵗ (X → Key)
         let z ← suffixRun S senc A p (completeTable p.cache g)
           (keysOf S pos coef p (completeTable p.cache g))}[Win p z] := by
  rw [← prEvent_eq_evalDist_singleton]
  have h : S.monitoringExperiment pos coef senc A =ᵈ (do
      let p ← prefixRun A; let g ← $ᵗ (X → Key)
      let z ← suffixRun S senc A p (completeTable p.cache g)
        (keysOf S pos coef p (completeTable p.cache g))
      pure (decide (Win p z))) := by
    simp only [Variant.monitoringExperiment, Variant.monitoringGame, roExec_eq, prefixRun,
      roRun_bind, roRun_liftM, bind_map_left, map_bind, bind_assoc, pure_bind]
    refine EvalDistEq.bind_right _ fun H => EvalDistEq.bind_right _ fun z =>
      EvalDistEq.bind_right _ fun r => EvalDistEq.bind_right _ fun m => ?_
    let : MeasurableSpace Bool := ⊤
    refine (EvalDistEq.of_evalDist_eq (evalDist_roRun_eq_tableRun
      (S.monitoringSuffix pos coef senc A H z.1 r m) z.2)).trans ?_
    refine EvalDistEq.bind_right _ fun g => ?_
    rw [tableRun_suffix S pos coef senc A (completeTable z.2 g) ⟨H, z.1, z.2, r, m⟩]
  rw [h.prEvent_eq]
  simp only [prEvent_norm, decide_eq_true_eq]

/-! ## The real, programmed and fresh runs -/

section Runs

variable [SampleableType G] [Fintype Addr] [DecidableEq Addr] [SampleableType ρ] [DecidableEq X]
  [Fintype X] [SampleableType Key] [SampleableType Msg] [DecidableEq G]

/-- The outcome of a run: the prefix and the second phase's outcome. -/
abbrev Outcome (G Addr ρ X Key Msg σ : Type) (n : ℕ) :=
  Pre G Addr ρ X Key Msg σ n × ((Fin (n + 1) → Msg) × QueryLog (unifSpec + (X →ₒ Key)))

/-- The real run: the prefix, a uniform table completing its cache, the suffix against it. -/
noncomputable def realRun : ProbComp (Outcome G Addr ρ X Key Msg σ n) :=
  prefixRun A >>= fun p => (fun z => (p, z)) <$> ($ᵗ (X → Key) >>= fun g =>
    suffixRun S senc A p (completeTable p.cache g) (keysOf S pos coef p (completeTable p.cache g)))

/-- The programmed run: the prefix, a uniform table completing its cache with fresh keys at the
hidden points, the suffix against it. -/
noncomputable def progRun : ProbComp (Outcome G Addr ρ X Key Msg σ n) :=
  prefixRun A >>= fun p => (fun z => (p, z)) <$> ($ᵗ (X → Key) >>= fun g =>
    $ᵗ (Fin (n + 1) → Key) >>= fun κ =>
      suffixRun S senc A p (progTable pos coef S p g κ)
        (keysOf S pos coef p (progTable pos coef S p g κ)))

/-- The run with a fresh key for ciphertext `i`: the prefix, a uniform table completing its
cache, the suffix against it with the key of ciphertext `i` replaced by a fresh key. -/
noncomputable def freshRun (i : Fin (n + 1)) : ProbComp (Outcome G Addr ρ X Key Msg σ n) :=
  prefixRun A >>= fun p => (fun z => (p, z)) <$> ($ᵗ (X → Key) >>= fun g =>
    $ᵗ Key >>= fun κ' =>
      suffixRun S senc A p (completeTable p.cache g)
        (Function.update (keysOf S pos coef p (completeTable p.cache g)) i κ'))

theorem prob_experiment_eq_realRun :
    𝒟[S.monitoringExperiment pos coef senc A] {true} =
      Pr{let w ← realRun S pos coef senc A}[Win w.1 w.2] := by
  rw [prob_experiment_eq]
  simp only [realRun, prEvent_norm]

/-- On good prefixes, the real and the programmed runs agree: overriding a uniform table at
distinct points by independent uniform keys leaves it uniform. -/
theorem prob_realRun_eq_progRun (E : Outcome G Addr ρ X Key Msg σ n → Prop) :
    Pr{let w ← realRun S pos coef senc A}[E w ∧ w.1.Good pos coef S] =
      Pr{let w ← progRun S pos coef senc A}[E w ∧ w.1.Good pos coef S] := by
  simp only [realRun, progRun]
  refine prEvent_bind_congr _ _ _ _ _ fun p => ?_
  rw [prEvent_map, prEvent_map]
  by_cases hgood : p.Good pos coef S
  · have hinj : ∀ i j, p.hid pos coef i → p.hid pos coef j →
        p.K pos coef S i = p.K pos coef S j → i = j :=
      fun i j hi _ hij => by_contra fun hne => hgood.1 i j hi hne hij
    have h := override_uniform (X := X) (Key := Key) (p.K pos coef S) (p.hid pos coef) hinj
      fun T => suffixRun S senc A p (completeTable p.cache T)
        (keysOf S pos coef p (completeTable p.cache T))
    refine ((EvalDistEq.bind_right _ fun g => (bind_const_eqd _ _).symm).trans h.symm).prEvent_eq
      fun z => E (p, z) ∧ p.Good pos coef S
  · simp only [hgood, and_false, prEvent_false]

/-- The programmed run decomposes: either every hidden point is queried, or some hidden point is
not queried and the adversary still wins. -/
theorem prob_progRun_le_hit_add_sum :
    Pr{let w ← progRun S pos coef senc A}[Win w.1 w.2 ∧ w.1.Good pos coef S] ≤
      Pr{let w ← progRun S pos coef senc A}[w.1.Good pos coef S ∧
          ∀ i, w.1.hid pos coef i → Hit (w.1.K pos coef S i) w.2] +
        ∑ i, Pr{let w ← progRun S pos coef senc A}[Win w.1 w.2 ∧ w.1.Good pos coef S ∧
          w.1.hid pos coef i ∧ ¬Hit (w.1.K pos coef S i) w.2] := by
  refine le_trans (prEvent_mono _ _ (fun w => (w.1.Good pos coef S ∧
      ∀ i, w.1.hid pos coef i → Hit (w.1.K pos coef S i) w.2) ∨
      ∃ i, Win w.1 w.2 ∧ w.1.Good pos coef S ∧ w.1.hid pos coef i ∧
        ¬Hit (w.1.K pos coef S i) w.2) fun w hw => ?_) ?_
  · by_cases hall : ∀ i, w.1.hid pos coef i → Hit (w.1.K pos coef S i) w.2
    · exact Or.inl ⟨hw.2, hall⟩
    · push Not at hall
      obtain ⟨i, hi, hmiss⟩ := hall
      exact Or.inr ⟨i, hw.1, hw.2, hi, hmiss⟩
  · exact (prEvent_or_le _ _ _).trans (add_le_add le_rfl (prEvent_exists_le _ _))

/-! ## Un-programming one hidden point -/

/-- For a good prefix and a hidden index `i`, the programmed table's values at the shared points
are the keys `κ`, so changing `κ i` changes exactly the key of ciphertext `i`. -/
theorem keysOf_progTable_update {p : Pre G Addr ρ X Key Msg σ n} (hgood : p.Good pos coef S)
    {i : Fin (n + 1)} (hi : p.hid pos coef i) (g : X → Key) (κ : Fin (n + 1) → Key) (κ' : Key) :
    keysOf S pos coef p (progTable pos coef S p g (Function.update κ i κ')) =
      Function.update (keysOf S pos coef p (progTable pos coef S p g κ)) i κ' := by
  have hinj : ∀ i j, p.hid pos coef i → p.hid pos coef j →
      p.K pos coef S i = p.K pos coef S j → i = j :=
    fun i j hi _ hij => by_contra fun hne => hgood.1 i j hi hne hij
  funext j
  by_cases hj : j = i
  · subst hj
    simp only [keysOf, progTable, completeTable, hgood.2 j hi, Option.getD_none,
      Function.update_self, override_hit _ _ _ _ hinj hi]
  · have hne : p.K pos coef S j ≠ p.K pos coef S i :=
      fun h => hgood.1 i j hi (Ne.symm hj) h.symm
    simp only [keysOf, progTable, completeTable, Function.update_of_ne hj,
      override_update_of_ne _ _ _ _ _ _ hne]

/-- Changing the key of index `i` changes the programmed table only at `K i`. -/
theorem progTable_update_of_ne (p : Pre G Addr ρ X Key Msg σ n) (g : X → Key)
    (κ : Fin (n + 1) → Key) (i : Fin (n + 1)) (κ' : Key) {Z : X} (hZ : Z ≠ p.K pos coef S i) :
    progTable pos coef S p g (Function.update κ i κ') Z = progTable pos coef S p g κ Z := by
  simp only [progTable, completeTable, override_update_of_ne _ _ _ _ _ _ hZ]

omit [DecidableEq X] in
theorem not_hit_iff_logAvoids (Z : X)
    (z : (Fin (n + 1) → Msg) × QueryLog (unifSpec + (X →ₒ Key))) :
    ¬Hit Z z ↔ LogAvoids {Z} z.2 := by
  simp only [Hit, LogAvoids, Set.mem_singleton_iff, not_exists]
  constructor
  · rintro h ⟨t, u⟩ he Z' hZ' rfl
    cases hZ'
    exact h u he
  · intro h u he
    exact h _ he Z rfl rfl

/-- **Un-programming.** If the adversary does not query the hidden point `K i` in the programmed
run, the key `κ i` is used only in ciphertext `i`; replacing it by an independent key costs
nothing. -/
theorem prob_miss_le_fresh (i : Fin (n + 1)) :
    Pr{let w ← progRun S pos coef senc A}[Win w.1 w.2 ∧ w.1.Good pos coef S ∧
        w.1.hid pos coef i ∧ ¬Hit (w.1.K pos coef S i) w.2] ≤
      Pr{let w ← freshRun S pos coef senc A i}[w.2.1 i = w.1.m i] := by
  simp only [progRun, freshRun]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun p => ?_
  rw [prEvent_map, prEvent_map]
  by_cases hgi : p.Good pos coef S ∧ p.hid pos coef i
  · obtain ⟨hgood, hi⟩ := hgi
    -- the inner computation with a fresh key for `i`, as a function of the table
    let k : (X → Key) → ProbComp ((Fin (n + 1) → Msg) × QueryLog (unifSpec + (X →ₒ Key))) :=
      fun T => $ᵗ Key >>= fun κ' => suffixRun S senc A p (completeTable p.cache T)
        (Function.update (keysOf S pos coef p (completeTable p.cache T)) i κ')
    have hinj : ∀ i j, p.hid pos coef i → p.hid pos coef j →
        p.K pos coef S i = p.K pos coef S j → i = j :=
      fun i j hi _ hij => by_contra fun hne => hgood.1 i j hi hne hij
    have hover := override_uniform (X := X) (Key := Key) (p.K pos coef S) (p.hid pos coef) hinj k
    -- the right-hand side, with an unused `κ` inserted, is the overridden run
    refine le_of_le_of_eq ?_ (((EvalDistEq.bind_right _ fun g => (bind_const_eqd _ _).symm).trans
      hover.symm).prEvent_eq fun z => z.1 i = p.m i).symm
    refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun g => ?_
    simp only [k]
    -- rename `κ i` to the fresh key `κ'`
    refine le_of_eq_of_le ((RestrictedMonitoring.Decrypt.uniform_update_eqd i fun κ =>
      suffixRun S senc A p (progTable pos coef S p g κ)
        (keysOf S pos coef p (progTable pos coef S p g κ))).symm.prEvent_eq _) ?_
    have hkeys : ∀ (κ : Fin (n + 1) → Key) (κ' : Key),
        keysOf S pos coef p (progTable pos coef S p g (Function.update κ i κ')) =
          Function.update (keysOf S pos coef p (progTable pos coef S p g κ)) i κ' :=
      fun κ κ' => keysOf_progTable_update S pos coef hgood hi g κ κ'
    simp only [hkeys]
    refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun κ => ?_
    refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun κ' => ?_
    -- the two tables agree away from `K i`, which is not queried
    have hagree := tableRun_withQueryLog_eq_of_agree (S := {p.K pos coef S i})
      (T := progTable pos coef S p g (Function.update κ i κ')) (T' := progTable pos coef S p g κ)
      (fun Z hZ => progTable_update_of_ne S pos coef p g κ i κ' hZ)
      (A.respond p.c.2.2 fun j => (senc (Function.update
        (keysOf S pos coef p (progTable pos coef S p g κ)) i κ' j) (p.m j), S.eph (p.r j)))
      fun z => Win p z ∧ p.Good pos coef S ∧ p.hid pos coef i
    simp only [suffixRun]
    refine le_trans (le_of_eq ?_) ((le_of_eq hagree).trans (prEvent_mono _ _ _ fun z hz => ?_))
    · exact prEvent_congr _ _ _ fun z => by
        rw [← not_hit_iff_logAvoids]
        tauto
    · exact hz.1.1 i
  · refine le_of_eq_of_le ?_ zero_le
    refine prEvent_eq_zero_of_forall_not _ _ fun z h => hgi ⟨h.2.1, h.2.2.1⟩

/-! ## One-time security of ciphertext `i` -/

/-- The ciphertexts with the key of ciphertext `i` replaced, as an update of the vector of
ciphertexts. -/
theorem update_keys_eq (r : Fin (n + 1) → ρ) (m : Fin (n + 1) → Msg) (keys : Fin (n + 1) → Key)
    (i : Fin (n + 1)) (κ' : Key) :
    (fun j => (senc (Function.update keys i κ' j) (m j), S.eph (r j))) =
      Function.update (fun j => (senc (keys j) (m j), S.eph (r j))) i
        (senc κ' (m i), S.eph (r i)) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [Function.update_of_ne hj]

/-- The suffix of the game with a fresh key for ciphertext `i` and the message `μ` in it, as an
oracle computation; its verdict is whether the adversary's guess for `mᵢ` is `mᵢ`. -/
def freshSuffix (i : Fin (n + 1)) (H : Addr → G) (c : Commit G Addr σ n) (r : Fin (n + 1) → ρ)
    (m : Fin (n + 1) → Msg) (μ : Msg) : OracleComp (unifSpec + (X →ₒ Key)) Bool := do
  let keys ← queryFin fun j => S.pt (r j) (pts pos coef H c j)
  let key ← $ᵗ Key
  let m' ← A.respond c.2.2 (Function.update (fun j => (senc (keys j) (m j), S.eph (r j))) i
    (senc key μ, S.eph (r i)))
  return decide (m' i = m i)

/-- The reduction to one-time security of the cipher for ciphertext `i`: it runs the game with a
lazily sampled KDF of its own, submits the message `mᵢ` and a fixed default message, places the
challenge ciphertext in slot `i`, and outputs whether the adversary's guess for `mᵢ` is `mᵢ`. -/
noncomputable def otReduction [Inhabited Msg] (i : Fin (n + 1)) :
    OTAdversary Msg C (Pre G Addr ρ X Key Msg σ n × (Fin (n + 1) → Key) ×
      (X →ₒ Key).QueryCache) where
  choose := do
    let H ← $ᵗ (Addr → G)
    let z ← roRun (A.commit H) ∅
    let r ← $ᵗ (Fin (n + 1) → ρ)
    let m ← $ᵗ (Fin (n + 1) → Msg)
    let w ← roRun (queryFin fun j => S.pt (r j) (pts pos coef H z.1 j)) z.2
    return (m i, default, (⟨H, z.1, z.2, r, m⟩, w.1, w.2))
  guess st ct := do
    let v ← roRun (A.respond st.1.c.2.2 (Function.update
      (fun j => (senc (st.2.1 j) (st.1.m j), S.eph (st.1.r j))) i (ct, S.eph (st.1.r i)))) st.2.2
    return decide (v.1 i = st.1.m i)

/-- The one-time experiment of `otReduction i` for bit `b` is the game with the message `mᵢ`
(`b = false`) or the default message (`b = true`) encrypted under a fresh key in slot `i`. -/
theorem otExperiment_eqd [Inhabited Msg] (i : Fin (n + 1)) (b : Bool) :
    otExperiment senc (otReduction S pos coef senc A i) b =ᵈ (do
      let H ← $ᵗ (Addr → G)
      let z ← roRun (A.commit H) ∅
      let r ← $ᵗ (Fin (n + 1) → ρ)
      let m ← $ᵗ (Fin (n + 1) → Msg)
      Prod.fst <$> roRun (freshSuffix S pos coef senc A i H z.1 r m
        (if b then default else m i)) z.2) := by
  simp only [otExperiment, otReduction, freshSuffix, roRun_bind, roRun_liftM, bind_map_left,
    map_bind, bind_assoc, pure_bind, roRun_pure, map_pure]
  exact .rfl

/-- The one-time experiment for `b = false` is the fresh run. -/
theorem prob_otExperiment_false [Inhabited Msg] (i : Fin (n + 1)) :
    𝒟[otExperiment senc (otReduction S pos coef senc A i) false] {true} =
      Pr{let w ← freshRun S pos coef senc A i}[w.2.1 i = w.1.m i] := by
  rw [← prEvent_eq_evalDist_singleton, (otExperiment_eqd S pos coef senc A i false).prEvent_eq]
  simp only [freshRun, prefixRun, bind_assoc, pure_bind, Bool.false_eq_true, ite_false]
  refine prEvent_bind_congr _ _ _ _ _ fun H => prEvent_bind_congr _ _ _ _ _ fun z =>
    prEvent_bind_congr _ _ _ _ _ fun r => prEvent_bind_congr _ _ _ _ _ fun m => ?_
  let : MeasurableSpace Bool := ⊤
  refine ((EvalDistEq.of_evalDist_eq (evalDist_roRun_eq_tableRun
    (freshSuffix S pos coef senc A i H z.1 r m (m i)) z.2)).prEvent_eq _).trans ?_
  rw [prEvent_map]
  simp only [freshSuffix, tableRun_bind, tableRun_queryFin, pure_bind, tableRun_liftM,
    tableRun_pure]
  refine prEvent_bind_congr _ _ _ _ _ fun g => prEvent_bind_congr _ _ _ _ _ fun κ' => ?_
  simp only [suffixRun, keysOf, update_keys_eq]
  conv_lhs => rw [← loggingOracle.fst_map_run_simulateQ (A.respond _ _)]
  simp only [tableRun_map, prEvent_norm, decide_eq_true_eq]
  rfl

/-- Replacing the message of slot `i` does not change the ciphertexts when slot `i` is
overwritten. -/
theorem update_msg_vec (r : Fin (n + 1) → ρ) (m : Fin (n + 1) → Msg) (keys : Fin (n + 1) → Key)
    (i : Fin (n + 1)) (μ : Msg) (ct : C × E) :
    Function.update (fun j => (senc (keys j) (Function.update m i μ j), S.eph (r j))) i ct =
      Function.update (fun j => (senc (keys j) (m j), S.eph (r j))) i ct := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [Function.update_of_ne hj]

/-- In the one-time experiment for `b = true` the message `mᵢ` is independent of the adversary's
view, so it is guessed with probability `1/|Msg|`. -/
theorem prob_otExperiment_true [Inhabited Msg] [Fintype Msg] (i : Fin (n + 1)) :
    𝒟[otExperiment senc (otReduction S pos coef senc A i) true] {true} =
      (Fintype.card Msg : ℝ≥0∞)⁻¹ := by
  rw [← prEvent_eq_evalDist_singleton, (otExperiment_eqd S pos coef senc A i true).prEvent_eq]
  simp only [ite_true]
  refine prEvent_bind_eq_of_forall_eq _ (prEvent_true_eq_one _) _ _ fun H => ?_
  refine prEvent_bind_eq_of_forall_eq _ (prEvent_true_eq_one _) _ _ fun z => ?_
  refine prEvent_bind_eq_of_forall_eq _ (prEvent_true_eq_one _) _ _ fun r => ?_
  rw [← (RestrictedMonitoring.Decrypt.uniform_update_eqd i _).prEvent_eq]
  refine prEvent_bind_eq_of_forall_eq _ (prEvent_true_eq_one _) _ _ fun m => ?_
  simp only [freshSuffix, roRun_bind, roRun_liftM, bind_map_left, map_bind, bind_assoc,
    pure_bind, roRun_pure, map_pure, update_msg_vec, Function.update_self]
  -- move the fresh message to the end
  rw [prEvent_bind_swap]
  refine prEvent_bind_eq_of_forall _ _ fun w => ?_
  rw [prEvent_bind_swap]
  refine prEvent_bind_eq_of_forall _ _ fun key => ?_
  rw [prEvent_bind_swap]
  refine prEvent_bind_eq_of_forall _ _ fun v => ?_
  simp only [prEvent_norm, decide_eq_true_eq]
  exact SampleableType.prEvent_uniformSample_eq_singleton' _

/-- **One-time security of ciphertext `i`.** -/
theorem prob_fresh_le_ot [Inhabited Msg] [Fintype Msg] (i : Fin (n + 1)) :
    Pr{let w ← freshRun S pos coef senc A i}[w.2.1 i = w.1.m i] ≤
      otAdvantage senc (otReduction S pos coef senc A i) + (Fintype.card Msg : ℝ≥0∞)⁻¹ := by
  rw [← prob_otExperiment_false, otAdvantage, ← prob_otExperiment_true S pos coef senc A i]
  exact (MeasureTheory.Measure.apply_true_le_add_boolDist _ _).trans (le_of_eq (add_comm _ _))

end Runs

/-! ## Bad prefixes -/

/-- A variant is *unpredictable* if, for `P ≠ 0`, the KDF input `S.pt r P` for uniform
ephemeral randomness `r` takes any given value with probability at most `1/|F|`. -/
def _root_.AuditPay.KdfRO.Variant.Unpredictable (S : Variant G ρ E X) (F : Type) [Fintype F]
    [SampleableType ρ] : Prop :=
  ∀ P : G, P ≠ 0 → ∀ Z : X, Pr{let r ← $ᵗ ρ}[S.pt r P = Z] ≤ (Fintype.card F : ℝ≥0∞)⁻¹

section Bad

variable [Fintype F] [SampleableType G] [Fintype Addr] [DecidableEq Addr] [SampleableType ρ]
  [DecidableEq X] [Fintype X] [SampleableType Key] [SampleableType Msg] [DecidableEq G]

/-- Two shared points, one of them hidden, coincide with probability at most `1/|F|`. -/
theorem prob_coll_le (hS : S.Unpredictable F) (H : Addr → G) (c : Commit G Addr σ n)
    (cache : (X →ₒ Key).QueryCache) (m : Fin (n + 1) → Msg) {i j : Fin (n + 1)} (hij : i ≠ j) :
    Pr{let r ← $ᵗ (Fin (n + 1) → ρ)}[(⟨H, c, cache, r, m⟩ : Pre G Addr ρ X Key Msg σ n).hid
        pos coef i ∧ (⟨H, c, cache, r, m⟩ : Pre G Addr ρ X Key Msg σ n).K pos coef S i =
          (⟨H, c, cache, r, m⟩ : Pre G Addr ρ X Key Msg σ n).K pos coef S j] ≤
      (Fintype.card F : ℝ≥0∞)⁻¹ := by
  refine prEvent_uniform_fun_le_of_update i _ fun r => ?_
  simp only [Pre.hid, Pre.K, Pre.P, Function.update_self, Function.update_of_ne (Ne.symm hij),
    decide_eq_true_eq]
  by_cases hP : pts pos coef H c i = 0
  · simp [hP]
  · exact (prEvent_mono _ _ _ fun x hx => hx.2).trans (hS _ hP _)

/-- A hidden shared point was queried in the first phase with probability at most `q₁/|F|`. -/
theorem prob_pre_le (hS : S.Unpredictable F) (H : Addr → G) (c : Commit G Addr σ n)
    {cache : (X →ₒ Key).QueryCache} {q₁ : ℕ} (hc : (cachedPoints cache).length ≤ q₁)
    (m : Fin (n + 1) → Msg) (i : Fin (n + 1)) :
    Pr{let r ← $ᵗ (Fin (n + 1) → ρ)}[(⟨H, c, cache, r, m⟩ : Pre G Addr ρ X Key Msg σ n).hid
        pos coef i ∧ (cache ((⟨H, c, cache, r, m⟩ : Pre G Addr ρ X Key Msg σ n).K pos coef S
          i)).isSome] ≤ q₁ * (Fintype.card F : ℝ≥0∞)⁻¹ := by
  refine prEvent_uniform_fun_le_of_update i _ fun r => ?_
  simp only [Pre.hid, Pre.K, Pre.P, decide_eq_true_eq]
  by_cases hP : pts pos coef H c i = 0
  · simp [hP]
  · refine (prEvent_mono _ _ (fun x => ∃ Z ∈ (cachedPoints cache).toFinset,
      S.pt x (pts pos coef H c i) = Z) fun x hx => ?_).trans ?_
    · refine ⟨_, List.mem_toFinset.2 (mem_cachedPoints.2 hx.2), ?_⟩
      simp
    · refine (prEvent_exists_finset_le_card_mul _ _ _ fun Z _ => hS _ hP Z).trans ?_
      gcongr
      exact_mod_cast (List.toFinset_card_le _).trans hc

/-- **Bad prefixes are rare.** For an unpredictable variant and an adversary making at most `q₁`
KDF queries in its first phase, the prefix is bad with probability at most
`((n + 1) q₁ + (n + 1) n) / |F|`. -/
theorem prob_not_good_le (hS : S.Unpredictable F) {q₁ q₂ : ℕ} (hq : A.QueryBound q₁ q₂) :
    Pr{let p ← prefixRun A}[¬p.Good pos coef S] ≤
      ((n + 1) * q₁ + (n + 1) * n : ℕ) * (Fintype.card F : ℝ≥0∞)⁻¹ := by
  simp only [prefixRun]
  refine prEvent_bind_le_of_forall_le _ _ _ fun H => ?_
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun z hz => ?_
  have hc : (cachedPoints z.2).length ≤ q₁ := by
    have h1 := toSet_encard_le_of_mem_support_roRun (hq.commit H) hz
    rw [QueryCache.toSet_empty, Set.encard_empty, zero_add] at h1
    exact_mod_cast (length_cachedPoints_le z.2).trans h1
  -- the messages play no role: sample them first
  simp only [prEvent_norm]
  rw [prEvent_bind_bind_swap_of_countable_left]
  refine prEvent_bind_le_of_forall _ _ fun m => ?_
  refine le_trans (prEvent_mono _ _ (fun r =>
    (∃ i, (⟨H, z.1, z.2, r, m⟩ : Pre G Addr ρ X Key Msg σ n).hid pos coef i ∧
      (z.2 ((⟨H, z.1, z.2, r, m⟩ : Pre G Addr ρ X Key Msg σ n).K pos coef S i)).isSome) ∨
    ∃ i, ∃ j ∈ Finset.univ.erase i,
      (⟨H, z.1, z.2, r, m⟩ : Pre G Addr ρ X Key Msg σ n).hid pos coef i ∧
        (⟨H, z.1, z.2, r, m⟩ : Pre G Addr ρ X Key Msg σ n).K pos coef S i =
          (⟨H, z.1, z.2, r, m⟩ : Pre G Addr ρ X Key Msg σ n).K pos coef S j) fun r hr => ?_) ?_
  · simp only [Pre.Good, not_and_or, not_forall, not_not, exists_prop] at hr
    rcases hr with ⟨i, j, hi, hij, hK⟩ | ⟨i, hi, hcache⟩
    · exact Or.inr ⟨i, j, Finset.mem_erase.2 ⟨Ne.symm hij, Finset.mem_univ j⟩, hi, hK⟩
    · exact Or.inl ⟨i, hi, Option.isSome_iff_ne_none.2 hcache⟩
  · refine (prEvent_or_le _ _ _).trans ?_
    push_cast
    rw [add_mul]
    refine add_le_add ?_ ?_
    · refine (prEvent_exists_le_card_mul _ _ fun i => prob_pre_le S pos coef hS H z.1 hc m i).trans
        (le_of_eq ?_)
      rw [Fintype.card_fin, mul_assoc]
      push_cast
      ring
    · refine (prEvent_exists_le_card_mul _ _ (ε := n * (Fintype.card F : ℝ≥0∞)⁻¹)
        fun i => ?_).trans (le_of_eq ?_)
      · refine (prEvent_exists_finset_le_card_mul _ _ _ fun j hj =>
          prob_coll_le S pos coef hS H z.1 z.2 m (Finset.ne_of_mem_erase hj).symm).trans
          (le_of_eq ?_)
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
          Nat.add_sub_cancel]
      · rw [Fintype.card_fin]
        push_cast
        ring

end Bad

/-! ## The generic bound -/

section Generic

variable [Fintype F] [SampleableType G] [Fintype Addr] [DecidableEq Addr] [SampleableType ρ]
  [DecidableEq X] [Fintype X] [SampleableType Key] [SampleableType Msg] [DecidableEq G]

/-- The probability that, in the programmed run, the prefix is good and the adversary queries
the KDF at every hidden shared point. The reductions of `AuditPay.Monitoring.StrongDH` and
`AuditPay.Monitoring.Twin` bound it. -/
noncomputable def hitProb : ℝ≥0∞ :=
  Pr{let w ← progRun S pos coef senc A}[w.1.Good pos coef S ∧
    ∀ i, w.1.hid pos coef i → Hit (w.1.K pos coef S i) w.2]

/-- The real run's prefix is bad exactly as often as the prefix. -/
theorem prob_realRun_not_good_le :
    Pr{let w ← realRun S pos coef senc A}[¬w.1.Good pos coef S] ≤
      Pr{let p ← prefixRun A}[¬p.Good pos coef S] := by
  simp only [realRun]
  refine prEvent_bind_le_prEvent_of_forall_eq_zero _ _ _ _ fun p hp => ?_
  rw [prEvent_map]
  exact prEvent_eq_zero_of_forall_not _ _ fun z h => h (not_not.1 hp)

/-- **The generic bound.** For an unpredictable variant and an adversary making at most `q₁` KDF
queries in its first phase, the probability of decrypting all `n + 1` ciphertexts is at most the
probability of a bad prefix, plus the probability that every hidden shared point is queried in
the programmed run, plus, for each ciphertext, the one-time advantage of `otReduction` and
`1/|Msg|`. -/
theorem experiment_le_hitProb_add [Inhabited Msg] [Fintype Msg] (hS : S.Unpredictable F)
    {q₁ q₂ : ℕ} (hq : A.QueryBound q₁ q₂) :
    𝒟[S.monitoringExperiment pos coef senc A] {true} ≤
      ((n + 1) * q₁ + (n + 1) * n : ℕ) * (Fintype.card F : ℝ≥0∞)⁻¹ +
        hitProb S pos coef senc A +
        ∑ i, (otAdvantage senc (otReduction S pos coef senc A i) +
          (Fintype.card Msg : ℝ≥0∞)⁻¹) := by
  rw [prob_experiment_eq_realRun]
  calc Pr{let w ← realRun S pos coef senc A}[Win w.1 w.2]
      ≤ Pr{let w ← realRun S pos coef senc A}[¬w.1.Good pos coef S] +
          Pr{let w ← realRun S pos coef senc A}[Win w.1 w.2 ∧ ¬¬w.1.Good pos coef S] :=
        prEvent_le_prEvent_add_prEvent_and_not _ _ _
    _ ≤ ((n + 1) * q₁ + (n + 1) * n : ℕ) * (Fintype.card F : ℝ≥0∞)⁻¹ +
          Pr{let w ← progRun S pos coef senc A}[Win w.1 w.2 ∧ w.1.Good pos coef S] := by
        gcongr
        · exact (prob_realRun_not_good_le S pos coef senc A).trans
            (prob_not_good_le S pos coef A hS hq)
        · simp only [not_not]
          exact (prob_realRun_eq_progRun S pos coef senc A _).le
    _ ≤ ((n + 1) * q₁ + (n + 1) * n : ℕ) * (Fintype.card F : ℝ≥0∞)⁻¹ +
          (hitProb S pos coef senc A +
            ∑ i, Pr{let w ← freshRun S pos coef senc A i}[w.2.1 i = w.1.m i]) := by
        gcongr
        refine (prob_progRun_le_hit_add_sum S pos coef senc A).trans ?_
        exact add_le_add le_rfl (Finset.sum_le_sum fun i _ => prob_miss_le_fresh S pos coef senc A i)
    _ ≤ _ := by
        rw [add_assoc]
        gcongr with j
        exact prob_fresh_le_ot S pos coef senc A j

end Generic

end AuditPay.Monitoring
