/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.KdfRO.Monitoring.Hop
import AuditPay.KdfRO.SharedSecretStrong

/-!
# Theorem 3, decryption game with a random-oracle KDF, paper's scheme: reduction to strong DH

For Algorithm 2 (one ephemeral value) with a random-oracle key-derivation function, the
decryption game of Definition 3 reduces, without the algebraic group model, to the shared-secret
game with decision oracles (`AuditPay.RestrictedMonitoring.SharedSecret.strongExperiment`),
hence tightly to the strong Diffie–Hellman problem (`AuditPay.StrongDH`).

The reduction `ssAdversary` plays the shared-secret game with decision oracles: it receives the
ephemeral points `Rᵢ = rᵢ • g` and must output `rᵢ • Pᵢ` for all `i`, with
`Pᵢ = RetrieveKey(V, aᵢ) - H(aᵢ)`. It encrypts under fresh keys `κᵢ` for the hidden indices
(`Pᵢ ≠ 0`; for the others `Kᵢ = rᵢ • 0 = 0` is known), answers the adversary's KDF query at a
point `Z` with `κⱼ` for the first hidden `j` with `Z = rⱼ • Pⱼ` — recognised with the decision
query `(j, Pⱼ, Z)` — and finally outputs, for each hidden `i`, the first logged point `Z` with
`Z = rᵢ • Pᵢ`. Its simulation is exactly the programmed run of `AuditPay.Monitoring.Hop`, and
it makes at most `n + 1` decision queries per KDF query of the adversary, plus `n + 1` per logged
point at the end.
-/

open OracleComp OracleSpec DiffieHellman ENNReal

namespace AuditPay.Monitoring.StrongDH

open KdfRO SLIND RestrictedMonitoring RestrictedMonitoring.SharedSecret

variable {F G Addr Key Msg C σ : Type} {k n : ℕ} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq G]

/-- Run the oracle computations `f 0, …, f (m - 1)` in order and collect their outputs. -/
def seqFin {ι : Type} {spec : OracleSpec ι} {β : Type} :
    ∀ {m : ℕ}, (Fin m → OracleComp spec β) → OracleComp spec (Fin m → β)
  | 0, _ => pure Fin.elim0
  | _ + 1, f => do
    let a ← f 0
    let as ← seqFin fun i => f i.succ
    pure (Fin.cons a as)

/-- A handler that answers every `f i` deterministically answers `seqFin f` with the vector of
answers. -/
theorem simulateQ_seqFin {ι : Type} {spec : OracleSpec ι} {β : Type}
    (impl : QueryImpl spec ProbComp) :
    ∀ {m : ℕ} (f : Fin m → OracleComp spec β) (v : Fin m → β),
      (∀ i, simulateQ impl (f i) = pure (v i)) → simulateQ impl (seqFin f) = pure v
  | 0, f, v, _ => by
    simp only [seqFin, simulateQ_pure]
    congr
    funext i
    exact i.elim0
  | m + 1, f, v, h => by
    simp only [seqFin, simulateQ_bind, h 0, pure_bind,
      simulateQ_seqFin impl (fun i => f i.succ) (fun i => v i.succ) fun i => h i.succ,
      simulateQ_pure]
    congr 1
    funext i
    refine Fin.cases ?_ ?_ i <;> simp

/-- Find the first hidden index `j` (`Pⱼ ≠ 0`) in a list with `Z = rⱼ • Pⱼ`, with one decision
query `(j, Pⱼ, Z)` per hidden index. -/
def findHit (P : Fin (n + 1) → G) (Z : G) :
    List (Fin (n + 1)) → OracleComp (unifSpec + multiSpec n G) (Option (Fin (n + 1)))
  | [] => pure none
  | j :: js =>
    if P j = 0 then findHit P Z js else do
      let hit ← query (spec := multiSpec n G) (j, P j, Z)
      if hit then pure (some j) else findHit P Z js

/-- Against the decision oracles for `r`, `findHit` finds the first hidden `j` with
`rⱼ • Pⱼ = Z`. -/
theorem simulateQ_multiImpl_findHit (r : Fin (n + 1) → F) (P : Fin (n + 1) → G) (Z : G) :
    ∀ js : List (Fin (n + 1)), simulateQ (multiImpl r) (findHit P Z js) =
      pure (js.find? fun j => decide (P j ≠ 0) && decide (r j • P j = Z))
  | [] => by simp [findHit]
  | j :: js => by
    simp only [findHit, List.find?_cons]
    by_cases hP : P j = 0
    · simp [hP, simulateQ_multiImpl_findHit r P Z js]
    · simp only [hP, ite_false, simulateQ_bind, simulateQ_multiImpl_query, pure_bind, ne_eq,
        not_false_eq_true, decide_true, Bool.true_and]
      by_cases hZ : Z = r j • P j
      · simp [hZ]
      · simp [hZ, Ne.symm hZ, simulateQ_multiImpl_findHit r P Z js]

/-- Find the first logged point `Z` with `Z = rᵢ • Pᵢ`, with one decision query `(i, Pᵢ, Z)` per
point. -/
def scanLog (i : Fin (n + 1)) (P : G) :
    List G → OracleComp (unifSpec + multiSpec n G) (Option G)
  | [] => pure none
  | Z :: Zs => do
    let hit ← query (spec := multiSpec n G) (i, P, Z)
    if hit then pure (some Z) else scanLog i P Zs

theorem simulateQ_multiImpl_scanLog (r : Fin (n + 1) → F) (i : Fin (n + 1)) (P : G) :
    ∀ Zs : List G, simulateQ (multiImpl r) (scanLog i P Zs) =
      pure (Zs.find? fun Z => decide (Z = r i • P))
  | [] => by simp [scanLog]
  | Z :: Zs => by
    simp only [scanLog, simulateQ_bind, simulateQ_multiImpl_query, pure_bind, List.find?_cons]
    by_cases h : Z = r i • P <;> simp [h, simulateQ_multiImpl_scanLog r i P Zs]

/-- The reduction's answer to a KDF query at the explicit point `Z`: the first-phase cache if
`Z` is cached, else `κ j` for the first hidden `j` with `Z = rⱼ • Pⱼ` (found with the decision
oracle), else the reduction's own table `gB`. -/
def evalM (cache : (G →ₒ Key).QueryCache) (gB : G → Key) (κ : Fin (n + 1) → Key)
    (P : Fin (n + 1) → G) (Z : G) : OracleComp (unifSpec + multiSpec n G) Key :=
  match cache Z with
  | some v => pure v
  | none => do
    let j? ← findHit P Z (List.finRange (n + 1))
    pure (match j? with
      | some j => κ j
      | none => gB Z)

/-- The reduction's handler for the adversary's second phase: uniform queries are forwarded,
KDF queries are answered by `evalM`. -/
def hB (cache : (G →ₒ Key).QueryCache) (gB : G → Key) (κ : Fin (n + 1) → Key)
    (P : Fin (n + 1) → G) :
    QueryImpl (unifSpec + (G →ₒ Key)) (OracleComp (unifSpec + multiSpec n G)) :=
  fun t => match t with
    | Sum.inl m => liftM ((unifSpec + multiSpec n G).query (Sum.inl m))
    | Sum.inr Z => evalM cache gB κ P Z

/-- The table that `evalM` computes against the decision oracles for `r`: the cache completed
by `gB` overridden at the hidden points `rⱼ • Pⱼ`. -/
def effTable (cache : (G →ₒ Key).QueryCache) (gB : G → Key) (κ : Fin (n + 1) → Key)
    (P : Fin (n + 1) → G) (r : Fin (n + 1) → F) : G → Key :=
  completeTable cache (override gB (fun j => r j • P j) (fun j => decide (P j ≠ 0)) κ)

theorem simulateQ_multiImpl_evalM (cache : (G →ₒ Key).QueryCache) (gB : G → Key)
    (κ : Fin (n + 1) → Key) (P : Fin (n + 1) → G) (r : Fin (n + 1) → F) (Z : G) :
    simulateQ (multiImpl r) (evalM cache gB κ P Z) = pure (effTable cache gB κ P r Z) := by
  simp only [evalM, effTable, completeTable, override, overrideBy]
  cases cache Z with
  | some v => simp
  | none =>
    simp only [simulateQ_bind, simulateQ_multiImpl_findHit, pure_bind, simulateQ_pure,
      Option.getD_none]
    cases (List.finRange (n + 1)).find? fun j => decide (P j ≠ 0) && decide (r j • P j = Z) <;>
      simp

/-- Against the decision oracles for `r`, the reduction's handler is the table `effTable`. -/
theorem simulateQ_multiImpl_hB {α : Type} (cache : (G →ₒ Key).QueryCache) (gB : G → Key)
    (κ : Fin (n + 1) → Key) (P : Fin (n + 1) → G) (r : Fin (n + 1) → F)
    (oa : OracleComp (unifSpec + (G →ₒ Key)) α) :
    simulateQ (multiImpl r) (simulateQ (hB cache gB κ P) oa) =
      tableRun (effTable cache gB κ P r) oa := by
  refine QueryImpl.simulateQ_simulateQ_eq_of_apply (fun t => ?_) oa
  rcases t with m | Z
  · simp [hB, multiImpl, unifFwdAnswerImpl, tbl]
  · rw [hB, simulateQ_multiImpl_evalM]
    simp only [tbl, unifFwdAnswerImpl, QueryImpl.passthrough_add, QueryImpl.add_apply_inr,
      QueryImpl.liftTarget_apply, QueryImpl.ofFn_apply]
    rfl

/-! ## The reduction's keys and extraction -/

variable (g : G) (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F)

/-- The reduction's keys: `κ i` for hidden indices, the table's value at `0` otherwise. -/
def redKeys (p : Pre G Addr F G Key Msg σ n) (T : G → Key) (κ : Fin (n + 1) → Key)
    (i : Fin (n + 1)) : Key :=
  if p.P pos coef i = 0 then T 0 else κ i

/-- The reduction's extraction from the second phase's log: `0` for a public index, else the
first logged point `Z` with `Z = rᵢ • Pᵢ`. -/
def extract (p : Pre G Addr F G Key Msg σ n) (log : QueryLog (unifSpec + (G →ₒ Key)))
    (i : Fin (n + 1)) : G :=
  if p.P pos coef i = 0 then 0
  else ((kdfPoints log).find? fun Z => decide (Z = p.r i • p.P pos coef i)).getD 0

/-- The reduction wins the shared-secret game. -/
def WinSS (w : Outcome G Addr F G Key Msg σ n) : Prop :=
  ∀ i, extract pos coef w.1 w.2.2 i = w.1.r i • w.1.P pos coef i

/-- The event of the generic bound (`hitProb`): the prefix is good and every hidden shared point
is queried in the second phase. -/
def HitAll (w : Outcome G Addr F G Key Msg σ n) : Prop :=
  w.1.Good pos coef (single F g) ∧
    ∀ i, w.1.hid pos coef i → Hit (w.1.K pos coef (single F g) i) w.2

theorem simulateQ_multiImpl_keys (cache : (G →ₒ Key).QueryCache) (gB : G → Key)
    (κ : Fin (n + 1) → Key) (P : Fin (n + 1) → G) (r : Fin (n + 1) → F) :
    simulateQ (multiImpl r)
        (seqFin fun i => if P i = 0 then evalM cache gB κ P 0 else pure (κ i)) =
      pure fun i => if P i = 0 then effTable cache gB κ P r 0 else κ i :=
  simulateQ_seqFin _ _ _ fun i => by
    by_cases h : P i = 0 <;> simp [h, simulateQ_multiImpl_evalM]

theorem simulateQ_multiImpl_extract (P : Fin (n + 1) → G) (r : Fin (n + 1) → F)
    (log : QueryLog (unifSpec + (G →ₒ Key))) :
    simulateQ (multiImpl r) (seqFin fun i => if P i = 0 then pure 0
        else (fun o => o.getD 0) <$> scanLog i (P i) (kdfPoints log)) =
      pure fun i => if P i = 0 then 0
        else ((kdfPoints log).find? fun Z => decide (Z = r i • P i)).getD 0 :=
  simulateQ_seqFin _ _ _ fun i => by
    by_cases h : P i = 0 <;> simp [h, simulateQ_multiImpl_scanLog]

/-- The table the reduction computes is the programmed table of the prefix. -/
theorem effTable_eq_progTable (p : Pre G Addr F G Key Msg σ n) (gB : G → Key)
    (κ : Fin (n + 1) → Key) :
    effTable p.cache gB κ (p.P pos coef) p.r = progTable pos coef (single F g) p gB κ := rfl

/-- For a good prefix, the reduction's keys are the programmed run's keys. -/
theorem redKeys_eq_keysOf {p : Pre G Addr F G Key Msg σ n}
    (hgood : p.Good pos coef (single F g)) (gB : G → Key) (κ : Fin (n + 1) → Key) :
    redKeys pos coef p (progTable pos coef (single F g) p gB κ) κ =
      keysOf (single F g) pos coef p (progTable pos coef (single F g) p gB κ) := by
  funext i
  simp only [redKeys, keysOf]
  by_cases hP : p.P pos coef i = 0
  · have hK : p.K pos coef (single F g) i = 0 := by simp [Pre.K, single, hP]
    rw [ite_eq_left hP, hK]
  · have hinj : ∀ i j, p.hid pos coef i → p.hid pos coef j →
        p.K pos coef (single F g) i = p.K pos coef (single F g) j → i = j :=
      fun i j hi _ hij => by_contra fun hne => hgood.1 i j hi hne hij
    have hi : p.hid pos coef i := by simpa [Pre.hid] using hP
    rw [ite_eq_right hP]
    simp only [progTable, completeTable, hgood.2 i hi, Option.getD_none,
      override_hit _ _ _ _ hinj hi]

/-- If every hidden point is queried the extraction is correct. -/
theorem winSS_of_hitAll {w : Outcome G Addr F G Key Msg σ n} (h : HitAll g pos coef w) :
    WinSS pos coef w := by
  obtain ⟨p, z⟩ := w
  obtain ⟨_, hhit⟩ := h
  intro i
  simp only [extract]
  by_cases hP : p.P pos coef i = 0
  · simp [hP]
  · rw [ite_eq_right hP]
    have hi : p.hid pos coef i := by simpa [Pre.hid] using hP
    obtain ⟨u, hu⟩ := hhit i hi
    have hmem : p.K pos coef (single F g) i ∈ kdfPoints z.2 := mem_kdfPoints.2 ⟨u, hu⟩
    have hsome : ((kdfPoints z.2).find? fun Z => decide (Z = p.r i • p.P pos coef i)).isSome :=
      List.find?_isSome.2 ⟨_, hmem, by simp [Pre.K, single]⟩
    obtain ⟨Z₀, hZ₀⟩ := Option.isSome_iff_exists.1 hsome
    have htest := List.find?_some hZ₀
    rw [hZ₀, Option.getD_some]
    exact of_decide_eq_true htest

/-- The state of the reduction after the first phase: `H`, the commitment and the KDF cache. -/
abbrev State (G Addr Key σ : Type) (n : ℕ) :=
  (Addr → G) × Commit G Addr σ n × (G →ₒ Key).QueryCache

variable [Fintype F] [DecidableEq F] [SampleableType F] [SampleableType G] [Fintype G]
  [Fintype Addr] [DecidableEq Addr] [SampleableType Key] [SampleableType Msg] [DecidableEq Msg]
  (senc : Key → Msg → C) (A : Adversary G Addr G G Key Msg C σ n)

/-- The shared-secret adversary with decision oracles built from a decryption adversary against
the paper's scheme. -/
noncomputable def ssAdversary : StrongAdversary G Addr (State G Addr Key σ n) n where
  commit H := do
    let z ← roRun (A.commit H) ∅
    return (z.1.1, z.1.2.1, (H, z.1, z.2))
  respond st R := do
    let m ← $ᵗ (Fin (n + 1) → Msg)
    let gB ← $ᵗ (G → Key)
    let κ ← $ᵗ (Fin (n + 1) → Key)
    let keys ← seqFin fun i =>
      if pts pos coef st.1 st.2.1 i = 0 then evalM st.2.2 gB κ (pts pos coef st.1 st.2.1) 0
      else pure (κ i)
    let z ← simulateQ (hB st.2.2 gB κ (pts pos coef st.1 st.2.1))
      (A.respond st.2.1.2.2 fun i => (senc (keys i) (m i), R i)).withQueryLog
    seqFin fun i =>
      if pts pos coef st.1 st.2.1 i = 0 then pure 0
      else (fun o => o.getD 0) <$> scanLog i (pts pos coef st.1 st.2.1 i) (kdfPoints z.2)

/-- The strong Diffie–Hellman reduction for the decryption game of the paper's scheme. -/
noncomputable def sdhReduction : AuditPay.StrongDH.Adversary F G :=
  SharedSecret.sdhReduction pos coef (ssAdversary pos coef senc A)

/-! ## The reduction's run as the programmed run -/

/-- The reduction's run: the programmed run with the reduction's keys. -/
noncomputable def redRun : ProbComp (Outcome G Addr F G Key Msg σ n) :=
  prefixRun A >>= fun p => $ᵗ (G → Key) >>= fun gB => $ᵗ (Fin (n + 1) → Key) >>= fun κ =>
    (fun z => (p, z)) <$> suffixRun (single F g) senc A p
      (progTable pos coef (single F g) p gB κ)
      (redKeys pos coef p (progTable pos coef (single F g) p gB κ) κ)

omit [Fintype F] [DecidableEq F] [DecidableEq Msg] in
/-- The shared-secret experiment with decision oracles of `ssAdversary` is the reduction's run
followed by the check that the extracted points are right. -/
theorem prob_experiment_eq_redRun :
    𝒟[strongExperiment g pos coef (ssAdversary pos coef senc A)] {true} =
      Pr{let w ← redRun g pos coef senc A}[WinSS pos coef w] := by
  rw [← prEvent_eq_evalDist_singleton]
  simp only [strongExperiment, ssAdversary, redRun, prefixRun, bind_assoc, pure_bind,
    simulateQ_bind, simulateQ_multiImpl_liftM, simulateQ_multiImpl_keys, simulateQ_multiImpl_hB,
    simulateQ_multiImpl_extract, prEvent_norm, decide_eq_true_eq]
  refine prEvent_bind_congr' _ _ _ fun H => prEvent_bind_congr' _ _ _ fun z =>
    prEvent_bind_congr' _ _ _ fun r => prEvent_bind_congr' _ _ _ fun m =>
    prEvent_bind_congr' _ _ _ fun gB => prEvent_bind_congr' _ _ _ fun κ => ?_
  simp only [suffixRun, redKeys, WinSS, extract, Pre.P, single, encPoint, pts]
  rfl

omit [Fintype F] [DecidableEq F] [DecidableEq Msg] in
/-- The programmed run and the reduction's run agree on the hit event. -/
theorem prob_progRun_eq_redRun :
    Pr{let w ← progRun (single F g) pos coef senc A}[HitAll g pos coef w] =
      Pr{let w ← redRun g pos coef senc A}[HitAll g pos coef w] := by
  simp only [progRun, redRun, prEvent_norm]
  refine prEvent_bind_congr' _ _ _ fun p => prEvent_bind_congr' _ _ _ fun gB =>
    prEvent_bind_congr' _ _ _ fun κ => ?_
  by_cases hgood : p.Good pos coef (single F g)
  · rw [redKeys_eq_keysOf g pos coef hgood]
  · refine (prEvent_eq_zero_of_forall_not _ _ fun z hz => hgood hz.1).trans
      (prEvent_eq_zero_of_forall_not _ _ fun z hz => hgood hz.1).symm


/-! ## The bound -/

omit [DecidableEq G] [DecidableEq F] [SampleableType G] [Fintype G] in
/-- The paper's scheme is unpredictable: for `P ≠ 0` and uniform `r`, the point `r • P` takes
any given value with probability at most `1/|F|`. -/
theorem single_unpredictable : (single F g).Unpredictable F := by
  intro P hP Z
  have hinj : Function.Injective fun r : F => ((single F g).pt r P) := by
    intro a a' h
    simp only [single] at h
    have h1 : (a - a') • P = 0 := by rw [sub_smul, h, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h1).resolve_right hP)
  refine (SampleableType.prEvent_uniformSample_apply_eq_le hinj Z).trans ?_
  rw [Nat.card_eq_fintype_card]

omit [Fintype F] [DecidableEq F] [DecidableEq Msg] in
/-- **The hit probability is bounded by the shared-secret game with decision oracles**, with no
loss. -/
theorem hitProb_le :
    hitProb (single F g) pos coef senc A ≤
      𝒟[strongExperiment g pos coef (ssAdversary pos coef senc A)] {true} := by
  rw [prob_experiment_eq_redRun]
  refine le_of_eq_of_le (prob_progRun_eq_redRun g pos coef senc A) ?_
  exact prEvent_mono _ _ _ fun w hw => winSS_of_hitAll g pos coef hw

/-- **Theorem 3 for the paper's scheme, decryption game, random-oracle KDF, no algebraic group
model** (option 2). For a generator `g`, an adversary that outputs an arbitrary vector `V` and
`n + 1` distinct addresses, makes at most `q₁` KDF queries before and `q₂` after receiving the
ciphertexts, decrypts all `n + 1` ciphertexts with probability at most
`((n + 1) q₁ + (n + 1) n) / |F|` (a bad prefix), plus the strong Diffie–Hellman success
probability of `sdhReduction` plus `1/|F|`, plus, for each ciphertext, the one-time advantage of
`otReduction` against the cipher plus `1/|Msg|`. -/
theorem experiment_le [Inhabited Msg] [Fintype Msg] {g : G}
    (hg : Function.Bijective (· • g : F → G)) {q₁ q₂ : ℕ} (hq : A.QueryBound q₁ q₂) :
    𝒟[experiment g pos coef senc A] {true} ≤
      ((n + 1) * q₁ + (n + 1) * n : ℕ) * (Fintype.card F : ℝ≥0∞)⁻¹ +
        (𝒟[AuditPay.StrongDH.experiment g (sdhReduction pos coef senc A)] {true} +
          (Fintype.card F : ℝ≥0∞)⁻¹) +
        ∑ i, (otAdvantage senc (otReduction (single F g) pos coef senc A i) +
          (Fintype.card Msg : ℝ≥0∞)⁻¹) := by
  refine (experiment_le_hitProb_add (single F g) pos coef senc A (single_unpredictable g) hq).trans
    ?_
  gcongr
  refine (hitProb_le g pos coef senc A).trans ?_
  exact strong_success_le hg pos coef (ssAdversary pos coef senc A)

end AuditPay.Monitoring.StrongDH
