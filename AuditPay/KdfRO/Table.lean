/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.KdfRO.ROM
import VCVio.OracleComp.QueryTracking.RandomOracle.DependentTable
import VCVio.OracleComp.QueryTracking.LoggingOracle.Core

/-!
# The key-derivation function as a table: eager runs

A game run in the random oracle model from a cache `c` (`KdfRO.roRun`) has the same output
distribution as: sample a uniformly random table `g : X → Key`, complete the cache with it
(`completeTable c g`: cached answers win), and answer every KDF query from the completed table
(VCV-io's `OracleComp.evalDist_simulateQ_romImpl_run'_eq_completeTable`; here
`evalDist_roRun_eq_tableRun`). The *eager* run `tableRun T oa` against a fixed table `T` is a
stateless handler, which makes three facts easy that the proofs of `AuditPay.Monitoring` use:

* `tableRun_withQueryLog_eq_of_agree`: two tables that agree outside a set `S` give the same
  distribution of outputs and query logs on the event that no KDF query lies in `S`;
* `override_uniform`: overwriting a uniform table at distinct points by independent uniform keys
  leaves it uniform (the keys become the table's values at those points);
* `tableRun_queryFin`: the challenger's queries at points `K 0, …, K n` just read the table.

The log of a run is VCV-io's `OracleComp.withQueryLog`: the computation returns, besides its
output, the list of its queries with their answers.
-/

open OracleComp OracleSpec ENNReal

namespace AuditPay.KdfRO

variable {X Key α β : Type}

/-- Answer uniform queries by sampling and KDF queries from the table `T`. -/
def tbl (T : X → Key) : QueryImpl (unifSpec + (X →ₒ Key)) ProbComp :=
  unifFwdAnswerImpl (QueryImpl.ofFn T)

/-- Run a game against the fixed KDF table `T`. -/
def tableRun (T : X → Key) (oa : OracleComp (unifSpec + (X →ₒ Key)) α) : ProbComp α :=
  simulateQ (tbl T) oa

@[simp]
theorem tableRun_pure (T : X → Key) (a : α) :
    tableRun T (pure a : OracleComp (unifSpec + (X →ₒ Key)) α) = pure a := by
  simp [tableRun]

@[simp]
theorem tableRun_bind (T : X → Key) (oa : OracleComp (unifSpec + (X →ₒ Key)) α)
    (ob : α → OracleComp (unifSpec + (X →ₒ Key)) β) :
    tableRun T (oa >>= ob) = tableRun T oa >>= fun a => tableRun T (ob a) := by
  simp [tableRun]

@[simp]
theorem tableRun_map (T : X → Key) (f : α → β) (oa : OracleComp (unifSpec + (X →ₒ Key)) α) :
    tableRun T (f <$> oa) = f <$> tableRun T oa := by
  simp [tableRun]

@[simp]
theorem tableRun_liftM (T : X → Key) (pc : ProbComp α) :
    tableRun T (liftM pc : OracleComp (unifSpec + (X →ₒ Key)) α) = pc := by
  simp [tableRun, tbl, unifFwdAnswerImpl, QueryImpl.simulateQ_add_liftM_left]

@[simp]
theorem tableRun_query (T : X → Key) (Z : X) :
    tableRun T (query (spec := X →ₒ Key) Z : OracleComp (unifSpec + (X →ₒ Key)) Key) =
      pure (T Z) := by
  simp only [tableRun, tbl, unifFwdAnswerImpl, QueryImpl.passthrough_add]
  erw [QueryImpl.simulateQ_add_liftM_query_right]
  rfl

@[simp]
theorem tableRun_ite (T : X → Key) (p : Prop) [Decidable p]
    (oa ob : OracleComp (unifSpec + (X →ₒ Key)) α) :
    tableRun T (if p then oa else ob) = if p then tableRun T oa else tableRun T ob := by
  split_ifs <;> rfl

/-- A uniform query of the sum signature, against a table. -/
@[simp]
theorem tableRun_query_inl (T : X → Key) (n : ℕ) :
    tableRun T (liftM ((unifSpec + (X →ₒ Key)).query (Sum.inl n))) =
      (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) := by
  simp [tableRun, tbl, unifFwdAnswerImpl]

/-- A KDF query of the sum signature, against a table. -/
@[simp]
theorem tableRun_query_inr (T : X → Key) (Z : X) :
    tableRun T (liftM ((unifSpec + (X →ₒ Key)).query (Sum.inr Z))) = pure (T Z) := by
  simp only [tableRun, tbl, unifFwdAnswerImpl, QueryImpl.passthrough_add]
  rw [QueryImpl.simulateQ_add_query_right]
  rfl

/-- **Lazy equals eager.** A run in the random oracle model from the cache `c` has the output
distribution of a run against a uniformly random table completing `c`. -/
theorem evalDist_roRun_eq_tableRun [DecidableEq X] [Fintype X] [SampleableType Key]
    [MeasurableSpace α]
    (oa : OracleComp (unifSpec + (X →ₒ Key)) α) (c : (X →ₒ Key).QueryCache) :
    𝒟[Prod.fst <$> roRun oa c] =
      𝒟[($ᵗ (X → Key)) >>= fun g => tableRun (completeTable c g) oa] :=
  OracleComp.evalDist_simulateQ_romImpl_run'_eq_completeTable oa c

/-! ## Logged runs against two tables that agree off a set -/

/-- No KDF query of a log lies in `S`. -/
def LogAvoids (S : Set X) (log : QueryLog (unifSpec + (X →ₒ Key))) : Prop :=
  ∀ e ∈ log, ∀ Z, e.1 = Sum.inr Z → Z ∉ S

@[simp]
theorem logAvoids_nil (S : Set X) : LogAvoids S ([] : QueryLog (unifSpec + (X →ₒ Key))) := by
  simp [LogAvoids]

@[simp]
theorem logAvoids_cons_inl (S : Set X) (n : ℕ) (u : (unifSpec + (X →ₒ Key)).Range (Sum.inl n))
    (log : QueryLog (unifSpec + (X →ₒ Key))) :
    LogAvoids S (⟨Sum.inl n, u⟩ :: log) ↔ LogAvoids S log := by
  simp [LogAvoids]

@[simp]
theorem logAvoids_cons_inr (S : Set X) (Z : X) (u : (unifSpec + (X →ₒ Key)).Range (Sum.inr Z))
    (log : QueryLog (unifSpec + (X →ₒ Key))) :
    LogAvoids S (⟨Sum.inr Z, u⟩ :: log) ↔ Z ∉ S ∧ LogAvoids S log := by
  simp [LogAvoids]

/-- A KDF query at a point of `S` appears in the log. -/
theorem mem_of_not_logAvoids {S : Set X} {log : QueryLog (unifSpec + (X →ₒ Key))}
    {Z : X} (hZ : Z ∈ S) {u : Key} (h : ⟨Sum.inr Z, u⟩ ∈ log) : ¬LogAvoids S log :=
  fun hav => hav _ h Z rfl hZ

/-- **Tables that agree off `S` are indistinguishable until a query in `S`.** The logged runs of
a game against two such tables put the same mass on every event conjoined with the absence of
KDF queries in `S`. -/
theorem tableRun_withQueryLog_eq_of_agree {T T' : X → Key} {S : Set X}
    (hT : ∀ Z, Z ∉ S → T Z = T' Z) (oa : OracleComp (unifSpec + (X →ₒ Key)) α)
    (E : α × QueryLog (unifSpec + (X →ₒ Key)) → Prop) :
    Pr{let z ← tableRun T oa.withQueryLog}[E z ∧ LogAvoids S z.2] =
      Pr{let z ← tableRun T' oa.withQueryLog}[E z ∧ LogAvoids S z.2] := by
  induction oa using OracleComp.inductionOn generalizing E with
  | pure a => simp
  | query_bind t k ih =>
    rw [withQueryLog_bind, withQueryLog_query]
    simp only [bind_assoc, pure_bind, tableRun_bind, tableRun_map]
    rcases t with n | Z
    · rw [tableRun_query_inl, tableRun_query_inl]
      refine prEvent_bind_congr _ _ _ _ _ fun u => ?_
      simp only [prEvent_map, List.singleton_append, Prod.map_snd, logAvoids_cons_inl]
      exact ih u _
    · rw [tableRun_query_inr, tableRun_query_inr, pure_bind, pure_bind]
      simp only [prEvent_map, List.singleton_append, Prod.map_snd, logAvoids_cons_inr]
      by_cases hZ : Z ∈ S
      · simp only [hZ, not_true_eq_false, false_and, and_false, prEvent_false]
      · rw [hT Z hZ]
        simp only [hZ, not_false_eq_true, true_and]
        exact ih (T' Z) _

/-! ## The KDF points of a log -/

/-- The points of the KDF queries in a log, in order (with repetitions). -/
def kdfPoints (log : QueryLog (unifSpec + (X →ₒ Key))) : List X :=
  log.filterMap fun e => match e.1 with
    | Sum.inr Z => some Z
    | Sum.inl _ => none

@[simp]
theorem kdfPoints_nil : kdfPoints ([] : QueryLog (unifSpec + (X →ₒ Key))) = [] := rfl

@[simp]
theorem kdfPoints_cons_inl (n : ℕ) (u : (unifSpec + (X →ₒ Key)).Range (Sum.inl n))
    (log : QueryLog (unifSpec + (X →ₒ Key))) : kdfPoints (⟨Sum.inl n, u⟩ :: log) = kdfPoints log :=
  rfl

@[simp]
theorem kdfPoints_cons_inr (Z : X) (u : (unifSpec + (X →ₒ Key)).Range (Sum.inr Z))
    (log : QueryLog (unifSpec + (X →ₒ Key))) :
    kdfPoints (⟨Sum.inr Z, u⟩ :: log) = Z :: kdfPoints log :=
  rfl

/-- A point is among the KDF points of a log iff the log holds a KDF query at it. -/
theorem mem_kdfPoints {log : QueryLog (unifSpec + (X →ₒ Key))} {Z : X} :
    Z ∈ kdfPoints log ↔ ∃ u, ⟨Sum.inr Z, u⟩ ∈ log := by
  induction log with
  | nil => simp
  | cons e log ih =>
    obtain ⟨t, u⟩ := e
    rcases t with n | Z'
    · simp only [kdfPoints_cons_inl, ih, List.mem_cons]
      constructor
      · rintro ⟨u', h⟩
        exact ⟨u', Or.inr h⟩
      · rintro ⟨u', h | h⟩
        · cases h
        · exact ⟨u', h⟩
    · simp only [kdfPoints_cons_inr, List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨u', h⟩)
        · exact ⟨u, Or.inl rfl⟩
        · exact ⟨u', Or.inr h⟩
      · rintro ⟨u', h | h⟩
        · cases h
          exact Or.inl rfl
        · exact Or.inr ⟨u', h⟩

/-- A game making at most `q` KDF queries logs at most `q` KDF points. -/
theorem length_kdfPoints_le_of_mem_support (T : X → Key) {oa : OracleComp (unifSpec + (X →ₒ Key)) α}
    {q : ℕ} (h : IsQueryBoundP oa IsKdfQuery q)
    {z : α × QueryLog (unifSpec + (X →ₒ Key))} (hz : z ∈ support (tableRun T oa.withQueryLog)) :
    (kdfPoints z.2).length ≤ q := by
  induction oa using OracleComp.inductionOn generalizing q z with
  | pure a =>
    simp only [withQueryLog_pure, tableRun_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    rw [withQueryLog_bind, withQueryLog_query] at hz
    simp only [bind_assoc, pure_bind, tableRun_bind, tableRun_map] at hz
    rcases t with n | Z
    · rw [tableRun_query_inl, mem_support_bind_iff] at hz
      obtain ⟨u, -, hz⟩ := hz
      rw [support_map] at hz
      obtain ⟨z', hz', rfl⟩ := hz
      have := ih u (h.2 u) hz'
      simp only [IsKdfQuery, Sum.isRight_inl, Bool.false_eq_true, ite_false] at this
      simpa using this
    · rw [tableRun_query_inr, pure_bind, support_map] at hz
      obtain ⟨z', hz', rfl⟩ := hz
      have := ih (T Z) (h.2 (T Z)) hz'
      simp only [IsKdfQuery, Sum.isRight_inr, ite_true] at this
      have hq : 0 < q := h.1.resolve_left (by simp [IsKdfQuery])
      simp only [Prod.map_snd, List.singleton_append, kdfPoints_cons_inr, List.length_cons]
      omega

/-! ## Overriding a table at hidden points -/

/-- The table `g` overwritten by the key `κ i` at the points that the recognizer `rec i`
accepts (the first accepting index wins). -/
def overrideBy {m : ℕ} (g : X → Key) (rec : Fin m → X → Bool) (κ : Fin m → Key) (Z : X) :
    Key :=
  match (List.finRange m).find? (fun i => rec i Z) with
  | some i => κ i
  | none => g Z

/-- Recognizers that agree at `Z` give the same overridden table at `Z`. -/
theorem overrideBy_congr {m : ℕ} (g : X → Key) {rec rec' : Fin m → X → Bool} (κ : Fin m → Key)
    {Z : X} (h : ∀ i, rec i Z = rec' i Z) : overrideBy g rec κ Z = overrideBy g rec' κ Z := by
  unfold overrideBy
  have : (fun i => rec i Z) = fun i => rec' i Z := funext h
  rw [this]

/-- The table `g` overwritten, at the point `K i` of every index `i` with `hid i`, by the key
`κ i` (the first such index wins). -/
def override [DecidableEq X] {m : ℕ} (g : X → Key) (K : Fin m → X) (hid : Fin m → Bool)
    (κ : Fin m → Key) (Z : X) :
    Key :=
  overrideBy g (fun i Z => hid i && decide (K i = Z)) κ Z

/-- At a point that is not a hidden point, the overridden table is the original. -/
theorem override_of_not_hit [DecidableEq X] {m : ℕ} (g : X → Key) (K : Fin m → X)
    (hid : Fin m → Bool) (κ : Fin m → Key) {Z : X} (hZ : ∀ i, hid i → K i ≠ Z) :
    override g K hid κ Z = g Z := by
  unfold override overrideBy
  have h : (List.finRange m).find? (fun i => hid i && decide (K i = Z)) = none := by
    rw [List.find?_eq_none]
    intro i _
    by_cases hi : hid i = true
    · simp [hi, hZ i hi]
    · simp [hi]
  rw [h]

/-- At the hidden point `K i`, when `K` is injective on hidden indices, the overridden table is
`κ i`. -/
theorem override_hit [DecidableEq X] {m : ℕ} (g : X → Key) (K : Fin m → X) (hid : Fin m → Bool)
    (κ : Fin m → Key) (hinj : ∀ i j, hid i → hid j → K i = K j → i = j) {i : Fin m}
    (hi : hid i) : override g K hid κ (K i) = κ i := by
  unfold override overrideBy
  have hsome : ((List.finRange m).find? (fun j => hid j && decide (K j = K i))).isSome :=
    List.find?_isSome.2 ⟨i, List.mem_finRange i, by simp [hi]⟩
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.1 hsome
  have hj' := List.find?_some hj
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hj'
  rw [hj, hinj j i hj'.1 hi hj'.2]

/-- Changing the key of index `i` does not change the overridden table away from `K i`. -/
theorem override_update_of_ne [DecidableEq X] {m : ℕ} (g : X → Key) (K : Fin m → X)
    (hid : Fin m → Bool) (κ : Fin m → Key) (i : Fin m) (v : Key) {Z : X} (hZ : Z ≠ K i) :
    override g K hid (Function.update κ i v) Z = override g K hid κ Z := by
  unfold override overrideBy
  cases hf : (List.finRange m).find? (fun j => hid j && decide (K j = Z)) with
  | none => rfl
  | some j =>
    have hj := List.find?_some hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
    have hji : j ≠ i := fun h => hZ (h ▸ hj.2).symm
    simp [Function.update_of_ne hji]

/-- The bijection behind `override_uniform`: swap the keys `κ` with the table's values at the
hidden points. -/
def swapHidden [DecidableEq X] {m : ℕ} (K : Fin m → X) (hid : Fin m → Bool) :
    (X → Key) × (Fin m → Key) → (X → Key) × (Fin m → Key) :=
  fun gk => (override gk.1 K hid gk.2, fun i => if hid i then gk.1 (K i) else gk.2 i)

/-- `swapHidden` is an involution when `K` is injective on hidden indices. -/
theorem swapHidden_swapHidden [DecidableEq X] {m : ℕ} (K : Fin m → X) (hid : Fin m → Bool)
    (hinj : ∀ i j, hid i → hid j → K i = K j → i = j) (gk : (X → Key) × (Fin m → Key)) :
    swapHidden K hid (swapHidden K hid gk) = gk := by
  obtain ⟨g, κ⟩ := gk
  simp only [swapHidden]
  refine Prod.ext ?_ ?_
  · funext Z
    change override (override g K hid κ) K hid (fun i => if hid i then g (K i) else κ i) Z = g Z
    by_cases hZ : ∃ i, hid i ∧ K i = Z
    · obtain ⟨i, hi, rfl⟩ := hZ
      rw [override_hit _ K hid _ hinj hi]
      simp [hi]
    · push Not at hZ
      rw [override_of_not_hit _ K hid _ hZ, override_of_not_hit _ K hid _ hZ]
  · funext i
    change (if hid i then override g K hid κ (K i) else if hid i then g (K i) else κ i) = κ i
    by_cases hi : hid i = true
    · simp only [hi, ite_true]
      exact override_hit _ K hid _ hinj hi
    · simp [hi]

/-- **Overriding a uniform table at distinct points by independent uniform keys leaves it
uniform.** For `K` injective on hidden indices and any continuation `k`, sampling a table and
keys and running `k` on the overridden table is the same as running it on the table. -/
theorem override_uniform [DecidableEq X] [SampleableType Key] [SampleableType (X → Key)]
    {m : ℕ} (K : Fin m → X) (hid : Fin m → Bool)
    (hinj : ∀ i j, hid i → hid j → K i = K j → i = j) (k : (X → Key) → ProbComp β) :
    (do let g ← $ᵗ (X → Key); let κ ← $ᵗ (Fin m → Key); k (override g K hid κ)) =ᵈ
      (do let g ← $ᵗ (X → Key); let _κ ← $ᵗ (Fin m → Key); k g) := by
  have hbij : Function.Bijective (swapHidden (Key := Key) K hid) :=
    Function.Involutive.bijective (swapHidden_swapHidden K hid hinj)
  have h := uniform_bind_bij (e := swapHidden (Key := Key) K hid) hbij
    (fun gk : (X → Key) × (Fin m → Key) => k gk.1)
  rw [SampleableType.uniformSample_prod_eq_bind] at h
  simp only [bind_assoc, pure_bind, swapHidden] at h
  exact h

/-! ## The challenger's queries -/

/-- The KDF queries at the points `K 0, …, K (m - 1)`, in order. -/
def queryFin : ∀ {m : ℕ}, (Fin m → X) → OracleComp (unifSpec + (X →ₒ Key)) (Fin m → Key)
  | 0, _ => pure Fin.elim0
  | _ + 1, K => do
    let k ← query (spec := X →ₒ Key) (K 0)
    let ks ← queryFin fun i => K i.succ
    pure (Fin.cons k ks)

/-- Against a table, the challenger's queries read the table. -/
@[simp]
theorem tableRun_queryFin (T : X → Key) : ∀ {m : ℕ} (K : Fin m → X),
    tableRun T (queryFin K) = pure fun i => T (K i)
  | 0, K => by
    simp only [queryFin, tableRun_pure]
    congr
    funext i
    exact i.elim0
  | m + 1, K => by
    simp only [queryFin, tableRun_bind, tableRun_query, pure_bind, tableRun_queryFin T]
    rw [tableRun_pure]
    congr 1
    funext i
    refine Fin.cases ?_ ?_ i <;> simp

/-- The challenger's queries make exactly `m` KDF queries. -/
theorem isQueryBoundP_queryFin : ∀ {m : ℕ} (K : Fin m → X),
    IsQueryBoundP (queryFin K : OracleComp (unifSpec + (X →ₒ Key)) _) IsKdfQuery m
  | 0, _ => isQueryBoundP_pure _ _ _
  | m + 1, K => by
    simp only [queryFin]
    have h1 : IsQueryBoundP (query (spec := X →ₒ Key) (K 0) :
        OracleComp (unifSpec + (X →ₒ Key)) Key) IsKdfQuery 1 := by
      rw [show (query (spec := X →ₒ Key) (K 0) : OracleComp (unifSpec + (X →ₒ Key)) Key) =
        liftM ((unifSpec + (X →ₒ Key)).query (Sum.inr (K 0))) from rfl, isQueryBoundP_query_iff]
      exact fun _ => Nat.one_pos
    have h2 : ∀ k : Key, IsQueryBoundP ((queryFin fun i => K i.succ) >>= fun ks =>
        (pure (Fin.cons k ks) : OracleComp (unifSpec + (X →ₒ Key)) (Fin (m + 1) → Key)))
        IsKdfQuery m := by
      intro k
      have h := isQueryBoundP_bind (isQueryBoundP_queryFin fun i => K i.succ)
        (fun ks _ => isQueryBoundP_pure (p := IsKdfQuery)
          (pure (Fin.cons k ks) : OracleComp (unifSpec + (X →ₒ Key)) (Fin (m + 1) → Key)) 0)
      simpa using h
    have h3 := isQueryBoundP_bind h1 fun k _ => h2 k
    exact h3.mono (by omega)

end AuditPay.KdfRO
