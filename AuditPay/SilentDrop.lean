/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.MembershipHidingPublic

/-!
# Theorem 4 with public hash functions: generation that never fails (silent drop)

In `AuditPay.MembershipHidingPublic` the challenger outputs `none` when the rows of the
requested set are linearly dependent. Here generation never fails. The requested addresses
come as an **ordered list** of any length (a guaranteed core first, then optional extras). A
*selection rule* keeps a sub-family with linearly independent rows, the other addresses are
silently dropped, and the published vector is a uniformly random solution for the kept family:
the slots that the kept equations leave undetermined are filled at random.

## Selection rules

A `Selection` chooses the kept addresses from `(pos, coef, request)` only, never from the
audit secret keys or from `H`, and satisfies:

* the kept addresses are requested ones (`Selection.subset`);
* their rows are linearly independent (`Selection.indep`);
* **prefix property** (`Selection.prefix_subset`): if the rows of the first `j` requested
  addresses are linearly independent, all of them are kept.

`Selection.greedy` is the intended rule: walk the request in order and keep an address exactly
when the rows kept so far stay linearly independent with its row added (`greedySelect`,
`mem_greedyStep_iff`). An address is then dropped only when its row is a linear combination of
kept rows (`coefRow_mem_span_greedySelect`).

## Statements

For every selection rule:

* `SilentDrop.vecGen_eqd`: for every request, of any length, the published vector is exactly
  uniform on `Fin n → G`. Hence `SilentDrop.advantage_eq_zero`: the Membership Hiding advantage
  of the corresponding game is `0`, with no restriction on the requests.
* `SilentDrop.prob_exists_dropped_le`: except with probability `depBound Q n k s |F|` over the
  hash tables, for every request simultaneously, every address among its first
  `min s (length)` entries is kept. Kept addresses retrieve their audit keys
  (`SilentDrop.retrieveKey_encodeSet_select`).
-/

open OracleComp ENNReal

namespace AuditPay

/-! ## Selection rules -/

section Selection

variable {F : Type*} [Field F] {Addr : Type*} [DecidableEq Addr] {k n : ℕ}

/-- A rule selecting, from an ordered request, the addresses that get encoded. It may depend
on the position and coefficient hash tables and on the request, and on nothing else. -/
structure Selection (F Addr : Type*) [Field F] [DecidableEq Addr] (k n : ℕ) where
  /-- The addresses kept from the ordered request `l`. -/
  select : (Addr → Fin k → Fin n) → (Addr → Fin k → F) → List Addr → Finset Addr
  /-- Only requested addresses are kept. -/
  subset : ∀ pos coef l, select pos coef l ⊆ l.toFinset
  /-- The rows of the kept addresses are linearly independent. -/
  indep : ∀ pos coef l, RowsIndep pos coef (select pos coef l)
  /-- Prefix property: if the rows of the first `j` requested addresses are linearly
  independent, all of them are kept. -/
  prefix_subset : ∀ pos coef l j,
    RowsIndep pos coef (l.take j).toFinset → (l.take j).toFinset ⊆ select pos coef l

/-- If the rows of all requested addresses are linearly independent, nothing is dropped. -/
theorem Selection.select_eq_toFinset (sel : Selection F Addr k n) {pos : Addr → Fin k → Fin n}
    {coef : Addr → Fin k → F} {l : List Addr} (h : RowsIndep pos coef l.toFinset) :
    sel.select pos coef l = l.toFinset := by
  refine (sel.subset pos coef l).antisymm ?_
  have := sel.prefix_subset pos coef l l.length
  rwa [List.take_length, imp_iff_right h] at this

/-- Outside the bad event `Dep s`, every address among the first `min s (length)` entries of
every request is kept. -/
theorem Selection.take_subset_of_not_dep (sel : Selection F Addr k n) {s : ℕ}
    {pos : Addr → Fin k → Fin n} {coef : Addr → Fin k → F} (h : ¬Dep s pos coef)
    (l : List Addr) : (l.take s).toFinset ⊆ sel.select pos coef l :=
  sel.prefix_subset pos coef l s <| rowsIndep_of_not_dep h <|
    (List.toFinset_card_le _).trans (List.length_take_le s l)

/-! ### The greedy rule -/

/-- The rows of `S` stay independent with the row of `a` added exactly when `S` has independent
rows and the row of `a` is not in their span (or `a` is already in `S`). -/
theorem rowsIndep_insert_iff {pos : Addr → Fin k → Fin n} {coef : Addr → Fin k → F}
    {S : Finset Addr} {a : Addr} :
    RowsIndep pos coef (insert a S) ↔ RowsIndep pos coef S ∧
      (coefRow pos coef a ∈ Submodule.span F (coefRow pos coef '' (S : Set Addr)) → a ∈ S) := by
  have h := linearIndepOn_insert_iff (K := F) (s := (S : Set Addr)) (a := a)
    (f := coefRow pos coef)
  rw [← Finset.coe_insert] at h
  exact h

/-- One step of the greedy rule: keep `a` exactly when the rows kept so far stay linearly
independent with the row of `a` added. -/
noncomputable def greedyStep (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F)
    (S : Finset Addr) (a : Addr) : Finset Addr :=
  open Classical in if RowsIndep pos coef (insert a S) then insert a S else S

/-- The greedy rule: walk the request in order, keeping an address exactly when its row is
linearly independent of the rows kept so far. -/
noncomputable def greedySelect (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F)
    (l : List Addr) : Finset Addr :=
  l.foldl (greedyStep pos coef) ∅

theorem greedyStep_subset (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F)
    (S : Finset Addr) (a : Addr) : greedyStep pos coef S a ⊆ insert a S := by
  unfold greedyStep
  split_ifs
  · exact Finset.Subset.rfl
  · exact Finset.subset_insert a S

theorem subset_greedyStep (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F)
    (S : Finset Addr) (a : Addr) : S ⊆ greedyStep pos coef S a := by
  unfold greedyStep
  split_ifs
  · exact Finset.subset_insert a S
  · exact Finset.Subset.rfl

theorem rowsIndep_greedyStep {pos : Addr → Fin k → Fin n} {coef : Addr → Fin k → F}
    {S : Finset Addr} (hS : RowsIndep pos coef S) (a : Addr) :
    RowsIndep pos coef (greedyStep pos coef S a) := by
  unfold greedyStep
  split_ifs with h
  · exact h
  · exact hS

theorem greedyStep_eq_insert {pos : Addr → Fin k → Fin n} {coef : Addr → Fin k → F}
    {S : Finset Addr} {a : Addr} (h : RowsIndep pos coef (insert a S)) :
    greedyStep pos coef S a = insert a S := by
  rw [greedyStep, ite_eq_left h]

/-- The greedy step in terms of spans: if the kept addresses `S` have independent rows, a new
address is kept exactly when its row is not in the span of the kept rows. -/
theorem mem_greedyStep_iff {pos : Addr → Fin k → Fin n} {coef : Addr → Fin k → F}
    {S : Finset Addr} (hS : RowsIndep pos coef S) {a : Addr} (ha : a ∉ S) :
    a ∈ greedyStep pos coef S a ↔
      coefRow pos coef a ∉ Submodule.span F (coefRow pos coef '' (S : Set Addr)) := by
  unfold greedyStep
  split_ifs with h
  · exact iff_of_true (Finset.mem_insert_self a S) fun hmem =>
      ha ((rowsIndep_insert_iff.mp h).2 hmem)
  · refine iff_of_false ha fun hnot => h (rowsIndep_insert_iff.mpr ⟨hS, fun hmem => ?_⟩)
    exact absurd hmem hnot

theorem foldl_greedyStep_subset (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F)
    (l : List Addr) (S : Finset Addr) : l.foldl (greedyStep pos coef) S ⊆ S ∪ l.toFinset := by
  induction l generalizing S with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, List.toFinset_cons, Finset.union_insert, ← Finset.insert_union]
    exact (ih _).trans (Finset.union_subset_union_left (greedyStep_subset pos coef S a))

theorem subset_foldl_greedyStep (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F)
    (l : List Addr) (S : Finset Addr) : S ⊆ l.foldl (greedyStep pos coef) S := by
  induction l generalizing S with
  | nil => exact Finset.Subset.rfl
  | cons a l ih => exact (subset_greedyStep pos coef S a).trans (ih _)

theorem rowsIndep_foldl_greedyStep {pos : Addr → Fin k → Fin n} {coef : Addr → Fin k → F}
    (l : List Addr) {S : Finset Addr} (hS : RowsIndep pos coef S) :
    RowsIndep pos coef (l.foldl (greedyStep pos coef) S) := by
  induction l generalizing S with
  | nil => exact hS
  | cons a l ih => exact ih (rowsIndep_greedyStep hS a)

/-- Starting from `S`, the greedy rule keeps a whole list whose rows, together with those of
`S`, are linearly independent. -/
theorem foldl_greedyStep_eq {pos : Addr → Fin k → Fin n} {coef : Addr → Fin k → F}
    (l : List Addr) {S : Finset Addr} (h : RowsIndep pos coef (S ∪ l.toFinset)) :
    l.foldl (greedyStep pos coef) S = S ∪ l.toFinset := by
  induction l generalizing S with
  | nil => simp
  | cons a l ih =>
    rw [List.toFinset_cons, Finset.union_insert, ← Finset.insert_union] at h ⊢
    rw [List.foldl_cons, greedyStep_eq_insert (h.mono Finset.subset_union_left)]
    exact ih h

/-- The greedy rule drops an address only when its row is a linear combination of kept rows:
starting from `S` with independent rows, the row of every address of the list lies in the span
of the rows kept at the end. -/
theorem coefRow_mem_span_foldl_greedyStep {pos : Addr → Fin k → Fin n}
    {coef : Addr → Fin k → F} (l : List Addr) {S : Finset Addr} (hS : RowsIndep pos coef S)
    {a : Addr} (ha : a ∈ l) :
    coefRow pos coef a ∈
      Submodule.span F (coefRow pos coef '' ↑(l.foldl (greedyStep pos coef) S)) := by
  induction l generalizing S with
  | nil => simp at ha
  | cons b l ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp ha with rfl | hal
    · -- the row of the head is in the span of the rows kept right after its step
      have hstep : coefRow pos coef a ∈
          Submodule.span F (coefRow pos coef '' ↑(greedyStep pos coef S a)) := by
        by_cases h : RowsIndep pos coef (insert a S)
        · rw [greedyStep_eq_insert h]
          exact Submodule.subset_span ⟨a, Finset.mem_coe.mpr (Finset.mem_insert_self a S), rfl⟩
        · have hSa : greedyStep pos coef S a = S := by rw [greedyStep, ite_eq_right h]
          rw [hSa]
          by_contra hnot
          exact h (rowsIndep_insert_iff.mpr ⟨hS, fun hmem => absurd hmem hnot⟩)
      exact Submodule.span_mono (Set.image_mono
        (Finset.coe_subset.mpr (subset_foldl_greedyStep pos coef l _))) hstep
    · exact ih (rowsIndep_greedyStep hS b) hal

/-- The greedy rule keeps a maximal independent sub-family: the row of every requested address
lies in the span of the kept rows, so an address is dropped only when its row is a linear
combination of rows that are kept. -/
theorem coefRow_mem_span_greedySelect (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F)
    {l : List Addr} {a : Addr} (ha : a ∈ l) :
    coefRow pos coef a ∈
      Submodule.span F (coefRow pos coef '' ↑(greedySelect pos coef l)) :=
  coefRow_mem_span_foldl_greedyStep l (rowsIndep_empty pos coef) ha

/-- The greedy rule is a selection rule. -/
noncomputable def Selection.greedy : Selection F Addr k n where
  select := greedySelect
  subset pos coef l := by
    have h := foldl_greedyStep_subset pos coef l ∅
    rw [Finset.empty_union] at h
    exact h
  indep pos coef l := rowsIndep_foldl_greedyStep l (rowsIndep_empty pos coef)
  prefix_subset pos coef l j h := by
    have h' : RowsIndep pos coef (∅ ∪ (l.take j).toFinset) := by rwa [Finset.empty_union]
    calc (l.take j).toFinset
        = (l.take j).foldl (greedyStep pos coef) ∅ := by
          rw [foldl_greedyStep_eq _ h', Finset.empty_union]
      _ ⊆ (l.drop j).foldl (greedyStep pos coef) ((l.take j).foldl (greedyStep pos coef) ∅) :=
          subset_foldl_greedyStep pos coef _ _
      _ = greedySelect pos coef l := by
          rw [greedySelect, ← List.foldl_append, List.take_append_drop]

end Selection

/-! ## Generation and the game -/

namespace SilentDrop

variable {F G Addr σ : Type} {k n : ℕ} [Field F] [Fintype F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G] [Fintype Addr] [DecidableEq Addr] [NeZero n]

/-- Generation that never fails: keep the addresses selected from the ordered request `l`,
sample fresh uniform audit secret keys for them, and publish a uniformly random solution of
their system `M ⋆ V = AK`. -/
noncomputable def vecGen (sel : Selection F Addr k n) (g : G) (H : Addr → G)
    (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F) (l : List Addr) :
    ProbComp (Fin n → G) := do
  let sk ← $ᵗ (sel.select pos coef l → F)
  let ρ ← $ᵗ (Fin n → G)
  return encodeSet g H pos coef (sel.select pos coef l) sk ρ

omit [Fintype F] [SampleableType F] [SampleableType G] [Fintype Addr] [NeZero n] in
/-- Correctness: every kept address retrieves exactly its audit key from the published
vector. -/
theorem retrieveKey_encodeSet_select (sel : Selection F Addr k n) (g : G) (H : Addr → G)
    (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F) (l : List Addr)
    (sk : sel.select pos coef l → F) (ρ : Fin n → G) (a : sel.select pos coef l) :
    retrieveKey pos coef (encodeSet g H pos coef (sel.select pos coef l) sk ρ) a =
      auditKey g (sk a) (H a) :=
  retrieveKey_encodeSet (sel.indep pos coef l) sk ρ a

omit [Fintype F] [SampleableType F] [SampleableType G] [Fintype Addr] [NeZero n] in
/-- Coverage and correctness together: outside the bad event `Dep s`, every address among the
first `min s (length)` entries of a request is kept and retrieves exactly its audit key. -/
theorem retrieveKey_encodeSet_of_not_dep (sel : Selection F Addr k n) {s : ℕ}
    {pos : Addr → Fin k → Fin n} {coef : Addr → Fin k → F} (h : ¬Dep s pos coef) (g : G)
    (H : Addr → G) (l : List Addr) (sk : sel.select pos coef l → F) (ρ : Fin n → G) {a : Addr}
    (ha : a ∈ l.take s) :
    retrieveKey pos coef (encodeSet g H pos coef (sel.select pos coef l) sk ρ) a =
      auditKey g (sk ⟨a, sel.take_subset_of_not_dep h l (List.mem_toFinset.mpr ha)⟩) (H a) :=
  retrieveKey_encodeSet_select sel g H pos coef l sk ρ ⟨a, _⟩

omit [Fintype F] [Fintype Addr] [NeZero n] in
/-- **Uniformity**, in bind form: for every request, of any length, the published vector is a
uniformly random vector. -/
theorem vecGen_bind_eqd {γ : Type} {g : G} (hg : Function.Bijective (· • g : F → G))
    (sel : Selection F Addr k n) (H : Addr → G) (pos : Addr → Fin k → Fin n)
    (coef : Addr → Fin k → F) (l : List Addr) (f : (Fin n → G) → ProbComp γ) :
    (vecGen sel g H pos coef l >>= f) =ᵈ ($ᵗ (Fin n → G) >>= f) := by
  simp only [vecGen, bind_assoc, pure_bind]
  exact MembershipHidingPublic.encodeSet_eqd hg H pos coef _ f

omit [Fintype F] [Fintype Addr] [NeZero n] in
/-- **Uniformity**: for every request, of any length, the vector published by the never-failing
generation is exactly uniform on `Fin n → G`. -/
theorem vecGen_eqd {g : G} (hg : Function.Bijective (· • g : F → G))
    (sel : Selection F Addr k n) (H : Addr → G) (pos : Addr → Fin k → Fin n)
    (coef : Addr → Fin k → F) (l : List Addr) :
    vecGen sel g H pos coef l =ᵈ ($ᵗ (Fin n → G) : ProbComp (Fin n → G)) := by
  have h := vecGen_bind_eqd hg sel H pos coef l (pure : (Fin n → G) → ProbComp (Fin n → G))
  rwa [bind_pure, bind_pure] at h

/-- A Membership Hiding adversary against the never-failing generation with public hash
functions. Its two requests are ordered lists of any length. -/
structure Adversary (F G Addr σ : Type) (k n : ℕ) where
  /-- Choose two candidate requests, given all three hash tables. -/
  choose : (Addr → G) → (Addr → Fin k → Fin n) → (Addr → Fin k → F) →
    ProbComp (List Addr × List Addr × σ)
  /-- Guess which request was encoded, from the published vector. -/
  guess : σ → (Fin n → G) → ProbComp Bool

/-- The Membership Hiding experiment for the never-failing generation, encoding request `b`. -/
noncomputable def experiment (sel : Selection F Addr k n) (g : G)
    (A : Adversary F G Addr σ k n) (b : Bool) : ProbComp Bool := do
  let H ← $ᵗ (Addr → G)
  let pos ← $ᵗ (Addr → Fin k → Fin n)
  let coef ← $ᵗ (Addr → Fin k → F)
  let p ← A.choose H pos coef
  let V ← vecGen sel g H pos coef (if b then p.2.1 else p.1)
  A.guess p.2.2 V

/-- The experiment with a uniformly random vector in place of the encoding. -/
noncomputable def ideal (A : Adversary F G Addr σ k n) : ProbComp Bool := do
  let H ← $ᵗ (Addr → G)
  let pos ← $ᵗ (Addr → Fin k → Fin n)
  let coef ← $ᵗ (Addr → Fin k → F)
  let p ← A.choose H pos coef
  let V ← $ᵗ (Fin n → G)
  A.guess p.2.2 V

/-- The Membership Hiding advantage against the never-failing generation. -/
noncomputable def advantage (sel : Selection F Addr k n) (g : G)
    (A : Adversary F G Addr σ k n) : ℝ≥0∞ :=
  𝒟[experiment sel g A false].boolDist 𝒟[experiment sel g A true]

omit [Fintype F] in
/-- Encoding either request is the ideal experiment. -/
theorem experiment_eqd_ideal {g : G} (hg : Function.Bijective (· • g : F → G))
    (sel : Selection F Addr k n) (A : Adversary F G Addr σ k n) (b : Bool) :
    experiment sel g A b =ᵈ ideal A :=
  EvalDistEq.bind_right _ fun H => EvalDistEq.bind_right _ fun pos =>
    EvalDistEq.bind_right _ fun coef => EvalDistEq.bind_right _ fun _ =>
      vecGen_bind_eqd hg sel H pos coef _ _

omit [Fintype F] in
/-- **Theorem 4** for the never-failing generation with public hash functions: the published
vector hides the request perfectly, with no restriction on the requests. -/
theorem advantage_eq_zero {g : G} (hg : Function.Bijective (· • g : F → G))
    (sel : Selection F Addr k n) (A : Adversary F G Addr σ k n) : advantage sel g A = 0 := by
  rw [advantage, evalDist_eq_of_eqd ((experiment_eqd_ideal hg sel A false).trans
    (experiment_eqd_ideal hg sel A true).symm), MeasureTheory.Measure.boolDist_self]

omit [AddCommGroup G] [Module F G] [SampleableType G] in
/-- **Coverage.** Except with probability `depBound |Addr| n k s |F|` over the position and
coefficient tables, for every ordered request simultaneously, every address among its first
`min s (length)` entries is kept (nothing is dropped from the first `s` entries). -/
theorem prob_exists_dropped_le (sel : Selection F Addr k n) (s : ℕ) :
    Pr{let pos ← $ᵗ (Addr → Fin k → Fin n); let coef ← $ᵗ (Addr → Fin k → F)}[
        ∃ l : List Addr, ∃ a ∈ l.take s, a ∉ sel.select pos coef l] ≤
      ENNReal.ofReal (depBound (Fintype.card Addr) n k s (Fintype.card F)) := by
  have h := MembershipHidingPublic.prob_dep_le (F := F) (Addr := Addr) (k := k) (n := n) s
  rw [← SampleableType.prEvent_uniformSample_prod
    (fun ω : (Addr → Fin k → Fin n) × (Addr → Fin k → F) => Dep s ω.1 ω.2)] at h
  rw [← SampleableType.prEvent_uniformSample_prod
    (fun ω : (Addr → Fin k → Fin n) × (Addr → Fin k → F) =>
      ∃ l : List Addr, ∃ a ∈ l.take s, a ∉ sel.select ω.1 ω.2 l)]
  refine (prEvent_mono _ _ _ fun ω ⟨l, a, ha, hna⟩ => ?_).trans h
  by_contra hdep
  exact hna (sel.take_subset_of_not_dep hdep l (List.mem_toFinset.mpr ha))

end SilentDrop

end AuditPay
