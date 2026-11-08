/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.Dependence.Basic
import AuditPay.Dependence.Positions
import AuditPay.Dependence.Algebraic

/-!
# Public hash functions: the probability that some small set of addresses is unencodable

The hash functions of Algorithm 3 are fixed and public, and an adversary chooses which
addresses to monitor after evaluating them. The encoding of a set `T` of addresses succeeds
when the rows of `T` are linearly independent, so the bad event is

  `Dep s`: some set of at most `s` addresses has linearly dependent rows.

For position and coefficient hashes that are uniformly random functions on a finite address
type `Addr` with `Q = |Addr|` (the addresses whose hashes the adversary has evaluated), this
file proves

  `Pr[Dep s] ≤ depBound Q n k s |F|`,

where

  `depBound Q n k s q = ∑_{t=1}^{s} C(Q,t) · (depStruct n k t + depAlg n k t q)`,
  `depStruct n k t = C(n,t-1) · ((t-1)/n)^{k·t}`,
  `depAlg n k t q = ∑_{u=t}^{n} C(n,u) · (u/n)^{k·t} · q^{t-1} / q^u`.

## Proof

If some set of at most `s` rows is dependent, the support `T` of a dependency is a nonempty set
of `t ≤ s` addresses carrying a dependency `∑ a ∈ T, γ a • row a = 0` with every `γ a ≠ 0`
(`exists_isNZDep_of_dep`). A union bound over `T` gives the factor `C(Q,t)`. Let `U(T)` be
the set of slots hit by the positions of `T`.

* Structural case, `|U(T)| ≤ t - 1`: then `U(T)` lies in one of the `C(n,t-1)` sets of `t - 1`
  slots, and it lies in a fixed set `U` of slots with probability `(|U|/n)^{k·t}`. This is the
  Hall-violator count of `AuditPay.Singularity.Hall`, with `t` of the `Q` addresses in place of
  `s` of the `n` rows.
* Algebraic case, `|U(T)| = u ≥ t`: scale `γ` to be `1` at a fixed address of `T`, which leaves
  `|F|^{t-1}` candidates. For each of them, and for fixed positions, the dependency holds with
  probability at most `|F|^{-u}` over the coefficients
  (`card_filter_coef_dep_le`). A union bound over the value `U` of `U(T)` gives the factor
  `C(n,u) · (u/n)^{k·t}`.

Probabilities are stated by counting over the finite sample space of hash outputs, as in
`AuditPay.Singularity`. The theorem holds for every `s`; for `s > n` the bound exceeds `1`
whenever `Q > n`, as it must (any `n + 1` rows are dependent).
-/

open Finset

namespace AuditPay

/-! ## The bound -/

/-- Structural term of `depBound` for sets of `t` addresses: `C(n,t-1) · ((t-1)/n)^{k·t}`. -/
noncomputable def depStruct (n k t : ℕ) : ℝ :=
  (n.choose (t - 1) : ℝ) * (((t : ℝ) - 1) / n) ^ (k * t)

/-- Algebraic term of `depBound` for sets of `t` addresses over a field of `q` elements:
`∑_{u=t}^{n} C(n,u) · (u/n)^{k·t} · q^{t-1} / q^u`. -/
noncomputable def depAlg (n k t q : ℕ) : ℝ :=
  ∑ u ∈ Icc t n, (n.choose u : ℝ) * ((u : ℝ) / n) ^ (k * t) * ((q : ℝ) ^ (t - 1) / (q : ℝ) ^ u)

/-- The public-hash dependence bound, for `Q` addresses, a vector of `n` slots, `k` hash
functions, sets of at most `s` addresses, and a field of `q` elements:
`∑_{t=1}^{s} C(Q,t) · (depStruct n k t + depAlg n k t q)`. -/
noncomputable def depBound (Q n k s q : ℕ) : ℝ :=
  ∑ t ∈ Icc 1 s, (Q.choose t : ℝ) * (depStruct n k t + depAlg n k t q)

theorem depStruct_nonneg (n k t : ℕ) : 0 ≤ depStruct n k t := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp [depStruct]
  · have h1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
    exact mul_nonneg (Nat.cast_nonneg _)
      (pow_nonneg (div_nonneg (by linarith) (Nat.cast_nonneg _)) _)

theorem depAlg_nonneg (n k t q : ℕ) : 0 ≤ depAlg n k t q :=
  sum_nonneg fun _ _ => by positivity

theorem depBound_nonneg (Q n k s q : ℕ) : 0 ≤ depBound Q n k s q :=
  sum_nonneg fun t _ =>
    mul_nonneg (Nat.cast_nonneg _) (add_nonneg (depStruct_nonneg n k t) (depAlg_nonneg n k t q))

/-- The bound grows with the cap on the set size. -/
theorem depBound_mono (Q n k q : ℕ) {s s' : ℕ} (h : s ≤ s') :
    depBound Q n k s q ≤ depBound Q n k s' q :=
  sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right h) fun t _ _ =>
    mul_nonneg (Nat.cast_nonneg _) (add_nonneg (depStruct_nonneg n k t) (depAlg_nonneg n k t q))

/-! ## Counting helpers -/

/-- Union bound over a finite index set, for counts in `ℝ`. -/
theorem card_filter_le_sum_card_filter {α ι : Type*} [Fintype α] (I : Finset ι) (P : α → Prop)
    (R : ι → α → Prop) [DecidablePred P] [∀ i, DecidablePred (R i)]
    (h : ∀ x, P x → ∃ i ∈ I, R i x) :
    (#(univ.filter P) : ℝ) ≤ ∑ i ∈ I, (#(univ.filter (R i)) : ℝ) := by
  classical
  have hsub : univ.filter P ⊆ I.biUnion fun i => univ.filter (R i) := fun x hx => by
    obtain ⟨i, hi, hR⟩ := h x (mem_filter.mp hx).2
    exact mem_biUnion.mpr ⟨i, hi, mem_filter.mpr ⟨mem_univ _, hR⟩⟩
  exact_mod_cast (card_le_card hsub).trans card_biUnion_le

/-- Counting a subset of a product type cut out by a condition on the first factor. -/
theorem card_filter_fst {α β : Type*} [Fintype α] [Fintype β] (P : α → Prop) [DecidablePred P] :
    #(univ.filter fun x : α × β => P x.1) = #(univ.filter P) * Fintype.card β :=
  card_filter_fst_equiv (Equiv.refl _) P

variable {F : Type*} [Field F] [Fintype F] {Addr : Type*} [Fintype Addr] [DecidableEq Addr]
  {n k : ℕ}

/-- The sample space: position and coefficient hash tables. -/
local notation "Ω" => (Addr → Fin k → Fin n) × (Addr → Fin k → F)

/-! ## Structural case -/

/-- `T` fails structurally: its positions all lie in some set of `|T| - 1` slots. -/
def StructBad (pos : Addr → Fin k → Fin n) (T : Finset Addr) : Prop :=
  ∃ U ∈ powersetCard (#T - 1) (univ : Finset (Fin n)), hitSlots pos T ⊆ U

omit [Field F] in
/-- A nonempty set `T` of `t` addresses fails structurally with probability at most
`C(n,t-1) · ((t-1)/n)^{k·t}`. -/
theorem card_filter_structBad_le (T : Finset Addr) (hT : T.Nonempty)
    [DecidablePred fun ω : Ω => StructBad ω.1 T] :
    (#(univ.filter fun ω : Ω => StructBad ω.1 T) : ℝ) ≤
      depStruct n k #T * Fintype.card Ω := by
  classical
  have h1 : 1 ≤ #T := hT.card_pos
  calc (#(univ.filter fun ω : Ω => StructBad ω.1 T) : ℝ)
      ≤ ∑ U ∈ powersetCard (#T - 1) (univ : Finset (Fin n)),
          (#(univ.filter fun ω : Ω => hitSlots ω.1 T ⊆ U) : ℝ) :=
        card_filter_le_sum_card_filter _ _ _ fun ω h => h
    _ = ∑ U ∈ powersetCard (#T - 1) (univ : Finset (Fin n)),
          (((#T : ℝ) - 1) / n) ^ (k * #T) * Fintype.card Ω := by
        refine sum_congr rfl fun U hU => ?_
        rw [card_filter_fst fun pos : Addr → Fin k → Fin n => hitSlots pos T ⊆ U, Nat.cast_mul,
          card_filter_hitSlots_subset_real, (mem_powersetCard.mp hU).2, Nat.cast_sub h1,
          Nat.cast_one, Fintype.card_prod, Nat.cast_mul, mul_assoc]
    _ = depStruct n k #T * Fintype.card Ω := by
        rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul, depStruct,
          mul_assoc]

/-! ## Algebraic case -/

/-- `T` fails algebraically: it hits at least `|T|` slots, yet its rows satisfy a dependency
with no zero coefficient. -/
def AlgBad (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F) (T : Finset Addr) : Prop :=
  #T ≤ #(hitSlots pos T) ∧ ∃ γ, IsNZDep pos coef T γ

/-- For fixed coefficients `γ` and a fixed set `U` of slots: the positions of `T` hit exactly
`U` and `γ` is a dependency with no zero coefficient, with probability at most
`(|U|/n)^{k·|T|} / |F|^{|U|}`. -/
theorem card_filter_hitSlots_eq_isNZDep_le (T : Finset Addr) (γ : Addr → F) (U : Finset (Fin n))
    [DecidablePred fun ω : Ω => hitSlots ω.1 T = U ∧ IsNZDep ω.1 ω.2 T γ] :
    (#(univ.filter fun ω : Ω => hitSlots ω.1 T = U ∧ IsNZDep ω.1 ω.2 T γ) : ℝ) ≤
      ((#U : ℝ) / n) ^ (k * #T) / (Fintype.card F : ℝ) ^ #U * Fintype.card Ω := by
  classical
  set cB : ℝ := ((Fintype.card (Addr → Fin k → F) : ℕ) : ℝ) with hcB
  have hterm : ∀ pos : Addr → Fin k → Fin n,
      (#(univ.filter fun coef : Addr → Fin k → F =>
        hitSlots pos T = U ∧ IsNZDep pos coef T γ) : ℝ) ≤
        if hitSlots pos T ⊆ U then cB / (Fintype.card F : ℝ) ^ #U else 0 := by
    intro pos
    by_cases hU : hitSlots pos T = U
    · rw [ite_eq_left hU.subset]
      by_cases hγ : ∀ a ∈ T, γ a ≠ 0
      · have h := card_filter_coef_dep_le pos T γ hγ
        rw [hU] at h
        refine le_trans ?_ h
        have hsub : (univ.filter fun coef : Addr → Fin k → F =>
            hitSlots pos T = U ∧ IsNZDep pos coef T γ) ⊆
            univ.filter fun coef : Addr → Fin k → F =>
              ∑ a ∈ T, γ a • coefRow pos coef a = 0 := fun coef hcoef => by
          rw [mem_filter] at hcoef ⊢
          exact ⟨hcoef.1, hcoef.2.2.2⟩
        exact_mod_cast card_le_card hsub
      · rw [filter_false_of_mem fun coef _ h => hγ h.2.1, card_empty, Nat.cast_zero]
        positivity
    · rw [filter_false_of_mem fun coef _ h => hU h.1, card_empty, Nat.cast_zero]
      split_ifs <;> positivity
  calc (#(univ.filter fun ω : Ω => hitSlots ω.1 T = U ∧ IsNZDep ω.1 ω.2 T γ) : ℝ)
      = ∑ pos : Addr → Fin k → Fin n, (#(univ.filter fun coef : Addr → Fin k → F =>
          hitSlots pos T = U ∧ IsNZDep pos coef T γ) : ℝ) := by
        rw [card_filter_prod_eq_sum]
        push_cast
        rfl
    _ ≤ ∑ pos : Addr → Fin k → Fin n,
          if hitSlots pos T ⊆ U then cB / (Fintype.card F : ℝ) ^ #U else 0 :=
        sum_le_sum fun pos _ => hterm pos
    _ = (#(univ.filter fun pos : Addr → Fin k → Fin n => hitSlots pos T ⊆ U) : ℝ) *
          (cB / (Fintype.card F : ℝ) ^ #U) := by
        rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
    _ = ((#U : ℝ) / n) ^ (k * #T) / (Fintype.card F : ℝ) ^ #U * Fintype.card Ω := by
        rw [card_filter_hitSlots_subset_real, Fintype.card_prod, Nat.cast_mul]
        ring

/-- Coefficient vectors normalised at `a₀`: equal to `1` at `a₀`, arbitrary on the rest of `T`,
and `0` outside `T`. Every dependency on `T` that is nonzero at `a₀ ∈ T` has exactly one
scalar multiple of this form. -/
def normCoeffs (T : Finset Addr) (a₀ : Addr) : Finset (Addr → F) :=
  Fintype.piFinset fun a => if a ∈ T.erase a₀ then univ else {if a = a₀ then 1 else 0}

/-- There are `|F|^{|T|-1}` normalised coefficient vectors. -/
theorem card_normCoeffs {T : Finset Addr} {a₀ : Addr} (ha₀ : a₀ ∈ T) :
    #(normCoeffs (F := F) T a₀) = Fintype.card F ^ (#T - 1) := by
  rw [normCoeffs, Fintype.card_piFinset]
  simp only [apply_ite card, card_univ, card_singleton]
  rw [prod_ite_mem, univ_inter, prod_const, card_erase_of_mem ha₀]

/-- A dependency with no zero coefficient can be scaled to be `1` at a given address of `T`. -/
theorem IsNZDep.exists_normCoeffs {pos : Addr → Fin k → Fin n} {coef : Addr → Fin k → F}
    {T : Finset Addr} {γ : Addr → F} (h : IsNZDep pos coef T γ) {a₀ : Addr} (ha₀ : a₀ ∈ T) :
    ∃ γ' ∈ normCoeffs T a₀, IsNZDep pos coef T γ' := by
  have h0 : γ a₀ ≠ 0 := h.1 a₀ ha₀
  refine ⟨fun a => if a ∈ T then (γ a₀)⁻¹ * γ a else 0, ?_, fun a ha => ?_, ?_⟩
  · rw [normCoeffs, Fintype.mem_piFinset]
    intro a
    by_cases ha : a ∈ T.erase a₀
    · rw [ite_eq_left ha]
      exact mem_univ _
    · rw [ite_eq_right ha, mem_singleton]
      by_cases haa : a = a₀
      · rw [haa]
        simp [ha₀, h0]
      · have haT : a ∉ T := fun haT => ha (mem_erase.mpr ⟨haa, haT⟩)
        simp [haT, haa]
  · simp only [ite_eq_left ha]
    exact mul_ne_zero (inv_ne_zero h0) (h.1 a ha)
  · calc ∑ a ∈ T, (if a ∈ T then (γ a₀)⁻¹ * γ a else 0) • coefRow pos coef a
        = ∑ a ∈ T, (γ a₀)⁻¹ • (γ a • coefRow pos coef a) :=
          sum_congr rfl fun a ha => by rw [ite_eq_left ha, mul_smul]
      _ = 0 := by rw [← smul_sum, h.2, smul_zero]

/-- A nonempty set `T` of `t` addresses fails algebraically with probability at most
`∑_{u=t}^{n} C(n,u) · (u/n)^{k·t} · |F|^{t-1} / |F|^u`. -/
theorem card_filter_algBad_le (T : Finset Addr) (hT : T.Nonempty)
    [DecidablePred fun ω : Ω => AlgBad ω.1 ω.2 T] :
    (#(univ.filter fun ω : Ω => AlgBad ω.1 ω.2 T) : ℝ) ≤
      depAlg n k #T (Fintype.card F) * Fintype.card Ω := by
  classical
  obtain ⟨a₀, ha₀⟩ := hT
  calc (#(univ.filter fun ω : Ω => AlgBad ω.1 ω.2 T) : ℝ)
      ≤ ∑ γ ∈ normCoeffs (F := F) T a₀, (#(univ.filter fun ω : Ω =>
          #T ≤ #(hitSlots ω.1 T) ∧ IsNZDep ω.1 ω.2 T γ) : ℝ) :=
        card_filter_le_sum_card_filter _ _ _ fun ω ⟨hle, γ, hγ⟩ => by
          obtain ⟨γ', hγ', hdep⟩ := hγ.exists_normCoeffs ha₀
          exact ⟨γ', hγ', hle, hdep⟩
    _ ≤ ∑ _γ ∈ normCoeffs (F := F) T a₀, ∑ u ∈ Icc #T n,
          ∑ _U ∈ powersetCard u (univ : Finset (Fin n)),
            ((u : ℝ) / n) ^ (k * #T) / (Fintype.card F : ℝ) ^ u * Fintype.card Ω := by
        refine sum_le_sum fun γ _ => ?_
        refine (card_filter_le_sum_card_filter (Icc #T n) _
          (fun u (ω : Ω) => #(hitSlots ω.1 T) = u ∧ IsNZDep ω.1 ω.2 T γ)
          fun ω ⟨hle, hdep⟩ =>
            ⟨_, mem_Icc.mpr ⟨hle, card_hitSlots_le _ _⟩, rfl, hdep⟩).trans ?_
        refine sum_le_sum fun u _ => ?_
        refine (card_filter_le_sum_card_filter (powersetCard u (univ : Finset (Fin n))) _
          (fun U (ω : Ω) => hitSlots ω.1 T = U ∧ IsNZDep ω.1 ω.2 T γ)
          fun ω ⟨hu, hdep⟩ =>
            ⟨_, mem_powersetCard.mpr ⟨subset_univ _, hu⟩, rfl, hdep⟩).trans ?_
        refine sum_le_sum fun U hU => ?_
        rw [← (mem_powersetCard.mp hU).2]
        exact card_filter_hitSlots_eq_isNZDep_le T γ U
    _ = depAlg n k #T (Fintype.card F) * Fintype.card Ω := by
        simp only [sum_const, card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul,
          card_normCoeffs ha₀]
        rw [depAlg, sum_mul, mul_sum]
        refine sum_congr rfl fun u _ => ?_
        push_cast
        ring

/-! ## The dependence bound -/

omit [Fintype F] [DecidableEq Addr] in
/-- A dependent set of at most `s` addresses yields a set of `t ≤ s` addresses that fails
structurally or algebraically. -/
theorem exists_bad_of_dep {s : ℕ} {pos : Addr → Fin k → Fin n} {coef : Addr → Fin k → F}
    (h : Dep s pos coef) :
    ∃ t ∈ Icc 1 s, ∃ T ∈ powersetCard t (univ : Finset Addr),
      StructBad pos T ∨ AlgBad pos coef T := by
  obtain ⟨T, hne, hTs, hTn, γ, hγ⟩ := exists_isNZDep_of_dep h
  refine ⟨#T, mem_Icc.mpr ⟨hne.card_pos, hTs⟩, T, mem_powersetCard.mpr ⟨subset_univ _, rfl⟩, ?_⟩
  rcases lt_or_ge #(hitSlots pos T) #T with hlt | hge
  · obtain ⟨U, hU, -, hUc⟩ := exists_subsuperset_card_eq (subset_univ (hitSlots pos T))
      (n := #T - 1) (by omega) (by simp only [card_univ, Fintype.card_fin]; omega)
    exact Or.inl ⟨U, mem_powersetCard.mpr ⟨subset_univ _, hUc⟩, hU⟩
  · exact Or.inr ⟨hge, γ, hγ⟩

/-- **Dependence bound** for public hash functions, by counting: among all position and
coefficient hash tables on `Addr`, the fraction for which some set of at most `s` addresses has
linearly dependent rows is at most `depBound |Addr| n k s |F|`. -/
theorem card_dep_le (s : ℕ) [DecidablePred fun ω : Ω => Dep s ω.1 ω.2] :
    (#(univ.filter fun ω : Ω => Dep s ω.1 ω.2) : ℝ) ≤
      depBound (Fintype.card Addr) n k s (Fintype.card F) * Fintype.card Ω := by
  classical
  have hT : ∀ T : Finset Addr, T.Nonempty →
      (#(univ.filter fun ω : Ω => StructBad ω.1 T ∨ AlgBad ω.1 ω.2 T) : ℝ) ≤
        (depStruct n k #T + depAlg n k #T (Fintype.card F)) * Fintype.card Ω := by
    intro T hne
    rw [add_mul]
    refine le_trans ?_
      (add_le_add (card_filter_structBad_le T hne) (card_filter_algBad_le T hne))
    rw [filter_or]
    exact_mod_cast card_union_le _ _
  calc (#(univ.filter fun ω : Ω => Dep s ω.1 ω.2) : ℝ)
      ≤ ∑ t ∈ Icc 1 s, (#(univ.filter fun ω : Ω =>
          ∃ T ∈ powersetCard t (univ : Finset Addr),
            StructBad ω.1 T ∨ AlgBad ω.1 ω.2 T) : ℝ) :=
        card_filter_le_sum_card_filter _ _ _ fun ω h => exists_bad_of_dep h
    _ ≤ ∑ t ∈ Icc 1 s, ∑ T ∈ powersetCard t (univ : Finset Addr),
          (#(univ.filter fun ω : Ω => StructBad ω.1 T ∨ AlgBad ω.1 ω.2 T) : ℝ) :=
        sum_le_sum fun t _ => card_filter_le_sum_card_filter _ _ _ fun ω h => h
    _ ≤ ∑ t ∈ Icc 1 s, ∑ _T ∈ powersetCard t (univ : Finset Addr),
          (depStruct n k t + depAlg n k t (Fintype.card F)) * Fintype.card Ω := by
        refine sum_le_sum fun t ht => sum_le_sum fun T hT' => ?_
        have hc := (mem_powersetCard.mp hT').2
        have hne : T.Nonempty := card_pos.mp (by rw [hc]; exact (mem_Icc.mp ht).1)
        rw [← hc]
        exact hT T hne
    _ = depBound (Fintype.card Addr) n k s (Fintype.card F) * Fintype.card Ω := by
        rw [depBound, sum_mul]
        refine sum_congr rfl fun t _ => ?_
        rw [sum_const, card_powersetCard, card_univ, nsmul_eq_mul, mul_assoc]

/-- `card_dep_le` as a fraction of the sample space. -/
theorem card_dep_div_le (s : ℕ) [DecidablePred fun ω : Ω => Dep s ω.1 ω.2] :
    (#(univ.filter fun ω : Ω => Dep s ω.1 ω.2) : ℝ) / Fintype.card Ω ≤
      depBound (Fintype.card Addr) n k s (Fintype.card F) :=
  div_le_of_le_mul₀ (Nat.cast_nonneg _) (depBound_nonneg _ _ _ _ _) (card_dep_le s)

end AuditPay
