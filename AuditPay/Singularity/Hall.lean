/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Basic.Real.Basic

/-!
# §7.4, structural part: Hall violators

The support graph of positions `pos : Fin n → Fin k → Fin n` joins row `r` to the columns
`pos r i`. If it has no perfect matching then, by Hall's theorem, some set `T` of `s` rows has
all of its positions inside a set `U` of `s - 1` columns. A union bound over `(T, U)` bounds
the number of such `pos`.
-/

open Finset

namespace AuditPay

variable {n k : ℕ}

/-- The support graph of `pos` has a perfect matching: some permutation `σ` of the columns has
`σ r` among the positions of row `r`, for every row `r`. -/
def HasMatching (pos : Fin n → Fin k → Fin n) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), ∀ r, ∃ i, pos r i = σ r

instance (pos : Fin n → Fin k → Fin n) : Decidable (HasMatching pos) := by
  unfold HasMatching; infer_instance

/-- Hall's theorem: without a perfect matching, some set of rows `T` has fewer than `#T`
columns among its positions. -/
theorem exists_hall_violator {pos : Fin n → Fin k → Fin n} (h : ¬HasMatching pos) :
    ∃ T : Finset (Fin n), #(T.biUnion fun r => univ.image (pos r)) < #T := by
  by_contra hT
  push Not at hT
  obtain ⟨f, hf, hfm⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective _).mp hT
  exact h ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf), fun r => by
    simpa using hfm r⟩

/-- The number of positions whose rows in `T` all point into the columns `U`. -/
theorem card_filter_forall_mem (T U : Finset (Fin n)) :
    #(univ.filter fun pos : Fin n → Fin k → Fin n => ∀ r ∈ T, ∀ i, pos r i ∈ U) =
      #U ^ (k * #T) * n ^ (k * (n - #T)) := by
  have : (univ.filter fun pos : Fin n → Fin k → Fin n => ∀ r ∈ T, ∀ i, pos r i ∈ U) =
      Fintype.piFinset fun r => if r ∈ T then Fintype.piFinset fun _ : Fin k => U else univ := by
    ext pos
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    refine ⟨fun h r => ?_, fun h r hr i => ?_⟩
    · split_ifs with hr
      · exact Fintype.mem_piFinset.mpr (h r hr)
      · exact mem_univ _
    · have := h r
      rw [ite_eq_left hr, Fintype.mem_piFinset] at this
      exact this i
  rw [this, Fintype.card_piFinset]
  simp only [apply_ite card, Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin,
    Fintype.card_fun, prod_ite, filter_univ_mem]
  rw [← compl_filter, filter_univ_mem, card_compl, Fintype.card_fin, ← pow_mul, ← pow_mul]

/-- Every `pos` without a perfect matching has some set `T` of `s ≥ 1` rows whose positions all
lie in some set `U` of `s - 1` columns. -/
theorem filter_not_hasMatching_subset :
    (univ.filter fun pos : Fin n → Fin k → Fin n => ¬HasMatching pos) ⊆
      (Icc 1 n).biUnion fun s =>
        (powersetCard s univ ×ˢ powersetCard (s - 1) univ).biUnion fun TU =>
          univ.filter fun pos : Fin n → Fin k → Fin n => ∀ r ∈ TU.1, ∀ i, pos r i ∈ TU.2 := by
  intro pos hpos
  rw [mem_filter] at hpos
  obtain ⟨T, hT⟩ := exists_hall_violator hpos.2
  have hTn : #T ≤ n := by simpa using card_le_univ T
  obtain ⟨U, hWU, -, hU⟩ := exists_subsuperset_card_eq
    (subset_univ (T.biUnion fun r => univ.image (pos r))) (n := #T - 1) (by omega)
    (by simp only [card_univ, Fintype.card_fin]; omega)
  simp only [mem_biUnion, mem_Icc, mem_product, mem_powersetCard, subset_univ, true_and,
    mem_filter, mem_univ]
  refine ⟨#T, ⟨by omega, hTn⟩, (T, U), ⟨rfl, hU⟩, fun r hr i => hWU ?_⟩
  simp only [mem_biUnion, mem_image]
  exact ⟨r, hr, i, mem_univ _, rfl⟩

/-- Union bound over Hall violators, in `ℕ`. -/
theorem card_not_hasMatching_le_nat :
    #(univ.filter fun pos : Fin n → Fin k → Fin n => ¬HasMatching pos) ≤
      ∑ s ∈ Icc 1 n, n.choose s * n.choose (s - 1) * ((s - 1) ^ (k * s) * n ^ (k * (n - s))) := by
  refine (card_le_card filter_not_hasMatching_subset).trans
    (card_biUnion_le.trans (sum_le_sum fun s hs => ?_))
  refine card_biUnion_le.trans (le_of_eq ?_)
  rw [sum_congr rfl fun TU hTU => ?_, sum_const, card_product, card_powersetCard,
    card_powersetCard, card_univ, Fintype.card_fin, smul_eq_mul]
  rw [mem_product, mem_powersetCard, mem_powersetCard] at hTU
  rw [card_filter_forall_mem, hTU.1.2, hTU.2.2]

/-- Union bound over Hall violators: the fraction of positions without a perfect matching is at
most `∑_{s=1}^{n} C(n,s) · C(n,s-1) · ((s-1)/n)^{k·s}`. -/
theorem card_not_hasMatching_le :
    (#(univ.filter fun pos : Fin n → Fin k → Fin n => ¬HasMatching pos) : ℝ) ≤
      (∑ s ∈ Icc 1 n, (n.choose s : ℝ) * (n.choose (s - 1) : ℝ) *
        (((s : ℝ) - 1) / n) ^ (k * s)) * Fintype.card (Fin n → Fin k → Fin n) := by
  refine (Nat.cast_le.mpr card_not_hasMatching_le_nat).trans (le_of_eq ?_)
  push_cast
  rw [sum_mul]
  refine sum_congr rfl fun s hs => ?_
  rw [mem_Icc] at hs
  simp only [Fintype.card_fun, Fintype.card_fin]
  push_cast
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [Nat.cast_sub hs.1, Nat.cast_one, div_pow, ← pow_mul,
    show k * n = k * s + k * (n - s) by rw [← mul_add]; congr 1; omega, pow_add]
  field_simp

end AuditPay
