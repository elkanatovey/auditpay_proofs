/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.Singularity

/-!
# Public-hash analysis, structural part: the slots hit by a set of addresses

`hitSlots pos T` is the set of slots of the vector that the position hashes of the addresses in
`T` point to. For a fixed set `U` of slots, the probability over uniform positions that
`hitSlots pos T ⊆ U` is `(|U| / n) ^ (k · |T|)`. This is the count behind
`AuditPay.card_filter_forall_mem` (§7.4), with the rows indexed by an arbitrary finite address
type instead of `Fin n`.
-/

open Finset

namespace AuditPay

variable {Addr : Type*} {n k : ℕ}

/-- The slots hit by the position hashes of the addresses in `T`. -/
def hitSlots (pos : Addr → Fin k → Fin n) (T : Finset Addr) : Finset (Fin n) :=
  T.biUnion fun a => univ.image (pos a)

theorem mem_hitSlots {pos : Addr → Fin k → Fin n} {T : Finset Addr} {j : Fin n} :
    j ∈ hitSlots pos T ↔ ∃ a ∈ T, ∃ i, pos a i = j := by
  simp [hitSlots]

theorem hitSlots_subset_iff {pos : Addr → Fin k → Fin n} {T : Finset Addr}
    {U : Finset (Fin n)} : hitSlots pos T ⊆ U ↔ ∀ a ∈ T, ∀ i, pos a i ∈ U := by
  refine ⟨fun h a ha i => h (mem_hitSlots.mpr ⟨a, ha, i, rfl⟩), fun h j hj => ?_⟩
  obtain ⟨a, ha, i, rfl⟩ := mem_hitSlots.mp hj
  exact h a ha i

theorem card_hitSlots_le (pos : Addr → Fin k → Fin n) (T : Finset Addr) :
    #(hitSlots pos T) ≤ n := by
  simpa using card_le_univ (hitSlots pos T)

variable [Fintype Addr] [DecidableEq Addr]

/-- The number of position tables whose rows in `T` all point into the slots `U`. -/
theorem card_filter_hitSlots_subset (T : Finset Addr) (U : Finset (Fin n)) :
    #(univ.filter fun pos : Addr → Fin k → Fin n => hitSlots pos T ⊆ U) =
      #U ^ (k * #T) * n ^ (k * (Fintype.card Addr - #T)) := by
  have : (univ.filter fun pos : Addr → Fin k → Fin n => hitSlots pos T ⊆ U) =
      Fintype.piFinset fun a => if a ∈ T then Fintype.piFinset fun _ : Fin k => U else univ := by
    ext pos
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, hitSlots_subset_iff]
    refine ⟨fun h a => ?_, fun h a ha i => ?_⟩
    · split_ifs with ha
      · exact Fintype.mem_piFinset.mpr (h a ha)
      · exact mem_univ _
    · have := h a
      rw [ite_eq_left ha, Fintype.mem_piFinset] at this
      exact this i
  rw [this, Fintype.card_piFinset]
  simp only [apply_ite card, Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin,
    Fintype.card_fun, prod_ite, filter_univ_mem]
  rw [← compl_filter, filter_univ_mem, card_compl, ← pow_mul, ← pow_mul]

/-- The fraction of position tables whose rows in `T` all point into the slots `U` is
`(|U| / n) ^ (k · |T|)`. -/
theorem card_filter_hitSlots_subset_real (T : Finset Addr) (U : Finset (Fin n)) :
    (#(univ.filter fun pos : Addr → Fin k → Fin n => hitSlots pos T ⊆ U) : ℝ) =
      ((#U : ℝ) / n) ^ (k * #T) * Fintype.card (Addr → Fin k → Fin n) := by
  have hTQ : #T ≤ Fintype.card Addr := card_le_univ T
  have hcard : (Fintype.card (Addr → Fin k → Fin n) : ℝ) =
      (n : ℝ) ^ (k * #T) * (n : ℝ) ^ (k * (Fintype.card Addr - #T)) := by
    rw [← pow_add, ← mul_add, Nat.add_sub_cancel' hTQ]
    simp [pow_mul]
  rw [card_filter_hitSlots_subset, hcard]
  push_cast
  rcases Nat.eq_zero_or_pos #U with hU | hU
  · rw [hU]
    rcases Nat.eq_zero_or_pos (k * #T) with h0 | h0
    · simp [h0]
    · simp [h0.ne']
  · have hn : (n : ℝ) ≠ 0 := by
      obtain ⟨j, -⟩ := card_pos.mp hU
      exact_mod_cast j.pos.ne'
    rw [div_pow]
    field_simp

end AuditPay
