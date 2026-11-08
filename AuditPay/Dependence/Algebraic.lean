/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.Dependence.Basic
import AuditPay.Dependence.Positions

/-!
# Public-hash analysis, algebraic part: one fixed dependency

Fix the positions `pos`, a set `T` of addresses and coefficients `γ` that are nonzero on `T`.
The rows of `T` satisfy `∑ a ∈ T, γ a • row a = 0` for at most a `|F| ^ (-u)` fraction of the
coefficient tables, where `u` is the number of slots hit by `T`.

Reason: slot `j` contributes the equation `∑_{(a, i) : a ∈ T, pos a i = j} γ a · coef a i = 0`.
For a hit slot this is a nontrivial linear equation, and different slots involve disjoint sets
of coefficients. Formally, pick one "pivot" entry `(a, i)` with `pos a i = j` for each hit slot
`j`; a solution is determined by its values off the pivots, so there are at most
`|F| ^ (|Addr| · k - u)` solutions.

`AuditPay.Singularity.Algebraic` bounds the same kind of event for one fixed square matrix by
Schwartz–Zippel on its determinant (`n / |F|`). That bound does not survive a union over the
subsets an adversary can choose from; the per-dependency count here (`|F| ^ (-u)`, to be
multiplied by the `|F| ^ (|T| - 1)` dependencies up to scaling) does.
-/

open Finset

namespace AuditPay

variable {F : Type*} [Field F] {Addr : Type*} {n k : ℕ}

/-- The row of an address is additive in the coefficient table. -/
theorem coefRow_sub (pos : Addr → Fin k → Fin n) (c c' : Addr → Fin k → F) (a : Addr) :
    coefRow pos (c - c') a = coefRow pos c a - coefRow pos c' a := by
  ext j
  simp only [coefRow, Pi.sub_apply, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

variable [Fintype F] [Fintype Addr] [DecidableEq Addr]

/-- For coefficients `γ` nonzero on `T`, the coefficient tables satisfying the dependency
`∑ a ∈ T, γ a • row a = 0` number at most `|F| ^ (|Addr| · k - u)`, where `u` is the number of
slots hit by `T`. Stated without subtraction. -/
theorem card_filter_coef_dep_mul_le (pos : Addr → Fin k → Fin n) (T : Finset Addr) (γ : Addr → F)
    (hγ : ∀ a ∈ T, γ a ≠ 0)
    [DecidablePred fun coef : Addr → Fin k → F => ∑ a ∈ T, γ a • coefRow pos coef a = 0] :
    #(univ.filter fun coef : Addr → Fin k → F => ∑ a ∈ T, γ a • coefRow pos coef a = 0) *
      Fintype.card F ^ #(hitSlots pos T) ≤ Fintype.card (Addr → Fin k → F) := by
  classical
  -- one pivot entry `(a, i)`, with `a ∈ T` and `pos a i = j`, for each hit slot `j`
  have hex : ∀ j : {j // j ∈ hitSlots pos T},
      ∃ x : Addr × Fin k, x.1 ∈ T ∧ pos x.1 x.2 = j := by
    rintro ⟨j, hj⟩
    obtain ⟨a, ha, i, hi⟩ := mem_hitSlots.mp hj
    exact ⟨(a, i), ha, hi⟩
  choose piv hpivT hpiv using hex
  have hpiv_inj : Function.Injective piv := fun j j' h =>
    Subtype.ext (by rw [← hpiv j, ← hpiv j', h])
  let P : Finset (Addr × Fin k) := univ.image piv
  have hPcard : #P = #(hitSlots pos T) := by
    rw [card_image_of_injective _ hpiv_inj, card_univ, Fintype.card_coe]
  -- a solution that vanishes off the pivots is zero
  have hzero : ∀ δ : Addr → Fin k → F, ∑ a ∈ T, γ a • coefRow pos δ a = 0 →
      (∀ a i, (a, i) ∉ P → δ a i = 0) → δ = 0 := by
    intro δ hδ hoff
    funext a i
    change δ a i = 0
    by_contra hne
    have hx : (a, i) ∈ P := by_contra fun hx => hne (hoff a i hx)
    obtain ⟨j, -, hj⟩ := mem_image.mp hx
    have haT : a ∈ T := by
      have := hpivT j
      rwa [hj] at this
    have hposj : pos a i = j := by
      have := hpiv j
      rwa [hj] at this
    -- every other entry pointing at slot `j` is not a pivot, so `δ` vanishes there
    have hvanish : ∀ a' i', pos a' i' = (j : Fin n) → (a', i') ≠ (a, i) → δ a' i' = 0 := by
      intro a' i' hpos hne'
      refine hoff a' i' fun hx' => hne' ?_
      obtain ⟨j', -, hj'⟩ := mem_image.mp hx'
      have h1 : pos a' i' = j' := by
        have := hpiv j'
        rwa [hj'] at this
      have hjj : j' = j := Subtype.ext (h1.symm.trans hpos)
      rw [← hj', hjj, hj]
    have hother : ∀ a' ∈ T, a' ≠ a →
        γ a' * ∑ i', (if pos a' i' = (j : Fin n) then δ a' i' else 0) = 0 := by
      intro a' _ ha'
      rw [sum_eq_zero, mul_zero]
      intro i' _
      split_ifs with h
      · exact hvanish a' i' h fun h' => ha' (Prod.ext_iff.mp h').1
      · rfl
    have hself : ∑ i', (if pos a i' = (j : Fin n) then δ a i' else 0) = δ a i := by
      rw [sum_eq_single_of_mem i (mem_univ i), ite_eq_left hposj]
      intro i' _ hi'
      split_ifs with h
      · exact hvanish a i' h fun h' => hi' (Prod.ext_iff.mp h').2
      · rfl
    -- the equation of slot `j` reads `γ a * δ a i = 0`
    have hj0 := congrFun hδ (j : Fin n)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, coefRow, Pi.zero_apply] at hj0
    rw [sum_eq_single_of_mem a haT hother, hself] at hj0
    exact hne ((mul_eq_zero.mp hj0).resolve_left (hγ a haT))
  -- so restricting to the non-pivot entries is injective on the solutions
  let res : (Addr → Fin k → F) → ({x : Addr × Fin k // x ∉ P} → F) := fun c x => c x.1.1 x.1.2
  have hinj : Set.InjOn res
      ↑(univ.filter fun coef : Addr → Fin k → F => ∑ a ∈ T, γ a • coefRow pos coef a = 0) := by
    intro c hc c' hc' hres
    rw [mem_coe, mem_filter] at hc hc'
    refine sub_eq_zero.mp (hzero (c - c') ?_ fun a i hx => ?_)
    · simp only [coefRow_sub, smul_sub, sum_sub_distrib, hc.2, hc'.2, sub_zero]
    · exact sub_eq_zero.mpr (congrFun hres ⟨(a, i), hx⟩)
  have hle : #(univ.filter fun coef : Addr → Fin k → F =>
      ∑ a ∈ T, γ a • coefRow pos coef a = 0) ≤
      Fintype.card F ^ (Fintype.card (Addr × Fin k) - #P) := by
    have h := card_le_card_of_injOn (t := univ) res (fun _ _ => mem_coe.mpr (mem_univ _)) hinj
    rwa [card_univ, Fintype.card_fun, Fintype.card_subtype_compl, Fintype.card_coe] at h
  calc _ ≤ Fintype.card F ^ (Fintype.card (Addr × Fin k) - #P) *
        Fintype.card F ^ #(hitSlots pos T) := Nat.mul_le_mul_right _ hle
    _ = Fintype.card F ^ Fintype.card (Addr × Fin k) := by
        rw [← hPcard, ← pow_add, Nat.sub_add_cancel (card_le_univ P)]
    _ = Fintype.card (Addr → Fin k → F) := by
        rw [← Fintype.card_fun]
        exact Fintype.card_congr (Equiv.curry _ _ _)

/-- For coefficients `γ` nonzero on `T`, the dependency `∑ a ∈ T, γ a • row a = 0` holds for at
most a `|F| ^ (-u)` fraction of the coefficient tables, where `u` is the number of slots hit by
`T`. -/
theorem card_filter_coef_dep_le (pos : Addr → Fin k → Fin n) (T : Finset Addr) (γ : Addr → F)
    (hγ : ∀ a ∈ T, γ a ≠ 0)
    [DecidablePred fun coef : Addr → Fin k → F => ∑ a ∈ T, γ a • coefRow pos coef a = 0] :
    (#(univ.filter fun coef : Addr → Fin k → F =>
        ∑ a ∈ T, γ a • coefRow pos coef a = 0) : ℝ) ≤
      Fintype.card (Addr → Fin k → F) / (Fintype.card F : ℝ) ^ #(hitSlots pos T) := by
  rw [le_div_iff₀ (pow_pos (by exact_mod_cast Fintype.card_pos) _)]
  exact_mod_cast card_filter_coef_dep_mul_le pos T γ hγ

end AuditPay
