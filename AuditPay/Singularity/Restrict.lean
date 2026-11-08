/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Embedding.Basic

/-!
# Restricting uniform functions to finitely many points

A function on `Addr` splits into its restriction to `n` distinct addresses `rows` and its values
on the remaining addresses. Hence the restriction of a uniformly random function is uniform,
which reduces §7.4 for hash functions on `Addr` to the case of rows indexed by `Fin n`.
-/

open Finset

namespace AuditPay

/-- Splitting a function on `Addr` into its restriction to the addresses `rows` and its values
on the other addresses. -/
noncomputable def restrictEquiv {Addr X : Type*} {n : ℕ} (rows : Fin n ↪ Addr) :
    (Addr → X) ≃ (Fin n → X) × ({a // a ∉ Set.range rows} → X) := by
  classical
  exact (Equiv.piEquivPiSubtypeProd (· ∈ Set.range rows) fun _ => X).trans
    (Equiv.prodCongr (Equiv.arrowCongr (Equiv.ofInjective rows rows.injective).symm
      (Equiv.refl X)) (Equiv.refl _))

/-- The first component of `restrictEquiv` is the restriction to `rows`. -/
theorem restrictEquiv_fst {Addr X : Type*} {n : ℕ} (rows : Fin n ↪ Addr) (h : Addr → X) :
    (restrictEquiv rows h).1 = h ∘ rows := by
  ext r
  simp [restrictEquiv]

/-- If `e : α ≃ β × γ`, the number of `a` whose first component satisfies `P` is
`#{b | P b} · |γ|`. -/
theorem card_filter_fst_equiv {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (e : α ≃ β × γ) (P : β → Prop) [DecidablePred P] :
    #(univ.filter fun a => P (e a).1) = #(univ.filter P) * Fintype.card γ := by
  rw [← card_univ (α := γ), ← card_product]
  exact card_equiv e fun a => by simp

end AuditPay
