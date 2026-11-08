/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.Singularity

/-!
# Linear dependence among the rows of a set of addresses

Definitions for the public-hash analysis of Algorithm 3: the rows of a set `T` of addresses
(`RowsIndep`), the bad event that some small set of addresses has linearly dependent rows
(`Dep`), and the reduction of that event to a linear dependency *with no zero coefficient* on a
nonempty set of at most `min s (n + 1)` addresses (`exists_isNZDep_of_dep`).
-/

open Finset

namespace AuditPay

variable {F : Type*} [Field F] {Addr : Type*} {k n : ℕ}

/-- The rows of the addresses in `T` are linearly independent over `F`. -/
def RowsIndep (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F) (T : Finset Addr) : Prop :=
  LinearIndependent F fun a : T => coefRow pos coef (a : Addr)

/-- `RowsIndep` in Mathlib's `LinearIndepOn` form. -/
theorem rowsIndep_iff_linearIndepOn {pos : Addr → Fin k → Fin n} {coef : Addr → Fin k → F}
    {T : Finset Addr} :
    RowsIndep pos coef T ↔ LinearIndepOn F (coefRow pos coef) (T : Set Addr) :=
  Iff.rfl

/-- The empty set of addresses has independent rows. -/
theorem rowsIndep_empty (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F) :
    RowsIndep pos coef ∅ :=
  linearIndependent_empty_type

/-- A subset of a set with independent rows has independent rows. -/
theorem RowsIndep.mono {pos : Addr → Fin k → Fin n} {coef : Addr → Fin k → F}
    {S T : Finset Addr} (hT : RowsIndep pos coef T) (hST : S ⊆ T) : RowsIndep pos coef S :=
  LinearIndepOn.mono hT (coe_subset.mpr hST)

/-- A set with independent rows has at most `n` addresses. -/
theorem RowsIndep.card_le {pos : Addr → Fin k → Fin n} {coef : Addr → Fin k → F}
    {T : Finset Addr} (hT : RowsIndep pos coef T) : #T ≤ n := by
  have h := LinearIndependent.fintype_card_le_finrank hT
  rwa [Fintype.card_coe, Module.finrank_fin_fun] at h

/-- The bad event `Dep s`: some set of at most `s` addresses has linearly dependent rows. -/
def Dep (s : ℕ) (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F) : Prop :=
  ∃ T : Finset Addr, #T ≤ s ∧ ¬RowsIndep pos coef T

/-- Outside `Dep s`, every set of at most `s` addresses has independent rows. -/
theorem rowsIndep_of_not_dep {s : ℕ} {pos : Addr → Fin k → Fin n} {coef : Addr → Fin k → F}
    (h : ¬Dep s pos coef) {T : Finset Addr} (hT : #T ≤ s) : RowsIndep pos coef T :=
  by_contra fun hT' => h ⟨T, hT, hT'⟩

/-- `Dep` is monotone in the size cap. -/
theorem Dep.mono {s s' : ℕ} {pos : Addr → Fin k → Fin n} {coef : Addr → Fin k → F}
    (h : Dep s pos coef) (hs : s ≤ s') : Dep s' pos coef := by
  obtain ⟨T, hT, hT'⟩ := h
  exact ⟨T, hT.trans hs, hT'⟩

/-- `γ` is a linear dependency among the rows of `T` with no zero coefficient on `T`. -/
def IsNZDep (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F) (T : Finset Addr)
    (γ : Addr → F) : Prop :=
  (∀ a ∈ T, γ a ≠ 0) ∧ ∑ a ∈ T, γ a • coefRow pos coef a = 0

/-- If some set of at most `s` addresses has dependent rows, then some nonempty set `T` of at
most `s` addresses, and at most `n + 1`, carries a dependency with no zero coefficient: take
the support of a dependency among (any `n + 1` of) the given rows. -/
theorem exists_isNZDep_of_dep {s : ℕ} {pos : Addr → Fin k → Fin n} {coef : Addr → Fin k → F}
    (h : Dep s pos coef) :
    ∃ T : Finset Addr, T.Nonempty ∧ #T ≤ s ∧ #T ≤ n + 1 ∧ ∃ γ, IsNZDep pos coef T γ := by
  classical
  obtain ⟨T, hTs, hT⟩ := h
  -- cut `T` down to at most `n + 1` addresses; it stays dependent
  obtain ⟨T₀, hT₀T, hT₀n, hT₀⟩ : ∃ T₀ ⊆ T, #T₀ ≤ n + 1 ∧ ¬RowsIndep pos coef T₀ := by
    rcases le_or_gt #T (n + 1) with hle | hgt
    · exact ⟨T, Subset.rfl, hle, hT⟩
    · obtain ⟨T₀, hT₀T, hT₀c⟩ := exists_subset_card_eq hgt.le
      refine ⟨T₀, hT₀T, hT₀c.le, fun hind => ?_⟩
      have := hind.card_le
      omega
  -- a dependency among the rows of `T₀`, restricted to its support
  have hT₀' : ¬LinearIndepOn F (coefRow pos coef) (T₀ : Set Addr) := hT₀
  obtain ⟨f, hf, a, ha, hfa⟩ := not_linearIndepOn_finset_iff.mp hT₀'
  refine ⟨T₀.filter fun a => f a ≠ 0, ⟨a, mem_filter.mpr ⟨ha, hfa⟩⟩,
    (card_le_card (filter_subset _ _)).trans ((card_le_card hT₀T).trans hTs),
    (card_le_card (filter_subset _ _)).trans hT₀n, f, fun a ha => (mem_filter.mp ha).2, ?_⟩
  refine Eq.trans (sum_filter_of_ne fun a _ ha => ?_) hf
  intro hfa
  exact ha (by rw [hfa, zero_smul])

end AuditPay
