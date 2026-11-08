/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.Defs
import AuditPay.Singularity.Algebraic
import AuditPay.Singularity.Hall
import AuditPay.Singularity.Restrict
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Basic.Real.Basic

/-!
# §7.4: the probability that the encoding matrix is singular

The paper (§7.4) estimates the probability that the `n × n` encoding matrix `M` of
Algorithm 3 is singular when each row comes from `k` uniformly random positions with uniformly
random coefficients, as `n·e^{-k}` (an all-zero column) plus `≈ 1/q`. This file proves a
rigorous version:

  `Pr[det M = 0] ≤ hallBound n k + n / |F|`

* `n / |F|` (the "algebraic" term) is Schwartz–Zippel: when the bipartite support graph of the
  positions has a perfect matching, `det M` is a nonzero polynomial of total degree `≤ n` in the
  coefficients.
* `hallBound n k` (the "structural" term) bounds the probability that the support graph has no
  perfect matching. By Hall's theorem some set `T` of `s` rows then has all its positions inside
  a set `U` of `s - 1` columns; a union bound over `(T, U)` gives
  `∑_{s=1}^{n} C(n,s) · C(n,s-1) · ((s-1)/n)^{k·s}`. The `s = n` term is
  `n·(1-1/n)^{kn} ≤ n·e^{-k}`, the paper's all-zero-column estimate.

Probabilities are stated by counting over the finite sample space of hash outputs.

The algebraic term is proved in `AuditPay.Singularity.Algebraic` (`card_coef_singular_le`), the
structural term in `AuditPay.Singularity.Hall` (`card_not_hasMatching_le`), and the reduction
from hash functions on `Addr` to rows indexed by `Fin n` uses `AuditPay.Singularity.Restrict`.
-/

open Matrix

namespace AuditPay

/-- The structural-singularity term: a union bound over Hall violators. -/
noncomputable def hallBound (n k : ℕ) : ℝ :=
  ∑ s ∈ Finset.Icc 1 n, (n.choose s : ℝ) * (n.choose (s - 1) : ℝ) * (((s : ℝ) - 1) / n) ^ (k * s)

/-- `hallBound` is a sum of nonnegative terms. -/
theorem hallBound_nonneg (n k : ℕ) : 0 ≤ hallBound n k := by
  refine Finset.sum_nonneg fun s hs => ?_
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast (Finset.mem_Icc.mp hs).1
  exact mul_nonneg (by positivity) (pow_nonneg (div_nonneg (by linarith) (by positivity)) _)

/-- Counting a subset of a product type fibrewise over the first factor. -/
theorem card_filter_prod_eq_sum {α β : Type*} [Fintype α] [Fintype β] (P : α × β → Prop)
    [DecidablePred P] :
    (Finset.univ.filter P).card = ∑ a, (Finset.univ.filter fun b => P (a, b)).card := by
  simp only [Finset.card_filter, Fintype.sum_prod_type]

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- §7.4, for `n` addresses whose `k` position hashes and `k` coefficient hashes are
independent and uniform (rows indexed by `Fin n`). -/
theorem card_singular_le (n k : ℕ) :
    ((Finset.univ.filter fun ω : (Fin n → Fin k → Fin n) × (Fin n → Fin k → F) =>
        (coefMatrix ω.1 ω.2 id).det = 0).card : ℝ) /
      Fintype.card ((Fin n → Fin k → Fin n) × (Fin n → Fin k → F)) ≤
    hallBound n k + n / Fintype.card F := by
  set cA := (Fintype.card (Fin n → Fin k → Fin n) : ℝ)
  set cB := (Fintype.card (Fin n → Fin k → F) : ℝ) with hcB
  have hterm : ∀ pos : Fin n → Fin k → Fin n,
      ((Finset.univ.filter fun coef : Fin n → Fin k → F =>
        (coefMatrix pos coef id).det = 0).card : ℝ) ≤
      n / Fintype.card F * cB + if HasMatching pos then 0 else cB := by
    intro pos
    split_ifs with h
    · obtain ⟨σ, hσ⟩ := h
      rw [add_zero]
      exact card_coef_singular_le (F := F) pos σ hσ
    · have h1 : ((Finset.univ.filter fun coef : Fin n → Fin k → F =>
          (coefMatrix pos coef id).det = 0).card : ℝ) ≤ cB := by
        rw [hcB]
        exact_mod_cast Finset.card_le_univ _
      have h2 : 0 ≤ n / Fintype.card F * cB := by positivity
      linarith
  rw [Fintype.card_prod, Nat.cast_mul]
  refine div_le_of_le_mul₀ (by positivity) (add_nonneg (hallBound_nonneg n k) (by positivity)) ?_
  calc _ = ∑ pos : Fin n → Fin k → Fin n, ((Finset.univ.filter fun coef : Fin n → Fin k → F =>
          (coefMatrix pos coef id).det = 0).card : ℝ) := by
        rw [card_filter_prod_eq_sum]
        push_cast
        rfl
    _ ≤ ∑ pos : Fin n → Fin k → Fin n,
          (n / Fintype.card F * cB + if HasMatching pos then 0 else cB) :=
        Finset.sum_le_sum fun pos _ => hterm pos
    _ = cA * (n / Fintype.card F * cB) +
          ((Finset.univ.filter fun pos : Fin n → Fin k → Fin n => ¬HasMatching pos).card : ℝ) *
            cB := by
        rw [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero, zero_add,
          Finset.sum_const, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul]
    _ ≤ cA * (n / Fintype.card F * cB) + hallBound n k * cA * cB := by
        gcongr
        exact card_not_hasMatching_le
    _ = (hallBound n k + n / Fintype.card F) * (cA * cB) := by ring

/-- §7.4 for hash functions on an arbitrary finite address space, evaluated at `n` distinct
addresses `rows`: the restriction of uniform hash functions to `rows` is uniform, so the bound
of `card_singular_le` applies. -/
theorem card_singular_rows_le {Addr : Type*} [Fintype Addr] [DecidableEq Addr]
    (n k : ℕ) (rows : Fin n ↪ Addr) :
    ((Finset.univ.filter fun ω : (Addr → Fin k → Fin n) × (Addr → Fin k → F) =>
        (coefMatrix ω.1 ω.2 rows).det = 0).card : ℝ) /
      Fintype.card ((Addr → Fin k → Fin n) × (Addr → Fin k → F)) ≤
    hallBound n k + n / Fintype.card F := by
  classical
  let e : (Addr → Fin k → Fin n) × (Addr → Fin k → F) ≃
      ((Fin n → Fin k → Fin n) × (Fin n → Fin k → F)) ×
        (({a // a ∉ Set.range rows} → Fin k → Fin n) × ({a // a ∉ Set.range rows} → Fin k → F)) :=
    (Equiv.prodCongr (restrictEquiv rows) (restrictEquiv rows)).trans
      (Equiv.prodProdProdComm _ _ _ _)
  have he : ∀ ω, (e ω).1 = (ω.1 ∘ rows, ω.2 ∘ rows) := fun ω => by
    simp [e, restrictEquiv_fst]
  have hfilter : (Finset.univ.filter fun ω : (Addr → Fin k → Fin n) × (Addr → Fin k → F) =>
        (coefMatrix ω.1 ω.2 rows).det = 0) =
      Finset.univ.filter fun ω => (coefMatrix (e ω).1.1 (e ω).1.2 id).det = 0 := by
    simp only [he]
    rfl
  rw [hfilter, card_filter_fst_equiv e (fun ω => (coefMatrix ω.1 ω.2 id).det = 0),
    Fintype.card_congr e, Fintype.card_prod _ (_ × _), Nat.cast_mul, Nat.cast_mul]
  rcases Nat.eq_zero_or_pos (Fintype.card (({a // a ∉ Set.range rows} → Fin k → Fin n) ×
      ({a // a ∉ Set.range rows} → Fin k → F))) with hc | hc
  · rw [hc, Nat.cast_zero, mul_zero, zero_div]
    exact add_nonneg (hallBound_nonneg n k) (by positivity)
  · rw [mul_div_mul_right _ _ (by positivity)]
    exact card_singular_le n k

end AuditPay
