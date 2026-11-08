/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.Defs
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Basic.Real.Basic

/-!
# §7.4, algebraic part: Schwartz–Zippel for the encoding matrix

When the positions `pos` admit a perfect matching of rows to columns, the determinant of the
encoding matrix is a nonzero polynomial of total degree `≤ n` in the coefficients, so it
vanishes for at most an `n / |F|` fraction of coefficient choices.
-/

open Matrix MvPolynomial

namespace AuditPay

variable {F : Type*} [Field F] {n k : ℕ}

/-- The encoding matrix with each coefficient `coef r i` replaced by the variable `X (r, i)`. -/
noncomputable def polyCoefMatrix (pos : Fin n → Fin k → Fin n) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin k) F) :=
  Matrix.of fun r j => ∑ i, if pos r i = j then X (r, i) else 0

/-- Evaluating the formal determinant at the coefficients gives the actual determinant. -/
theorem eval_det_polyCoefMatrix (pos : Fin n → Fin k → Fin n) (coef : Fin n → Fin k → F) :
    eval (fun x => coef x.1 x.2) (polyCoefMatrix pos).det = (coefMatrix pos coef id).det := by
  rw [RingHom.map_det]
  congr 1
  ext r j
  simp [polyCoefMatrix, coefMatrix, coefRow, apply_ite]

/-- The formal determinant is homogeneous of degree `n`. -/
theorem isHomogeneous_det_polyCoefMatrix (pos : Fin n → Fin k → Fin n) :
    (polyCoefMatrix (F := F) pos).det.IsHomogeneous n := by
  rw [det_apply']
  apply IsHomogeneous.sum
  intro σ _
  have hprod := IsHomogeneous.prod Finset.univ (fun r => polyCoefMatrix (F := F) pos (σ r) r)
    (fun _ => 1) fun r _ => by
      simp only [polyCoefMatrix, of_apply]
      apply IsHomogeneous.sum
      intro i _
      split_ifs
      · exact isHomogeneous_X _ _
      · exact isHomogeneous_zero _ _ _
  have hc := isHomogeneous_C (Fin n × Fin k) ((Equiv.Perm.sign σ : ℤ) : F)
  simpa using hc.mul hprod

/-- The formal determinant is nonzero as soon as some permutation `σ` of the columns is
realised by the positions, i.e. `σ r` is one of the positions of row `r`. -/
theorem det_polyCoefMatrix_ne_zero (pos : Fin n → Fin k → Fin n) (σ : Equiv.Perm (Fin n))
    (h : ∀ r, ∃ i, pos r i = σ r) : (polyCoefMatrix (F := F) pos).det ≠ 0 := by
  choose c hc using h
  intro h0
  have h1 := congrArg (eval fun x : Fin n × Fin k => if x.2 = c x.1 then (1 : F) else 0) h0
  have hM : (eval fun x : Fin n × Fin k => if x.2 = c x.1 then (1 : F) else 0).mapMatrix
      (polyCoefMatrix pos) = σ.permMatrix F := by
    ext r j
    simp only [RingHom.mapMatrix_apply, map_apply, polyCoefMatrix, of_apply, map_sum,
      apply_ite (eval _), eval_X, map_zero]
    rw [Finset.sum_eq_single (c r) (fun i _ hi => by simp [hi]) (by simp)]
    simp [hc, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  rw [map_zero, RingHom.map_det, hM, det_permutation] at h1
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h] at h1

/-- Schwartz–Zippel over an arbitrary finite type of variables, with the point drawn uniformly
from `σ → F`, stated multiplicatively over `ℝ`. -/
theorem card_eval_eq_zero_le [Fintype F] [DecidableEq F] {σ : Type*} [Fintype σ] [DecidableEq σ]
    {p : MvPolynomial σ F} (hp : p ≠ 0) :
    ((Finset.univ.filter fun x : σ → F => eval x p = 0).card : ℝ) ≤
      p.totalDegree / Fintype.card F * Fintype.card (σ → F) := by
  set e := Fintype.equivFin σ
  have hp' : rename e p ≠ 0 := fun h =>
    hp (rename_injective _ e.injective (h.trans (map_zero _).symm))
  have h := schwartz_zippel_totalDegree hp' Finset.univ
  rw [Fintype.piFinset_univ, Finset.card_univ] at h
  have hcard : (Finset.univ.filter fun f : Fin (Fintype.card σ) → F => eval f (rename e p) = 0).card
      = (Finset.univ.filter fun x : σ → F => eval x p = 0).card :=
    Finset.card_equiv (e.symm.arrowCongr (Equiv.refl F)) fun f => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, eval_rename]
      rfl
  rw [hcard] at h
  have h' := (NNRat.cast_le (K := ℝ)).mpr h
  push_cast at h'
  have hF : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ (by positivity)] at h'
  calc _ ≤ _ := h'
    _ ≤ _ := by
      rw [Fintype.card_fun]
      push_cast
      gcongr
      exact_mod_cast totalDegree_rename_le _ _

/-- For positions realising a permutation `σ` of the columns, at most an `n / |F|` fraction of
the coefficient choices make the encoding matrix singular. -/
theorem card_coef_singular_le [Fintype F] [DecidableEq F] (pos : Fin n → Fin k → Fin n)
    (σ : Equiv.Perm (Fin n)) (h : ∀ r, ∃ i, pos r i = σ r) :
    ((Finset.univ.filter fun coef : Fin n → Fin k → F =>
        (coefMatrix pos coef id).det = 0).card : ℝ) ≤
      n / Fintype.card F * Fintype.card (Fin n → Fin k → F) := by
  have h1 := card_eval_eq_zero_le (det_polyCoefMatrix_ne_zero (F := F) pos σ h)
  have hcard : (Finset.univ.filter fun coef : Fin n → Fin k → F =>
        (coefMatrix pos coef id).det = 0).card =
      (Finset.univ.filter fun x : Fin n × Fin k → F =>
        eval x (polyCoefMatrix pos).det = 0).card :=
    Finset.card_equiv (Equiv.curry _ _ _).symm fun coef => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, ← eval_det_polyCoefMatrix]
      rfl
  rw [hcard, Fintype.card_congr (Equiv.curry (Fin n) (Fin k) F).symm]
  refine h1.trans ?_
  gcongr
  exact_mod_cast (isHomogeneous_det_polyCoefMatrix pos).totalDegree_le

end AuditPay
