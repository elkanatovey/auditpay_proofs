/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.Dependence.Basic

/-!
# Algorithm 3 without padding: a uniformly random solution of a rectangular system

`AuditKeyVecGen` in the paper pads the monitored set with random addresses to `n = |V|`
addresses and solves a square system (`AuditPay.auditKeyVecGen`). Here the set `T` is *not*
padded. Its encoding matrix `M` has one row per address of `T` and `n` columns, and the
procedure outputs a uniformly random solution `V` of `M ⋆ V = AK`, where `AK` holds the audit
keys of `T`. Equivalently: the slots not determined by the equations get uniformly random group
elements.

## The form used

For a right inverse `R` of `M` (`M * R = 1`; one exists exactly when the rows of `M` are
linearly independent) and a uniformly random `ρ : Fin n → G`, the output is

  `rectSolve M R AK ρ = ρ + R ⋆ (AK - M ⋆ ρ)`.

This is the uniform distribution on the solution set `{V | M ⋆ V = AK}`, for any choice of `R`:

* every output is a solution (`matVecG_rectSolve`);
* every solution is an output, namely of itself (`rectSolve_eq_self`);
* `ρ ↦ rectSolve M R AK ρ` commutes with translations by the kernel of `M`
  (`rectSolve_add`), and any two solutions differ by an element of the kernel. So translating
  `ρ` by `V' - V` maps the `ρ` with output `V` bijectively onto the `ρ` with output `V'`: all
  solutions are equally likely. The probability statement is
  `AuditPay.MembershipHidingPublic.prob_rectSolve_eq`.

The right inverse is picked by `Classical.choose` (`rightInv`). The distribution of the output
does not depend on which right inverse is used; a real implementation would run Gaussian
elimination and fill the free slots at random.
-/

open Matrix

namespace AuditPay

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-! ## More on matrices acting on vectors of group elements -/

section MatVecG

variable {ι κ : Type*} [Fintype κ]

theorem matVecG_zero (M : Matrix ι κ F) : matVecG M (0 : κ → G) = 0 := by
  ext i
  simp [matVecG]

theorem matVecG_sub (M : Matrix ι κ F) (v w : κ → G) :
    matVecG M (v - w) = matVecG M v - matVecG M w := by
  ext i
  simp [matVecG, smul_sub, Finset.sum_sub_distrib]

end MatVecG

/-! ## Solving a rectangular system with a right inverse -/

section RectSolve

variable {ι : Type*} [DecidableEq ι] {n : ℕ}

/-- A right inverse of `M`, if there is one (and `0` otherwise). -/
noncomputable def rightInv (M : Matrix ι (Fin n) F) : Matrix (Fin n) ι F :=
  open Classical in if h : ∃ R : Matrix (Fin n) ι F, M * R = 1 then h.choose else 0

/-- A matrix with linearly independent rows has a right inverse. -/
theorem exists_right_inverse_of_linearIndependent_row [Finite ι] {M : Matrix ι (Fin n) F}
    (h : LinearIndependent F M.row) : ∃ R : Matrix (Fin n) ι F, M * R = 1 := by
  cases nonempty_fintype ι
  have ⟨f, hf⟩ := IsSemisimpleModule.extension_property M.toLinearMapRight'
    (vecMul_injective_iff.mpr h) .id
  exact ⟨f.toMatrixRight', toLinearMapRight'.injective <| by simpa using hf⟩

/-- `rightInv M` is a right inverse of `M` when the rows of `M` are linearly independent. -/
theorem mul_rightInv [Finite ι] {M : Matrix ι (Fin n) F} (h : LinearIndependent F M.row) :
    M * rightInv M = 1 := by
  have hex := exists_right_inverse_of_linearIndependent_row h
  rw [rightInv, dite_eq_left hex]
  exact hex.choose_spec

/-- Conversely, a matrix with a right inverse has linearly independent rows. -/
theorem linearIndependent_row_of_mul_eq_one [Finite ι] {M : Matrix ι (Fin n) F}
    {R : Matrix (Fin n) ι F} (h : M * R = 1) : LinearIndependent F M.row := by
  cases nonempty_fintype ι
  refine vecMul_injective_iff.mp fun x y hxy => ?_
  have h' := congrArg (fun v => v ᵥ* R) hxy
  simpa only [vecMul_vecMul, h, vecMul_one] using h'

variable [Fintype ι]

/-- The solution of `M ⋆ V = b` determined by the right inverse `R` of `M` and the vector `ρ`:
`ρ + R ⋆ (b - M ⋆ ρ)`. With `ρ` uniformly random this is a uniformly random solution (see the
module docstring). -/
def rectSolve (M : Matrix ι (Fin n) F) (R : Matrix (Fin n) ι F) (b : ι → G) (ρ : Fin n → G) :
    Fin n → G :=
  ρ + matVecG R (b - matVecG M ρ)

/-- `rectSolve` outputs a solution. -/
theorem matVecG_rectSolve {M : Matrix ι (Fin n) F} {R : Matrix (Fin n) ι F} (h : M * R = 1)
    (b : ι → G) (ρ : Fin n → G) : matVecG M (rectSolve M R b ρ) = b := by
  rw [rectSolve, matVecG_add, ← matVecG_mul, h, matVecG_one, add_sub_cancel]

omit [DecidableEq ι] in
/-- Every solution is an output of `rectSolve`: it is the output on itself. -/
theorem rectSolve_eq_self {M : Matrix ι (Fin n) F} (R : Matrix (Fin n) ι F) {b : ι → G}
    {V : Fin n → G} (h : matVecG M V = b) : rectSolve M R b V = V := by
  rw [rectSolve, h, sub_self, matVecG_zero, add_zero]

omit [DecidableEq ι] in
/-- `rectSolve` commutes with translations by the kernel of `M`. -/
theorem rectSolve_add {M : Matrix ι (Fin n) F} (R : Matrix (Fin n) ι F) (b : ι → G)
    (ρ : Fin n → G) {δ : Fin n → G} (hδ : matVecG M δ = 0) :
    rectSolve M R b (ρ + δ) = rectSolve M R b ρ + δ := by
  rw [rectSolve, rectSolve, matVecG_add, hδ, add_zero, add_right_comm]

end RectSolve

/-! ## Encoding a set of addresses -/

section SetEncoding

variable {Addr : Type*} [DecidableEq Addr] {k n : ℕ}

/-- The encoding matrix of the set `T`: one row per address of `T`, no padding. -/
abbrev setMatrix (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F) (T : Finset Addr) :
    Matrix T (Fin n) F :=
  coefMatrix pos coef fun a : T => (a : Addr)

/-- The audit keys of the addresses in `T`: `AK_a = sk_a • g + H(a)`. -/
def setAuditKeys (g : G) (H : Addr → G) (T : Finset Addr) (sk : T → F) : T → G :=
  fun a => auditKey g (sk a) (H a)

/-- The vector encoding the set `T` with audit secret keys `sk`, determined by `ρ`: the
solution `rectSolve M (rightInv M) AK ρ` of `M ⋆ V = AK`. It is a solution when the rows of `T`
are linearly independent. -/
noncomputable def encodeSet (g : G) (H : Addr → G) (pos : Addr → Fin k → Fin n)
    (coef : Addr → Fin k → F) (T : Finset Addr) (sk : T → F) (ρ : Fin n → G) : Fin n → G :=
  rectSolve (setMatrix pos coef T) (rightInv (setMatrix pos coef T)) (setAuditKeys g H T sk) ρ

/-- `AuditKeyVecGen` for a set `T` without padding: `none` when the rows of `T` are linearly
dependent, and otherwise the solution of `M ⋆ V = AK` determined by `ρ`. With `ρ` uniformly
random this is a uniformly random solution. -/
noncomputable def auditKeyVecGenSet (g : G) (H : Addr → G) (pos : Addr → Fin k → Fin n)
    (coef : Addr → Fin k → F) (T : Finset Addr) (sk : T → F) (ρ : Fin n → G) :
    Option (Fin n → G) :=
  open Classical in if RowsIndep pos coef T then some (encodeSet g H pos coef T sk ρ) else none

theorem auditKeyVecGenSet_of_rowsIndep {g : G} {H : Addr → G} {pos : Addr → Fin k → Fin n}
    {coef : Addr → Fin k → F} {T : Finset Addr} (hT : RowsIndep pos coef T) (sk : T → F)
    (ρ : Fin n → G) :
    auditKeyVecGenSet g H pos coef T sk ρ = some (encodeSet g H pos coef T sk ρ) := by
  rw [auditKeyVecGenSet, ite_eq_left hT]

theorem auditKeyVecGenSet_isSome_iff {g : G} {H : Addr → G} {pos : Addr → Fin k → Fin n}
    {coef : Addr → Fin k → F} {T : Finset Addr} (sk : T → F) (ρ : Fin n → G) :
    (auditKeyVecGenSet g H pos coef T sk ρ).isSome ↔ RowsIndep pos coef T := by
  unfold auditKeyVecGenSet
  split_ifs with hT <;> simp [hT]

/-- Correctness of the encoding: if the rows of `T` are linearly independent, every address of
`T` retrieves exactly its audit key. -/
theorem retrieveKey_encodeSet {g : G} {H : Addr → G} {pos : Addr → Fin k → Fin n}
    {coef : Addr → Fin k → F} {T : Finset Addr} (hT : RowsIndep pos coef T) (sk : T → F)
    (ρ : Fin n → G) (a : T) :
    retrieveKey pos coef (encodeSet g H pos coef T sk ρ) a = auditKey g (sk a) (H a) :=
  (retrieveKey_eq_matVecG pos coef (fun a : T => (a : Addr)) _ a).trans
    (congrFun (matVecG_rectSolve (mul_rightInv hT) _ _) a)

/-- Correctness of `AuditKeyVecGen` without padding: a successfully generated vector returns,
for every monitored address, exactly its audit key. -/
theorem retrieveKey_of_auditKeyVecGenSet {g : G} {H : Addr → G} {pos : Addr → Fin k → Fin n}
    {coef : Addr → Fin k → F} {T : Finset Addr} {sk : T → F} {ρ V : Fin n → G}
    (h : auditKeyVecGenSet g H pos coef T sk ρ = some V) (a : T) :
    retrieveKey pos coef V a = auditKey g (sk a) (H a) := by
  unfold auditKeyVecGenSet at h
  split_ifs at h with hT
  cases h
  exact retrieveKey_encodeSet hT sk ρ a

/-- End-to-end auditing correctness (§6.3) without padding: a selective encryption by a
monitored address, under the key retrieved from a successfully generated vector, decrypts under
that address's audit secret key. -/
theorem decrypt_encrypt_retrieveKey_set {K M C : Type*} (kdf : G → K) (senc : K → M → C)
    (sdec : K → C → Option M) (hsym : ∀ k m, sdec k (senc k m) = some m)
    {g : G} {H : Addr → G} {pos : Addr → Fin k → Fin n} {coef : Addr → Fin k → F}
    {T : Finset Addr} {sk : T → F} {ρ V : Fin n → G}
    (hV : auditKeyVecGenSet g H pos coef T sk ρ = some V) (a : T) (r : F) (m : M) :
    decrypt kdf sdec (sk a)
      (encrypt kdf senc g (retrieveKey pos coef V a) (H a) r m) = some m := by
  rw [retrieveKey_of_auditKeyVecGenSet hV]
  exact decrypt_encrypt kdf senc sdec hsym g _ _ _ m

end SetEncoding

end AuditPay
