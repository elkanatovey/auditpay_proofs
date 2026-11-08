/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# AuditPay: algebraic definitions

Deterministic cores of the paper's Algorithm 2 (selective encryption) and Algorithm 3
(audit-key vector encoding and retrieval), with their correctness lemmas.

## Group model

`F` is the scalar field (`ℤ_q`), `G` the group written additively (`Module F G`), and `g : G`
a generator. Hash-to-curve is a function `H : Addr → G`. The `k` position hashes and `k`
coefficient hashes of Algorithm 3 are packaged as `pos : Addr → Fin k → Fin n` and
`coef : Addr → Fin k → F`, where `n = |V|`. The paper computes positions as `h_i(a) mod |V|`;
here the reduction modulo `|V|` is folded into `pos`.

## Linear algebra over `G`

Audit keys live in `G`, while the encoding matrix has entries in `F`. `matVecG M v` is the
action of an `F`-matrix on a vector of group elements, `(M ⋆ v) i = ∑ j, M i j • v j`.
-/

open Matrix

namespace AuditPay

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-! ## Algorithm 2: selective encryption -/

section SelectiveEncryption

/-- `AuditKey` (Algorithm 2, line 9): `AK_a = sk • g + H(a)`. -/
def auditKey (g : G) (sk : F) (Ha : G) : G := sk • g + Ha

/-- The encryptor's shared point (Algorithm 2, line 16): `K = r • (AK - H(a'))`. -/
def encPoint (r : F) (ak Ha' : G) : G := r • (ak - Ha')

/-- The decryptor's shared point (Algorithm 2, line 23): `K' = sk • R`. -/
def decPoint (sk : F) (R : G) : G := sk • R

/-- §5.1 correctness: if the encryptor's address is the audit key's address, the encryptor's
shared point equals the decryptor's, for the ephemeral key `R = r • g`. -/
theorem encPoint_auditKey (g Ha : G) (sk r : F) :
    encPoint r (auditKey g sk Ha) Ha = decPoint sk (r • g) := by
  simp [encPoint, decPoint, auditKey, smul_smul, mul_comm]

/-- Full Algorithm 2 encryption, given a key-derivation function and a deterministic
symmetric cipher. Returns `(SymEnc_{KDF(K)}(m), R)`. -/
def encrypt {K M C : Type*} (kdf : G → K) (senc : K → M → C)
    (g : G) (ak Ha' : G) (r : F) (m : M) : C × G :=
  (senc (kdf (encPoint r ak Ha')) m, r • g)

/-- Full Algorithm 2 decryption. -/
def decrypt {K M C : Type*} (kdf : G → K) (sdec : K → C → Option M)
    (sk : F) (ct : C × G) : Option M :=
  sdec (kdf (decPoint sk ct.2)) ct.1

/-- §5.1 correctness of the full scheme: decryption with `sk` recovers `m` from an encryption
under `AuditKey(a)` made by the owner of `a`. -/
theorem decrypt_encrypt {K M C : Type*} (kdf : G → K) (senc : K → M → C)
    (sdec : K → C → Option M) (hsym : ∀ k m, sdec k (senc k m) = some m)
    (g Ha : G) (sk r : F) (m : M) :
    decrypt kdf sdec sk (encrypt kdf senc g (auditKey g sk Ha) Ha r m) = some m := by
  simp [decrypt, encrypt, encPoint_auditKey, hsym]

end SelectiveEncryption

/-! ## Matrices acting on vectors of group elements -/

section MatVecG

variable {ι κ μ : Type*} [Fintype κ] [Fintype μ]

/-- An `F`-matrix acting on a vector of group elements. -/
def matVecG (M : Matrix ι κ F) (v : κ → G) : ι → G := fun i => ∑ j, M i j • v j

theorem matVecG_apply (M : Matrix ι κ F) (v : κ → G) (i : ι) :
    matVecG M v i = ∑ j, M i j • v j := rfl

theorem matVecG_mul (M : Matrix ι μ F) (N : Matrix μ κ F) (v : κ → G) :
    matVecG (M * N) v = matVecG M (matVecG N v) := by
  ext i
  simp only [matVecG, mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

theorem matVecG_one [DecidableEq κ] (v : κ → G) : matVecG (1 : Matrix κ κ F) v = v := by
  ext i
  simp [matVecG, one_apply, ite_smul]

theorem matVecG_add (M : Matrix ι κ F) (v w : κ → G) :
    matVecG M (v + w) = matVecG M v + matVecG M w := by
  ext i
  simp [matVecG, smul_add, Finset.sum_add_distrib]

/-- Solving `M ⋆ V = b` for square `M` (the `Solve` step of Algorithm 3). Returns `none`
when `M` is singular. -/
noncomputable def solve [DecidableEq F] {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n F) (b : n → G) : Option (n → G) :=
  if M.det ≠ 0 then some (matVecG M⁻¹ b) else none

theorem matVecG_of_solve_eq_some [DecidableEq F] {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n F} {b v : n → G} (h : solve M b = some v) : matVecG M v = b := by
  unfold solve at h
  split_ifs at h with hM
  cases h
  rw [← matVecG_mul, mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hM), matVecG_one]

theorem solve_isSome_iff [DecidableEq F] {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n F) (b : n → G) : (solve M b).isSome ↔ M.det ≠ 0 := by
  unfold solve
  split_ifs with hM <;> simp [hM]

end MatVecG

/-! ## Algorithm 3: audit-key vector encoding and retrieval -/

section AuditKeyVector

variable {Addr : Type*} {k n : ℕ}

/-- The row of the encoding matrix induced by address `a`: entry `j` is the sum of the
coefficients `c_i(a)` over the hash functions with `h_i(a) = j`. -/
def coefRow (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F) (a : Addr) : Fin n → F :=
  fun j => ∑ i, if pos a i = j then coef a i else 0

/-- `RetrieveKey` (Algorithm 3, lines 19–26): `∑ᵢ cᵢ(a) • V[hᵢ(a)]`. -/
def retrieveKey (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F) (V : Fin n → G)
    (a : Addr) : G :=
  ∑ i, coef a i • V (pos a i)

theorem retrieveKey_eq_sum_coefRow (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F)
    (V : Fin n → G) (a : Addr) :
    retrieveKey pos coef V a = ∑ j, coefRow pos coef a j • V j := by
  simp only [retrieveKey, coefRow, Finset.sum_smul, ite_smul, zero_smul]
  rw [Finset.sum_comm]
  simp

/-- The encoding matrix of Algorithm 3 for the addresses `rows`. -/
def coefMatrix {ι : Type*} (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F)
    (rows : ι → Addr) : Matrix ι (Fin n) F :=
  Matrix.of fun r => coefRow pos coef (rows r)

theorem retrieveKey_eq_matVecG {ι : Type*} (pos : Addr → Fin k → Fin n)
    (coef : Addr → Fin k → F) (rows : ι → Addr) (V : Fin n → G) (r : ι) :
    retrieveKey pos coef V (rows r) = matVecG (coefMatrix pos coef rows) V r := by
  simp [retrieveKey_eq_sum_coefRow, matVecG, coefMatrix]

/-- `AuditKeyVecGen` (Algorithm 3, lines 1–17) for the (already padded) monitored addresses
`rows`, with audit secret keys `sk`: solve `M ⋆ V = (AK_{rows r})_r`. -/
noncomputable def auditKeyVecGen [DecidableEq F] (g : G) (H : Addr → G) (pos : Addr → Fin k → Fin n)
    (coef : Addr → Fin k → F) (rows : Fin n → Addr) (sk : Fin n → F) : Option (Fin n → G) :=
  solve (coefMatrix pos coef rows) fun r => auditKey g (sk r) (H (rows r))

/-- Correctness of Algorithm 3: a successfully generated vector returns, for every monitored
address, exactly its audit key. -/
theorem retrieveKey_of_auditKeyVecGen [DecidableEq F] {g : G} {H : Addr → G}
    {pos : Addr → Fin k → Fin n} {coef : Addr → Fin k → F} {rows : Fin n → Addr}
    {sk : Fin n → F} {V : Fin n → G}
    (h : auditKeyVecGen g H pos coef rows sk = some V) (r : Fin n) :
    retrieveKey pos coef V (rows r) = auditKey g (sk r) (H (rows r)) := by
  rw [retrieveKey_eq_matVecG, matVecG_of_solve_eq_some h]

/-- End-to-end auditing correctness (§6.3): a selective encryption by a monitored address,
under the key retrieved from a successfully generated vector, decrypts under that address's
audit secret key. -/
theorem decrypt_encrypt_retrieveKey [DecidableEq F] {K M C : Type*} (kdf : G → K) (senc : K → M → C)
    (sdec : K → C → Option M) (hsym : ∀ k m, sdec k (senc k m) = some m)
    {g : G} {H : Addr → G} {pos : Addr → Fin k → Fin n} {coef : Addr → Fin k → F}
    {rows : Fin n → Addr} {sk : Fin n → F} {V : Fin n → G}
    (hV : auditKeyVecGen g H pos coef rows sk = some V) (r : Fin n) (ρ : F) (m : M) :
    decrypt kdf sdec (sk r)
      (encrypt kdf senc g (retrieveKey pos coef V (rows r)) (H (rows r)) ρ m) = some m := by
  rw [retrieveKey_of_auditKeyVecGen hV]
  exact decrypt_encrypt kdf senc sdec hsym g _ _ _ m

end AuditKeyVector

end AuditPay
