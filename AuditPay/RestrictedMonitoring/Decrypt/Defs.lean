/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.RestrictedMonitoring
import AuditPay.SLIND.Defs

/-!
# Theorem 3 (Restricted Monitoring), the paper's decryption game: definitions

## The game (Definition 3 of the paper, for algebraic adversaries)

Setup: the challenger samples the KDF key `hk` and the hash-to-curve oracle `H` and gives both to
the adversary. Commitment: the adversary outputs a vector `V` of size `n` and `n + 1` distinct
addresses `aᵢ`. Challenge: for each `i` the challenger samples a uniform message `mᵢ` and a
uniform ephemeral scalar `rᵢ`, and gives the adversary the selective encryption (Algorithm 2) of
`mᵢ` by address `aᵢ` under the audit key `RetrieveKey(V, aᵢ)`:
`(SymEnc_{KDF(hk, Kᵢ)}(mᵢ), rᵢ • g)` with `Kᵢ = rᵢ • (RetrieveKey(V, aᵢ) - H(aᵢ))`.
Response: the adversary outputs guesses `m'ᵢ`. It wins if *all* `n + 1` guesses are correct.

## Modelling choices

* **Algebraic adversary.** The adversary does not output the group elements `V_j` themselves but a
  *representation* of each over the group elements it has been given, `g` and `H(z)` for every
  address `z`: coefficients `c_j : F` and `d_j : Addr → F`, and the game sets
  `V_j := c_j • g + ∑_z d_j(z) • H(z)`. This is the standard way to formalise the algebraic group
  model (Fuchsbauer–Kiltz–Loss): an algebraic adversary must accompany every group element it
  outputs with such a representation. The adversary outputs no other group elements.
* **Messages** are independent and uniform over a finite message type `Msg`; the bound contains
  the guessing term `1/|Msg|`.
* **KDF and cipher** are those of the SL-IND development: a keyed KDF with public key `hk` under
  entropy smoothing, and a deterministic cipher that is one-time secure under a uniform key
  (`SLIND.otExperiment`).
* `H` is a uniformly random function handed over as a value; the position and coefficient hashes
  are arbitrary fixed functions.

## The proof idea

Write `Pᵢ = RetrieveKey(V, aᵢ) - H(aᵢ) = αᵢ • g + ∑_z βᵢ(z) • H(z)`, where `βᵢ` (`Commit.hCoeff`)
is computed from the adversary's representation. Because the `(n + 1) × n` encoding matrix has a
nonzero left-kernel vector, some `βᵢ` is a nonzero function: the *target* index `i*`
(`Commit.target`). This step is pure linear algebra. With `H(z) = u_z • g + t_z • Y` programmed,
`P_{i*} = α' • g + β' • Y` with `β' = ∑_z β_{i*}(z) t_z ≠ 0` except with probability `1/|F|`,
and a DDH challenge `(X, Y, Z)` is embedded in ciphertext `i*` alone: `R_{i*} = X`,
`K_{i*} = α' • X + β' • Z`. All other ciphertexts are computed honestly. Then entropy smoothing
makes the symmetric key of ciphertext `i*` uniform, one-time security replaces its plaintext by
a fixed dummy, and the adversary's guess for `m_{i*}` is independent of it.

The hybrids sample the target's message `μ` and ephemeral scalar `ρ` separately from the vectors
`m`, `r` (whose target coordinates are then unused); `AuditPay.RestrictedMonitoring.Decrypt`'s
`experiment_eqd` shows that this does not change the game.
-/

open OracleComp DiffieHellman ENNReal

namespace AuditPay.RestrictedMonitoring.Decrypt

open SLIND (Mode OTAdversary)

/-- Public parameters of selective encryption with an audit-key vector. -/
structure Params (F G Addr HK Key Msg C : Type) (k n : ℕ) where
  /-- The generator. -/
  g : G
  /-- Position hashes. -/
  pos : Addr → Fin k → Fin n
  /-- Coefficient hashes. -/
  coef : Addr → Fin k → F
  /-- The key-derivation function, keyed by a public key. -/
  kdf : HK → G → Key
  /-- The symmetric cipher. -/
  senc : Key → Msg → C
  /-- A fixed message used as the dummy plaintext in the hybrids. -/
  dummy : Msg

/-- The first-phase output of an algebraic adversary: a representation of the vector `V` over
`g` and the hash values, `n + 1` distinct addresses, and a state for the second phase. -/
structure Commit (F Addr σ : Type) (n : ℕ) where
  /-- The coefficient of `g` in `V_j`. -/
  cV : Fin n → F
  /-- The coefficient of `H(z)` in `V_j`. -/
  dV : Fin n → Addr → F
  /-- The `n + 1` distinct target addresses. -/
  addrs : Fin (n + 1) ↪ Addr
  /-- The adversary's state. -/
  state : σ

/-- An algebraic adversary against the decryption game. -/
structure Adversary (F G Addr HK Msg C σ : Type) (n : ℕ) where
  /-- Given `hk` and `H`, output a representation of `V`, `n + 1` distinct addresses, and a
  state. -/
  commit : HK → (Addr → G) → ProbComp (Commit F Addr σ n)
  /-- Given the state and the `n + 1` ciphertexts, guess the plaintexts. -/
  respond : σ → (Fin (n + 1) → C × G) → ProbComp (Fin (n + 1) → Msg)

variable {F G Addr HK Key Msg C σ : Type} {k n : ℕ}
  [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G]
  [Fintype Addr] [DecidableEq Addr] [SampleableType HK] [SampleableType Key]
  [DecidableEq Msg] [SampleableType Msg]

/-- The vector an algebraic commitment represents: `V_j = c_j • g + ∑_z d_j(z) • H(z)`. -/
def Commit.vec (c : Commit F Addr σ n) (g : G) (H : Addr → G) : Fin n → G :=
  fun j => c.cV j • g + ∑ z, c.dV j z • H z

/-- The challenge ciphertexts: ciphertext `i` is the selective encryption (Algorithm 2) of
`m i` by address `aᵢ` under the audit key `RetrieveKey(V, aᵢ)`, with ephemeral scalar `r i`. -/
def challenge (P : Params F G Addr HK Key Msg C k n) (hk : HK) (H : Addr → G)
    (c : Commit F Addr σ n) (m : Fin (n + 1) → Msg) (r : Fin (n + 1) → F) :
    Fin (n + 1) → C × G :=
  fun i => encrypt (P.kdf hk) P.senc P.g
    (retrieveKey P.pos P.coef (c.vec P.g H) (c.addrs i)) (H (c.addrs i)) (r i) (m i)

/-- The decryption game of Definition 3: the adversary wins if it returns the plaintexts of all
`n + 1` ciphertexts. -/
noncomputable def experiment (P : Params F G Addr HK Key Msg C k n)
    (A : Adversary F G Addr HK Msg C σ n) : ProbComp Bool := do
  let hk ← $ᵗ HK
  let H ← $ᵗ (Addr → G)
  let c ← A.commit hk H
  let m ← $ᵗ (Fin (n + 1) → Msg)
  let r ← $ᵗ (Fin (n + 1) → F)
  let m' ← A.respond c.state (challenge P hk H c m r)
  return decide (∀ i, m' i = m i)

/-! ## The representation of the encryption points and the target index -/

/-- The coefficient of `g` in `Pᵢ = RetrieveKey(V, aᵢ) - H(aᵢ)`. -/
def Commit.gCoeff (c : Commit F Addr σ n) (P : Params F G Addr HK Key Msg C k n)
    (i : Fin (n + 1)) : F :=
  ∑ j, coefRow P.pos P.coef (c.addrs i) j * c.cV j

/-- The coefficient of `H(z)` in `Pᵢ = RetrieveKey(V, aᵢ) - H(aᵢ)`. -/
def Commit.hCoeff (c : Commit F Addr σ n) (P : Params F G Addr HK Key Msg C k n)
    (i : Fin (n + 1)) : Addr → F :=
  fun z => ∑ j, coefRow P.pos P.coef (c.addrs i) j * c.dV j z - if z = c.addrs i then 1 else 0

/-- The target ciphertext: the first index `i` for which the `H`-part of `Pᵢ` is a nonzero
formal combination. Such an index always exists (`exists_hCoeff_ne_zero`). -/
def Commit.target (c : Commit F Addr σ n) (P : Params F G Addr HK Key Msg C k n) :
    Fin (n + 1) :=
  if h : ∃ i, c.hCoeff P i ≠ 0 then Fin.find _ h else 0

/-- The Diffie–Hellman point the reduction derives for ciphertext `i` from a DDH challenge
`(X, Z)`, when the oracle is programmed as `H(z) = u_z • g + t_z • Y`: `α' • X + β' • Z` with
`Pᵢ = α' • g + β' • Y`. -/
def ddhPoint (P : Params F G Addr HK Key Msg C k n) (c : Commit F Addr σ n) (u t : Addr → F)
    (i : Fin (n + 1)) (X Z : G) : G :=
  (c.gCoeff P i + ∑ z, c.hCoeff P i z * u z) • X + (∑ z, c.hCoeff P i z * t z) • Z

/-! ## Hybrids -/

/-- The target's ciphertext for the message `μ` and ephemeral scalar `ρ`, in the given mode:
real, then a uniform Diffie–Hellman point, then a uniform symmetric key, then a uniform key
encrypting the dummy message. -/
noncomputable def slot (P : Params F G Addr HK Key Msg C k n) (mode : Mode) (hk : HK)
    (H : Addr → G) (c : Commit F Addr σ n) (ρ : F) (μ : Msg) : ProbComp (C × G) :=
  match mode with
  | .real =>
    return encrypt (P.kdf hk) P.senc P.g
      (retrieveKey P.pos P.coef (c.vec P.g H) (c.addrs (c.target P))) (H (c.addrs (c.target P)))
      ρ μ
  | .randKey => do
    let K ← $ᵗ G
    return (P.senc (P.kdf hk K) μ, ρ • P.g)
  | .randSym => do
    let key ← $ᵗ Key
    return (P.senc key μ, ρ • P.g)
  | .dummy => do
    let key ← $ᵗ Key
    return (P.senc key P.dummy, ρ • P.g)

/-- The end of a run in which the target's ciphertext is `ct` and its message is `μ`: the other
ciphertexts are the honest encryptions of `m` with ephemeral scalars `r`, and the adversary wins
if it returns `μ` at the target and `m` elsewhere. -/
def finish (P : Params F G Addr HK Key Msg C k n) (A : Adversary F G Addr HK Msg C σ n)
    (hk : HK) (H : Addr → G) (c : Commit F Addr σ n) (m : Fin (n + 1) → Msg)
    (r : Fin (n + 1) → F) (μ : Msg) (ct : C × G) : ProbComp Bool := do
  let m' ← A.respond c.state (Function.update (challenge P hk H c m r) (c.target P) ct)
  return decide (∀ i, m' i = Function.update m (c.target P) μ i)

/-- The hybrids. The target's message `μ` and ephemeral scalar `ρ` are sampled separately; the
target coordinates of `m` and `r` are unused. `hybrid P A .real` is the decryption game
(`experiment_eqd`). -/
noncomputable def hybrid (P : Params F G Addr HK Key Msg C k n)
    (A : Adversary F G Addr HK Msg C σ n) (mode : Mode) : ProbComp Bool := do
  let hk ← $ᵗ HK
  let H ← $ᵗ (Addr → G)
  let c ← A.commit hk H
  let m ← $ᵗ (Fin (n + 1) → Msg)
  let r ← $ᵗ (Fin (n + 1) → F)
  let μ ← $ᵗ Msg
  let ρ ← $ᵗ F
  let ct ← slot P mode hk H c ρ μ
  finish P A hk H c m r μ ct

/-! ## Reductions -/

/-- The reduction to DDH (real → uniform Diffie–Hellman point for the target's ciphertext). It
programs `H(z) = u_z • g + t_z • Y`, embeds `X` as the target's ephemeral key and derives the
target's Diffie–Hellman point from `(X, Z)`. -/
noncomputable def ddhReduction (P : Params F G Addr HK Key Msg C k n)
    (A : Adversary F G Addr HK Msg C σ n) : DDHAdversary F G := fun _ X Y Z => do
  let hk ← $ᵗ HK
  let u ← $ᵗ (Addr → F)
  let t ← $ᵗ (Addr → F)
  let H : Addr → G := fun z => u z • P.g + t z • Y
  let c ← A.commit hk H
  let m ← $ᵗ (Fin (n + 1) → Msg)
  let r ← $ᵗ (Fin (n + 1) → F)
  let μ ← $ᵗ Msg
  finish P A hk H c m r μ (P.senc (P.kdf hk (ddhPoint P c u t (c.target P) X Z)) μ, X)

/-- The reduction to entropy smoothing (uniform Diffie–Hellman point → uniform symmetric key for
the target's ciphertext). -/
noncomputable def esReduction (P : Params F G Addr HK Key Msg C k n)
    (A : Adversary F G Addr HK Msg C σ n) : HK × Key → ProbComp Bool := fun hh => do
  let H ← $ᵗ (Addr → G)
  let c ← A.commit hh.1 H
  let m ← $ᵗ (Fin (n + 1) → Msg)
  let r ← $ᵗ (Fin (n + 1) → F)
  let μ ← $ᵗ Msg
  let ρ ← $ᵗ F
  finish P A hh.1 H c m r μ (P.senc hh.2 μ, ρ • P.g)

/-- The state the one-time reduction keeps between its two phases. -/
structure OTState (F G Addr HK Msg σ : Type) (n : ℕ) where
  /-- The KDF key. -/
  hk : HK
  /-- The hash-to-curve oracle. -/
  H : Addr → G
  /-- The adversary's commitment. -/
  c : Commit F Addr σ n
  /-- The messages of the non-target ciphertexts. -/
  m : Fin (n + 1) → Msg
  /-- The ephemeral scalars of the non-target ciphertexts. -/
  r : Fin (n + 1) → F
  /-- The target's message. -/
  μ : Msg
  /-- The target's ephemeral scalar. -/
  ρ : F

/-- The reduction to one-time security of the cipher (target's message → dummy message under a
uniform key). -/
noncomputable def otReduction (P : Params F G Addr HK Key Msg C k n)
    (A : Adversary F G Addr HK Msg C σ n) :
    OTAdversary Msg C (OTState F G Addr HK Msg σ n) where
  choose := do
    let hk ← $ᵗ HK
    let H ← $ᵗ (Addr → G)
    let c ← A.commit hk H
    let m ← $ᵗ (Fin (n + 1) → Msg)
    let r ← $ᵗ (Fin (n + 1) → F)
    let μ ← $ᵗ Msg
    let ρ ← $ᵗ F
    return (μ, P.dummy, ⟨hk, H, c, m, r, μ, ρ⟩)
  guess st ct := finish P A st.hk st.H st.c st.m st.r st.μ (ct, st.ρ • P.g)

end AuditPay.RestrictedMonitoring.Decrypt
