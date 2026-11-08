/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.Defs
import AuditPay.Prob
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
import VCVio.CryptoFoundations.HardnessAssumptions.EntropySmoothing

/-!
# Theorem 2 (SL-IND): games, assumptions and hybrids

## The SL-IND game (Definition 2)

The adversary is the auditor. Given the public parameters (the KDF key `hk` and the
hash-to-curve oracle `H`), it chooses the monitored set (already padded to `n = |V|` distinct
addresses), the audit secret keys, two deposit addresses `d₀, d₁` and a withdrawal address `w`.
The challenger builds `V` honestly with `AuditKeyVecGen` (the game does not cover a
maliciously formed `V`), makes deposits from `d₀` and `d₁`, and a withdrawal from `d_b`
to `w`: the base-mixer part, the two selective encryptions of the note (to `d_b` and `w`) and a
zero-knowledge proof. The adversary guesses `b`. If `d₀`, `d₁` or `w` is in the monitored set,
or `V` cannot be generated, the game outputs `false` in both worlds.

## Assumptions (all as named advantages of named reductions)

* **Base mixer unlinkability** (`mixerAdvantage`): the base mixer is abstract
  (`BaseMixer`: deposits and the non-auditing part of a withdrawal).
* **Zero knowledge** (`zkAdvantage`): an abstract NIZK whose proofs are indistinguishable from
  simulated ones. Our ZK game lets the distinguisher choose any statement–witness pair; the
  reduction only submits honestly generated pairs, so ZK for true statements suffices.
* **DDH** in `G` (VCV-io's `ddhAdvantage`).
* **Entropy smoothing** of the KDF (VCV-io's `EntropySmoothing.advantage`). The paper models the
  KDF as a random oracle; we use the standard-model keyed-KDF assumption, as VCV-io's hashed
  ElGamal does, with the KDF key `hk` public.
* **One-time security** of the symmetric cipher under a uniform key (`otAdvantage`).

The random oracle `H` is a uniformly random function on a finite address space, given to the
adversary as a value. The position and coefficient hashes are arbitrary fixed functions.

## Hybrids

`hybrid b sim mS mR` runs the game for bit `b`, with a real (`sim = false`) or simulated proof,
and the sender's and recipient's ciphertexts in modes `mS`, `mR` (`Mode`): real, then a uniform
Diffie–Hellman point, then a uniform symmetric key, then an encryption of a fixed dummy note.
-/

open OracleComp DiffieHellman ENNReal

namespace AuditPay.SLIND

/-! ## Abstract components and their security games -/

/-- The base mixer: deposits and the base (non-auditing) part of a withdrawal. -/
structure BaseMixer (Addr Note DTx WCore : Type) where
  /-- A deposit from an address: the depositor's secret note and the public deposit. -/
  deposit : Addr → ProbComp (Note × DTx)
  /-- The base part of a withdrawal (nullifier, root, recipient) spending a note, given the
  public deposits. -/
  withdraw : DTx × DTx → Note → Addr → ProbComp WCore

/-- A base-mixer unlinkability adversary. -/
structure MixerAdversary (Addr DTx WCore τ : Type) where
  /-- Choose the two depositors and the recipient. -/
  choose : ProbComp (Addr × Addr × Addr × τ)
  /-- Guess which deposit was withdrawn. -/
  guess : τ → DTx × DTx → WCore → ProbComp Bool

/-- The paper's admissibility condition on the challenge addresses: two different depositors,
and a recipient different from both. -/
def distinct {Addr : Type} [DecidableEq Addr] (d₀ d₁ w : Addr) : Bool :=
  decide (d₀ ≠ d₁ ∧ w ≠ d₀ ∧ w ≠ d₁)

/-- The base-mixer unlinkability experiment: deposits from `d₀, d₁`, a withdrawal of `d_b`'s
note to `w`. As in the paper, the challenge must have `d₀ ≠ d₁` and `w ∉ {d₀, d₁}`; otherwise
both worlds output `false` (a mixer may reveal that a withdrawal goes back to its depositor). -/
def mixerExperiment {Addr Note DTx WCore τ : Type} [DecidableEq Addr]
    (M : BaseMixer Addr Note DTx WCore)
    (B : MixerAdversary Addr DTx WCore τ) (b : Bool) : ProbComp Bool := do
  let c ← B.choose
  if distinct c.1 c.2.1 c.2.2.1 then
    let n₀ ← M.deposit c.1
    let n₁ ← M.deposit c.2.1
    let core ← M.withdraw (n₀.2, n₁.2) (if b then n₁.1 else n₀.1) c.2.2.1
    B.guess c.2.2.2 (n₀.2, n₁.2) core
  else return false

/-- Base-mixer unlinkability advantage. -/
noncomputable def mixerAdvantage {Addr Note DTx WCore τ : Type} [DecidableEq Addr]
    (M : BaseMixer Addr Note DTx WCore) (B : MixerAdversary Addr DTx WCore τ) : ℝ≥0∞ :=
  𝒟[mixerExperiment M B false].boolDist 𝒟[mixerExperiment M B true]

/-- A non-interactive zero-knowledge proof system with a simulator. -/
structure NIZK (Stmt Wit Proof : Type) where
  /-- The prover. -/
  prove : Stmt → Wit → ProbComp Proof
  /-- The simulator. -/
  sim : Stmt → ProbComp Proof

/-- A zero-knowledge distinguisher. -/
structure ZKAdversary (Stmt Wit Proof τ : Type) where
  /-- Choose a statement and witness. -/
  choose : ProbComp (Stmt × Wit × τ)
  /-- Distinguish a real proof from a simulated one. -/
  guess : τ → Proof → ProbComp Bool

/-- The zero-knowledge experiment: a real proof (`simulated = false`) or a simulated one. -/
def zkExperiment {Stmt Wit Proof τ : Type} (Z : NIZK Stmt Wit Proof)
    (D : ZKAdversary Stmt Wit Proof τ) (simulated : Bool) : ProbComp Bool := do
  let c ← D.choose
  let π ← if simulated then Z.sim c.1 else Z.prove c.1 c.2.1
  D.guess c.2.2 π

/-- Zero-knowledge advantage. -/
noncomputable def zkAdvantage {Stmt Wit Proof τ : Type} (Z : NIZK Stmt Wit Proof)
    (D : ZKAdversary Stmt Wit Proof τ) : ℝ≥0∞ :=
  𝒟[zkExperiment Z D false].boolDist 𝒟[zkExperiment Z D true]

/-- A one-time distinguisher for a symmetric cipher. -/
structure OTAdversary (Msg C τ : Type) where
  /-- Choose two messages. -/
  choose : ProbComp (Msg × Msg × τ)
  /-- Guess which one was encrypted. -/
  guess : τ → C → ProbComp Bool

/-- One-time security experiment for a deterministic cipher under a uniformly random key. -/
def otExperiment {Key Msg C τ : Type} [SampleableType Key] (senc : Key → Msg → C)
    (D : OTAdversary Msg C τ) (b : Bool) : ProbComp Bool := do
  let c ← D.choose
  let key ← $ᵗ Key
  D.guess c.2.2 (senc key (if b then c.2.1 else c.1))

/-- One-time security advantage. -/
noncomputable def otAdvantage {Key Msg C τ : Type} [SampleableType Key]
    (senc : Key → Msg → C) (D : OTAdversary Msg C τ) : ℝ≥0∞ :=
  𝒟[otExperiment senc D false].boolDist 𝒟[otExperiment senc D true]

/-! ## AuditPay parameters, adversaries and the SL-IND game -/

/-- The statement of the withdrawal proof: base withdrawal, the vector, and two ciphertexts. -/
abbrev Stmt (G WCore C : Type) (n : ℕ) := WCore × (Fin n → G) × (C × G) × (C × G)

/-- The witness of the withdrawal proof: the note, the sender, and both ephemeral scalars. -/
abbrev Wit (F Addr Note : Type) := Note × Addr × F × F

/-- Public parameters and components of AuditPay. -/
structure Params (F G Addr HK Key Note DTx WCore C Proof : Type) (k n : ℕ) where
  /-- The generator. -/
  g : G
  /-- Position hashes. -/
  pos : Addr → Fin k → Fin n
  /-- Coefficient hashes. -/
  coef : Addr → Fin k → F
  /-- The key-derivation function, keyed by a public key. -/
  kdf : HK → G → Key
  /-- The symmetric cipher. -/
  senc : Key → Note → C
  /-- A fixed note used as the dummy plaintext in the hybrids. -/
  dummy : Note
  /-- The base mixer. -/
  mixer : BaseMixer Addr Note DTx WCore
  /-- The withdrawal proof system. -/
  zk : NIZK (Stmt G WCore C n) (Wit F Addr Note) Proof

/-- The SL-IND adversary's choices: monitored set, audit secret keys, `d₀`, `d₁`, `w`, state. -/
abbrev Choice (F Addr σ : Type) (n : ℕ) := (Fin n ↪ Addr) × (Fin n → F) × Addr × Addr × Addr × σ

/-- An SL-IND adversary (the auditor). -/
structure Adversary (F G Addr HK DTx WCore C Proof σ : Type) (n : ℕ) where
  /-- Choose the monitored set, audit keys and the three addresses, given `hk` and `H`. -/
  choose : HK → (Addr → G) → ProbComp (Choice F Addr σ n)
  /-- Guess `b` from `V`, the deposits, and the withdrawal. -/
  guess : σ → (Fin n → G) → DTx × DTx → WCore → C × G → C × G → Proof → ProbComp Bool

/-- The challenge addresses must lie outside the monitored set. -/
def valid {F Addr σ : Type} [DecidableEq Addr] {n : ℕ} (c : Choice F Addr σ n) : Bool :=
  decide (∀ i, c.1 i ≠ c.2.2.1 ∧ c.1 i ≠ c.2.2.2.1 ∧ c.1 i ≠ c.2.2.2.2.1) &&
    distinct c.2.2.1 c.2.2.2.1 c.2.2.2.2.1

/-- The challenge addresses of a valid choice are not monitored. -/
theorem valid_excl {F Addr σ : Type} [DecidableEq Addr] {n : ℕ} {c : Choice F Addr σ n}
    (hv : valid c = true) : ∀ i, c.1 i ≠ c.2.2.1 ∧ c.1 i ≠ c.2.2.2.1 ∧ c.1 i ≠ c.2.2.2.2.1 := by
  simp only [valid, Bool.and_eq_true] at hv
  exact of_decide_eq_true hv.1

/-- The challenge addresses of a valid choice are admissible for the base mixer. -/
theorem valid_distinct {F Addr σ : Type} [DecidableEq Addr] {n : ℕ} {c : Choice F Addr σ n}
    (hv : valid c = true) : distinct c.2.2.1 c.2.2.2.1 c.2.2.2.2.1 = true := by
  simp only [valid, Bool.and_eq_true] at hv
  exact hv.2

/-- The mode of one selective-encryption ciphertext in the hybrids. -/
inductive Mode
  /-- The real ciphertext. -/
  | real
  /-- The Diffie–Hellman point is replaced by a uniform group element. -/
  | randKey
  /-- The symmetric key is replaced by a uniform key. -/
  | randSym
  /-- A uniform key encrypting the dummy note. -/
  | dummy
  deriving DecidableEq

variable {F G Addr HK Key Note DTx WCore C Proof σ : Type} {k n : ℕ}
  [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G]
  [Fintype Addr] [DecidableEq Addr] [SampleableType HK] [SampleableType Key]

/-- One selective-encryption ciphertext of the note `m` to address `a`, with ephemeral scalar
`r`, in the given mode. -/
noncomputable def slot (P : Params F G Addr HK Key Note DTx WCore C Proof k n) (mode : Mode)
    (r : F) (hk : HK) (H : Addr → G) (V : Fin n → G) (a : Addr) (m : Note) :
    ProbComp (C × G) :=
  match mode with
  | .real =>
    return (P.senc (P.kdf hk (encPoint r (retrieveKey P.pos P.coef V a) (H a))) m, r • P.g)
  | .randKey => do
    let K ← $ᵗ G
    return (P.senc (P.kdf hk K) m, r • P.g)
  | .randSym => do
    let key ← $ᵗ Key
    return (P.senc key m, r • P.g)
  | .dummy => do
    let key ← $ᵗ Key
    return (P.senc key P.dummy, r • P.g)

/-- The context of a challenge withdrawal, recorded by reductions that must finish the game
after their challenger answers. -/
structure Ctx (F G Addr HK Note DTx WCore σ : Type) (n : ℕ) where
  /-- The KDF key. -/
  hk : HK
  /-- The hash-to-curve oracle. -/
  H : Addr → G
  /-- The adversary's choice. -/
  c : Choice F Addr σ n
  /-- The audit-key vector. -/
  V : Fin n → G
  /-- The deposit from `d₀`. -/
  dep₀ : Note × DTx
  /-- The deposit from `d₁`. -/
  dep₁ : Note × DTx
  /-- The base part of the withdrawal. -/
  core : WCore

/-- The withdrawn note for bit `b`. -/
def Ctx.note {F G Addr HK Note DTx WCore σ : Type} {n : ℕ}
    (x : Ctx F G Addr HK Note DTx WCore σ n) (b : Bool) : Note :=
  if b then x.dep₁.1 else x.dep₀.1

/-- The withdrawing depositor for bit `b`. -/
def Ctx.sender {F G Addr HK Note DTx WCore σ : Type} {n : ℕ}
    (x : Ctx F G Addr HK Note DTx WCore σ n) (b : Bool) : Addr :=
  if b then x.c.2.2.2.1 else x.c.2.2.1

/-- The common first part of the hybrids for bit `b`: everything up to the base withdrawal, or
`none` if the game ends with `false` (invalid choice, or `V` cannot be generated). -/
noncomputable def setup (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) (hk : HK) (H : Addr → G) :
    ProbComp (Option (Ctx F G Addr HK Note DTx WCore σ n)) := do
  let c ← A.choose hk H
  if valid c then
    match auditKeyVecGen P.g H P.pos P.coef c.1 c.2.1 with
    | none => return none
    | some V => do
      let n₀ ← P.mixer.deposit c.2.2.1
      let n₁ ← P.mixer.deposit c.2.2.2.1
      let core ← P.mixer.withdraw (n₀.2, n₁.2) (if b then n₁.1 else n₀.1) c.2.2.2.2.1
      return some ⟨hk, H, c, V, n₀, n₁, core⟩
  else return none

/-- The adversary's final guess on a challenge withdrawal. -/
def finish (A : Adversary F G Addr HK DTx WCore C Proof σ n)
    (x : Ctx F G Addr HK Note DTx WCore σ n) (ctS ctR : C × G) (π : Proof) : ProbComp Bool :=
  A.guess x.c.2.2.2.2.2 x.V (x.dep₀.2, x.dep₁.2) x.core ctS ctR π

/-- The statement of the withdrawal proof. -/
def stmt (x : Ctx F G Addr HK Note DTx WCore σ n) (ctS ctR : C × G) : Stmt G WCore C n :=
  (x.core, x.V, ctS, ctR)

/-- The SL-IND hybrids. `hybrid P A b false .real .real` is the SL-IND game for bit `b`:
after `setup`, sample the two ephemeral scalars, form the sender's and recipient's ciphertexts
(in modes `mS` and `mR`), and a real (`sim = false`) or simulated proof. -/
noncomputable def hybrid (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b sim : Bool) (mS mR : Mode) :
    ProbComp Bool := do
  let hk ← $ᵗ HK
  let H ← $ᵗ (Addr → G)
  let ox ← setup P A b hk H
  match ox with
  | none => return false
  | some x => do
    let rS ← $ᵗ F
    let rR ← $ᵗ F
    let ctS ← slot P mS rS hk H x.V (x.sender b) (x.note b)
    let ctR ← slot P mR rR hk H x.V x.c.2.2.2.2.1 (x.note b)
    let π ← if sim then P.zk.sim (stmt x ctS ctR)
      else P.zk.prove (stmt x ctS ctR) (x.note b, x.sender b, rS, rR)
    finish A x ctS ctR π

/-- The SL-IND experiment for bit `b`. -/
noncomputable def experiment (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) : ProbComp Bool :=
  hybrid P A b false .real .real

/-- The SL-IND advantage. -/
noncomputable def advantage (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) : ℝ≥0∞ :=
  𝒟[experiment P A false].boolDist 𝒟[experiment P A true]

end AuditPay.SLIND
