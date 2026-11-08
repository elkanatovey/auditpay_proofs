/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.KdfRO.Table
import AuditPay.KdfRO.Variant
import AuditPay.RestrictedMonitoring.SharedSecret
import AuditPay.SLIND.Defs

/-!
# Theorem 3 (Restricted Monitoring), the paper's decryption game, random-oracle KDF: games

## The game (Definition 3 of the paper)

1. The challenger samples the hash-to-curve oracle `H` and gives it to the adversary. The
   adversary outputs an **arbitrary** vector `V` of `n` group elements and `n + 1` distinct
   addresses `a₀, …, aₙ`. (No algebraic representation of `V` is required, unlike
   `AuditPay.RestrictedMonitoring.Decrypt`.)
2. The challenger samples, for every `i`, a uniform message `mᵢ` and the ephemeral randomness
   `rᵢ`, forms the shared point `Kᵢ` of a selective encryption to `aᵢ` under the audit key
   `RetrieveKey(V, aᵢ)` (Algorithm 2 or its twin variant), **queries the KDF oracle** at `Kᵢ`, and
   gives the adversary the ciphertexts `(SymEnc_{KDF(Kᵢ)}(mᵢ), ephemeral data)`.
3. The adversary outputs guesses `m'ᵢ`; it wins if all `n + 1` are right.

Both phases of the adversary have oracle access to the KDF (and to uniform sampling); the game
is run in the random oracle model (`KdfRO.roExec`). The paper's Definition 3 does not say what
is encrypted; as in `AuditPay.RestrictedMonitoring.Decrypt`, the messages are independent and
uniform, so that a ciphertext whose key the adversary does not know is decrypted only by
guessing (the term `1/|Msg|`).

`Variant.monitoringGame` is written once for a `Variant`; `game` and `Twin.game` are its two
instances, written out (`game_eq`, `Twin.game_eq` are `rfl`).

## The prefix, the suffix and the eager suffix

The proofs split a run into the *prefix* (`prefixRun`: `H`, the commitment with its KDF cache,
the ephemeral randomness and the messages) and the *suffix* (the challenger's queries and the
second phase). By `KdfRO.evalDist_roRun_eq_tableRun` the suffix can be run against a fixed
table completing the prefix's cache; `suffixRun` is that eager run, with the second phase's
queries logged.
-/

open OracleComp OracleSpec ENNReal

namespace AuditPay.Monitoring

open KdfRO SLIND

/-- The first-phase output of an adversary: a vector `V`, `n + 1` distinct addresses and a
state (`AuditPay.RestrictedMonitoring.SharedSecret.Commit`). -/
abbrev Commit (G Addr σ : Type) (n : ℕ) := RestrictedMonitoring.SharedSecret.Commit G Addr σ n

/-- A decryption adversary with oracle access to the KDF `X →ₒ Key`. `E` is the type of the
published ephemeral data (`G` for Algorithm 2, `G × G` for the twin variant). -/
structure Adversary (G Addr E X Key Msg C σ : Type) (n : ℕ) where
  /-- Given `H`, output a vector `V`, `n + 1` distinct addresses and a state. -/
  commit : (Addr → G) → OracleComp (unifSpec + (X →ₒ Key)) (Commit G Addr σ n)
  /-- Given the state and the `n + 1` ciphertexts, guess the messages. -/
  respond : σ → (Fin (n + 1) → C × E) → OracleComp (unifSpec + (X →ₒ Key)) (Fin (n + 1) → Msg)

/-- The adversary makes at most `q₁` KDF queries in its first phase and `q₂` in its second, on
every execution path and for every input. -/
structure Adversary.QueryBound {G Addr E X Key Msg C σ : Type} {n : ℕ}
    (A : Adversary G Addr E X Key Msg C σ n) (q₁ q₂ : ℕ) : Prop where
  /-- At most `q₁` KDF queries while committing. -/
  commit : ∀ H, IsQueryBoundP (A.commit H) IsKdfQuery q₁
  /-- At most `q₂` KDF queries while responding. -/
  respond : ∀ st cts, IsQueryBoundP (A.respond st cts) IsKdfQuery q₂

variable {F G Addr ρ E X Key Msg C σ : Type} {k n : ℕ} [Field F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G]
  [Fintype Addr] [DecidableEq Addr] [SampleableType ρ] [SampleableType Key]
  [SampleableType Msg] [DecidableEq Msg]

/-- The points `Pᵢ = RetrieveKey(V, aᵢ) - H(aᵢ)` of a commitment. -/
def pts (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F) (H : Addr → G)
    (c : Commit G Addr σ n) (i : Fin (n + 1)) : G :=
  retrieveKey pos coef c.1 (c.2.1 i) - H (c.2.1 i)

/-! ## The game, for any variant -/

/-- The suffix of the decryption game, after the commitment, the ephemeral randomness `r` and
the messages `m`: the challenger's KDF queries at the shared points, the second phase, and the
verdict. -/
def _root_.AuditPay.KdfRO.Variant.monitoringSuffix (S : Variant G ρ E X)
    (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F) (senc : Key → Msg → C)
    (A : Adversary G Addr E X Key Msg C σ n) (H : Addr → G) (c : Commit G Addr σ n)
    (r : Fin (n + 1) → ρ) (m : Fin (n + 1) → Msg) : OracleComp (unifSpec + (X →ₒ Key)) Bool := do
  let keys ← queryFin fun i => S.pt (r i) (pts pos coef H c i)
  let m' ← A.respond c.2.2 fun i => (senc (keys i) (m i), S.eph (r i))
  return decide (∀ i, m' i = m i)

/-- The decryption game for a variant `S`: the adversary wins if it decrypts all `n + 1`
ciphertexts, whose keys the challenger obtains by querying the KDF oracle. -/
noncomputable def _root_.AuditPay.KdfRO.Variant.monitoringGame (S : Variant G ρ E X)
    (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F) (senc : Key → Msg → C)
    (A : Adversary G Addr E X Key Msg C σ n) : OracleComp (unifSpec + (X →ₒ Key)) Bool := do
  let H ← $ᵗ (Addr → G)
  let c ← A.commit H
  let r ← $ᵗ (Fin (n + 1) → ρ)
  let m ← $ᵗ (Fin (n + 1) → Msg)
  S.monitoringSuffix pos coef senc A H c r m

/-- The decryption experiment for a variant: the game run in the random oracle model. -/
noncomputable def _root_.AuditPay.KdfRO.Variant.monitoringExperiment [DecidableEq X]
    (S : Variant G ρ E X) (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F)
    (senc : Key → Msg → C) (A : Adversary G Addr E X Key Msg C σ n) : ProbComp Bool :=
  roExec (S.monitoringGame pos coef senc A)

/-! ## Algorithm 2 and the twin variant -/

/-- The decryption game of Definition 3 for the paper's scheme, with a random-oracle KDF:
ciphertext `i` is `(SymEnc_{KDF(rᵢ • (RetrieveKey(V, aᵢ) - H(aᵢ)))}(mᵢ), rᵢ • g)`. -/
noncomputable def game (g : G) (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F)
    (senc : Key → Msg → C) (A : Adversary G Addr G G Key Msg C σ n) :
    OracleComp (unifSpec + (G →ₒ Key)) Bool := do
  let H ← $ᵗ (Addr → G)
  let c ← A.commit H
  let r ← $ᵗ (Fin (n + 1) → F)
  let m ← $ᵗ (Fin (n + 1) → Msg)
  let keys ← queryFin fun i =>
    encPoint (r i) (retrieveKey pos coef c.1 (c.2.1 i)) (H (c.2.1 i))
  let m' ← A.respond c.2.2 fun i => (senc (keys i) (m i), r i • g)
  return decide (∀ i, m' i = m i)

omit [SampleableType Key] in
theorem game_eq (g : G) (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F)
    (senc : Key → Msg → C) (A : Adversary G Addr G G Key Msg C σ n) :
    game g pos coef senc A = (single F g).monitoringGame pos coef senc A := rfl

/-- The decryption experiment for the paper's scheme. -/
noncomputable def experiment [DecidableEq G] (g : G) (pos : Addr → Fin k → Fin n)
    (coef : Addr → Fin k → F) (senc : Key → Msg → C)
    (A : Adversary G Addr G G Key Msg C σ n) : ProbComp Bool :=
  roExec (game g pos coef senc A)

namespace Twin

/-- The decryption game for the twin variant: ciphertext `i` is
`(SymEnc_{KDF(r₁ᵢ • Pᵢ, r₂ᵢ • Pᵢ)}(mᵢ), r₁ᵢ • g, r₂ᵢ • g)` with
`Pᵢ = RetrieveKey(V, aᵢ) - H(aᵢ)`. -/
noncomputable def game (g : G) (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F)
    (senc : Key → Msg → C) (A : Adversary G Addr (G × G) (G × G) Key Msg C σ n) :
    OracleComp (unifSpec + ((G × G) →ₒ Key)) Bool := do
  let H ← $ᵗ (Addr → G)
  let c ← A.commit H
  let r ← $ᵗ (Fin (n + 1) → F × F)
  let m ← $ᵗ (Fin (n + 1) → Msg)
  let keys ← queryFin fun i =>
    Twin.encPoint (r i) (retrieveKey pos coef c.1 (c.2.1 i)) (H (c.2.1 i))
  let m' ← A.respond c.2.2 fun i => (senc (keys i) (m i), (r i).1 • g, (r i).2 • g)
  return decide (∀ i, m' i = m i)

omit [SampleableType Key] in
theorem game_eq (g : G) (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F)
    (senc : Key → Msg → C) (A : Adversary G Addr (G × G) (G × G) Key Msg C σ n) :
    game g pos coef senc A = (twin F g).monitoringGame pos coef senc A := rfl

/-- The decryption experiment for the twin variant. -/
noncomputable def experiment [DecidableEq G] (g : G) (pos : Addr → Fin k → Fin n)
    (coef : Addr → Fin k → F) (senc : Key → Msg → C)
    (A : Adversary G Addr (G × G) (G × G) Key Msg C σ n) : ProbComp Bool :=
  roExec (game g pos coef senc A)

end Twin

/-! ## The prefix of a run -/

/-- The outcome of the prefix of a run: `H`, the commitment, the KDF cache after the first
phase, the ephemeral randomness and the messages. -/
structure Pre (G Addr ρ X Key Msg σ : Type) (n : ℕ) where
  /-- The hash-to-curve oracle. -/
  H : Addr → G
  /-- The commitment. -/
  c : Commit G Addr σ n
  /-- The KDF cache after the first phase: the points the adversary queried, with their keys. -/
  cache : (X →ₒ Key).QueryCache
  /-- The ephemeral randomness. -/
  r : Fin (n + 1) → ρ
  /-- The messages. -/
  m : Fin (n + 1) → Msg

/-- The prefix of a run in the random oracle model: `H`, the first phase (lazily sampled KDF),
the ephemeral randomness and the messages. -/
noncomputable def prefixRun [DecidableEq X] (A : Adversary G Addr E X Key Msg C σ n) :
    ProbComp (Pre G Addr ρ X Key Msg σ n) := do
  let H ← $ᵗ (Addr → G)
  let z ← roRun (A.commit H) ∅
  let r ← $ᵗ (Fin (n + 1) → ρ)
  let m ← $ᵗ (Fin (n + 1) → Msg)
  return ⟨H, z.1, z.2, r, m⟩

variable (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F)

/-- The point `Pᵢ` of a prefix. -/
def Pre.P (p : Pre G Addr ρ X Key Msg σ n) (i : Fin (n + 1)) : G := pts pos coef p.H p.c i

/-- The KDF input `Kᵢ` of a prefix, for a variant. -/
def Pre.K (S : Variant G ρ E X) (p : Pre G Addr ρ X Key Msg σ n) (i : Fin (n + 1)) : X :=
  S.pt (p.r i) (p.P pos coef i)

/-- The *hidden* indices of a prefix: those with `Pᵢ ≠ 0`. For the others `Kᵢ` is the known
point `S.pt rᵢ 0`. -/
def Pre.hid [DecidableEq G] (p : Pre G Addr ρ X Key Msg σ n) (i : Fin (n + 1)) : Bool :=
  decide (p.P pos coef i ≠ 0)

/-- A *good* prefix: the hidden points are pairwise distinct, distinct from every other point,
and were not queried in the first phase. -/
def Pre.Good [DecidableEq G] (S : Variant G ρ E X) (p : Pre G Addr ρ X Key Msg σ n) : Prop :=
  (∀ i j, p.hid pos coef i → i ≠ j → p.K pos coef S i ≠ p.K pos coef S j) ∧
    ∀ i, p.hid pos coef i → p.cache (p.K pos coef S i) = none

/-! ## The suffix of a run, against a table -/

/-- The suffix of a run against the KDF table `T`, with the keys `keys` for the ciphertexts: the
second phase with its queries logged. -/
noncomputable def suffixRun (S : Variant G ρ E X) (senc : Key → Msg → C)
    (A : Adversary G Addr E X Key Msg C σ n) (p : Pre G Addr ρ X Key Msg σ n) (T : X → Key)
    (keys : Fin (n + 1) → Key) :
    ProbComp ((Fin (n + 1) → Msg) × QueryLog (unifSpec + (X →ₒ Key))) :=
  tableRun T (A.respond p.c.2.2 fun i => (senc (keys i) (p.m i), S.eph (p.r i))).withQueryLog

/-- The adversary decrypted every ciphertext. -/
abbrev Win (p : Pre G Addr ρ X Key Msg σ n)
    (z : (Fin (n + 1) → Msg) × QueryLog (unifSpec + (X →ₒ Key))) : Prop :=
  ∀ i, z.1 i = p.m i

/-- The second phase queried the KDF at the point `Z`. -/
def Hit (Z : X) (z : (Fin (n + 1) → Msg) × QueryLog (unifSpec + (X →ₒ Key))) : Prop :=
  ∃ u, ⟨Sum.inr Z, u⟩ ∈ z.2

/-- The *programmed* table of a prefix: the table `g` completing the prefix's cache, with the
fresh keys `κ` at the hidden points. -/
def progTable [DecidableEq X] [DecidableEq G] (S : Variant G ρ E X)
    (p : Pre G Addr ρ X Key Msg σ n) (g : X → Key) (κ : Fin (n + 1) → Key) : X → Key :=
  completeTable p.cache (override g (p.K pos coef S) (p.hid pos coef) κ)

end AuditPay.Monitoring
