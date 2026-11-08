/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.KdfRO.ROM
import AuditPay.KdfRO.Variant
import AuditPay.SLIND.Defs

/-!
# Note hiding for a mismatched address, with a random-oracle KDF: games

## The game

The setting is that of the IND-Key game (Definition 1 of the paper), but the challenge is a real
ciphertext, and the key-derivation function is a random oracle that the adversary can query.

1. The challenger samples the hash-to-curve oracle `H` and gives it to the adversary. The
   adversary picks the audit-key address `a` and the encryptor's address `a*`.
2. If `a* = a` the game outputs `false`. Otherwise the challenger samples an audit key for `a`
   (`sk`, `AK_a = sk • g + H(a)`) and the ephemeral randomness, and gives the adversary
   `sk`, `AK_a` and the ephemeral point(s). The adversary picks two notes `m₀, m₁`.
3. The challenger computes the shared point `K = r • (AK_a - H(a*))` (Algorithm 2, line 16),
   **queries the KDF oracle** at `K`, and gives the adversary `SymEnc_{KDF(K)}(m_b)`.
4. The adversary outputs a guess for `b`.

In all three phases the adversary is an oracle computation with oracle access to the KDF (and to
uniform sampling). The KDF is not handed over as a table: the adversary learns its values only
at the points it queries. The game is run in the random oracle model (`KdfRO.roExec`), so the
challenger's query in step 3 and the adversary's queries are answered by the same lazily sampled
random function.

The advantage is the distance between the games for `b = false` and `b = true`.

## How this differs from Definition 1

* Definition 1 hands the adversary the shared point itself, or a uniform group element, and asks
  it to tell them apart. Here the adversary never sees the shared point; it sees a note encrypted
  under the key derived from it.
* The adversary chooses the notes after seeing `(sk, AK_a, R)`, which is at least the power of an
  adversary that must fix them earlier.
* The adversary is the auditor: it knows `sk`. It may be unbounded, but the bounds for the
  variants that need them depend on the number of its KDF queries (`Adversary.QueryBound`).

## The two variants

`Variant.game` is written once for a `Variant` (how the ephemeral randomness gives the published
data and the KDF input). `game` and `Twin.game` are its instances for Algorithm 2 and for the
two-ephemeral-value variant, written out in full; `game_eq` and `Twin.game_eq` are `rfl`.
-/

open OracleComp OracleSpec ENNReal

namespace AuditPay.NoteHiding

open KdfRO SLIND

/-- A note-hiding adversary. `E` is the type of the published ephemeral data and `X` the input
type of the KDF: `E = X = G` for Algorithm 2, `E = X = G × G` for the twin variant. All three
phases have oracle access to the KDF `X →ₒ Key`. -/
structure Adversary (F G Addr E X Key Note C σ τ : Type) where
  /-- Choose the audit-key address `a`, the encryptor's address `a*` and a state, given the
  random oracle `H`. -/
  choose : (Addr → G) → OracleComp (unifSpec + (X →ₒ Key)) (Addr × Addr × σ)
  /-- Choose two notes and a state, from the state and `(sk, AK_a, ephemeral data)`. -/
  notes : σ → F → G → E → OracleComp (unifSpec + (X →ₒ Key)) (Note × Note × τ)
  /-- Guess which note was encrypted, from the state and the symmetric ciphertext. -/
  guess : τ → C → OracleComp (unifSpec + (X →ₒ Key)) Bool

/-- The adversary makes at most `q₁`, `q₂` and `q₃` KDF queries in its three phases, on every
execution path and for every input. (Uniform-sampling queries are not counted.) -/
structure Adversary.QueryBound {F G Addr E X Key Note C σ τ : Type}
    (A : Adversary F G Addr E X Key Note C σ τ) (q₁ q₂ q₃ : ℕ) : Prop where
  /-- At most `q₁` KDF queries while choosing the addresses. -/
  choose : ∀ H, IsQueryBoundP (A.choose H) IsKdfQuery q₁
  /-- At most `q₂` KDF queries while choosing the notes. -/
  notes : ∀ st sk ak e, IsQueryBoundP (A.notes st sk ak e) IsKdfQuery q₂
  /-- At most `q₃` KDF queries while guessing. -/
  guess : ∀ st ct, IsQueryBoundP (A.guess st ct) IsKdfQuery q₃

variable {F G Addr ρ E X Key Note C σ τ : Type} [Field F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G]
  [Fintype Addr] [DecidableEq Addr] [SampleableType ρ] [DecidableEq X] [SampleableType Key]

/-! ## The game, for any variant -/

/-- The note-hiding game for bit `b`, for a variant `S` of selective encryption. -/
noncomputable def _root_.AuditPay.KdfRO.Variant.game (S : Variant G ρ E X) (g : G)
    (senc : Key → Note → C) (A : Adversary F G Addr E X Key Note C σ τ) (b : Bool) :
    OracleComp (unifSpec + (X →ₒ Key)) Bool := do
  let H ← $ᵗ (Addr → G)
  let p ← A.choose H
  if p.1 = p.2.1 then return false else do
    let sk ← $ᵗ F
    let r ← $ᵗ ρ
    let c ← A.notes p.2.2 sk (auditKey g sk (H p.1)) (S.eph r)
    let key ← query (spec := X →ₒ Key) (S.pt r (auditKey g sk (H p.1) - H p.2.1))
    A.guess c.2.2 (senc key (if b then c.2.1 else c.1))

/-- The note-hiding advantage for a variant: the distance between the games for the two bits,
run in the random oracle model. -/
noncomputable def _root_.AuditPay.KdfRO.Variant.advantage (S : Variant G ρ E X) (g : G)
    (senc : Key → Note → C) (A : Adversary F G Addr E X Key Note C σ τ) : ℝ≥0∞ :=
  𝒟[roExec (S.game g senc A false)].boolDist 𝒟[roExec (S.game g senc A true)]

/-! ## Algorithm 2 (the paper's scheme) -/

/-- The note-hiding game for bit `b` and the paper's scheme: the note `m_b` is encrypted under
`KDF(r • (AK_a - H(a*)))`, and the adversary knows `sk`, `AK_a` and `R = r • g`. -/
noncomputable def game (g : G) (senc : Key → Note → C)
    (A : Adversary F G Addr G G Key Note C σ τ) (b : Bool) :
    OracleComp (unifSpec + (G →ₒ Key)) Bool := do
  let H ← $ᵗ (Addr → G)
  let p ← A.choose H
  if p.1 = p.2.1 then return false else do
    let sk ← $ᵗ F
    let r ← $ᵗ F
    let c ← A.notes p.2.2 sk (auditKey g sk (H p.1)) (r • g)
    let key ← query (spec := G →ₒ Key) (encPoint r (auditKey g sk (H p.1)) (H p.2.1))
    A.guess c.2.2 (senc key (if b then c.2.1 else c.1))

omit [SampleableType Key] in
theorem game_eq (g : G) (senc : Key → Note → C)
    (A : Adversary F G Addr G G Key Note C σ τ) (b : Bool) :
    game g senc A b = (single F g).game g senc A b := rfl

/-- The note-hiding experiment for bit `b`: the game run in the random oracle model. -/
noncomputable def experiment [DecidableEq G] (g : G) (senc : Key → Note → C)
    (A : Adversary F G Addr G G Key Note C σ τ) (b : Bool) : ProbComp Bool :=
  roExec (game g senc A b)

/-- The note-hiding advantage for the paper's scheme. -/
noncomputable def advantage [DecidableEq G] (g : G) (senc : Key → Note → C)
    (A : Adversary F G Addr G G Key Note C σ τ) : ℝ≥0∞ :=
  𝒟[experiment g senc A false].boolDist 𝒟[experiment g senc A true]

theorem advantage_eq [DecidableEq G] (g : G) (senc : Key → Note → C)
    (A : Adversary F G Addr G G Key Note C σ τ) :
    advantage g senc A = (single F g).advantage g senc A := rfl

/-! ## The twin variant -/

namespace Twin

/-- The note-hiding game for bit `b` and the twin variant: the note `m_b` is encrypted under
`KDF(r₁ • P, r₂ • P)` with `P = AK_a - H(a*)`, and the adversary knows `sk`, `AK_a`,
`R₁ = r₁ • g` and `R₂ = r₂ • g`. -/
noncomputable def game (g : G) (senc : Key → Note → C)
    (A : Adversary F G Addr (G × G) (G × G) Key Note C σ τ) (b : Bool) :
    OracleComp (unifSpec + ((G × G) →ₒ Key)) Bool := do
  let H ← $ᵗ (Addr → G)
  let p ← A.choose H
  if p.1 = p.2.1 then return false else do
    let sk ← $ᵗ F
    let r ← $ᵗ (F × F)
    let c ← A.notes p.2.2 sk (auditKey g sk (H p.1)) (r.1 • g, r.2 • g)
    let key ← query (spec := (G × G) →ₒ Key)
      (Twin.encPoint r (auditKey g sk (H p.1)) (H p.2.1))
    A.guess c.2.2 (senc key (if b then c.2.1 else c.1))

omit [SampleableType Key] in
theorem game_eq (g : G) (senc : Key → Note → C)
    (A : Adversary F G Addr (G × G) (G × G) Key Note C σ τ) (b : Bool) :
    game g senc A b = (twin F g).game g senc A b := rfl

/-- The note-hiding experiment for bit `b` and the twin variant. -/
noncomputable def experiment [DecidableEq G] (g : G) (senc : Key → Note → C)
    (A : Adversary F G Addr (G × G) (G × G) Key Note C σ τ) (b : Bool) : ProbComp Bool :=
  roExec (game g senc A b)

/-- The note-hiding advantage for the twin variant. -/
noncomputable def advantage [DecidableEq G] (g : G) (senc : Key → Note → C)
    (A : Adversary F G Addr (G × G) (G × G) Key Note C σ τ) : ℝ≥0∞ :=
  𝒟[experiment g senc A false].boolDist 𝒟[experiment g senc A true]

theorem advantage_eq [DecidableEq G] (g : G) (senc : Key → Note → C)
    (A : Adversary F G Addr (G × G) (G × G) Key Note C σ τ) :
    advantage g senc A = (twin F g).advantage g senc A := rfl

end Twin

/-! ## The ideal run, and the event that the shared point is queried -/

/-- The outcome of an ideal run with an admissible choice: the point `P = AK_a - H(a*)`, the
ephemeral randomness, and the final KDF cache. -/
abbrev Outcome (G ρ X Key : Type) := G × ρ × (X →ₒ Key).QueryCache

/-- The *ideal* run for bit `b`: the game in the random oracle model, written out phase by phase
(each phase continues from the cache the previous one left), except that the note is encrypted
under a fresh uniform key and the challenger does not query the KDF. Returns the adversary's
guess and, unless the choice was inadmissible, the `Outcome`. In this run the cache holds
exactly the points the adversary queried. -/
noncomputable def _root_.AuditPay.KdfRO.Variant.idealRun (S : Variant G ρ E X) (g : G)
    (senc : Key → Note → C) (A : Adversary F G Addr E X Key Note C σ τ) (b : Bool) :
    ProbComp (Bool × Option (Outcome G ρ X Key)) := do
  let H ← $ᵗ (Addr → G)
  let z ← roRun (A.choose H) ∅
  if z.1.1 = z.1.2.1 then return (false, none) else do
    let sk ← $ᵗ F
    let r ← $ᵗ ρ
    let w ← roRun (A.notes z.1.2.2 sk (auditKey g sk (H z.1.1)) (S.eph r)) z.2
    let key ← $ᵗ Key
    let v ← roRun (A.guess w.1.2.2 (senc key (if b then w.1.2.1 else w.1.1))) w.2
    return (v.1, some (auditKey g sk (H z.1.1) - H z.1.2.1, r, v.2))

/-- The adversary queried the KDF at the shared point `S.pt r P` in an ideal run. -/
def _root_.AuditPay.KdfRO.Variant.Queried (S : Variant G ρ E X)
    (o : Option (Outcome G ρ X Key)) : Prop :=
  ∃ t, o = some t ∧ (t.2.2 (S.pt t.2.1 t.1)).isSome

/-- The probability that the adversary queries the KDF at the shared point in the ideal run for
bit `b`. -/
noncomputable def _root_.AuditPay.KdfRO.Variant.queryProb (S : Variant G ρ E X) (g : G)
    (senc : Key → Note → C) (A : Adversary F G Addr E X Key Note C σ τ) (b : Bool) : ℝ≥0∞ :=
  Pr{let x ← S.idealRun g senc A b}[S.Queried x.2]

/-! ## The one-time-security reduction -/

/-- The reduction to one-time security of the cipher: it runs the adversary's first two phases
against a lazily sampled KDF of its own, submits the adversary's two notes, and runs the last
phase on the challenge ciphertext. (If the adversary's choice is inadmissible it submits fixed
default notes and outputs `false`.) -/
noncomputable def _root_.AuditPay.KdfRO.Variant.otReduction [Inhabited Note]
    (S : Variant G ρ E X) (g : G) (A : Adversary F G Addr E X Key Note C σ τ) :
    OTAdversary Note C (Option (τ × (X →ₒ Key).QueryCache)) where
  choose := do
    let H ← $ᵗ (Addr → G)
    let z ← roRun (A.choose H) ∅
    if z.1.1 = z.1.2.1 then return (default, default, none) else do
      let sk ← $ᵗ F
      let r ← $ᵗ ρ
      let w ← roRun (A.notes z.1.2.2 sk (auditKey g sk (H z.1.1)) (S.eph r)) z.2
      return (w.1.1, w.1.2.1, some (w.1.2.2, w.2))
  guess st ct :=
    match st with
    | none => return false
    | some s => Prod.fst <$> roRun (A.guess s.1 ct) s.2

/-- The one-time-security reduction for note hiding of the paper's scheme. -/
noncomputable def otReduction [DecidableEq G] [Inhabited Note] (g : G)
    (A : Adversary F G Addr G G Key Note C σ τ) :
    OTAdversary Note C (Option (τ × (G →ₒ Key).QueryCache)) :=
  (single F g).otReduction g A

/-- The one-time-security reduction for note hiding of the twin variant. -/
noncomputable def Twin.otReduction [DecidableEq G] [Inhabited Note] (g : G)
    (A : Adversary F G Addr (G × G) (G × G) Key Note C σ τ) :
    OTAdversary Note C (Option (τ × ((G × G) →ₒ Key).QueryCache)) :=
  (twin F g).otReduction g A

end AuditPay.NoteHiding
