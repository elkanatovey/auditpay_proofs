/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.KdfRO.ROM
import AuditPay.KdfRO.Variant
import AuditPay.SLINDDrop.Defs

/-!
# Theorem 2 (SL-IND) with a random-oracle KDF: games and hybrids

The SL-IND game of `AuditPay.SLINDDrop` (Theorem 2 for the never-failing generation), with the
key-derivation function modelled as a **random oracle that the adversary queries**, as in the
paper, instead of a keyed hash under entropy smoothing. This is the setting in which the
security of the selective encryption can be proved without DDH (see `AuditPay.KdfRO`).

## The game

The adversary is the auditor. It has oracle access to the KDF `X →ₒ Key` (and to uniform
sampling) in both of its phases; `X = G` for Algorithm 2 and `X = G × G` for the twin variant.

1. The challenger samples the hash-to-curve oracle `H` and gives it to the adversary, which
   chooses (`SLINDDrop.Choice`) an ordered request `l`, audit secret keys `sk`, fill scalars
   `w`, two deposit addresses `d₀, d₁`, a withdrawal address `w_addr` and a state.
2. The choice must be *valid* (`SLINDDrop.valid`): `d₀ ≠ d₁`, `w_addr ∉ {d₀, d₁}`, and none of
   the three in the selected set `T = sel.select pos coef l`; otherwise the game outputs
   `false` in both worlds. The challenger publishes
   `V = encodeSet g H pos coef T sk|_T (w • g)` (never fails), makes deposits from `d₀` and
   `d₁`, and the base part of a withdrawal of `d_b`'s note to `w_addr`.
3. The challenger samples the ephemeral randomness `rS, rR` of the two selective encryptions
   (to the sender `d_b` and to the recipient `w_addr`), **queries the KDF oracle** at the two
   shared points `S.pt rS (RetrieveKey(V, d_b) - H(d_b))` and
   `S.pt rR (RetrieveKey(V, w_addr) - H(w_addr))`, encrypts the note under the two answers, and
   proves the withdrawal statement with the witness `(note, d_b, rS, rR)`.
4. The adversary sees `V`, the deposits, the base withdrawal, both ciphertexts (each with its
   published ephemeral data) and the proof, and guesses `b`.

The game is an oracle computation; the experiment runs it in the random oracle model
(`KdfRO.roExec`), so the challenger's two queries and the adversary's queries are answered by
the same lazily sampled random function. The adversary never holds the KDF as a table.

## How this differs from `AuditPay.SLINDDrop` and from the paper's Definition 2

* The KDF has no public key `hk`; there is no entropy-smoothing assumption. The symmetric key
  of a ciphertext is the random oracle's answer at the shared point. Everything else about the
  generation of `V`, the validity check, the base mixer, the proof system and the cipher is
  as in `AuditPay.SLINDDrop`.
* The adversary's phases are oracle computations; bounds may depend on its numbers of KDF
  queries (`Adversary.QueryBound`).
* Against Definition 2: as in `AuditPay.SLIND`, the adversary chooses the secret keys (and
  here the fill scalars) and sees `H`; the challenge addresses must be distinct and unmonitored;
  `V` is honestly generated; the proof statement contains `V` itself.
* The game is written once for a `Variant` (`KdfRO.Variant`: the published ephemeral data and
  the KDF input), so that Algorithm 2 (`KdfRO.single`) and the twin variant (`KdfRO.twin`) are
  two instances. The statement and witness of the withdrawal proof carry the published
  ephemeral data `E` and the ephemeral randomness `ρ` of the variant.

## Hybrids

`hybrid S sel P A b sim mS mR` is the game for bit `b`, run phase by phase in the random oracle
model (each phase continues from the cache the previous one left), with a real or simulated
proof and the two ciphertexts in modes `mS`, `mR` (`Mode`): the real ciphertext (its key is the
KDF's answer at the shared point), the note under a *fresh* uniform key, or the dummy note
under a fresh key. It also returns the final KDF cache, which is what the random-oracle hop
inspects: `QueriedS`/`QueriedR` say that the shared point of the sender's/recipient's
ciphertext is in it, and `queryProbS`/`queryProbR` are the probabilities of these events in
the runs where that ciphertext's key is fresh. In those runs the key is independent of the
shared point, so this is the probability that the adversary (or, in the sender's case, the
challenger's query for the recipient's ciphertext) hits the shared point.
-/

open OracleComp OracleSpec ENNReal

namespace AuditPay.SLINDRO

open KdfRO
open AuditPay.SLIND (BaseMixer NIZK distinct)
open AuditPay.SLINDDrop (Choice selected valid)

/-- The statement of the withdrawal proof: base withdrawal, the vector, and two ciphertexts,
each a symmetric ciphertext with its published ephemeral data. -/
abbrev Stmt (G WCore C E : Type) (n : ℕ) := WCore × (Fin n → G) × (C × E) × (C × E)

/-- The witness of the withdrawal proof: the note, the sender, and the ephemeral randomness of
both ciphertexts. -/
abbrev Wit (Addr Note ρ : Type) := Note × Addr × ρ × ρ

/-- Public parameters and components of AuditPay, for a random-oracle KDF: there is no KDF
key. `ρ` is the ephemeral randomness and `E` the published ephemeral data of the
selective-encryption variant. -/
structure Params (F G Addr ρ E Key Note DTx WCore C Proof : Type) (k n : ℕ) where
  /-- The generator. -/
  g : G
  /-- Position hashes. -/
  pos : Addr → Fin k → Fin n
  /-- Coefficient hashes. -/
  coef : Addr → Fin k → F
  /-- The symmetric cipher. -/
  senc : Key → Note → C
  /-- A fixed note used as the dummy plaintext in the hybrids. -/
  dummy : Note
  /-- The base mixer. -/
  mixer : BaseMixer Addr Note DTx WCore
  /-- The withdrawal proof system. -/
  zk : NIZK (Stmt G WCore C E n) (Wit Addr Note ρ) Proof

/-- An SL-IND adversary (the auditor) with oracle access to the KDF `X →ₒ Key` in both phases.
`E` is the type of the published ephemeral data of a ciphertext. -/
structure Adversary (F G Addr E X Key DTx WCore C Proof σ : Type) (n : ℕ) where
  /-- Choose the request, audit secret keys, fill scalars, the three addresses and a state,
  given `H`. -/
  choose : (Addr → G) → OracleComp (unifSpec + (X →ₒ Key)) (Choice F Addr σ n)
  /-- Guess `b` from the state, `V`, the deposits, the base withdrawal, the two ciphertexts and
  the proof. -/
  guess : σ → (Fin n → G) → DTx × DTx → WCore → C × E → C × E → Proof →
    OracleComp (unifSpec + (X →ₒ Key)) Bool

/-- The adversary makes at most `q₁` KDF queries in its first phase and `q₂` in its second, on
every execution path and for every input. (Uniform-sampling queries are not counted.) -/
structure Adversary.QueryBound {F G Addr E X Key DTx WCore C Proof σ : Type} {n : ℕ}
    (A : Adversary F G Addr E X Key DTx WCore C Proof σ n) (q₁ q₂ : ℕ) : Prop where
  /-- At most `q₁` KDF queries while choosing. -/
  choose : ∀ H, IsQueryBoundP (A.choose H) IsKdfQuery q₁
  /-- At most `q₂` KDF queries while guessing. -/
  guess : ∀ st V deps core ctS ctR π,
    IsQueryBoundP (A.guess st V deps core ctS ctR π) IsKdfQuery q₂

variable {F G Addr ρ E X Key Note DTx WCore C Proof σ : Type} {k n : ℕ}
  [Field F] [AddCommGroup G] [Module F G] [DecidableEq Addr]

/-- The audit-key vector of a request `l` with audit secret keys `sk` and fill scalars `w`:
`V = encodeSet g H pos coef T sk|_T (w • g)` for the selected set `T = sel.select pos coef l`
(`AuditPay.SilentDrop`). -/
noncomputable def auditVec (g : G) (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F)
    (sel : Selection F Addr k n) (H : Addr → G) (l : List Addr) (sk : Addr → F)
    (w : Fin n → F) : Fin n → G :=
  encodeSet g H pos coef (sel.select pos coef l) (fun a => sk a) fun j => w j • g

/-- The context of a challenge withdrawal: everything up to the base withdrawal. -/
structure Ctx (F G Addr Note DTx WCore σ : Type) (n : ℕ) where
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
def Ctx.note (x : Ctx F G Addr Note DTx WCore σ n) (b : Bool) : Note :=
  if b then x.dep₁.1 else x.dep₀.1

/-- The withdrawing depositor for bit `b`. -/
def Ctx.sender (x : Ctx F G Addr Note DTx WCore σ n) (b : Bool) : Addr :=
  if b then x.c.d₁ else x.c.d₀

/-- The point `RetrieveKey(V, a) - H(a)` that a selective encryption to `a` is keyed on. -/
def Ctx.pt (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F)
    (x : Ctx F G Addr Note DTx WCore σ n) (a : Addr) : G :=
  retrieveKey pos coef x.V a - x.H a

variable [SampleableType G] [Fintype Addr] [SampleableType Key]

/-- After the adversary's choice: if it is valid, generate `V`, make the two deposits and the
base withdrawal of `d_b`'s note; otherwise `none` (the game outputs `false`). -/
noncomputable def setup (sel : Selection F Addr k n)
    (P : Params F G Addr ρ E Key Note DTx WCore C Proof k n) (b : Bool) (H : Addr → G)
    (c : Choice F Addr σ n) : ProbComp (Option (Ctx F G Addr Note DTx WCore σ n)) :=
  if valid sel P.pos P.coef c then do
    let n₀ ← P.mixer.deposit c.d₀
    let n₁ ← P.mixer.deposit c.d₁
    let core ← P.mixer.withdraw (n₀.2, n₁.2) (if b then n₁.1 else n₀.1) c.wAddr
    return some ⟨H, c, auditVec P.g P.pos P.coef sel H c.req c.sk c.fill, n₀, n₁, core⟩
  else return none

/-- The statement of the withdrawal proof. -/
def stmt (x : Ctx F G Addr Note DTx WCore σ n) (ctS ctR : C × E) : Stmt G WCore C E n :=
  (x.core, x.V, ctS, ctR)

/-- The adversary's final guess on a challenge withdrawal. -/
def finish (A : Adversary F G Addr E X Key DTx WCore C Proof σ n)
    (x : Ctx F G Addr Note DTx WCore σ n) (ctS ctR : C × E) (π : Proof) :
    OracleComp (unifSpec + (X →ₒ Key)) Bool :=
  A.guess x.c.state x.V (x.dep₀.2, x.dep₁.2) x.core ctS ctR π

/-! ## The game -/

variable [SampleableType ρ]

/-- The SL-IND game for bit `b` with a random-oracle KDF, for the selective-encryption variant
`S` and the selection rule `sel`. The two symmetric keys are the KDF oracle's answers at the
shared points of the sender's and the recipient's ciphertexts. -/
noncomputable def game (S : Variant G ρ E X) (sel : Selection F Addr k n)
    (P : Params F G Addr ρ E Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr E X Key DTx WCore C Proof σ n) (b : Bool) :
    OracleComp (unifSpec + (X →ₒ Key)) Bool := do
  let H ← $ᵗ (Addr → G)
  let c ← A.choose H
  let ox ← setup sel P b H c
  match ox with
  | none => return false
  | some x => do
    let rS ← $ᵗ ρ
    let rR ← $ᵗ ρ
    let keyS ← query (spec := X →ₒ Key) (S.pt rS (x.pt P.pos P.coef (x.sender b)))
    let keyR ← query (spec := X →ₒ Key) (S.pt rR (x.pt P.pos P.coef x.c.wAddr))
    let ctS := (P.senc keyS (x.note b), S.eph rS)
    let ctR := (P.senc keyR (x.note b), S.eph rR)
    let π ← P.zk.prove (stmt x ctS ctR) (x.note b, x.sender b, rS, rR)
    finish A x ctS ctR π

/-- The SL-IND experiment for bit `b`: the game run in the random oracle model. -/
noncomputable def experiment [DecidableEq X] (S : Variant G ρ E X) (sel : Selection F Addr k n)
    (P : Params F G Addr ρ E Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr E X Key DTx WCore C Proof σ n) (b : Bool) : ProbComp Bool :=
  roExec (game S sel P A b)

/-- The SL-IND advantage with a random-oracle KDF. -/
noncomputable def advantage [DecidableEq X] (S : Variant G ρ E X) (sel : Selection F Addr k n)
    (P : Params F G Addr ρ E Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr E X Key DTx WCore C Proof σ n) : ℝ≥0∞ :=
  𝒟[experiment S sel P A false].boolDist 𝒟[experiment S sel P A true]

/-! ## Hybrids -/

/-- The mode of one ciphertext in the hybrids. -/
inductive Mode
  /-- The real ciphertext: the note under the KDF's answer at the shared point. -/
  | real
  /-- The note under a fresh uniform key; the KDF is not queried. -/
  | fresh
  /-- The dummy note under a fresh uniform key. -/
  | dummy
  deriving DecidableEq

/-- The symmetric key of a ciphertext in a mode: the KDF's answer at the shared point
`S.pt r P`, or a fresh uniform key. -/
def keyQ (S : Variant G ρ E X) : Mode → ρ → G → OracleComp (unifSpec + (X →ₒ Key)) Key
  | .real, r, P => query (spec := X →ₒ Key) (S.pt r P)
  | .fresh, _, _ => $ᵗ Key
  | .dummy, _, _ => $ᵗ Key

/-- The plaintext of a ciphertext in a mode: the note, or the dummy note. -/
def msg (P : Params F G Addr ρ E Key Note DTx WCore C Proof k n) : Mode → Note → Note
  | .dummy, _ => P.dummy
  | _, m => m

/-- The rest of the game after both ciphertexts: the proof (real or simulated) and the
adversary's guess. -/
def tailD (P : Params F G Addr ρ E Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr E X Key DTx WCore C Proof σ n) (b sim : Bool)
    (x : Ctx F G Addr Note DTx WCore σ n) (rS rR : ρ) (ctS ctR : C × E) :
    OracleComp (unifSpec + (X →ₒ Key)) Bool := do
  let π ← if sim then P.zk.sim (stmt x ctS ctR)
    else P.zk.prove (stmt x ctS ctR) (x.note b, x.sender b, rS, rR)
  finish A x ctS ctR π

/-- The rest of the game after the recipient's key. -/
def tailR (S : Variant G ρ E X) (P : Params F G Addr ρ E Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr E X Key DTx WCore C Proof σ n) (b sim : Bool) (mR : Mode)
    (x : Ctx F G Addr Note DTx WCore σ n) (rS rR : ρ) (ctS : C × E) (keyR : Key) :
    OracleComp (unifSpec + (X →ₒ Key)) Bool :=
  tailD P A b sim x rS rR ctS (P.senc keyR (msg P mR (x.note b)), S.eph rR)

/-- The rest of the game after the sender's ciphertext. -/
def tailC (S : Variant G ρ E X) (P : Params F G Addr ρ E Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr E X Key DTx WCore C Proof σ n) (b sim : Bool) (mR : Mode)
    (x : Ctx F G Addr Note DTx WCore σ n) (rS rR : ρ) (ctS : C × E) :
    OracleComp (unifSpec + (X →ₒ Key)) Bool := do
  let keyR ← keyQ S mR rR (x.pt P.pos P.coef x.c.wAddr)
  tailR S P A b sim mR x rS rR ctS keyR

/-- The rest of the game after the sender's key. -/
def tailS (S : Variant G ρ E X) (P : Params F G Addr ρ E Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr E X Key DTx WCore C Proof σ n) (b sim : Bool) (mS mR : Mode)
    (x : Ctx F G Addr Note DTx WCore σ n) (rS rR : ρ) (keyS : Key) :
    OracleComp (unifSpec + (X →ₒ Key)) Bool :=
  tailC S P A b sim mR x rS rR (P.senc keyS (msg P mS (x.note b)), S.eph rS)

/-- The rest of the game after both ciphertexts with a *simulated* proof: it does not depend on
the ephemeral randomness, which only the real prover uses. -/
def simTailD (P : Params F G Addr ρ E Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr E X Key DTx WCore C Proof σ n)
    (x : Ctx F G Addr Note DTx WCore σ n) (ctS ctR : C × E) :
    OracleComp (unifSpec + (X →ₒ Key)) Bool := do
  let π ← P.zk.sim (stmt x ctS ctR)
  finish A x ctS ctR π

omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq Addr] [SampleableType G] [Fintype Addr]
  [SampleableType Key] [SampleableType ρ] in
theorem tailD_true (P : Params F G Addr ρ E Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr E X Key DTx WCore C Proof σ n) (b : Bool)
    (x : Ctx F G Addr Note DTx WCore σ n) (rS rR : ρ) (ctS ctR : C × E) :
    tailD P A b true x rS rR ctS ctR = simTailD P A x ctS ctR := rfl

/-- The rest of the game after the sender's ciphertext with a simulated proof. -/
def simTailC (S : Variant G ρ E X) (P : Params F G Addr ρ E Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr E X Key DTx WCore C Proof σ n) (b : Bool) (mR : Mode)
    (x : Ctx F G Addr Note DTx WCore σ n) (rR : ρ) (ctS : C × E) :
    OracleComp (unifSpec + (X →ₒ Key)) Bool := do
  let keyR ← keyQ S mR rR (x.pt P.pos P.coef x.c.wAddr)
  simTailD P A x ctS (P.senc keyR (msg P mR (x.note b)), S.eph rR)

omit [DecidableEq Addr] [SampleableType G] [Fintype Addr] [SampleableType ρ] in
theorem tailC_true (S : Variant G ρ E X) (P : Params F G Addr ρ E Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr E X Key DTx WCore C Proof σ n) (b : Bool) (mR : Mode)
    (x : Ctx F G Addr Note DTx WCore σ n) (rS rR : ρ) (ctS : C × E) :
    tailC S P A b true mR x rS rR ctS = simTailC S P A b mR x rR ctS := rfl

/-- The hybrids as oracle computations: the game with a real (`sim = false`) or simulated
proof, and the ciphertexts in modes `mS`, `mR`. -/
noncomputable def gameH (S : Variant G ρ E X) (sel : Selection F Addr k n)
    (P : Params F G Addr ρ E Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr E X Key DTx WCore C Proof σ n) (b sim : Bool) (mS mR : Mode) :
    OracleComp (unifSpec + (X →ₒ Key)) Bool := do
  let H ← $ᵗ (Addr → G)
  let c ← A.choose H
  let ox ← setup sel P b H c
  match ox with
  | none => return false
  | some x => do
    let rS ← $ᵗ ρ
    let rR ← $ᵗ ρ
    let keyS ← keyQ S mS rS (x.pt P.pos P.coef (x.sender b))
    tailS S P A b sim mS mR x rS rR keyS

/-- The game is the hybrid with a real proof and two real ciphertexts. -/
theorem game_eq (S : Variant G ρ E X) (sel : Selection F Addr k n)
    (P : Params F G Addr ρ E Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr E X Key DTx WCore C Proof σ n) (b : Bool) :
    game S sel P A b = gameH S sel P A b false .real .real := rfl

/-- The outcome of a hybrid with a valid choice: the context, the ephemeral randomness of both
ciphertexts, and the final KDF cache. -/
structure Out (F G Addr ρ X Key Note DTx WCore σ : Type) (n : ℕ) where
  /-- The context of the challenge withdrawal. -/
  x : Ctx F G Addr Note DTx WCore σ n
  /-- The sender's ephemeral randomness. -/
  rS : ρ
  /-- The recipient's ephemeral randomness. -/
  rR : ρ
  /-- The KDF cache at the end of the run: the points that were queried. -/
  cache : (X →ₒ Key).QueryCache

variable [DecidableEq X]

/-- The hybrids, run phase by phase in the random oracle model from the empty cache: the
adversary's guess together with the outcome (`none` for an invalid choice). The hybrid with a
real proof and two real ciphertexts is the game (`roExec_gameH`). -/
noncomputable def hybrid (S : Variant G ρ E X) (sel : Selection F Addr k n)
    (P : Params F G Addr ρ E Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr E X Key DTx WCore C Proof σ n) (b sim : Bool) (mS mR : Mode) :
    ProbComp (Bool × Option (Out F G Addr ρ X Key Note DTx WCore σ n)) := do
  let H ← $ᵗ (Addr → G)
  let z ← roRun (A.choose H) ∅
  let ox ← setup sel P b H z.1
  match ox with
  | none => return (false, none)
  | some x => do
    let rS ← $ᵗ ρ
    let rR ← $ᵗ ρ
    let w ← roRun (keyQ S mS rS (x.pt P.pos P.coef (x.sender b))) z.2
    let v ← roRun (tailS S P A b sim mS mR x rS rR w.1) w.2
    return (v.1, some ⟨x, rS, rR, v.2⟩)

/-- A hybrid run in the random oracle model is the phase-by-phase hybrid. -/
theorem roExec_gameH (S : Variant G ρ E X) (sel : Selection F Addr k n)
    (P : Params F G Addr ρ E Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr E X Key DTx WCore C Proof σ n) (b sim : Bool) (mS mR : Mode) :
    roExec (gameH S sel P A b sim mS mR) = Prod.fst <$> hybrid S sel P A b sim mS mR := by
  simp only [roExec_eq, gameH, hybrid, roRun_bind, roRun_liftM, bind_map_left, map_bind]
  refine bind_congr fun H => bind_congr fun z => bind_congr fun ox => ?_
  cases ox with
  | none => simp
  | some x =>
    simp only [roRun_bind, roRun_liftM, bind_map_left, map_bind]
    simp only [map_eq_bind_pure_comp, Function.comp_def, pure_bind]

/-- The experiment is the hybrid with a real proof and two real ciphertexts. -/
theorem experiment_eq (S : Variant G ρ E X) (sel : Selection F Addr k n)
    (P : Params F G Addr ρ E Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr E X Key DTx WCore C Proof σ n) (b : Bool) :
    experiment S sel P A b = Prod.fst <$> hybrid S sel P A b false .real .real :=
  roExec_gameH S sel P A b false .real .real

/-! ## The query events -/

/-- The shared point of the sender's ciphertext is in the final cache: the KDF was queried at
it at some time, by the adversary or by the challenger. -/
def QueriedS (S : Variant G ρ E X) (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F)
    (b : Bool) : Option (Out F G Addr ρ X Key Note DTx WCore σ n) → Prop
  | none => False
  | some o => (o.cache (S.pt o.rS (o.x.pt pos coef (o.x.sender b)))).isSome

/-- The shared point of the recipient's ciphertext is in the final cache. -/
def QueriedR (S : Variant G ρ E X) (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F) :
    Option (Out F G Addr ρ X Key Note DTx WCore σ n) → Prop
  | none => False
  | some o => (o.cache (S.pt o.rR (o.x.pt pos coef o.x.c.wAddr))).isSome

/-- The probability that, in the hybrid with a simulated proof, the sender's note under a
*fresh* key and the recipient's ciphertext real, the shared point of the sender's ciphertext is
queried (by the adversary, or by the challenger's query for the recipient's ciphertext). -/
noncomputable def queryProbS (S : Variant G ρ E X) (sel : Selection F Addr k n)
    (P : Params F G Addr ρ E Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr E X Key DTx WCore C Proof σ n) (b : Bool) : ℝ≥0∞ :=
  Pr{let x ← hybrid S sel P A b true .fresh .real}[QueriedS S P.pos P.coef b x.2]

/-- The probability that, in the hybrid with a simulated proof, the sender's ciphertext a
dummy and the recipient's note under a *fresh* key, the shared point of the recipient's
ciphertext is queried by the adversary. -/
noncomputable def queryProbR (S : Variant G ρ E X) (sel : Selection F Addr k n)
    (P : Params F G Addr ρ E Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr E X Key DTx WCore C Proof σ n) (b : Bool) : ℝ≥0∞ :=
  Pr{let x ← hybrid S sel P A b true .dummy .fresh}[QueriedR S P.pos P.coef x.2]

/-! ## Facts about `setup` -/

omit [SampleableType G] [Fintype Addr] [SampleableType Key] [SampleableType ρ] [DecidableEq X] in
/-- A context produced by `setup` comes from a valid choice, records `H` and the choice, and
its vector is the generated one. -/
theorem setup_spec {sel : Selection F Addr k n}
    {P : Params F G Addr ρ E Key Note DTx WCore C Proof k n} {b : Bool} {H : Addr → G}
    {c : Choice F Addr σ n} {x : Ctx F G Addr Note DTx WCore σ n}
    (h : some x ∈ support (setup sel P b H c)) :
    valid sel P.pos P.coef c = true ∧ x.H = H ∧ x.c = c ∧
      x.V = auditVec P.g P.pos P.coef sel H c.req c.sk c.fill := by
  unfold setup at h
  by_cases hv : valid sel P.pos P.coef c = true
  · simp only [hv, ite_true] at h
    obtain ⟨n₀, -, h⟩ := support_bind_exists h
    obtain ⟨n₁, -, h⟩ := support_bind_exists h
    obtain ⟨core, -, h⟩ := support_bind_exists h
    simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at h
    subst h
    exact ⟨hv, rfl, rfl, rfl⟩
  · simp [hv] at h

omit [SampleableType G] [Fintype Addr] [SampleableType Key] [SampleableType ρ] [DecidableEq X] in
/-- An invalid choice gives no context. -/
theorem setup_of_not_valid {sel : Selection F Addr k n}
    {P : Params F G Addr ρ E Key Note DTx WCore C Proof k n} {b : Bool} {H : Addr → G}
    {c : Choice F Addr σ n} (hv : ¬valid sel P.pos P.coef c = true) :
    setup sel P b H c = pure none := by
  simp [setup, hv]

omit [SampleableType ρ] [DecidableEq X] [SampleableType G] [Fintype Addr] [SampleableType Key]
  [AddCommGroup G] [Module F G] in
/-- The sender of a valid choice is not a selected address. -/
theorem sender_not_mem_selected {sel : Selection F Addr k n} {pos : Addr → Fin k → Fin n}
    {coef : Addr → Fin k → F} {x : Ctx F G Addr Note DTx WCore σ n}
    (hv : valid sel pos coef x.c = true) (b : Bool) :
    x.sender b ∉ selected sel pos coef x.c := by
  have h := SLINDDrop.valid_excl hv
  cases b
  · exact h.1
  · exact h.2.1

omit [SampleableType ρ] [DecidableEq X] [SampleableType G] [Fintype Addr] [SampleableType Key]
  [AddCommGroup G] [Module F G] in
/-- The recipient of a valid choice is not a selected address. -/
theorem recipient_not_mem_selected {sel : Selection F Addr k n} {pos : Addr → Fin k → Fin n}
    {coef : Addr → Fin k → F} {x : Ctx F G Addr Note DTx WCore σ n}
    (hv : valid sel pos coef x.c = true) : x.c.wAddr ∉ selected sel pos coef x.c :=
  (SLINDDrop.valid_excl hv).2.2

/-! ## The size of the cache -/

section Cache

omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq Addr] [SampleableType G] [Fintype Addr]
  [SampleableType ρ] in
/-- A lifted step leaves the cache unchanged. -/
theorem snd_eq_of_mem_support_roRun_liftM {α : Type} {pc : ProbComp α} {c : (X →ₒ Key).QueryCache}
    {z : α × (X →ₒ Key).QueryCache}
    (hz : z ∈ support (roRun (liftM pc : OracleComp (unifSpec + (X →ₒ Key)) α) c)) : z.2 = c := by
  rw [roRun_liftM, support_map] at hz
  obtain ⟨a, -, rfl⟩ := hz
  rfl

omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq Addr] [SampleableType G] [Fintype Addr]
  [SampleableType ρ] in
/-- A single KDF query adds at most one entry to the cache. -/
theorem toSet_encard_le_of_mem_support_roRun_query {Z : X} {c : (X →ₒ Key).QueryCache}
    {z : Key × (X →ₒ Key).QueryCache}
    (hz : z ∈ support (roRun (query (spec := X →ₒ Key) Z :
      OracleComp (unifSpec + (X →ₒ Key)) Key) c)) :
    z.2.toSet.encard ≤ c.toSet.encard + 1 :=
  toSet_encard_le_of_mem_support_roRun (q := 1) (by
    rw [show (query (spec := X →ₒ Key) Z : OracleComp (unifSpec + (X →ₒ Key)) Key) =
      liftM ((unifSpec + (X →ₒ Key)).query (Sum.inr Z)) from rfl, isQueryBoundP_query_iff]
    exact fun _ => Nat.one_pos) hz

omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq Addr] [SampleableType G] [Fintype Addr]
  [SampleableType ρ] in
/-- The key of a ciphertext in any mode adds at most one entry to the cache. -/
theorem toSet_encard_le_of_mem_support_roRun_keyQ (S : Variant G ρ E X) (m : Mode) (r : ρ)
    (Q : G) {c : (X →ₒ Key).QueryCache} {z : Key × (X →ₒ Key).QueryCache}
    (hz : z ∈ support (roRun (keyQ S m r Q) c)) : z.2.toSet.encard ≤ c.toSet.encard + 1 := by
  cases m with
  | real => exact toSet_encard_le_of_mem_support_roRun_query hz
  | fresh => rw [snd_eq_of_mem_support_roRun_liftM hz]; exact le_self_add
  | dummy => rw [snd_eq_of_mem_support_roRun_liftM hz]; exact le_self_add

omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq Addr] [SampleableType G] [Fintype Addr]
  [SampleableType ρ] in
/-- A fresh key leaves the cache unchanged. -/
theorem snd_eq_of_mem_support_roRun_keyQ (S : Variant G ρ E X) {m : Mode} (hm : m ≠ .real)
    (r : ρ) (Q : G) {c : (X →ₒ Key).QueryCache} {z : Key × (X →ₒ Key).QueryCache}
    (hz : z ∈ support (roRun (keyQ S m r Q) c)) : z.2 = c := by
  cases m with
  | real => exact absurd rfl hm
  | fresh => exact snd_eq_of_mem_support_roRun_liftM hz
  | dummy => exact snd_eq_of_mem_support_roRun_liftM hz

omit [DecidableEq Addr] [SampleableType G] [Fintype Addr] [SampleableType ρ] in
/-- With a simulated proof, the rest of the game after the sender's key adds at most
`1 + q₂` entries to the cache: one for the recipient's key, `q₂` for the adversary's guess. -/
theorem toSet_encard_le_of_mem_support_roRun_tailS (S : Variant G ρ E X)
    (P : Params F G Addr ρ E Key Note DTx WCore C Proof k n)
    {A : Adversary F G Addr E X Key DTx WCore C Proof σ n} {q₁ q₂ : ℕ} (hq : A.QueryBound q₁ q₂)
    (b : Bool) (mS mR : Mode) (x : Ctx F G Addr Note DTx WCore σ n) (rS rR : ρ) (keyS : Key)
    {c : (X →ₒ Key).QueryCache} {z : Bool × (X →ₒ Key).QueryCache}
    (hz : z ∈ support (roRun (tailS S P A b true mS mR x rS rR keyS) c)) :
    z.2.toSet.encard ≤ c.toSet.encard + 1 + q₂ := by
  simp only [tailS, tailC_true, simTailC, simTailD, roRun_bind, mem_support_bind_iff] at hz
  obtain ⟨w, hw, p, hp, hz⟩ := hz
  have h1 := toSet_encard_le_of_mem_support_roRun_keyQ S mR rR _ hw
  have h2 := snd_eq_of_mem_support_roRun_liftM hp
  have h3 := toSet_encard_le_of_mem_support_roRun (hq.guess _ _ _ _ _ _ _) hz
  rw [h2] at h3
  calc z.2.toSet.encard ≤ w.2.toSet.encard + q₂ := h3
    _ ≤ c.toSet.encard + 1 + q₂ := by gcongr

/-- In a hybrid with a simulated proof and a fresh key for the sender's ciphertext, of an
adversary making at most `q₁` and `q₂` KDF queries in its two phases, the final cache holds at
most `q₁ + q₂ + 1` points: the adversary's queries and the recipient's key. -/
theorem length_cachedPoints_le_of_mem_support_hybrid [Finite X] (S : Variant G ρ E X)
    (sel : Selection F Addr k n) (P : Params F G Addr ρ E Key Note DTx WCore C Proof k n)
    {A : Adversary F G Addr E X Key DTx WCore C Proof σ n} {q₁ q₂ : ℕ} (hq : A.QueryBound q₁ q₂)
    (b : Bool) {mS : Mode} (hmS : mS ≠ .real) (mR : Mode)
    {x : Bool × Option (Out F G Addr ρ X Key Note DTx WCore σ n)}
    (hx : x ∈ support (hybrid S sel P A b true mS mR)) {o : Out F G Addr ρ X Key Note DTx WCore σ n}
    (ho : x.2 = some o) : (cachedPoints o.cache).length ≤ q₁ + q₂ + 1 := by
  simp only [hybrid, mem_support_bind_iff] at hx
  obtain ⟨H, -, z, hz, ox, -, hx⟩ := hx
  cases ox with
  | none =>
    simp only [support_pure, Set.mem_singleton_iff] at hx
    subst hx
    exact absurd ho (by simp)
  | some x' =>
    simp only [mem_support_bind_iff] at hx
    obtain ⟨rS, -, rR, -, w, hw, v, hv, hx⟩ := hx
    simp only [support_pure, Set.mem_singleton_iff] at hx
    subst hx
    simp only [Option.some.injEq] at ho
    subst ho
    have h1 := toSet_encard_le_of_mem_support_roRun (hq.choose H) hz
    have h2 := snd_eq_of_mem_support_roRun_keyQ S hmS rS _ hw
    have h3 := toSet_encard_le_of_mem_support_roRun_tailS S P hq b mS mR x' rS rR w.1 hv
    have h4 := length_cachedPoints_le v.2
    rw [QueryCache.toSet_empty, Set.encard_empty, zero_add] at h1
    rw [h2] at h3
    have : ((cachedPoints v.2).length : ℕ∞) ≤ ((q₁ + q₂ + 1 : ℕ) : ℕ∞) := by
      push_cast
      calc ((cachedPoints v.2).length : ℕ∞) ≤ v.2.toSet.encard := h4
        _ ≤ z.2.toSet.encard + 1 + q₂ := h3
        _ ≤ q₁ + 1 + q₂ := by gcongr
        _ = q₁ + q₂ + 1 := by ring
    exact_mod_cast this

end Cache

end AuditPay.SLINDRO
