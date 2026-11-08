/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.SLINDRO.Defs

/-!
# Theorem 2 with a random-oracle KDF: the zero-knowledge, one-time and base-mixer reductions

One named reduction per hybrid step that does not involve the KDF, as in
`AuditPay.SLINDDrop.Reductions`. Each runs the SL-IND adversary with a lazily sampled KDF of
its own (`KdfRO.roRun`, continuing from the cache the previous phase left) and embeds its
challenge in the component that changes between two consecutive hybrids. When the adversary's
choice is invalid, a reduction behaves like the hybrids (outputs `false`), answering its own
challenger with fixed values where it must.

The random-oracle hops (real key → fresh key) have no reduction of their own: their cost is the
probability `queryProbS`/`queryProbR` that the shared point is queried, which the option files
bound by the one-wayness game of `AuditPay.SLINDRO.OW`.
-/

open OracleComp OracleSpec ENNReal

namespace AuditPay.SLINDRO

open KdfRO
open AuditPay.SLIND (ZKAdversary OTAdversary MixerAdversary)
open AuditPay.SLINDDrop (Choice valid)

variable {F G Addr ρ E X Key Note DTx WCore C Proof σ : Type} {k n : ℕ}
  [Field F] [AddCommGroup G] [Module F G] [DecidableEq Addr]
  [SampleableType G] [Fintype Addr] [SampleableType Key] [SampleableType ρ] [DecidableEq X]

/-! ## Zero knowledge -/

/-- The state of the zero-knowledge reduction after it has submitted its statement: the
context, the ephemeral randomness, the two ciphertexts, and the KDF cache. -/
structure ZKState (F G Addr ρ E X Key Note DTx WCore C σ : Type) (n : ℕ) where
  /-- The context of the challenge withdrawal. -/
  x : Ctx F G Addr Note DTx WCore σ n
  /-- The sender's ephemeral randomness. -/
  rS : ρ
  /-- The recipient's ephemeral randomness. -/
  rR : ρ
  /-- The sender's ciphertext. -/
  ctS : C × E
  /-- The recipient's ciphertext. -/
  ctR : C × E
  /-- The KDF cache. -/
  cache : (X →ₒ Key).QueryCache

variable [Inhabited Addr] [Inhabited WCore] [Inhabited C]

/-- The reduction to zero knowledge (real → simulated proof), for bit `b`. It samples the
ephemeral randomness before the validity check, so that an invalid run can submit a fixed
statement and witness built from it. -/
noncomputable def zkReduction (S : Variant G ρ E X) (sel : Selection F Addr k n)
    (P : Params F G Addr ρ E Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr E X Key DTx WCore C Proof σ n) (b : Bool) :
    ZKAdversary (Stmt G WCore C E n) (Wit Addr Note ρ) Proof
      (Option (ZKState F G Addr ρ E X Key Note DTx WCore C σ n)) where
  choose := do
    let H ← $ᵗ (Addr → G)
    let z ← roRun (A.choose H) ∅
    let ox ← setup sel P b H z.1
    let rS ← $ᵗ ρ
    let rR ← $ᵗ ρ
    match ox with
    | none => return ((default, 0, (default, S.eph rS), (default, S.eph rR)),
        (P.dummy, default, rS, rR), none)
    | some x => do
      let w ← roRun (keyQ S .real rS (x.pt P.pos P.coef (x.sender b))) z.2
      let w' ← roRun (keyQ S .real rR (x.pt P.pos P.coef x.c.wAddr)) w.2
      let ctS := (P.senc w.1 (x.note b), S.eph rS)
      let ctR := (P.senc w'.1 (x.note b), S.eph rR)
      return (stmt x ctS ctR, (x.note b, x.sender b, rS, rR), some ⟨x, rS, rR, ctS, ctR, w'.2⟩)
  guess st π :=
    match st with
    | none => return false
    | some s => Prod.fst <$> roRun (finish A s.x s.ctS s.ctR π) s.cache

/-! ## One-time security of the cipher -/

/-- The state of the one-time reduction for the sender's ciphertext: the context, the
ephemeral randomness, and the KDF cache. -/
structure OTStateS (F G Addr ρ X Key Note DTx WCore σ : Type) (n : ℕ) where
  /-- The context of the challenge withdrawal. -/
  x : Ctx F G Addr Note DTx WCore σ n
  /-- The sender's ephemeral randomness. -/
  rS : ρ
  /-- The recipient's ephemeral randomness. -/
  rR : ρ
  /-- The KDF cache. -/
  cache : (X →ₒ Key).QueryCache

/-- The reduction to one-time security for the sender's ciphertext (note → dummy note under a
fresh key), with the recipient's ciphertext real and the proof simulated. -/
noncomputable def otReductionS (S : Variant G ρ E X) (sel : Selection F Addr k n)
    (P : Params F G Addr ρ E Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr E X Key DTx WCore C Proof σ n) (b : Bool) :
    OTAdversary Note C (Option (OTStateS F G Addr ρ X Key Note DTx WCore σ n)) where
  choose := do
    let H ← $ᵗ (Addr → G)
    let z ← roRun (A.choose H) ∅
    let ox ← setup sel P b H z.1
    match ox with
    | none => return (P.dummy, P.dummy, none)
    | some x => do
      let rS ← $ᵗ ρ
      let rR ← $ᵗ ρ
      return (x.note b, P.dummy, some ⟨x, rS, rR, z.2⟩)
  guess st ct :=
    match st with
    | none => return false
    | some s => Prod.fst <$> roRun (tailC S P A b true .real s.x s.rS s.rR (ct, S.eph s.rS)) s.cache

/-- The state of the one-time reduction for the recipient's ciphertext: the context, the
ephemeral randomness, the sender's (dummy) ciphertext, and the KDF cache. -/
structure OTStateR (F G Addr ρ E X Key Note DTx WCore C σ : Type) (n : ℕ) where
  /-- The context of the challenge withdrawal. -/
  x : Ctx F G Addr Note DTx WCore σ n
  /-- The sender's ephemeral randomness. -/
  rS : ρ
  /-- The recipient's ephemeral randomness. -/
  rR : ρ
  /-- The sender's ciphertext. -/
  ctS : C × E
  /-- The KDF cache. -/
  cache : (X →ₒ Key).QueryCache

/-- The reduction to one-time security for the recipient's ciphertext, with the sender's
ciphertext already a dummy and the proof simulated. -/
noncomputable def otReductionR (S : Variant G ρ E X) (sel : Selection F Addr k n)
    (P : Params F G Addr ρ E Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr E X Key DTx WCore C Proof σ n) (b : Bool) :
    OTAdversary Note C (Option (OTStateR F G Addr ρ E X Key Note DTx WCore C σ n)) where
  choose := do
    let H ← $ᵗ (Addr → G)
    let z ← roRun (A.choose H) ∅
    let ox ← setup sel P b H z.1
    match ox with
    | none => return (P.dummy, P.dummy, none)
    | some x => do
      let rS ← $ᵗ ρ
      let rR ← $ᵗ ρ
      let keyS ← $ᵗ Key
      return (x.note b, P.dummy, some ⟨x, rS, rR, (P.senc keyS P.dummy, S.eph rS), z.2⟩)
  guess st ct :=
    match st with
    | none => return false
    | some s => Prod.fst <$> roRun (tailD P A b true s.x s.rS s.rR s.ctS (ct, S.eph s.rR)) s.cache

/-! ## Base-mixer unlinkability -/

/-- The reduction to base-mixer unlinkability, once both ciphertexts are dummies under fresh
keys and the proof is simulated. It generates `V` itself from the adversary's choice. -/
noncomputable def mixerReduction (S : Variant G ρ E X) (sel : Selection F Addr k n)
    (P : Params F G Addr ρ E Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr E X Key DTx WCore C Proof σ n) :
    MixerAdversary Addr DTx WCore ((Addr → G) × Choice F Addr σ n × (X →ₒ Key).QueryCache) where
  choose := do
    let H ← $ᵗ (Addr → G)
    let z ← roRun (A.choose H) ∅
    return (z.1.d₀, z.1.d₁, z.1.wAddr, (H, z.1, z.2))
  guess st deps core :=
    if valid sel P.pos P.coef st.2.1 then do
      let V := auditVec P.g P.pos P.coef sel st.1 st.2.1.req st.2.1.sk st.2.1.fill
      let rS ← $ᵗ ρ
      let rR ← $ᵗ ρ
      let keyS ← $ᵗ Key
      let keyR ← $ᵗ Key
      let ctS := (P.senc keyS P.dummy, S.eph rS)
      let ctR := (P.senc keyR P.dummy, S.eph rR)
      let π ← P.zk.sim (core, V, ctS, ctR)
      Prod.fst <$> roRun (A.guess st.2.1.state V deps core ctS ctR π) st.2.2
    else return false

end AuditPay.SLINDRO
