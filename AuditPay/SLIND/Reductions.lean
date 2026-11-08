/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.SLIND.Defs

/-!
# Theorem 2 (SL-IND): the reductions

One named reduction per hybrid step. Each runs the SL-IND adversary and embeds its challenge in
the component that changes between two consecutive hybrids. When the adversary's choice is
invalid or `V` cannot be generated, a reduction behaves like the hybrids (outputs `false`),
answering its own challenger with fixed default values where it must.
-/

open OracleComp DiffieHellman ENNReal

namespace AuditPay.SLIND

variable {F G Addr HK Key Note DTx WCore C Proof σ : Type} {k n : ℕ}
  [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G]
  [Fintype Addr] [DecidableEq Addr] [SampleableType HK] [SampleableType Key]
  [Inhabited Addr] [Inhabited WCore] [Inhabited C]

/-- A fixed default statement, used by reductions in an invalid run. -/
def defaultStmt : Stmt G WCore C n := (default, 0, (default, 0), (default, 0))

/-! ## Zero knowledge -/

/-- The reduction to zero knowledge (real → simulated proof), for bit `b`. -/
noncomputable def zkReduction (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) :
    ZKAdversary (Stmt G WCore C n) (Wit F Addr Note) Proof
      (Option (Ctx F G Addr HK Note DTx WCore σ n × (C × G) × (C × G))) where
  choose := do
    let hk ← $ᵗ HK
    let H ← $ᵗ (Addr → G)
    let ox ← setup P A b hk H
    match ox with
    | none => return (defaultStmt, (P.dummy, default, 0, 0), none)
    | some x => do
      let rS ← $ᵗ F
      let rR ← $ᵗ F
      let ctS ← slot P .real rS hk H x.V (x.sender b) (x.note b)
      let ctR ← slot P .real rR hk H x.V x.c.2.2.2.2.1 (x.note b)
      return (stmt x ctS ctR, (x.note b, x.sender b, rS, rR), some (x, ctS, ctR))
  guess st π :=
    match st with
    | none => return false
    | some s => finish A s.1 s.2.1 s.2.2 π

/-! ## DDH -/

/-- Coefficients expressing `RetrieveKey(V, a)` as a combination of the monitored audit keys:
`RetrieveKey(V, a) = ∑ᵢ λᵢ • AKᵢ` when `V = M⁻¹ ⋆ AK`. -/
noncomputable def keyCoeffs (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (rows : Fin n → Addr) (a : Addr) : Fin n → F :=
  Matrix.vecMul (coefRow P.pos P.coef a) (coefMatrix P.pos P.coef rows)⁻¹

/-- The Diffie–Hellman point the reduction derives from a DDH challenge `(X, Z)` for
the address `a`, when the oracle is programmed as `H(x) = u_x • g + t_x • Y`:
`α • X + β • Z` with `RetrieveKey(V, a) - H(a) = α • g + β • Y`. -/
noncomputable def ddhPoint (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (c : Choice F Addr σ n) (u t : Addr → F) (a : Addr) (X Z : G) : G :=
  (∑ i, keyCoeffs P c.1 a i * (c.2.1 i + u (c.1 i)) - u a) • X +
    (∑ i, keyCoeffs P c.1 a i * t (c.1 i) - t a) • Z

/-- The reduction to DDH for the sender's ciphertext (real → uniform DH point), for bit `b`,
with the recipient's ciphertext real and the proof simulated. -/
noncomputable def ddhReductionS (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) : DDHAdversary F G :=
  fun _ X Y Z => do
    let hk ← $ᵗ HK
    let u ← $ᵗ (Addr → F)
    let t ← $ᵗ (Addr → F)
    let H : Addr → G := fun x => u x • P.g + t x • Y
    let ox ← setup P A b hk H
    match ox with
    | none => return false
    | some x => do
      let rR ← $ᵗ F
      let ctS := (P.senc (P.kdf hk (ddhPoint P x.c u t (x.sender b) X Z)) (x.note b), X)
      let ctR ← slot P .real rR hk H x.V x.c.2.2.2.2.1 (x.note b)
      let π ← P.zk.sim (stmt x ctS ctR)
      finish A x ctS ctR π

/-- The reduction to DDH for the recipient's ciphertext, for bit `b`, with the sender's
ciphertext already a dummy and the proof simulated. -/
noncomputable def ddhReductionR (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) : DDHAdversary F G :=
  fun _ X Y Z => do
    let hk ← $ᵗ HK
    let u ← $ᵗ (Addr → F)
    let t ← $ᵗ (Addr → F)
    let H : Addr → G := fun x => u x • P.g + t x • Y
    let ox ← setup P A b hk H
    match ox with
    | none => return false
    | some x => do
      let rS ← $ᵗ F
      let ctS ← slot P .dummy rS hk H x.V (x.sender b) (x.note b)
      let ctR := (P.senc (P.kdf hk (ddhPoint P x.c u t x.c.2.2.2.2.1 X Z)) (x.note b), X)
      let π ← P.zk.sim (stmt x ctS ctR)
      finish A x ctS ctR π

/-! ## Entropy smoothing -/

/-- The reduction to entropy smoothing for the sender's ciphertext (DH point → uniform key). -/
noncomputable def esReductionS (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) : HK × Key → ProbComp Bool :=
  fun hh => do
    let H ← $ᵗ (Addr → G)
    let ox ← setup P A b hh.1 H
    match ox with
    | none => return false
    | some x => do
      let rS ← $ᵗ F
      let rR ← $ᵗ F
      let ctS := (P.senc hh.2 (x.note b), rS • P.g)
      let ctR ← slot P .real rR hh.1 H x.V x.c.2.2.2.2.1 (x.note b)
      let π ← P.zk.sim (stmt x ctS ctR)
      finish A x ctS ctR π

/-- The reduction to entropy smoothing for the recipient's ciphertext. -/
noncomputable def esReductionR (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) : HK × Key → ProbComp Bool :=
  fun hh => do
    let H ← $ᵗ (Addr → G)
    let ox ← setup P A b hh.1 H
    match ox with
    | none => return false
    | some x => do
      let rS ← $ᵗ F
      let rR ← $ᵗ F
      let ctS ← slot P .dummy rS hh.1 H x.V (x.sender b) (x.note b)
      let ctR := (P.senc hh.2 (x.note b), rR • P.g)
      let π ← P.zk.sim (stmt x ctS ctR)
      finish A x ctS ctR π

/-! ## One-time security of the cipher -/

/-- The reduction to one-time security for the sender's ciphertext (note → dummy note). -/
noncomputable def otReductionS (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) :
    OTAdversary Note C
      (Option (HK × (Addr → G) × Ctx F G Addr HK Note DTx WCore σ n × F × F)) where
  choose := do
    let hk ← $ᵗ HK
    let H ← $ᵗ (Addr → G)
    let ox ← setup P A b hk H
    match ox with
    | none => return (P.dummy, P.dummy, none)
    | some x => do
      let rS ← $ᵗ F
      let rR ← $ᵗ F
      return (x.note b, P.dummy, some (hk, H, x, rS, rR))
  guess st ct :=
    match st with
    | none => return false
    | some s => do
      let ctS := (ct, s.2.2.2.1 • P.g)
      let ctR ← slot P .real s.2.2.2.2 s.1 s.2.1 s.2.2.1.V s.2.2.1.c.2.2.2.2.1 (s.2.2.1.note b)
      let π ← P.zk.sim (stmt s.2.2.1 ctS ctR)
      finish A s.2.2.1 ctS ctR π

/-- The reduction to one-time security for the recipient's ciphertext. -/
noncomputable def otReductionR (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) :
    OTAdversary Note C (Option (Ctx F G Addr HK Note DTx WCore σ n × F × (C × G))) where
  choose := do
    let hk ← $ᵗ HK
    let H ← $ᵗ (Addr → G)
    let ox ← setup P A b hk H
    match ox with
    | none => return (P.dummy, P.dummy, none)
    | some x => do
      let rS ← $ᵗ F
      let rR ← $ᵗ F
      let ctS ← slot P .dummy rS hk H x.V (x.sender b) (x.note b)
      return (x.note b, P.dummy, some (x, rR, ctS))
  guess st ct :=
    match st with
    | none => return false
    | some s => do
      let ctR := (ct, s.2.1 • P.g)
      let π ← P.zk.sim (stmt s.1 s.2.2 ctR)
      finish A s.1 s.2.2 ctR π

/-! ## Base-mixer unlinkability -/

/-- The reduction to base-mixer unlinkability, once both ciphertexts are dummies and the proof
is simulated. -/
noncomputable def mixerReduction (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) :
    MixerAdversary Addr DTx WCore (HK × (Addr → G) × Choice F Addr σ n) where
  choose := do
    let hk ← $ᵗ HK
    let H ← $ᵗ (Addr → G)
    let c ← A.choose hk H
    return (c.2.2.1, c.2.2.2.1, c.2.2.2.2.1, (hk, H, c))
  guess st deps core :=
    if valid st.2.2 then
      match auditKeyVecGen P.g st.2.1 P.pos P.coef st.2.2.1 st.2.2.2.1 with
      | none => return false
      | some V => do
        let rS ← $ᵗ F
        let rR ← $ᵗ F
        let ctS ← slot P .dummy rS st.1 st.2.1 V st.2.2.2.2.1 P.dummy
        let ctR ← slot P .dummy rR st.1 st.2.1 V st.2.2.2.2.2.2.1 P.dummy
        let π ← P.zk.sim (core, V, ctS, ctR)
        A.guess st.2.2.2.2.2.2.2 V deps core ctS ctR π
    else return false

end AuditPay.SLIND
