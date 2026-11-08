/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.SLINDDrop.Defs
import AuditPay.SLIND.Reductions

/-!
# Theorem 2 (SL-IND) for the never-failing generation: the reductions

One named reduction per hybrid step, as in `AuditPay.SLIND.Reductions`. Each runs the SL-IND
adversary and embeds its challenge in the component that changes between two consecutive
hybrids. When the adversary's choice is invalid, a reduction behaves like the hybrids (outputs
`false`), answering its own challenger with fixed default values where it must.

The only reductions whose computation differs from `AuditPay.SLIND` beyond the generation of
`V` are the DDH reductions: their point `ddhPoint` expresses `RetrieveKey(V, a) − H(a)` as a
combination of `g` and `Y` through the right inverse `R` of the selected set's encoding matrix
and the fill scalars.
-/

open OracleComp DiffieHellman ENNReal

namespace AuditPay.SLINDDrop

open AuditPay.SLIND (Params Mode slot Stmt Wit NIZK ZKAdversary OTAdversary MixerAdversary
  defaultStmt)

variable {F G Addr HK Key Note DTx WCore C Proof σ : Type} {k n : ℕ}
  [Field F] [Fintype F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G]
  [Fintype Addr] [DecidableEq Addr] [SampleableType HK] [SampleableType Key]
  [Inhabited Addr] [Inhabited WCore] [Inhabited C]

/-! ## Zero knowledge -/

/-- The reduction to zero knowledge (real → simulated proof), for bit `b`. -/
noncomputable def zkReduction (sel : Selection F Addr k n)
    (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) :
    ZKAdversary (Stmt G WCore C n) (Wit F Addr Note) Proof
      (Option (Ctx F G Addr HK Note DTx WCore σ n × (C × G) × (C × G))) where
  choose := do
    let hk ← $ᵗ HK
    let H ← $ᵗ (Addr → G)
    let ox ← setup sel P A b hk H
    match ox with
    | none => return (defaultStmt, (P.dummy, default, 0, 0), none)
    | some x => do
      let rS ← $ᵗ F
      let rR ← $ᵗ F
      let ctS ← slot P .real rS hk H x.V (x.sender b) (x.note b)
      let ctR ← slot P .real rR hk H x.V x.c.wAddr (x.note b)
      return (stmt x ctS ctR, (x.note b, x.sender b, rS, rR), some (x, ctS, ctR))
  guess st π :=
    match st with
    | none => return false
    | some s => finish A s.1 s.2.1 s.2.2 π

/-! ## DDH -/

/-- Coefficients of the selected audit keys in `RetrieveKey(V, a)`: `λ = row_a ᵥ* R`, where `R`
is the right inverse of the encoding matrix of the selected set. -/
noncomputable def keyCoeffs (sel : Selection F Addr k n)
    (P : Params F G Addr HK Key Note DTx WCore C Proof k n) (c : Choice F Addr σ n)
    (a : Addr) : selected sel P.pos P.coef c → F :=
  Matrix.vecMul (coefRow P.pos P.coef a)
    (rightInv (setMatrix P.pos P.coef (selected sel P.pos P.coef c)))

/-- The Diffie–Hellman point the reduction derives from a DDH challenge `(X, Z)` for the
address `a`, when the oracle is programmed as `H(z) = u_z • g + t_z • Y` and the fill is
`ρ = w • g`: `α • X + β • Z` with `RetrieveKey(V, a) − H(a) = α • g + β • Y`, where
`α = row_a · w + ∑_{z ∈ T} λ_z (sk_z + u_z − (M w)_z) − u_a` and `β = ∑_{z ∈ T} λ_z t_z − t_a`. -/
noncomputable def ddhPoint (sel : Selection F Addr k n)
    (P : Params F G Addr HK Key Note DTx WCore C Proof k n) (c : Choice F Addr σ n)
    (u t : Addr → F) (a : Addr) (X Z : G) : G :=
  (dotProduct (coefRow P.pos P.coef a) c.fill +
      ∑ z, keyCoeffs sel P c a z * (c.sk z + u z -
        Matrix.mulVec (setMatrix P.pos P.coef (selected sel P.pos P.coef c)) c.fill z) -
      u a) • X +
    (∑ z, keyCoeffs sel P c a z * t z - t a) • Z

/-- The reduction to DDH for the sender's ciphertext (real → uniform DH point), for bit `b`,
with the recipient's ciphertext real and the proof simulated. -/
noncomputable def ddhReductionS (sel : Selection F Addr k n)
    (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) : DDHAdversary F G :=
  fun _ X Y Z => do
    let hk ← $ᵗ HK
    let u ← $ᵗ (Addr → F)
    let t ← $ᵗ (Addr → F)
    let H : Addr → G := fun x => u x • P.g + t x • Y
    let ox ← setup sel P A b hk H
    match ox with
    | none => return false
    | some x => do
      let rR ← $ᵗ F
      let ctS := (P.senc (P.kdf hk (ddhPoint sel P x.c u t (x.sender b) X Z)) (x.note b), X)
      let ctR ← slot P .real rR hk H x.V x.c.wAddr (x.note b)
      let π ← P.zk.sim (stmt x ctS ctR)
      finish A x ctS ctR π

/-- The reduction to DDH for the recipient's ciphertext, for bit `b`, with the sender's
ciphertext already a dummy and the proof simulated. -/
noncomputable def ddhReductionR (sel : Selection F Addr k n)
    (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) : DDHAdversary F G :=
  fun _ X Y Z => do
    let hk ← $ᵗ HK
    let u ← $ᵗ (Addr → F)
    let t ← $ᵗ (Addr → F)
    let H : Addr → G := fun x => u x • P.g + t x • Y
    let ox ← setup sel P A b hk H
    match ox with
    | none => return false
    | some x => do
      let rS ← $ᵗ F
      let ctS ← slot P .dummy rS hk H x.V (x.sender b) (x.note b)
      let ctR := (P.senc (P.kdf hk (ddhPoint sel P x.c u t x.c.wAddr X Z)) (x.note b), X)
      let π ← P.zk.sim (stmt x ctS ctR)
      finish A x ctS ctR π

/-! ## Entropy smoothing -/

/-- The reduction to entropy smoothing for the sender's ciphertext (DH point → uniform key). -/
noncomputable def esReductionS (sel : Selection F Addr k n)
    (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) : HK × Key → ProbComp Bool :=
  fun hh => do
    let H ← $ᵗ (Addr → G)
    let ox ← setup sel P A b hh.1 H
    match ox with
    | none => return false
    | some x => do
      let rS ← $ᵗ F
      let rR ← $ᵗ F
      let ctS := (P.senc hh.2 (x.note b), rS • P.g)
      let ctR ← slot P .real rR hh.1 H x.V x.c.wAddr (x.note b)
      let π ← P.zk.sim (stmt x ctS ctR)
      finish A x ctS ctR π

/-- The reduction to entropy smoothing for the recipient's ciphertext. -/
noncomputable def esReductionR (sel : Selection F Addr k n)
    (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) : HK × Key → ProbComp Bool :=
  fun hh => do
    let H ← $ᵗ (Addr → G)
    let ox ← setup sel P A b hh.1 H
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
noncomputable def otReductionS (sel : Selection F Addr k n)
    (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) :
    OTAdversary Note C
      (Option (HK × (Addr → G) × Ctx F G Addr HK Note DTx WCore σ n × F × F)) where
  choose := do
    let hk ← $ᵗ HK
    let H ← $ᵗ (Addr → G)
    let ox ← setup sel P A b hk H
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
      let ctR ← slot P .real s.2.2.2.2 s.1 s.2.1 s.2.2.1.V s.2.2.1.c.wAddr (s.2.2.1.note b)
      let π ← P.zk.sim (stmt s.2.2.1 ctS ctR)
      finish A s.2.2.1 ctS ctR π

/-- The reduction to one-time security for the recipient's ciphertext. -/
noncomputable def otReductionR (sel : Selection F Addr k n)
    (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) :
    OTAdversary Note C (Option (Ctx F G Addr HK Note DTx WCore σ n × F × (C × G))) where
  choose := do
    let hk ← $ᵗ HK
    let H ← $ᵗ (Addr → G)
    let ox ← setup sel P A b hk H
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
is simulated. It generates `V` itself from the adversary's choice. -/
noncomputable def mixerReduction (sel : Selection F Addr k n)
    (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) :
    MixerAdversary Addr DTx WCore (HK × (Addr → G) × Choice F Addr σ n) where
  choose := do
    let hk ← $ᵗ HK
    let H ← $ᵗ (Addr → G)
    let c ← A.choose hk H
    return (c.d₀, c.d₁, c.wAddr, (hk, H, c))
  guess st deps core :=
    if valid sel P.pos P.coef st.2.2 then do
      let rS ← $ᵗ F
      let rR ← $ᵗ F
      let ctS ← slot P .dummy rS st.1 st.2.1 (auditVec sel P st.2.1 st.2.2) st.2.2.d₀ P.dummy
      let ctR ← slot P .dummy rR st.1 st.2.1 (auditVec sel P st.2.1 st.2.2) st.2.2.wAddr
        P.dummy
      let π ← P.zk.sim (core, auditVec sel P st.2.1 st.2.2, ctS, ctR)
      A.guess st.2.2.state (auditVec sel P st.2.1 st.2.2) deps core ctS ctR π
    else return false

end AuditPay.SLINDDrop
