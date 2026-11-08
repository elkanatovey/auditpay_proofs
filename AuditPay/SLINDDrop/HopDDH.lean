/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.SLINDDrop.Reductions
import AuditPay.SLIND.HopDDH

/-!
# Theorem 2 for the never-failing generation, DDH hops: real DH point → uniform group element

This is the only step whose argument differs from `AuditPay.SLIND.HopDDH`. With the oracle
programmed as `H(z) = u_z • g + t_z • Y` and the fill `ρ = w • g`, every entry of
`V = ρ + R ⋆ (AK − M ⋆ ρ)` is a known combination of `g` and `Y`:

  `V_j = (w_j + ∑_{z ∈ T} R_{j z} (sk_z + u_z − (M w)_z)) • g + (∑_{z ∈ T} R_{j z} t_z) • Y`

(`auditVec_programmed`). Hence, for any address `a`, `RetrieveKey(V, a) − H(a) = α • g + β • Y`
with `β = ∑_{z ∈ T} λ_z t_z − t_a` and `λ = row_a ᵥ* R` (`retrieveKey_programmed`). If `a` is not
selected, `t_a` does not occur in the sum, so `β = 0` only with probability `1/|F|` over the
fresh `t_a` (`prob_beta_le_finset`), exactly as in the original proof where `a` is outside the
padded set. The identity holds for every matrix `R`; that `R` is a right inverse is not needed
here.
-/

open OracleComp DiffieHellman ENNReal

namespace AuditPay.SLINDDrop

open AuditPay.SLIND (Params Mode slot)

variable {F G Addr HK Key Note DTx WCore C Proof σ : Type} {k n : ℕ}
  [Field F] [Fintype F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G]
  [Fintype Addr] [DecidableEq Addr] [SampleableType HK] [SampleableType Key]
  [Inhabited Addr] [Inhabited WCore] [Inhabited C]

/-! ## The algebra of the programmed vector -/

section Algebra

omit [Fintype F] [SampleableType F] [SampleableType G] [Fintype Addr] [SampleableType HK]
  [SampleableType Key] [Inhabited Addr] [Inhabited WCore] [Inhabited C] [DecidableEq Addr]

/-- A matrix acting on a vector of combinations of `g` and `Y` acts on the coefficients. -/
theorem matVecG_smul_add {ι κ : Type} [Fintype κ] (M : Matrix ι κ F) (g Y : G)
    (p q : κ → F) :
    matVecG M (fun j => p j • g + q j • Y) =
      fun i => Matrix.mulVec M p i • g + Matrix.mulVec M q i • Y := by
  funext i
  simp only [matVecG, Matrix.mulVec, dotProduct, smul_add, Finset.sum_add_distrib,
    Finset.sum_smul, smul_smul]

/-- A matrix acting on a vector of multiples of `g` acts on the scalars. -/
theorem matVecG_smul {ι κ : Type} [Fintype κ] (M : Matrix ι κ F) (g : G) (p : κ → F) :
    matVecG M (fun j => p j • g) = fun i => Matrix.mulVec M p i • g := by
  funext i
  simp only [matVecG, Matrix.mulVec, dotProduct, Finset.sum_smul, smul_smul]

/-- A linear combination of combinations of `g` and `Y`. -/
theorem sum_smul_smul_add {κ : Type} [Fintype κ] (r p q : κ → F) (g Y : G) :
    ∑ j, r j • (p j • g + q j • Y) = dotProduct r p • g + dotProduct r q • Y := by
  simp only [dotProduct, smul_add, Finset.sum_add_distrib, Finset.sum_smul, smul_smul]

end Algebra

section Programmed

omit [Fintype F] [SampleableType F] [SampleableType G] [Fintype Addr] [SampleableType HK]
  [SampleableType Key] [Inhabited Addr] [Inhabited WCore] [Inhabited C]

/-- The vector for the programmed oracle `H(z) = u_z • g + t_z • Y` and the fill `w • g`:
`V_j = (w_j + (R *ᵥ d)_j) • g + (R *ᵥ t|_T)_j • Y` with `d_z = sk_z + u_z − (M *ᵥ w)_z`. -/
theorem auditVec_programmed (sel : Selection F Addr k n)
    (P : Params F G Addr HK Key Note DTx WCore C Proof k n) (c : Choice F Addr σ n)
    (u t : Addr → F) (Y : G) :
    auditVec sel P (fun z => u z • P.g + t z • Y) c = fun j =>
      (c.fill + Matrix.mulVec (rightInv (setMatrix P.pos P.coef (selected sel P.pos P.coef c)))
        (fun z => c.sk z + u z -
          Matrix.mulVec (setMatrix P.pos P.coef (selected sel P.pos P.coef c)) c.fill z)) j • P.g +
      Matrix.mulVec (rightInv (setMatrix P.pos P.coef (selected sel P.pos P.coef c)))
        (fun z => t z) j • Y := by
  set T := selected sel P.pos P.coef c
  set M := setMatrix P.pos P.coef T
  set R := rightInv M
  have h1 : setAuditKeys P.g (fun z => u z • P.g + t z • Y) T (fun a => c.sk a) -
      matVecG M (fun j => c.fill j • P.g) =
      fun z : T => (c.sk z + u z - Matrix.mulVec M c.fill z) • P.g + t z • Y := by
    rw [matVecG_smul]
    funext z
    simp only [setAuditKeys, auditKey, Pi.sub_apply]
    module
  simp only [auditVec, encodeSet, rectSolve]
  rw [h1, matVecG_smul_add]
  funext j
  simp only [Pi.add_apply]
  module

/-- `RetrieveKey(V, a)` for the programmed oracle and the fill `w • g`:
`(row_a · w + ∑_{z ∈ T} λ_z d_z) • g + (∑_{z ∈ T} λ_z t_z) • Y`, with `λ = keyCoeffs`. -/
theorem retrieveKey_programmed (sel : Selection F Addr k n)
    (P : Params F G Addr HK Key Note DTx WCore C Proof k n) (c : Choice F Addr σ n)
    (u t : Addr → F) (Y : G) (a : Addr) :
    retrieveKey P.pos P.coef (auditVec sel P (fun z => u z • P.g + t z • Y) c) a =
      (dotProduct (coefRow P.pos P.coef a) c.fill +
          ∑ z, keyCoeffs sel P c a z * (c.sk z + u z -
            Matrix.mulVec (setMatrix P.pos P.coef (selected sel P.pos P.coef c)) c.fill z)) •
        P.g +
      (∑ z, keyCoeffs sel P c a z * t z) • Y := by
  rw [retrieveKey_eq_sum_coefRow, auditVec_programmed, sum_smul_smul_add, dotProduct_add,
    Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec]
  rfl

/-- On a real DDH tuple `(r • g, y • g, (r * y) • g)`, the reduction's point is the true
shared point of the selective encryption. -/
theorem ddhPoint_real {sel : Selection F Addr k n}
    {P : Params F G Addr HK Key Note DTx WCore C Proof k n} {c : Choice F Addr σ n}
    {u t : Addr → F} {y r : F} {V : Fin n → G}
    (hV : auditVec sel P (fun z => u z • P.g + t z • (y • P.g)) c = V) (a : Addr) :
    ddhPoint sel P c u t a (r • P.g) ((r * y) • P.g) =
      encPoint r (retrieveKey P.pos P.coef V a) (u a • P.g + t a • (y • P.g)) := by
  subst hV
  rw [retrieveKey_programmed]
  simp only [ddhPoint, encPoint]
  module

end Programmed

omit [Inhabited Addr] in
/-- For an address outside a finite set `T`, the coefficient `∑_{z ∈ T} λ_z t_z − t_a`
vanishes with probability at most `1/|F|` over a uniform `t`. -/
theorem prob_beta_le_finset (T : Finset Addr) (lam : T → F) {a : Addr} (ha : a ∉ T) :
    Pr{let t ← $ᵗ (Addr → F)}[∑ z, lam z * t z - t a = 0] ≤ (Fintype.card F : ℝ≥0∞)⁻¹ := by
  let e := T.equivFin
  let rows : Fin T.card ↪ Addr := e.symm.toEmbedding.trans (Function.Embedding.subtype _)
  have key : ∀ t : Addr → F, (∑ z, lam z * t z - t a = 0) ↔
      (∑ i, lam (e.symm i) * t (rows i) - t a = 0) := by
    intro t
    have hs : ∑ z, lam z * t z = ∑ i, lam (e.symm i) * t (rows i) :=
      (e.symm.sum_comp fun z => lam z * t z).symm
    rw [hs]
  rw [prEvent_congr _ _ _ key]
  refine SLIND.prob_beta_le rows _ ?_
  rintro ⟨i, hi⟩
  exact ha (hi ▸ (e.symm i).2)

/-! ## Facts about `setup` -/

omit [Fintype F] [SampleableType F] [SampleableType G] [Fintype Addr] [SampleableType HK]
  [SampleableType Key] [Inhabited Addr] [Inhabited WCore] [Inhabited C] in
/-- A context produced by `setup` comes from a valid choice, and its vector is the generated
one. -/
theorem setup_spec {sel : Selection F Addr k n}
    {P : Params F G Addr HK Key Note DTx WCore C Proof k n}
    {A : Adversary F G Addr HK DTx WCore C Proof σ n} {b : Bool} {hk : HK} {H : Addr → G}
    {x : Ctx F G Addr HK Note DTx WCore σ n} (h : some x ∈ support (setup sel P A b hk H)) :
    valid sel P.pos P.coef x.c = true ∧ auditVec sel P H x.c = x.V := by
  unfold setup at h
  obtain ⟨c, -, hc⟩ := support_bind_exists h
  by_cases hv : valid sel P.pos P.coef c = true
  · simp only [hv, ite_true] at hc
    obtain ⟨n₀, -, hc⟩ := support_bind_exists hc
    obtain ⟨n₁, -, hc⟩ := support_bind_exists hc
    obtain ⟨core, -, hc⟩ := support_bind_exists hc
    simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at hc
    subst hc
    exact ⟨hv, rfl⟩
  · simp [hv] at hc

omit [Fintype F] [SampleableType F] [SampleableType G] [Fintype Addr] [SampleableType HK]
  [SampleableType Key] [Inhabited Addr] [Inhabited WCore] [Inhabited C]
  [AddCommGroup G] [Module F G] in
/-- The sender of a valid choice is not a selected address. -/
theorem sender_not_mem_selected {sel : Selection F Addr k n} {pos : Addr → Fin k → Fin n}
    {coef : Addr → Fin k → F} {x : Ctx F G Addr HK Note DTx WCore σ n}
    (hv : valid sel pos coef x.c = true) (b : Bool) :
    x.sender b ∉ selected sel pos coef x.c := by
  have h := valid_excl hv
  cases b
  · exact h.1
  · exact h.2.1

omit [Fintype F] [SampleableType F] [SampleableType G] [Fintype Addr] [SampleableType HK]
  [SampleableType Key] [Inhabited Addr] [Inhabited WCore] [Inhabited C]
  [AddCommGroup G] [Module F G] in
/-- The recipient of a valid choice is not a selected address. -/
theorem recipient_not_mem_selected {sel : Selection F Addr k n} {pos : Addr → Fin k → Fin n}
    {coef : Addr → Fin k → F} {x : Ctx F G Addr HK Note DTx WCore σ n}
    (hv : valid sel pos coef x.c = true) : x.c.wAddr ∉ selected sel pos coef x.c :=
  (valid_excl hv).2.2

/-! ## Sender's ciphertext: the real branch -/

/-- The reduction's run on a real DDH tuple `(r • g, ·, ·)`, after rewriting its key as the true
shared point: it depends on the programmed oracle only through `H`. -/
noncomputable def realBodyS (sel : Selection F Addr k n)
    (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) (r : F) (hk : HK)
    (H : Addr → G) : ProbComp Bool := do
  let ox ← setup sel P A b hk H
  match ox with
  | none => return false
  | some x => do
    let rR ← $ᵗ F
    let ctS := (P.senc (P.kdf hk (encPoint r (retrieveKey P.pos P.coef x.V (x.sender b))
      (H (x.sender b)))) (x.note b), r • P.g)
    let ctR ← slot P .real rR hk H x.V x.c.wAddr (x.note b)
    let π ← P.zk.sim (stmt x ctS ctR)
    finish A x ctS ctR π

omit [Fintype F] [Inhabited Addr] [Inhabited WCore] [Inhabited C] in
/-- The DDH reduction for the sender's ciphertext, run on a real tuple, is the hybrid with the
real ciphertext (and simulated proof). -/
theorem ddhRealS_eqd (sel : Selection F Addr k n)
    {P : Params F G Addr HK Key Note DTx WCore C Proof k n}
    (hg : Function.Bijective (· • P.g : F → G))
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) :
    ddhRealExperiment P.g (ddhReductionS sel P A b) =ᵈ hybrid sel P A b true .real .real := by
  -- 1. rewrite the reduction's key as the true shared point
  have h1 : ddhRealExperiment P.g (ddhReductionS sel P A b) =ᵈ (do
      let x ← $ᵗ F; let y ← $ᵗ F; let hk ← $ᵗ HK; let u ← $ᵗ (Addr → F)
      let t ← $ᵗ (Addr → F)
      realBodyS sel P A b x hk fun z => u z • P.g + t z • (y • P.g)) := by
    simp only [ddhRealExperiment, ddhReductionS, realBodyS]
    refine EvalDistEq.bind_right _ fun x => EvalDistEq.bind_right _ fun y =>
      EvalDistEq.bind_right _ fun hk => EvalDistEq.bind_right _ fun u =>
        EvalDistEq.bind_right _ fun t => ?_
    refine OracleComp.EvalDistEq.bind_congr_of_support _ fun ox hox => ?_
    cases ox with
    | none => exact .rfl
    | some c =>
      have hV := (setup_spec hox).2
      simp only [ddhPoint_real hV]
      exact .rfl
  refine h1.trans ?_
  -- 2. move `hk` to the front
  refine EvalDistEq.trans (my := do
      let hk ← $ᵗ HK; let x ← $ᵗ F; let y ← $ᵗ F; let u ← $ᵗ (Addr → F)
      let t ← $ᵗ (Addr → F)
      realBodyS sel P A b x hk fun z => u z • P.g + t z • (y • P.g)) ?_ ?_
  · refine (EvalDistEq.bind_right _ fun x => bind_swap_eqd _ _ _).trans ?_
    exact bind_swap_eqd _ _ _
  refine EvalDistEq.bind_right _ fun hk => ?_
  -- 3. the programmed oracle is a uniform `H`
  refine (IndKey.reprogram hg fun x H => realBodyS sel P A b x hk H).trans ?_
  refine EvalDistEq.bind_right _ fun H => ?_
  -- 4. sample the ephemeral scalar after `setup`, as `rS`
  simp only [realBodyS]
  refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun ox => ?_)
  cases ox with
  | none => exact bind_const_eqd _ _
  | some x =>
    simp only [slot, pure_bind, ite_true]
    exact .rfl

/-! ## Sender's ciphertext: the random branch -/

/-- The reduction's run after the challenge context, with sender key point `K`. -/
noncomputable def keyedBodyS (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) (X : G) (hk : HK)
    (H : Addr → G) (x : Ctx F G Addr HK Note DTx WCore σ n) (rR : F) (K : G) :
    ProbComp Bool := do
  let ctS := (P.senc (P.kdf hk K) (x.note b), X)
  let ctR ← slot P .real rR hk H x.V x.c.wAddr (x.note b)
  let π ← P.zk.sim (stmt x ctS ctR)
  finish A x ctS ctR π

/-- The reduction's state before the DDH value `Z` is used: `(x, y, hk, u, t, setup result)`. -/
abbrev DPre (F G Addr HK Note DTx WCore σ : Type) (n : ℕ) :=
  F × F × HK × (Addr → F) × (Addr → F) × Option (Ctx F G Addr HK Note DTx WCore σ n)

/-- The programmed oracle of a reduction state. -/
def DPre.oracle (g : G) (w : DPre F G Addr HK Note DTx WCore σ n) : Addr → G :=
  fun q => w.2.2.2.1 q • g + w.2.2.2.2.1 q • (w.2.1 • g)

/-- The reduction's run up to `setup`. -/
noncomputable def prefixS (sel : Selection F Addr k n)
    (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) :
    ProbComp (DPre F G Addr HK Note DTx WCore σ n) := do
  let x ← $ᵗ F
  let y ← $ᵗ F
  let hk ← $ᵗ HK
  let u ← $ᵗ (Addr → F)
  let t ← $ᵗ (Addr → F)
  let ox ← setup sel P A b hk fun q => u q • P.g + t q • (y • P.g)
  return (x, y, hk, u, t, ox)

/-- The rest of the reduction's run on a random tuple `Z = z • g`, with `z` sampled last. -/
noncomputable def contRealS (sel : Selection F Addr k n)
    (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool)
    (w : DPre F G Addr HK Note DTx WCore σ n) : ProbComp Bool :=
  match w.2.2.2.2.2 with
  | none => return false
  | some c => do
    let rR ← $ᵗ F
    let z ← $ᵗ F
    keyedBodyS P A b (w.1 • P.g) w.2.2.1 (w.oracle P.g) c rR
      (ddhPoint sel P c.c w.2.2.2.1 w.2.2.2.2.1 (c.sender b) (w.1 • P.g) (z • P.g))

/-- The ideal counterpart of `contRealS`: a uniform sender key point. -/
noncomputable def contIdealS (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool)
    (w : DPre F G Addr HK Note DTx WCore σ n) : ProbComp Bool :=
  match w.2.2.2.2.2 with
  | none => return false
  | some c => do
    let rR ← $ᵗ F
    let K ← $ᵗ G
    keyedBodyS P A b (w.1 • P.g) w.2.2.1 (w.oracle P.g) c rR K

/-- The coefficient of `Y` in the sender's point: `∑_{z ∈ T} λ_z t_z − t_sender`. -/
noncomputable def betaS (sel : Selection F Addr k n)
    (P : Params F G Addr HK Key Note DTx WCore C Proof k n) (b : Bool)
    (c : Ctx F G Addr HK Note DTx WCore σ n) (t : Addr → F) : F :=
  ∑ z, keyCoeffs sel P c.c (c.sender b) z * t z - t (c.sender b)

/-- The bad event of the random branch: the coefficient of `Y` vanishes. -/
def BadS (sel : Selection F Addr k n) (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (b : Bool) (w : DPre F G Addr HK Note DTx WCore σ n) : Prop :=
  match w.2.2.2.2.2 with
  | none => False
  | some c => betaS sel P b c w.2.2.2.2.1 = 0

omit [Fintype F] [Inhabited Addr] [Inhabited WCore] [Inhabited C] in
/-- Moving the DDH value `z` to the end of the reduction's run. -/
theorem ddhRandomS_eqd (sel : Selection F Addr k n)
    (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) :
    ddhRandomExperiment P.g (ddhReductionS sel P A b) =ᵈ
      prefixS sel P A b >>= contRealS sel P A b := by
  simp only [ddhRandomExperiment, ddhReductionS, prefixS, contRealS, keyedBodyS,
    bind_assoc, pure_bind]
  refine EvalDistEq.bind_right _ fun x => EvalDistEq.bind_right _ fun y => ?_
  refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun hk => ?_)
  refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun u => ?_)
  refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun t => ?_)
  refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun ox => ?_)
  cases ox with
  | none => exact bind_const_eqd _ _
  | some c => exact bind_swap_eqd _ _ _

omit [Fintype F] [SampleableType HK] [Inhabited Addr] [Inhabited WCore] [Inhabited C]
  [Fintype Addr] in
/-- Outside the bad event the reduction's random branch and the ideal hybrid agree. -/
theorem contRealS_eqd {sel : Selection F Addr k n}
    {P : Params F G Addr HK Key Note DTx WCore C Proof k n}
    (hg : Function.Bijective (· • P.g : F → G))
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool)
    (w : DPre F G Addr HK Note DTx WCore σ n) (hw : ¬BadS sel P b w) :
    contRealS sel P A b w =ᵈ contIdealS P A b w := by
  obtain ⟨x, y, hk, u, t, ox⟩ := w
  cases ox with
  | none => exact .rfl
  | some c =>
    have hβ : betaS sel P b c t ≠ 0 := hw
    simp only [contRealS, contIdealS]
    refine EvalDistEq.bind_right _ fun rR => ?_
    set α := dotProduct (coefRow P.pos P.coef (c.sender b)) c.c.fill +
      ∑ z, keyCoeffs sel P c.c (c.sender b) z * (c.c.sk z + u z -
        Matrix.mulVec (setMatrix P.pos P.coef (selected sel P.pos P.coef c.c)) c.c.fill z) -
      u (c.sender b)
    have he : (fun z : F => ddhPoint sel P c.c u t (c.sender b) (x • P.g) (z • P.g)) =
        fun z => α • (x • P.g) + (betaS sel P b c t * z) • P.g := by
      funext z
      simp only [ddhPoint, betaS, α, smul_smul]
    have hbij : Function.Bijective
        (fun z : F => ddhPoint sel P c.c u t (c.sender b) (x • P.g) (z • P.g)) := by
      rw [he]
      exact (Equiv.addLeft (α • (x • P.g))).bijective.comp
        (hg.comp (mulLeft_bijective₀ _ hβ))
    exact uniform_bind_bij
      (e := fun z : F => ddhPoint sel P c.c u t (c.sender b) (x • P.g) (z • P.g))
      hbij (fun K => keyedBodyS P A b (x • P.g) hk _ c rR K)

/-- The ideal run as a function of the ephemeral scalar, the KDF key and the oracle. -/
noncomputable def idealBodyS (sel : Selection F Addr k n)
    (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) (r : F) (hk : HK)
    (H : Addr → G) : ProbComp Bool := do
  let ox ← setup sel P A b hk H
  match ox with
  | none => return false
  | some c => do
    let rR ← $ᵗ F
    let K ← $ᵗ G
    keyedBodyS P A b (r • P.g) hk H c rR K

omit [Fintype F] [Inhabited Addr] [Inhabited WCore] [Inhabited C] in
/-- The ideal branch is the hybrid with a uniform sender key point. -/
theorem idealS_eqd (sel : Selection F Addr k n)
    {P : Params F G Addr HK Key Note DTx WCore C Proof k n}
    (hg : Function.Bijective (· • P.g : F → G))
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) :
    prefixS sel P A b >>= contIdealS P A b =ᵈ hybrid sel P A b true .randKey .real := by
  have h0 : prefixS sel P A b >>= contIdealS P A b = (do
      let x ← $ᵗ F; let y ← $ᵗ F; let hk ← $ᵗ HK; let u ← $ᵗ (Addr → F)
      let t ← $ᵗ (Addr → F)
      idealBodyS sel P A b x hk fun q => u q • P.g + t q • (y • P.g)) := by
    simp only [prefixS, contIdealS, idealBodyS, bind_assoc, pure_bind]
    rfl
  rw [h0]
  refine EvalDistEq.trans (my := do
      let hk ← $ᵗ HK; let x ← $ᵗ F; let y ← $ᵗ F; let u ← $ᵗ (Addr → F)
      let t ← $ᵗ (Addr → F)
      idealBodyS sel P A b x hk fun q => u q • P.g + t q • (y • P.g)) ?_ ?_
  · refine (EvalDistEq.bind_right _ fun x => bind_swap_eqd _ _ _).trans ?_
    exact bind_swap_eqd _ _ _
  refine EvalDistEq.bind_right _ fun hk => ?_
  refine (IndKey.reprogram hg fun x H => idealBodyS sel P A b x hk H).trans ?_
  refine EvalDistEq.bind_right _ fun H => ?_
  simp only [idealBodyS, keyedBodyS]
  refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun ox => ?_)
  cases ox with
  | none => exact bind_const_eqd _ _
  | some x =>
    simp only [slot, bind_assoc, pure_bind, ite_true]
    exact .rfl

omit [Inhabited Addr] [Inhabited WCore] [Inhabited C] [SampleableType Key] in
/-- The bad event has probability at most `1/|F|`: the oracle given to the adversary hides `t`,
and the sender is not selected. -/
theorem prob_badS_le (sel : Selection F Addr k n)
    {P : Params F G Addr HK Key Note DTx WCore C Proof k n}
    (hg : Function.Bijective (· • P.g : F → G))
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) :
    Pr{let w ← prefixS sel P A b}[BadS sel P b w] ≤ (Fintype.card F : ℝ≥0∞)⁻¹ := by
  let proj : DPre F G Addr HK Note DTx WCore σ n →
      (Addr → F) × Option (Ctx F G Addr HK Note DTx WCore σ n) := fun w =>
    (w.2.2.2.2.1, w.2.2.2.2.2)
  let Bad' : (Addr → F) × Option (Ctx F G Addr HK Note DTx WCore σ n) → Prop := fun v =>
    match v.2 with
    | none => False
    | some c => betaS sel P b c v.1 = 0
  have hproj : Pr{let w ← prefixS sel P A b}[BadS sel P b w] =
      Pr{let v ← proj <$> prefixS sel P A b}[Bad' v] := by
    rw [prEvent_map]
    rfl
  have hdist : proj <$> prefixS sel P A b =ᵈ (do
      let hk ← $ᵗ HK; let H ← $ᵗ (Addr → G); let ox ← setup sel P A b hk H
      let t ← $ᵗ (Addr → F)
      return (t, ox)) := by
    have h0 : proj <$> prefixS sel P A b = (do
        let _x ← $ᵗ F; let y ← $ᵗ F; let hk ← $ᵗ HK; let u ← $ᵗ (Addr → F)
        let t ← $ᵗ (Addr → F)
        (do let ox ← setup sel P A b hk fun q => u q • P.g + t q • (y • P.g)
            return (t, ox))) := by
      simp [prefixS, proj, map_bind]
    rw [h0]
    refine EvalDistEq.trans (my := do
        let hk ← $ᵗ HK; let _x ← $ᵗ F; let y ← $ᵗ F; let u ← $ᵗ (Addr → F)
        let t ← $ᵗ (Addr → F)
        (do let ox ← setup sel P A b hk fun q => u q • P.g + t q • (y • P.g)
            return (t, ox))) ?_ ?_
    · refine (EvalDistEq.bind_right _ fun x => bind_swap_eqd _ _ _).trans ?_
      exact bind_swap_eqd _ _ _
    refine EvalDistEq.bind_right _ fun hk => ?_
    refine EvalDistEq.trans (my := do
        let _x ← $ᵗ F; let _y ← $ᵗ F; let t ← $ᵗ (Addr → F); let H ← $ᵗ (Addr → G)
        (do let ox ← setup sel P A b hk H; return (t, ox))) ?_ ?_
    · refine EvalDistEq.bind_right _ fun x => EvalDistEq.bind_right _ fun y => ?_
      exact IndKey.reprogram_core hg (y • P.g) fun t H => do
        let ox ← setup sel P A b hk H
        return (t, ox)
    refine ((bind_const_eqd _ _).trans (bind_const_eqd _ _)).trans ?_
    refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun H => ?_)
    exact bind_swap_eqd _ _ _
  rw [hproj, hdist.prEvent_eq Bad']
  refine prEvent_bind_le_of_forall_le _ _ _ fun hk => ?_
  refine prEvent_bind_le_of_forall_le _ _ _ fun H => ?_
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun ox hox => ?_
  cases ox with
  | none => simp [Bad']
  | some c =>
    have hv := (setup_spec hox).1
    simp only [Bad', betaS, bind_pure_comp, prEvent_map]
    exact prob_beta_le_finset _ _ (sender_not_mem_selected hv b)

omit [Inhabited Addr] [Inhabited WCore] [Inhabited C] in
/-- Sender's ciphertext: replacing its DH point by a uniform group element costs the DDH
advantage of `ddhReductionS` plus `1/|F|`. -/
theorem hop_ddhS (sel : Selection F Addr k n)
    {P : Params F G Addr HK Key Note DTx WCore C Proof k n}
    (hg : Function.Bijective (· • P.g : F → G))
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) :
    𝒟[hybrid sel P A b true .real .real].boolDist 𝒟[hybrid sel P A b true .randKey .real] ≤
      ddhAdvantage P.g (ddhReductionS sel P A b) + (Fintype.card F : ℝ≥0∞)⁻¹ := by
  have hreal := (ddhRealS_eqd sel hg A b).evalDist_eq
  have hrand := (ddhRandomS_eqd sel P A b).evalDist_eq
  have hideal := (idealS_eqd sel hg A b).evalDist_eq
  have h1 := prEvent_bind_le_add_of_disagree (mx := prefixS sel P A b)
    (my := contRealS sel P A b) (oc := contIdealS P A b) (q := fun y => y = true) (ε₂ := 0)
    (prob_badS_le sel hg A b)
    (fun w _ hw => by rw [add_zero]; exact ((contRealS_eqd hg A b w hw).prEvent_eq _).le)
  have h2 := prEvent_bind_le_add_of_disagree (mx := prefixS sel P A b)
    (my := contIdealS P A b) (oc := contRealS sel P A b) (q := fun y => y = true) (ε₂ := 0)
    (prob_badS_le sel hg A b)
    (fun w _ hw => by rw [add_zero]; exact ((contRealS_eqd hg A b w hw).symm.prEvent_eq _).le)
  have hdist : 𝒟[ddhRandomExperiment P.g (ddhReductionS sel P A b)].boolDist
      𝒟[hybrid sel P A b true .randKey .real] ≤ (Fintype.card F : ℝ≥0∞)⁻¹ := by
    rw [hrand, ← hideal, MeasureTheory.Measure.boolDist,
      ← prEvent_eq_evalDist_singleton, ← prEvent_eq_evalDist_singleton]
    simp only [add_zero] at h1 h2
    exact ENNReal.absDiff_le_iff.2 ⟨h1, h2⟩
  rw [← hreal]
  calc _ ≤ ddhAdvantage P.g (ddhReductionS sel P A b) +
        𝒟[ddhRandomExperiment P.g (ddhReductionS sel P A b)].boolDist
          𝒟[hybrid sel P A b true .randKey .real] :=
        MeasureTheory.Measure.boolDist_triangle _ _ _
    _ ≤ _ := by gcongr

/-! ## Recipient's ciphertext -/

/-- The reduction for the recipient's ciphertext, run on a real DDH tuple `(r • g, ·, ·)`, after
rewriting its key as the true shared point. -/
noncomputable def realBodyR (sel : Selection F Addr k n)
    (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) (r : F) (hk : HK)
    (H : Addr → G) : ProbComp Bool := do
  let ox ← setup sel P A b hk H
  match ox with
  | none => return false
  | some x => do
    let rS ← $ᵗ F
    let ctS ← slot P .dummy rS hk H x.V (x.sender b) (x.note b)
    let ctR := (P.senc (P.kdf hk (encPoint r (retrieveKey P.pos P.coef x.V x.c.wAddr)
      (H x.c.wAddr))) (x.note b), r • P.g)
    let π ← P.zk.sim (stmt x ctS ctR)
    finish A x ctS ctR π

omit [Fintype F] [Inhabited Addr] [Inhabited WCore] [Inhabited C] in
/-- The DDH reduction for the recipient's ciphertext, run on a real tuple, is the hybrid with
the real recipient ciphertext. -/
theorem ddhRealR_eqd (sel : Selection F Addr k n)
    {P : Params F G Addr HK Key Note DTx WCore C Proof k n}
    (hg : Function.Bijective (· • P.g : F → G))
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) :
    ddhRealExperiment P.g (ddhReductionR sel P A b) =ᵈ hybrid sel P A b true .dummy .real := by
  have h1 : ddhRealExperiment P.g (ddhReductionR sel P A b) =ᵈ (do
      let x ← $ᵗ F; let y ← $ᵗ F; let hk ← $ᵗ HK; let u ← $ᵗ (Addr → F)
      let t ← $ᵗ (Addr → F)
      realBodyR sel P A b x hk fun z => u z • P.g + t z • (y • P.g)) := by
    simp only [ddhRealExperiment, ddhReductionR, realBodyR]
    refine EvalDistEq.bind_right _ fun x => EvalDistEq.bind_right _ fun y =>
      EvalDistEq.bind_right _ fun hk => EvalDistEq.bind_right _ fun u =>
        EvalDistEq.bind_right _ fun t => ?_
    refine OracleComp.EvalDistEq.bind_congr_of_support _ fun ox hox => ?_
    cases ox with
    | none => exact .rfl
    | some c =>
      have hV := (setup_spec hox).2
      simp only [ddhPoint_real hV]
      exact .rfl
  refine h1.trans ?_
  refine EvalDistEq.trans (my := do
      let hk ← $ᵗ HK; let x ← $ᵗ F; let y ← $ᵗ F; let u ← $ᵗ (Addr → F)
      let t ← $ᵗ (Addr → F)
      realBodyR sel P A b x hk fun z => u z • P.g + t z • (y • P.g)) ?_ ?_
  · refine (EvalDistEq.bind_right _ fun x => bind_swap_eqd _ _ _).trans ?_
    exact bind_swap_eqd _ _ _
  refine EvalDistEq.bind_right _ fun hk => ?_
  refine (IndKey.reprogram hg fun x H => realBodyR sel P A b x hk H).trans ?_
  refine EvalDistEq.bind_right _ fun H => ?_
  simp only [realBodyR]
  refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun ox => ?_)
  cases ox with
  | none => exact bind_const_eqd _ _
  | some x =>
    refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun rS => ?_)
    simp only [slot, bind_assoc, pure_bind, ite_true]
    exact .rfl

/-- The recipient-hop reduction's run after the sender's dummy ciphertext, with recipient key
point `K`. -/
noncomputable def keyedBodyR (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) (X : G) (hk : HK)
    (x : Ctx F G Addr HK Note DTx WCore σ n) (ctS : C × G) (K : G) : ProbComp Bool := do
  let ctR := (P.senc (P.kdf hk K) (x.note b), X)
  let π ← P.zk.sim (stmt x ctS ctR)
  finish A x ctS ctR π

/-- The rest of the recipient-hop reduction's run on a random tuple, with `z` sampled last. -/
noncomputable def contRealR (sel : Selection F Addr k n)
    (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool)
    (w : DPre F G Addr HK Note DTx WCore σ n) : ProbComp Bool :=
  match w.2.2.2.2.2 with
  | none => return false
  | some c => do
    let rS ← $ᵗ F
    let ctS ← slot P .dummy rS w.2.2.1 (w.oracle P.g) c.V (c.sender b) (c.note b)
    let z ← $ᵗ F
    keyedBodyR P A b (w.1 • P.g) w.2.2.1 c ctS
      (ddhPoint sel P c.c w.2.2.2.1 w.2.2.2.2.1 c.c.wAddr (w.1 • P.g) (z • P.g))

/-- The ideal counterpart of `contRealR`: a uniform recipient key point. -/
noncomputable def contIdealR (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool)
    (w : DPre F G Addr HK Note DTx WCore σ n) : ProbComp Bool :=
  match w.2.2.2.2.2 with
  | none => return false
  | some c => do
    let rS ← $ᵗ F
    let ctS ← slot P .dummy rS w.2.2.1 (w.oracle P.g) c.V (c.sender b) (c.note b)
    let K ← $ᵗ G
    keyedBodyR P A b (w.1 • P.g) w.2.2.1 c ctS K

/-- The coefficient of `Y` in the recipient's point: `∑_{z ∈ T} λ_z t_z − t_{w_addr}`. -/
noncomputable def betaR (sel : Selection F Addr k n)
    (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (c : Ctx F G Addr HK Note DTx WCore σ n) (t : Addr → F) : F :=
  ∑ z, keyCoeffs sel P c.c c.c.wAddr z * t z - t c.c.wAddr

/-- The bad event of the recipient hop's random branch. -/
def BadR (sel : Selection F Addr k n) (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (w : DPre F G Addr HK Note DTx WCore σ n) : Prop :=
  match w.2.2.2.2.2 with
  | none => False
  | some c => betaR sel P c w.2.2.2.2.1 = 0

omit [Fintype F] [Inhabited Addr] [Inhabited WCore] [Inhabited C] in
/-- Moving the DDH value `z` to the end of the recipient-hop reduction's run. -/
theorem ddhRandomR_eqd (sel : Selection F Addr k n)
    (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) :
    ddhRandomExperiment P.g (ddhReductionR sel P A b) =ᵈ
      prefixS sel P A b >>= contRealR sel P A b := by
  simp only [ddhRandomExperiment, ddhReductionR, prefixS, contRealR, keyedBodyR,
    bind_assoc, pure_bind]
  refine EvalDistEq.bind_right _ fun x => EvalDistEq.bind_right _ fun y => ?_
  refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun hk => ?_)
  refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun u => ?_)
  refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun t => ?_)
  refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun ox => ?_)
  cases ox with
  | none => exact bind_const_eqd _ _
  | some c =>
    refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun rS => ?_)
    exact bind_swap_eqd _ _ _

omit [Fintype F] [SampleableType HK] [Inhabited Addr] [Inhabited WCore] [Inhabited C]
  [Fintype Addr] in
/-- Outside the bad event the recipient hop's random branch and the ideal hybrid agree. -/
theorem contRealR_eqd {sel : Selection F Addr k n}
    {P : Params F G Addr HK Key Note DTx WCore C Proof k n}
    (hg : Function.Bijective (· • P.g : F → G))
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool)
    (w : DPre F G Addr HK Note DTx WCore σ n) (hw : ¬BadR sel P w) :
    contRealR sel P A b w =ᵈ contIdealR P A b w := by
  obtain ⟨x, y, hk, u, t, ox⟩ := w
  cases ox with
  | none => exact .rfl
  | some c =>
    have hβ : betaR sel P c t ≠ 0 := hw
    simp only [contRealR, contIdealR]
    refine EvalDistEq.bind_right _ fun rS => EvalDistEq.bind_right _ fun ctS => ?_
    set α := dotProduct (coefRow P.pos P.coef c.c.wAddr) c.c.fill +
      ∑ z, keyCoeffs sel P c.c c.c.wAddr z * (c.c.sk z + u z -
        Matrix.mulVec (setMatrix P.pos P.coef (selected sel P.pos P.coef c.c)) c.c.fill z) -
      u c.c.wAddr
    have he : (fun z : F => ddhPoint sel P c.c u t c.c.wAddr (x • P.g) (z • P.g)) =
        fun z => α • (x • P.g) + (betaR sel P c t * z) • P.g := by
      funext z
      simp only [ddhPoint, betaR, α, smul_smul]
    have hbij : Function.Bijective
        (fun z : F => ddhPoint sel P c.c u t c.c.wAddr (x • P.g) (z • P.g)) := by
      rw [he]
      exact (Equiv.addLeft (α • (x • P.g))).bijective.comp
        (hg.comp (mulLeft_bijective₀ _ hβ))
    exact uniform_bind_bij
      (e := fun z : F => ddhPoint sel P c.c u t c.c.wAddr (x • P.g) (z • P.g))
      hbij (fun K => keyedBodyR P A b (x • P.g) hk c ctS K)

/-- The ideal recipient-hop run as a function of the ephemeral scalar, the KDF key and the
oracle. -/
noncomputable def idealBodyR (sel : Selection F Addr k n)
    (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) (r : F) (hk : HK)
    (H : Addr → G) : ProbComp Bool := do
  let ox ← setup sel P A b hk H
  match ox with
  | none => return false
  | some c => do
    let rS ← $ᵗ F
    let ctS ← slot P .dummy rS hk H c.V (c.sender b) (c.note b)
    let K ← $ᵗ G
    keyedBodyR P A b (r • P.g) hk c ctS K

omit [Fintype F] [Inhabited Addr] [Inhabited WCore] [Inhabited C] in
/-- The ideal branch is the hybrid with a uniform recipient key point. -/
theorem idealR_eqd (sel : Selection F Addr k n)
    {P : Params F G Addr HK Key Note DTx WCore C Proof k n}
    (hg : Function.Bijective (· • P.g : F → G))
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) :
    prefixS sel P A b >>= contIdealR P A b =ᵈ hybrid sel P A b true .dummy .randKey := by
  have h0 : prefixS sel P A b >>= contIdealR P A b = (do
      let x ← $ᵗ F; let y ← $ᵗ F; let hk ← $ᵗ HK; let u ← $ᵗ (Addr → F)
      let t ← $ᵗ (Addr → F)
      idealBodyR sel P A b x hk fun q => u q • P.g + t q • (y • P.g)) := by
    simp only [prefixS, contIdealR, idealBodyR, bind_assoc, pure_bind]
    rfl
  rw [h0]
  refine EvalDistEq.trans (my := do
      let hk ← $ᵗ HK; let x ← $ᵗ F; let y ← $ᵗ F; let u ← $ᵗ (Addr → F)
      let t ← $ᵗ (Addr → F)
      idealBodyR sel P A b x hk fun q => u q • P.g + t q • (y • P.g)) ?_ ?_
  · refine (EvalDistEq.bind_right _ fun x => bind_swap_eqd _ _ _).trans ?_
    exact bind_swap_eqd _ _ _
  refine EvalDistEq.bind_right _ fun hk => ?_
  refine (IndKey.reprogram hg fun x H => idealBodyR sel P A b x hk H).trans ?_
  refine EvalDistEq.bind_right _ fun H => ?_
  simp only [idealBodyR, keyedBodyR]
  refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun ox => ?_)
  cases ox with
  | none => exact bind_const_eqd _ _
  | some x =>
    refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun rS => ?_)
    simp only [slot, bind_assoc, pure_bind, ite_true]
    exact .rfl

omit [Inhabited Addr] [Inhabited WCore] [Inhabited C] [SampleableType Key] in
/-- The recipient hop's bad event has probability at most `1/|F|`. -/
theorem prob_badR_le (sel : Selection F Addr k n)
    {P : Params F G Addr HK Key Note DTx WCore C Proof k n}
    (hg : Function.Bijective (· • P.g : F → G))
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) :
    Pr{let w ← prefixS sel P A b}[BadR sel P w] ≤ (Fintype.card F : ℝ≥0∞)⁻¹ := by
  let proj : DPre F G Addr HK Note DTx WCore σ n →
      (Addr → F) × Option (Ctx F G Addr HK Note DTx WCore σ n) := fun w =>
    (w.2.2.2.2.1, w.2.2.2.2.2)
  let Bad' : (Addr → F) × Option (Ctx F G Addr HK Note DTx WCore σ n) → Prop := fun v =>
    match v.2 with
    | none => False
    | some c => betaR sel P c v.1 = 0
  have hproj : Pr{let w ← prefixS sel P A b}[BadR sel P w] =
      Pr{let v ← proj <$> prefixS sel P A b}[Bad' v] := by
    rw [prEvent_map]
    rfl
  have hdist : proj <$> prefixS sel P A b =ᵈ (do
      let hk ← $ᵗ HK; let H ← $ᵗ (Addr → G); let ox ← setup sel P A b hk H
      let t ← $ᵗ (Addr → F)
      return (t, ox)) := by
    have h0 : proj <$> prefixS sel P A b = (do
        let _x ← $ᵗ F; let y ← $ᵗ F; let hk ← $ᵗ HK; let u ← $ᵗ (Addr → F)
        let t ← $ᵗ (Addr → F)
        (do let ox ← setup sel P A b hk fun q => u q • P.g + t q • (y • P.g)
            return (t, ox))) := by
      simp [prefixS, proj, map_bind]
    rw [h0]
    refine EvalDistEq.trans (my := do
        let hk ← $ᵗ HK; let _x ← $ᵗ F; let y ← $ᵗ F; let u ← $ᵗ (Addr → F)
        let t ← $ᵗ (Addr → F)
        (do let ox ← setup sel P A b hk fun q => u q • P.g + t q • (y • P.g)
            return (t, ox))) ?_ ?_
    · refine (EvalDistEq.bind_right _ fun x => bind_swap_eqd _ _ _).trans ?_
      exact bind_swap_eqd _ _ _
    refine EvalDistEq.bind_right _ fun hk => ?_
    refine EvalDistEq.trans (my := do
        let _x ← $ᵗ F; let _y ← $ᵗ F; let t ← $ᵗ (Addr → F); let H ← $ᵗ (Addr → G)
        (do let ox ← setup sel P A b hk H; return (t, ox))) ?_ ?_
    · refine EvalDistEq.bind_right _ fun x => EvalDistEq.bind_right _ fun y => ?_
      exact IndKey.reprogram_core hg (y • P.g) fun t H => do
        let ox ← setup sel P A b hk H
        return (t, ox)
    refine ((bind_const_eqd _ _).trans (bind_const_eqd _ _)).trans ?_
    refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun H => ?_)
    exact bind_swap_eqd _ _ _
  rw [hproj, hdist.prEvent_eq Bad']
  refine prEvent_bind_le_of_forall_le _ _ _ fun hk => ?_
  refine prEvent_bind_le_of_forall_le _ _ _ fun H => ?_
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun ox hox => ?_
  cases ox with
  | none => simp [Bad']
  | some c =>
    have hv := (setup_spec hox).1
    simp only [Bad', betaR, bind_pure_comp, prEvent_map]
    exact prob_beta_le_finset _ _ (recipient_not_mem_selected hv)

omit [Inhabited Addr] [Inhabited WCore] [Inhabited C] in
/-- Recipient's ciphertext, with the sender's already a dummy. -/
theorem hop_ddhR (sel : Selection F Addr k n)
    {P : Params F G Addr HK Key Note DTx WCore C Proof k n}
    (hg : Function.Bijective (· • P.g : F → G))
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) :
    𝒟[hybrid sel P A b true .dummy .real].boolDist 𝒟[hybrid sel P A b true .dummy .randKey] ≤
      ddhAdvantage P.g (ddhReductionR sel P A b) + (Fintype.card F : ℝ≥0∞)⁻¹ := by
  have hreal := (ddhRealR_eqd sel hg A b).evalDist_eq
  have hrand := (ddhRandomR_eqd sel P A b).evalDist_eq
  have hideal := (idealR_eqd sel hg A b).evalDist_eq
  have h1 := prEvent_bind_le_add_of_disagree (mx := prefixS sel P A b)
    (my := contRealR sel P A b) (oc := contIdealR P A b) (q := fun y => y = true) (ε₂ := 0)
    (prob_badR_le sel hg A b)
    (fun w _ hw => by rw [add_zero]; exact ((contRealR_eqd hg A b w hw).prEvent_eq _).le)
  have h2 := prEvent_bind_le_add_of_disagree (mx := prefixS sel P A b)
    (my := contIdealR P A b) (oc := contRealR sel P A b) (q := fun y => y = true) (ε₂ := 0)
    (prob_badR_le sel hg A b)
    (fun w _ hw => by rw [add_zero]; exact ((contRealR_eqd hg A b w hw).symm.prEvent_eq _).le)
  have hdist : 𝒟[ddhRandomExperiment P.g (ddhReductionR sel P A b)].boolDist
      𝒟[hybrid sel P A b true .dummy .randKey] ≤ (Fintype.card F : ℝ≥0∞)⁻¹ := by
    rw [hrand, ← hideal, MeasureTheory.Measure.boolDist,
      ← prEvent_eq_evalDist_singleton, ← prEvent_eq_evalDist_singleton]
    simp only [add_zero] at h1 h2
    exact ENNReal.absDiff_le_iff.2 ⟨h1, h2⟩
  rw [← hreal]
  calc _ ≤ ddhAdvantage P.g (ddhReductionR sel P A b) +
        𝒟[ddhRandomExperiment P.g (ddhReductionR sel P A b)].boolDist
          𝒟[hybrid sel P A b true .dummy .randKey] :=
        MeasureTheory.Measure.boolDist_triangle _ _ _
    _ ≤ _ := by gcongr

end AuditPay.SLINDDrop
