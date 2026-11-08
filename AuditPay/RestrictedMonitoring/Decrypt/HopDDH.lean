/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.RestrictedMonitoring.Decrypt.Algebra
import AuditPay.IndKey
import VCVio.EvalDist.Monad.Disagreement.Measure

/-!
# Theorem 3, decryption game, DDH hop: the target's Diffie–Hellman point becomes uniform

The reduction programs `H(z) = u_z • g + t_z • Y` and embeds the DDH challenge in the target's
ciphertext only. On a real tuple its run is the real hybrid. On a random tuple the target's point
is `α' • X + β' • Z`, which is uniform unless `β' = ∑_z β_{i*}(z) t_z = 0`; since the
`H`-coefficients `β_{i*}` of the target are a nonzero function (`hCoeff_target_ne_zero`) and
the oracle hides `t`, that has probability at most `1/|F|`.
-/

open OracleComp DiffieHellman ENNReal

namespace AuditPay.RestrictedMonitoring.Decrypt

open SLIND (Mode)

variable {F G Addr HK Key Msg C σ : Type} {k n : ℕ}
  [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G]
  [Fintype Addr] [DecidableEq Addr] [SampleableType HK] [SampleableType Key]
  [DecidableEq Msg] [SampleableType Msg]

/-! ## The real branch -/

/-- The reduction's run on a real DDH tuple `(ρ • g, ·, ·)`, after rewriting its key as the true
shared point: it depends on the programmed oracle only through `H`. -/
noncomputable def realBody (P : Params F G Addr HK Key Msg C k n)
    (A : Adversary F G Addr HK Msg C σ n) (ρ : F) (hk : HK) (H : Addr → G) : ProbComp Bool := do
  let c ← A.commit hk H
  let m ← $ᵗ (Fin (n + 1) → Msg)
  let r ← $ᵗ (Fin (n + 1) → F)
  let μ ← $ᵗ Msg
  finish P A hk H c m r μ (encrypt (P.kdf hk) P.senc P.g
    (retrieveKey P.pos P.coef (c.vec P.g H) (c.addrs (c.target P))) (H (c.addrs (c.target P)))
    ρ μ)

omit [Fintype F] in
/-- The DDH reduction, run on a real tuple, is the real hybrid. -/
theorem ddhReal_eqd {P : Params F G Addr HK Key Msg C k n}
    (hg : Function.Bijective (· • P.g : F → G)) (A : Adversary F G Addr HK Msg C σ n) :
    ddhRealExperiment P.g (ddhReduction P A) =ᵈ hybrid P A .real := by
  -- 1. rewrite the reduction's key as the true shared point
  have h1 : ddhRealExperiment P.g (ddhReduction P A) = (do
      let x ← $ᵗ F; let y ← $ᵗ F; let hk ← $ᵗ HK; let u ← $ᵗ (Addr → F)
      let t ← $ᵗ (Addr → F)
      realBody P A x hk fun z => u z • P.g + t z • (y • P.g)) := by
    simp only [ddhRealExperiment, ddhReduction, realBody, ddhPoint_real, encrypt]
  rw [h1]
  -- 2. move `hk` to the front
  refine EvalDistEq.trans (my := do
      let hk ← $ᵗ HK; let x ← $ᵗ F; let y ← $ᵗ F; let u ← $ᵗ (Addr → F)
      let t ← $ᵗ (Addr → F)
      realBody P A x hk fun z => u z • P.g + t z • (y • P.g)) ?_ ?_
  · refine (EvalDistEq.bind_right _ fun x => bind_swap_eqd _ _ _).trans ?_
    exact bind_swap_eqd _ _ _
  simp only [hybrid]
  refine EvalDistEq.bind_right _ fun hk => ?_
  -- 3. the programmed oracle is a uniform `H`
  refine (IndKey.reprogram hg fun x H => realBody P A x hk H).trans ?_
  refine EvalDistEq.bind_right _ fun H => ?_
  -- 4. sample the target's ephemeral scalar last, as `ρ`
  simp only [realBody, slot, pure_bind]
  refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun c => ?_)
  refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun m => ?_)
  refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun r => ?_)
  exact bind_swap_eqd _ _ _

/-! ## The random branch -/

/-- The reduction's state before the DDH value `Z` is used. -/
structure Pre (F Addr HK σ : Type) (n : ℕ) where
  /-- The DDH scalar `x`, the target's ephemeral scalar. -/
  x : F
  /-- The DDH scalar `y`. -/
  y : F
  /-- The KDF key. -/
  hk : HK
  /-- The oracle programming `u`. -/
  u : Addr → F
  /-- The oracle programming `t`. -/
  t : Addr → F
  /-- The adversary's commitment. -/
  c : Commit F Addr σ n

/-- The programmed oracle of a reduction state. -/
def Pre.oracle (g : G) (w : Pre F Addr HK σ n) : Addr → G :=
  fun z => w.u z • g + w.t z • (w.y • g)

/-- The coefficient of `Y` in the target's encryption point: `β' = ∑_z β_{i*}(z) t_z`. -/
def Pre.beta (P : Params F G Addr HK Key Msg C k n) (w : Pre F Addr HK σ n) : F :=
  ∑ z, w.c.hCoeff P (w.c.target P) z * w.t z

/-- The reduction's run up to the adversary's commitment. -/
noncomputable def pre (P : Params F G Addr HK Key Msg C k n)
    (A : Adversary F G Addr HK Msg C σ n) : ProbComp (Pre F Addr HK σ n) := do
  let x ← $ᵗ F
  let y ← $ᵗ F
  let hk ← $ᵗ HK
  let u ← $ᵗ (Addr → F)
  let t ← $ᵗ (Addr → F)
  let c ← A.commit hk fun z => u z • P.g + t z • (y • P.g)
  return ⟨x, y, hk, u, t, c⟩

/-- The end of the reduction's run, with the target's Diffie–Hellman point `K`. -/
def keyed (P : Params F G Addr HK Key Msg C k n) (A : Adversary F G Addr HK Msg C σ n)
    (w : Pre F Addr HK σ n) (m : Fin (n + 1) → Msg) (r : Fin (n + 1) → F) (μ : Msg) (K : G) :
    ProbComp Bool :=
  finish P A w.hk (w.oracle P.g) w.c m r μ (P.senc (P.kdf w.hk K) μ, w.x • P.g)

/-- The rest of the reduction's run on a random tuple `Z = z • g`, with `z` sampled last. -/
noncomputable def contReal (P : Params F G Addr HK Key Msg C k n)
    (A : Adversary F G Addr HK Msg C σ n) (w : Pre F Addr HK σ n) : ProbComp Bool := do
  let m ← $ᵗ (Fin (n + 1) → Msg)
  let r ← $ᵗ (Fin (n + 1) → F)
  let μ ← $ᵗ Msg
  let z ← $ᵗ F
  keyed P A w m r μ (ddhPoint P w.c w.u w.t (w.c.target P) (w.x • P.g) (z • P.g))

/-- The ideal counterpart of `contReal`: a uniform Diffie–Hellman point for the target. -/
noncomputable def contIdeal (P : Params F G Addr HK Key Msg C k n)
    (A : Adversary F G Addr HK Msg C σ n) (w : Pre F Addr HK σ n) : ProbComp Bool := do
  let m ← $ᵗ (Fin (n + 1) → Msg)
  let r ← $ᵗ (Fin (n + 1) → F)
  let μ ← $ᵗ Msg
  let K ← $ᵗ G
  keyed P A w m r μ K

omit [Fintype F] [SampleableType G] [SampleableType Key] in
/-- Moving the DDH value `z` to the end of the reduction's run. -/
theorem ddhRandom_eqd (P : Params F G Addr HK Key Msg C k n)
    (A : Adversary F G Addr HK Msg C σ n) :
    ddhRandomExperiment P.g (ddhReduction P A) =ᵈ pre P A >>= contReal P A := by
  simp only [ddhRandomExperiment, ddhReduction, pre, contReal, keyed, bind_assoc, pure_bind]
  refine EvalDistEq.bind_right _ fun x => EvalDistEq.bind_right _ fun y => ?_
  refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun hk => ?_)
  refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun u => ?_)
  refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun t => ?_)
  refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun c => ?_)
  refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun m => ?_)
  refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun r => ?_)
  exact bind_swap_eqd _ _ _

omit [Fintype F] [SampleableType HK] [SampleableType Key] in
/-- When the coefficient of `Y` is nonzero, the reduction's random branch and the ideal run
agree: the target's point is uniform. -/
theorem contReal_eqd {P : Params F G Addr HK Key Msg C k n}
    (hg : Function.Bijective (· • P.g : F → G)) (A : Adversary F G Addr HK Msg C σ n)
    (w : Pre F Addr HK σ n) (hw : w.beta P ≠ 0) :
    contReal P A w =ᵈ contIdeal P A w := by
  simp only [contReal, contIdeal]
  refine EvalDistEq.bind_right _ fun m => EvalDistEq.bind_right _ fun r =>
    EvalDistEq.bind_right _ fun μ => ?_
  set α := w.c.gCoeff P (w.c.target P) + ∑ z, w.c.hCoeff P (w.c.target P) z * w.u z
  have he : (fun z : F => ddhPoint P w.c w.u w.t (w.c.target P) (w.x • P.g) (z • P.g)) =
      fun z => α • (w.x • P.g) + (w.beta P * z) • P.g := by
    funext z
    simp only [ddhPoint, Pre.beta, α, smul_smul]
  have hbij : Function.Bijective
      (fun z : F => ddhPoint P w.c w.u w.t (w.c.target P) (w.x • P.g) (z • P.g)) := by
    rw [he]
    exact (Equiv.addLeft (α • (w.x • P.g))).bijective.comp
      (hg.comp (mulLeft_bijective₀ _ hw))
  exact uniform_bind_bij
    (e := fun z : F => ddhPoint P w.c w.u w.t (w.c.target P) (w.x • P.g) (z • P.g))
    hbij (fun K => keyed P A w m r μ K)

/-- The ideal run as a function of the target's ephemeral scalar, the KDF key and the oracle. -/
noncomputable def idealBody (P : Params F G Addr HK Key Msg C k n)
    (A : Adversary F G Addr HK Msg C σ n) (ρ : F) (hk : HK) (H : Addr → G) : ProbComp Bool := do
  let c ← A.commit hk H
  let m ← $ᵗ (Fin (n + 1) → Msg)
  let r ← $ᵗ (Fin (n + 1) → F)
  let μ ← $ᵗ Msg
  let K ← $ᵗ G
  finish P A hk H c m r μ (P.senc (P.kdf hk K) μ, ρ • P.g)

omit [Fintype F] in
/-- The ideal branch is the hybrid with a uniform Diffie–Hellman point for the target. -/
theorem ideal_eqd {P : Params F G Addr HK Key Msg C k n}
    (hg : Function.Bijective (· • P.g : F → G)) (A : Adversary F G Addr HK Msg C σ n) :
    pre P A >>= contIdeal P A =ᵈ hybrid P A .randKey := by
  have h0 : pre P A >>= contIdeal P A = (do
      let x ← $ᵗ F; let y ← $ᵗ F; let hk ← $ᵗ HK; let u ← $ᵗ (Addr → F)
      let t ← $ᵗ (Addr → F)
      idealBody P A x hk fun z => u z • P.g + t z • (y • P.g)) := by
    simp only [pre, contIdeal, idealBody, keyed, bind_assoc, pure_bind]
    rfl
  rw [h0]
  refine EvalDistEq.trans (my := do
      let hk ← $ᵗ HK; let x ← $ᵗ F; let y ← $ᵗ F; let u ← $ᵗ (Addr → F)
      let t ← $ᵗ (Addr → F)
      idealBody P A x hk fun z => u z • P.g + t z • (y • P.g)) ?_ ?_
  · refine (EvalDistEq.bind_right _ fun x => bind_swap_eqd _ _ _).trans ?_
    exact bind_swap_eqd _ _ _
  simp only [hybrid]
  refine EvalDistEq.bind_right _ fun hk => ?_
  refine (IndKey.reprogram hg fun x H => idealBody P A x hk H).trans ?_
  refine EvalDistEq.bind_right _ fun H => ?_
  simp only [idealBody, slot, bind_assoc, pure_bind]
  refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun c => ?_)
  refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun m => ?_)
  refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun r => ?_)
  exact bind_swap_eqd _ _ _

omit [SampleableType Key] [DecidableEq Msg] [SampleableType Msg] in
/-- The coefficient of `Y` vanishes with probability at most `1/|F|`: the target's
`H`-coefficients are nonzero, and the oracle handed to the adversary hides `t`. -/
theorem prob_beta_le {P : Params F G Addr HK Key Msg C k n}
    (hg : Function.Bijective (· • P.g : F → G)) (A : Adversary F G Addr HK Msg C σ n) :
    Pr{let w ← pre P A}[w.beta P = 0] ≤ (Fintype.card F : ℝ≥0∞)⁻¹ := by
  let proj : Pre F Addr HK σ n → (Addr → F) × Commit F Addr σ n := fun w => (w.t, w.c)
  let Bad' : (Addr → F) × Commit F Addr σ n → Prop := fun v =>
    ∑ z, v.2.hCoeff P (v.2.target P) z * v.1 z = 0
  have hproj : Pr{let w ← pre P A}[w.beta P = 0] =
      Pr{let v ← proj <$> pre P A}[Bad' v] := by
    rw [prEvent_map]
    rfl
  have hdist : proj <$> pre P A =ᵈ (do
      let hk ← $ᵗ HK; let H ← $ᵗ (Addr → G); let c ← A.commit hk H
      let t ← $ᵗ (Addr → F)
      return (t, c)) := by
    have h0 : proj <$> pre P A = (do
        let _x ← $ᵗ F; let y ← $ᵗ F; let hk ← $ᵗ HK; let u ← $ᵗ (Addr → F)
        let t ← $ᵗ (Addr → F)
        (do let c ← A.commit hk fun z => u z • P.g + t z • (y • P.g); return (t, c))) := by
      simp [pre, proj, map_bind]
    rw [h0]
    refine EvalDistEq.trans (my := do
        let hk ← $ᵗ HK; let _x ← $ᵗ F; let y ← $ᵗ F; let u ← $ᵗ (Addr → F)
        let t ← $ᵗ (Addr → F)
        (do let c ← A.commit hk fun z => u z • P.g + t z • (y • P.g); return (t, c))) ?_ ?_
    · refine (EvalDistEq.bind_right _ fun x => bind_swap_eqd _ _ _).trans ?_
      exact bind_swap_eqd _ _ _
    refine EvalDistEq.bind_right _ fun hk => ?_
    refine EvalDistEq.trans (my := do
        let _x ← $ᵗ F; let _y ← $ᵗ F; let t ← $ᵗ (Addr → F); let H ← $ᵗ (Addr → G)
        (do let c ← A.commit hk H; return (t, c))) ?_ ?_
    · refine EvalDistEq.bind_right _ fun x => EvalDistEq.bind_right _ fun y => ?_
      exact IndKey.reprogram_core hg (y • P.g) fun t H => do
        let c ← A.commit hk H
        return (t, c)
    refine ((bind_const_eqd _ _).trans (bind_const_eqd _ _)).trans ?_
    refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun H => ?_)
    exact bind_swap_eqd _ _ _
  rw [hproj, hdist.prEvent_eq Bad']
  refine prEvent_bind_le_of_forall_le _ _ _ fun hk => ?_
  refine prEvent_bind_le_of_forall_le _ _ _ fun H => ?_
  refine prEvent_bind_le_of_forall_le _ _ _ fun c => ?_
  simp only [Bad', bind_pure_comp, prEvent_map]
  exact prob_form_eq_zero_le (hCoeff_target_ne_zero P c)

/-- Replacing the target's Diffie–Hellman point by a uniform group element costs the DDH
advantage of `ddhReduction` plus `1/|F|`. -/
theorem hop_ddh {P : Params F G Addr HK Key Msg C k n}
    (hg : Function.Bijective (· • P.g : F → G)) (A : Adversary F G Addr HK Msg C σ n) :
    𝒟[hybrid P A .real].boolDist 𝒟[hybrid P A .randKey] ≤
      ddhAdvantage P.g (ddhReduction P A) + (Fintype.card F : ℝ≥0∞)⁻¹ := by
  have hreal := (ddhReal_eqd hg A).evalDist_eq
  have hrand := (ddhRandom_eqd P A).evalDist_eq
  have hideal := (ideal_eqd hg A).evalDist_eq
  have h1 := prEvent_bind_le_add_of_disagree (mx := pre P A) (my := contReal P A)
    (oc := contIdeal P A) (q := fun y => y = true) (D := fun w => w.beta P = 0) (ε₂ := 0)
    (prob_beta_le hg A)
    (fun w _ hw => by rw [add_zero]; exact ((contReal_eqd hg A w hw).prEvent_eq _).le)
  have h2 := prEvent_bind_le_add_of_disagree (mx := pre P A) (my := contIdeal P A)
    (oc := contReal P A) (q := fun y => y = true) (D := fun w => w.beta P = 0) (ε₂ := 0)
    (prob_beta_le hg A)
    (fun w _ hw => by rw [add_zero]; exact ((contReal_eqd hg A w hw).symm.prEvent_eq _).le)
  have hdist : 𝒟[ddhRandomExperiment P.g (ddhReduction P A)].boolDist
      𝒟[hybrid P A .randKey] ≤ (Fintype.card F : ℝ≥0∞)⁻¹ := by
    rw [hrand, ← hideal, MeasureTheory.Measure.boolDist,
      ← prEvent_eq_evalDist_singleton, ← prEvent_eq_evalDist_singleton]
    simp only [add_zero] at h1 h2
    exact ENNReal.absDiff_le_iff.2 ⟨h1, h2⟩
  rw [← hreal]
  calc _ ≤ ddhAdvantage P.g (ddhReduction P A) +
        𝒟[ddhRandomExperiment P.g (ddhReduction P A)].boolDist 𝒟[hybrid P A .randKey] :=
        MeasureTheory.Measure.boolDist_triangle _ _ _
    _ ≤ _ := by gcongr

end AuditPay.RestrictedMonitoring.Decrypt
