/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.Defs
import AuditPay.Prob
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
import VCVio.EvalDist.Monad.Disagreement.Measure

/-!
# Theorem 1: IND-Key security of selective encryption

Definition 1 of the paper (the IND-Key game) and Theorem 1 (IND-Key security under DDH in the
random oracle model), with a tight reduction:

  `IND-Key advantage ≤ DDH advantage of `ddhReduction A` + 1/|F|`

with no loss in the number of random-oracle queries.

## Modeling

* The random oracle `H : Addr → G` (hash-to-curve) is a uniformly random function on a finite
  address space, sampled at the start and handed to the adversary as a value. This gives the
  adversary at least the power of oracle access.
* Definition 1 hands the adversary `(sk, AK_a, R, K_b)`. We write it in the
  real-or-random style of VCV-io's DDH: `realExperiment` gives the true shared point
  `K₀ = r • (AK_a - H(a*))`, `randomExperiment` a uniform `K₁ ∈ G`, and the advantage is the
  distance between the two (`Measure.boolDist`).
* If the adversary submits `a* = a` (Definition 1 requires `a* ≠ a`) both experiments return
  `false`.
* The game follows Definition 1; there is no audit-key query oracle.

## The reduction

On a DDH challenge `(g, X, Y, Z)` the reduction programs `H(x) = u_x • g + t_x • Y` for
independent uniform `u_x, t_x`, sets `R = X`, and answers
`K = sk • X + (u_a - u_{a*}) • X + (t_a - t_{a*}) • Z`. With a real DDH tuple this is exactly the
real experiment. With a random tuple it is the random experiment unless `t_a = t_{a*}`, which
has probability `1/|F|` because `H` hides `t`.
-/

open OracleComp DiffieHellman ENNReal

namespace AuditPay.IndKey

/-- An IND-Key adversary: first, given the random oracle, it picks the audit-key address `a`
and the encryptor's address `a*`; then it guesses from `(sk, AK_a, R, K)`. -/
structure Adversary (F G Addr σ : Type) where
  /-- Choose `(a, a*)` and a state, given the random oracle `H`. -/
  choose : (Addr → G) → ProbComp (Addr × Addr × σ)
  /-- Guess from the state and `(sk, AK_a, R, K)`. -/
  guess : σ → F → G → G → G → ProbComp Bool

variable {F G Addr σ : Type} [Field F] [Fintype F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G] [Fintype Addr] [DecidableEq Addr]

/-- The IND-Key experiment with the true shared point `K₀ = r • (AK_a - H(a*))`
(Definition 1, `b = 0`). -/
noncomputable def realExperiment (g : G) (A : Adversary F G Addr σ) : ProbComp Bool := do
  let H ← $ᵗ (Addr → G)
  let p ← A.choose H
  if p.1 = p.2.1 then return false else do
    let sk ← $ᵗ F
    let r ← $ᵗ F
    A.guess p.2.2 sk (auditKey g sk (H p.1)) (r • g)
      (encPoint r (auditKey g sk (H p.1)) (H p.2.1))

/-- The IND-Key experiment with a uniformly random key `K₁ ∈ G` (Definition 1, `b = 1`). -/
noncomputable def randomExperiment (g : G) (A : Adversary F G Addr σ) : ProbComp Bool := do
  let H ← $ᵗ (Addr → G)
  let p ← A.choose H
  if p.1 = p.2.1 then return false else do
    let sk ← $ᵗ F
    let r ← $ᵗ F
    let K ← $ᵗ G
    A.guess p.2.2 sk (auditKey g sk (H p.1)) (r • g) K

/-- The IND-Key advantage: the distance between the real and random experiments. -/
noncomputable def advantage (g : G) (A : Adversary F G Addr σ) : ℝ≥0∞ :=
  𝒟[realExperiment g A].boolDist 𝒟[randomExperiment g A]

/-- The DDH reduction for Theorem 1. -/
noncomputable def ddhReduction (A : Adversary F G Addr σ) : DDHAdversary F G := fun g X Y Z => do
  let u ← $ᵗ (Addr → F)
  let t ← $ᵗ (Addr → F)
  let p ← A.choose fun x => u x • g + t x • Y
  if p.1 = p.2.1 then return false else do
    let sk ← $ᵗ F
    A.guess p.2.2 sk (auditKey g sk (u p.1 • g + t p.1 • Y)) X
      (sk • X + (u p.1 - u p.2.1) • X + (t p.1 - t p.2.1) • Z)

/-! ## The real branch -/

/-- The real experiment after `H` is fixed, with the ephemeral scalar `r` sampled first. -/
noncomputable def realCont (g : G) (A : Adversary F G Addr σ) (r : F) (H : Addr → G) :
    ProbComp Bool := do
  let p ← A.choose H
  if p.1 = p.2.1 then return false else do
    let sk ← $ᵗ F
    A.guess p.2.2 sk (auditKey g sk (H p.1)) (r • g)
      (encPoint r (auditKey g sk (H p.1)) (H p.2.1))

omit [Fintype F] [SampleableType F] [SampleableType G] in
/-- On a real DDH tuple the reduction's key is the true shared point. -/
theorem real_key (g : G) (sk x y ua ua' ta ta' : F) :
    sk • (x • g) + (ua - ua') • (x • g) + (ta - ta') • ((x * y) • g) =
      encPoint x (auditKey g sk (ua • g + ta • (y • g))) (ua' • g + ta' • (y • g)) := by
  simp only [encPoint, auditKey]
  module

omit [Fintype F] [SampleableType G] [Fintype Addr] in
/-- Sampling `r` first and then the rest of the real experiment. -/
theorem realCont_eqd (g : G) (A : Adversary F G Addr σ) (H : Addr → G) :
    (do let r ← $ᵗ F; realCont g A r H) =ᵈ (do
      let p ← A.choose H
      if p.1 = p.2.1 then return false else do
        let sk ← $ᵗ F
        let r ← $ᵗ F
        A.guess p.2.2 sk (auditKey g sk (H p.1)) (r • g)
          (encPoint r (auditKey g sk (H p.1)) (H p.2.1))) := by
  simp only [realCont]
  refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun p => ?_)
  by_cases h : p.1 = p.2.1
  · simp only [h, ite_true]
    exact bind_const_eqd _ _
  · simp only [h, ite_false]
    exact bind_swap_eqd _ _ _

omit [Fintype F] in
/-- The reduction's programmed oracle `H = u • g + t • Y` is a uniformly random function,
independent of `t`. -/
theorem reprogram_core {g : G} (hg : Function.Bijective (· • g : F → G)) (Y : G) {β : Type}
    (k : (Addr → F) → (Addr → G) → ProbComp β) :
    (do let u ← $ᵗ (Addr → F); let t ← $ᵗ (Addr → F); k t fun z => u z • g + t z • Y) =ᵈ
      (do let t ← $ᵗ (Addr → F); let H ← $ᵗ (Addr → G); k t H) := by
  refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun t => ?_)
  exact uniform_bind_bij (e := fun (u : Addr → F) (z : Addr) => u z • g + t z • Y)
    (bijective_smul_add hg fun z => t z • Y) (k t)

omit [Fintype F] in
/-- Replacing the reduction's oracle by a uniform one, when the continuation ignores `t`. -/
theorem reprogram {g : G} (hg : Function.Bijective (· • g : F → G)) {β : Type}
    (k : F → (Addr → G) → ProbComp β) :
    (do
      let x ← $ᵗ F; let y ← $ᵗ F; let u ← $ᵗ (Addr → F); let t ← $ᵗ (Addr → F)
      k x fun z => u z • g + t z • (y • g)) =ᵈ
      (do let H ← $ᵗ (Addr → G); let x ← $ᵗ F; k x H) := by
  refine EvalDistEq.trans (my := do
      let x ← $ᵗ F; let _y ← $ᵗ F; let _t ← $ᵗ (Addr → F); let H ← $ᵗ (Addr → G); k x H) ?_ ?_
  · refine EvalDistEq.bind_right _ fun x => EvalDistEq.bind_right _ fun y => ?_
    exact reprogram_core hg (y • g) fun _ H => k x H
  refine EvalDistEq.trans (my := do let x ← $ᵗ F; let H ← $ᵗ (Addr → G); k x H) ?_ ?_
  · refine EvalDistEq.bind_right _ fun x => ?_
    exact (bind_const_eqd _ _).trans (bind_const_eqd _ _)
  exact bind_swap_eqd _ _ _

omit [Fintype F] in
/-- The reduction run on a real DDH tuple is the real IND-Key experiment. -/
theorem ddhReal_eqd {g : G} (hg : Function.Bijective (· • g : F → G))
    (A : Adversary F G Addr σ) :
    ddhRealExperiment g (ddhReduction A) =ᵈ realExperiment g A := by
  have h0 : ddhRealExperiment g (ddhReduction A) = (do
      let x ← $ᵗ F; let y ← $ᵗ F; let u ← $ᵗ (Addr → F); let t ← $ᵗ (Addr → F)
      realCont g A x fun z => u z • g + t z • (y • g)) := by
    simp only [ddhRealExperiment, ddhReduction, realCont, real_key]
  rw [h0]
  exact (reprogram hg (realCont g A)).trans
    (EvalDistEq.bind_right _ fun H => realCont_eqd g A H)

/-! ## The random branch -/

/-- The random-key experiment after `H` is fixed, with the ephemeral scalar sampled first. -/
noncomputable def randCont (g : G) (A : Adversary F G Addr σ) (r : F) (H : Addr → G) :
    ProbComp Bool := do
  let p ← A.choose H
  if p.1 = p.2.1 then return false else do
    let sk ← $ᵗ F
    let K ← $ᵗ G
    A.guess p.2.2 sk (auditKey g sk (H p.1)) (r • g) K

omit [Fintype F] [Fintype Addr] in
/-- Sampling `r` first and then the rest of the random experiment. -/
theorem randCont_eqd (g : G) (A : Adversary F G Addr σ) (H : Addr → G) :
    (do let r ← $ᵗ F; randCont g A r H) =ᵈ (do
      let p ← A.choose H
      if p.1 = p.2.1 then return false else do
        let sk ← $ᵗ F
        let r ← $ᵗ F
        let K ← $ᵗ G
        A.guess p.2.2 sk (auditKey g sk (H p.1)) (r • g) K) := by
  simp only [randCont]
  refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun p => ?_)
  by_cases h : p.1 = p.2.1
  · simp only [h, ite_true]
    exact bind_const_eqd _ _
  · simp only [h, ite_false]
    exact bind_swap_eqd _ _ _

/-- The state of the reduction before the challenge: `(x, y, u, t, adversary's choice)`. -/
abbrev Pre (F Addr σ : Type) := F × F × (Addr → F) × (Addr → F) × (Addr × Addr × σ)

/-- The reduction's run on a random DDH tuple, up to the adversary's choice. -/
noncomputable def randPrefix (g : G) (A : Adversary F G Addr σ) : ProbComp (Pre F Addr σ) := do
  let x ← $ᵗ F; let y ← $ᵗ F; let u ← $ᵗ (Addr → F); let t ← $ᵗ (Addr → F)
  let p ← A.choose fun z => u z • g + t z • (y • g)
  return (x, y, u, t, p)

/-- The rest of the reduction's run on a random DDH tuple, with `Z = z • g` sampled last.
When `ideal` is set, the term `(t_a - t_{a*}) • Z` is replaced by `Z`. -/
noncomputable def randRest (g : G) (A : Adversary F G Addr σ) (ideal : Bool)
    (w : Pre F Addr σ) : ProbComp Bool :=
  if w.2.2.2.2.1 = w.2.2.2.2.2.1 then return false else do
    let sk ← $ᵗ F
    let z ← $ᵗ F
    A.guess w.2.2.2.2.2.2 sk
      (auditKey g sk (w.2.2.1 w.2.2.2.2.1 • g + w.2.2.2.1 w.2.2.2.2.1 • (w.2.1 • g))) (w.1 • g)
      (sk • (w.1 • g) + (w.2.2.1 w.2.2.2.2.1 - w.2.2.1 w.2.2.2.2.2.1) • (w.1 • g) +
        if ideal then z • g else
          (w.2.2.2.1 w.2.2.2.2.1 - w.2.2.2.1 w.2.2.2.2.2.1) • (z • g))

omit [Fintype F] [SampleableType G] in
/-- Moving the DDH value `z` from the start of the reduction's run to the end. -/
theorem ddhRandom_eqd (g : G) (A : Adversary F G Addr σ) :
    ddhRandomExperiment g (ddhReduction A) =ᵈ randPrefix g A >>= randRest g A false := by
  simp only [ddhRandomExperiment, ddhReduction, randPrefix, randRest, bind_assoc, pure_bind,
    Bool.false_eq_true, ite_false]
  refine EvalDistEq.bind_right _ fun x => EvalDistEq.bind_right _ fun y => ?_
  refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun u => ?_)
  refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun t => ?_)
  refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun p => ?_)
  by_cases h : p.1 = p.2.1
  · simp only [h, ite_true]
    exact bind_const_eqd _ _
  · simp only [h, ite_false]
    exact bind_swap_eqd _ _ _

omit [Fintype F] in
/-- In the ideal hybrid the key is uniform, so it is the random IND-Key experiment. -/
theorem randIdeal_eqd {g : G} (hg : Function.Bijective (· • g : F → G))
    (A : Adversary F G Addr σ) :
    randPrefix g A >>= randRest g A true =ᵈ randomExperiment g A := by
  have h0 : randPrefix g A >>= randRest g A true =ᵈ (do
      let x ← $ᵗ F; let y ← $ᵗ F; let u ← $ᵗ (Addr → F); let t ← $ᵗ (Addr → F)
      randCont g A x fun z => u z • g + t z • (y • g)) := by
    simp only [randPrefix, randRest, randCont, bind_assoc, pure_bind, ite_true]
    refine EvalDistEq.bind_right _ fun x => EvalDistEq.bind_right _ fun y =>
      EvalDistEq.bind_right _ fun u => EvalDistEq.bind_right _ fun t =>
        EvalDistEq.bind_right _ fun p => ?_
    by_cases h : p.1 = p.2.1
    · simp only [h, ite_true]
      exact .rfl
    · simp only [h, ite_false]
      refine EvalDistEq.bind_right _ fun sk => ?_
      exact uniform_bind_bij
        (e := fun z : F => sk • (x • g) + (u p.1 - u p.2.1) • (x • g) + z • g)
        ((Equiv.addLeft (sk • (x • g) + (u p.1 - u p.2.1) • (x • g))).bijective.comp hg) _
  exact h0.trans ((reprogram hg (randCont g A)).trans
    (EvalDistEq.bind_right _ fun H => randCont_eqd g A H))

/-! ## The bad event -/

/-- The bad event of the random branch: the adversary's two (distinct) addresses received
colliding `t` values. -/
def Bad (w : Pre F Addr σ) : Prop :=
  w.2.2.2.2.1 ≠ w.2.2.2.2.2.1 ∧ w.2.2.2.1 w.2.2.2.2.1 = w.2.2.2.1 w.2.2.2.2.2.1

omit [Fintype F] [SampleableType G] [Fintype Addr] in
/-- Outside the bad event, the reduction's random branch and the ideal hybrid agree. -/
theorem randRest_eqd_of_not_bad (g : G) (A : Adversary F G Addr σ) (w : Pre F Addr σ)
    (hw : ¬Bad w) :
    randRest g A false w =ᵈ randRest g A true w := by
  obtain ⟨x, y, u, t, p⟩ := w
  unfold randRest
  by_cases ha : p.1 = p.2.1
  · simp only [ha, ite_true]
    exact .rfl
  · have ht : t p.1 - t p.2.1 ≠ 0 := sub_ne_zero.2 fun h => hw ⟨ha, h⟩
    simp only [ha, ite_false, Bool.false_eq_true, ite_true]
    refine EvalDistEq.bind_right _ fun sk => ?_
    simp only [smul_smul]
    exact uniform_bind_bij (e := fun z : F => (t p.1 - t p.2.1) * z)
      (mulLeft_bijective₀ _ ht) (fun z => A.guess p.2.2 sk _ (x • g) (_ + z • g))

/-- The bad event has probability at most `1/|F|`: the oracle `H` given to the adversary is
independent of `t`. -/
theorem prob_bad_le {g : G} (hg : Function.Bijective (· • g : F → G))
    (A : Adversary F G Addr σ) :
    Pr{let w ← randPrefix g A}[Bad w] ≤ (Fintype.card F : ℝ≥0∞)⁻¹ := by
  let proj : Pre F Addr σ → (Addr → F) × (Addr × Addr × σ) := fun w => (w.2.2.2.1, w.2.2.2.2)
  let Bad' : (Addr → F) × (Addr × Addr × σ) → Prop := fun v =>
    v.2.1 ≠ v.2.2.1 ∧ v.1 v.2.1 = v.1 v.2.2.1
  have hproj : Pr{let w ← randPrefix g A}[Bad w] = Pr{let v ← proj <$> randPrefix g A}[Bad' v] := by
    rw [prEvent_map]
    rfl
  have hdist : proj <$> randPrefix g A =ᵈ (do
      let H ← $ᵗ (Addr → G); let p ← A.choose H; let t ← $ᵗ (Addr → F)
      return (t, p)) := by
    have h0 : proj <$> randPrefix g A = (do
        let _x ← $ᵗ F; let y ← $ᵗ F; let u ← $ᵗ (Addr → F); let t ← $ᵗ (Addr → F)
        (do let p ← A.choose fun z => u z • g + t z • (y • g); return (t, p))) := by
      simp [randPrefix, proj, map_bind]
    rw [h0]
    refine EvalDistEq.trans (my := do
        let _x ← $ᵗ F; let _y ← $ᵗ F; let t ← $ᵗ (Addr → F); let H ← $ᵗ (Addr → G)
        (do let p ← A.choose H; return (t, p))) ?_ ?_
    · refine EvalDistEq.bind_right _ fun x => EvalDistEq.bind_right _ fun y => ?_
      exact reprogram_core hg (y • g) fun t H => do let p ← A.choose H; return (t, p)
    refine ((bind_const_eqd _ _).trans (bind_const_eqd _ _)).trans ?_
    refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun H => ?_)
    exact bind_swap_eqd _ _ _
  rw [hproj, hdist.prEvent_eq Bad']
  refine prEvent_bind_le_of_forall_le _ _ _ fun H => ?_
  refine prEvent_bind_le_of_forall_le _ _ _ fun p => ?_
  by_cases ha : p.1 = p.2.1
  · simp [Bad', ha]
  · simp only [Bad', ha, ne_eq, not_false_eq_true, true_and, bind_pure_comp, prEvent_map]
    exact prob_coord_eq_le ha

/-- **Theorem 1** (IND-Key security, tight form): for a generator `g`, the IND-Key advantage of
any adversary is at most the DDH advantage of `ddhReduction A` plus `1/|F|`. -/
theorem advantage_le {g : G} (hg : Function.Bijective (· • g : F → G))
    (A : Adversary F G Addr σ) :
    advantage g A ≤ ddhAdvantage g (ddhReduction A) + (Fintype.card F : ℝ≥0∞)⁻¹ := by
  have hreal := (ddhReal_eqd hg A).evalDist_eq
  have hrand := (ddhRandom_eqd g A).evalDist_eq
  have hideal := (randIdeal_eqd hg A).evalDist_eq
  -- the distance between the reduction's random branch and the ideal hybrid
  have hbad : ∀ b : Bool,
      Pr{let y ← randPrefix g A >>= randRest g A b}[y = true] ≤
        Pr{let y ← randPrefix g A >>= randRest g A (!b)}[y = true] +
          (Fintype.card F : ℝ≥0∞)⁻¹ := by
    intro b
    have := prEvent_bind_le_add_of_disagree (mx := randPrefix g A) (my := randRest g A b)
      (oc := randRest g A (!b)) (q := fun y => y = true) (ε₂ := 0) (prob_bad_le hg A)
      (fun w _ hw => by
        rw [add_zero]
        cases b
        · exact ((randRest_eqd_of_not_bad g A w hw).prEvent_eq _).le
        · exact ((randRest_eqd_of_not_bad g A w hw).symm.prEvent_eq _).le)
    simpa only [add_zero] using this
  have hdist : 𝒟[ddhRandomExperiment g (ddhReduction A)].boolDist 𝒟[randomExperiment g A] ≤
      (Fintype.card F : ℝ≥0∞)⁻¹ := by
    rw [hrand, ← hideal, MeasureTheory.Measure.boolDist,
      ← prEvent_eq_evalDist_singleton, ← prEvent_eq_evalDist_singleton]
    exact ENNReal.absDiff_le_iff.2 ⟨hbad false, hbad true⟩
  calc advantage g A
      = 𝒟[ddhRealExperiment g (ddhReduction A)].boolDist 𝒟[randomExperiment g A] := by
        rw [advantage, hreal]
    _ ≤ ddhAdvantage g (ddhReduction A) +
          𝒟[ddhRandomExperiment g (ddhReduction A)].boolDist 𝒟[randomExperiment g A] :=
        MeasureTheory.Measure.boolDist_triangle _ _ _
    _ ≤ ddhAdvantage g (ddhReduction A) + (Fintype.card F : ℝ≥0∞)⁻¹ := by gcongr

end AuditPay.IndKey
