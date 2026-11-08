/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.Defs
import AuditPay.Prob
import AuditPay.IndKey
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman

/-!
# Theorem 3: Restricted Monitoring, key-output game

## The game

The adversary outputs a vector `V`, `|V| + 1` distinct addresses and a secret key `sk_a` for
each, and wins if every address retrieves exactly its audit key,
`RetrieveKey(V, a) = sk_a • g + H(a)`. This is the easiest to win of the three Restricted
Monitoring games formalized: `RestrictedMonitoring.SharedSecret` is the shared-secret game
(arbitrary `V`, reduction to CDH; `SharedSecret.keyOutput_le` shows it also bounds this game),
and `RestrictedMonitoring.Decrypt` is Definition 3's decryption game.

The position and coefficient hashes `pos`, `coef` are arbitrary fixed functions here, which only
strengthens the statement: the argument needs no randomness from them. The hash-to-curve `H` is
a random oracle.

## The reduction

On a DLog challenge `Y`, program `H(x) = u_x • g + t_x • Y`. The `|V|+1` rows of the encoding
matrix are linearly dependent; for a nonzero dependency `γ`,
`∑ γᵢ (skᵢ • g + H(aᵢ)) = ∑ γᵢ RetrieveKey(V, aᵢ) = 0`, i.e.
`(∑ γᵢ (skᵢ + u_{aᵢ})) • g + (∑ γᵢ t_{aᵢ}) • Y = 0`, which reveals `log Y` unless
`∑ γᵢ t_{aᵢ} = 0`. Since `H` hides `t`, that happens with probability `1/|F|`.
-/

open OracleComp DiffieHellman ENNReal

namespace AuditPay.RestrictedMonitoring

/-- A Restricted Monitoring adversary: given `H`, it outputs a vector `V` of size `n`, `n + 1`
distinct addresses, and an audit secret key for each. -/
structure Adversary (F G Addr : Type) (n : ℕ) where
  /-- The adversary's output. -/
  run : (Addr → G) → ProbComp ((Fin n → G) × (Fin (n + 1) ↪ Addr) × (Fin (n + 1) → F))

variable {F G Addr : Type} {k n : ℕ} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]
  [Fintype Addr] [DecidableEq Addr]

/-- The Restricted Monitoring experiment: the adversary wins if all `n + 1` addresses retrieve
their claimed audit keys from `V`. -/
noncomputable def experiment (g : G) (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F)
    (A : Adversary F G Addr n) : ProbComp Bool := do
  let H ← $ᵗ (Addr → G)
  let out ← A.run H
  return decide (∀ i, retrieveKey pos coef out.1 (out.2.1 i) =
    auditKey g (out.2.2 i) (H (out.2.1 i)))

/-- A nonzero left-kernel vector of a matrix, if one exists (it does when there are more rows
than columns). -/
noncomputable def dependency {m : ℕ} (C : Matrix (Fin m) (Fin n) F) : Fin m → F := by
  classical
  exact if h : ∃ γ : Fin m → F, γ ≠ 0 ∧ Matrix.vecMul γ C = 0 then h.choose else 0

/-- The DLog reduction for Theorem 3. -/
noncomputable def dlogReduction (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F)
    (A : Adversary F G Addr n) : DLogAdversary F G := fun g Y => do
  let u ← $ᵗ (Addr → F)
  let t ← $ᵗ (Addr → F)
  let out ← A.run fun x => u x • g + t x • Y
  let γ := dependency (coefMatrix pos coef out.2.1)
  return -(∑ i, γ i * (out.2.2 i + u (out.2.1 i))) / ∑ i, γ i * t (out.2.1 i)

/-! ## Linear algebra: the dependency -/

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- `n + 1` rows in an `n`-dimensional space are linearly dependent. -/
theorem exists_vecMul_eq_zero (C : Matrix (Fin (n + 1)) (Fin n) F) :
    ∃ γ : Fin (n + 1) → F, γ ≠ 0 ∧ Matrix.vecMul γ C = 0 := by
  have hdep : ¬LinearIndependent F (fun i => C i) := fun h => by
    have := h.fintype_card_le_finrank
    simp at this
  obtain ⟨γ, hγ, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hdep
  exact ⟨γ, fun h => hi (by simp [h]), by rw [Matrix.vecMul_eq_sum]; exact hγ⟩

omit [SampleableType F] in
/-- The dependency of a matrix with `n + 1` rows and `n` columns is a nonzero left-kernel
vector. -/
theorem dependency_spec (C : Matrix (Fin (n + 1)) (Fin n) F) :
    dependency C ≠ 0 ∧ Matrix.vecMul (dependency C) C = 0 := by
  have h := exists_vecMul_eq_zero C
  unfold dependency
  rw [dite_eq_left h]
  exact h.choose_spec

/-! ## Algebra: a winning output reveals the discrete logarithm -/

omit [SampleableType F] [SampleableType G] [DecidableEq G] [Fintype Addr] [DecidableEq Addr] in
/-- If the adversary wins against the programmed oracle `H(x) = u_x • g + t_x • (y • g)` and
`∑ γᵢ t_{aᵢ} ≠ 0`, the reduction's answer is `y`. -/
theorem answer_eq_of_win {g : G} (hg : Function.Injective (· • g : F → G))
    (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F) (V : Fin n → G)
    (S : Fin (n + 1) → Addr) (sk : Fin (n + 1) → F) (y : F) (u t : Addr → F)
    (hwin : ∀ i, retrieveKey pos coef V (S i) =
      auditKey g (sk i) (u (S i) • g + t (S i) • (y • g)))
    (ht : ∑ i, dependency (coefMatrix pos coef S) i * t (S i) ≠ 0) :
    -(∑ i, dependency (coefMatrix pos coef S) i * (sk i + u (S i))) /
      ∑ i, dependency (coefMatrix pos coef S) i * t (S i) = y := by
  have hγ := (dependency_spec (coefMatrix pos coef S)).2
  have hcol : ∀ j, ∑ i, dependency (coefMatrix pos coef S) i * coefMatrix pos coef S i j = 0 := by
    intro j
    simpa [Matrix.vecMul, dotProduct] using congrFun hγ j
  have h0 : ∑ i, dependency (coefMatrix pos coef S) i • retrieveKey pos coef V (S i) = 0 := by
    simp only [retrieveKey_eq_matVecG pos coef S V, matVecG, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, hcol, zero_smul, Finset.sum_const_zero]
  have h1 : ((∑ i, dependency (coefMatrix pos coef S) i * (sk i + u (S i))) +
      (∑ i, dependency (coefMatrix pos coef S) i * t (S i)) * y) • g = (0 : F) • g := by
    rw [zero_smul, ← h0, Finset.sum_mul, ← Finset.sum_add_distrib, Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hwin i, auditKey]
    module
  rw [div_eq_iff ht]
  linear_combination -hg h1

/-! ## Probability: the oracle hides `t` -/

omit [DecidableEq F] in
/-- A nonzero linear form in distinct coordinates of a uniformly random function vanishes with
probability at most `1/|F|`. -/
theorem prob_linear_eq_zero_le {m : ℕ} {γ : Fin m → F} (hγ : γ ≠ 0) {S : Fin m → Addr}
    (hS : Function.Injective S) :
    Pr{let t ← $ᵗ (Addr → F)}[∑ i, γ i * t (S i) = 0] ≤ (Fintype.card F : ℝ≥0∞)⁻¹ := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, γ i ≠ 0 := Function.ne_iff.1 hγ
  let e := Equiv.funSplitAt (S i₀) F
  refine (SampleableType.prEvent_uniformSample_equiv e.symm
    fun t : Addr → F => ∑ i, γ i * t (S i) = 0).symm.trans_le ?_
  refine SampleableType.prEvent_uniformSample_prod_le_of_forall_snd _ fun r => ?_
  have hdiff : ∀ c c' : F, (∑ i, γ i * e.symm (c, r) (S i)) - ∑ i, γ i * e.symm (c', r) (S i) =
      γ i₀ * (c - c') := by
    intro c c'
    rw [← Finset.sum_sub_distrib]
    simp only [← mul_sub]
    rw [Finset.sum_eq_single i₀]
    · simp [e]
    · intro i _ hi
      have : S i ≠ S i₀ := hS.ne hi
      simp [e, this]
    · simp
  have hinj : Function.Injective fun c : F => ∑ i, γ i * e.symm (c, r) (S i) := by
    intro c c' h
    have := hdiff c c'
    rw [show (∑ i, γ i * e.symm (c, r) (S i)) = ∑ i, γ i * e.symm (c', r) (S i) from h,
      sub_self] at this
    exact sub_eq_zero.1 ((mul_eq_zero.1 this.symm).resolve_left hi₀)
  refine (SampleableType.prEvent_uniformSample_apply_eq_le hinj 0).trans_eq ?_
  rw [Nat.card_eq_fintype_card]

/-! ## The joint run of the reduction -/

/-- The output type of a Restricted Monitoring adversary. -/
abbrev Out (F G Addr : Type) (n : ℕ) := (Fin n → G) × (Fin (n + 1) ↪ Addr) × (Fin (n + 1) → F)

/-- The winning condition of the experiment against the oracle `H`. -/
abbrev Wins (g : G) (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F) (H : Addr → G)
    (out : Out F G Addr n) : Prop :=
  ∀ i, retrieveKey pos coef out.1 (out.2.1 i) = auditKey g (out.2.2 i) (H (out.2.1 i))

/-- The linear form `∑ γᵢ t_{aᵢ}` that the reduction divides by. -/
noncomputable def tForm (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F) (t : Addr → F)
    (out : Out F G Addr n) : F :=
  ∑ i, dependency (coefMatrix pos coef out.2.1) i * t (out.2.1 i)

/-- The reduction's answer, given its randomness `u, t` and the adversary's output. -/
noncomputable def answer (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F)
    (u t : Addr → F) (out : Out F G Addr n) : F :=
  -(∑ i, dependency (coefMatrix pos coef out.2.1) i * (out.2.2 i + u (out.2.1 i))) /
    tForm pos coef t out

/-- The reduction run on a uniform DLog challenge `y • g`, recording `(y, u, t, out)`. -/
noncomputable def joint (g : G) (A : Adversary F G Addr n) :
    ProbComp (F × (Addr → F) × (Addr → F) × Out F G Addr n) := do
  let y ← $ᵗ F
  let u ← $ᵗ (Addr → F)
  let t ← $ᵗ (Addr → F)
  let out ← A.run fun x => u x • g + t x • (y • g)
  return (y, u, t, out)

omit [SampleableType G] [DecidableEq G] in
/-- The reduction's success probability is that of its answer being `y` in the joint run. -/
theorem prob_answer_eq (g : G) (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F)
    (A : Adversary F G Addr n) :
    Pr{let w ← joint g A}[answer pos coef w.2.1 w.2.2.1 w.2.2.2 = w.1] =
      𝒟[dlogExperiment g (dlogReduction pos coef A)] {true} := by
  rw [prEvent_eq_evalDist_decide]
  simp only [joint, dlogExperiment, dlogReduction, answer, tForm, bind_assoc, pure_bind]

omit [Fintype F] [DecidableEq F] in
/-- The adversary wins in the joint run exactly as often as in the experiment: the programmed
oracle is uniform. -/
theorem prob_wins_eq {g : G} (hg : Function.Bijective (· • g : F → G))
    (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F) (A : Adversary F G Addr n) :
    Pr{let w ← joint g A}[Wins g pos coef (fun x => w.2.1 x • g + w.2.2.1 x • (w.1 • g)) w.2.2.2] =
      𝒟[experiment g pos coef A] {true} := by
  let k' : (Addr → G) → ProbComp Bool := fun H => do
    let out ← A.run H
    return decide (Wins g pos coef H out)
  have h : (joint g A >>= fun w =>
      return decide (Wins g pos coef (fun x => w.2.1 x • g + w.2.2.1 x • (w.1 • g)) w.2.2.2)) =ᵈ
      experiment g pos coef A := by
    simp only [joint, bind_assoc, pure_bind]
    refine EvalDistEq.trans (my := do
        let _y ← $ᵗ F; let _t ← $ᵗ (Addr → F); let H ← $ᵗ (Addr → G); k' H) ?_ ?_
    · refine EvalDistEq.bind_right _ fun y => ?_
      exact IndKey.reprogram_core hg (y • g) fun _ H => k' H
    · exact (bind_const_eqd _ _).trans (bind_const_eqd _ _)
  rw [prEvent_eq_evalDist_decide, h.evalDist_eq]

omit [DecidableEq G] in
/-- The linear form `∑ γᵢ t_{aᵢ}` vanishes with probability at most `1/|F|`: the oracle handed
to the adversary hides `t`. -/
theorem prob_tForm_le {g : G} (hg : Function.Bijective (· • g : F → G))
    (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F) (A : Adversary F G Addr n) :
    Pr{let w ← joint g A}[tForm pos coef w.2.2.1 w.2.2.2 = 0] ≤ (Fintype.card F : ℝ≥0∞)⁻¹ := by
  let proj : F × (Addr → F) × (Addr → F) × Out F G Addr n → (Addr → F) × Out F G Addr n :=
    fun w => (w.2.2.1, w.2.2.2)
  have hproj : Pr{let w ← joint g A}[tForm pos coef w.2.2.1 w.2.2.2 = 0] =
      Pr{let v ← proj <$> joint g A}[tForm pos coef v.1 v.2 = 0] := by
    rw [prEvent_map]
  have hdist : proj <$> joint g A =ᵈ (do
      let H ← $ᵗ (Addr → G); let out ← A.run H; let t ← $ᵗ (Addr → F)
      return (t, out)) := by
    have h0 : proj <$> joint g A = (do
        let y ← $ᵗ F; let u ← $ᵗ (Addr → F); let t ← $ᵗ (Addr → F)
        (do let out ← A.run fun x => u x • g + t x • (y • g); return (t, out))) := by
      simp [joint, proj, map_bind]
    rw [h0]
    refine EvalDistEq.trans (my := do
        let _y ← $ᵗ F; let t ← $ᵗ (Addr → F); let H ← $ᵗ (Addr → G)
        (do let out ← A.run H; return (t, out))) ?_ ?_
    · refine EvalDistEq.bind_right _ fun y => ?_
      exact IndKey.reprogram_core hg (y • g) fun t H => do let out ← A.run H; return (t, out)
    refine (bind_const_eqd _ _).trans ?_
    refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun H => ?_)
    exact bind_swap_eqd _ _ _
  rw [hproj, hdist.prEvent_eq (fun v => tForm pos coef v.1 v.2 = 0)]
  refine prEvent_bind_le_of_forall_le _ _ _ fun H => ?_
  refine prEvent_bind_le_of_forall_le _ _ _ fun out => ?_
  simp only [bind_pure_comp, prEvent_map, tForm]
  exact prob_linear_eq_zero_le (dependency_spec _).1 out.2.1.injective

/-- **Theorem 3** (Restricted Monitoring): no adversary can make `|V| + 1` addresses retrieve
audit keys whose secret keys it knows, except by solving discrete log or with probability
`1/|F|`. -/
theorem success_le {g : G} (hg : Function.Bijective (· • g : F → G))
    (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F) (A : Adversary F G Addr n) :
    𝒟[experiment g pos coef A] {true} ≤
      𝒟[dlogExperiment g (dlogReduction pos coef A)] {true} + (Fintype.card F : ℝ≥0∞)⁻¹ := by
  rw [← prob_wins_eq hg pos coef A, ← prob_answer_eq g pos coef A]
  calc Pr{let w ← joint g A}[
        Wins g pos coef (fun x => w.2.1 x • g + w.2.2.1 x • (w.1 • g)) w.2.2.2]
      ≤ Pr{let w ← joint g A}[answer pos coef w.2.1 w.2.2.1 w.2.2.2 = w.1 ∨
          tForm pos coef w.2.2.1 w.2.2.2 = 0] := by
        refine prEvent_mono _ _ _ fun w hw => ?_
        by_cases ht : tForm pos coef w.2.2.1 w.2.2.2 = 0
        · exact Or.inr ht
        · exact Or.inl (answer_eq_of_win hg.1 pos coef w.2.2.2.1 w.2.2.2.2.1 w.2.2.2.2.2 w.1
            w.2.1 w.2.2.1 hw ht)
    _ ≤ _ := prEvent_or_le _ _ _
    _ ≤ _ := by
        gcongr
        exact prob_tForm_le hg pos coef A

end AuditPay.RestrictedMonitoring
