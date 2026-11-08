/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.RestrictedMonitoring

/-!
# Theorem 3 (Restricted Monitoring): the shared-secret game

## The game

`AuditPay.RestrictedMonitoring.success_le` treats an adversary that *outputs audit secret keys*
for `|V| + 1` addresses. Definition 3 asks for less: the adversary only has to *decrypt*, and
an adversary that can decrypt need not know any secret key. The symmetric key of
a ciphertext is derived from the Diffie–Hellman point `K = r • (RetrieveKey(V, a) - H(a))`
(Algorithm 2, line 16). This file proves that no adversary can compute that point for all
`|V| + 1` ciphertexts, whatever `V` is. A key-output adversary can (`keyOutput_le`), so this
strengthens the key-output statement; the decryption game itself is in
`AuditPay.RestrictedMonitoring.Decrypt`.

The adversary is given the hash-to-curve oracle `H` and outputs an arbitrary vector `V` of size
`n` and `n + 1` distinct addresses `aᵢ`. The challenger samples independent uniform `rᵢ` and
publishes the ephemeral keys `Rᵢ = rᵢ • g`. The adversary wins if it outputs, for *every* `i`,
the shared point `Kᵢ = rᵢ • (RetrieveKey(V, aᵢ) - H(aᵢ))` of the selective encryption to `aᵢ`.

There is no restriction on how `V` is formed and no algebraic-group assumption. As in the
key-output game, `pos` and `coef` are arbitrary fixed functions and `H` is a random oracle.

## The reduction (to CDH, tight up to `1/|F|`)

On a CDH instance `(g, X = x • g, Y = y • g)`, program `H(z) = u_z • g + t_z • Y` and set
`Rᵢ = X + sᵢ • g` for uniform `sᵢ`, so that `rᵢ = x + sᵢ` are independent and uniform. Write
`Pᵢ = RetrieveKey(V, aᵢ) - H(aᵢ)`; the reduction can compute it. If the adversary wins,
`Kᵢ - sᵢ • Pᵢ = x • Pᵢ`. For a nonzero left-kernel vector `γ` of the `(n + 1) × n` encoding
matrix, `∑ γᵢ • RetrieveKey(V, aᵢ) = 0`, hence

  `∑ γᵢ • (Kᵢ - sᵢ • Pᵢ) = -x • ∑ γᵢ • H(aᵢ) = -(∑ γᵢ u_{aᵢ}) • X - (∑ γᵢ t_{aᵢ}) • (x * y) • g`,

which yields `(x * y) • g` unless `∑ γᵢ t_{aᵢ} = 0`. Since `H` hides `t`, that has probability
at most `1/|F|`.
-/

open OracleComp DiffieHellman ENNReal

namespace AuditPay.RestrictedMonitoring.SharedSecret

/-- The first-phase output of a shared-secret adversary: a vector `V` of size `n`, `n + 1`
distinct addresses, and a state for the second phase. -/
abbrev Commit (G Addr σ : Type) (n : ℕ) := (Fin n → G) × (Fin (n + 1) ↪ Addr) × σ

/-- A shared-secret adversary against Restricted Monitoring. -/
structure Adversary (G Addr σ : Type) (n : ℕ) where
  /-- Given `H`, output a vector `V`, `n + 1` distinct addresses, and a state. -/
  commit : (Addr → G) → ProbComp (Commit G Addr σ n)
  /-- Given the state and the ephemeral keys `Rᵢ`, output the shared points `Kᵢ`. -/
  respond : σ → (Fin (n + 1) → G) → ProbComp (Fin (n + 1) → G)

variable {F G Addr σ : Type} {k n : ℕ} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]
  [Fintype Addr] [DecidableEq Addr]

/-- The shared-secret experiment: the adversary wins if, for all `n + 1` addresses, it outputs
the Diffie–Hellman point `rᵢ • (RetrieveKey(V, aᵢ) - H(aᵢ))` of a selective encryption to `aᵢ`
with ephemeral key `Rᵢ = rᵢ • g`. -/
noncomputable def experiment (g : G) (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F)
    (A : Adversary G Addr σ n) : ProbComp Bool := do
  let H ← $ᵗ (Addr → G)
  let c ← A.commit H
  let r ← $ᵗ (Fin (n + 1) → F)
  let K ← A.respond c.2.2 fun i => r i • g
  return decide (∀ i, K i = encPoint (r i) (retrieveKey pos coef c.1 (c.2.1 i)) (H (c.2.1 i)))

/-- The linear form `∑ γᵢ t_{aᵢ}` that the reduction divides by, for the dependency `γ` of the
encoding matrix of the addresses `S`. -/
noncomputable def tForm (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F) (t : Addr → F)
    (S : Fin (n + 1) → Addr) : F :=
  ∑ i, dependency (coefMatrix pos coef S) i * t (S i)

/-- The reduction's answer, from its randomness `u, t, s`, the CDH instance `(g, X, Y)` and the
adversary's outputs: `-(∑ γᵢ t_{aᵢ})⁻¹ • (∑ γᵢ • (Kᵢ - sᵢ • Pᵢ) + (∑ γᵢ u_{aᵢ}) • X)` with
`Pᵢ = RetrieveKey(V, aᵢ) - H(aᵢ)`. -/
noncomputable def answer (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F) (g X Y : G)
    (u t : Addr → F) (V : Fin n → G) (S : Fin (n + 1) → Addr) (s : Fin (n + 1) → F)
    (K : Fin (n + 1) → G) : G :=
  (-(tForm pos coef t S)⁻¹) •
    (∑ i, dependency (coefMatrix pos coef S) i •
        (K i - s i • (retrieveKey pos coef V (S i) - (u (S i) • g + t (S i) • Y))) +
      (∑ i, dependency (coefMatrix pos coef S) i * u (S i)) • X)

/-- The CDH reduction for the shared-secret game. -/
noncomputable def cdhReduction (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F)
    (A : Adversary G Addr σ n) : CDHAdversary F G := fun g X Y => do
  let u ← $ᵗ (Addr → F)
  let t ← $ᵗ (Addr → F)
  let c ← A.commit fun z => u z • g + t z • Y
  let s ← $ᵗ (Fin (n + 1) → F)
  let K ← A.respond c.2.2 fun i => X + s i • g
  return answer pos coef g X Y u t c.1 c.2.1 s K

/-! ## Algebra: winning outputs reveal the Diffie–Hellman value -/

omit [SampleableType F] [SampleableType G] [DecidableEq G] [Fintype Addr] [DecidableEq Addr] in
/-- The dependency of the encoding matrix annihilates the retrieved keys, whatever `V` is. -/
theorem sum_dependency_smul_retrieveKey (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F)
    (V : Fin n → G) (S : Fin (n + 1) → Addr) :
    ∑ i, dependency (coefMatrix pos coef S) i • retrieveKey pos coef V (S i) = 0 := by
  have hγ := (dependency_spec (coefMatrix pos coef S)).2
  have hcol : ∀ j, ∑ i, dependency (coefMatrix pos coef S) i * coefMatrix pos coef S i j = 0 := by
    intro j
    simpa [Matrix.vecMul, dotProduct] using congrFun hγ j
  simp only [retrieveKey_eq_matVecG pos coef S V, matVecG, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, hcol, zero_smul, Finset.sum_const_zero]

omit [SampleableType F] [SampleableType G] [DecidableEq G] [Fintype Addr] [DecidableEq Addr] in
/-- If the adversary wins against the programmed oracle `H(z) = u_z • g + t_z • (y • g)` with
ephemeral scalars `rᵢ = x + sᵢ`, and `∑ γᵢ t_{aᵢ} ≠ 0`, the reduction's answer is the
Diffie–Hellman value `(x * y) • g`. -/
theorem answer_eq_of_win (g : G) (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F)
    (V : Fin n → G) (S : Fin (n + 1) → Addr) (x y : F) (u t : Addr → F) (s : Fin (n + 1) → F)
    (K : Fin (n + 1) → G)
    (hwin : ∀ i, K i = encPoint (x + s i) (retrieveKey pos coef V (S i))
      (u (S i) • g + t (S i) • (y • g)))
    (ht : tForm pos coef t S ≠ 0) :
    answer pos coef g (x • g) (y • g) u t V S s K = (x * y) • g := by
  set γ := dependency (coefMatrix pos coef S) with hγ
  set U := ∑ i, γ i * u (S i) with hU
  have hT : tForm pos coef t S = ∑ i, γ i * t (S i) := rfl
  have h1 : ∑ i, γ i • (K i - s i • (retrieveKey pos coef V (S i) -
      (u (S i) • g + t (S i) • (y • g)))) =
      x • ∑ i, γ i • (retrieveKey pos coef V (S i) - (u (S i) • g + t (S i) • (y • g))) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hwin i, encPoint]
    module
  have h2 : ∑ i, γ i • (retrieveKey pos coef V (S i) - (u (S i) • g + t (S i) • (y • g))) =
      -((U + tForm pos coef t S * y) • g) := by
    simp only [smul_sub, Finset.sum_sub_distrib]
    rw [sum_dependency_smul_retrieveKey, zero_sub, hT, hU, Finset.sum_mul,
      ← Finset.sum_add_distrib, Finset.sum_smul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    module
  have hc : -(tForm pos coef t S)⁻¹ * (x * -(U + tForm pos coef t S * y) + U * x) = x * y := by
    field_simp
    ring
  rw [answer, ← hγ, ← hU, h1, h2, ← hc]
  module

/-! ## The joint run of the reduction -/

/-- A run of the reduction on the CDH instance `(g, x • g, y • g)`. -/
structure Run (F G Addr σ : Type) (n : ℕ) where
  /-- The CDH scalar `x`. -/
  x : F
  /-- The CDH scalar `y`. -/
  y : F
  /-- The oracle programming `u`. -/
  u : Addr → F
  /-- The oracle programming `t`. -/
  t : Addr → F
  /-- The adversary's first-phase output. -/
  c : Commit G Addr σ n
  /-- The offsets of the ephemeral scalars: `rᵢ = x + sᵢ`. -/
  s : Fin (n + 1) → F
  /-- The adversary's second-phase output. -/
  K : Fin (n + 1) → G

/-- The oracle the reduction programs in a run. -/
def Run.oracle (g : G) (w : Run F G Addr σ n) : Addr → G :=
  fun z => w.u z • g + w.t z • (w.y • g)

/-- The adversary wins in a run of the reduction: every `Kᵢ` is the shared point for the
ephemeral scalar `x + sᵢ`. -/
abbrev Wins (g : G) (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F)
    (w : Run F G Addr σ n) : Prop :=
  ∀ i, w.K i = encPoint (w.x + w.s i) (retrieveKey pos coef w.c.1 (w.c.2.1 i))
    (w.oracle g (w.c.2.1 i))

/-- The reduction run on a uniform CDH instance, recording all of its values. -/
noncomputable def joint (g : G) (A : Adversary G Addr σ n) : ProbComp (Run F G Addr σ n) := do
  let x ← $ᵗ F
  let y ← $ᵗ F
  let u ← $ᵗ (Addr → F)
  let t ← $ᵗ (Addr → F)
  let c ← A.commit fun z => u z • g + t z • (y • g)
  let s ← $ᵗ (Fin (n + 1) → F)
  let K ← A.respond c.2.2 fun i => x • g + s i • g
  return ⟨x, y, u, t, c, s, K⟩

omit [SampleableType G] in
/-- The reduction's success probability is that of its answer being `(x * y) • g` in the joint
run. -/
theorem prob_answer_eq (g : G) (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F)
    (A : Adversary G Addr σ n) :
    Pr{let w ← joint g A}[answer pos coef g (w.x • g) (w.y • g) w.u w.t w.c.1 w.c.2.1 w.s w.K =
        (w.x * w.y) • g] =
      𝒟[cdhExperiment g (cdhReduction pos coef A)] {true} := by
  rw [prEvent_eq_evalDist_decide]
  simp only [joint, cdhExperiment, cdhReduction, bind_assoc, pure_bind]

omit [Fintype F] [DecidableEq F] in
/-- The adversary wins in the joint run exactly as often as in the experiment: the programmed
oracle is uniform, and so are the ephemeral scalars `x + sᵢ`. -/
theorem prob_wins_eq {g : G} (hg : Function.Bijective (· • g : F → G))
    (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F) (A : Adversary G Addr σ n) :
    Pr{let w ← joint g A}[Wins g pos coef w] = 𝒟[experiment g pos coef A] {true} := by
  -- the experiment after the commitment, as a function of the ephemeral scalars
  let body : (Addr → G) → Commit G Addr σ n → (Fin (n + 1) → F) → ProbComp Bool :=
    fun H c r => do
      let K ← A.respond c.2.2 fun i => r i • g
      return decide (∀ i, K i =
        encPoint (r i) (retrieveKey pos coef c.1 (c.2.1 i)) (H (c.2.1 i)))
  let k' : F → (Addr → G) → ProbComp Bool := fun x H => do
    let c ← A.commit H
    let s ← $ᵗ (Fin (n + 1) → F)
    body H c fun i => x + s i
  have h : (joint g A >>= fun w => return decide (Wins g pos coef w)) =ᵈ
      experiment g pos coef A := by
    have h0 : (joint g A >>= fun w => return decide (Wins g pos coef w)) = (do
        let x ← $ᵗ F; let y ← $ᵗ F; let u ← $ᵗ (Addr → F); let t ← $ᵗ (Addr → F)
        k' x fun z => u z • g + t z • (y • g)) := by
      simp only [joint, bind_assoc, pure_bind, ← add_smul]
      rfl
    rw [h0]
    refine (IndKey.reprogram hg k').trans ?_
    simp only [experiment, k']
    refine EvalDistEq.bind_right _ fun H => ?_
    refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun c => ?_)
    refine EvalDistEq.trans (my := do
        let _x ← $ᵗ F; let r ← $ᵗ (Fin (n + 1) → F); body H c r) ?_ (bind_const_eqd _ _)
    refine EvalDistEq.bind_right _ fun x => ?_
    exact uniform_bind_bij (e := fun (s : Fin (n + 1) → F) (i : Fin (n + 1)) => x + s i)
      (Equiv.piCongrRight fun _ : Fin (n + 1) => Equiv.addLeft x).bijective (body H c)
  rw [prEvent_eq_evalDist_decide, h.evalDist_eq]

omit [DecidableEq G] in
/-- The linear form `∑ γᵢ t_{aᵢ}` vanishes with probability at most `1/|F|`: the oracle handed
to the adversary hides `t`. -/
theorem prob_tForm_le {g : G} (hg : Function.Bijective (· • g : F → G))
    (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F) (A : Adversary G Addr σ n) :
    Pr{let w ← joint (F := F) g A}[tForm pos coef w.t w.c.2.1 = 0] ≤
      (Fintype.card F : ℝ≥0∞)⁻¹ := by
  let proj : Run F G Addr σ n → (Addr → F) × Commit G Addr σ n := fun w => (w.t, w.c)
  have hproj : Pr{let w ← joint (F := F) g A}[tForm pos coef w.t w.c.2.1 = 0] =
      Pr{let v ← proj <$> joint (F := F) g A}[tForm pos coef v.1 v.2.2.1 = 0] := by
    rw [prEvent_map]
  have hdist : proj <$> joint (F := F) g A =ᵈ (do
      let H ← $ᵗ (Addr → G); let c ← A.commit H; let t ← $ᵗ (Addr → F)
      return (t, c)) := by
    have h0 : proj <$> joint (F := F) g A = (do
        let x ← $ᵗ F; let y ← $ᵗ F; let u ← $ᵗ (Addr → F); let t ← $ᵗ (Addr → F)
        (do
          let c ← A.commit fun z => u z • g + t z • (y • g)
          let s ← $ᵗ (Fin (n + 1) → F)
          let _K ← A.respond c.2.2 fun i => x • g + s i • g
          return (t, c))) := by
      simp [joint, proj, map_bind]
    rw [h0]
    refine EvalDistEq.trans (my := do
        let _x ← $ᵗ F; let _y ← $ᵗ F; let u ← $ᵗ (Addr → F); let t ← $ᵗ (Addr → F)
        (do let c ← A.commit fun z => u z • g + t z • (_y • g); return (t, c))) ?_ ?_
    · refine EvalDistEq.bind_right _ fun x => EvalDistEq.bind_right _ fun y =>
        EvalDistEq.bind_right _ fun u => EvalDistEq.bind_right _ fun t =>
          EvalDistEq.bind_right _ fun c => ?_
      exact (EvalDistEq.bind_right _ fun s => bind_const_eqd _ _).trans (bind_const_eqd _ _)
    refine EvalDistEq.trans (my := do
        let _x ← $ᵗ F; let _y ← $ᵗ F; let t ← $ᵗ (Addr → F); let H ← $ᵗ (Addr → G)
        (do let c ← A.commit H; return (t, c))) ?_ ?_
    · refine EvalDistEq.bind_right _ fun x => EvalDistEq.bind_right _ fun y => ?_
      exact IndKey.reprogram_core hg (y • g) fun t H => do let c ← A.commit H; return (t, c)
    refine ((bind_const_eqd _ _).trans (bind_const_eqd _ _)).trans ?_
    refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun H => ?_)
    exact bind_swap_eqd _ _ _
  rw [hproj, hdist.prEvent_eq (fun v => tForm pos coef v.1 v.2.2.1 = 0)]
  refine prEvent_bind_le_of_forall_le _ _ _ fun H => ?_
  refine prEvent_bind_le_of_forall_le _ _ _ fun c => ?_
  simp only [bind_pure_comp, prEvent_map, tForm]
  exact prob_linear_eq_zero_le (dependency_spec _).1 c.2.1.injective

/-- **Theorem 3, shared-secret form** (Restricted Monitoring for arbitrary `V`): no adversary
can output a vector `V` and `|V| + 1` distinct addresses and then compute the Diffie–Hellman
points of selective encryptions to all of them, except by solving CDH or with probability
`1/|F|`. -/
theorem success_le {g : G} (hg : Function.Bijective (· • g : F → G))
    (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F) (A : Adversary G Addr σ n) :
    𝒟[experiment g pos coef A] {true} ≤
      𝒟[cdhExperiment g (cdhReduction pos coef A)] {true} + (Fintype.card F : ℝ≥0∞)⁻¹ := by
  rw [← prob_wins_eq hg pos coef A, ← prob_answer_eq g pos coef A]
  calc Pr{let w ← joint g A}[Wins g pos coef w]
      ≤ Pr{let w ← joint g A}[
          answer pos coef g (w.x • g) (w.y • g) w.u w.t w.c.1 w.c.2.1 w.s w.K = (w.x * w.y) • g ∨
            tForm pos coef w.t w.c.2.1 = 0] := by
        refine prEvent_mono _ _ _ fun w hw => ?_
        by_cases ht : tForm pos coef w.t w.c.2.1 = 0
        · exact Or.inr ht
        · exact Or.inl (answer_eq_of_win g pos coef w.c.1 w.c.2.1 w.x w.y w.u w.t w.s w.K hw ht)
    _ ≤ _ := prEvent_or_le _ _ _
    _ ≤ _ := by
        gcongr
        exact prob_tForm_le hg pos coef A

/-! ## Relation to the key-output game -/

/-- A key-output adversary (`RestrictedMonitoring.Adversary`) as a shared-secret adversary: it
keeps its claimed secret keys as state and answers `Kᵢ = skᵢ • Rᵢ` (Algorithm 2's `Decrypt`). -/
def ofKeyOutput (A : RestrictedMonitoring.Adversary F G Addr n) :
    Adversary G Addr (Fin (n + 1) → F) n where
  commit H := A.run H
  respond sk R := return fun i => decPoint (sk i) (R i)

omit [Fintype F] [DecidableEq F] in
/-- The shared-secret game is no harder to win than the key-output game: an adversary that
knows audit secret keys for all `n + 1` addresses computes all the shared points. Hence
`success_le` also bounds the key-output game, by CDH instead of DLog. -/
theorem keyOutput_le (g : G) (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F)
    (A : RestrictedMonitoring.Adversary F G Addr n) :
    𝒟[RestrictedMonitoring.experiment g pos coef A] {true} ≤
      𝒟[experiment g pos coef (ofKeyOutput A)] {true} := by
  have h : RestrictedMonitoring.experiment g pos coef A =ᵈ (do
      let H ← $ᵗ (Addr → G)
      let out ← A.run H
      let _r ← $ᵗ (Fin (n + 1) → F)
      return decide (∀ i, retrieveKey pos coef out.1 (out.2.1 i) =
        auditKey g (out.2.2 i) (H (out.2.1 i)))) := by
    simp only [RestrictedMonitoring.experiment]
    refine EvalDistEq.bind_right _ fun H => EvalDistEq.bind_right _ fun out => ?_
    exact (bind_const_eqd _ _).symm
  rw [h.evalDist_eq, ← prEvent_eq_evalDist_singleton, ← prEvent_eq_evalDist_singleton]
  simp only [experiment, ofKeyOutput, pure_bind]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun H => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun out => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun r => ?_
  refine prEvent_pure_le_pure _ _ _ _ fun hwin => ?_
  simp only [decide_eq_true_eq] at hwin ⊢
  intro i
  rw [hwin i, encPoint_auditKey]

end AuditPay.RestrictedMonitoring.SharedSecret
