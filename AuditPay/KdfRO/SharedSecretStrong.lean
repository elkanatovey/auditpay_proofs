/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.RestrictedMonitoring.SharedSecret
import AuditPay.KdfRO.StrongDH

/-!
# The shared-secret game with decision oracles, and its reduction to strong Diffie–Hellman

## The game

The shared-secret game of `AuditPay.RestrictedMonitoring.SharedSecret` (the adversary outputs an
arbitrary `V` and `n + 1` addresses, receives the ephemeral points `Rᵢ = rᵢ • g`, and must output
all `n + 1` shared points `rᵢ • (RetrieveKey(V, aᵢ) - H(aᵢ))`), where the adversary may in
addition **query** a decision oracle: on `(i, U, V)` it learns whether `V = rᵢ • U`. This is the
game the reduction of `AuditPay.Monitoring.StrongDH` plays: it uses the oracle to recognise the
shared points among the KDF queries of a decryption adversary.

## The reduction

On a strong Diffie–Hellman instance `(g, X, Y)` with the decision oracle `(U, V) ↦ [V = x • U]`,
program `H(z) = u_z • g + t_z • Y`, set `Rᵢ = X + sᵢ • g` for uniform `sᵢ` (so `rᵢ = x + sᵢ`), and
answer a decision query `(i, U, V)` by the query `(U, V - sᵢ • U)` to the strong Diffie–Hellman
oracle (`shift`). The answer is `SharedSecret.answer`; `SharedSecret.answer_eq_of_win` and the
hiding of `t` give `strong_success_le`:

  `Pr[win] ≤ Pr[StrongDH.experiment g (sdhReduction A) = true] + 1/|F|`.

As in `AuditPay.SharedKeyOW`, the proof goes through a `Kernel` whose second phase may depend on
the ephemeral scalars, which is how the oracle enters once the experiment has answered it.
-/

open OracleComp OracleSpec DiffieHellman ENNReal

namespace AuditPay.RestrictedMonitoring.SharedSecret

/-- The decision oracles of the shared-secret game with decision oracles: a query `(i, U, V)`
asks whether `V = rᵢ • U`. -/
abbrev multiSpec (n : ℕ) (G : Type) : OracleSpec (Fin (n + 1) × G × G) :=
  (Fin (n + 1) × G × G) →ₒ Bool

/-- A shared-secret adversary with decision oracles for the ephemeral scalars. -/
structure StrongAdversary (G Addr σ : Type) (n : ℕ) where
  /-- Given `H`, output a vector `V`, `n + 1` distinct addresses, and a state. -/
  commit : (Addr → G) → ProbComp (Commit G Addr σ n)
  /-- Given the state and the ephemeral keys `Rᵢ`, output the shared points `Kᵢ`, with oracle
  access to the decision oracles `(i, U, V) ↦ [V = rᵢ • U]`. -/
  respond : σ → (Fin (n + 1) → G) → OracleComp (unifSpec + multiSpec n G) (Fin (n + 1) → G)

/-- Proof device: a shared-secret adversary whose second phase is a `ProbComp` that may depend
on the ephemeral scalars (its last argument). -/
structure Kernel (F G Addr σ : Type) (n : ℕ) where
  /-- Given `H`, output a vector `V`, `n + 1` distinct addresses, and a state. -/
  commit : (Addr → G) → ProbComp (Commit G Addr σ n)
  /-- Given the state, the ephemeral keys and the ephemeral scalars, output the shared points. -/
  respond : σ → (Fin (n + 1) → G) → (Fin (n + 1) → F) → ProbComp (Fin (n + 1) → G)

variable {F G Addr σ : Type} {k n : ℕ} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]
  [Fintype Addr] [DecidableEq Addr]

/-- The decision oracles for the ephemeral scalars `r`: a query `(i, U, V)` is answered by
whether `V = rᵢ • U`. -/
def multiImpl (r : Fin (n + 1) → F) : QueryImpl (unifSpec + multiSpec n G) ProbComp :=
  unifFwdAnswerImpl (QueryImpl.ofFn fun q : Fin (n + 1) × G × G => decide (q.2.2 = r q.1 • q.2.1))

omit [Fintype F] [DecidableEq F] [SampleableType F] [SampleableType G] in
@[simp]
theorem simulateQ_multiImpl_liftM {α : Type} (r : Fin (n + 1) → F) (pc : ProbComp α) :
    simulateQ (multiImpl (G := G) r) (liftM pc : OracleComp (unifSpec + multiSpec n G) α) = pc := by
  simp [multiImpl, unifFwdAnswerImpl, QueryImpl.simulateQ_add_liftM_left]

omit [Fintype F] [DecidableEq F] [SampleableType F] [SampleableType G] in
@[simp]
theorem simulateQ_multiImpl_query (r : Fin (n + 1) → F) (i : Fin (n + 1)) (U V : G) :
    simulateQ (multiImpl (G := G) r)
        (query (spec := multiSpec n G) (i, U, V) : OracleComp (unifSpec + multiSpec n G) Bool) =
      pure (decide (V = r i • U)) := by
  simp only [multiImpl, unifFwdAnswerImpl, QueryImpl.passthrough_add]
  erw [QueryImpl.simulateQ_add_liftM_query_right]
  rfl

/-- The shared-secret experiment with decision oracles. -/
noncomputable def strongExperiment (g : G) (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F)
    (A : StrongAdversary G Addr σ n) : ProbComp Bool := do
  let H ← $ᵗ (Addr → G)
  let c ← A.commit H
  let r ← $ᵗ (Fin (n + 1) → F)
  let K ← simulateQ (multiImpl r) (A.respond c.2.2 fun i => r i • g)
  return decide (∀ i, K i = encPoint (r i) (retrieveKey pos coef c.1 (c.2.1 i)) (H (c.2.1 i)))

/-- Translating the decision oracles for `rᵢ = x + sᵢ` into the strong Diffie–Hellman oracle for
`x`: `V = (x + sᵢ) • U` iff `V - sᵢ • U = x • U`. -/
def shift (s : Fin (n + 1) → F) :
    QueryImpl (unifSpec + multiSpec n G) (OracleComp (unifSpec + StrongDH.oracleSpec G)) :=
  fun t => match t with
    | Sum.inl m => liftM ((unifSpec + StrongDH.oracleSpec G).query (Sum.inl m))
    | Sum.inr q => query (spec := StrongDH.oracleSpec G) (q.2.1, q.2.2 - s q.1 • q.2.1)

omit [Fintype F] [DecidableEq F] [SampleableType F] [SampleableType G] in
/-- Against the strong Diffie–Hellman oracle for `x`, the translated oracles are the decision
oracles for `x + sᵢ`. -/
theorem simulateQ_oracleImpl_shift {α : Type} (x : F) (s : Fin (n + 1) → F)
    (oa : OracleComp (unifSpec + multiSpec n G) α) :
    simulateQ (StrongDH.oracleImpl x) (simulateQ (shift s) oa) =
      simulateQ (multiImpl fun i => x + s i) oa := by
  refine QueryImpl.simulateQ_simulateQ_eq_of_apply (fun t => ?_) oa
  rcases t with m | ⟨i, U, V⟩
  · simp [shift, multiImpl, unifFwdAnswerImpl, StrongDH.oracleImpl]
  · simp only [shift, multiImpl, unifFwdAnswerImpl]
    rw [StrongDH.simulateQ_oracleImpl_query]
    have : (V - s i • U = x • U) ↔ (V = (x + s i) • U) := by
      rw [add_smul, sub_eq_iff_eq_add]
    rw [decide_eq_decide.2 this]
    rfl

/-- The strong Diffie–Hellman reduction for the shared-secret game with decision oracles. -/
noncomputable def sdhReduction (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F)
    (A : StrongAdversary G Addr σ n) : StrongDH.Adversary F G := fun g X Y => do
  let u ← $ᵗ (Addr → F)
  let t ← $ᵗ (Addr → F)
  let c ← A.commit fun z => u z • g + t z • Y
  let s ← $ᵗ (Fin (n + 1) → F)
  let K ← simulateQ (shift s) (A.respond c.2.2 fun i => X + s i • g)
  return answer pos coef g X Y u t c.1 c.2.1 s K

/-! ## Kernels -/

/-- The kernel of an adversary with decision oracles. -/
def StrongAdversary.kernel (A : StrongAdversary G Addr σ n) : Kernel F G Addr σ n where
  commit := A.commit
  respond st R r := simulateQ (multiImpl r) (A.respond st R)

/-- The shared-secret experiment of a kernel. -/
noncomputable def Kernel.experiment (g : G) (pos : Addr → Fin k → Fin n)
    (coef : Addr → Fin k → F) (A : Kernel F G Addr σ n) : ProbComp Bool := do
  let H ← $ᵗ (Addr → G)
  let c ← A.commit H
  let r ← $ᵗ (Fin (n + 1) → F)
  let K ← A.respond c.2.2 (fun i => r i • g) r
  return decide (∀ i, K i = encPoint (r i) (retrieveKey pos coef c.1 (c.2.1 i)) (H (c.2.1 i)))

/-- The reduction's run for a kernel, on the Diffie–Hellman instance `(g, x • g, y • g)`. -/
noncomputable def Kernel.cdhRun (g : G) (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F)
    (A : Kernel F G Addr σ n) : ProbComp Bool := do
  let x ← $ᵗ F
  let y ← $ᵗ F
  let u ← $ᵗ (Addr → F)
  let t ← $ᵗ (Addr → F)
  let c ← A.commit fun z => u z • g + t z • (y • g)
  let s ← $ᵗ (Fin (n + 1) → F)
  let K ← A.respond c.2.2 (fun i => x • g + s i • g) (fun i => x + s i)
  return decide (answer pos coef g (x • g) (y • g) u t c.1 c.2.1 s K = (x * y) • g)

omit [Fintype F] [DecidableEq F] in
theorem strongExperiment_eq_kernel (g : G) (pos : Addr → Fin k → Fin n)
    (coef : Addr → Fin k → F) (A : StrongAdversary G Addr σ n) :
    strongExperiment g pos coef A = A.kernel.experiment g pos coef := rfl

omit [SampleableType G] in
theorem sdhExperiment_eq_kernel (g : G) (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F)
    (A : StrongAdversary G Addr σ n) :
    StrongDH.experiment g (sdhReduction pos coef A) = A.kernel.cdhRun g pos coef := by
  simp only [StrongDH.experiment, sdhReduction, Kernel.cdhRun, StrongAdversary.kernel,
    simulateQ_bind, StrongDH.simulateQ_oracleImpl_liftM, simulateQ_pure, bind_assoc, pure_bind,
    simulateQ_oracleImpl_shift]

/-! ## The joint run of the reduction, for kernels -/

/-- A run of the reduction on the Diffie–Hellman instance `(g, x • g, y • g)`
(`SharedSecret.Run`), produced by a kernel. -/
noncomputable def Kernel.joint (g : G) (A : Kernel F G Addr σ n) : ProbComp (Run F G Addr σ n) := do
  let x ← $ᵗ F
  let y ← $ᵗ F
  let u ← $ᵗ (Addr → F)
  let t ← $ᵗ (Addr → F)
  let c ← A.commit fun z => u z • g + t z • (y • g)
  let s ← $ᵗ (Fin (n + 1) → F)
  let K ← A.respond c.2.2 (fun i => x • g + s i • g) (fun i => x + s i)
  return ⟨x, y, u, t, c, s, K⟩

omit [SampleableType G] in
/-- The reduction's success probability is that of its answer being `(x * y) • g` in the joint
run. -/
theorem Kernel.prob_answer_eq (g : G) (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F)
    (A : Kernel F G Addr σ n) :
    Pr{let w ← Kernel.joint g A}[
        answer pos coef g (w.x • g) (w.y • g) w.u w.t w.c.1 w.c.2.1 w.s w.K = (w.x * w.y) • g] =
      𝒟[A.cdhRun g pos coef] {true} := by
  rw [prEvent_eq_evalDist_decide]
  simp only [joint, Kernel.cdhRun, bind_assoc, pure_bind]

omit [Fintype F] [DecidableEq F] in
/-- The adversary wins in the joint run exactly as often as in the experiment: the programmed
oracle is uniform, and so are the ephemeral scalars `x + sᵢ`. -/
theorem Kernel.prob_wins_eq {g : G} (hg : Function.Bijective (· • g : F → G))
    (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F) (A : Kernel F G Addr σ n) :
    Pr{let w ← Kernel.joint g A}[Wins g pos coef w] = 𝒟[A.experiment g pos coef] {true} := by
  let body : (Addr → G) → Commit G Addr σ n → (Fin (n + 1) → F) → ProbComp Bool :=
    fun H c r => do
      let K ← A.respond c.2.2 (fun i => r i • g) r
      return decide (∀ i, K i =
        encPoint (r i) (retrieveKey pos coef c.1 (c.2.1 i)) (H (c.2.1 i)))
  let k' : F → (Addr → G) → ProbComp Bool := fun x H => do
    let c ← A.commit H
    let s ← $ᵗ (Fin (n + 1) → F)
    body H c fun i => x + s i
  have h : (Kernel.joint g A >>= fun w => return decide (Wins g pos coef w)) =ᵈ
      A.experiment g pos coef := by
    have h0 : (Kernel.joint g A >>= fun w => return decide (Wins g pos coef w)) = (do
        let x ← $ᵗ F; let y ← $ᵗ F; let u ← $ᵗ (Addr → F); let t ← $ᵗ (Addr → F)
        k' x fun z => u z • g + t z • (y • g)) := by
      simp only [Kernel.joint, bind_assoc, pure_bind, ← add_smul]
      rfl
    rw [h0]
    refine (IndKey.reprogram hg k').trans ?_
    simp only [Kernel.experiment, k']
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
theorem Kernel.prob_tForm_le {g : G} (hg : Function.Bijective (· • g : F → G))
    (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F) (A : Kernel F G Addr σ n) :
    Pr{let w ← Kernel.joint g A}[tForm pos coef w.t w.c.2.1 = 0] ≤ (Fintype.card F : ℝ≥0∞)⁻¹ := by
  let proj : Run F G Addr σ n → (Addr → F) × Commit G Addr σ n := fun w => (w.t, w.c)
  have hproj : Pr{let w ← Kernel.joint g A}[tForm pos coef w.t w.c.2.1 = 0] =
      Pr{let v ← proj <$> Kernel.joint g A}[tForm pos coef v.1 v.2.2.1 = 0] := by
    rw [prEvent_map]
  have hdist : proj <$> Kernel.joint g A =ᵈ (do
      let H ← $ᵗ (Addr → G); let c ← A.commit H; let t ← $ᵗ (Addr → F)
      return (t, c)) := by
    have h0 : proj <$> Kernel.joint g A = (do
        let x ← $ᵗ F; let y ← $ᵗ F; let u ← $ᵗ (Addr → F); let t ← $ᵗ (Addr → F)
        (do
          let c ← A.commit fun z => u z • g + t z • (y • g)
          let s ← $ᵗ (Fin (n + 1) → F)
          let _K ← A.respond c.2.2 (fun i => x • g + s i • g) (fun i => x + s i)
          return (t, c))) := by
      simp [Kernel.joint, proj, map_bind]
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
  exact RestrictedMonitoring.prob_linear_eq_zero_le (dependency_spec _).1 c.2.1.injective

/-- The shared-secret game for kernels. -/
theorem Kernel.success_le {g : G} (hg : Function.Bijective (· • g : F → G))
    (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F) (A : Kernel F G Addr σ n) :
    𝒟[A.experiment g pos coef] {true} ≤
      𝒟[A.cdhRun g pos coef] {true} + (Fintype.card F : ℝ≥0∞)⁻¹ := by
  rw [← Kernel.prob_wins_eq hg pos coef A, ← Kernel.prob_answer_eq g pos coef A]
  calc Pr{let w ← Kernel.joint g A}[Wins g pos coef w]
      ≤ Pr{let w ← Kernel.joint g A}[
          answer pos coef g (w.x • g) (w.y • g) w.u w.t w.c.1 w.c.2.1 w.s w.K = (w.x * w.y) • g ∨
            tForm pos coef w.t w.c.2.1 = 0] := by
        refine prEvent_mono _ _ _ fun w hw => ?_
        by_cases ht : tForm pos coef w.t w.c.2.1 = 0
        · exact Or.inr ht
        · exact Or.inl (answer_eq_of_win g pos coef w.c.1 w.c.2.1 w.x w.y w.u w.t w.s w.K hw ht)
    _ ≤ _ := prEvent_or_le _ _ _
    _ ≤ _ := by
        gcongr
        exact Kernel.prob_tForm_le hg pos coef A

/-- **The shared-secret game with decision oracles.** For a generator `g`, an adversary that may
test whether `V = rᵢ • U` for pairs `(U, V)` of its choice outputs all `n + 1` shared points with
probability at most the strong Diffie–Hellman success probability of `sdhReduction A` plus
`1/|F|`. -/
theorem strong_success_le {g : G} (hg : Function.Bijective (· • g : F → G))
    (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F) (A : StrongAdversary G Addr σ n) :
    𝒟[strongExperiment g pos coef A] {true} ≤
      𝒟[StrongDH.experiment g (sdhReduction pos coef A)] {true} +
        (Fintype.card F : ℝ≥0∞)⁻¹ := by
  rw [strongExperiment_eq_kernel, sdhExperiment_eq_kernel]
  exact A.kernel.success_le hg pos coef

end AuditPay.RestrictedMonitoring.SharedSecret
