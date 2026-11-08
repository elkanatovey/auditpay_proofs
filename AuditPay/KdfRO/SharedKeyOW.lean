/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.IndKey
import AuditPay.KdfRO.StrongDH

/-!
# One-wayness of the shared key of selective encryption

## The game

This is the IND-Key game (Definition 1 of the paper, `AuditPay.IndKey`) with a *computational*
goal. The adversary is given the hash-to-curve oracle `H` and picks the audit-key address `a` and
the encryptor's address `a*`. The challenger samples an audit key for `a`
(`sk`, `AK_a = sk • g + H(a)`) and an ephemeral scalar `r`, and gives the adversary
`(sk, AK_a, R)` with `R = r • g`. The adversary wins if it **outputs the shared point**
`K = r • (AK_a - H(a*))` of Algorithm 2, line 16.

Differences from Definition 1: the adversary is not handed a candidate key and asked to tell it
from a uniform group element; it must compute the key itself. As in `AuditPay.IndKey`, the
adversary loses if it submits `a* = a` (then `K = sk • R` and it would win trivially). There is no
key-derivation function in this game.

## The statement

`success_le`: the adversary wins with probability at most the CDH success probability of
`cdhReduction A` plus `1/|F|`. No DDH assumption is used.

## The variant with a decision oracle

In `strongExperiment` the adversary may in addition **query** a decision oracle for the ephemeral
scalar: on `(U, V)` it learns whether `V = r • U`, so it can test candidates for `K` (query
`(AK_a - H(a*), K')`). `strong_success_le` bounds its success by the strong Diffie–Hellman
success probability (`AuditPay.StrongDH`) of `sdhReduction A` plus `1/|F|`. This is the form used
when the key-derivation function is a random oracle and the scheme is unchanged.

## The reduction

On a CDH instance `(g, X, Y)` program `H(z) = u_z • g + t_z • Y`, set `R = X`, and run the
adversary. If it outputs `K = x • (AK_a - H(a*))`, then
`K - (sk + u_a - u_{a*}) • X = (t_a - t_{a*}) • (x * y) • g`, which gives the CDH answer unless
`t_a = t_{a*}`; `H` hides `t`, so that has probability `1/|F|`. With the decision oracle, the
oracle for `r` is the strong Diffie–Hellman oracle for `x` itself, and queries are forwarded.

Both statements are instances of one lemma about a `Kernel`: a proof device in which the
adversary's guess is a `ProbComp` that may depend on the ephemeral scalar (which is how the
decision oracle enters once the experiment has answered its queries).
-/

open OracleComp OracleSpec DiffieHellman ENNReal

namespace AuditPay.SharedKeyOW

/-- A one-wayness adversary: first, given the random oracle `H`, it picks the audit-key address
`a` and the encryptor's address `a*`; then, from `(sk, AK_a, R)`, it outputs a group element. -/
structure Adversary (F G Addr σ : Type) where
  /-- Choose `(a, a*)` and a state, given the random oracle `H`. -/
  choose : (Addr → G) → ProbComp (Addr × Addr × σ)
  /-- Output a candidate for the shared point, from the state and `(sk, AK_a, R)`. -/
  guess : σ → F → G → G → ProbComp G

/-- A one-wayness adversary with oracle access to a decision oracle for the ephemeral scalar. -/
structure StrongAdversary (F G Addr σ : Type) where
  /-- Choose `(a, a*)` and a state, given the random oracle `H`. -/
  choose : (Addr → G) → ProbComp (Addr × Addr × σ)
  /-- Output a candidate for the shared point, from the state and `(sk, AK_a, R)`, with oracle
  access to the decision oracle `(U, V) ↦ [V = r • U]`. -/
  guess : σ → F → G → G → OracleComp (unifSpec + StrongDH.oracleSpec G) G

/-- Proof device: an adversary whose guess is a `ProbComp` that may depend on the ephemeral
scalar `r` (its last argument). `Adversary.kernel` ignores `r`; `StrongAdversary.kernel` uses it
only to answer decision queries. -/
structure Kernel (F G Addr σ : Type) where
  /-- Choose `(a, a*)` and a state, given the random oracle `H`. -/
  choose : (Addr → G) → ProbComp (Addr × Addr × σ)
  /-- Output a candidate for the shared point, from the state, `(sk, AK_a, R)` and `r`. -/
  guess : σ → F → G → G → F → ProbComp G

variable {F G Addr σ : Type} [Field F] [Fintype F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]
  [Fintype Addr] [DecidableEq Addr]

/-! ## The games -/

/-- The one-wayness experiment: the adversary wins if it outputs the shared point
`K = r • (AK_a - H(a*))` for its chosen `a ≠ a*`. -/
noncomputable def experiment (g : G) (A : Adversary F G Addr σ) : ProbComp Bool := do
  let H ← $ᵗ (Addr → G)
  let p ← A.choose H
  if p.1 = p.2.1 then return false else do
    let sk ← $ᵗ F
    let r ← $ᵗ F
    let K ← A.guess p.2.2 sk (auditKey g sk (H p.1)) (r • g)
    return decide (K = encPoint r (auditKey g sk (H p.1)) (H p.2.1))

/-- The one-wayness experiment with a decision oracle for the ephemeral scalar `r`: the
adversary's queries `(U, V)` are answered by whether `V = r • U`. -/
noncomputable def strongExperiment (g : G) (A : StrongAdversary F G Addr σ) : ProbComp Bool := do
  let H ← $ᵗ (Addr → G)
  let p ← A.choose H
  if p.1 = p.2.1 then return false else do
    let sk ← $ᵗ F
    let r ← $ᵗ F
    let K ← simulateQ (StrongDH.oracleImpl r) (A.guess p.2.2 sk (auditKey g sk (H p.1)) (r • g))
    return decide (K = encPoint r (auditKey g sk (H p.1)) (H p.2.1))

/-! ## The reductions -/

/-- The reductions' answer: from a correct shared point `K` for `R = X` and the programming
`H(z) = u_z • g + t_z • Y`, the Diffie–Hellman value is
`(t_a - t_{a*})⁻¹ • (K - (sk + u_a - u_{a*}) • X)`. -/
def answer (X : G) (u t : Addr → F) (a a' : Addr) (sk : F) (K : G) : G :=
  (t a - t a')⁻¹ • (K - (sk + u a - u a') • X)

/-- The CDH reduction for the one-wayness game. (It runs the adversary to the end even when the
adversary's choice is inadmissible; its output is then irrelevant.) -/
noncomputable def cdhReduction (A : Adversary F G Addr σ) : CDHAdversary F G := fun g X Y => do
  let u ← $ᵗ (Addr → F)
  let t ← $ᵗ (Addr → F)
  let p ← A.choose fun z => u z • g + t z • Y
  let sk ← $ᵗ F
  let K ← A.guess p.2.2 sk (auditKey g sk (u p.1 • g + t p.1 • Y)) X
  return answer X u t p.1 p.2.1 sk K

/-- The strong Diffie–Hellman reduction for the one-wayness game with a decision oracle. The
adversary's decision queries are forwarded unchanged to the reduction's own oracle: with `R = X`
the two oracles coincide. -/
noncomputable def sdhReduction (A : StrongAdversary F G Addr σ) : StrongDH.Adversary F G :=
  fun g X Y => do
    let u ← $ᵗ (Addr → F)
    let t ← $ᵗ (Addr → F)
    let p ← A.choose fun z => u z • g + t z • Y
    let sk ← $ᵗ F
    let K ← A.guess p.2.2 sk (auditKey g sk (u p.1 • g + t p.1 • Y)) X
    return answer X u t p.1 p.2.1 sk K

/-! ## Kernels -/

/-- The kernel of a plain adversary: the guess ignores the ephemeral scalar. -/
def Adversary.kernel (A : Adversary F G Addr σ) : Kernel F G Addr σ where
  choose := A.choose
  guess st sk ak R _ := A.guess st sk ak R

/-- The kernel of an adversary with a decision oracle: the ephemeral scalar answers the decision
queries. -/
def StrongAdversary.kernel (A : StrongAdversary F G Addr σ) : Kernel F G Addr σ where
  choose := A.choose
  guess st sk ak R r := simulateQ (StrongDH.oracleImpl r) (A.guess st sk ak R)

/-- The one-wayness experiment of a kernel. -/
noncomputable def Kernel.experiment (g : G) (A : Kernel F G Addr σ) : ProbComp Bool := do
  let H ← $ᵗ (Addr → G)
  let p ← A.choose H
  if p.1 = p.2.1 then return false else do
    let sk ← $ᵗ F
    let r ← $ᵗ F
    let K ← A.guess p.2.2 sk (auditKey g sk (H p.1)) (r • g) r
    return decide (K = encPoint r (auditKey g sk (H p.1)) (H p.2.1))

/-- The reduction's run for a kernel, on the Diffie–Hellman instance `(g, x • g, y • g)`. -/
noncomputable def Kernel.cdhRun (g : G) (A : Kernel F G Addr σ) : ProbComp Bool := do
  let x ← $ᵗ F
  let y ← $ᵗ F
  let u ← $ᵗ (Addr → F)
  let t ← $ᵗ (Addr → F)
  let p ← A.choose fun z => u z • g + t z • (y • g)
  let sk ← $ᵗ F
  let K ← A.guess p.2.2 sk (auditKey g sk (u p.1 • g + t p.1 • (y • g))) (x • g) x
  return decide (answer (x • g) u t p.1 p.2.1 sk K = (x * y) • g)

omit [Fintype F] in
theorem experiment_eq_kernel (g : G) (A : Adversary F G Addr σ) :
    experiment g A = A.kernel.experiment g := rfl

omit [Fintype F] in
theorem strongExperiment_eq_kernel (g : G) (A : StrongAdversary F G Addr σ) :
    strongExperiment g A = A.kernel.experiment g := rfl

omit [Fintype F] [SampleableType G] in
theorem cdhExperiment_eq_kernel (g : G) (A : Adversary F G Addr σ) :
    cdhExperiment g (cdhReduction A) = A.kernel.cdhRun g := by
  simp only [cdhExperiment, cdhReduction, Kernel.cdhRun, Adversary.kernel, bind_assoc, pure_bind]

omit [Fintype F] [SampleableType G] in
theorem sdhExperiment_eq_kernel (g : G) (A : StrongAdversary F G Addr σ) :
    StrongDH.experiment g (sdhReduction A) = A.kernel.cdhRun g := by
  simp only [StrongDH.experiment, sdhReduction, Kernel.cdhRun, StrongAdversary.kernel,
    simulateQ_bind, StrongDH.simulateQ_oracleImpl_liftM, simulateQ_pure, bind_assoc, pure_bind]

/-! ## Algebra: a correct shared point reveals the Diffie–Hellman value -/

omit [Fintype F] [SampleableType F] [SampleableType G] [DecidableEq G] [Fintype Addr]
  [DecidableEq Addr] in
/-- If `K` is the shared point for `R = x • g` against the programmed oracle
`H(z) = u_z • g + t_z • (y • g)`, and `t_a ≠ t_{a*}`, the reductions' answer is `(x * y) • g`. -/
theorem answer_eq_of_win (g : G) (x y sk : F) (u t : Addr → F) (a a' : Addr) (K : G)
    (hK : K = encPoint x (auditKey g sk (u a • g + t a • (y • g))) (u a' • g + t a' • (y • g)))
    (ht : t a ≠ t a') :
    answer (x • g) u t a a' sk K = (x * y) • g := by
  have hc : (t a - t a')⁻¹ * ((t a - t a') * (x * y)) = x * y := by
    have : t a - t a' ≠ 0 := sub_ne_zero.2 ht
    field_simp
  rw [answer, hK, encPoint, auditKey, ← hc]
  module

/-! ## The joint run of the reduction -/

/-- A run of the reduction on the Diffie–Hellman instance `(g, x • g, y • g)`. -/
structure Run (F G Addr σ : Type) where
  /-- The scalar `x` (the ephemeral scalar of the simulated game). -/
  x : F
  /-- The scalar `y`. -/
  y : F
  /-- The oracle programming `u`. -/
  u : Addr → F
  /-- The oracle programming `t`. -/
  t : Addr → F
  /-- The adversary's choice. -/
  p : Addr × Addr × σ
  /-- The audit secret key. -/
  sk : F
  /-- The adversary's output. -/
  K : G

/-- The adversary wins in a run of the reduction. -/
abbrev Wins (g : G) (w : Run F G Addr σ) : Prop :=
  w.p.1 ≠ w.p.2.1 ∧ w.K = encPoint w.x
    (auditKey g w.sk (w.u w.p.1 • g + w.t w.p.1 • (w.y • g)))
    (w.u w.p.2.1 • g + w.t w.p.2.1 • (w.y • g))

/-- The reduction run on a uniform Diffie–Hellman instance, recording all of its values. -/
noncomputable def joint (g : G) (A : Kernel F G Addr σ) : ProbComp (Run F G Addr σ) := do
  let x ← $ᵗ F
  let y ← $ᵗ F
  let u ← $ᵗ (Addr → F)
  let t ← $ᵗ (Addr → F)
  let p ← A.choose fun z => u z • g + t z • (y • g)
  let sk ← $ᵗ F
  let K ← A.guess p.2.2 sk (auditKey g sk (u p.1 • g + t p.1 • (y • g))) (x • g) x
  return ⟨x, y, u, t, p, sk, K⟩

omit [Fintype F] [SampleableType G] in
/-- The reduction's success probability is that of its answer being `(x * y) • g` in the joint
run. -/
theorem prob_answer_eq (g : G) (A : Kernel F G Addr σ) :
    Pr{let w ← joint g A}[answer (w.x • g) w.u w.t w.p.1 w.p.2.1 w.sk w.K = (w.x * w.y) • g] =
      𝒟[A.cdhRun g] {true} := by
  rw [prEvent_eq_evalDist_decide]
  simp only [joint, Kernel.cdhRun, bind_assoc, pure_bind]

omit [Fintype F] in
/-- The adversary wins in the joint run exactly as often as in the experiment: the programmed
oracle is uniform. -/
theorem prob_wins_eq {g : G} (hg : Function.Bijective (· • g : F → G)) (A : Kernel F G Addr σ) :
    Pr{let w ← joint g A}[Wins g w] = 𝒟[A.experiment g] {true} := by
  let k' : F → (Addr → G) → ProbComp Bool := fun x H => do
    let p ← A.choose H
    let sk ← $ᵗ F
    let K ← A.guess p.2.2 sk (auditKey g sk (H p.1)) (x • g) x
    return decide (p.1 ≠ p.2.1 ∧ K = encPoint x (auditKey g sk (H p.1)) (H p.2.1))
  have h : (joint g A >>= fun w => return decide (Wins g w)) =ᵈ A.experiment g := by
    have h0 : (joint g A >>= fun w => return decide (Wins g w)) = (do
        let x ← $ᵗ F; let y ← $ᵗ F; let u ← $ᵗ (Addr → F); let t ← $ᵗ (Addr → F)
        k' x fun z => u z • g + t z • (y • g)) := by
      simp only [joint, bind_assoc, pure_bind]
      rfl
    rw [h0]
    refine (IndKey.reprogram hg k').trans ?_
    simp only [Kernel.experiment, k']
    refine EvalDistEq.bind_right _ fun H => ?_
    refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun p => ?_)
    by_cases ha : p.1 = p.2.1
    · simp only [ha, ne_eq, not_true_eq_false, false_and, decide_false, ite_true]
      exact (EvalDistEq.bind_right _ fun x =>
        (EvalDistEq.bind_right _ fun sk => bind_const_eqd _ _).trans (bind_const_eqd _ _)).trans
          (bind_const_eqd _ _)
    · simp only [ha, ne_eq, not_false_eq_true, true_and, ite_false]
      exact bind_swap_eqd _ _ _
  rw [prEvent_eq_evalDist_decide, h.evalDist_eq]

omit [DecidableEq G] in
/-- The two (distinct) addresses receive colliding `t` values with probability at most `1/|F|`:
the oracle handed to the adversary hides `t`. -/
theorem prob_tDiff_le {g : G} (hg : Function.Bijective (· • g : F → G)) (A : Kernel F G Addr σ) :
    Pr{let w ← joint g A}[w.p.1 ≠ w.p.2.1 ∧ w.t w.p.1 = w.t w.p.2.1] ≤
      (Fintype.card F : ℝ≥0∞)⁻¹ := by
  let proj : Run F G Addr σ → (Addr → F) × (Addr × Addr × σ) := fun w => (w.t, w.p)
  let Bad' : (Addr → F) × (Addr × Addr × σ) → Prop := fun v =>
    v.2.1 ≠ v.2.2.1 ∧ v.1 v.2.1 = v.1 v.2.2.1
  have hproj : Pr{let w ← joint g A}[w.p.1 ≠ w.p.2.1 ∧ w.t w.p.1 = w.t w.p.2.1] =
      Pr{let v ← proj <$> joint g A}[Bad' v] := by
    rw [prEvent_map]
  have hdist : proj <$> joint g A =ᵈ (do
      let H ← $ᵗ (Addr → G); let p ← A.choose H; let t ← $ᵗ (Addr → F)
      return (t, p)) := by
    have h0 : proj <$> joint g A = (do
        let x ← $ᵗ F; let y ← $ᵗ F; let u ← $ᵗ (Addr → F); let t ← $ᵗ (Addr → F)
        (do
          let p ← A.choose fun z => u z • g + t z • (y • g)
          let sk ← $ᵗ F
          let _K ← A.guess p.2.2 sk (auditKey g sk (u p.1 • g + t p.1 • (y • g))) (x • g) x
          return (t, p))) := by
      simp [joint, proj, map_bind]
    rw [h0]
    refine EvalDistEq.trans (my := do
        let _x ← $ᵗ F; let y ← $ᵗ F; let u ← $ᵗ (Addr → F); let t ← $ᵗ (Addr → F)
        (do let p ← A.choose fun z => u z • g + t z • (y • g); return (t, p))) ?_ ?_
    · refine EvalDistEq.bind_right _ fun x => EvalDistEq.bind_right _ fun y =>
        EvalDistEq.bind_right _ fun u => EvalDistEq.bind_right _ fun t =>
          EvalDistEq.bind_right _ fun p => ?_
      exact (EvalDistEq.bind_right _ fun sk => bind_const_eqd _ _).trans (bind_const_eqd _ _)
    refine EvalDistEq.trans (my := do
        let _x ← $ᵗ F; let _y ← $ᵗ F; let t ← $ᵗ (Addr → F); let H ← $ᵗ (Addr → G)
        (do let p ← A.choose H; return (t, p))) ?_ ?_
    · refine EvalDistEq.bind_right _ fun x => EvalDistEq.bind_right _ fun y => ?_
      exact IndKey.reprogram_core hg (y • g) fun t H => do let p ← A.choose H; return (t, p)
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

/-- One-wayness for kernels: the experiment is won with probability at most that of the
reduction's run plus `1/|F|`. -/
theorem Kernel.success_le {g : G} (hg : Function.Bijective (· • g : F → G))
    (A : Kernel F G Addr σ) :
    𝒟[A.experiment g] {true} ≤ 𝒟[A.cdhRun g] {true} + (Fintype.card F : ℝ≥0∞)⁻¹ := by
  rw [← prob_wins_eq hg A, ← prob_answer_eq g A]
  calc Pr{let w ← joint g A}[Wins g w]
      ≤ Pr{let w ← joint g A}[
          answer (w.x • g) w.u w.t w.p.1 w.p.2.1 w.sk w.K = (w.x * w.y) • g ∨
            (w.p.1 ≠ w.p.2.1 ∧ w.t w.p.1 = w.t w.p.2.1)] := by
        refine prEvent_mono _ _ _ fun w hw => ?_
        by_cases ht : w.t w.p.1 = w.t w.p.2.1
        · exact Or.inr ⟨hw.1, ht⟩
        · exact Or.inl (answer_eq_of_win g w.x w.y w.sk w.u w.t w.p.1 w.p.2.1 w.K hw.2 ht)
    _ ≤ _ := prEvent_or_le _ _ _
    _ ≤ _ := by
        gcongr
        exact prob_tDiff_le hg A

/-! ## Main statements -/

/-- **One-wayness of the shared key** (the replacement for Theorem 1 that needs no DDH): for a
generator `g`, an adversary that is given `(sk, AK_a, R)` for its chosen `a ≠ a*` outputs the
shared point `r • (AK_a - H(a*))` with probability at most the CDH success probability of
`cdhReduction A` plus `1/|F|`. -/
theorem success_le {g : G} (hg : Function.Bijective (· • g : F → G))
    (A : Adversary F G Addr σ) :
    𝒟[experiment g A] {true} ≤
      𝒟[cdhExperiment g (cdhReduction A)] {true} + (Fintype.card F : ℝ≥0∞)⁻¹ := by
  rw [experiment_eq_kernel, cdhExperiment_eq_kernel]
  exact A.kernel.success_le hg

/-- **One-wayness of the shared key with a decision oracle**: an adversary that can also test
whether `V = r • U` for pairs `(U, V)` of its choice outputs the shared point with probability
at most the strong Diffie–Hellman success probability of `sdhReduction A` plus `1/|F|`. -/
theorem strong_success_le {g : G} (hg : Function.Bijective (· • g : F → G))
    (A : StrongAdversary F G Addr σ) :
    𝒟[strongExperiment g A] {true} ≤
      𝒟[StrongDH.experiment g (sdhReduction A)] {true} + (Fintype.card F : ℝ≥0∞)⁻¹ := by
  rw [strongExperiment_eq_kernel, sdhExperiment_eq_kernel]
  exact A.kernel.success_le hg

end AuditPay.SharedKeyOW
