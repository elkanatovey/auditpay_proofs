/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.SLINDRO.Defs
import AuditPay.SLINDDrop.HopDDH
import AuditPay.KdfRO.StrongDH

/-!
# One-wayness of the shared key in the SL-IND setting

## The game

The computational core of Theorem 2 with a random-oracle KDF: the one-wayness game of
`AuditPay.SharedKeyOW` (output the shared point of a selective encryption to an address whose
audit key you hold), in the setting of the SL-IND game, where the audit keys are published as
the vector `V` of the never-failing generation.

1. The challenger samples the hash-to-curve oracle `H` and gives it to the adversary, which
   chooses an ordered request `l`, audit secret keys `sk`, fill scalars `w`, a **target
   address** `a` and a state (`Choice`).
2. If `a` is a selected address (`a ∈ sel.select pos coef l`) the adversary loses: the auditor
   decrypts the ciphertexts of the addresses it monitors. Otherwise the challenger samples the
   ephemeral scalar `r` and gives the adversary `R = r • g`.
3. The adversary wins if it outputs the shared point `K = r • (RetrieveKey(V, a) - H(a))` of a
   selective encryption to `a` (Algorithm 2, line 16), where `V = encodeSet g H pos coef T sk|_T
   (w • g)` is the vector the challenger of the SL-IND game would publish for this choice.

In `strongExperiment` the adversary may in addition **query** a decision oracle for `r`: on
`(U, W)` it learns whether `W = r • U` (`AuditPay.StrongDH.oracleSpec`). The adversary chooses
everything the SL-IND adversary chooses, with the target in the role of the sender or the
recipient of the challenge withdrawal; the deposits, the base withdrawal, the other ciphertext
and the proof are not part of this game, because an adversary of the SL-IND game can simulate
them itself (see `AuditPay.SLINDRO.StrongDH`, `AuditPay.SLINDRO.Twin`).

## The statements

`success_le`: `Pr[win] ≤ CDH(cdhReduction A) + 1/|F|`;
`strong_success_le`: `Pr[win] ≤ sDH(sdhReduction A) + 1/|F|` with the decision oracle.

## The reduction

On a Diffie–Hellman instance `(g, X, Y)` program `H(z) = u_z • g + t_z • Y`, send `R = X`, and
run the adversary. With `ρ = w • g`, every entry of `V` is a known combination of `g` and `Y`,
and `RetrieveKey(V, a) - H(a) = α • g + β • Y` with `β = ∑_{z ∈ T} λ_z t_z - t_a`, where
`λ = row_a ᵥ* R` for a right inverse `R` of the encoding matrix of `T` (the algebra of
`AuditPay.SLINDDrop.HopDDH`). A correct `K = x • (α • g + β • Y)` then gives
`β⁻¹ • (K - α • X) = (x · y) • g`, unless `β = 0`; as `a ∉ T`, `t_a` is fresh and `H` hides `t`,
so `β = 0` has probability at most `1/|F|` (`prob_beta_le_finset`). With the decision oracle,
the oracle for `r` is the strong Diffie–Hellman oracle for `x` itself, and queries are
forwarded. As in `AuditPay.SharedKeyOW`, both statements are instances of one lemma about a
`Kernel`, an adversary whose guess is a `ProbComp` that may read the ephemeral scalar.
-/

open OracleComp OracleSpec DiffieHellman ENNReal

namespace AuditPay.SLINDRO.OW

/-- The one-wayness adversary's choice: an ordered request, audit secret keys, fill scalars,
the target address, and a state. -/
structure Choice (F Addr σ : Type) (n : ℕ) where
  /-- The ordered request `l`. -/
  req : List Addr
  /-- Audit secret keys; those of the selected addresses are used. -/
  sk : Addr → F
  /-- The fill scalars `w`. -/
  fill : Fin n → F
  /-- The target address: the shared point of a selective encryption to it is to be found. -/
  target : Addr
  /-- The adversary's state. -/
  state : σ

/-- A one-wayness adversary: given `H` it chooses a request, keys, fill, a target and a state;
given `R = r • g` it outputs a candidate for the shared point. -/
structure Adversary (F G Addr σ : Type) (n : ℕ) where
  /-- The choice, given `H`. -/
  choose : (Addr → G) → ProbComp (Choice F Addr σ n)
  /-- A candidate for the shared point, from the state and `R`. -/
  guess : σ → G → ProbComp G

/-- A one-wayness adversary with oracle access to the decision oracle `(U, W) ↦ [W = r • U]`
for the ephemeral scalar. -/
structure StrongAdversary (F G Addr σ : Type) (n : ℕ) where
  /-- The choice, given `H`. -/
  choose : (Addr → G) → ProbComp (Choice F Addr σ n)
  /-- A candidate for the shared point, from the state and `R`, with the decision oracle. -/
  guess : σ → G → OracleComp (unifSpec + StrongDH.oracleSpec G) G

/-- Proof device: an adversary whose guess may read the ephemeral scalar `r` (its last
argument). `Adversary.kernel` ignores it; `StrongAdversary.kernel` uses it to answer decision
queries. -/
structure Kernel (F G Addr σ : Type) (n : ℕ) where
  /-- The choice, given `H`. -/
  choose : (Addr → G) → ProbComp (Choice F Addr σ n)
  /-- A candidate for the shared point, from the state, `R` and `r`. -/
  guess : σ → G → F → ProbComp G

variable {F G Addr σ : Type} {k n : ℕ} [Field F] [Fintype F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]
  [Fintype Addr] [DecidableEq Addr]

section Choice

omit [Fintype F] [SampleableType F] [SampleableType G] [DecidableEq G] [Fintype Addr]

/-- The selected set `T = sel.select pos coef l` of a choice. -/
abbrev Choice.selected (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F)
    (sel : Selection F Addr k n) (p : Choice F Addr σ n) : Finset Addr :=
  sel.select pos coef p.req

/-- The vector `V` of a choice. -/
noncomputable def Choice.vec (g : G) (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F)
    (sel : Selection F Addr k n) (H : Addr → G) (p : Choice F Addr σ n) : Fin n → G :=
  auditVec g pos coef sel H p.req p.sk p.fill

/-- The point `RetrieveKey(V, a) - H(a)` that a selective encryption to the target is keyed
on. -/
noncomputable def Choice.pt (g : G) (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F)
    (sel : Selection F Addr k n) (H : Addr → G) (p : Choice F Addr σ n) : G :=
  retrieveKey pos coef (p.vec g pos coef sel H) p.target - H p.target

end Choice

variable (g : G) (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F)
  (sel : Selection F Addr k n)

/-! ## The games -/

/-- The one-wayness experiment: the adversary wins if its target is not selected and it outputs
the shared point `r • (RetrieveKey(V, a) - H(a))`. -/
noncomputable def experiment (A : Adversary F G Addr σ n) : ProbComp Bool := do
  let H ← $ᵗ (Addr → G)
  let p ← A.choose H
  if p.target ∈ p.selected pos coef sel then return false else do
    let r ← $ᵗ F
    let K ← A.guess p.state (r • g)
    return decide (K = r • p.pt g pos coef sel H)

/-- The one-wayness experiment with the decision oracle `(U, W) ↦ [W = r • U]` for the
ephemeral scalar. -/
noncomputable def strongExperiment (A : StrongAdversary F G Addr σ n) : ProbComp Bool := do
  let H ← $ᵗ (Addr → G)
  let p ← A.choose H
  if p.target ∈ p.selected pos coef sel then return false else do
    let r ← $ᵗ F
    let K ← simulateQ (StrongDH.oracleImpl r) (A.guess p.state (r • g))
    return decide (K = r • p.pt g pos coef sel H)

/-! ## The reductions -/

/-- Coefficients of the selected audit keys in `RetrieveKey(V, a)`: `λ = row_a ᵥ* R`, where `R`
is the right inverse of the encoding matrix of the selected set. -/
noncomputable def keyCoeffs (p : Choice F Addr σ n) : p.selected pos coef sel → F :=
  Matrix.vecMul (coefRow pos coef p.target)
    (rightInv (setMatrix pos coef (p.selected pos coef sel)))

/-- The coefficient of `g` in `RetrieveKey(V, a) - H(a)` for the programmed oracle
`H(z) = u_z • g + t_z • Y`: `row_a · w + ∑_{z ∈ T} λ_z (sk_z + u_z - (M w)_z) - u_a`. -/
noncomputable def alpha (u : Addr → F) (p : Choice F Addr σ n) : F :=
  dotProduct (coefRow pos coef p.target) p.fill +
    ∑ z, keyCoeffs pos coef sel p z * (p.sk z + u z -
      Matrix.mulVec (setMatrix pos coef (p.selected pos coef sel)) p.fill z) - u p.target

/-- The coefficient of `Y` in `RetrieveKey(V, a) - H(a)` for the programmed oracle:
`∑_{z ∈ T} λ_z t_z - t_a`. -/
noncomputable def beta (t : Addr → F) (p : Choice F Addr σ n) : F :=
  ∑ z, keyCoeffs pos coef sel p z * t z - t p.target

/-- The reductions' answer: from a correct shared point `K` for `R = X`, the Diffie–Hellman
value is `β⁻¹ • (K - α • X)`. -/
noncomputable def answer (X : G) (u t : Addr → F) (p : Choice F Addr σ n) (K : G) : G :=
  (beta pos coef sel t p)⁻¹ • (K - alpha pos coef sel u p • X)

/-- The CDH reduction for the one-wayness game. (It runs the adversary to the end even when the
target is selected; its output is then irrelevant.) -/
noncomputable def cdhReduction (A : Adversary F G Addr σ n) : CDHAdversary F G := fun g X Y => do
  let u ← $ᵗ (Addr → F)
  let t ← $ᵗ (Addr → F)
  let p ← A.choose fun z => u z • g + t z • Y
  let K ← A.guess p.state X
  return answer pos coef sel X u t p K

/-- The strong Diffie–Hellman reduction for the one-wayness game with a decision oracle. The
adversary's decision queries are forwarded unchanged: with `R = X` the two oracles coincide. -/
noncomputable def sdhReduction (A : StrongAdversary F G Addr σ n) : StrongDH.Adversary F G :=
  fun g X Y => do
    let u ← $ᵗ (Addr → F)
    let t ← $ᵗ (Addr → F)
    let p ← A.choose fun z => u z • g + t z • Y
    let K ← A.guess p.state X
    return answer pos coef sel X u t p K

/-! ## Kernels -/

/-- The kernel of a plain adversary: the guess ignores the ephemeral scalar. -/
def Adversary.kernel (A : Adversary F G Addr σ n) : Kernel F G Addr σ n where
  choose := A.choose
  guess st R _ := A.guess st R

/-- The kernel of an adversary with a decision oracle: the ephemeral scalar answers the
decision queries. -/
def StrongAdversary.kernel (A : StrongAdversary F G Addr σ n) : Kernel F G Addr σ n where
  choose := A.choose
  guess st R r := simulateQ (StrongDH.oracleImpl r) (A.guess st R)

/-- The one-wayness experiment of a kernel. -/
noncomputable def Kernel.experiment (A : Kernel F G Addr σ n) : ProbComp Bool := do
  let H ← $ᵗ (Addr → G)
  let p ← A.choose H
  if p.target ∈ p.selected pos coef sel then return false else do
    let r ← $ᵗ F
    let K ← A.guess p.state (r • g) r
    return decide (K = r • p.pt g pos coef sel H)

/-- The reduction's run for a kernel, on the Diffie–Hellman instance `(g, x • g, y • g)`. -/
noncomputable def Kernel.cdhRun (A : Kernel F G Addr σ n) : ProbComp Bool := do
  let x ← $ᵗ F
  let y ← $ᵗ F
  let u ← $ᵗ (Addr → F)
  let t ← $ᵗ (Addr → F)
  let p ← A.choose fun z => u z • g + t z • (y • g)
  let K ← A.guess p.state (x • g) x
  return decide (answer pos coef sel (x • g) u t p K = (x * y) • g)

omit [Fintype F] in
theorem experiment_eq_kernel (A : Adversary F G Addr σ n) :
    experiment g pos coef sel A = A.kernel.experiment g pos coef sel := rfl

omit [Fintype F] in
theorem strongExperiment_eq_kernel (A : StrongAdversary F G Addr σ n) :
    strongExperiment g pos coef sel A = A.kernel.experiment g pos coef sel := rfl

omit [Fintype F] [SampleableType G] in
theorem cdhExperiment_eq_kernel (A : Adversary F G Addr σ n) :
    cdhExperiment g (cdhReduction pos coef sel A) = A.kernel.cdhRun g pos coef sel := by
  simp only [cdhExperiment, cdhReduction, Kernel.cdhRun, Adversary.kernel, bind_assoc, pure_bind]

omit [Fintype F] [SampleableType G] in
theorem sdhExperiment_eq_kernel (A : StrongAdversary F G Addr σ n) :
    StrongDH.experiment g (sdhReduction pos coef sel A) = A.kernel.cdhRun g pos coef sel := by
  simp only [StrongDH.experiment, sdhReduction, Kernel.cdhRun, StrongAdversary.kernel,
    simulateQ_bind, StrongDH.simulateQ_oracleImpl_liftM, simulateQ_pure, bind_assoc, pure_bind]

/-! ## Algebra: the programmed vector, and a correct shared point reveals the DH value -/

section Algebra

omit [Fintype F] [SampleableType F] [SampleableType G] [DecidableEq G] [Fintype Addr]

/-- The vector for the programmed oracle `H(z) = u_z • g + t_z • Y` and the fill `w • g`:
`V_j = (w_j + (R *ᵥ d)_j) • g + (R *ᵥ t|_T)_j • Y` with `d_z = sk_z + u_z - (M *ᵥ w)_z`
(`AuditPay.SLINDDrop.auditVec_programmed`, for this generation). -/
theorem auditVec_programmed (l : List Addr) (sk : Addr → F) (w : Fin n → F) (u t : Addr → F)
    (Y : G) :
    auditVec g pos coef sel (fun z => u z • g + t z • Y) l sk w = fun j =>
      (w + Matrix.mulVec (rightInv (setMatrix pos coef (sel.select pos coef l)))
        (fun z => sk z + u z - Matrix.mulVec (setMatrix pos coef (sel.select pos coef l)) w z)) j •
        g +
      Matrix.mulVec (rightInv (setMatrix pos coef (sel.select pos coef l))) (fun z => t z) j •
        Y := by
  set T := sel.select pos coef l
  set M := setMatrix pos coef T
  set R := rightInv M
  have h1 : setAuditKeys g (fun z => u z • g + t z • Y) T (fun a => sk a) -
      matVecG M (fun j => w j • g) =
      fun z : T => (sk z + u z - Matrix.mulVec M w z) • g + t z • Y := by
    rw [SLINDDrop.matVecG_smul]
    funext z
    simp only [setAuditKeys, auditKey, Pi.sub_apply]
    module
  simp only [auditVec, encodeSet, rectSolve]
  rw [h1, SLINDDrop.matVecG_smul_add]
  funext j
  simp only [Pi.add_apply]
  module

/-- The target's point for the programmed oracle: `α • g + β • Y`. -/
theorem pt_programmed (p : Choice F Addr σ n) (u t : Addr → F) (Y : G) :
    p.pt g pos coef sel (fun z => u z • g + t z • Y) =
      alpha pos coef sel u p • g + beta pos coef sel t p • Y := by
  rw [Choice.pt, Choice.vec, retrieveKey_eq_sum_coefRow, auditVec_programmed,
    SLINDDrop.sum_smul_smul_add, dotProduct_add, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec]
  simp only [alpha, beta, keyCoeffs, Choice.selected, dotProduct]
  module

/-- If `K` is the shared point for `R = x • g` against the programmed oracle
`H(z) = u_z • g + t_z • (y • g)`, and `β ≠ 0`, the reductions' answer is `(x * y) • g`. -/
theorem answer_eq_of_win (x y : F) (u t : Addr → F) (p : Choice F Addr σ n) (K : G)
    (hK : K = x • p.pt g pos coef sel fun z => u z • g + t z • (y • g))
    (hβ : beta pos coef sel t p ≠ 0) :
    answer pos coef sel (x • g) u t p K = (x * y) • g := by
  have hc : (beta pos coef sel t p)⁻¹ * (beta pos coef sel t p * (x * y)) = x * y := by
    field_simp
  rw [answer, hK, pt_programmed, ← hc]
  module

end Algebra

/-! ## The joint run of the reduction -/

/-- A run of the reduction on the Diffie–Hellman instance `(g, x • g, y • g)`. -/
structure Run (F G Addr σ : Type) (n : ℕ) where
  /-- The scalar `x` (the ephemeral scalar of the simulated game). -/
  x : F
  /-- The scalar `y`. -/
  y : F
  /-- The oracle programming `u`. -/
  u : Addr → F
  /-- The oracle programming `t`. -/
  t : Addr → F
  /-- The adversary's choice. -/
  p : Choice F Addr σ n
  /-- The adversary's output. -/
  K : G

/-- The adversary wins in a run of the reduction. -/
abbrev Wins (w : Run F G Addr σ n) : Prop :=
  w.p.target ∉ w.p.selected pos coef sel ∧
    w.K = w.x • w.p.pt g pos coef sel fun z => w.u z • g + w.t z • (w.y • g)

/-- The reduction run on a uniform Diffie–Hellman instance, recording all of its values. -/
noncomputable def joint (A : Kernel F G Addr σ n) : ProbComp (Run F G Addr σ n) := do
  let x ← $ᵗ F
  let y ← $ᵗ F
  let u ← $ᵗ (Addr → F)
  let t ← $ᵗ (Addr → F)
  let p ← A.choose fun z => u z • g + t z • (y • g)
  let K ← A.guess p.state (x • g) x
  return ⟨x, y, u, t, p, K⟩

omit [Fintype F] [SampleableType G] in
/-- The reduction's success probability is that of its answer being `(x * y) • g` in the joint
run. -/
theorem prob_answer_eq (A : Kernel F G Addr σ n) :
    Pr{let w ← joint g A}[answer pos coef sel (w.x • g) w.u w.t w.p w.K = (w.x * w.y) • g] =
      𝒟[A.cdhRun g pos coef sel] {true} := by
  rw [prEvent_eq_evalDist_decide]
  simp only [joint, Kernel.cdhRun, bind_assoc, pure_bind]

omit [Fintype F] in
/-- The adversary wins in the joint run exactly as often as in the experiment: the programmed
oracle is uniform. -/
theorem prob_wins_eq (hg : Function.Bijective (· • g : F → G)) (A : Kernel F G Addr σ n) :
    Pr{let w ← joint g A}[Wins g pos coef sel w] = 𝒟[A.experiment g pos coef sel] {true} := by
  let k' : F → (Addr → G) → ProbComp Bool := fun x H => do
    let p ← A.choose H
    let K ← A.guess p.state (x • g) x
    return decide (p.target ∉ p.selected pos coef sel ∧ K = x • p.pt g pos coef sel H)
  have h : (joint g A >>= fun w => return decide (Wins g pos coef sel w)) =ᵈ
      A.experiment g pos coef sel := by
    have h0 : (joint g A >>= fun w => return decide (Wins g pos coef sel w)) = (do
        let x ← $ᵗ F; let y ← $ᵗ F; let u ← $ᵗ (Addr → F); let t ← $ᵗ (Addr → F)
        k' x fun z => u z • g + t z • (y • g)) := by
      simp only [joint, bind_assoc, pure_bind]
      rfl
    rw [h0]
    refine (IndKey.reprogram hg k').trans ?_
    simp only [Kernel.experiment, k']
    refine EvalDistEq.bind_right _ fun H => ?_
    refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun p => ?_)
    by_cases ha : p.target ∈ p.selected pos coef sel
    · simp only [ha, not_true_eq_false, false_and, decide_false, ite_true]
      exact (EvalDistEq.bind_right _ fun x => bind_const_eqd _ _).trans (bind_const_eqd _ _)
    · simp only [ha, not_false_eq_true, true_and, ite_false]
      exact .rfl
  rw [prEvent_eq_evalDist_decide, h.evalDist_eq]

omit [DecidableEq G] in
/-- For an unselected target, `β = ∑_{z ∈ T} λ_z t_z - t_a` vanishes with probability at most
`1/|F|`: the oracle handed to the adversary hides `t`, and `t_a` does not occur in the sum. -/
theorem prob_beta_le (hg : Function.Bijective (· • g : F → G)) (A : Kernel F G Addr σ n) :
    Pr{let w ← joint g A}[w.p.target ∉ w.p.selected pos coef sel ∧
        beta pos coef sel w.t w.p = 0] ≤ (Fintype.card F : ℝ≥0∞)⁻¹ := by
  let proj : Run F G Addr σ n → (Addr → F) × Choice F Addr σ n := fun w => (w.t, w.p)
  let Bad' : (Addr → F) × Choice F Addr σ n → Prop := fun v =>
    v.2.target ∉ v.2.selected pos coef sel ∧ beta pos coef sel v.1 v.2 = 0
  have hproj : Pr{let w ← joint g A}[w.p.target ∉ w.p.selected pos coef sel ∧
      beta pos coef sel w.t w.p = 0] = Pr{let v ← proj <$> joint g A}[Bad' v] := by
    rw [prEvent_map]
  have hdist : proj <$> joint g A =ᵈ (do
      let H ← $ᵗ (Addr → G); let p ← A.choose H; let t ← $ᵗ (Addr → F)
      return (t, p)) := by
    have h0 : proj <$> joint g A = (do
        let x ← $ᵗ F; let y ← $ᵗ F; let u ← $ᵗ (Addr → F); let t ← $ᵗ (Addr → F)
        (do
          let p ← A.choose fun z => u z • g + t z • (y • g)
          let _K ← A.guess p.state (x • g) x
          return (t, p))) := by
      simp [joint, proj, map_bind]
    rw [h0]
    refine EvalDistEq.trans (my := do
        let _x ← $ᵗ F; let y ← $ᵗ F; let u ← $ᵗ (Addr → F); let t ← $ᵗ (Addr → F)
        (do let p ← A.choose fun z => u z • g + t z • (y • g); return (t, p))) ?_ ?_
    · refine EvalDistEq.bind_right _ fun x => EvalDistEq.bind_right _ fun y =>
        EvalDistEq.bind_right _ fun u => EvalDistEq.bind_right _ fun t =>
          EvalDistEq.bind_right _ fun p => ?_
      exact bind_const_eqd _ _
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
  by_cases ha : p.target ∈ p.selected pos coef sel
  · simp [Bad', ha]
  · simp only [Bad', ha, not_false_eq_true, true_and, bind_pure_comp, prEvent_map, beta]
    exact SLINDDrop.prob_beta_le_finset _ _ ha

/-- One-wayness for kernels: the experiment is won with probability at most that of the
reduction's run plus `1/|F|`. -/
theorem Kernel.success_le (hg : Function.Bijective (· • g : F → G)) (A : Kernel F G Addr σ n) :
    𝒟[A.experiment g pos coef sel] {true} ≤
      𝒟[A.cdhRun g pos coef sel] {true} + (Fintype.card F : ℝ≥0∞)⁻¹ := by
  rw [← prob_wins_eq g pos coef sel hg A, ← prob_answer_eq g pos coef sel A]
  calc Pr{let w ← joint g A}[Wins g pos coef sel w]
      ≤ Pr{let w ← joint g A}[
          answer pos coef sel (w.x • g) w.u w.t w.p w.K = (w.x * w.y) • g ∨
            (w.p.target ∉ w.p.selected pos coef sel ∧ beta pos coef sel w.t w.p = 0)] := by
        refine prEvent_mono _ _ _ fun w hw => ?_
        by_cases hβ : beta pos coef sel w.t w.p = 0
        · exact Or.inr ⟨hw.1, hβ⟩
        · exact Or.inl (answer_eq_of_win g pos coef sel w.x w.y w.u w.t w.p w.K hw.2 hβ)
    _ ≤ _ := prEvent_or_le _ _ _
    _ ≤ _ := by
        gcongr
        exact prob_beta_le g pos coef sel hg A

/-! ## Main statements -/

/-- **One-wayness of the shared key in the SL-IND setting**: for a generator `g`, an adversary
that chooses the request, the audit secret keys, the fill scalars and an unselected target
address after seeing `H`, and then receives `R = r • g`, outputs the shared point
`r • (RetrieveKey(V, a) - H(a))` with probability at most the CDH success probability of
`cdhReduction A` plus `1/|F|`. -/
theorem success_le (hg : Function.Bijective (· • g : F → G)) (A : Adversary F G Addr σ n) :
    𝒟[experiment g pos coef sel A] {true} ≤
      𝒟[cdhExperiment g (cdhReduction pos coef sel A)] {true} + (Fintype.card F : ℝ≥0∞)⁻¹ := by
  rw [experiment_eq_kernel, cdhExperiment_eq_kernel]
  exact A.kernel.success_le g pos coef sel hg

/-- **One-wayness of the shared key in the SL-IND setting, with a decision oracle**: an
adversary that can also test whether `W = r • U` for pairs `(U, W)` of its choice outputs the
shared point with probability at most the strong Diffie–Hellman success probability of
`sdhReduction A` plus `1/|F|`. -/
theorem strong_success_le (hg : Function.Bijective (· • g : F → G))
    (A : StrongAdversary F G Addr σ n) :
    𝒟[strongExperiment g pos coef sel A] {true} ≤
      𝒟[StrongDH.experiment g (sdhReduction pos coef sel A)] {true} +
        (Fintype.card F : ℝ≥0∞)⁻¹ := by
  rw [strongExperiment_eq_kernel, sdhExperiment_eq_kernel]
  exact A.kernel.success_le g pos coef sel hg

end AuditPay.SLINDRO.OW
