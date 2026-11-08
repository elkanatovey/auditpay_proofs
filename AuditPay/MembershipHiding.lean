/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.Defs
import AuditPay.Prob
import AuditPay.Singularity
import VCVio.EvalDist.Monad.Disagreement.Measure

/-!
# Theorem 4: Membership Hiding, hashes sampled after the sets

## Model

This file proves Theorem 4 in the model where the position and coefficient hashes are **sampled
after the candidate sets are fixed** (for example, salted with fresh per-epoch randomness); the
sets may then have the full size `|V|`. The adversary still sees the hash functions, the
hash-to-curve oracle `H`, and the vector `V`. The version with public hash functions, fixed
before the adversary chooses, and sets of at most `s` addresses is
`AuditPay.MembershipHidingPublic` and `AuditPay.SilentDrop`.

Further modeling choices:
* The adversary supplies the two candidate sets already padded to exactly `n = |V|` distinct
  addresses (`Fin n ↪ Addr`). This only strengthens it: an adversary whose sets the
  challenger pads with random addresses is simulated by one that pads them itself.
* `AuditKeyVecGen` returns `none` when the encoding matrix is singular; the adversary sees that.
* The audit keys `AK_a = sk_a • g + H(a)` use fresh uniform `sk_a`.

## Statement

`advantage ≤ 2 · (hallBound n k + n/|F|)`: whenever both encoding matrices are invertible,
`V = M⁻¹ ⋆ AK` is a uniformly random vector whatever the set, so the advantage is at most the
probability that one of the two matrices is singular (bounded in `AuditPay.Singularity`).
-/

open OracleComp ENNReal

namespace AuditPay.MembershipHiding

/-- A Membership Hiding adversary for a vector of size `n` and `k` hash functions. -/
structure Adversary (F G Addr σ : Type) (k n : ℕ) where
  /-- Choose two candidate monitored sets (padded to `n` distinct addresses), given `H`. -/
  choose : (Addr → G) → ProbComp ((Fin n ↪ Addr) × (Fin n ↪ Addr) × σ)
  /-- Guess which set was encoded, from the hash functions and the published vector. -/
  guess : σ → (Addr → Fin k → Fin n) → (Addr → Fin k → F) → Option (Fin n → G) →
    ProbComp Bool

variable {F G Addr σ : Type} {k n : ℕ} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G] [Fintype Addr] [DecidableEq Addr] [NeZero n]

/-- The Membership Hiding experiment encoding the set `S_b`. The hash functions are sampled
after the sets are chosen. -/
noncomputable def experiment (g : G) (A : Adversary F G Addr σ k n) (b : Bool) :
    ProbComp Bool := do
  let H ← $ᵗ (Addr → G)
  let p ← A.choose H
  let pos ← $ᵗ (Addr → Fin k → Fin n)
  let coef ← $ᵗ (Addr → Fin k → F)
  let sk ← $ᵗ (Fin n → F)
  A.guess p.2.2 pos coef (auditKeyVecGen g H pos coef (if b then p.2.1 else p.1) sk)

/-- The Membership Hiding advantage: the distance between encoding `S₀` and encoding `S₁`. -/
noncomputable def advantage (g : G) (A : Adversary F G Addr σ k n) : ℝ≥0∞ :=
  𝒟[experiment g A false].boolDist 𝒟[experiment g A true]

/-! ## Splitting the experiment -/

/-- The experiment's state once the hash functions are sampled: `(H, choice, pos, coef)`. -/
abbrev Pre (F G Addr σ : Type) (k n : ℕ) : Type :=
  (Addr → G) × ((Fin n ↪ Addr) × (Fin n ↪ Addr) × σ) × (Addr → Fin k → Fin n) ×
    (Addr → Fin k → F)

/-- The experiment up to and including the sampling of the hash functions. -/
noncomputable def pre (A : Adversary F G Addr σ k n) : ProbComp (Pre F G Addr σ k n) := do
  let H ← $ᵗ (Addr → G)
  let p ← A.choose H
  let pos ← $ᵗ (Addr → Fin k → Fin n)
  let coef ← $ᵗ (Addr → Fin k → F)
  return (H, p, pos, coef)

/-- The rest of the experiment encoding `S_b`: sample the audit secret keys and run the guess. -/
noncomputable def rest (g : G) (A : Adversary F G Addr σ k n) (b : Bool)
    (w : Pre F G Addr σ k n) : ProbComp Bool := do
  let sk ← $ᵗ (Fin n → F)
  A.guess w.2.1.2.2 w.2.2.1 w.2.2.2
    (auditKeyVecGen g w.1 w.2.2.1 w.2.2.2 (if b then w.2.1.2.1 else w.2.1.1) sk)

omit [Fintype F] in
/-- The experiment is its prefix followed by its rest. -/
theorem experiment_eq (g : G) (A : Adversary F G Addr σ k n) (b : Bool) :
    experiment g A b = pre A >>= rest g A b := by
  simp only [experiment, pre, rest, bind_assoc, pure_bind]

/-! ## The published vector is uniform when the encoding matrix is invertible -/

omit [Fintype F] [DecidableEq F] [SampleableType F] [SampleableType G] [NeZero n] in
/-- An invertible matrix acts bijectively on vectors of group elements. -/
theorem matVecG_inv_bijective {M : Matrix (Fin n) (Fin n) F} (hM : M.det ≠ 0) :
    Function.Bijective (matVecG (G := G) M⁻¹) := by
  have hu : IsUnit M.det := isUnit_iff_ne_zero.2 hM
  refine Function.bijective_iff_has_inverse.2 ⟨matVecG M, fun v => ?_, fun v => ?_⟩
  · rw [← matVecG_mul, Matrix.mul_nonsing_inv _ hu, matVecG_one]
  · rw [← matVecG_mul, Matrix.nonsing_inv_mul _ hu, matVecG_one]

omit [Fintype F] [Fintype Addr] [DecidableEq Addr] [NeZero n] in
/-- If the encoding matrix of `rows` is invertible, the vector produced by `AuditKeyVecGen` from
fresh uniform secret keys is a uniformly random vector. -/
theorem auditKeyVecGen_eqd {g : G} (hg : Function.Bijective (· • g : F → G)) (H : Addr → G)
    (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F) (rows : Fin n → Addr)
    (hM : (coefMatrix pos coef rows).det ≠ 0) (f : Option (Fin n → G) → ProbComp Bool) :
    (do let sk ← $ᵗ (Fin n → F); f (auditKeyVecGen g H pos coef rows sk)) =ᵈ
      (do let V ← $ᵗ (Fin n → G); f (some V)) := by
  have h : ∀ sk : Fin n → F, auditKeyVecGen g H pos coef rows sk =
      some (matVecG (coefMatrix pos coef rows)⁻¹ fun r => sk r • g + H (rows r)) := by
    intro sk
    simp only [auditKeyVecGen, solve, hM, ne_eq, not_false_eq_true, ite_true, auditKey]
  simp only [h]
  exact uniform_bind_bij
    (e := fun sk : Fin n → F => matVecG (coefMatrix pos coef rows)⁻¹ fun r => sk r • g + H (rows r))
    ((matVecG_inv_bijective hM).comp (bijective_smul_add hg fun r => H (rows r)))
    (fun V => f (some V))

/-! ## The bad event -/

/-- The bad event: one of the two encoding matrices is singular. -/
def Bad (w : Pre F G Addr σ k n) : Prop :=
  (coefMatrix w.2.2.1 w.2.2.2 w.2.1.1).det = 0 ∨ (coefMatrix w.2.2.1 w.2.2.2 w.2.1.2.1).det = 0

omit [Fintype F] [Fintype Addr] [DecidableEq Addr] [NeZero n] in
/-- Outside the bad event, encoding `S₀` and encoding `S₁` give the same distribution. -/
theorem rest_eqd_of_not_bad {g : G} (hg : Function.Bijective (· • g : F → G))
    (A : Adversary F G Addr σ k n) (w : Pre F G Addr σ k n) (hw : ¬Bad w) :
    rest g A false w =ᵈ rest g A true w := by
  have h0 : (coefMatrix w.2.2.1 w.2.2.2 w.2.1.1).det ≠ 0 := fun h => hw (Or.inl h)
  have h1 : (coefMatrix w.2.2.1 w.2.2.2 w.2.1.2.1).det ≠ 0 := fun h => hw (Or.inr h)
  simp only [rest, Bool.false_eq_true, ite_false, ite_true]
  exact (auditKeyVecGen_eqd hg w.1 w.2.2.1 w.2.2.2 w.2.1.1 h0 _).trans
    (auditKeyVecGen_eqd hg w.1 w.2.2.1 w.2.2.2 w.2.1.2.1 h1 _).symm

omit [DecidableEq F] in
/-- For a fixed set of `n` addresses, freshly sampled hash functions give a singular encoding
matrix with probability at most `hallBound n k + n/|F|`. -/
theorem prob_singular_le (rows : Fin n ↪ Addr) :
    Pr{let pos ← $ᵗ (Addr → Fin k → Fin n); let coef ← $ᵗ (Addr → Fin k → F)}[
        (coefMatrix pos coef rows).det = 0] ≤
      ENNReal.ofReal (hallBound n k + n / Fintype.card F) := by
  classical
  rw [← SampleableType.prEvent_uniformSample_prod
    (fun ω : (Addr → Fin k → Fin n) × (Addr → Fin k → F) => (coefMatrix ω.1 ω.2 rows).det = 0),
    SampleableType.prEvent_uniformSample_eq_ofReal]
  exact ENNReal.ofReal_le_ofReal (card_singular_rows_le n k rows)

omit [DecidableEq F] [AddCommGroup G] [Module F G] in
/-- The bad event has probability at most `2 · (hallBound n k + n/|F|)`. -/
theorem prob_bad_le (A : Adversary F G Addr σ k n) :
    Pr{let w ← pre A}[Bad w] ≤ 2 * ENNReal.ofReal (hallBound n k + n / Fintype.card F) := by
  have hone : ∀ r : (Fin n ↪ Addr) × (Fin n ↪ Addr) × σ → (Fin n ↪ Addr),
      Pr{let w ← pre A}[(coefMatrix w.2.2.1 w.2.2.2 (r w.2.1)).det = 0] ≤
        ENNReal.ofReal (hallBound n k + n / Fintype.card F) := by
    intro r
    refine prEvent_bind_le_of_forall_le _ _ _ fun H => ?_
    refine prEvent_bind_le_of_forall_le _ _ _ fun p => ?_
    simp only [prEvent_norm]
    exact prob_singular_le (r p)
  refine (prEvent_or_le _ _ _).trans ?_
  rw [two_mul]
  exact add_le_add (hone Prod.fst) (hone fun p => p.2.1)

/-- **Theorem 4** (Membership Hiding, with hash functions sampled after the sets are fixed). -/
theorem advantage_le {g : G} (hg : Function.Bijective (· • g : F → G))
    (A : Adversary F G Addr σ k n) :
    advantage g A ≤ 2 * ENNReal.ofReal (hallBound n k + n / Fintype.card F) := by
  have hbad : ∀ b : Bool,
      Pr{let y ← pre A >>= rest g A b}[y = true] ≤
        Pr{let y ← pre A >>= rest g A (!b)}[y = true] +
          2 * ENNReal.ofReal (hallBound n k + n / Fintype.card F) := by
    intro b
    have := prEvent_bind_le_add_of_disagree (mx := pre A) (my := rest g A b)
      (oc := rest g A (!b)) (q := fun y => y = true) (ε₂ := 0) (prob_bad_le A)
      (fun w _ hw => by
        rw [add_zero]
        cases b
        · exact ((rest_eqd_of_not_bad hg A w hw).prEvent_eq _).le
        · exact ((rest_eqd_of_not_bad hg A w hw).symm.prEvent_eq _).le)
    simpa only [add_zero] using this
  rw [advantage, experiment_eq, experiment_eq, MeasureTheory.Measure.boolDist,
    ← prEvent_eq_evalDist_singleton, ← prEvent_eq_evalDist_singleton]
  exact ENNReal.absDiff_le_iff.2 ⟨hbad false, hbad true⟩

end AuditPay.MembershipHiding
