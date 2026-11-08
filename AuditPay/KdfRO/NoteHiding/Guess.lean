/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.KdfRO.NoteHiding.Hop
import AuditPay.KdfRO.SharedKeyOW

/-!
# Note hiding for the paper's scheme under plain CDH, with a loss factor (random-oracle KDF)

**Scheme unchanged, plain CDH, loss factor `q + 1`.** For Algorithm 2 with a random-oracle
key-derivation function, the note-hiding advantage of an adversary making at most
`q = q₁ + q₂ + q₃` KDF queries is at most

  `(q + 1) · (CDH(cdhReduction A false) + 1/|F|) + OT(otReduction A) +
     (q + 1) · (CDH(cdhReduction A true) + 1/|F|)`.

The reduction has no decision oracle and no trapdoor: it guesses which of the adversary's KDF
queries is the shared point, by picking an index uniformly in `Fin (q + 1)` and outputting the
queried point with that index. If the adversary queried the shared point, the guess is right
with probability at least `1/(q + 1)`. This is the classical argument;
`AuditPay.NoteHiding.StrongDH` and `AuditPay.NoteHiding.Twin` remove the loss.
-/

open OracleComp OracleSpec DiffieHellman ENNReal

namespace AuditPay.NoteHiding.Guess

open KdfRO SLIND

variable {F G Addr Key Note C σ τ : Type} [Field F] [Fintype F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]
  [Fintype Addr] [DecidableEq Addr] [SampleableType Key]

/-- The one-wayness adversary that guesses: it simulates the ideal run for `b` with a lazily
sampled KDF of its own, picks an index uniformly in `Fin (q + 1)` and outputs the queried point
with that index (or `0`). -/
noncomputable def owAdversary (q : ℕ) (senc : Key → Note → C)
    (A : Adversary F G Addr G G Key Note C σ τ) (b : Bool) :
    SharedKeyOW.Adversary F G Addr (σ × (G →ₒ Key).QueryCache) where
  choose H := do
    let z ← roRun (A.choose H) ∅
    return (z.1.1, z.1.2.1, (z.1.2.2, z.2))
  guess st sk ak R := do
    let w ← roRun (A.notes st.1 sk ak R) st.2
    let key ← $ᵗ Key
    let v ← roRun (A.guess w.1.2.2 (senc key (if b then w.1.2.1 else w.1.1))) w.2
    let j ← $ᵗ (Fin (q + 1))
    return ((cachedPoints v.2)[(j : ℕ)]?).getD 0

/-- The CDH reduction for note hiding with a guess, for bit `b`. -/
noncomputable def cdhReduction (q : ℕ) (senc : Key → Note → C)
    (A : Adversary F G Addr G G Key Note C σ τ) (b : Bool) : CDHAdversary F G :=
  SharedKeyOW.cdhReduction (owAdversary q senc A b)

/-- The last step of `owAdversary`, as a function of the outcome of an ideal run. -/
noncomputable def leaf (q : ℕ) (x : Bool × Option (Outcome G F G Key)) : ProbComp Bool :=
  match x.2 with
  | none => return false
  | some o => do
    let j ← $ᵗ (Fin (q + 1))
    return decide (((cachedPoints o.2.2)[(j : ℕ)]?).getD 0 = o.2.1 • o.1)

omit [Fintype F] in
/-- The one-wayness experiment of `owAdversary` is the ideal run followed by the guess. -/
theorem experiment_eqd (q : ℕ) (g : G) (senc : Key → Note → C)
    (A : Adversary F G Addr G G Key Note C σ τ) (b : Bool) :
    SharedKeyOW.experiment g (owAdversary q senc A b) =ᵈ
      (single F g).idealRun g senc A b >>= leaf q := by
  simp only [SharedKeyOW.experiment, owAdversary, Variant.idealRun, bind_assoc, pure_bind]
  refine EvalDistEq.bind_right _ fun H => EvalDistEq.bind_right _ fun z => ?_
  by_cases ha : z.1.1 = z.1.2.1
  · simp only [ha, ite_true, pure_bind, leaf]
    exact .rfl
  · simp only [ha, ite_false, bind_assoc, pure_bind, leaf, encPoint, single]
    exact .rfl

omit [Fintype F] [SampleableType F] [SampleableType Key] in
/-- If the shared point is among at most `q` cached points, the guess finds it with probability
at least `1/(q + 1)`. -/
theorem le_prEvent_leaf {g : G} {q : ℕ} {x : Bool × Option (Outcome G F G Key)}
    (hx : ∀ o, x.2 = some o → (cachedPoints o.2.2).length ≤ q)
    (hQ : (single F g).Queried x.2) :
    ((q + 1 : ℕ) : ℝ≥0∞)⁻¹ ≤ Pr{let y ← leaf q x}[y = true] := by
  obtain ⟨o, ho, hK⟩ := hQ
  obtain ⟨P, r, c⟩ := o
  have hlen : (cachedPoints c).length ≤ q := hx _ ho
  simp only [leaf, ho]
  simp only [single] at hK
  obtain ⟨i, hi⟩ := List.getElem?_of_mem (mem_cachedPoints.2 hK)
  have hiq : i < q + 1 := by
    have := (List.getElem?_eq_some_iff.1 hi).1
    omega
  simp only [prEvent_norm]
  refine le_trans (le_of_eq ?_) (prEvent_mono _ (fun j : Fin (q + 1) => j = ⟨i, hiq⟩) _
    fun j hj => ?_)
  · rw [SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_fin]
  · subst hj
    simp [hi]

omit [Fintype F] in
/-- In the ideal run, the adversary queries the KDF at the shared point with probability at most
`q + 1` times the success probability of `owAdversary` in the one-wayness game, for an adversary
making at most `q = q₁ + q₂ + q₃` KDF queries. -/
theorem queryProb_le_experiment (g : G) (senc : Key → Note → C)
    {A : Adversary F G Addr G G Key Note C σ τ} {q₁ q₂ q₃ : ℕ} (hq : A.QueryBound q₁ q₂ q₃)
    (b : Bool) :
    (single F g).queryProb g senc A b ≤
      ((q₁ + q₂ + q₃ + 1 : ℕ) : ℝ≥0∞) *
        𝒟[SharedKeyOW.experiment g (owAdversary (q₁ + q₂ + q₃) senc A b)] {true} := by
  rw [← prEvent_eq_evalDist_singleton, (experiment_eqd _ g senc A b).prEvent_eq]
  set q := q₁ + q₂ + q₃
  have hsz : (single F g).queryProb g senc A b = Pr{let x ← (single F g).idealRun g senc A b}[
      (single F g).Queried x.2 ∧ ∀ o, x.2 = some o → (cachedPoints o.2.2).length ≤ q] :=
    prEvent_congr_of_support _ _ _ fun x hx =>
      ⟨fun h => ⟨h, fun o ho => length_cachedPoints_le_of_mem_support_idealRun _ g senc hq b hx ho⟩,
        fun h => h.1⟩
  rw [hsz]
  have hq1 : ((q + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by simp
  have hq2 : ((q + 1 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have h := mul_le_prEvent_bind_of_forall ((single F g).idealRun g senc A b) (leaf q)
    (fun x => (single F g).Queried x.2 ∧ ∀ o, x.2 = some o → (cachedPoints o.2.2).length ≤ q)
    (fun y => y = true) le_rfl fun x hx => le_prEvent_leaf hx.2 hx.1
  calc _ = ((q + 1 : ℕ) : ℝ≥0∞) * (Pr{let x ← (single F g).idealRun g senc A b}[
          (single F g).Queried x.2 ∧ ∀ o, x.2 = some o → (cachedPoints o.2.2).length ≤ q] *
          ((q + 1 : ℕ) : ℝ≥0∞)⁻¹) := by
        rw [mul_comm _ (_)⁻¹, ← mul_assoc, ENNReal.mul_inv_cancel hq1 hq2, one_mul]
    _ ≤ _ := by gcongr

/-- **Note hiding for a mismatched address, random-oracle KDF, scheme unchanged, plain CDH**
(option 1). For a generator `g`, the note-hiding advantage of an adversary against Algorithm 2
that makes at most `q = q₁ + q₂ + q₃` KDF queries is at most the one-time advantage of
`otReduction` against the cipher plus, for each of the two bits, `q + 1` times the CDH success
probability of `cdhReduction` plus `1/|F|`. -/
theorem advantage_le [Inhabited Note] {g : G} (hg : Function.Bijective (· • g : F → G))
    (senc : Key → Note → C) {A : Adversary F G Addr G G Key Note C σ τ}
    {q₁ q₂ q₃ : ℕ} (hq : A.QueryBound q₁ q₂ q₃) :
    advantage g senc A ≤
      ((q₁ + q₂ + q₃ + 1 : ℕ) : ℝ≥0∞) *
          (𝒟[cdhExperiment g (cdhReduction (q₁ + q₂ + q₃) senc A false)] {true} +
            (Fintype.card F : ℝ≥0∞)⁻¹) +
        otAdvantage senc (otReduction g A) +
      ((q₁ + q₂ + q₃ + 1 : ℕ) : ℝ≥0∞) *
          (𝒟[cdhExperiment g (cdhReduction (q₁ + q₂ + q₃) senc A true)] {true} +
            (Fintype.card F : ℝ≥0∞)⁻¹) := by
  rw [advantage_eq]
  refine (advantage_le_queryProb (single F g) g senc A).trans ?_
  have h0 := (queryProb_le_experiment g senc hq false).trans
    (mul_le_mul_right (SharedKeyOW.success_le hg (owAdversary (q₁ + q₂ + q₃) senc A false)) _)
  have h1 := (queryProb_le_experiment g senc hq true).trans
    (mul_le_mul_right (SharedKeyOW.success_le hg (owAdversary (q₁ + q₂ + q₃) senc A true)) _)
  exact add_le_add (add_le_add h0 le_rfl) h1

end AuditPay.NoteHiding.Guess
