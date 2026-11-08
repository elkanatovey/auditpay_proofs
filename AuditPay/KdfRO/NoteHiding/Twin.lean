/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.KdfRO.NoteHiding.Hop
import AuditPay.KdfRO.SharedKeyOW

/-!
# Note hiding for the twin variant under plain CDH (random-oracle KDF)

**Scheme changed (two ephemeral values), tight reduction to CDH.** For the twin variant of
selective encryption (`AuditPay.Twin`) with a random-oracle key-derivation function, the
note-hiding advantage (`AuditPay.NoteHiding.Twin.advantage`) of an adversary making at most
`q = q₁ + q₂ + q₃` KDF queries is at most

  `(CDH(cdhReduction A false) + 1/|F| + q/|F|) + OT(otReduction A) +
     (CDH(cdhReduction A true) + 1/|F| + q/|F|)`,

where `CDH` is the success probability in VCV-io's `cdhExperiment`.

## The trapdoor test on the ephemeral side

By `AuditPay.NoteHiding.advantage_le_queryProb` it remains to bound the probability that the
adversary queries the KDF at the pair `(r₁ • P, r₂ • P)`, `P = AK_a - H(a*)`, in the ideal run.
The reduction must find that pair among the queried pairs without a decision oracle. This is the
twin Diffie–Hellman trapdoor test of Cash, Kiltz and Shoup, applied to the two *ephemeral*
values:

* Given the first ephemeral point `R₁` (of unknown discrete logarithm `r₁`), pick uniform `s, t`
  and set `R₂ = s • g - t • R₁`. Then `r₂ = s - t * r₁` is uniform and independent of `r₁`, and
  `t` is independent of `(R₁, R₂)`.
* Accept a queried pair `(Z₁, Z₂)` iff `t • Z₁ + Z₂ = s • P` (`test`).
* The true pair passes: `t • (r₁ • P) + r₂ • P = s • P`.
* A pair with `Z₁ ≠ r₁ • P` passes only if `t • (Z₁ - r₁ • P) = r₂ • P - Z₂`, which holds for at
  most one `t` (`prob_test_le`). The adversary's view does not depend on `t`, so with at most `q`
  queried pairs some such pair passes with probability at most `q/|F|`.
* A pair with `Z₁ = r₁ • P` that passes is the true pair. So, unless a wrong pair passes, the
  first accepted pair has first component `r₁ • P`: the shared point of Algorithm 2 for the
  ephemeral point `R₁`.

Hence `owAdversary` wins the one-wayness game of `AuditPay.SharedKeyOW` (for `R = R₁`), and
`AuditPay.SharedKeyOW.success_le` gives the CDH bound. This file is the machine-checked version
of that argument; the test is sound as stated.
-/

open OracleComp OracleSpec DiffieHellman ENNReal

namespace AuditPay.NoteHiding.Twin

open KdfRO SLIND

variable {F G Addr Key Note C σ τ : Type} [Field F] [Fintype F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]
  [Fintype Addr] [DecidableEq Addr] [SampleableType Key]

/-- The trapdoor test with trapdoor `(s, t)` for the point `P`: accept the pair `(Z₁, Z₂)` iff
`t • Z₁ + Z₂ = s • P`. -/
def test (s t : F) (P : G) (Z : G × G) : Bool := decide (t • Z.1 + Z.2 = s • P)

/-- The first component of the first cached pair that passes the trapdoor test (or `0`). -/
noncomputable def extract (s t : F) (P : G) (c : ((G × G) →ₒ Key).QueryCache) : G :=
  (((cachedPoints c).find? (test s t P)).map Prod.fst).getD 0

/-- The one-wayness adversary built from a note-hiding adversary against the twin variant and a
bit `b`. Given `(sk, AK_a, R)` it uses `R` as the first ephemeral point, samples a trapdoor
`(s, t)` and sets the second ephemeral point to `s • g - t • R`. It simulates the ideal run for
`b` with a lazily sampled KDF of its own, and outputs the first component of the first queried
pair that passes the trapdoor test. Its state after the first phase is
`(H(a*), the adversary's state, the KDF cache)`. -/
noncomputable def owAdversary (g : G) (senc : Key → Note → C)
    (A : Adversary F G Addr (G × G) (G × G) Key Note C σ τ) (b : Bool) :
    SharedKeyOW.Adversary F G Addr (G × σ × ((G × G) →ₒ Key).QueryCache) where
  choose H := do
    let z ← roRun (A.choose H) ∅
    return (z.1.1, z.1.2.1, (H z.1.2.1, z.1.2.2, z.2))
  guess st sk ak R := do
    let s ← $ᵗ F
    let t ← $ᵗ F
    let w ← roRun (A.notes st.2.1 sk ak (R, s • g - t • R)) st.2.2
    let key ← $ᵗ Key
    let v ← roRun (A.guess w.1.2.2 (senc key (if b then w.1.2.1 else w.1.1))) w.2
    return extract s t (ak - st.1) v.2

/-- The CDH reduction for note hiding of the twin variant, for bit `b`. -/
noncomputable def cdhReduction (g : G) (senc : Key → Note → C)
    (A : Adversary F G Addr (G × G) (G × G) Key Note C σ τ) (b : Bool) : CDHAdversary F G :=
  SharedKeyOW.cdhReduction (owAdversary g senc A b)

/-! ## The trapdoor test -/

omit [Fintype F] [SampleableType F] [SampleableType G] [DecidableEq G] in
/-- The true pair passes the trapdoor test. -/
theorem test_true (r₁ r₂ t : F) (P : G) [DecidableEq G] :
    test (r₂ + t * r₁) t P (r₁ • P, r₂ • P) = true := by
  simp only [test, decide_eq_true_eq]
  module

omit [SampleableType G] in
/-- A fixed pair whose first component is wrong passes the trapdoor test with probability at
most `1/|F|` over the trapdoor `t` (with `s = r₂ + t * r₁`, i.e. for fixed ephemeral points). -/
theorem prob_test_le (r₁ r₂ : F) (P : G) (Z : G × G) (hZ : Z.1 ≠ r₁ • P) :
    Pr{let t ← $ᵗ F}[test (r₂ + t * r₁) t P Z = true] ≤ (Fintype.card F : ℝ≥0∞)⁻¹ := by
  have hD : Z.1 - r₁ • P ≠ 0 := sub_ne_zero.2 hZ
  have hinj : Function.Injective fun t : F => t • (Z.1 - r₁ • P) := by
    intro t t' h
    have h' : (t - t') • (Z.1 - r₁ • P) = 0 := by
      rw [sub_smul]
      exact sub_eq_zero.2 h
    exact sub_eq_zero.1 ((smul_eq_zero.1 h').resolve_right hD)
  have key : ∀ t : F, (test (r₂ + t * r₁) t P Z = true) ↔
      t • (Z.1 - r₁ • P) = r₂ • P - Z.2 := by
    intro t
    simp only [test, decide_eq_true_eq]
    constructor
    · intro h
      have : t • (Z.1 - r₁ • P) = (t • Z.1 + Z.2) - Z.2 - (t * r₁) • P := by module
      rw [this, h]
      module
    · intro h
      have : t • Z.1 + Z.2 = t • (Z.1 - r₁ • P) + Z.2 + (t * r₁) • P := by module
      rw [this, h]
      module
  rw [prEvent_congr _ _ _ key]
  refine (SampleableType.prEvent_uniformSample_apply_eq_le hinj _).trans_eq ?_
  rw [Nat.card_eq_fintype_card]

/-! ## The one-wayness experiment as the ideal run followed by the trapdoor test -/

/-- The last step of `owAdversary`, as a function of the outcome of an ideal run: sample the
trapdoor `t` (the second ephemeral scalar is `r₂ = s - t * r₁`, so `s = r₂ + t * r₁`) and check
whether the extracted point is `r₁ • P`. -/
noncomputable def leaf (x : Bool × Option (Outcome G (F × F) (G × G) Key)) : ProbComp Bool :=
  match x.2 with
  | none => return false
  | some o => do
    let t ← $ᵗ F
    return decide (extract (o.2.1.2 + t * o.2.1.1) t o.1 o.2.2 = o.2.1.1 • o.1)

omit [Fintype F] in
/-- The one-wayness experiment of `owAdversary` is the ideal run of the twin variant followed by
the trapdoor test: the second ephemeral scalar `s - t * r₁` is uniform, and the adversary's view
does not depend on `t`, which can therefore be sampled at the end. -/
theorem experiment_eqd (g : G) (senc : Key → Note → C)
    (A : Adversary F G Addr (G × G) (G × G) Key Note C σ τ) (b : Bool) :
    SharedKeyOW.experiment g (owAdversary g senc A b) =ᵈ
      (twin F g).idealRun g senc A b >>= leaf := by
  simp only [SharedKeyOW.experiment, owAdversary, Variant.idealRun, bind_assoc, pure_bind]
  refine EvalDistEq.bind_right _ fun H => EvalDistEq.bind_right _ fun z => ?_
  by_cases ha : z.1.1 = z.1.2.1
  · simp only [ha, ite_true, pure_bind, leaf]
    exact .rfl
  · simp only [ha, ite_false, bind_assoc, pure_bind, leaf]
    refine EvalDistEq.bind_right _ fun sk => ?_
    rw [SampleableType.uniformSample_prod_eq_bind]
    simp only [bind_assoc, pure_bind]
    refine EvalDistEq.bind_right _ fun r₁ => ?_
    -- move the trapdoor `t` to the front on both sides
    refine (bind_swap_eqd _ _ _).trans ?_
    refine EvalDistEq.trans ?_ (EvalDistEq.bind_right _ fun r₂ => EvalDistEq.bind_right _ fun w =>
      EvalDistEq.bind_right _ fun key => bind_swap_eqd _ _ _).symm
    refine EvalDistEq.trans ?_ (EvalDistEq.bind_right _ fun r₂ => EvalDistEq.bind_right _ fun w =>
      bind_swap_eqd _ _ _).symm
    refine EvalDistEq.trans ?_ (EvalDistEq.bind_right _ fun r₂ => bind_swap_eqd _ _ _).symm
    refine EvalDistEq.trans ?_ (bind_swap_eqd _ _ _).symm
    refine EvalDistEq.bind_right _ fun t => ?_
    -- reparametrize `s = r₂ + t * r₁`
    refine EvalDistEq.trans ?_
      (uniform_bind_bij (e := fun s : F => s - t * r₁) (Equiv.subRight (t * r₁)).bijective _)
    simp only [sub_smul, mul_smul, sub_add_cancel, encPoint, twin]
    exact .rfl

/-! ## The error of the trapdoor test -/

omit [SampleableType Key] in
/-- If the true pair is among at most `q` cached pairs, the trapdoor test fails to extract
`r₁ • P` with probability at most `q/|F|` over the trapdoor. -/
theorem prEvent_leaf_le {g : G} {q : ℕ} {x : Bool × Option (Outcome G (F × F) (G × G) Key)}
    (hx : ∀ o, x.2 = some o → (cachedPoints o.2.2).length ≤ q)
    (hQ : (twin F g).Queried x.2) :
    Pr{let y ← leaf x}[¬(y = true)] ≤ q * (Fintype.card F : ℝ≥0∞)⁻¹ := by
  obtain ⟨o, ho, hK⟩ := hQ
  obtain ⟨P, r, c⟩ := o
  have hlen := hx _ ho
  simp only [leaf, ho]
  simp only [twin] at hK
  have hmem : (r.1 • P, r.2 • P) ∈ cachedPoints c := mem_cachedPoints.2 hK
  -- failure means that a pair with a wrong first component passes the test
  have himp : ∀ t : F, ¬(decide (extract (r.2 + t * r.1) t P c = r.1 • P) = true) →
      ∃ Z ∈ (cachedPoints c).toFinset, Z.1 ≠ r.1 • P ∧ test (r.2 + t * r.1) t P Z = true := by
    intro t ht
    rw [decide_eq_true_eq] at ht
    have hsome : ((cachedPoints c).find? (test (r.2 + t * r.1) t P)).isSome :=
      List.find?_isSome.2 ⟨_, hmem, test_true r.1 r.2 t P⟩
    obtain ⟨Z, hZ⟩ := Option.isSome_iff_exists.1 hsome
    refine ⟨Z, List.mem_toFinset.2 (List.mem_of_find?_eq_some hZ), fun h1 => ht ?_,
      List.find?_some hZ⟩
    simp [extract, hZ, h1]
  simp only [prEvent_norm]
  refine (prEvent_mono _ _ _ himp).trans ?_
  refine (prEvent_exists_finset_le_card_mul _ _ _ (ε := (Fintype.card F : ℝ≥0∞)⁻¹)
    fun Z _ => ?_).trans ?_
  · by_cases hZ : Z.1 = r.1 • P
    · simp [hZ]
    · exact (prEvent_mono _ _ _ fun t h => h.2).trans (prob_test_le r.1 r.2 P Z hZ)
  · gcongr
    exact_mod_cast (List.toFinset_card_le _).trans hlen

/-- In the ideal run, the adversary queries the KDF at the pair of shared points with probability
at most the success probability of `owAdversary` in the one-wayness game plus `q/|F|`, for an
adversary making at most `q = q₁ + q₂ + q₃` KDF queries. -/
theorem queryProb_le_experiment (g : G) (senc : Key → Note → C)
    {A : Adversary F G Addr (G × G) (G × G) Key Note C σ τ} {q₁ q₂ q₃ : ℕ}
    (hq : A.QueryBound q₁ q₂ q₃) (b : Bool) :
    (twin F g).queryProb g senc A b ≤
      𝒟[SharedKeyOW.experiment g (owAdversary g senc A b)] {true} +
        (q₁ + q₂ + q₃ : ℕ) * (Fintype.card F : ℝ≥0∞)⁻¹ := by
  rw [← prEvent_eq_evalDist_singleton, (experiment_eqd g senc A b).prEvent_eq]
  exact prEvent_le_prEvent_bind_add_of_support _ _ _ _ fun x hx hQ =>
    prEvent_leaf_le (fun o ho => length_cachedPoints_le_of_mem_support_idealRun _ g senc hq b hx ho)
      hQ

/-- In the ideal run, the adversary queries the KDF at the pair of shared points with probability
at most the CDH success probability of `cdhReduction` plus `1/|F| + q/|F|`. -/
theorem queryProb_le {g : G} (hg : Function.Bijective (· • g : F → G)) (senc : Key → Note → C)
    {A : Adversary F G Addr (G × G) (G × G) Key Note C σ τ} {q₁ q₂ q₃ : ℕ}
    (hq : A.QueryBound q₁ q₂ q₃) (b : Bool) :
    (twin F g).queryProb g senc A b ≤
      𝒟[cdhExperiment g (cdhReduction g senc A b)] {true} + (Fintype.card F : ℝ≥0∞)⁻¹ +
        (q₁ + q₂ + q₃ : ℕ) * (Fintype.card F : ℝ≥0∞)⁻¹ :=
  (queryProb_le_experiment g senc hq b).trans
    (add_le_add (SharedKeyOW.success_le hg (owAdversary g senc A b)) le_rfl)

/-- **Note hiding for a mismatched address, random-oracle KDF, twin variant** (option 3). For a
generator `g`, the note-hiding advantage of an adversary against the two-ephemeral-value variant
that makes at most `q₁ + q₂ + q₃` KDF queries is at most the one-time advantage of `otReduction`
against the cipher plus, for each of the two bits, the CDH success probability of `cdhReduction`
plus `1/|F|` plus `(q₁ + q₂ + q₃)/|F|`. The reduction to plain CDH is tight. -/
theorem advantage_le [Inhabited Note] {g : G} (hg : Function.Bijective (· • g : F → G))
    (senc : Key → Note → C) {A : Adversary F G Addr (G × G) (G × G) Key Note C σ τ}
    {q₁ q₂ q₃ : ℕ} (hq : A.QueryBound q₁ q₂ q₃) :
    advantage g senc A ≤
      (𝒟[cdhExperiment g (cdhReduction g senc A false)] {true} + (Fintype.card F : ℝ≥0∞)⁻¹ +
          (q₁ + q₂ + q₃ : ℕ) * (Fintype.card F : ℝ≥0∞)⁻¹) +
        otAdvantage senc (otReduction g A) +
      (𝒟[cdhExperiment g (cdhReduction g senc A true)] {true} + (Fintype.card F : ℝ≥0∞)⁻¹ +
          (q₁ + q₂ + q₃ : ℕ) * (Fintype.card F : ℝ≥0∞)⁻¹) := by
  rw [advantage_eq]
  refine (advantage_le_queryProb (twin F g) g senc A).trans ?_
  gcongr
  · exact queryProb_le hg senc hq false
  · exact le_rfl
  · exact queryProb_le hg senc hq true

end AuditPay.NoteHiding.Twin
