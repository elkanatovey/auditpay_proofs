/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.SetEncoding
import AuditPay.Dependence
import AuditPay.Prob
import VCVio.EvalDist.Monad.Disagreement.Measure

/-!
# Theorem 4: Membership Hiding with public hash functions

Theorem 4 with the hash functions **public and fixed before the adversary chooses its sets**;
the size of the sets and the number of addresses whose hashes the adversary has evaluated are
bounded. (`AuditPay.MembershipHiding` proves the alternative model in which the position and
coefficient hashes are sampled after the candidate sets are fixed.)

## Model

* **The address type is the set of evaluated addresses.** `Addr` is a finite type and
  `Q = |Addr|`. The hash-to-curve table `H` and the position and coefficient tables are sampled
  uniformly over all of `Addr` and handed to the adversary in full before it chooses its sets.
  There is no query counting; the bound is a function of `Q`. (An adaptive adversary that
  makes `Q` queries to random oracles on a huge address space only ever uses the tables on the
  addresses it queried; treating those as the whole address type is the usual, here informal,
  step.)
* **Bounded sets.** The adversary chooses two sets of at most `s` addresses each
  (`BoundedSet Addr s`); `s` is a parameter.
* **No padding, uniform solution.** The challenger does not pad the set. It samples fresh
  audit secret keys for the addresses of the set and outputs a uniformly random solution of the
  rectangular system `M ⋆ V = AK` (`AuditPay.auditKeyVecGenSet`), or `none` if the rows of the
  set are linearly dependent; the adversary sees that.

## Statements

* `prob_dep_le`: `Pr[Dep s] ≤ depBound Q n k s |F|` over uniform position and coefficient
  tables, where `Dep s` says that some set of at most `s` addresses has dependent rows.
* `auditKeyVecGenSet_eqd`: if the rows of `T` are linearly independent, the published vector is
  exactly uniform on `Fin n → G`, whatever `T` is.
* `advantage_le`: `advantage ≤ depBound Q n k s |F|`. Outside `Dep s` both candidate sets have
  independent rows, so both worlds publish a uniformly random vector; one bad event covers both
  sets. The bound is statistical.

The variant in which generation never fails is in `AuditPay.SilentDrop`.
-/

open OracleComp ENNReal

namespace AuditPay.MembershipHidingPublic

variable {F G Addr σ : Type} {k n s : ℕ} [Field F] [Fintype F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G] [Fintype Addr] [DecidableEq Addr] [NeZero n]

/-! ## The dependence bound as a probability -/

/-- **Dependence bound** for public hash functions: over uniformly random position and
coefficient tables on `Addr`, some set of at most `s` addresses has linearly dependent rows
with probability at most `depBound |Addr| n k s |F|`. -/
theorem prob_dep_le (s : ℕ) :
    Pr{let pos ← $ᵗ (Addr → Fin k → Fin n); let coef ← $ᵗ (Addr → Fin k → F)}[
        Dep s pos coef] ≤
      ENNReal.ofReal (depBound (Fintype.card Addr) n k s (Fintype.card F)) := by
  classical
  rw [← SampleableType.prEvent_uniformSample_prod
    (fun ω : (Addr → Fin k → Fin n) × (Addr → Fin k → F) => Dep s ω.1 ω.2),
    SampleableType.prEvent_uniformSample_eq_ofReal]
  exact ENNReal.ofReal_le_ofReal (card_dep_div_le s)

/-! ## The generation procedure outputs a uniformly random solution -/

omit [Fintype F] [SampleableType F] [NeZero n] in
/-- With `ρ` uniformly random, all solutions of `M ⋆ V = b` are equally likely outputs of
`rectSolve M R b ρ`. -/
theorem prob_rectSolve_eq {ι : Type} [Fintype ι] (M : Matrix ι (Fin n) F)
    (R : Matrix (Fin n) ι F) {b : ι → G} {V V' : Fin n → G} (hV : matVecG M V = b)
    (hV' : matVecG M V' = b) :
    Pr{let ρ ← $ᵗ (Fin n → G)}[rectSolve M R b ρ = V] =
      Pr{let ρ ← $ᵗ (Fin n → G)}[rectSolve M R b ρ = V'] := by
  have hδ : matVecG M (V' - V) = 0 := by rw [matVecG_sub, hV, hV', sub_self]
  rw [← SampleableType.prEvent_uniformSample_equiv (Equiv.addRight (V' - V))
    fun ρ => rectSolve M R b ρ = V']
  refine prEvent_congr _ _ _ fun ρ => ?_
  rw [Equiv.coe_addRight, rectSolve_add R b ρ hδ]
  constructor
  · intro h
    rw [h]
    abel
  · intro h
    rw [eq_sub_of_add_eq h]
    abel

omit [Fintype F] [SampleableType F] [NeZero n] in
/-- `rectSolve M R b ρ` never outputs a vector that is not a solution of `M ⋆ V = b`. Together
with `prob_rectSolve_eq`: with `ρ` uniformly random, `rectSolve M R b ρ` is uniformly
distributed on the solution set. -/
theorem prob_rectSolve_eq_zero {ι : Type} [Fintype ι] [DecidableEq ι] {M : Matrix ι (Fin n) F}
    {R : Matrix (Fin n) ι F} (h : M * R = 1) {b : ι → G} {V : Fin n → G}
    (hV : matVecG M V ≠ b) :
    Pr{let ρ ← $ᵗ (Fin n → G)}[rectSolve M R b ρ = V] = 0 :=
  prEvent_eq_zero_of_forall_not _ _ fun ρ hρ => hV (hρ ▸ matVecG_rectSolve h b ρ)

/-! ## The published vector is uniform -/

omit [Fintype F] [Fintype Addr] [NeZero n] in
/-- The vector encoding a set `T`, generated from fresh uniform audit secret keys and a uniform
`ρ`, is a uniformly random vector, whatever `T` is. (It encodes `T` when the rows of `T` are
linearly independent: `AuditPay.retrieveKey_encodeSet`.) -/
theorem encodeSet_eqd {γ : Type} {g : G} (hg : Function.Bijective (· • g : F → G))
    (H : Addr → G) (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F) (T : Finset Addr)
    (f : (Fin n → G) → ProbComp γ) :
    (do let sk ← $ᵗ (T → F); let ρ ← $ᵗ (Fin n → G); f (encodeSet g H pos coef T sk ρ)) =ᵈ
      (do let V ← $ᵗ (Fin n → G); f V) := by
  set M := setMatrix pos coef T
  set R := rightInv M
  -- the audit keys `sk a • g + H a` are uniformly random group elements
  have h1 :
      (do let sk ← $ᵗ (T → F); let ρ ← $ᵗ (Fin n → G); f (encodeSet g H pos coef T sk ρ)) =ᵈ
        (do let AK ← $ᵗ (T → G); let ρ ← $ᵗ (Fin n → G); f (rectSolve M R AK ρ)) :=
    uniform_bind_bij (bijective_smul_add hg fun a : T => H a)
      (fun AK => do let ρ ← $ᵗ (Fin n → G); f (rectSolve M R AK ρ))
  -- for fixed `ρ`, the right-hand side `AK - M ⋆ ρ` is uniform
  have h2 :
      (do let AK ← $ᵗ (T → G); let ρ ← $ᵗ (Fin n → G); f (rectSolve M R AK ρ)) =ᵈ
        (do let ρ ← $ᵗ (Fin n → G); let w ← $ᵗ (T → G); f (ρ + matVecG R w)) :=
    (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun ρ =>
      uniform_bind_bij (e := fun AK : T → G => AK - matVecG M ρ)
        (Equiv.subRight (matVecG M ρ)).bijective fun w => f (ρ + matVecG R w))
  -- for fixed `w`, the translate `ρ + R ⋆ w` is uniform
  have h3 :
      (do let ρ ← $ᵗ (Fin n → G); let w ← $ᵗ (T → G); f (ρ + matVecG R w)) =ᵈ
        (do let _ ← $ᵗ (T → G); let V ← $ᵗ (Fin n → G); f V) :=
    (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun w =>
      uniform_bind_bij (bijective_add_right (matVecG R w)) f)
  exact h1.trans (h2.trans (h3.trans (bind_const_eqd _ _)))

omit [Fintype F] [Fintype Addr] [NeZero n] in
/-- **Uniformity.** If the rows of `T` are linearly independent, the vector produced by
`AuditKeyVecGen` without padding, from fresh uniform audit secret keys, is exactly uniform on
`Fin n → G`, whatever `T` is. Generalises `MembershipHiding.auditKeyVecGen_eqd` from square
invertible to rectangular systems of full row rank. -/
theorem auditKeyVecGenSet_eqd {γ : Type} {g : G} (hg : Function.Bijective (· • g : F → G))
    (H : Addr → G) (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F) (T : Finset Addr)
    (hT : RowsIndep pos coef T) (f : Option (Fin n → G) → ProbComp γ) :
    (do
        let sk ← $ᵗ (T → F)
        let ρ ← $ᵗ (Fin n → G)
        f (auditKeyVecGenSet g H pos coef T sk ρ)) =ᵈ
      (do let V ← $ᵗ (Fin n → G); f (some V)) := by
  simp only [auditKeyVecGenSet_of_rowsIndep hT]
  exact encodeSet_eqd hg H pos coef T fun V => f (some V)

/-! ## The game -/

/-- A set of at most `s` addresses. -/
abbrev BoundedSet (Addr : Type) (s : ℕ) : Type := {T : Finset Addr // T.card ≤ s}

/-- A Membership Hiding adversary against public hash functions, for a vector of size `n`,
`k` hash functions, and candidate sets of at most `s` addresses. Its state type `σ` is
arbitrary, so it can keep the hash tables for its guess. -/
structure Adversary (F G Addr σ : Type) (k n s : ℕ) where
  /-- Choose two candidate monitored sets of at most `s` addresses each, given all three hash
  tables. -/
  choose : (Addr → G) → (Addr → Fin k → Fin n) → (Addr → Fin k → F) →
    ProbComp (BoundedSet Addr s × BoundedSet Addr s × σ)
  /-- Guess which set was encoded, from the published vector (`none` if generation failed). -/
  guess : σ → Option (Fin n → G) → ProbComp Bool

/-- `AuditKeyVecGen` without padding, with its randomness: fresh uniform audit secret keys for
the addresses of `T`, and a uniformly random solution of `M ⋆ V = AK`; `none` if the rows of `T`
are linearly dependent. -/
noncomputable def vecGen (g : G) (H : Addr → G) (pos : Addr → Fin k → Fin n)
    (coef : Addr → Fin k → F) (T : Finset Addr) : ProbComp (Option (Fin n → G)) := do
  let sk ← $ᵗ (T → F)
  let ρ ← $ᵗ (Fin n → G)
  return auditKeyVecGenSet g H pos coef T sk ρ

/-- The Membership Hiding experiment with public hash functions, encoding the set `S_b`. All
hash tables are sampled first and given to the adversary before it chooses its sets. -/
noncomputable def experiment (g : G) (A : Adversary F G Addr σ k n s) (b : Bool) :
    ProbComp Bool := do
  let H ← $ᵗ (Addr → G)
  let pos ← $ᵗ (Addr → Fin k → Fin n)
  let coef ← $ᵗ (Addr → Fin k → F)
  let p ← A.choose H pos coef
  let V ← vecGen g H pos coef (if b then p.2.1 else p.1).1
  A.guess p.2.2 V

/-- The Membership Hiding advantage: the distance between encoding `S₀` and encoding `S₁`. -/
noncomputable def advantage (g : G) (A : Adversary F G Addr σ k n s) : ℝ≥0∞ :=
  𝒟[experiment g A false].boolDist 𝒟[experiment g A true]

/-! ## Splitting the experiment -/

/-- The three hash tables `(H, pos, coef)`. -/
abbrev Tables (F G Addr : Type) (k n : ℕ) : Type :=
  (Addr → G) × (Addr → Fin k → Fin n) × (Addr → Fin k → F)

/-- Sampling the hash tables. -/
noncomputable def tables : ProbComp (Tables F G Addr k n) := do
  let H ← $ᵗ (Addr → G)
  let pos ← $ᵗ (Addr → Fin k → Fin n)
  let coef ← $ᵗ (Addr → Fin k → F)
  return (H, pos, coef)

/-- The experiment encoding `S_b`, once the hash tables are fixed. -/
noncomputable def rest (g : G) (A : Adversary F G Addr σ k n s) (b : Bool)
    (w : Tables F G Addr k n) : ProbComp Bool := do
  let p ← A.choose w.1 w.2.1 w.2.2
  let V ← vecGen g w.1 w.2.1 w.2.2 (if b then p.2.1 else p.1).1
  A.guess p.2.2 V

/-- The experiment with a uniformly random vector in place of the encoding. -/
noncomputable def ideal (A : Adversary F G Addr σ k n s) (w : Tables F G Addr k n) :
    ProbComp Bool := do
  let p ← A.choose w.1 w.2.1 w.2.2
  let V ← $ᵗ (Fin n → G)
  A.guess p.2.2 (some V)

omit [Fintype F] in
/-- The experiment is the sampling of the tables followed by its rest. -/
theorem experiment_eq (g : G) (A : Adversary F G Addr σ k n s) (b : Bool) :
    experiment g A b = tables >>= rest g A b := by
  simp only [experiment, tables, rest, bind_assoc, pure_bind]

omit [Fintype F] [Fintype Addr] [NeZero n] in
/-- If the rows of `T` are linearly independent, `vecGen` publishes a uniformly random vector. -/
theorem vecGen_bind_eqd {γ : Type} {g : G} (hg : Function.Bijective (· • g : F → G))
    (H : Addr → G) (pos : Addr → Fin k → Fin n) (coef : Addr → Fin k → F) (T : Finset Addr)
    (hT : RowsIndep pos coef T) (f : Option (Fin n → G) → ProbComp γ) :
    (vecGen g H pos coef T >>= f) =ᵈ (do let V ← $ᵗ (Fin n → G); f (some V)) := by
  simp only [vecGen, bind_assoc, pure_bind]
  exact auditKeyVecGenSet_eqd hg H pos coef T hT f

omit [Fintype F] [Fintype Addr] [NeZero n] in
/-- Outside the bad event `Dep s`, the experiment encoding either set is the ideal one. -/
theorem rest_eqd_ideal {g : G} (hg : Function.Bijective (· • g : F → G))
    (A : Adversary F G Addr σ k n s) (w : Tables F G Addr k n) (hw : ¬Dep s w.2.1 w.2.2)
    (b : Bool) : rest g A b w =ᵈ ideal A w :=
  EvalDistEq.bind_right _ fun p =>
    vecGen_bind_eqd hg w.1 w.2.1 w.2.2 _ (rowsIndep_of_not_dep hw (if b then p.2.1 else p.1).2) _

omit [AddCommGroup G] [Module F G] in
/-- The bad event `Dep s` has probability at most `depBound |Addr| n k s |F|`. -/
theorem prob_tables_dep_le (s : ℕ) :
    Pr{let w ← (tables : ProbComp (Tables F G Addr k n))}[Dep s w.2.1 w.2.2] ≤
      ENNReal.ofReal (depBound (Fintype.card Addr) n k s (Fintype.card F)) := by
  refine prEvent_bind_le_of_forall_le _ _ _ fun H => ?_
  simp only [prEvent_norm]
  exact prob_dep_le s

/-- **Theorem 4** (Membership Hiding, with public hash functions and candidate sets of at most
`s` addresses): the advantage is at most `depBound Q n k s |F|`, where `Q = |Addr|` is the
number of addresses whose hashes the adversary knows. -/
theorem advantage_le {g : G} (hg : Function.Bijective (· • g : F → G))
    (A : Adversary F G Addr σ k n s) :
    advantage g A ≤ ENNReal.ofReal (depBound (Fintype.card Addr) n k s (Fintype.card F)) := by
  have hbad : ∀ b : Bool,
      Pr{let y ← tables >>= rest g A b}[y = true] ≤
        Pr{let y ← tables >>= rest g A (!b)}[y = true] +
          ENNReal.ofReal (depBound (Fintype.card Addr) n k s (Fintype.card F)) := by
    intro b
    have := prEvent_bind_le_add_of_disagree (mx := tables) (my := rest g A b)
      (oc := rest g A (!b)) (q := fun y => y = true) (D := fun w => Dep s w.2.1 w.2.2)
      (ε₂ := 0) (prob_tables_dep_le s)
      (fun w _ hw => by
        rw [add_zero]
        exact (((rest_eqd_ideal hg A w hw b).trans
          (rest_eqd_ideal hg A w hw (!b)).symm).prEvent_eq _).le)
    simpa only [add_zero] using this
  rw [advantage, experiment_eq, experiment_eq, MeasureTheory.Measure.boolDist,
    ← prEvent_eq_evalDist_singleton, ← prEvent_eq_evalDist_singleton]
  exact ENNReal.absDiff_le_iff.2 ⟨hbad false, hbad true⟩

/-- Candidate sets of at most half the vector size (`s = n / 2`) are an instance. -/
example {g : G} (hg : Function.Bijective (· • g : F → G))
    (A : Adversary F G Addr σ k n (n / 2)) :
    advantage g A ≤
      ENNReal.ofReal (depBound (Fintype.card Addr) n k (n / 2) (Fintype.card F)) :=
  advantage_le hg A

end AuditPay.MembershipHidingPublic
