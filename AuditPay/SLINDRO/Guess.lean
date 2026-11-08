/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.SLINDRO.Generic
import AuditPay.SLINDRO.OW
import AuditPay.SLINDRO.Single
import AuditPay.KdfRO.NoteHiding.Guess

/-!
# Theorem 2 with a random-oracle KDF, the paper's scheme: plain CDH with a loss factor

**Scheme unchanged (Algorithm 2), plain CDH, loss factor `q + 2`.** For the SL-IND game of
`AuditPay.SLINDRO` with the selective encryption of Algorithm 2 (`AuditPay.SLINDRO.Single.game`),
the advantage of an adversary making at most `q₁` KDF queries in its first phase and `q₂` in its
second is at most

  `hopBound false + Mixer(mixerReduction A) + hopBound true`,

with, for the hidden bit `b` and `q = q₁ + q₂ + 1`,

  `hopBound b = ZK(zkReduction A b) + (q + 1) · (CDH(cdhReductionS A b) + 1/|F|) +
                 OT(otReductionS A b) + (q + 1) · (CDH(cdhReductionR A b) + 1/|F|) +
                 OT(otReductionR A b)`.

The reduction has no decision oracle and no trapdoor: it guesses which of the queried points is
the shared point, by picking an index uniformly in `Fin (q + 1)` and outputting the point with
that index in the final cache, which holds at most `q = q₁ + q₂ + 1` points (the adversary's
queries and the challenger's query for the other ciphertext). If the shared point was queried,
the guess is right with probability at least `1/(q + 1)`. This is the classical argument;
`AuditPay.SLINDRO.StrongDH` and `AuditPay.SLINDRO.Twin` remove the loss.
-/

open OracleComp OracleSpec DiffieHellman ENNReal

namespace AuditPay.SLINDRO.Guess

open KdfRO
open AuditPay.SLIND (zkAdvantage otAdvantage mixerAdvantage)
open AuditPay.SLINDDrop (Choice valid)

variable {F G Addr Key Note DTx WCore C Proof σ : Type} {k n : ℕ}
  [Field F] [Fintype F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]
  [Fintype Addr] [DecidableEq Addr] [SampleableType Key]
  (sel : Selection F Addr k n) (P : Params F G Addr F G Key Note DTx WCore C Proof k n)
  (A : Adversary F G Addr G G Key DTx WCore C Proof σ n)

/-! ## The one-wayness adversaries -/

/-- The state of the one-wayness adversaries after the first phase: `H`, the SL-IND adversary's
choice, and the KDF cache. -/
abbrev State (F G Addr Key σ : Type) (n : ℕ) :=
  (Addr → G) × Choice F Addr σ n × (G →ₒ Key).QueryCache

/-- The one-wayness adversary for the sender's ciphertext and bit `b` that guesses: it
simulates the fresh-key hybrid with its own lazily sampled KDF (the sender's ephemeral point
being `R`), picks an index uniformly in `Fin (q + 1)` and outputs the queried point with that
index (or `0`). -/
noncomputable def owAdversaryS (q : ℕ) (b : Bool) :
    OW.Adversary F G Addr (State F G Addr Key σ n) n where
  choose H := do
    let z ← roRun (A.choose H) ∅
    return ⟨z.1.req, z.1.sk, z.1.fill, if b then z.1.d₁ else z.1.d₀, (H, z.1, z.2)⟩
  guess st R := do
    let ox ← setup sel P b st.1 st.2.1
    match ox with
    | none => return 0
    | some x => do
      let rR ← $ᵗ F
      let keyS ← $ᵗ Key
      let v ← roRun (simTailC (single F P.g) P A b .real x rR (P.senc keyS (x.note b), R)) st.2.2
      let j ← $ᵗ (Fin (q + 1))
      return ((cachedPoints v.2)[(j : ℕ)]?).getD 0

/-- The one-wayness adversary for the recipient's ciphertext and bit `b` that guesses, with the
sender's ciphertext a dummy under a fresh key. -/
noncomputable def owAdversaryR (q : ℕ) (b : Bool) :
    OW.Adversary F G Addr (State F G Addr Key σ n) n where
  choose H := do
    let z ← roRun (A.choose H) ∅
    return ⟨z.1.req, z.1.sk, z.1.fill, z.1.wAddr, (H, z.1, z.2)⟩
  guess st R := do
    let ox ← setup sel P b st.1 st.2.1
    match ox with
    | none => return 0
    | some x => do
      let rS ← $ᵗ F
      let keyS ← $ᵗ Key
      let keyR ← $ᵗ Key
      let v ← roRun (simTailD P A x (P.senc keyS P.dummy, rS • P.g) (P.senc keyR (x.note b), R))
        st.2.2
      let j ← $ᵗ (Fin (q + 1))
      return ((cachedPoints v.2)[(j : ℕ)]?).getD 0

/-- The CDH reduction with a guess for the sender's ciphertext and bit `b`. -/
noncomputable def cdhReductionS (q : ℕ) (b : Bool) : CDHAdversary F G :=
  OW.cdhReduction P.pos P.coef sel (owAdversaryS sel P A q b)

/-- The CDH reduction with a guess for the recipient's ciphertext and bit `b`. -/
noncomputable def cdhReductionR (q : ℕ) (b : Bool) : CDHAdversary F G :=
  OW.cdhReduction P.pos P.coef sel (owAdversaryR sel P A q b)

/-! ## The one-wayness experiments as the fresh-key hybrids followed by the guess -/

/-- The outcome of a hybrid as a note-hiding outcome for the sender's ciphertext: the sender's
point, its ephemeral scalar, and the final cache. -/
def outS (b : Bool) (o : Out F G Addr F G Key Note DTx WCore σ n) : NoteHiding.Outcome G F G Key :=
  (o.x.pt P.pos P.coef (o.x.sender b), o.rS, o.cache)

/-- The outcome of a hybrid as a note-hiding outcome for the recipient's ciphertext. -/
def outR (o : Out F G Addr F G Key Note DTx WCore σ n) : NoteHiding.Outcome G F G Key :=
  (o.x.pt P.pos P.coef o.x.c.wAddr, o.rR, o.cache)

/-- The last step of `owAdversaryS`, as a function of the outcome of the fresh-key hybrid
(`NoteHiding.Guess.leaf`). -/
noncomputable def leafS (q : ℕ) (b : Bool)
    (x : Bool × Option (Out F G Addr F G Key Note DTx WCore σ n)) : ProbComp Bool :=
  NoteHiding.Guess.leaf q (x.1, x.2.map (outS P b))

/-- The last step of `owAdversaryR`, as a function of the outcome of the fresh-key hybrid. -/
noncomputable def leafR (q : ℕ)
    (x : Bool × Option (Out F G Addr F G Key Note DTx WCore σ n)) : ProbComp Bool :=
  NoteHiding.Guess.leaf q (x.1, x.2.map (outR P))

omit [Fintype F] [SampleableType F] [AddCommGroup G] [Module F G] [SampleableType G]
  [DecidableEq G] [Fintype Addr] [SampleableType Key] in
/-- The sender of a valid choice is not selected (on choices). -/
theorem sender_not_mem_select {c : Choice F Addr σ n} (hv : valid sel P.pos P.coef c = true)
    (b : Bool) : (if b then c.d₁ else c.d₀) ∉ sel.select P.pos P.coef c.req := by
  have h := SLINDDrop.valid_excl hv
  cases b
  · exact h.1
  · exact h.2.1

omit [Fintype F] in
/-- The fresh-key hybrid followed by the guess succeeds at most as often as `owAdversaryS` in
the one-wayness game (the two differ only on invalid choices, where the former outputs
`false`). -/
theorem prEvent_leafS_le_experiment (q : ℕ) (b : Bool) :
    Pr{let y ← hybrid (single F P.g) sel P A b true .fresh .real >>= leafS P q b}[y = true] ≤
      Pr{let y ← OW.experiment P.g P.pos P.coef sel (owAdversaryS sel P A q b)}[y = true] := by
  simp only [OW.experiment, owAdversaryS, hybrid, bind_assoc, pure_bind]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun H => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun z => ?_
  by_cases hsel : (if b then z.1.d₁ else z.1.d₀) ∈ sel.select P.pos P.coef z.1.req
  · have hv : ¬valid sel P.pos P.coef z.1 = true := fun hv =>
      sender_not_mem_select sel P hv b hsel
    simp [setup_of_not_valid hv, leafS, NoteHiding.Guess.leaf]
  · simp only [OW.Choice.selected, hsel, ite_false]
    -- the one-wayness game samples `r` before the deposits; move it after them
    rw [(bind_swap_eqd _ _ _).prEvent_eq]
    refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun ox hox => ?_
    cases ox with
    | none => simp [leafS, NoteHiding.Guess.leaf]
    | some x =>
      obtain ⟨hv, hH, hc, hV⟩ := setup_spec hox
      obtain ⟨H', c', V', dep₀, dep₁, core⟩ := x
      simp only at hH hc hV
      subst hH hc hV
      simp only [keyQ, tailS, tailC_true, msg, single, roRun_liftM, bind_map_left, bind_assoc,
        pure_bind, leafS, outS, Option.map_some, NoteHiding.Guess.leaf]
      exact le_rfl

omit [Fintype F] in
/-- The fresh-key hybrid (the sender's ciphertext a dummy) followed by the guess succeeds at
most as often as `owAdversaryR` in the one-wayness game. -/
theorem prEvent_leafR_le_experiment (q : ℕ) (b : Bool) :
    Pr{let y ← hybrid (single F P.g) sel P A b true .dummy .fresh >>= leafR P q}[y = true] ≤
      Pr{let y ← OW.experiment P.g P.pos P.coef sel (owAdversaryR sel P A q b)}[y = true] := by
  simp only [OW.experiment, owAdversaryR, hybrid, bind_assoc, pure_bind]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun H => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun z => ?_
  by_cases hsel : z.1.wAddr ∈ sel.select P.pos P.coef z.1.req
  · have hv : ¬valid sel P.pos P.coef z.1 = true := fun hv =>
      (SLINDDrop.valid_excl hv).2.2 hsel
    simp [setup_of_not_valid hv, leafR, NoteHiding.Guess.leaf]
  · simp only [OW.Choice.selected, hsel, ite_false]
    rw [(bind_swap_eqd _ _ _).prEvent_eq]
    refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun ox hox => ?_
    cases ox with
    | none => simp [leafR, NoteHiding.Guess.leaf]
    | some x =>
      obtain ⟨hv, hH, hc, hV⟩ := setup_spec hox
      obtain ⟨H', c', V', dep₀, dep₁, core⟩ := x
      simp only at hH hc hV
      subst hH hc hV
      simp only [keyQ, tailS, tailC_true, simTailC, msg, single, roRun_liftM, roRun_bind,
        bind_map_left, bind_assoc, pure_bind, leafR, outR, Option.map_some, NoteHiding.Guess.leaf]
      -- the hybrid samples `rS` before `rR`; the one-wayness game gives `rR` first
      exact le_of_eq ((bind_swap_eqd _ _ _).prEvent_eq _)

/-! ## The bounds -/

omit [Fintype F] in
/-- The sender's shared point is queried in the fresh-key hybrid with probability at most
`q + 1` times the success probability of `owAdversaryS` in the one-wayness game, where
`q = q₁ + q₂ + 1` bounds the number of queried points. -/
theorem queryProbS_le_experiment {q₁ q₂ : ℕ} (hq : A.QueryBound q₁ q₂) (b : Bool) :
    queryProbS (single F P.g) sel P A b ≤
      ((q₁ + q₂ + 1 + 1 : ℕ) : ℝ≥0∞) *
        𝒟[OW.experiment P.g P.pos P.coef sel (owAdversaryS sel P A (q₁ + q₂ + 1) b)] {true} := by
  rw [← prEvent_eq_evalDist_singleton]
  set q := q₁ + q₂ + 1
  have hsz : queryProbS (single F P.g) sel P A b =
      Pr{let x ← hybrid (single F P.g) sel P A b true .fresh .real}[
        QueriedS (single F P.g) P.pos P.coef b x.2 ∧
          ∀ o, x.2 = some o → (cachedPoints o.cache).length ≤ q] :=
    prEvent_congr_of_support _ _ _ fun x hx =>
      ⟨fun h => ⟨h, fun o ho => length_cachedPoints_le_of_mem_support_hybrid (single F P.g) sel P
          hq b (by simp) .real hx ho⟩, fun h => h.1⟩
  rw [hsz]
  have hq1 : ((q + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by simp
  have hq2 : ((q + 1 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have h := mul_le_prEvent_bind_of_forall (hybrid (single F P.g) sel P A b true .fresh .real)
    (leafS P q b) (fun x => QueriedS (single F P.g) P.pos P.coef b x.2 ∧
      ∀ o, x.2 = some o → (cachedPoints o.cache).length ≤ q) (fun y => y = true) le_rfl
    fun x hx => by
      obtain ⟨v, o⟩ := x
      cases o with
      | none => exact absurd hx.1 (by simp [QueriedS])
      | some o =>
        refine NoteHiding.Guess.le_prEvent_leaf (g := P.g) (fun o' ho' => ?_)
          ⟨outS P b o, rfl, hx.1⟩
        simp only [Option.map_some, Option.some.injEq] at ho'
        subst ho'
        exact hx.2 o rfl
  calc _ = ((q + 1 : ℕ) : ℝ≥0∞) *
        (Pr{let x ← hybrid (single F P.g) sel P A b true .fresh .real}[
          QueriedS (single F P.g) P.pos P.coef b x.2 ∧
            ∀ o, x.2 = some o → (cachedPoints o.cache).length ≤ q] *
          ((q + 1 : ℕ) : ℝ≥0∞)⁻¹) := by
        rw [mul_comm _ (_)⁻¹, ← mul_assoc, ENNReal.mul_inv_cancel hq1 hq2, one_mul]
    _ ≤ ((q + 1 : ℕ) : ℝ≥0∞) *
        Pr{let y ← hybrid (single F P.g) sel P A b true .fresh .real >>= leafS P q b}[
          y = true] := by
        gcongr
    _ ≤ _ := by
        gcongr
        exact prEvent_leafS_le_experiment sel P A q b

omit [Fintype F] in
/-- The recipient's shared point is queried in the fresh-key hybrid (the sender's ciphertext a
dummy) with probability at most `q + 1` times the success probability of `owAdversaryR` in the
one-wayness game. -/
theorem queryProbR_le_experiment {q₁ q₂ : ℕ} (hq : A.QueryBound q₁ q₂) (b : Bool) :
    queryProbR (single F P.g) sel P A b ≤
      ((q₁ + q₂ + 1 + 1 : ℕ) : ℝ≥0∞) *
        𝒟[OW.experiment P.g P.pos P.coef sel (owAdversaryR sel P A (q₁ + q₂ + 1) b)] {true} := by
  rw [← prEvent_eq_evalDist_singleton]
  set q := q₁ + q₂ + 1
  have hsz : queryProbR (single F P.g) sel P A b =
      Pr{let x ← hybrid (single F P.g) sel P A b true .dummy .fresh}[
        QueriedR (single F P.g) P.pos P.coef x.2 ∧
          ∀ o, x.2 = some o → (cachedPoints o.cache).length ≤ q] :=
    prEvent_congr_of_support _ _ _ fun x hx =>
      ⟨fun h => ⟨h, fun o ho => length_cachedPoints_le_of_mem_support_hybrid (single F P.g) sel P
          hq b (by simp) .fresh hx ho⟩, fun h => h.1⟩
  rw [hsz]
  have hq1 : ((q + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by simp
  have hq2 : ((q + 1 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have h := mul_le_prEvent_bind_of_forall (hybrid (single F P.g) sel P A b true .dummy .fresh)
    (leafR P q) (fun x => QueriedR (single F P.g) P.pos P.coef x.2 ∧
      ∀ o, x.2 = some o → (cachedPoints o.cache).length ≤ q) (fun y => y = true) le_rfl
    fun x hx => by
      obtain ⟨v, o⟩ := x
      cases o with
      | none => exact absurd hx.1 (by simp [QueriedR])
      | some o =>
        refine NoteHiding.Guess.le_prEvent_leaf (g := P.g) (fun o' ho' => ?_)
          ⟨outR P o, rfl, hx.1⟩
        simp only [Option.map_some, Option.some.injEq] at ho'
        subst ho'
        exact hx.2 o rfl
  calc _ = ((q + 1 : ℕ) : ℝ≥0∞) *
        (Pr{let x ← hybrid (single F P.g) sel P A b true .dummy .fresh}[
          QueriedR (single F P.g) P.pos P.coef x.2 ∧
            ∀ o, x.2 = some o → (cachedPoints o.cache).length ≤ q] *
          ((q + 1 : ℕ) : ℝ≥0∞)⁻¹) := by
        rw [mul_comm _ (_)⁻¹, ← mul_assoc, ENNReal.mul_inv_cancel hq1 hq2, one_mul]
    _ ≤ ((q + 1 : ℕ) : ℝ≥0∞) *
        Pr{let y ← hybrid (single F P.g) sel P A b true .dummy .fresh >>= leafR P q}[
          y = true] := by
        gcongr
    _ ≤ _ := by
        gcongr
        exact prEvent_leafR_le_experiment sel P A q b

/-- The sender's shared point is queried in the fresh-key hybrid with probability at most
`q₁ + q₂ + 2` times the CDH success probability of `cdhReductionS` plus `1/|F|`. -/
theorem queryProbS_le (hg : Function.Bijective (· • P.g : F → G)) {q₁ q₂ : ℕ}
    (hq : A.QueryBound q₁ q₂) (b : Bool) :
    queryProbS (single F P.g) sel P A b ≤
      ((q₁ + q₂ + 1 + 1 : ℕ) : ℝ≥0∞) *
        (𝒟[cdhExperiment P.g (cdhReductionS sel P A (q₁ + q₂ + 1) b)] {true} +
          (Fintype.card F : ℝ≥0∞)⁻¹) :=
  (queryProbS_le_experiment sel P A hq b).trans
    (mul_le_mul_right (OW.success_le P.g P.pos P.coef sel hg (owAdversaryS sel P A _ b)) _)

/-- The recipient's shared point is queried in the fresh-key hybrid with probability at most
`q₁ + q₂ + 2` times the CDH success probability of `cdhReductionR` plus `1/|F|`. -/
theorem queryProbR_le (hg : Function.Bijective (· • P.g : F → G)) {q₁ q₂ : ℕ}
    (hq : A.QueryBound q₁ q₂) (b : Bool) :
    queryProbR (single F P.g) sel P A b ≤
      ((q₁ + q₂ + 1 + 1 : ℕ) : ℝ≥0∞) *
        (𝒟[cdhExperiment P.g (cdhReductionR sel P A (q₁ + q₂ + 1) b)] {true} +
          (Fintype.card F : ℝ≥0∞)⁻¹) :=
  (queryProbR_le_experiment sel P A hq b).trans
    (mul_le_mul_right (OW.success_le P.g P.pos P.coef sel hg (owAdversaryR sel P A _ b)) _)

variable [Inhabited Addr] [Inhabited WCore] [Inhabited C]

/-- The cost of moving from the SL-IND game for bit `b` to the hybrid with a simulated proof and
two dummy ciphertexts, under CDH with a guess, for an adversary making at most `q₁ + q₂` KDF
queries. -/
noncomputable def hopBound (q₁ q₂ : ℕ) (b : Bool) : ℝ≥0∞ :=
  zkAdvantage P.zk (zkReduction (single F P.g) sel P A b) +
    ((q₁ + q₂ + 1 + 1 : ℕ) : ℝ≥0∞) *
      (𝒟[cdhExperiment P.g (cdhReductionS sel P A (q₁ + q₂ + 1) b)] {true} +
        (Fintype.card F : ℝ≥0∞)⁻¹) +
    otAdvantage P.senc (otReductionS (single F P.g) sel P A b) +
    ((q₁ + q₂ + 1 + 1 : ℕ) : ℝ≥0∞) *
      (𝒟[cdhExperiment P.g (cdhReductionR sel P A (q₁ + q₂ + 1) b)] {true} +
        (Fintype.card F : ℝ≥0∞)⁻¹) +
    otAdvantage P.senc (otReductionR (single F P.g) sel P A b)

/-- **Theorem 2 (SL-IND) with a random-oracle KDF, the paper's scheme, under plain CDH**
(option 1). For a generator `g` and every selection rule, the SL-IND advantage of an adversary
against Algorithm 2 that makes at most `q₁` KDF queries before and `q₂` after the challenge is
at most the base-mixer unlinkability advantage of `mixerReduction` plus, for each value of the
hidden bit, the zero-knowledge advantage of `zkReduction`, and, for each of the two
ciphertexts, `q₁ + q₂ + 2` times the CDH success probability of the reduction
(`cdhReductionS`, `cdhReductionR`) plus `1/|F|`, and the one-time advantage of the reduction
(`otReductionS`, `otReductionR`). -/
theorem advantage_le (hg : Function.Bijective (· • P.g : F → G)) {q₁ q₂ : ℕ}
    (hq : A.QueryBound q₁ q₂) :
    Single.advantage sel P A ≤
      hopBound sel P A q₁ q₂ false +
        mixerAdvantage P.mixer (mixerReduction (single F P.g) sel P A) +
        hopBound sel P A q₁ q₂ true := by
  rw [Single.advantage_eq]
  refine (advantage_le_queryProb (single F P.g) sel P A).trans ?_
  simp only [SLINDRO.hopBound, hopBound]
  gcongr
  · exact queryProbS_le sel P A hg hq false
  · exact queryProbR_le sel P A hg hq false
  · exact queryProbS_le sel P A hg hq true
  · exact queryProbR_le sel P A hg hq true

end AuditPay.SLINDRO.Guess
