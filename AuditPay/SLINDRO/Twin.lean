/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.SLINDRO.Generic
import AuditPay.SLINDRO.OW
import AuditPay.KdfRO.NoteHiding.Twin

/-!
# Theorem 2 with a random-oracle KDF, twin variant: reduction to plain CDH

**Scheme changed (two ephemeral values per ciphertext), tight reduction to CDH.** For the SL-IND
game of `AuditPay.SLINDRO` with the twin variant of selective encryption (`AuditPay.Twin`,
`KdfRO.twin`: a ciphertext is `(SymEnc_{KDF(r₁ • P, r₂ • P)}(note), r₁ • g, r₂ • g)` with
`P = RetrieveKey(V, a) - H(a)`), the advantage of an adversary making at most `q₁` KDF queries in
its first phase and `q₂` in its second is at most

  `hopBound false + Mixer(mixerReduction A) + hopBound true`,

with, for the hidden bit `b` and `q = q₁ + q₂ + 1`,

  `hopBound b = ZK(zkReduction A b) + (CDH(cdhReductionS A b) + 1/|F| + q/|F|) +
                 OT(otReductionS A b) + (CDH(cdhReductionR A b) + 1/|F| + q/|F|) +
                 OT(otReductionR A b)`,

where `CDH` is the success probability in VCV-io's `cdhExperiment`.

The statement and witness of the withdrawal proof carry two ephemeral points and two ephemeral
scalars per ciphertext (`Stmt G WCore C (G × G) n`, `Wit Addr Note (F × F)`).

## The trapdoor test on the ephemeral side

By `AuditPay.SLINDRO.advantage_le_queryProb` it remains to bound the probability that the pair
of shared points of the sender's (resp. recipient's) ciphertext is queried in the hybrid where
its key is fresh. The reduction must find that pair among the queried pairs without a decision
oracle: this is the twin Diffie–Hellman trapdoor test of Cash, Kiltz and Shoup on the ephemeral
side, exactly as in `AuditPay.NoteHiding.Twin`. The one-wayness adversary (plain, no oracle;
`AuditPay.SLINDRO.OW`) forwards the SL-IND adversary's choice with the target address, receives
the first ephemeral point `R₁`, picks a trapdoor `(s, t)`, sets `R₂ = s • g - t • R₁` (so that
`r₂ = s - t r₁` is uniform and `t` is hidden), simulates the rest of the fresh-key hybrid, and
outputs the first component of the first queried pair `(Z₁, Z₂)` with `t • Z₁ + Z₂ = s • P`
(`NoteHiding.Twin.extract`). The true pair passes; a wrong pair passes with probability at most
`1/|F|` over `t` (`NoteHiding.Twin.prob_test_le`), and the final cache holds at most
`q₁ + 1 + q₂` pairs (the adversary's queries and the challenger's query for the other
ciphertext), whence the `q/|F|` term. `OW.success_le` then gives the CDH bound.
-/

open OracleComp OracleSpec DiffieHellman ENNReal

namespace AuditPay.SLINDRO.Twin

open KdfRO
open AuditPay.SLIND (zkAdvantage otAdvantage mixerAdvantage)
open AuditPay.SLINDDrop (Choice valid)
open AuditPay.NoteHiding.Twin (extract)

variable {F G Addr Key Note DTx WCore C Proof σ : Type} {k n : ℕ}
  [Field F] [Fintype F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]
  [Fintype Addr] [DecidableEq Addr] [SampleableType Key]
  (sel : Selection F Addr k n)
  (P : Params F G Addr (F × F) (G × G) Key Note DTx WCore C Proof k n)
  (A : Adversary F G Addr (G × G) (G × G) Key DTx WCore C Proof σ n)

/-! ## The game, written out -/

/-- The SL-IND game for bit `b` with a random-oracle KDF and the twin variant: ciphertext
`(SymEnc_{KDF(r₁ • P, r₂ • P)}(note), r₁ • g, r₂ • g)` with `P = RetrieveKey(V, a) - H(a)`, for
the sender `d_b` and the recipient `w_addr`, with the KDF queried at the pairs. -/
noncomputable def game (b : Bool) : OracleComp (unifSpec + ((G × G) →ₒ Key)) Bool := do
  let H ← $ᵗ (Addr → G)
  let c ← A.choose H
  let ox ← setup sel P b H c
  match ox with
  | none => return false
  | some x => do
    let rS ← $ᵗ (F × F)
    let rR ← $ᵗ (F × F)
    let keyS ← query (spec := (G × G) →ₒ Key)
      (AuditPay.Twin.encPoint rS (retrieveKey P.pos P.coef x.V (x.sender b)) (x.H (x.sender b)))
    let keyR ← query (spec := (G × G) →ₒ Key)
      (AuditPay.Twin.encPoint rR (retrieveKey P.pos P.coef x.V x.c.wAddr) (x.H x.c.wAddr))
    let ctS := (P.senc keyS (x.note b), (rS.1 • P.g, rS.2 • P.g))
    let ctR := (P.senc keyR (x.note b), (rR.1 • P.g, rR.2 • P.g))
    let π ← P.zk.prove (stmt x ctS ctR) (x.note b, x.sender b, rS, rR)
    finish A x ctS ctR π

omit [Fintype F] [DecidableEq G] [SampleableType Key] in
theorem game_eq (b : Bool) : game sel P A b = SLINDRO.game (twin F P.g) sel P A b := rfl

/-- The SL-IND experiment for bit `b`: the game run in the random oracle model. -/
noncomputable def experiment (b : Bool) : ProbComp Bool := roExec (game sel P A b)

/-- The SL-IND advantage with a random-oracle KDF, for the twin variant. -/
noncomputable def advantage : ℝ≥0∞ :=
  𝒟[experiment sel P A false].boolDist 𝒟[experiment sel P A true]

omit [Fintype F] in
theorem advantage_eq : advantage sel P A = SLINDRO.advantage (twin F P.g) sel P A := rfl

/-! ## The one-wayness adversaries -/

/-- The state of the one-wayness adversaries after the first phase: `H`, the SL-IND adversary's
choice, and the KDF cache. -/
abbrev State (F G Addr Key σ : Type) (n : ℕ) :=
  (Addr → G) × Choice F Addr σ n × ((G × G) →ₒ Key).QueryCache

/-- The one-wayness adversary for the sender's ciphertext and bit `b`. It forwards the SL-IND
adversary's choice with the sender `d_b` as target; given `R`, it picks a trapdoor `(s, t)`,
uses `(R, s • g - t • R)` as the sender's ephemeral points, simulates the fresh-key hybrid (the
recipient's ciphertext real, under its own lazily sampled KDF; the sender's note under a fresh
key; a simulated proof), and extracts with the trapdoor test. -/
noncomputable def owAdversaryS (b : Bool) : OW.Adversary F G Addr (State F G Addr Key σ n) n where
  choose H := do
    let z ← roRun (A.choose H) ∅
    return ⟨z.1.req, z.1.sk, z.1.fill, if b then z.1.d₁ else z.1.d₀, (H, z.1, z.2)⟩
  guess st R := do
    let s ← $ᵗ F
    let t ← $ᵗ F
    let ox ← setup sel P b st.1 st.2.1
    match ox with
    | none => return 0
    | some x => do
      let rR ← $ᵗ (F × F)
      let keyS ← $ᵗ Key
      let v ← roRun (simTailC (twin F P.g) P A b .real x rR
        (P.senc keyS (x.note b), (R, s • P.g - t • R))) st.2.2
      return extract s t (x.pt P.pos P.coef (x.sender b)) v.2

/-- The one-wayness adversary for the recipient's ciphertext and bit `b`, with the sender's
ciphertext a dummy under a fresh key. -/
noncomputable def owAdversaryR (b : Bool) : OW.Adversary F G Addr (State F G Addr Key σ n) n where
  choose H := do
    let z ← roRun (A.choose H) ∅
    return ⟨z.1.req, z.1.sk, z.1.fill, z.1.wAddr, (H, z.1, z.2)⟩
  guess st R := do
    let s ← $ᵗ F
    let t ← $ᵗ F
    let ox ← setup sel P b st.1 st.2.1
    match ox with
    | none => return 0
    | some x => do
      let rS ← $ᵗ (F × F)
      let keyS ← $ᵗ Key
      let keyR ← $ᵗ Key
      let v ← roRun (simTailD P A x (P.senc keyS P.dummy, (rS.1 • P.g, rS.2 • P.g))
        (P.senc keyR (x.note b), (R, s • P.g - t • R))) st.2.2
      return extract s t (x.pt P.pos P.coef x.c.wAddr) v.2

/-- The CDH reduction for the sender's ciphertext and bit `b`. -/
noncomputable def cdhReductionS (b : Bool) : CDHAdversary F G :=
  OW.cdhReduction P.pos P.coef sel (owAdversaryS sel P A b)

/-- The CDH reduction for the recipient's ciphertext and bit `b`. -/
noncomputable def cdhReductionR (b : Bool) : CDHAdversary F G :=
  OW.cdhReduction P.pos P.coef sel (owAdversaryR sel P A b)


/-! ## The one-wayness experiments as the fresh-key hybrids followed by the trapdoor test -/

/-- The outcome of a hybrid as a note-hiding outcome for the sender's ciphertext: the sender's
point, its ephemeral scalars, and the final cache. -/
def outS (b : Bool) (o : Out F G Addr (F × F) (G × G) Key Note DTx WCore σ n) :
    NoteHiding.Outcome G (F × F) (G × G) Key :=
  (o.x.pt P.pos P.coef (o.x.sender b), o.rS, o.cache)

/-- The outcome of a hybrid as a note-hiding outcome for the recipient's ciphertext. -/
def outR (o : Out F G Addr (F × F) (G × G) Key Note DTx WCore σ n) :
    NoteHiding.Outcome G (F × F) (G × G) Key :=
  (o.x.pt P.pos P.coef o.x.c.wAddr, o.rR, o.cache)

/-- The last step of `owAdversaryS`, as a function of the outcome of the fresh-key hybrid:
sample the trapdoor `t` (the second ephemeral scalar is `r₂ = s - t r₁`, so `s = r₂ + t r₁`) and
check whether the extracted point is `r₁ • P` (`NoteHiding.Twin.leaf`). -/
noncomputable def leafS (b : Bool)
    (x : Bool × Option (Out F G Addr (F × F) (G × G) Key Note DTx WCore σ n)) : ProbComp Bool :=
  NoteHiding.Twin.leaf (x.1, x.2.map (outS P b))

/-- The last step of `owAdversaryR`, as a function of the outcome of the fresh-key hybrid. -/
noncomputable def leafR
    (x : Bool × Option (Out F G Addr (F × F) (G × G) Key Note DTx WCore σ n)) : ProbComp Bool :=
  NoteHiding.Twin.leaf (x.1, x.2.map (outR P))

omit [Fintype F] [SampleableType F] [DecidableEq G] in
/-- The reparametrization of the trapdoor: `(r₁, s) ↦ (r₁, s - t r₁)` is a bijection. -/
theorem shear_bijective (t : F) : Function.Bijective fun a : F × F => (a.1, a.2 - t * a.1) :=
  (Equiv.prodShear (Equiv.refl F) fun r => Equiv.subRight (t * r)).bijective

omit [Fintype F] [Fintype Addr] [DecidableEq Addr] in
/-- The second phase of `owAdversaryS` for a valid choice, with `R = r • g`, is the fresh-key
hybrid's continuation followed by `leafS`: the second ephemeral scalar `s - t r` is uniform, and
the adversary's view does not depend on `t`, which can therefore be sampled at the end. -/
theorem bodyS_eqd (b : Bool) (x : Ctx F G Addr Note DTx WCore σ n)
    (c : ((G × G) →ₒ Key).QueryCache) :
    (do
      let r ← $ᵗ F
      let s ← $ᵗ F
      let t ← $ᵗ F
      let rR ← $ᵗ (F × F)
      let keyS ← $ᵗ Key
      let v ← roRun (simTailC (twin F P.g) P A b .real x rR
        (P.senc keyS (x.note b), (r • P.g, s • P.g - t • (r • P.g)))) c
      return decide (extract s t (x.pt P.pos P.coef (x.sender b)) v.2 =
        r • x.pt P.pos P.coef (x.sender b))) =ᵈ
    (do
      let rS ← $ᵗ (F × F)
      let rR ← $ᵗ (F × F)
      let w ← roRun (keyQ (twin F P.g) .fresh rS (x.pt P.pos P.coef (x.sender b))) c
      let v ← roRun (tailS (twin F P.g) P A b true .fresh .real x rS rR w.1) w.2
      leafS P b (v.1, some ⟨x, rS, rR, v.2⟩)) := by
  simp only [keyQ, tailS, tailC_true, msg, twin, roRun_liftM, bind_map_left, leafS, outS,
    Option.map_some, NoteHiding.Twin.leaf]
  -- move the trapdoor `t` to the front on both sides
  refine EvalDistEq.trans ?_ (bind_last_swap4_eqd _ _ _ _ _ _).symm
  refine ((EvalDistEq.bind_right _ fun r => bind_swap_eqd _ _ _).trans (bind_swap_eqd _ _ _)).trans
    ?_
  refine EvalDistEq.bind_right _ fun t => ?_
  -- merge `(r, s)` into one sample and reparametrize `s = r₂ + t r₁`
  refine (prod_merge_eqd _).trans ?_
  refine EvalDistEq.trans ?_ (uniform_bind_bij (shear_bijective t) _)
  refine EvalDistEq.bind_right _ fun a => ?_
  simp only [sub_smul, mul_smul, sub_add_cancel]
  exact .rfl

omit [Fintype F] [Fintype Addr] [DecidableEq Addr] in
/-- The second phase of `owAdversaryR` for a valid choice, with `R = r • g`, is the fresh-key
hybrid's continuation (the sender's ciphertext a dummy) followed by `leafR`. -/
theorem bodyR_eqd (b : Bool) (x : Ctx F G Addr Note DTx WCore σ n)
    (c : ((G × G) →ₒ Key).QueryCache) :
    (do
      let r ← $ᵗ F
      let s ← $ᵗ F
      let t ← $ᵗ F
      let rS ← $ᵗ (F × F)
      let keyS ← $ᵗ Key
      let keyR ← $ᵗ Key
      let v ← roRun (simTailD P A x (P.senc keyS P.dummy, (rS.1 • P.g, rS.2 • P.g))
        (P.senc keyR (x.note b), (r • P.g, s • P.g - t • (r • P.g)))) c
      return decide (extract s t (x.pt P.pos P.coef x.c.wAddr) v.2 =
        r • x.pt P.pos P.coef x.c.wAddr)) =ᵈ
    (do
      let rS ← $ᵗ (F × F)
      let rR ← $ᵗ (F × F)
      let w ← roRun (keyQ (twin F P.g) .dummy rS (x.pt P.pos P.coef (x.sender b))) c
      let v ← roRun (tailS (twin F P.g) P A b true .dummy .fresh x rS rR w.1) w.2
      leafR P (v.1, some ⟨x, rS, rR, v.2⟩)) := by
  simp only [keyQ, tailS, tailC_true, simTailC, msg, twin, roRun_liftM, roRun_bind, bind_map_left,
    bind_assoc, leafR, outR, Option.map_some, NoteHiding.Twin.leaf]
  -- the hybrid samples `rS` before `rR`; the one-wayness game gives `rR` first
  refine EvalDistEq.trans ?_ (bind_swap_eqd _ _ _).symm
  -- move the trapdoor `t` to the front on both sides
  refine EvalDistEq.trans ?_ (bind_last_swap5_eqd _ _ _ _ _ _ _).symm
  refine ((EvalDistEq.bind_right _ fun r => bind_swap_eqd _ _ _).trans (bind_swap_eqd _ _ _)).trans
    ?_
  refine EvalDistEq.bind_right _ fun t => ?_
  refine (prod_merge_eqd _).trans ?_
  refine EvalDistEq.trans ?_ (uniform_bind_bij (shear_bijective t) _)
  refine EvalDistEq.bind_right _ fun a => ?_
  simp only [sub_smul, mul_smul, sub_add_cancel]
  exact .rfl

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
/-- The fresh-key hybrid followed by the trapdoor test succeeds at most as often as
`owAdversaryS` in the one-wayness game (the two differ only on invalid choices, where the
former outputs `false`). -/
theorem prEvent_leafS_le_experiment (b : Bool) :
    Pr{let y ← hybrid (twin F P.g) sel P A b true .fresh .real >>= leafS P b}[y = true] ≤
      Pr{let y ← OW.experiment P.g P.pos P.coef sel (owAdversaryS sel P A b)}[y = true] := by
  simp only [OW.experiment, owAdversaryS, hybrid, bind_assoc, pure_bind]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun H => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun z => ?_
  by_cases hsel : (if b then z.1.d₁ else z.1.d₀) ∈ sel.select P.pos P.coef z.1.req
  · have hv : ¬valid sel P.pos P.coef z.1 = true := fun hv =>
      sender_not_mem_select sel P hv b hsel
    simp [setup_of_not_valid hv, leafS, NoteHiding.Twin.leaf]
  · simp only [OW.Choice.selected, hsel, ite_false]
    -- the one-wayness game samples `r`, `s`, `t` before the deposits; move them after
    rw [(bind_swap3_eqd _ _ _ _ _).prEvent_eq]
    refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun ox hox => ?_
    cases ox with
    | none => simp [leafS, NoteHiding.Twin.leaf]
    | some x =>
      obtain ⟨hv, hH, hc, hV⟩ := setup_spec hox
      obtain ⟨H', c', V', dep₀, dep₁, core⟩ := x
      simp only at hH hc hV
      subst hH hc hV
      simp only [bind_assoc, pure_bind]
      exact le_of_eq ((bodyS_eqd P A b _ z.2).symm.prEvent_eq _)

omit [Fintype F] in
/-- The fresh-key hybrid (the sender's ciphertext a dummy) followed by the trapdoor test
succeeds at most as often as `owAdversaryR` in the one-wayness game. -/
theorem prEvent_leafR_le_experiment (b : Bool) :
    Pr{let y ← hybrid (twin F P.g) sel P A b true .dummy .fresh >>= leafR P}[y = true] ≤
      Pr{let y ← OW.experiment P.g P.pos P.coef sel (owAdversaryR sel P A b)}[y = true] := by
  simp only [OW.experiment, owAdversaryR, hybrid, bind_assoc, pure_bind]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun H => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun z => ?_
  by_cases hsel : z.1.wAddr ∈ sel.select P.pos P.coef z.1.req
  · have hv : ¬valid sel P.pos P.coef z.1 = true := fun hv =>
      (SLINDDrop.valid_excl hv).2.2 hsel
    simp [setup_of_not_valid hv, leafR, NoteHiding.Twin.leaf]
  · simp only [OW.Choice.selected, hsel, ite_false]
    rw [(bind_swap3_eqd _ _ _ _ _).prEvent_eq]
    refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun ox hox => ?_
    cases ox with
    | none => simp [leafR, NoteHiding.Twin.leaf]
    | some x =>
      obtain ⟨hv, hH, hc, hV⟩ := setup_spec hox
      obtain ⟨H', c', V', dep₀, dep₁, core⟩ := x
      simp only at hH hc hV
      subst hH hc hV
      simp only [bind_assoc, pure_bind]
      exact le_of_eq ((bodyR_eqd P A b _ z.2).symm.prEvent_eq _)

/-! ## The error of the trapdoor test, and the bounds -/

/-- The pair of shared points of the sender's ciphertext is queried in the fresh-key hybrid with
probability at most the success probability of `owAdversaryS` in the one-wayness game plus
`(q₁ + q₂ + 1)/|F|`. -/
theorem queryProbS_le_experiment {q₁ q₂ : ℕ} (hq : A.QueryBound q₁ q₂) (b : Bool) :
    queryProbS (twin F P.g) sel P A b ≤
      𝒟[OW.experiment P.g P.pos P.coef sel (owAdversaryS sel P A b)] {true} +
        (q₁ + q₂ + 1 : ℕ) * (Fintype.card F : ℝ≥0∞)⁻¹ := by
  rw [← prEvent_eq_evalDist_singleton]
  refine (prEvent_le_prEvent_bind_add_of_support _ (leafS P b) _ (· = true)
    fun x hx hQ => ?_).trans (add_le_add (prEvent_leafS_le_experiment sel P A b) le_rfl)
  obtain ⟨v, o⟩ := x
  cases o with
  | none => exact absurd hQ (by simp [QueriedS])
  | some o =>
    refine NoteHiding.Twin.prEvent_leaf_le (g := P.g) (fun o' ho' => ?_) ⟨outS P b o, rfl, hQ⟩
    simp only [Option.map_some, Option.some.injEq] at ho'
    subst ho'
    exact length_cachedPoints_le_of_mem_support_hybrid (twin F P.g) sel P hq b
      (by simp) .real hx rfl

/-- The pair of shared points of the recipient's ciphertext is queried in the fresh-key hybrid
(the sender's ciphertext a dummy) with probability at most the success probability of
`owAdversaryR` in the one-wayness game plus `(q₁ + q₂ + 1)/|F|`. -/
theorem queryProbR_le_experiment {q₁ q₂ : ℕ} (hq : A.QueryBound q₁ q₂) (b : Bool) :
    queryProbR (twin F P.g) sel P A b ≤
      𝒟[OW.experiment P.g P.pos P.coef sel (owAdversaryR sel P A b)] {true} +
        (q₁ + q₂ + 1 : ℕ) * (Fintype.card F : ℝ≥0∞)⁻¹ := by
  rw [← prEvent_eq_evalDist_singleton]
  refine (prEvent_le_prEvent_bind_add_of_support _ (leafR P) _ (· = true)
    fun x hx hQ => ?_).trans (add_le_add (prEvent_leafR_le_experiment sel P A b) le_rfl)
  obtain ⟨v, o⟩ := x
  cases o with
  | none => exact absurd hQ (by simp [QueriedR])
  | some o =>
    refine NoteHiding.Twin.prEvent_leaf_le (g := P.g) (fun o' ho' => ?_) ⟨outR P o, rfl, hQ⟩
    simp only [Option.map_some, Option.some.injEq] at ho'
    subst ho'
    exact length_cachedPoints_le_of_mem_support_hybrid (twin F P.g) sel P hq b
      (by simp) .fresh hx rfl

/-- The sender's pair of shared points is queried in the fresh-key hybrid with probability at
most the CDH success probability of `cdhReductionS` plus `1/|F| + (q₁ + q₂ + 1)/|F|`. -/
theorem queryProbS_le (hg : Function.Bijective (· • P.g : F → G)) {q₁ q₂ : ℕ}
    (hq : A.QueryBound q₁ q₂) (b : Bool) :
    queryProbS (twin F P.g) sel P A b ≤
      𝒟[cdhExperiment P.g (cdhReductionS sel P A b)] {true} + (Fintype.card F : ℝ≥0∞)⁻¹ +
        (q₁ + q₂ + 1 : ℕ) * (Fintype.card F : ℝ≥0∞)⁻¹ :=
  (queryProbS_le_experiment sel P A hq b).trans
    (add_le_add (OW.success_le P.g P.pos P.coef sel hg (owAdversaryS sel P A b)) le_rfl)

/-- The recipient's pair of shared points is queried in the fresh-key hybrid with probability
at most the CDH success probability of `cdhReductionR` plus `1/|F| + (q₁ + q₂ + 1)/|F|`. -/
theorem queryProbR_le (hg : Function.Bijective (· • P.g : F → G)) {q₁ q₂ : ℕ}
    (hq : A.QueryBound q₁ q₂) (b : Bool) :
    queryProbR (twin F P.g) sel P A b ≤
      𝒟[cdhExperiment P.g (cdhReductionR sel P A b)] {true} + (Fintype.card F : ℝ≥0∞)⁻¹ +
        (q₁ + q₂ + 1 : ℕ) * (Fintype.card F : ℝ≥0∞)⁻¹ :=
  (queryProbR_le_experiment sel P A hq b).trans
    (add_le_add (OW.success_le P.g P.pos P.coef sel hg (owAdversaryR sel P A b)) le_rfl)

variable [Inhabited Addr] [Inhabited WCore] [Inhabited C]

/-- The cost of moving from the SL-IND game for bit `b` to the hybrid with a simulated proof and
two dummy ciphertexts, under CDH, for an adversary making at most `q₁ + q₂` KDF queries. -/
noncomputable def hopBound (q₁ q₂ : ℕ) (b : Bool) : ℝ≥0∞ :=
  zkAdvantage P.zk (zkReduction (twin F P.g) sel P A b) +
    (𝒟[cdhExperiment P.g (cdhReductionS sel P A b)] {true} + (Fintype.card F : ℝ≥0∞)⁻¹ +
      (q₁ + q₂ + 1 : ℕ) * (Fintype.card F : ℝ≥0∞)⁻¹) +
    otAdvantage P.senc (otReductionS (twin F P.g) sel P A b) +
    (𝒟[cdhExperiment P.g (cdhReductionR sel P A b)] {true} + (Fintype.card F : ℝ≥0∞)⁻¹ +
      (q₁ + q₂ + 1 : ℕ) * (Fintype.card F : ℝ≥0∞)⁻¹) +
    otAdvantage P.senc (otReductionR (twin F P.g) sel P A b)

/-- **Theorem 2 (SL-IND) with a random-oracle KDF, twin variant, under CDH** (option 3). For a
generator `g` and every selection rule, the SL-IND advantage of an adversary against the
two-ephemeral-value variant that makes at most `q₁` KDF queries before and `q₂` after the
challenge is at most the base-mixer unlinkability advantage of `mixerReduction` plus, for each
value of the hidden bit, the zero-knowledge advantage of `zkReduction`, and, for each of the two
ciphertexts, the CDH success probability of the reduction (`cdhReductionS`, `cdhReductionR`)
plus `1/|F|` plus `(q₁ + q₂ + 1)/|F|` (the trapdoor tests) and the one-time advantage of the
reduction (`otReductionS`, `otReductionR`). The reduction to plain CDH is tight. -/
theorem advantage_le (hg : Function.Bijective (· • P.g : F → G)) {q₁ q₂ : ℕ}
    (hq : A.QueryBound q₁ q₂) :
    advantage sel P A ≤
      hopBound sel P A q₁ q₂ false +
        mixerAdvantage P.mixer (mixerReduction (twin F P.g) sel P A) +
        hopBound sel P A q₁ q₂ true := by
  rw [advantage_eq]
  refine (advantage_le_queryProb (twin F P.g) sel P A).trans ?_
  simp only [SLINDRO.hopBound, hopBound]
  gcongr
  · exact queryProbS_le sel P A hg hq false
  · exact queryProbR_le sel P A hg hq false
  · exact queryProbS_le sel P A hg hq true
  · exact queryProbR_le sel P A hg hq true

end AuditPay.SLINDRO.Twin
