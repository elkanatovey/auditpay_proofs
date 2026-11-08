/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.SLIND.Reductions
import VCVio.EvalDist.Monad.Disagreement.Measure
import AuditPay.IndKey
import AuditPay.RestrictedMonitoring

/-!
# Theorem 2, DDH hops: real Diffie–Hellman point → uniform group element

For an address `a` outside the monitored set, the encryption key `r • (RetrieveKey(V, a) - H(a))`
is pseudorandom: with `H(x) = u_x • g + t_x • Y` the point `RetrieveKey(V, a) - H(a)` is
`α • g + β • Y` where `β = ∑ᵢ λᵢ t_{rowsᵢ} - t_a` involves the fresh coordinate `t_a`, so
`β ≠ 0` except with probability `1/|F|`.
-/

open OracleComp DiffieHellman ENNReal

namespace AuditPay.SLIND

variable {F G Addr HK Key Note DTx WCore C Proof σ : Type} {k n : ℕ}
  [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G]
  [Fintype Addr] [DecidableEq Addr] [SampleableType HK] [SampleableType Key]
  [Inhabited Addr] [Inhabited WCore] [Inhabited C]

/-! ## Facts about `setup` and the reduction's algebra -/

omit [Fintype F] [SampleableType F] [SampleableType G] [Fintype Addr] [SampleableType HK]
  [SampleableType Key] [Inhabited Addr] [Inhabited WCore] [Inhabited C] in
/-- A context produced by `setup` comes from a valid choice and a successful vector generation. -/
theorem setup_spec {P : Params F G Addr HK Key Note DTx WCore C Proof k n}
    {A : Adversary F G Addr HK DTx WCore C Proof σ n} {b : Bool} {hk : HK} {H : Addr → G}
    {x : Ctx F G Addr HK Note DTx WCore σ n} (h : some x ∈ support (setup P A b hk H)) :
    valid x.c = true ∧ auditKeyVecGen P.g H P.pos P.coef x.c.1 x.c.2.1 = some x.V := by
  unfold setup at h
  obtain ⟨c, -, hc⟩ := support_bind_exists h
  by_cases hv : valid c = true
  · simp only [hv, ite_true] at hc
    cases hgen : auditKeyVecGen P.g H P.pos P.coef c.1 c.2.1 with
    | none => simp [hgen] at hc
    | some V =>
      simp only [hgen] at hc
      obtain ⟨n₀, -, hc⟩ := support_bind_exists hc
      obtain ⟨n₁, -, hc⟩ := support_bind_exists hc
      obtain ⟨core, -, hc⟩ := support_bind_exists hc
      simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at hc
      subst hc
      exact ⟨hv, hgen⟩
  · simp [hv] at hc

omit [Fintype F] [SampleableType F] [SampleableType G] [Fintype Addr] [DecidableEq Addr]
  [SampleableType HK] [SampleableType Key] [Inhabited Addr] [Inhabited WCore] [Inhabited C] in
/-- A key retrieved from a generated vector is a combination of the monitored audit keys, with
coefficients `keyCoeffs`. -/
theorem retrieveKey_eq_sum_keyCoeffs {P : Params F G Addr HK Key Note DTx WCore C Proof k n}
    {H : Addr → G} {rows : Fin n → Addr} {sk : Fin n → F} {V : Fin n → G}
    (hV : auditKeyVecGen P.g H P.pos P.coef rows sk = some V) (a : Addr) :
    retrieveKey P.pos P.coef V a =
      ∑ i, keyCoeffs P rows a i • auditKey P.g (sk i) (H (rows i)) := by
  unfold auditKeyVecGen solve at hV
  split_ifs at hV with hM
  cases hV
  simp only [retrieveKey_eq_sum_coefRow, keyCoeffs, Matrix.vecMul, dotProduct, matVecG,
    Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

omit [Fintype F] [SampleableType F] [SampleableType G] [Fintype Addr] [DecidableEq Addr]
  [SampleableType HK] [SampleableType Key] [Inhabited Addr] [Inhabited WCore] [Inhabited C] in
/-- On a real DDH tuple `(r • g, y • g, (r * y) • g)`, the reduction's point is the true
shared point of the selective encryption. -/
theorem ddhPoint_real {P : Params F G Addr HK Key Note DTx WCore C Proof k n}
    {c : Choice F Addr σ n} {u t : Addr → F} {y r : F} {V : Fin n → G}
    (hV : auditKeyVecGen P.g (fun z => u z • P.g + t z • (y • P.g)) P.pos P.coef c.1 c.2.1 =
      some V) (a : Addr) :
    ddhPoint P c u t a (r • P.g) ((r * y) • P.g) =
      encPoint r (retrieveKey P.pos P.coef V a) (u a • P.g + t a • (y • P.g)) := by
  rw [retrieveKey_eq_sum_keyCoeffs hV]
  set lam := keyCoeffs P c.1 a
  have hsum : ∑ i, lam i • auditKey P.g (c.2.1 i) (u (c.1 i) • P.g + t (c.1 i) • (y • P.g)) =
      ((∑ i, lam i * (c.2.1 i + u (c.1 i))) + (∑ i, lam i * t (c.1 i)) * y) • P.g := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib, Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [auditKey]
    module
  rw [hsum]
  simp only [ddhPoint, encPoint]
  module

/-! ## Sender's ciphertext: the real branch -/

/-- The reduction's run on a real DDH tuple `(r • g, ·, ·)`, after rewriting its key as the true
shared point: it depends on the programmed oracle only through `H`. -/
noncomputable def realBodyS (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) (r : F) (hk : HK)
    (H : Addr → G) : ProbComp Bool := do
  let ox ← setup P A b hk H
  match ox with
  | none => return false
  | some x => do
    let rR ← $ᵗ F
    let ctS := (P.senc (P.kdf hk (encPoint r (retrieveKey P.pos P.coef x.V (x.sender b))
      (H (x.sender b)))) (x.note b), r • P.g)
    let ctR ← slot P .real rR hk H x.V x.c.2.2.2.2.1 (x.note b)
    let π ← P.zk.sim (stmt x ctS ctR)
    finish A x ctS ctR π

omit [Fintype F] [Inhabited Addr] [Inhabited WCore] [Inhabited C] in
/-- The DDH reduction for the sender's ciphertext, run on a real tuple, is the hybrid with the
real ciphertext (and simulated proof). -/
theorem ddhRealS_eqd {P : Params F G Addr HK Key Note DTx WCore C Proof k n}
    (hg : Function.Bijective (· • P.g : F → G))
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) :
    ddhRealExperiment P.g (ddhReductionS P A b) =ᵈ hybrid P A b true .real .real := by
  -- 1. rewrite the reduction's key as the true shared point
  have h1 : ddhRealExperiment P.g (ddhReductionS P A b) =ᵈ (do
      let x ← $ᵗ F; let y ← $ᵗ F; let hk ← $ᵗ HK; let u ← $ᵗ (Addr → F)
      let t ← $ᵗ (Addr → F)
      realBodyS P A b x hk fun z => u z • P.g + t z • (y • P.g)) := by
    simp only [ddhRealExperiment, ddhReductionS, realBodyS]
    refine EvalDistEq.bind_right _ fun x => EvalDistEq.bind_right _ fun y =>
      EvalDistEq.bind_right _ fun hk => EvalDistEq.bind_right _ fun u =>
        EvalDistEq.bind_right _ fun t => ?_
    refine OracleComp.EvalDistEq.bind_congr_of_support _ fun ox hox => ?_
    cases ox with
    | none => exact .rfl
    | some c =>
      have hV := (setup_spec hox).2
      simp only [ddhPoint_real hV]
      exact .rfl
  refine h1.trans ?_
  -- 2. move `hk` to the front
  refine EvalDistEq.trans (my := do
      let hk ← $ᵗ HK; let x ← $ᵗ F; let y ← $ᵗ F; let u ← $ᵗ (Addr → F)
      let t ← $ᵗ (Addr → F)
      realBodyS P A b x hk fun z => u z • P.g + t z • (y • P.g)) ?_ ?_
  · refine (EvalDistEq.bind_right _ fun x => bind_swap_eqd _ _ _).trans ?_
    exact bind_swap_eqd _ _ _
  refine EvalDistEq.bind_right _ fun hk => ?_
  -- 3. the programmed oracle is a uniform `H`
  refine (IndKey.reprogram hg fun x H => realBodyS P A b x hk H).trans ?_
  refine EvalDistEq.bind_right _ fun H => ?_
  -- 4. sample the ephemeral scalar after `setup`, as `rS`
  simp only [realBodyS]
  refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun ox => ?_)
  cases ox with
  | none => exact bind_const_eqd _ _
  | some x =>
    simp only [slot, pure_bind, ite_true]
    exact .rfl

/-! ## Sender's ciphertext: the random branch -/

/-- The reduction's run after the challenge context, with sender key point `K`. -/
noncomputable def keyedBodyS (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) (X : G) (hk : HK)
    (H : Addr → G) (x : Ctx F G Addr HK Note DTx WCore σ n) (rR : F) (K : G) :
    ProbComp Bool := do
  let ctS := (P.senc (P.kdf hk K) (x.note b), X)
  let ctR ← slot P .real rR hk H x.V x.c.2.2.2.2.1 (x.note b)
  let π ← P.zk.sim (stmt x ctS ctR)
  finish A x ctS ctR π

/-- The reduction's state before the DDH value `Z` is used: `(x, y, hk, u, t, setup result)`. -/
abbrev DPre (F G Addr HK Note DTx WCore σ : Type) (n : ℕ) :=
  F × F × HK × (Addr → F) × (Addr → F) × Option (Ctx F G Addr HK Note DTx WCore σ n)

/-- The programmed oracle of a reduction state. -/
def DPre.oracle (g : G) (w : DPre F G Addr HK Note DTx WCore σ n) : Addr → G :=
  fun q => w.2.2.2.1 q • g + w.2.2.2.2.1 q • (w.2.1 • g)

/-- The reduction's run up to `setup`. -/
noncomputable def prefixS (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) :
    ProbComp (DPre F G Addr HK Note DTx WCore σ n) := do
  let x ← $ᵗ F
  let y ← $ᵗ F
  let hk ← $ᵗ HK
  let u ← $ᵗ (Addr → F)
  let t ← $ᵗ (Addr → F)
  let ox ← setup P A b hk fun q => u q • P.g + t q • (y • P.g)
  return (x, y, hk, u, t, ox)

/-- The rest of the reduction's run on a random tuple `Z = z • g`, with `z` sampled last. -/
noncomputable def contRealS (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool)
    (w : DPre F G Addr HK Note DTx WCore σ n) : ProbComp Bool :=
  match w.2.2.2.2.2 with
  | none => return false
  | some c => do
    let rR ← $ᵗ F
    let z ← $ᵗ F
    keyedBodyS P A b (w.1 • P.g) w.2.2.1 (w.oracle P.g) c rR
      (ddhPoint P c.c w.2.2.2.1 w.2.2.2.2.1 (c.sender b) (w.1 • P.g) (z • P.g))

/-- The ideal counterpart of `contRealS`: a uniform sender key point. -/
noncomputable def contIdealS (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool)
    (w : DPre F G Addr HK Note DTx WCore σ n) : ProbComp Bool :=
  match w.2.2.2.2.2 with
  | none => return false
  | some c => do
    let rR ← $ᵗ F
    let K ← $ᵗ G
    keyedBodyS P A b (w.1 • P.g) w.2.2.1 (w.oracle P.g) c rR K

/-- The coefficient of `Y` in the sender's point: `∑ᵢ λᵢ t_{rowsᵢ} - t_sender`. -/
noncomputable def betaS (P : Params F G Addr HK Key Note DTx WCore C Proof k n) (b : Bool)
    (c : Ctx F G Addr HK Note DTx WCore σ n) (t : Addr → F) : F :=
  ∑ i, keyCoeffs P c.c.1 (c.sender b) i * t (c.c.1 i) - t (c.sender b)

/-- The bad event of the random branch: the coefficient of `Y` vanishes. -/
def BadS (P : Params F G Addr HK Key Note DTx WCore C Proof k n) (b : Bool)
    (w : DPre F G Addr HK Note DTx WCore σ n) : Prop :=
  match w.2.2.2.2.2 with
  | none => False
  | some c => betaS P b c w.2.2.2.2.1 = 0

omit [Fintype F] [Inhabited Addr] [Inhabited WCore] [Inhabited C] in
/-- Moving the DDH value `z` to the end of the reduction's run. -/
theorem ddhRandomS_eqd (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) :
    ddhRandomExperiment P.g (ddhReductionS P A b) =ᵈ prefixS P A b >>= contRealS P A b := by
  simp only [ddhRandomExperiment, ddhReductionS, prefixS, contRealS, keyedBodyS,
    bind_assoc, pure_bind]
  refine EvalDistEq.bind_right _ fun x => EvalDistEq.bind_right _ fun y => ?_
  refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun hk => ?_)
  refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun u => ?_)
  refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun t => ?_)
  refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun ox => ?_)
  cases ox with
  | none => exact bind_const_eqd _ _
  | some c => exact bind_swap_eqd _ _ _

omit [Fintype F] [SampleableType HK] [Inhabited Addr] [Inhabited WCore] [Inhabited C]
  [DecidableEq F] [Fintype Addr] [DecidableEq Addr] in
/-- Outside the bad event the reduction's random branch and the ideal hybrid agree. -/
theorem contRealS_eqd {P : Params F G Addr HK Key Note DTx WCore C Proof k n}
    (hg : Function.Bijective (· • P.g : F → G))
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool)
    (w : DPre F G Addr HK Note DTx WCore σ n) (hw : ¬BadS P b w) :
    contRealS P A b w =ᵈ contIdealS P A b w := by
  obtain ⟨x, y, hk, u, t, ox⟩ := w
  cases ox with
  | none => exact .rfl
  | some c =>
    have hβ : betaS P b c t ≠ 0 := hw
    simp only [contRealS, contIdealS]
    refine EvalDistEq.bind_right _ fun rR => ?_
    set α := ∑ i, keyCoeffs P c.c.1 (c.sender b) i * (c.c.2.1 i + u (c.c.1 i)) - u (c.sender b)
    have he : (fun z : F => ddhPoint P c.c u t (c.sender b) (x • P.g) (z • P.g)) =
        fun z => α • (x • P.g) + (betaS P b c t * z) • P.g := by
      funext z
      simp only [ddhPoint, betaS, α, smul_smul]
    have hbij : Function.Bijective
        (fun z : F => ddhPoint P c.c u t (c.sender b) (x • P.g) (z • P.g)) := by
      rw [he]
      exact (Equiv.addLeft (α • (x • P.g))).bijective.comp
        (hg.comp (mulLeft_bijective₀ _ hβ))
    exact uniform_bind_bij (e := fun z : F => ddhPoint P c.c u t (c.sender b) (x • P.g) (z • P.g))
      hbij (fun K => keyedBodyS P A b (x • P.g) hk _ c rR K)

/-- The ideal run as a function of the ephemeral scalar, the KDF key and the oracle. -/
noncomputable def idealBodyS (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) (r : F) (hk : HK)
    (H : Addr → G) : ProbComp Bool := do
  let ox ← setup P A b hk H
  match ox with
  | none => return false
  | some c => do
    let rR ← $ᵗ F
    let K ← $ᵗ G
    keyedBodyS P A b (r • P.g) hk H c rR K

omit [Fintype F] [Inhabited Addr] [Inhabited WCore] [Inhabited C] in
/-- The ideal branch is the hybrid with a uniform sender key point. -/
theorem idealS_eqd {P : Params F G Addr HK Key Note DTx WCore C Proof k n}
    (hg : Function.Bijective (· • P.g : F → G))
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) :
    prefixS P A b >>= contIdealS P A b =ᵈ hybrid P A b true .randKey .real := by
  have h0 : prefixS P A b >>= contIdealS P A b = (do
      let x ← $ᵗ F; let y ← $ᵗ F; let hk ← $ᵗ HK; let u ← $ᵗ (Addr → F)
      let t ← $ᵗ (Addr → F)
      idealBodyS P A b x hk fun q => u q • P.g + t q • (y • P.g)) := by
    simp only [prefixS, contIdealS, idealBodyS, bind_assoc, pure_bind]
    rfl
  rw [h0]
  refine EvalDistEq.trans (my := do
      let hk ← $ᵗ HK; let x ← $ᵗ F; let y ← $ᵗ F; let u ← $ᵗ (Addr → F)
      let t ← $ᵗ (Addr → F)
      idealBodyS P A b x hk fun q => u q • P.g + t q • (y • P.g)) ?_ ?_
  · refine (EvalDistEq.bind_right _ fun x => bind_swap_eqd _ _ _).trans ?_
    exact bind_swap_eqd _ _ _
  refine EvalDistEq.bind_right _ fun hk => ?_
  refine (IndKey.reprogram hg fun x H => idealBodyS P A b x hk H).trans ?_
  refine EvalDistEq.bind_right _ fun H => ?_
  simp only [idealBodyS, keyedBodyS]
  refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun ox => ?_)
  cases ox with
  | none => exact bind_const_eqd _ _
  | some x =>
    simp only [slot, bind_assoc, pure_bind, ite_true]
    exact .rfl

omit [Fintype F] [SampleableType F] [SampleableType G] [Fintype Addr] [SampleableType HK]
  [SampleableType Key] [Inhabited Addr] [Inhabited WCore] [Inhabited C] [Field F] [DecidableEq F]
  [AddCommGroup G] [Module F G] in
/-- The sender of a valid choice is not a monitored address. -/
theorem sender_not_mem_range {x : Ctx F G Addr HK Note DTx WCore σ n} (hv : valid x.c = true)
    (b : Bool) : x.sender b ∉ Set.range x.c.1 := by
  rintro ⟨i, hi⟩
  have h := valid_excl hv i
  cases b <;> simp only [Ctx.sender, Bool.false_eq_true, ite_false, ite_true] at hi <;>
    [exact h.1 hi; exact h.2.1 hi]

omit [DecidableEq F] [Inhabited Addr] in
/-- For an address outside the monitored set, the coefficient of `Y` vanishes with probability
at most `1/|F|` over the programming `t`. -/
theorem prob_beta_le (rows : Fin n ↪ Addr) (lam : Fin n → F) {a : Addr} (ha : a ∉ Set.range rows) :
    Pr{let t ← $ᵗ (Addr → F)}[∑ i, lam i * t (rows i) - t a = 0] ≤
      (Fintype.card F : ℝ≥0∞)⁻¹ := by
  have key : ∀ t : Addr → F, (∑ i, lam i * t (rows i) - t a = 0) ↔
      ∑ i, (Fin.cons (-1) lam : Fin (n + 1) → F) i * t ((Fin.cons a rows : Fin (n + 1) → Addr) i)
        = 0 := by
    intro t
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    constructor <;> intro h <;> linear_combination h
  rw [prEvent_congr _ _ _ key]
  refine RestrictedMonitoring.prob_linear_eq_zero_le ?_ ?_
  · intro h
    have := congrFun h 0
    simp at this
  · exact Fin.cons_injective_iff.2 ⟨ha, rows.injective⟩

omit [Inhabited Addr] [Inhabited WCore] [Inhabited C] [SampleableType Key] in
/-- The bad event has probability at most `1/|F|`: the oracle given to the adversary hides `t`. -/
theorem prob_badS_le {P : Params F G Addr HK Key Note DTx WCore C Proof k n}
    (hg : Function.Bijective (· • P.g : F → G))
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) :
    Pr{let w ← prefixS P A b}[BadS P b w] ≤ (Fintype.card F : ℝ≥0∞)⁻¹ := by
  let proj : DPre F G Addr HK Note DTx WCore σ n →
      (Addr → F) × Option (Ctx F G Addr HK Note DTx WCore σ n) := fun w =>
    (w.2.2.2.2.1, w.2.2.2.2.2)
  let Bad' : (Addr → F) × Option (Ctx F G Addr HK Note DTx WCore σ n) → Prop := fun v =>
    match v.2 with
    | none => False
    | some c => betaS P b c v.1 = 0
  have hproj : Pr{let w ← prefixS P A b}[BadS P b w] =
      Pr{let v ← proj <$> prefixS P A b}[Bad' v] := by
    rw [prEvent_map]
    rfl
  have hdist : proj <$> prefixS P A b =ᵈ (do
      let hk ← $ᵗ HK; let H ← $ᵗ (Addr → G); let ox ← setup P A b hk H
      let t ← $ᵗ (Addr → F)
      return (t, ox)) := by
    have h0 : proj <$> prefixS P A b = (do
        let _x ← $ᵗ F; let y ← $ᵗ F; let hk ← $ᵗ HK; let u ← $ᵗ (Addr → F)
        let t ← $ᵗ (Addr → F)
        (do let ox ← setup P A b hk fun q => u q • P.g + t q • (y • P.g); return (t, ox))) := by
      simp [prefixS, proj, map_bind]
    rw [h0]
    refine EvalDistEq.trans (my := do
        let hk ← $ᵗ HK; let _x ← $ᵗ F; let y ← $ᵗ F; let u ← $ᵗ (Addr → F)
        let t ← $ᵗ (Addr → F)
        (do let ox ← setup P A b hk fun q => u q • P.g + t q • (y • P.g); return (t, ox))) ?_ ?_
    · refine (EvalDistEq.bind_right _ fun x => bind_swap_eqd _ _ _).trans ?_
      exact bind_swap_eqd _ _ _
    refine EvalDistEq.bind_right _ fun hk => ?_
    refine EvalDistEq.trans (my := do
        let _x ← $ᵗ F; let _y ← $ᵗ F; let t ← $ᵗ (Addr → F); let H ← $ᵗ (Addr → G)
        (do let ox ← setup P A b hk H; return (t, ox))) ?_ ?_
    · refine EvalDistEq.bind_right _ fun x => EvalDistEq.bind_right _ fun y => ?_
      exact IndKey.reprogram_core hg (y • P.g) fun t H => do
        let ox ← setup P A b hk H
        return (t, ox)
    refine ((bind_const_eqd _ _).trans (bind_const_eqd _ _)).trans ?_
    refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun H => ?_)
    exact bind_swap_eqd _ _ _
  rw [hproj, hdist.prEvent_eq Bad']
  refine prEvent_bind_le_of_forall_le _ _ _ fun hk => ?_
  refine prEvent_bind_le_of_forall_le _ _ _ fun H => ?_
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun ox hox => ?_
  cases ox with
  | none => simp [Bad']
  | some c =>
    have hv := (setup_spec hox).1
    simp only [Bad', betaS, bind_pure_comp, prEvent_map]
    exact prob_beta_le c.c.1 _ (sender_not_mem_range hv b)

omit [Inhabited Addr] [Inhabited WCore] [Inhabited C] in
/-- Sender's ciphertext: replacing its DH point by a uniform group element costs the DDH
advantage of `ddhReductionS` plus `1/|F|`. -/
theorem hop_ddhS {P : Params F G Addr HK Key Note DTx WCore C Proof k n}
    (hg : Function.Bijective (· • P.g : F → G))
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) :
    𝒟[hybrid P A b true .real .real].boolDist 𝒟[hybrid P A b true .randKey .real] ≤
      ddhAdvantage P.g (ddhReductionS P A b) + (Fintype.card F : ℝ≥0∞)⁻¹ := by
  have hreal := (ddhRealS_eqd hg A b).evalDist_eq
  have hrand := (ddhRandomS_eqd P A b).evalDist_eq
  have hideal := (idealS_eqd hg A b).evalDist_eq
  have h1 := prEvent_bind_le_add_of_disagree (mx := prefixS P A b) (my := contRealS P A b)
    (oc := contIdealS P A b) (q := fun y => y = true) (ε₂ := 0) (prob_badS_le hg A b)
    (fun w _ hw => by rw [add_zero]; exact ((contRealS_eqd hg A b w hw).prEvent_eq _).le)
  have h2 := prEvent_bind_le_add_of_disagree (mx := prefixS P A b) (my := contIdealS P A b)
    (oc := contRealS P A b) (q := fun y => y = true) (ε₂ := 0) (prob_badS_le hg A b)
    (fun w _ hw => by rw [add_zero]; exact ((contRealS_eqd hg A b w hw).symm.prEvent_eq _).le)
  have hdist : 𝒟[ddhRandomExperiment P.g (ddhReductionS P A b)].boolDist
      𝒟[hybrid P A b true .randKey .real] ≤ (Fintype.card F : ℝ≥0∞)⁻¹ := by
    rw [hrand, ← hideal, MeasureTheory.Measure.boolDist,
      ← prEvent_eq_evalDist_singleton, ← prEvent_eq_evalDist_singleton]
    simp only [add_zero] at h1 h2
    exact ENNReal.absDiff_le_iff.2 ⟨h1, h2⟩
  rw [← hreal]
  calc _ ≤ ddhAdvantage P.g (ddhReductionS P A b) +
        𝒟[ddhRandomExperiment P.g (ddhReductionS P A b)].boolDist
          𝒟[hybrid P A b true .randKey .real] :=
        MeasureTheory.Measure.boolDist_triangle _ _ _
    _ ≤ _ := by gcongr

/-! ## Recipient's ciphertext -/

/-- The reduction for the recipient's ciphertext, run on a real DDH tuple `(r • g, ·, ·)`, after
rewriting its key as the true shared point. -/
noncomputable def realBodyR (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) (r : F) (hk : HK)
    (H : Addr → G) : ProbComp Bool := do
  let ox ← setup P A b hk H
  match ox with
  | none => return false
  | some x => do
    let rS ← $ᵗ F
    let ctS ← slot P .dummy rS hk H x.V (x.sender b) (x.note b)
    let ctR := (P.senc (P.kdf hk (encPoint r (retrieveKey P.pos P.coef x.V x.c.2.2.2.2.1)
      (H x.c.2.2.2.2.1))) (x.note b), r • P.g)
    let π ← P.zk.sim (stmt x ctS ctR)
    finish A x ctS ctR π

omit [Fintype F] [Inhabited Addr] [Inhabited WCore] [Inhabited C] in
/-- The DDH reduction for the recipient's ciphertext, run on a real tuple, is the hybrid with
the real recipient ciphertext. -/
theorem ddhRealR_eqd {P : Params F G Addr HK Key Note DTx WCore C Proof k n}
    (hg : Function.Bijective (· • P.g : F → G))
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) :
    ddhRealExperiment P.g (ddhReductionR P A b) =ᵈ hybrid P A b true .dummy .real := by
  have h1 : ddhRealExperiment P.g (ddhReductionR P A b) =ᵈ (do
      let x ← $ᵗ F; let y ← $ᵗ F; let hk ← $ᵗ HK; let u ← $ᵗ (Addr → F)
      let t ← $ᵗ (Addr → F)
      realBodyR P A b x hk fun z => u z • P.g + t z • (y • P.g)) := by
    simp only [ddhRealExperiment, ddhReductionR, realBodyR]
    refine EvalDistEq.bind_right _ fun x => EvalDistEq.bind_right _ fun y =>
      EvalDistEq.bind_right _ fun hk => EvalDistEq.bind_right _ fun u =>
        EvalDistEq.bind_right _ fun t => ?_
    refine OracleComp.EvalDistEq.bind_congr_of_support _ fun ox hox => ?_
    cases ox with
    | none => exact .rfl
    | some c =>
      have hV := (setup_spec hox).2
      simp only [ddhPoint_real hV]
      exact .rfl
  refine h1.trans ?_
  refine EvalDistEq.trans (my := do
      let hk ← $ᵗ HK; let x ← $ᵗ F; let y ← $ᵗ F; let u ← $ᵗ (Addr → F)
      let t ← $ᵗ (Addr → F)
      realBodyR P A b x hk fun z => u z • P.g + t z • (y • P.g)) ?_ ?_
  · refine (EvalDistEq.bind_right _ fun x => bind_swap_eqd _ _ _).trans ?_
    exact bind_swap_eqd _ _ _
  refine EvalDistEq.bind_right _ fun hk => ?_
  refine (IndKey.reprogram hg fun x H => realBodyR P A b x hk H).trans ?_
  refine EvalDistEq.bind_right _ fun H => ?_
  simp only [realBodyR]
  refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun ox => ?_)
  cases ox with
  | none => exact bind_const_eqd _ _
  | some x =>
    refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun rS => ?_)
    simp only [slot, bind_assoc, pure_bind, ite_true]
    exact .rfl

/-- The recipient-hop reduction's run after the sender's dummy ciphertext, with recipient key
point `K`. -/
noncomputable def keyedBodyR (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) (X : G) (hk : HK)
    (x : Ctx F G Addr HK Note DTx WCore σ n) (ctS : C × G) (K : G) : ProbComp Bool := do
  let ctR := (P.senc (P.kdf hk K) (x.note b), X)
  let π ← P.zk.sim (stmt x ctS ctR)
  finish A x ctS ctR π

/-- The rest of the recipient-hop reduction's run on a random tuple, with `z` sampled last. -/
noncomputable def contRealR (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool)
    (w : DPre F G Addr HK Note DTx WCore σ n) : ProbComp Bool :=
  match w.2.2.2.2.2 with
  | none => return false
  | some c => do
    let rS ← $ᵗ F
    let ctS ← slot P .dummy rS w.2.2.1 (w.oracle P.g) c.V (c.sender b) (c.note b)
    let z ← $ᵗ F
    keyedBodyR P A b (w.1 • P.g) w.2.2.1 c ctS
      (ddhPoint P c.c w.2.2.2.1 w.2.2.2.2.1 c.c.2.2.2.2.1 (w.1 • P.g) (z • P.g))

/-- The ideal counterpart of `contRealR`: a uniform recipient key point. -/
noncomputable def contIdealR (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool)
    (w : DPre F G Addr HK Note DTx WCore σ n) : ProbComp Bool :=
  match w.2.2.2.2.2 with
  | none => return false
  | some c => do
    let rS ← $ᵗ F
    let ctS ← slot P .dummy rS w.2.2.1 (w.oracle P.g) c.V (c.sender b) (c.note b)
    let K ← $ᵗ G
    keyedBodyR P A b (w.1 • P.g) w.2.2.1 c ctS K

/-- The coefficient of `Y` in the recipient's point: `∑ᵢ λᵢ t_{rowsᵢ} - t_w`. -/
noncomputable def betaR (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (c : Ctx F G Addr HK Note DTx WCore σ n) (t : Addr → F) : F :=
  ∑ i, keyCoeffs P c.c.1 c.c.2.2.2.2.1 i * t (c.c.1 i) - t c.c.2.2.2.2.1

/-- The bad event of the recipient hop's random branch. -/
def BadR (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (w : DPre F G Addr HK Note DTx WCore σ n) : Prop :=
  match w.2.2.2.2.2 with
  | none => False
  | some c => betaR P c w.2.2.2.2.1 = 0

omit [Fintype F] [Inhabited Addr] [Inhabited WCore] [Inhabited C] in
/-- Moving the DDH value `z` to the end of the recipient-hop reduction's run. -/
theorem ddhRandomR_eqd (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) :
    ddhRandomExperiment P.g (ddhReductionR P A b) =ᵈ prefixS P A b >>= contRealR P A b := by
  simp only [ddhRandomExperiment, ddhReductionR, prefixS, contRealR, keyedBodyR,
    bind_assoc, pure_bind]
  refine EvalDistEq.bind_right _ fun x => EvalDistEq.bind_right _ fun y => ?_
  refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun hk => ?_)
  refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun u => ?_)
  refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun t => ?_)
  refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun ox => ?_)
  cases ox with
  | none => exact bind_const_eqd _ _
  | some c =>
    refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun rS => ?_)
    exact bind_swap_eqd _ _ _

omit [Fintype F] [SampleableType HK] [Inhabited Addr] [Inhabited WCore] [Inhabited C]
  [DecidableEq F] [Fintype Addr] [DecidableEq Addr] in
/-- Outside the bad event the recipient hop's random branch and the ideal hybrid agree. -/
theorem contRealR_eqd {P : Params F G Addr HK Key Note DTx WCore C Proof k n}
    (hg : Function.Bijective (· • P.g : F → G))
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool)
    (w : DPre F G Addr HK Note DTx WCore σ n) (hw : ¬BadR P w) :
    contRealR P A b w =ᵈ contIdealR P A b w := by
  obtain ⟨x, y, hk, u, t, ox⟩ := w
  cases ox with
  | none => exact .rfl
  | some c =>
    have hβ : betaR P c t ≠ 0 := hw
    simp only [contRealR, contIdealR]
    refine EvalDistEq.bind_right _ fun rS => EvalDistEq.bind_right _ fun ctS => ?_
    set α := ∑ i, keyCoeffs P c.c.1 c.c.2.2.2.2.1 i * (c.c.2.1 i + u (c.c.1 i)) -
      u c.c.2.2.2.2.1
    have he : (fun z : F => ddhPoint P c.c u t c.c.2.2.2.2.1 (x • P.g) (z • P.g)) =
        fun z => α • (x • P.g) + (betaR P c t * z) • P.g := by
      funext z
      simp only [ddhPoint, betaR, α, smul_smul]
    have hbij : Function.Bijective
        (fun z : F => ddhPoint P c.c u t c.c.2.2.2.2.1 (x • P.g) (z • P.g)) := by
      rw [he]
      exact (Equiv.addLeft (α • (x • P.g))).bijective.comp
        (hg.comp (mulLeft_bijective₀ _ hβ))
    exact uniform_bind_bij
      (e := fun z : F => ddhPoint P c.c u t c.c.2.2.2.2.1 (x • P.g) (z • P.g))
      hbij (fun K => keyedBodyR P A b (x • P.g) hk c ctS K)

/-- The ideal recipient-hop run as a function of the ephemeral scalar, the KDF key and the
oracle. -/
noncomputable def idealBodyR (P : Params F G Addr HK Key Note DTx WCore C Proof k n)
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) (r : F) (hk : HK)
    (H : Addr → G) : ProbComp Bool := do
  let ox ← setup P A b hk H
  match ox with
  | none => return false
  | some c => do
    let rS ← $ᵗ F
    let ctS ← slot P .dummy rS hk H c.V (c.sender b) (c.note b)
    let K ← $ᵗ G
    keyedBodyR P A b (r • P.g) hk c ctS K

omit [Fintype F] [Inhabited Addr] [Inhabited WCore] [Inhabited C] in
/-- The ideal branch is the hybrid with a uniform recipient key point. -/
theorem idealR_eqd {P : Params F G Addr HK Key Note DTx WCore C Proof k n}
    (hg : Function.Bijective (· • P.g : F → G))
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) :
    prefixS P A b >>= contIdealR P A b =ᵈ hybrid P A b true .dummy .randKey := by
  have h0 : prefixS P A b >>= contIdealR P A b = (do
      let x ← $ᵗ F; let y ← $ᵗ F; let hk ← $ᵗ HK; let u ← $ᵗ (Addr → F)
      let t ← $ᵗ (Addr → F)
      idealBodyR P A b x hk fun q => u q • P.g + t q • (y • P.g)) := by
    simp only [prefixS, contIdealR, idealBodyR, bind_assoc, pure_bind]
    rfl
  rw [h0]
  refine EvalDistEq.trans (my := do
      let hk ← $ᵗ HK; let x ← $ᵗ F; let y ← $ᵗ F; let u ← $ᵗ (Addr → F)
      let t ← $ᵗ (Addr → F)
      idealBodyR P A b x hk fun q => u q • P.g + t q • (y • P.g)) ?_ ?_
  · refine (EvalDistEq.bind_right _ fun x => bind_swap_eqd _ _ _).trans ?_
    exact bind_swap_eqd _ _ _
  refine EvalDistEq.bind_right _ fun hk => ?_
  refine (IndKey.reprogram hg fun x H => idealBodyR P A b x hk H).trans ?_
  refine EvalDistEq.bind_right _ fun H => ?_
  simp only [idealBodyR, keyedBodyR]
  refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun ox => ?_)
  cases ox with
  | none => exact bind_const_eqd _ _
  | some x =>
    refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun rS => ?_)
    simp only [slot, bind_assoc, pure_bind, ite_true]
    exact .rfl

omit [Fintype F] [SampleableType F] [SampleableType G] [Fintype Addr] [SampleableType HK]
  [SampleableType Key] [Inhabited Addr] [Inhabited WCore] [Inhabited C] [Field F] [DecidableEq F]
  [AddCommGroup G] [Module F G] in
/-- The recipient of a valid choice is not a monitored address. -/
theorem recipient_not_mem_range {x : Ctx F G Addr HK Note DTx WCore σ n}
    (hv : valid x.c = true) : x.c.2.2.2.2.1 ∉ Set.range x.c.1 := by
  rintro ⟨i, hi⟩
  exact (valid_excl hv i).2.2 hi

omit [Inhabited Addr] [Inhabited WCore] [Inhabited C] [SampleableType Key] in
/-- The recipient hop's bad event has probability at most `1/|F|`. -/
theorem prob_badR_le {P : Params F G Addr HK Key Note DTx WCore C Proof k n}
    (hg : Function.Bijective (· • P.g : F → G))
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) :
    Pr{let w ← prefixS P A b}[BadR P w] ≤ (Fintype.card F : ℝ≥0∞)⁻¹ := by
  let proj : DPre F G Addr HK Note DTx WCore σ n →
      (Addr → F) × Option (Ctx F G Addr HK Note DTx WCore σ n) := fun w =>
    (w.2.2.2.2.1, w.2.2.2.2.2)
  let Bad' : (Addr → F) × Option (Ctx F G Addr HK Note DTx WCore σ n) → Prop := fun v =>
    match v.2 with
    | none => False
    | some c => betaR P c v.1 = 0
  have hproj : Pr{let w ← prefixS P A b}[BadR P w] =
      Pr{let v ← proj <$> prefixS P A b}[Bad' v] := by
    rw [prEvent_map]
    rfl
  have hdist : proj <$> prefixS P A b =ᵈ (do
      let hk ← $ᵗ HK; let H ← $ᵗ (Addr → G); let ox ← setup P A b hk H
      let t ← $ᵗ (Addr → F)
      return (t, ox)) := by
    have h0 : proj <$> prefixS P A b = (do
        let _x ← $ᵗ F; let y ← $ᵗ F; let hk ← $ᵗ HK; let u ← $ᵗ (Addr → F)
        let t ← $ᵗ (Addr → F)
        (do let ox ← setup P A b hk fun q => u q • P.g + t q • (y • P.g); return (t, ox))) := by
      simp [prefixS, proj, map_bind]
    rw [h0]
    refine EvalDistEq.trans (my := do
        let hk ← $ᵗ HK; let _x ← $ᵗ F; let y ← $ᵗ F; let u ← $ᵗ (Addr → F)
        let t ← $ᵗ (Addr → F)
        (do let ox ← setup P A b hk fun q => u q • P.g + t q • (y • P.g); return (t, ox))) ?_ ?_
    · refine (EvalDistEq.bind_right _ fun x => bind_swap_eqd _ _ _).trans ?_
      exact bind_swap_eqd _ _ _
    refine EvalDistEq.bind_right _ fun hk => ?_
    refine EvalDistEq.trans (my := do
        let _x ← $ᵗ F; let _y ← $ᵗ F; let t ← $ᵗ (Addr → F); let H ← $ᵗ (Addr → G)
        (do let ox ← setup P A b hk H; return (t, ox))) ?_ ?_
    · refine EvalDistEq.bind_right _ fun x => EvalDistEq.bind_right _ fun y => ?_
      exact IndKey.reprogram_core hg (y • P.g) fun t H => do
        let ox ← setup P A b hk H
        return (t, ox)
    refine ((bind_const_eqd _ _).trans (bind_const_eqd _ _)).trans ?_
    refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun H => ?_)
    exact bind_swap_eqd _ _ _
  rw [hproj, hdist.prEvent_eq Bad']
  refine prEvent_bind_le_of_forall_le _ _ _ fun hk => ?_
  refine prEvent_bind_le_of_forall_le _ _ _ fun H => ?_
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun ox hox => ?_
  cases ox with
  | none => simp [Bad']
  | some c =>
    have hv := (setup_spec hox).1
    simp only [Bad', betaR, bind_pure_comp, prEvent_map]
    exact prob_beta_le c.c.1 _ (recipient_not_mem_range hv)

omit [Inhabited Addr] [Inhabited WCore] [Inhabited C] in
/-- Recipient's ciphertext, with the sender's already a dummy. -/
theorem hop_ddhR {P : Params F G Addr HK Key Note DTx WCore C Proof k n}
    (hg : Function.Bijective (· • P.g : F → G))
    (A : Adversary F G Addr HK DTx WCore C Proof σ n) (b : Bool) :
    𝒟[hybrid P A b true .dummy .real].boolDist 𝒟[hybrid P A b true .dummy .randKey] ≤
      ddhAdvantage P.g (ddhReductionR P A b) + (Fintype.card F : ℝ≥0∞)⁻¹ := by
  have hreal := (ddhRealR_eqd hg A b).evalDist_eq
  have hrand := (ddhRandomR_eqd P A b).evalDist_eq
  have hideal := (idealR_eqd hg A b).evalDist_eq
  have h1 := prEvent_bind_le_add_of_disagree (mx := prefixS P A b) (my := contRealR P A b)
    (oc := contIdealR P A b) (q := fun y => y = true) (ε₂ := 0) (prob_badR_le hg A b)
    (fun w _ hw => by rw [add_zero]; exact ((contRealR_eqd hg A b w hw).prEvent_eq _).le)
  have h2 := prEvent_bind_le_add_of_disagree (mx := prefixS P A b) (my := contIdealR P A b)
    (oc := contRealR P A b) (q := fun y => y = true) (ε₂ := 0) (prob_badR_le hg A b)
    (fun w _ hw => by rw [add_zero]; exact ((contRealR_eqd hg A b w hw).symm.prEvent_eq _).le)
  have hdist : 𝒟[ddhRandomExperiment P.g (ddhReductionR P A b)].boolDist
      𝒟[hybrid P A b true .dummy .randKey] ≤ (Fintype.card F : ℝ≥0∞)⁻¹ := by
    rw [hrand, ← hideal, MeasureTheory.Measure.boolDist,
      ← prEvent_eq_evalDist_singleton, ← prEvent_eq_evalDist_singleton]
    simp only [add_zero] at h1 h2
    exact ENNReal.absDiff_le_iff.2 ⟨h1, h2⟩
  rw [← hreal]
  calc _ ≤ ddhAdvantage P.g (ddhReductionR P A b) +
        𝒟[ddhRandomExperiment P.g (ddhReductionR P A b)].boolDist
          𝒟[hybrid P A b true .dummy .randKey] :=
        MeasureTheory.Measure.boolDist_triangle _ _ _
    _ ≤ _ := by gcongr

end AuditPay.SLIND
