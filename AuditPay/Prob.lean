/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.OracleComp.EvalDist.Measure

/-!
# Probability helpers

Small `=ᵈ` (equality in distribution) lemmas for `ProbComp`, used by the game hops.
-/

open OracleComp

namespace AuditPay

variable {α β γ : Type}

/-- Re-indexing a uniform sample along a bijection does not change the distribution. -/
theorem uniform_bind_bij [SampleableType α] [SampleableType β] {e : α → β}
    (he : Function.Bijective e) (f : β → ProbComp γ) :
    (($ᵗ α : ProbComp α) >>= fun a => f (e a)) =ᵈ (($ᵗ β : ProbComp β) >>= f) := by
  have h : (($ᵗ α : ProbComp α) >>= fun a => f (e a)) = (e <$> ($ᵗ α : ProbComp α)) >>= f := by
    simp [map_eq_bind_pure_comp, bind_assoc]
  rw [h]
  exact (SampleableType.map_uniformSample_evalDistEq_of_bijective he).bind_left f

/-- A sample whose value is not used can be dropped. -/
theorem bind_const_eqd (mx : ProbComp α) (my : ProbComp β) : (mx >>= fun _ => my) =ᵈ my := by
  let : MeasurableSpace β := ⊤
  exact EvalDistEq.of_evalDist_eq (OracleComp.evalDist_bind_const mx my)

/-- Independent samples commute. -/
theorem bind_swap_eqd (mx : ProbComp α) (my : ProbComp β) (f : α → β → ProbComp γ) :
    (mx >>= fun a => my >>= fun b => f a b) =ᵈ (my >>= fun b => mx >>= fun a => f a b) :=
  OracleComp.EvalDistEq.bind_bind_swap mx my f

/-- Equal distributions give equal Boolean measures. -/
theorem evalDist_eq_of_eqd {mx my : ProbComp Bool} (h : mx =ᵈ my) : 𝒟[mx] = 𝒟[my] :=
  h.evalDist_eq

/-- Three independent samples taken before a fourth may be taken after it. -/
theorem bind_swap3_eqd {δ ε : Type} (ma : ProbComp α) (mb : ProbComp β) (mc : ProbComp γ)
    (mx : ProbComp δ) (k : α → β → γ → δ → ProbComp ε) :
    (do let a ← ma; let b ← mb; let c ← mc; let x ← mx; k a b c x) =ᵈ
      (do let x ← mx; let a ← ma; let b ← mb; let c ← mc; k a b c x) := by
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun a => EvalDistEq.bind_right _ fun b =>
    bind_swap_eqd _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun a => bind_swap_eqd _ _ _) ?_
  exact bind_swap_eqd _ _ _

/-- Two independent uniform samples are one uniform sample of the product. -/
theorem prod_merge_eqd [SampleableType α] [SampleableType β] (k : α → β → ProbComp γ) :
    (do let a ← $ᵗ α; let b ← $ᵗ β; k a b) =ᵈ (do let p ← $ᵗ (α × β); k p.1 p.2) := by
  rw [SampleableType.uniformSample_prod_eq_bind]
  simp only [bind_assoc, pure_bind]
  exact .rfl

/-- A sample taken after five others, and independent of them, may be taken first. -/
theorem bind_last_swap5_eqd {δ ε τ ζ : Type} (ma : ProbComp α) (mb : ProbComp β) (mc : ProbComp γ)
    (md : ProbComp δ) (me : α → β → γ → δ → ProbComp ε) (mt : ProbComp τ)
    (k : α → β → γ → δ → ε → τ → ProbComp ζ) :
    (do let a ← ma; let b ← mb; let c ← mc; let d ← md; let e ← me a b c d; let t ← mt
        k a b c d e t) =ᵈ
      (do let t ← mt; let a ← ma; let b ← mb; let c ← mc; let d ← md; let e ← me a b c d
          k a b c d e t) := by
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun a => EvalDistEq.bind_right _ fun b =>
    EvalDistEq.bind_right _ fun c => EvalDistEq.bind_right _ fun d => bind_swap_eqd _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun a => EvalDistEq.bind_right _ fun b =>
    EvalDistEq.bind_right _ fun c => bind_swap_eqd _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun a => EvalDistEq.bind_right _ fun b =>
    bind_swap_eqd _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun a => bind_swap_eqd _ _ _) ?_
  exact bind_swap_eqd _ _ _

/-- A sample taken after four others, and independent of them, may be taken first. -/
theorem bind_last_swap4_eqd {δ τ ε : Type} (ma : ProbComp α) (mb : ProbComp β) (mc : ProbComp γ)
    (md : α → β → γ → ProbComp δ) (mt : ProbComp τ) (k : α → β → γ → δ → τ → ProbComp ε) :
    (do let a ← ma; let b ← mb; let c ← mc; let d ← md a b c; let t ← mt; k a b c d t) =ᵈ
      (do let t ← mt; let a ← ma; let b ← mb; let c ← mc; let d ← md a b c; k a b c d t) := by
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun a => EvalDistEq.bind_right _ fun b =>
    EvalDistEq.bind_right _ fun c => bind_swap_eqd _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun a => EvalDistEq.bind_right _ fun b =>
    bind_swap_eqd _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun a => bind_swap_eqd _ _ _) ?_
  exact bind_swap_eqd _ _ _

/-- The pointwise affine map `u ↦ (x ↦ u x • g + c x)` is a bijection of function spaces when
`(· • g)` is a bijection. -/
theorem bijective_smul_add {F G Addr : Type} [Field F] [AddCommGroup G] [Module F G]
    {g : G} (hg : Function.Bijective (· • g : F → G)) (c : Addr → G) :
    Function.Bijective (fun u : Addr → F => fun x => u x • g + c x) := by
  let e : F ≃ G := Equiv.ofBijective _ hg
  let E : (Addr → F) ≃ (Addr → G) :=
    Equiv.piCongrRight fun x => e.trans (Equiv.addRight (c x))
  exact E.bijective

/-- A translate of a uniform group element by an independent point is uniform. -/
theorem bijective_add_right {G : Type} [AddCommGroup G] (c : G) :
    Function.Bijective (fun h : G => h + c) :=
  (Equiv.addRight c).bijective

/-- Two distinct coordinates of a uniformly random function collide with probability at most
`1/|F|`. -/
theorem prob_coord_eq_le {F Addr : Type} [AddCommGroup F] [Fintype F] [SampleableType F]
    [Fintype Addr] [DecidableEq Addr] {a a' : Addr} (h : a ≠ a') :
    Pr{let t ← $ᵗ (Addr → F)}[t a = t a'] ≤ (Fintype.card F : ENNReal)⁻¹ := by
  have h' : a' ≠ a := h.symm
  let R := {x : Addr // x ≠ a} → F
  let shear : F × R ≃ F × R :=
    { toFun := fun cr => (cr.1 - cr.2 ⟨a', h'⟩, cr.2)
      invFun := fun cr => (cr.1 + cr.2 ⟨a', h'⟩, cr.2)
      left_inv := fun cr => by simp
      right_inv := fun cr => by simp }
  let e : (Addr → F) ≃ F × R := (Equiv.piSplitAt a fun _ => F).trans shear
  have key : ∀ t : Addr → F, (t a = t a') ↔ (e t).1 = 0 := by
    intro t
    simp [e, shear, Equiv.piSplitAt, sub_eq_zero]
  rw [prEvent_congr _ _ _ key, SampleableType.prEvent_uniformSample_equiv e fun w => w.1 = 0]
  refine SampleableType.prEvent_uniformSample_prod_le_of_forall_snd _ fun _ => ?_
  exact (SampleableType.prEvent_uniformSample_eq_singleton (0 : F)).le

/-- Pointwise equal continuations give equal event computations after a common sample. -/
theorem prEvent_bind_congr' (mx : ProbComp α) (f g : α → ProbComp Prop)
    (h : ∀ a, prEvent (f a) = prEvent (g a)) : prEvent (mx >>= f) = prEvent (mx >>= g) := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_bind_of_discrete, prEvent_bind_of_discrete]
  exact MeasureTheory.lintegral_congr h

/-- Independent samples commute, for event computations. -/
theorem prEvent_bind_swap (mx : ProbComp α) (my : ProbComp β) (f : α → β → ProbComp Prop) :
    prEvent (mx >>= fun a => my >>= fun b => f a b) =
      prEvent (my >>= fun b => mx >>= fun a => f a b) := by
  rw [prEvent_def, prEvent_def, (bind_swap_eqd mx my f).evalDist_eq]

/-- An event computation whose continuation has the same probability after every value of a
sample has that probability. -/
theorem prEvent_bind_eq_of_forall (mx : ProbComp α) (f : α → ProbComp Prop) {ε : ENNReal}
    (h : ∀ a, prEvent (f a) = ε) : prEvent (mx >>= f) = ε := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_bind_of_discrete]
  simp only [h, MeasureTheory.lintegral_const, OracleComp.evalDist_apply_univ_eq_one, mul_one]

/-- A bound on an event of a uniform tuple that holds after resampling its `i`-th coordinate,
whatever the other coordinates are. -/
theorem prEvent_uniform_fun_le_of_update {N : ℕ} [SampleableType α] (i : Fin N)
    (p : (Fin N → α) → Prop) {ε : ENNReal}
    (h : ∀ r : Fin N → α, Pr{let x ← $ᵗ α}[p (Function.update r i x)] ≤ ε) :
    Pr{let r ← $ᵗ (Fin N → α)}[p r] ≤ ε := by
  let e := Equiv.funSplitAt i α
  refine (SampleableType.prEvent_uniformSample_equiv e.symm p).symm.trans_le ?_
  refine SampleableType.prEvent_uniformSample_prod_le_of_forall_snd _ fun rest => ?_
  obtain ⟨x₀⟩ : Nonempty α := inferInstance
  have key : ∀ x : α, e.symm (x, rest) = Function.update (e.symm (x₀, rest)) i x := by
    intro x
    funext j
    by_cases hj : j = i
    · subst hj
      simp [e, Equiv.funSplitAt, Equiv.piSplitAt]
    · simp [e, Equiv.funSplitAt, Equiv.piSplitAt, hj, Function.update_of_ne hj]
  exact le_trans (le_of_eq (prEvent_congr _ _ _ fun x => by rw [key x])) (h _)

/-- An event computation whose continuation is bounded after every value of a sample is
bounded. -/
theorem prEvent_bind_le_of_forall (mx : ProbComp α) (f : α → ProbComp Prop) {ε : ENNReal}
    (h : ∀ a, prEvent (f a) ≤ ε) : prEvent (mx >>= f) ≤ ε := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_bind_of_discrete]
  calc ∫⁻ a, prEvent (f a) ∂𝒟[mx] ≤ ∫⁻ _, ε ∂𝒟[mx] := MeasureTheory.lintegral_mono h
    _ = ε := by simp [MeasureTheory.lintegral_const, OracleComp.evalDist_apply_univ_eq_one]

/-- An event computation whose continuation is bounded after every reachable value of a sample
is bounded. -/
theorem prEvent_bind_le_of_forall_of_support (mx : ProbComp α) (f : α → ProbComp Prop)
    {ε : ENNReal} (h : ∀ a ∈ support mx, prEvent (f a) ≤ ε) : prEvent (mx >>= f) ≤ ε := by
  rw [bind_eq_attach_bind mx f]
  exact prEvent_bind_le_of_forall _ _ fun a => h a.1 a.2

/-- If every reachable outcome satisfying `p` makes the continuation satisfy `q` except with
probability `ε`, then `p` is at most as likely as `q` after the continuation, plus `ε`. -/
theorem prEvent_le_prEvent_bind_add_of_support (mx : ProbComp α) (f : α → ProbComp β)
    (p : α → Prop) (q : β → Prop) {ε : ENNReal}
    (h : ∀ a ∈ support mx, p a → Pr{let y ← f a}[¬q y] ≤ ε) :
    Pr{let a ← mx}[p a] ≤ Pr{let y ← mx >>= f}[q y] + ε := by
  have h1 := prEvent_bind_le_prEvent_add_of_support mx f (fun a => ¬p a) (fun y => ¬q y)
    fun a ha hp => h a ha (not_not.1 hp)
  have e1 := prEvent_add_prEvent_not_eq_prEvent_true mx p
  have e2 := prEvent_add_prEvent_not_eq_prEvent_true (mx >>= f) q
  rw [prEvent_true_eq_one] at e1 e2
  refine ENNReal.le_of_add_le_add_right (a := Pr{let a ← mx}[¬p a]) (prEvent_ne_top _) ?_
  calc Pr{let a ← mx}[p a] + Pr{let a ← mx}[¬p a] = 1 := e1
    _ = Pr{let y ← mx >>= f}[q y] + Pr{let y ← mx >>= f}[¬q y] := e2.symm
    _ ≤ Pr{let y ← mx >>= f}[q y] + (Pr{let a ← mx}[¬p a] + ε) := by gcongr
    _ = _ := by ring

end AuditPay
