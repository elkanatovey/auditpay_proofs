/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.RestrictedMonitoring.Decrypt.Split
import AuditPay.RestrictedMonitoring.Decrypt.HopDDH
import AuditPay.RestrictedMonitoring.Decrypt.HopES
import AuditPay.RestrictedMonitoring.Decrypt.HopOT

/-!
# Theorem 3 (Restricted Monitoring): the paper's decryption game, for algebraic adversaries

An algebraic adversary that outputs a vector `V` of size `n` and `n + 1` distinct addresses
cannot decrypt selective encryptions of uniform messages to all of them. Its success probability
is at most the advantages of named reductions against DDH (plus `1/|F|`), entropy smoothing of
the KDF and one-time security of the cipher, plus the guessing probability `1/|Msg|`. See
`AuditPay.RestrictedMonitoring.Decrypt.Defs` for the game and the modelling choices.

The proof singles out one target ciphertext (`Commit.target`), replaces its Diffie–Hellman point
by a uniform group element (`hop_ddh`), its symmetric key by a uniform key (`hop_es`) and its
plaintext by a dummy (`hop_ot`). In the last hybrid the adversary's view is independent of the
target's message (`prob_dummy_le`).
-/

open OracleComp DiffieHellman ENNReal MeasureTheory

namespace AuditPay.RestrictedMonitoring.Decrypt

open SLIND (Mode otAdvantage)

variable {F G Addr HK Key Msg C σ : Type} {k n : ℕ}
  [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G]
  [Fintype Addr] [DecidableEq Addr] [SampleableType HK] [SampleableType Key]
  [Fintype Msg] [DecidableEq Msg] [SampleableType Msg]

omit [Fintype F] in
/-- In the last hybrid the target's ciphertext encrypts a dummy, so the adversary's view is
independent of the target's message: it wins with probability at most `1/|Msg|`. -/
theorem prob_dummy_le (P : Params F G Addr HK Key Msg C k n)
    (A : Adversary F G Addr HK Msg C σ n) :
    𝒟[hybrid P A .dummy] {true} ≤ (Fintype.card Msg : ℝ≥0∞)⁻¹ := by
  -- sample the target's message after the adversary's response
  have h : hybrid P A .dummy =ᵈ (do
      let hk ← $ᵗ HK; let H ← $ᵗ (Addr → G); let c ← A.commit hk H
      let m ← $ᵗ (Fin (n + 1) → Msg); let r ← $ᵗ (Fin (n + 1) → F)
      let ρ ← $ᵗ F; let key ← $ᵗ Key
      let m' ← A.respond c.state (Function.update (challenge P hk H c m r) (c.target P)
        (P.senc key P.dummy, ρ • P.g))
      let μ ← $ᵗ Msg
      return decide (∀ i, m' i = Function.update m (c.target P) μ i)) := by
    simp only [hybrid, slot, finish, bind_assoc, pure_bind]
    refine EvalDistEq.bind_right _ fun hk => EvalDistEq.bind_right _ fun H =>
      EvalDistEq.bind_right _ fun c => EvalDistEq.bind_right _ fun m =>
        EvalDistEq.bind_right _ fun r => ?_
    refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun ρ => ?_)
    refine (bind_swap_eqd _ _ _).trans (EvalDistEq.bind_right _ fun key => ?_)
    exact bind_swap_eqd _ _ _
  rw [← prEvent_eq_evalDist_singleton, h.prEvent_eq]
  refine prEvent_bind_le_of_forall_le _ _ _ fun hk => ?_
  refine prEvent_bind_le_of_forall_le _ _ _ fun H => ?_
  refine prEvent_bind_le_of_forall_le _ _ _ fun c => ?_
  refine prEvent_bind_le_of_forall_le _ _ _ fun m => ?_
  refine prEvent_bind_le_of_forall_le _ _ _ fun r => ?_
  refine prEvent_bind_le_of_forall_le _ _ _ fun ρ => ?_
  refine prEvent_bind_le_of_forall_le _ _ _ fun key => ?_
  refine prEvent_bind_le_of_forall_le _ _ _ fun m' => ?_
  simp only [bind_pure_comp, prEvent_map, decide_eq_true_eq]
  refine (prEvent_mono _ _ (fun μ => m' (c.target P) = μ) fun μ hμ => ?_).trans
    (SampleableType.prEvent_uniformSample_eq_singleton' _).le
  simpa using hμ (c.target P)

/-- **Theorem 3, decryption game** (Restricted Monitoring, Definition 3, for algebraic
adversaries): an adversary that outputs a representation of a vector `V` of size `n` and `n + 1`
distinct addresses wins the decryption game — returns the plaintexts of selective encryptions
of uniform messages to all `n + 1` addresses — with probability at most the DDH advantage of
`ddhReduction` plus `1/|F|`, the entropy-smoothing advantage of `esReduction`, the one-time
advantage of `otReduction`, and `1/|Msg|`. -/
theorem success_le {P : Params F G Addr HK Key Msg C k n}
    (hg : Function.Bijective (· • P.g : F → G)) (A : Adversary F G Addr HK Msg C σ n) :
    𝒟[experiment P A] {true} ≤
      ddhAdvantage P.g (ddhReduction P A) + (Fintype.card F : ℝ≥0∞)⁻¹ +
        EntropySmoothing.advantage F P.g P.kdf (esReduction P A) +
        otAdvantage P.senc (otReduction P A) +
        (Fintype.card Msg : ℝ≥0∞)⁻¹ := by
  have t := Measure.boolDist_triangle
  rw [(experiment_eqd P A).evalDist_eq]
  calc 𝒟[hybrid P A .real] {true}
      ≤ 𝒟[hybrid P A .dummy] {true} + 𝒟[hybrid P A .real].boolDist 𝒟[hybrid P A .dummy] :=
        Measure.apply_true_le_add_boolDist _ _
    _ ≤ (Fintype.card Msg : ℝ≥0∞)⁻¹ +
          (𝒟[hybrid P A .real].boolDist 𝒟[hybrid P A .randKey] +
          (𝒟[hybrid P A .randKey].boolDist 𝒟[hybrid P A .randSym] +
          𝒟[hybrid P A .randSym].boolDist 𝒟[hybrid P A .dummy])) :=
        add_le_add (prob_dummy_le P A) ((t _ _ _).trans (add_le_add le_rfl (t _ _ _)))
    _ ≤ (Fintype.card Msg : ℝ≥0∞)⁻¹ +
          ((ddhAdvantage P.g (ddhReduction P A) + (Fintype.card F : ℝ≥0∞)⁻¹) +
          (EntropySmoothing.advantage F P.g P.kdf (esReduction P A) +
          otAdvantage P.senc (otReduction P A))) :=
        add_le_add le_rfl (add_le_add (hop_ddh hg A) (add_le_add (hop_es hg A) (hop_ot P A)))
    _ = _ := by ring

end AuditPay.RestrictedMonitoring.Decrypt
