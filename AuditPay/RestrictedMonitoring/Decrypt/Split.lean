/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.RestrictedMonitoring.Decrypt.Defs

/-!
# Theorem 3, decryption game: singling out the target ciphertext

The decryption game samples the messages and ephemeral scalars as two uniform vectors. The
hybrids sample the target's message and scalar separately and overwrite the target's ciphertext.
Since resampling one coordinate of a uniform vector leaves it uniform (`uniform_update_eqd`),
the real hybrid is the game (`experiment_eqd`).
-/

open OracleComp DiffieHellman ENNReal

namespace AuditPay.RestrictedMonitoring.Decrypt

open SLIND (Mode)

/-- Resampling one coordinate of a uniformly random tuple leaves it uniform. -/
theorem uniform_update_eqd {N : ℕ} {α β : Type} [SampleableType α] (i : Fin N)
    (f : (Fin N → α) → ProbComp β) :
    (do let v ← $ᵗ (Fin N → α); let x ← $ᵗ α; f (Function.update v i x)) =ᵈ
      (($ᵗ (Fin N → α) : ProbComp (Fin N → α)) >>= f) := by
  let : MeasurableSpace β := ⊤
  have h := SampleableType.evalDist_uniformSample_bind_equiv_symm (Equiv.funSplitAt i α)
    (fun _ v => f v)
  have hupd : ∀ (x : α) (v : Fin N → α),
      (Equiv.funSplitAt i α).symm (x, (Equiv.funSplitAt i α v).2) = Function.update v i x := by
    intro x v
    funext j
    by_cases hj : j = i
    · subst hj
      simp [Equiv.funSplitAt, Equiv.piSplitAt]
    · simp [Equiv.funSplitAt, Equiv.piSplitAt, hj]
  simp only [hupd] at h
  exact (bind_swap_eqd _ _ _).trans (EvalDistEq.of_evalDist_eq h)

variable {F G Addr HK Key Msg C σ : Type} {k n : ℕ}
  [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G]
  [Fintype Addr] [DecidableEq Addr] [SampleableType HK] [SampleableType Key]
  [DecidableEq Msg] [SampleableType Msg]

omit [Fintype F] [DecidableEq F] [SampleableType F] [SampleableType G] [DecidableEq Addr]
  [SampleableType HK] [SampleableType Key] [DecidableEq Msg] [SampleableType Msg] in
/-- Overwriting ciphertext `i₀` with a fresh encryption of `μ` with ephemeral scalar `ρ` gives
the challenge for the vectors with their `i₀`-th coordinates replaced. -/
theorem update_challenge (P : Params F G Addr HK Key Msg C k n) (hk : HK) (H : Addr → G)
    (c : Commit F Addr σ n) (m : Fin (n + 1) → Msg) (r : Fin (n + 1) → F) (i₀ : Fin (n + 1))
    (μ : Msg) (ρ : F) :
    Function.update (challenge P hk H c m r) i₀
        (encrypt (P.kdf hk) P.senc P.g (retrieveKey P.pos P.coef (c.vec P.g H) (c.addrs i₀))
          (H (c.addrs i₀)) ρ μ) =
      challenge P hk H c (Function.update m i₀ μ) (Function.update r i₀ ρ) := by
  funext i
  by_cases hi : i = i₀
  · subst hi
    simp [challenge]
  · simp [challenge, hi]

omit [Fintype F] in
/-- The decryption game is the real hybrid: sampling the target's message and ephemeral scalar
separately does not change the game. -/
theorem experiment_eqd (P : Params F G Addr HK Key Msg C k n)
    (A : Adversary F G Addr HK Msg C σ n) : experiment P A =ᵈ hybrid P A .real := by
  simp only [experiment, hybrid, slot, finish, pure_bind, update_challenge]
  refine EvalDistEq.bind_right _ fun hk => EvalDistEq.bind_right _ fun H =>
    EvalDistEq.bind_right _ fun c => ?_
  let body : (Fin (n + 1) → Msg) → (Fin (n + 1) → F) → ProbComp Bool := fun m r => do
    let m' ← A.respond c.state (challenge P hk H c m r)
    return decide (∀ i, m' i = m i)
  refine EvalDistEq.symm ?_
  -- sample the target's message right after the message vector
  refine EvalDistEq.trans (my := do
      let m ← $ᵗ (Fin (n + 1) → Msg); let μ ← $ᵗ Msg
      let r ← $ᵗ (Fin (n + 1) → F); let ρ ← $ᵗ F
      body (Function.update m (c.target P) μ) (Function.update r (c.target P) ρ)) ?_ ?_
  · exact EvalDistEq.bind_right _ fun m => bind_swap_eqd _ _ _
  -- absorb the target's ephemeral scalar into the vector of scalars
  refine EvalDistEq.trans (my := do
      let m ← $ᵗ (Fin (n + 1) → Msg); let μ ← $ᵗ Msg
      let r ← $ᵗ (Fin (n + 1) → F)
      body (Function.update m (c.target P) μ) r) ?_ ?_
  · exact EvalDistEq.bind_right _ fun m => EvalDistEq.bind_right _ fun μ =>
      uniform_update_eqd (c.target P) fun r => body (Function.update m (c.target P) μ) r
  -- absorb the target's message into the vector of messages
  exact uniform_update_eqd (c.target P) fun m => do
    let r ← $ᵗ (Fin (n + 1) → F)
    body m r

end AuditPay.RestrictedMonitoring.Decrypt
