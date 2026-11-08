/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.SLINDRO.Defs

/-!
# Theorem 2 with a random-oracle KDF, the paper's scheme: the game written out

The SL-IND game of `AuditPay.SLINDRO` for Algorithm 2 (`KdfRO.single`: one ephemeral value, the
key derived from `r • (RetrieveKey(V, a) - H(a))`), written out in full; it is the generic game
at the variant `single F g` by `rfl`. Its bounds are proved in `AuditPay.SLINDRO.StrongDH`
(option 2: strong Diffie–Hellman, tight) and `AuditPay.SLINDRO.Guess` (option 1: CDH with a
loss factor in the number of KDF queries).
-/

open OracleComp OracleSpec ENNReal

namespace AuditPay.SLINDRO.Single

open KdfRO

variable {F G Addr Key Note DTx WCore C Proof σ : Type} {k n : ℕ}
  [Field F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G]
  [Fintype Addr] [DecidableEq Addr] [SampleableType Key]
  (sel : Selection F Addr k n) (P : Params F G Addr F G Key Note DTx WCore C Proof k n)
  (A : Adversary F G Addr G G Key DTx WCore C Proof σ n)

/-- The SL-IND game for bit `b` with a random-oracle KDF and the paper's selective encryption:
ciphertext `(SymEnc_{KDF(r • (RetrieveKey(V, a) - H(a)))}(note), r • g)` for the sender `d_b`
and the recipient `w_addr`, with the KDF queried. -/
noncomputable def game (b : Bool) : OracleComp (unifSpec + (G →ₒ Key)) Bool := do
  let H ← $ᵗ (Addr → G)
  let c ← A.choose H
  let ox ← setup sel P b H c
  match ox with
  | none => return false
  | some x => do
    let rS ← $ᵗ F
    let rR ← $ᵗ F
    let keyS ← query (spec := G →ₒ Key)
      (encPoint rS (retrieveKey P.pos P.coef x.V (x.sender b)) (x.H (x.sender b)))
    let keyR ← query (spec := G →ₒ Key)
      (encPoint rR (retrieveKey P.pos P.coef x.V x.c.wAddr) (x.H x.c.wAddr))
    let ctS := (P.senc keyS (x.note b), rS • P.g)
    let ctR := (P.senc keyR (x.note b), rR • P.g)
    let π ← P.zk.prove (stmt x ctS ctR) (x.note b, x.sender b, rS, rR)
    finish A x ctS ctR π

omit [SampleableType Key] in
theorem game_eq (b : Bool) : game sel P A b = SLINDRO.game (single F P.g) sel P A b := rfl

variable [DecidableEq G]

/-- The SL-IND experiment for bit `b`: the game run in the random oracle model. -/
noncomputable def experiment (b : Bool) : ProbComp Bool := roExec (game sel P A b)

/-- The SL-IND advantage with a random-oracle KDF, for the paper's scheme. -/
noncomputable def advantage : ℝ≥0∞ :=
  𝒟[experiment sel P A false].boolDist 𝒟[experiment sel P A true]

theorem advantage_eq : advantage sel P A = SLINDRO.advantage (single F P.g) sel P A := rfl

end AuditPay.SLINDRO.Single
