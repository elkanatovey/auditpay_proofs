/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

/-!
# The strong Diffie–Hellman assumption

## The game

The challenger samples uniform scalars `x, y` and gives the adversary `(g, X, Y)` with
`X = x • g`, `Y = y • g`. The adversary also gets **oracle access** to a *decision oracle fixed
to the challenge `X`*: on a query `(U, V)` of two group elements of its choice, the oracle answers
whether `V = x • U`. The adversary wins if it outputs `(x * y) • g`.

Without the oracle this is VCV-io's `DiffieHellman.cdhExperiment`. The adversary is an oracle
computation: it cannot inspect the oracle, only query it, and the experiment answers the queries
with the secret `x`.

## Relation to the literature

This is the *strong Diffie–Hellman* assumption of Abdalla, Bellare and Rogaway (DHIES, CT-RSA
2001): CDH with a decision oracle `O_x(U, V) = [V = x • U]` restricted to one fixed exponent, the
one of the challenge element `X`. It is implied by the *gap* Diffie–Hellman assumption
(Okamoto–Pointcheval), whose decision oracle takes an arbitrary third base, and it implies CDH
(`cdhExperiment_eq_experiment_liftAdversary`: an adversary may ignore the oracle). It is unrelated
to the `q`-strong Diffie–Hellman assumption of Boneh and Boyen.
-/

open OracleComp OracleSpec DiffieHellman ENNReal

namespace AuditPay.StrongDH

/-- The decision oracle of the strong Diffie–Hellman problem: a query is a pair `(U, V)` of group
elements, the answer a Boolean. -/
abbrev oracleSpec (G : Type) : OracleSpec (G × G) := (G × G) →ₒ Bool

/-- A strong Diffie–Hellman adversary: given `(g, X, Y)`, and with oracle access to the decision
oracle (and to uniform sampling), it outputs a group element. `_F` is a phantom parameter for the
scalar field, as in VCV-io's `CDHAdversary`. -/
def Adversary (_F G : Type) := G → G → G → OracleComp (unifSpec + oracleSpec G) G

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The decision oracle for the secret scalar `x`: uniform-sampling queries are forwarded, and a
query `(U, V)` is answered by whether `V = x • U`. -/
def oracleImpl (x : F) : QueryImpl (unifSpec + oracleSpec G) ProbComp :=
  unifFwdAnswerImpl (QueryImpl.ofFn fun q : G × G => decide (q.2 = x • q.1))

/-- The strong Diffie–Hellman experiment: sample `x, y`, run the adversary on
`(g, x • g, y • g)` with the decision oracle for `x`, and check whether it outputs
`(x * y) • g`. -/
def experiment [SampleableType F] (g : G) (adversary : Adversary F G) : ProbComp Bool := do
  let x ← $ᵗ F
  let y ← $ᵗ F
  let h ← simulateQ (oracleImpl x) (adversary g (x • g) (y • g))
  return decide (h = (x * y) • g)

/-! ## Running computations against the decision oracle -/

/-- A computation that does not use the decision oracle is unaffected by it. -/
@[simp]
theorem simulateQ_oracleImpl_liftM {α : Type} (x : F) (pc : ProbComp α) :
    simulateQ (oracleImpl (G := G) x) (liftM pc : OracleComp (unifSpec + oracleSpec G) α) = pc := by
  simp [oracleImpl, unifFwdAnswerImpl, QueryImpl.simulateQ_add_liftM_left]

/-- A decision query `(U, V)` is answered by whether `V = x • U`. -/
@[simp]
theorem simulateQ_oracleImpl_query (x : F) (U V : G) :
    simulateQ (oracleImpl (G := G) x)
        (query (spec := oracleSpec G) (U, V) : OracleComp (unifSpec + oracleSpec G) Bool) =
      pure (decide (V = x • U)) := by
  simp only [oracleImpl, unifFwdAnswerImpl, QueryImpl.passthrough_add]
  erw [QueryImpl.simulateQ_add_liftM_query_right]
  rfl

/-- Search a list of candidates `Z` for one with `Z = x • P`, with one decision query `(P, Z)`
per candidate, stopping at the first hit. -/
def scan (P : G) : List G → OracleComp (unifSpec + oracleSpec G) (Option G)
  | [] => pure none
  | Z :: Zs => do
    let hit ← query (spec := oracleSpec G) (P, Z)
    if hit then pure (some Z) else scan P Zs

/-- Against the decision oracle for `x`, the scan returns the first candidate equal to `x • P`. -/
@[simp]
theorem simulateQ_oracleImpl_scan (x : F) (P : G) (Zs : List G) :
    simulateQ (oracleImpl (G := G) x) (scan P Zs) =
      pure (Zs.find? fun Z => decide (Z = x • P)) := by
  induction Zs with
  | nil => simp [scan]
  | cons Z Zs ih =>
    simp only [scan, simulateQ_bind, List.find?_cons, simulateQ_oracleImpl_query, pure_bind]
    by_cases h : Z = x • P <;> simp [h, ih]

/-! ## Strong Diffie–Hellman implies CDH -/

/-- A CDH adversary as a strong Diffie–Hellman adversary that never queries the oracle. -/
def liftAdversary (adversary : CDHAdversary F G) : Adversary F G :=
  fun g X Y => liftM (adversary g X Y)

/-- A CDH adversary succeeds in the strong Diffie–Hellman experiment exactly as often as in the
CDH experiment: the strong assumption implies CDH. -/
theorem cdhExperiment_eq_experiment_liftAdversary [SampleableType F] (g : G)
    (adversary : CDHAdversary F G) :
    experiment g (liftAdversary adversary) = cdhExperiment g adversary := by
  simp only [experiment, liftAdversary, simulateQ_oracleImpl_liftM, cdhExperiment]

end AuditPay.StrongDH
