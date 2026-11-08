/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.SLINDRO.Generic
import AuditPay.SLINDRO.OW
import AuditPay.SLINDRO.Single
import AuditPay.SLINDRO.StrongDH
import AuditPay.SLINDRO.Twin
import AuditPay.SLINDRO.Guess

/-!
# Theorem 2 (SL-IND) with a random-oracle KDF, without DDH

The SL-IND game of `AuditPay.SLINDDrop` (Theorem 2 for the never-failing generation) with the
key-derivation function modelled, as in the paper, as a random oracle that the adversary
queries (`AuditPay.SLINDRO.Defs`). The DDH and entropy-smoothing hops of the DDH-based proof are
replaced by one random-oracle hop per ciphertext (`AuditPay.SLINDRO.HopRO`), whose cost is the
probability that the ciphertext's shared point is queried; that probability is bounded through
the one-wayness of the shared key in the SL-IND setting (`AuditPay.SLINDRO.OW`), in three
options:

* option 2 (`AuditPay.SLINDRO.StrongDH.advantage_le`): Algorithm 2 as is, under strong
  Diffie–Hellman, with no loss beyond `1/|F|` terms;
* option 3 (`AuditPay.SLINDRO.Twin.advantage_le`): the twin variant (two ephemeral values per
  ciphertext), under CDH, with a loss of `(q₁ + q₂ + 1)/|F|` per ciphertext;
* option 1 (`AuditPay.SLINDRO.Guess.advantage_le`): Algorithm 2 as is, under CDH, with a loss
  factor of `q₁ + q₂ + 2` per ciphertext.

In every option the bound is, for each value of the hidden bit, the zero-knowledge advantage of
a named reduction, a one-wayness term per ciphertext (as above), and the one-time advantage of
a named reduction per ciphertext; plus the base-mixer unlinkability advantage of a named
reduction once (`AuditPay.SLINDRO.advantage_le_queryProb`).
-/
