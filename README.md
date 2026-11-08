# AuditPay — Lean formalization

Machine-checked proofs of the security theorems of *AuditPay: Anonymous Payments with
Controlled Oversight* (CCS '26). Every theorem is proved with no `sorry` and depends only on
Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Build and check

From this directory (the `formal/` directory of the paper repository, or the root of the
standalone repository <https://github.com/elkanatovey/auditpay_proofs>):

```
lake exe cache get   # Mathlib build cache
lake build
```

Toolchain: Lean `v4.35.0` (see `lean-toolchain`). Depends on
[VCV-io](https://github.com/Verified-zkEVM/VCV-io), pinned to a commit in `lakefile.toml`;
VCV-io brings Mathlib `v4.35.0`. Bump the pin on purpose, not with a bare `lake update`. To
check axioms, run `#print axioms` on a theorem in a file that does `import AuditPay`.

## Theorems of the paper

| Paper | Lean | Statement |
|---|---|---|
| Algorithm 2 (selective encryption), correctness | `AuditPay.decrypt_encrypt` | a ciphertext to a monitored address decrypts |
| Algorithm 3 (auditkey vector), correctness | `AuditPay.decrypt_encrypt_retrieveKey_set`, `SilentDrop.retrieveKey_encodeSet_select` | an encoded address retrieves its audit key and decrypts |
| Theorem 1 (IND-Key) | `AuditPay.IndKey.advantage_le` | `Adv ≤ DDH + 1/|F|` |
| Theorem 2 (SL-IND) | `AuditPay.SLINDDrop.advantage_le` | `Adv ≤ ZK + 2·(DDH + 1/|F| + ES + OT) + Mixer`, for any selection rule |
| Theorem 3 (Restricted Monitoring) | `AuditPay.RestrictedMonitoring.SharedSecret.success_le` | `Pr[win] ≤ CDH + 1/|F|`, for an arbitrary vector |
| Theorem 4 (Membership Hiding), hiding | `AuditPay.SilentDrop.advantage_eq_zero` | `Adv = 0`: the published vector is uniform for every request |
| Theorem 4, coverage | `AuditPay.SilentDrop.prob_exists_dropped_le` | the first `s` addresses of every request are encoded, except with probability `depBound Q n k s |F|` |
| §7.4 (singular sparse matrix) | `AuditPay.card_singular_le` | `Pr[det M = 0] ≤ hallBound n k + n/|F|` |

`DDH`, `CDH`, `ES` (entropy smoothing of the KDF), `OT` (one-time security of the cipher), `ZK`
and `Mixer` denote the advantage or success probability of a named reduction built from the
adversary. `Q` is the number of addresses whose hashes the adversary has evaluated, `n = |V|`,
`k` the number of hash functions and `s` the cap on the monitored set (the paper uses
`s = n/2`); `depBound` and `hallBound` are explicit finite sums (`AuditPay.Dependence`,
`AuditPay.Singularity`), and `scripts/depbound.py` evaluates them.

## Additional results

Not claimed in the paper; proved alongside.

- Theorem 2 for the padded, square vector generation: `AuditPay.SLIND.advantage_le`.
- Theorem 3 with the adversary outputting audit secret keys: `AuditPay.RestrictedMonitoring.success_le`
  (DLog); and with the adversary decrypting, for algebraic adversaries:
  `AuditPay.RestrictedMonitoring.Decrypt.success_le` (DDH, ES, OT).
- Theorem 4 with the game that fails on dependent rows: `AuditPay.MembershipHidingPublic.advantage_le`;
  and with the hash functions sampled after the candidate sets: `AuditPay.MembershipHiding.advantage_le`.
- Selective encryption and Theorems 2 and 3 without DDH, with the KDF as a random oracle:
  under strong Diffie–Hellman (`AuditPay.NoteHiding.advantage_le`, `AuditPay.Monitoring.StrongDH.experiment_le`,
  `AuditPay.SLINDRO.StrongDH.advantage_le`), under CDH with two ephemeral values per ciphertext
  (`…Twin…`), and under CDH with a guessing loss (`…Guess…`); one-wayness of the shared key
  (`AuditPay.SharedKeyOW`, `AuditPay.SLINDRO.OW`); strong DH implies CDH (`AuditPay.StrongDH`).

## Layout

`Defs` (Algorithms 2 and 3), `SetEncoding`, `SilentDrop` (vector generation), `Prob`
(probability helpers), `IndKey` (Theorem 1), `SLIND/*`, `SLINDDrop/*` (Theorem 2),
`RestrictedMonitoring*` (Theorem 3), `MembershipHiding*`, `Dependence/*` (Theorem 4),
`Singularity/*` (§7.4), `KdfRO/*`, `StrongDH`, `SharedKeyOW`, `NoteHiding`, `Monitoring`,
`SLINDRO/*` (results without DDH), `scripts/` (numerics).
