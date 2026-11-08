/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.Defs

/-!
# Selective encryption with two ephemeral values, and the shape shared by both variants

## The two-ephemeral-value variant

Algorithm 2 of the paper publishes one ephemeral point `R = r • g` and derives the symmetric key
from one Diffie–Hellman point `K = r • (AK - H(a'))`. In the *twin* variant the encryptor picks
two ephemeral scalars `r₁, r₂`, publishes `R₁ = r₁ • g` and `R₂ = r₂ • g`, and derives the key
from the **pair** `(r₁ • P, r₂ • P)` with `P = AK - H(a')`. The auditor, who knows `sk`, computes
the same pair as `(sk • R₁, sk • R₂)` (`Twin.encPoint_auditKey`). Compared with Algorithm 2 this
costs the encryptor two more scalar multiplications and one more published group element per
ciphertext (and the auditor one more scalar multiplication per decryption).

The variant exists because of its security proof: with a random-oracle key-derivation function
its note hiding reduces *tightly* to the plain computational Diffie–Hellman problem, through the
twin Diffie–Hellman trapdoor test of Cash, Kiltz and Shoup (see
`AuditPay.NoteHiding.Twin`), whereas for Algorithm 2 a tight proof needs the strong
Diffie–Hellman assumption.

## The shape of a variant

The games of `AuditPay.KdfRO` are written once for both variants. A `Variant` records how the
ephemeral randomness `ρ` determines the published ephemeral data (`eph`) and, together with the
point `P = AK - H(a')`, the input of the key-derivation function (`pt`).
-/

namespace AuditPay

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

namespace Twin

/-- The encryptor's pair of shared points in the twin variant: `(r₁ • P, r₂ • P)` with
`P = AK - H(a')`. -/
def encPoint (r : F × F) (ak Ha' : G) : G × G :=
  (AuditPay.encPoint r.1 ak Ha', AuditPay.encPoint r.2 ak Ha')

/-- The decryptor's pair of shared points in the twin variant: `(sk • R₁, sk • R₂)`. -/
def decPoint (sk : F) (R : G × G) : G × G :=
  (AuditPay.decPoint sk R.1, AuditPay.decPoint sk R.2)

/-- Correctness of the twin variant's key agreement: if the encryptor's address is the audit
key's address, the encryptor's pair equals the decryptor's, for the ephemeral keys
`(r₁ • g, r₂ • g)`. -/
theorem encPoint_auditKey (g Ha : G) (sk : F) (r : F × F) :
    encPoint r (auditKey g sk Ha) Ha = decPoint sk (r.1 • g, r.2 • g) := by
  simp [encPoint, decPoint, AuditPay.encPoint_auditKey]

/-- Twin-variant encryption, given a key-derivation function on pairs of points and a
deterministic symmetric cipher. Returns `(SymEnc_{KDF(K₁, K₂)}(m), R₁, R₂)`. -/
def encrypt {K M C : Type*} (kdf : G × G → K) (senc : K → M → C)
    (g : G) (ak Ha' : G) (r : F × F) (m : M) : C × G × G :=
  (senc (kdf (encPoint r ak Ha')) m, r.1 • g, r.2 • g)

/-- Twin-variant decryption. -/
def decrypt {K M C : Type*} (kdf : G × G → K) (sdec : K → C → Option M)
    (sk : F) (ct : C × G × G) : Option M :=
  sdec (kdf (decPoint sk ct.2)) ct.1

/-- Correctness of the twin variant: decryption with `sk` recovers `m` from an encryption under
`AuditKey(a)` made by the owner of `a`. -/
theorem decrypt_encrypt {K M C : Type*} (kdf : G × G → K) (senc : K → M → C)
    (sdec : K → C → Option M) (hsym : ∀ k m, sdec k (senc k m) = some m)
    (g Ha : G) (sk : F) (r : F × F) (m : M) :
    decrypt kdf sdec sk (encrypt kdf senc g (auditKey g sk Ha) Ha r m) = some m := by
  simp [decrypt, encrypt, encPoint_auditKey, hsym]

end Twin

namespace KdfRO

/-- The Diffie–Hellman part of a selective-encryption variant: `ρ` is the encryptor's ephemeral
randomness, `E` the published ephemeral data, `X` the input type of the key-derivation
function. -/
structure Variant (G ρ E X : Type*) where
  /-- The published ephemeral data. -/
  eph : ρ → E
  /-- The input of the key-derivation function, from the ephemeral randomness and the point
  `P = AK - H(a')`. -/
  pt : ρ → G → X

variable (F) in
/-- Algorithm 2 of the paper: `R = r • g` is published and the key is derived from `r • P`. -/
def single (g : G) : Variant G F G G where
  eph r := r • g
  pt r P := r • P

variable (F) in
/-- The twin variant: `(r₁ • g, r₂ • g)` is published and the key is derived from the pair
`(r₁ • P, r₂ • P)`. -/
def twin (g : G) : Variant G (F × F) (G × G) (G × G) where
  eph r := (r.1 • g, r.2 • g)
  pt r P := (r.1 • P, r.2 • P)

end KdfRO

end AuditPay
