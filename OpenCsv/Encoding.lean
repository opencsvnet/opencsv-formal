import OpenCsv.Value

/-!
# Canonical BabyBear digest encoding

The protocol model usually treats a field element as a mathematical value.
The Rust wire format must make a stricter claim: every digest is eight
little-endian `u32` limbs and each limb is the unique representative below
the BabyBear modulus. A decoder rejects, rather than reduces, any limb at or
above the modulus.

This module separates that representation theorem from the state-machine and
conservation theorems. It models the eight decoded `u32` integers; byte-order
and fixed-width parsing remain Rust serialization obligations checked by the
source-correspondence gate and adversarial tests.
-/

namespace OpenCsv.Encoding

/-- One decoded `u32` limb is canonical exactly below the BabyBear modulus. -/
def CanonicalLimb (encoded : Nat) : Prop := encoded < Value.babyBear

/-- The field value denoted by an integer limb. This is only an explanatory
projection: production deserialization does not call it for a non-canonical
limb. -/
def fieldValue (encoded : Nat) : Nat := encoded % Value.babyBear

/-- A strict decoder accepts the unique canonical representative and rejects
all integers at or above the modulus. -/
def decodeLimb (encoded : Nat) : Option Nat :=
  if encoded < Value.babyBear then some encoded else none

theorem decode_limb_accepts_canonical {encoded : Nat} (h : CanonicalLimb encoded) :
    decodeLimb encoded = some encoded := by
  change encoded < Value.babyBear at h
  rw [decodeLimb, if_pos h]

theorem decode_limb_rejects_noncanonical {encoded : Nat} (h : ¬ CanonicalLimb encoded) :
    decodeLimb encoded = none := by
  change ¬ encoded < Value.babyBear at h
  rw [decodeLimb, if_neg h]

/-- Canonical representatives are unique: if two accepted limbs denote the
same field element, their integer encodings are identical. -/
theorem canonical_limb_unique {left right : Nat}
    (hleft : CanonicalLimb left) (hright : CanonicalLimb right)
    (hsame : fieldValue left = fieldValue right) : left = right := by
  rw [fieldValue, Nat.mod_eq_of_lt hleft] at hsame
  rw [fieldValue, Nat.mod_eq_of_lt hright] at hsame
  exact hsame

/-- A full 32-byte digest after little-endian parsing: exactly eight integer
limbs. The `u32` width need not be repeated here because canonicality below
BabyBear is already a stronger upper bound. -/
abbrev EncodedDigest := Fin 8 → Nat

def CanonicalDigest (digest : EncodedDigest) : Prop :=
  ∀ index, CanonicalLimb (digest index)

def digestFieldValues (digest : EncodedDigest) : Fin 8 → Nat :=
  fun index => fieldValue (digest index)

/-- Eight-limb canonical encoding is injective pointwise. No non-canonical
"twin" can pass as a second byte identity for the same field digest. -/
theorem canonical_digest_injective {left right : EncodedDigest}
    (hleft : CanonicalDigest left) (hright : CanonicalDigest right)
    (hsame : digestFieldValues left = digestFieldValues right) : left = right := by
  funext index
  exact canonical_limb_unique (hleft index) (hright index)
    (congrFun hsame index)

/-- Reduction alone is ambiguous: zero and the modulus are distinct integer
encodings of the same field element. This is why deserialization rejects the
second encoding instead of silently normalizing it. -/
theorem modular_reduction_has_noncanonical_twins :
    0 ≠ Value.babyBear ∧
    fieldValue 0 = fieldValue Value.babyBear ∧
    ¬ CanonicalLimb Value.babyBear := by
  simp [Value.babyBear, fieldValue, CanonicalLimb]

/-! ## Axiom audit -/

#print axioms decode_limb_accepts_canonical
#print axioms decode_limb_rejects_noncanonical
#print axioms canonical_limb_unique
#print axioms canonical_digest_injective
#print axioms modular_reduction_has_noncanonical_twins

end OpenCsv.Encoding
