/-!
# The u64 conservation gadget (opencsv-rs `crates/opencsv-pcd/src/value.rs`)

Mechanized soundness of the circuit's value representation and carry-chain
sum constraint (paper §4.5 item 2: per-asset conservation over range-checked
values — "wrap-around cannot fake balance").

Model (plain Lean, no mathlib):

* values are three little-endian limbs of 24/24/16 bits (`Limbs`), matching
  `opencsv-core`'s `u64_to_felts` encoding;
* the field is modeled as the integers modulo the BabyBear prime
  `p = 2^31 − 2^27 + 1`: field equality of two integer representatives is
  divisibility of their difference by `p` (`FieldEq`). Primality of `p` is
  never used — the soundness argument needs only the size bound, so we do
  not prove it.

The circuit (`enforce_sum_eq`) constrains, per limb `i` with carry `c_i`
(`c_0 = 0`):

```text
t_i = lhs[0][i] + lhs[1][i] + c_i − rhs[0][i] − rhs[1][i]
t_i = 2^24 · c_{i+1}        (in the field; c_{i+1} ∈ {0,1}; c_3 = 0)
```

using a uniform radix `2^24` on all three limbs — the deliberate 72-bit
carry arithmetic of the Rust doc comment. `carryConstraints` below is a
one-to-one model of these equations.
-/

namespace OpenCsv.Value

/-- The BabyBear prime `p = 2^31 − 2^27 + 1 = 2013265921`. Only its size is
used, never its primality. -/
def babyBear : Nat := 2^31 - 2^27 + 1

/-- Field equality, modeled on integer representatives: `x ≡ y (mod p)`.
This is exactly what an in-circuit equality constraint over BabyBear means
for integer witnesses. -/
def FieldEq (x y : Int) : Prop := (babyBear : Int) ∣ x - y

/-- Three little-endian limbs (24, 24, 16 bits). -/
structure Limbs where
  /-- Low limb, 24 bits. -/
  l0 : Nat
  /-- Middle limb, 24 bits. -/
  l1 : Nat
  /-- Top limb, 16 bits. -/
  l2 : Nat

/-- The circuit's range check (`decompose_to_bits` with 24/24/16 bits):
each limb below its bit width. -/
def rangeChecked (l : Limbs) : Prop := l.l0 < 2^24 ∧ l.l1 < 2^24 ∧ l.l2 < 2^16

/-- The integer a limb triple encodes: `l0 + 2^24·l1 + 2^48·l2`. -/
def encode (l : Limbs) : Nat := l.l0 + 2^24 * l.l1 + 2^48 * l.l2

/-! ## Part 1 — a range-checked triple represents exactly `[0, 2^64)` -/

/-- Every range-checked triple encodes a value below `2^64`. -/
theorem encode_lt {l : Limbs} (h : rangeChecked l) : encode l < 2^64 := by
  obtain ⟨hl0, hl1, hl2⟩ := h
  simp only [encode]
  omega

/-- The encoding is injective on range-checked triples: a checked triple
encodes a *unique* value, and each value has at most one checked triple. -/
theorem encode_injective {l m : Limbs} (hl : rangeChecked l) (hm : rangeChecked m)
    (h : encode l = encode m) : l = m := by
  obtain ⟨l0, l1, l2⟩ := l
  obtain ⟨m0, m1, m2⟩ := m
  simp only [rangeChecked, encode] at hl hm h
  obtain ⟨hl0, hl1, hl2⟩ := hl
  obtain ⟨hm0, hm1, hm2⟩ := hm
  -- Peel off one limb at a time: the low limb is determined mod 2^24, etc.
  have e0 : l0 = m0 := by omega
  have e1 : l1 = m1 := by omega
  have e2 : l2 = m2 := by omega
  subst e0; subst e1; subst e2; rfl

/-- Every value below `2^64` has a range-checked encoding (the honest
decomposition `u64_to_felts`). -/
theorem encode_surjective {v : Nat} (hv : v < 2^64) :
    ∃ l : Limbs, rangeChecked l ∧ encode l = v := by
  have hdiv : v / 2^24 / 2^24 = v / 2^48 := by rw [Nat.div_div_eq_div_mul]
  refine ⟨⟨v % 2^24, (v / 2^24) % 2^24, v / 2^48⟩,
    ⟨by show v % 2^24 < 2^24; omega,
     by show (v / 2^24) % 2^24 < 2^24; omega,
     by show v / 2^48 < 2^16; omega⟩, ?_⟩
  show v % 2^24 + 2^24 * ((v / 2^24) % 2^24) + 2^48 * (v / 2^48) = v
  omega

/-- **Representation is exact** (the rustdoc claim: "a checked limb triple
encodes a unique value in `[0, 2^64)`"): bounded, injective, surjective. -/
theorem range_checked_represents_exactly :
    (∀ l : Limbs, rangeChecked l → encode l < 2^64) ∧
    (∀ l m : Limbs, rangeChecked l → rangeChecked m → encode l = encode m → l = m) ∧
    (∀ v : Nat, v < 2^64 → ∃ l : Limbs, rangeChecked l ∧ encode l = v) :=
  ⟨fun _l h => encode_lt h, fun _l _m hl hm h => encode_injective hl hm h,
   fun _v hv => encode_surjective hv⟩

/-! ## Part 2 — the key bound: `(-2^26, 2^26) ⊂ (-p/2, p/2)` -/

/-- The per-limb difference bound: with limbs below `2^24` and a boolean
incoming carry, the per-limb difference lies in `(-2^26, 2^26)`. (The top
limb's tighter `2^16` bound only makes the interval smaller; we reuse this
lemma there via the implied `2^24` bounds.) -/
theorem per_limb_difference_bound {x0 x1 y0 y1 : Nat} {c : Int}
    (hx0 : x0 < 2^24) (hx1 : x1 < 2^24) (hy0 : y0 < 2^24) (hy1 : y1 < 2^24)
    (hc : c = 0 ∨ c = 1) :
    -(2:Int)^26 < (x0 : Int) + x1 + c - y0 - y1 ∧
      (x0 : Int) + x1 + c - y0 - y1 < 2^26 := by
  rcases hc with rfl | rfl <;> omega

/-- **The key numerical fact.** The difference interval `(-2^26, 2^26)` lies
strictly inside `(-p/2, p/2)` for the BabyBear prime `p = 2^31 − 2^27 + 1`:
`2^26 < p/2 = 1006632960`. Hence two integers from these intervals that are
equal modulo `p` are equal, period — no modular wrap can satisfy a carry
equation spuriously. -/
theorem difference_interval_within_half_field :
    (2:Int)^26 < (babyBear : Int) / 2 := by
  have hp : (babyBear : Int) = 2013265921 := by decide
  rw [hp]; decide

/-- **No-wrap lemma.** Two integers in `(-2^26, 2^26)` that are equal in the
field are equal as integers: their difference is a multiple of `p` with
absolute value below `2^27 < p`, so it is zero. This is the load-bearing
step of the soundness argument. -/
theorem no_wrap {x y : Int} (hx : -(2:Int)^26 < x ∧ x < 2^26)
    (hy : -(2:Int)^26 < y ∧ y < 2^26) (h : FieldEq x y) : x = y := by
  have hp : (babyBear : Int) = 2013265921 := by decide
  obtain ⟨k, hk⟩ := h
  rw [hp] at hk
  -- x − y = p·k with |x − y| < 2^27 < p, forcing k = 0.
  have hk0 : k = 0 := by omega
  omega

/-! ## Part 3 — the carry-chain constraints and their soundness -/

/-- A carry witness for the sum constraint: the four carries of the chain
(`c_0` pinned to zero, `c_3` the final carry, pinned to zero by the
constraints). -/
structure CarryWitness where
  /-- Incoming carry of limb 0 (always 0). -/
  c0 : Int
  /-- Carry out of limb 0 / into limb 1. -/
  c1 : Int
  /-- Carry out of limb 1 / into limb 2. -/
  c2 : Int
  /-- Final carry out of limb 2 (pinned to 0: no overflow past the top). -/
  c3 : Int

/-- A boolean carry, as enforced in-circuit by a 1-bit decomposition
(`decompose_to_bits(next, 1)`). -/
def isBit (c : Int) : Prop := c = 0 ∨ c = 1

/-- **The constraints of `enforce_sum_eq`, modeled one-to-one.** Per limb,
the difference `lhs[0][i] + lhs[1][i] + c_i − rhs[0][i] − rhs[1][i]` equals
`2^24 · c_{i+1}` *in the field*; each outgoing carry is boolean; the final
carry is pinned to zero. Uniform radix `2^24` on all three limbs, exactly as
in the circuit (including the top, 16-bit limb). -/
def carryConstraints (lhs0 lhs1 rhs0 rhs1 : Limbs) (w : CarryWitness) : Prop :=
  w.c0 = 0 ∧ isBit w.c1 ∧ isBit w.c2 ∧ w.c3 = 0 ∧
  FieldEq ((lhs0.l0 : Int) + lhs1.l0 + w.c0 - rhs0.l0 - rhs1.l0) (2^24 * w.c1) ∧
  FieldEq ((lhs0.l1 : Int) + lhs1.l1 + w.c1 - rhs0.l1 - rhs1.l1) (2^24 * w.c2) ∧
  FieldEq ((lhs0.l2 : Int) + lhs1.l2 + w.c2 - rhs0.l2 - rhs1.l2) (2^24 * w.c3)

/-- **Carry soundness — the conservation gadget is sound.** If the
carry-chain constraints hold in the field (boolean carries, final carry
zero) and all four values are range-checked, then the integer sums are
equal: `encode lhs0 + encode lhs1 = encode rhs0 + encode rhs1`. Equality
holds over the integers, not just mod `p` — wrap-around cannot fake
balance. -/
theorem carry_sound {lhs0 lhs1 rhs0 rhs1 : Limbs} (w : CarryWitness)
    (hl0 : rangeChecked lhs0) (hl1 : rangeChecked lhs1)
    (hr0 : rangeChecked rhs0) (hr1 : rangeChecked rhs1)
    (h : carryConstraints lhs0 lhs1 rhs0 rhs1 w) :
    encode lhs0 + encode lhs1 = encode rhs0 + encode rhs1 := by
  obtain ⟨hc0, hc1, hc2, hc3, e0, e1, e2⟩ := h
  obtain ⟨ha0, ha1, ha2⟩ := hl0
  obtain ⟨hb0, hb1, hb2⟩ := hl1
  obtain ⟨hd0, hd1, hd2⟩ := hr0
  obtain ⟨he0, he1, he2⟩ := hr1
  -- Each field equation lifts to an integer equation via the no-wrap lemma:
  -- the per-limb difference and `2^24·c` both lie in `(-2^26, 2^26)`.
  have i0 : (lhs0.l0 : Int) + lhs1.l0 + w.c0 - rhs0.l0 - rhs1.l0 = 2^24 * w.c1 :=
    no_wrap (per_limb_difference_bound ha0 hb0 hd0 he0 (Or.inl hc0))
      (by rcases hc1 with h | h <;> rw [h] <;> constructor <;> omega) e0
  have i1 : (lhs0.l1 : Int) + lhs1.l1 + w.c1 - rhs0.l1 - rhs1.l1 = 2^24 * w.c2 :=
    no_wrap (per_limb_difference_bound ha1 hb1 hd1 he1 hc1)
      (by rcases hc2 with h | h <;> rw [h] <;> constructor <;> omega) e1
  have i2 : (lhs0.l2 : Int) + lhs1.l2 + w.c2 - rhs0.l2 - rhs1.l2 = 2^24 * w.c3 :=
    no_wrap
      (per_limb_difference_bound (by omega) (by omega) (by omega) (by omega) hc2)
      (by rw [hc3]; constructor <;> omega) e2
  -- Telescope the chain: the carries cancel and the encodings match.
  simp only [encode]
  omega

/-- **Honest direction (completeness) for the circuit's mint usage**
(`enforce_sum_eq [out0, out1] [V, 0]`): if the integer sums balance against
a single value, a boolean carry witness with final carry zero exists.

The general two-addends-both-sides converse is *false*: `(0,1,0) + (0,0,0)`
and `(2^24−1,0,0) + (1,0,0)` both encode `2^24`, yet the limb-0 difference
is `−2^24`, requiring carry `−1 ∉ {0,1}` — the circuit rejects this
(witness-generation failure). This is a completeness limitation, not a
soundness issue: the prover chooses the outputs and can always pick a
provable split. -/
theorem carry_complete_single {lhs0 lhs1 rhs : Limbs}
    (hl0 : rangeChecked lhs0) (hl1 : rangeChecked lhs1) (hr : rangeChecked rhs)
    (hbal : encode lhs0 + encode lhs1 = encode rhs + encode ⟨0, 0, 0⟩) :
    ∃ w : CarryWitness, carryConstraints lhs0 lhs1 rhs ⟨0, 0, 0⟩ w := by
  obtain ⟨ha0, ha1, ha2⟩ := hl0
  obtain ⟨hb0, hb1, hb2⟩ := hl1
  obtain ⟨hd0, hd1, hd2⟩ := hr
  -- The balance equation over the integers, limb by limb.
  have hbalI : (lhs0.l0 : Int) + 2^24 * lhs0.l1 + 2^48 * lhs0.l2
      + (lhs1.l0 + 2^24 * lhs1.l1 + 2^48 * lhs1.l2)
      = (rhs.l0 : Int) + 2^24 * rhs.l1 + 2^48 * rhs.l2 := by
    have h := hbal
    simp only [encode] at h
    omega
  -- Per-limb differences `u_i` and the natural carries of the balanced
  -- subtraction: `c1 = −(u1 + 2^24·u2)`, `c2 = −u2`.
  generalize hu1 : ((lhs0.l1 : Int) + lhs1.l1 - rhs.l1) = u1
  generalize hu2 : ((lhs0.l2 : Int) + lhs1.l2 - rhs.l2) = u2
  -- The carries are boolean: the limb-0 difference is `2^24·c1` and lies in
  -- `(-2^24, 2^25)`, forcing `c1 ∈ {0,1}`; then the limb-1 difference with
  -- incoming carry is `2^24·c2` in the same interval, forcing `c2 ∈ {0,1}`.
  have hc1 : -(u1 + 2^24 * u2) = 0 ∨ -(u1 + 2^24 * u2) = 1 := by omega
  have hc2 : -u2 = 0 ∨ -u2 = 1 := by omega
  -- The three carry equations hold as integer equalities (hence in the field).
  refine ⟨⟨0, -(u1 + 2^24 * u2), -u2, 0⟩, rfl, hc1, hc2, rfl, ?_, ?_, ?_⟩
  · show FieldEq ((lhs0.l0 : Int) + lhs1.l0 + 0 - rhs.l0 - 0)
      (2^24 * (-(u1 + 2^24 * u2)))
    exact ⟨0, by omega⟩
  · show FieldEq ((lhs0.l1 : Int) + lhs1.l1 + (-(u1 + 2^24 * u2)) - rhs.l1 - 0)
      (2^24 * (-u2))
    exact ⟨0, by omega⟩
  · show FieldEq ((lhs0.l2 : Int) + lhs1.l2 + (-u2) - rhs.l2 - 0) (2^24 * 0)
    exact ⟨0, by omega⟩

/-! ## Axiom audit -/

#print axioms range_checked_represents_exactly
#print axioms difference_interval_within_half_field
#print axioms no_wrap
#print axioms carry_sound
#print axioms carry_complete_single

end OpenCsv.Value
