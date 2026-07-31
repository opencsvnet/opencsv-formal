/-!
# Abstract cryptographic interfaces (paper §4.1, §6 item 1)

This file collects **every cryptographic hardness assumption** that the security
argument of paper §5 depends on. They are stated here, once, as clearly labeled
`axiom` declarations (for the concrete primitives) and as a structure field (for
the abstract proof system, which must be generic over the statement it proves).

Every theorem in `OpenCsv/Theorems.lean` is **conditional on exactly these
assumptions** — nothing else is trusted. In particular:

* the AIR/FRI proof system is *not* modeled — only its soundness, abstractly;
* Poseidon is *not* modeled — only the injectivity (collision-resistance)
  properties the protocol arguments actually use;
* the issuer signature scheme is *not* modeled — only an abstract
  EUF-CMA-style unforgeability property.

Reading guide: `axiom P : T` declares an opaque constant `P` of type `T` that
the proofs may use but never inspect. An `axiom` stating a *property* of such a
constant is precisely a cryptographic assumption.
-/

namespace OpenCsv

/-- Injectivity of a function. (Lean core without mathlib does not provide
`Function.Injective`, so we define it here.) Used to state collision-resistance
assumptions: an injective hash fixes its preimage. -/
def Injective {α β : Type} (f : α → β) : Prop := ∀ a b, f a = f b → a = b

/-- Carrier for field elements, digests, keys, and nullifiers (paper §4.1: `𝔽`).
We use `Nat` purely as a convenient countable carrier with decidable equality;
the development never uses arithmetic on it — only equality. -/
abbrev F := Nat

/-- Owner secret keys (paper §4.3: `osk`). Modeled as `Nat` for the same reason. -/
abbrev OwnerSecret := Nat

/-! ## Asset genesis (paper §4.2) -/

/-- Genesis parameters `G = (ipk, currency_code, terms_hash, nonce)`. -/
structure Asset where
  /-- Issuer public key for this asset. -/
  ipk : F
  /-- Currency code (e.g. USD). -/
  currency : F
  /-- Hash of the asset's human/legal terms. -/
  termsHash : F
  /-- Domain-separation nonce. -/
  nonce : F

/-- `asset_id := H("OpenCSV-asset" ∥ G)` — opaque hash of the genesis parameters. -/
axiom assetId : Asset → F

/-- **Cryptographic assumption (collision resistance of `H` at genesis).**
Distinct genesis parameters yield distinct asset IDs. This is what "the issuer
key is bound into the asset through genesis" means formally (§4.4 item 1). -/
axiom assetId_injective : Injective assetId

/-! ## Coins, commitments, nullifiers (paper §4.3) -/

/-- A coin `coin = (asset_id, v, owner, r)`. -/
structure Coin where
  /-- Asset this coin is denominated in. -/
  asset : F
  /-- Value in base units. The paper's range check `0 ≤ v < 2^64` is automatic
  in this model: values are natural numbers and all conservation sums are
  exact, so wrap-around is impossible by construction. -/
  value : Nat
  /-- Owner public key, `owner = H(osk)`. -/
  owner : F
  /-- Hiding randomness. -/
  r : F

/-- Coin commitment `C := H("coin" ∥ asset_id ∥ v ∥ owner ∥ r)` — opaque. -/
axiom commitHash : Coin → F

/-- **Cryptographic assumption (binding of the commitment scheme, §4.3).**
A commitment fixes exactly one coin: `H` is injective on coin openings.
Stated for completeness; the nullifier argument (T3) below identifies coins
with their openings directly, so only `ownerKey_injective` is load-bearing
there. -/
axiom commitHash_injective : Injective commitHash

/-- Owner-key derivation `owner = H(osk)` — opaque. -/
axiom ownerKey : OwnerSecret → F

/-- **Cryptographic assumption (collision resistance of `H` at owner keys).**
One owner public key comes from exactly one owner secret. This is the
injectivity the double-spend argument (T3, paper §5.2) actually needs: two
well-formed spends of one coin must use the same `osk`. -/
axiom ownerKey_injective : Injective ownerKey

/-- Nullifier derivation `nf := H("null" ∥ osk ∥ C)` — opaque.

Note that T3 needs *no* hardness assumption on `nullHash`: it is a function,
so once `osk` and `C` are fixed, the nullifier is determined. That is exactly
the paper's point (§4.3): "one coin can only ever yield one `nf`". -/
axiom nullHash : OwnerSecret → F → F

/-! ## Anchor context binding (the anti-grief fix, corrected)

Anchor records are copyable bytes: a mempool spy can copy a record into their
own transaction and try to win the first-occurrence race, freezing the
victim's coins. A *publicly self-consistent* binding `B = H(nf, ctx)` does not
help — `nf` and `ctx` are both on-chain, so anyone can recompute it. The
corrected design: the on-chain payload **is** the bound value
`P = H(raw_nf, ctx)`; the raw nullifier never appears on-chain (only in
consignments and proofs). Well-formedness is relative to a `raw_nf` supplied
by the verifier, so occurrences of a coin are recognizable only to those who
know its raw nullifier — consignment holders. That scoping is intended. -/

/-- Anchoring context `ctx`: derived from the carrying Bitcoin transaction's
input side. Modeled abstractly as a field element; the *un-reproducibility*
property (a copier's transaction derives a different `ctx` — in fact a context
fresh w.r.t. the whole log, since each transaction spends its own inputs)
appears as an explicit hypothesis in the anti-grief theorems. -/
abbrev AnchorCtx := F

/-- Context-binding hash `P = H(raw_nf, ctx)` — opaque. -/
axiom bindHash : F → AnchorCtx → F

/-- An **anchor entry** in the on-chain log: the payload `P` (the bound value
`H(raw_nf, ctx)`) and the carrying transaction's context `ctx`. The raw
nullifier is *not* part of the entry. -/
structure AnchorEntry where
  /-- The on-chain payload, claimed to be `H(raw_nf, ctx)` for the spent
  coin's raw nullifier. -/
  P : F
  /-- The carrying transaction's context. -/
  ctx : AnchorCtx

/-- **Well-formedness of an occurrence, relative to a raw nullifier** supplied
by the verifier (from the consignment/proof): the payload must be the binding
of that raw nullifier under the entry's context. Only well-formed entries
count as occurrences in the first-occurrence rule. -/
def AnchorEntry.wellFormed (e : AnchorEntry) (raw_nf : F) : Prop :=
  e.P = bindHash raw_nf e.ctx

/-- **Cryptographic assumption (collision resistance of `H` at the anchor
binding).** The binding is injective in both arguments: two different
`(raw_nf, ctx)` pairs never share a payload. This is what makes an occurrence
commit to exactly one coin under exactly one carrying context
(`payload_binds_one_nullifier`, `copied_record_not_wellformed`). -/
axiom bindHash_injective :
  ∀ nf₁ ctx₁ nf₂ ctx₂, bindHash nf₁ ctx₁ = bindHash nf₂ ctx₂ → nf₁ = nf₂ ∧ ctx₁ = ctx₂

/-- Abstract adversarial knowledge of a raw nullifier, given the public chain
log. Consignment holders know their coins' raw nullifiers *off-chain*; this
predicate is about what an adversary can derive/compute. Left abstract —
constrained by the preimage-resistance assumption below. -/
axiom KnowsRawNf : List AnchorEntry → F → Prop

/-- **Cryptographic assumption (preimage resistance of `H` at the anchor
binding).** Producing a *fresh* well-formed occurrence of `raw_nf` — one whose
context is not already on-chain, i.e. genuinely computed by the adversary
rather than replayed — requires knowing `raw_nf`. Equivalently: from the
payload `P = H(raw_nf, ctx)` alone, an adversary cannot derive `raw_nf` well
enough to bind it under a new context. (Honestly produced anchors are exempt:
their context is already in the log, so the freshness side condition fails —
the honest sender learned `raw_nf` from the coin's consignment anyway.) -/
axiom occurrence_requires_knowledge :
  ∀ (log : List AnchorEntry) (e : AnchorEntry) (raw_nf : F),
    e.wellFormed raw_nf → (∀ e' ∈ log, e'.ctx ≠ e.ctx) → KnowsRawNf log raw_nf

/-! ## Issuer signatures (paper §4.1: `Σ`, §4.4 item 1) -/

/-- The mint message signed by the issuer: `(asset_id, V, mint_nonce)`. -/
structure MintMsg where
  /-- Asset being minted (`asset_id`, bound to `ipk` via genesis). -/
  asset : F
  /-- Public total minted value `V`. -/
  value : Nat
  /-- Fresh mint nonce. -/
  nonce : F

/-- Signature type of the issuer scheme `Σ` — opaque. -/
axiom Sig : Type

/-- Signature verification `Σ.Verify(ipk, m, σ) ∈ {0,1}` — opaque. -/
axiom SigVerify : F → MintMsg → Sig → Bool

/-- The set of mint messages actually signed under `ipk` by the issuer (or by
whoever holds `isk`). This is the "signing oracle" side of the EUF-CMA game,
left abstract: we never say *which* messages are in it. -/
axiom SignedByIssuer : F → MintMsg → Prop

/-- **Cryptographic assumption (EUF-CMA unforgeability of `Σ`, abstractly).**
Any signature that verifies under `ipk` on a mint message was produced with
the issuer's secret key. Adversaries that could produce a verifying signature
on an unsigned message would break this axiom — that is the only way mint
authorization (§4.4 item 1) can fail. -/
axiom sig_unforgeable :
  ∀ (ipk : F) (m : MintMsg) (σ : Sig), SigVerify ipk m σ = true → SignedByIssuer ipk m

/-! ## The proof system `Π` (paper §4.1, §6 item 1) -/

/-- An abstract argument system `Π` for a compliance predicate, parameterized
by the type `Stmt` of public inputs (statements).

* `Holds` is the compliance predicate: `Holds x` means "the public input `x`
  describes a compliant computation" (for OpenCSV: a valid protocol step
  extending a valid coin trace — see `Compliance` in `State.lean`).
* `sound` is the **soundness assumption (paper §5: "soundness of `Π`")**,
  stated once: whenever `Π.Verify` accepts, the predicate genuinely holds
  (for some witness — the witness is existentially hidden, which is all the
  protocol logic ever needs).

This structure is a *hypothesis bundle*: the theorems quantify over arbitrary
`ProofSystem`s, so they hold of any proof system that is actually sound. The
AIR/FRI construction that would make `sound` true is deliberately NOT
mechanized (paper §6, "deliberately not mechanized"). -/
structure ProofSystem (Stmt : Type) where
  /-- Proof strings. -/
  Proof : Type
  /-- Verification keys (one per predicate: mint / transfer / redeem). -/
  Vk : Type
  /-- The compliance predicate this system argues about. -/
  Holds : Stmt → Prop
  /-- The verifier `Π.Verify(vk, x, π)`. -/
  verify : Vk → Stmt → Proof → Bool
  /-- **Cryptographic assumption: soundness of `Π`.** -/
  sound : ∀ (vk : Vk) (x : Stmt) (π : Proof), verify vk x π = true → Holds x

end OpenCsv
