# OpenCSV — Lean 4 formalization (paper §6)

Mechanization of the OpenCSV **protocol logic** — the coin state machine
(genesis → mint → transfer* → redeem), the value-conservation invariant, and
nullifier uniqueness — per the formal verification roadmap of paper §6.

Dependency-free: plain Lean 4 stdlib only (no mathlib). Toolchain pinned in
`lean-toolchain` (`leanprover/lean4:v4.15.0`).

## Build

```sh
lake build
```

Expected result: `Build completed successfully.`, with the axiom audit at the
end of `OpenCsv/Theorems.lean` printing the exact assumptions of each headline
theorem. The development contains **no `sorry` and no `admit`** (grep it);
every cryptographic hardness assumption is an explicitly labeled `axiom` in
`OpenCsv/Interfaces.lean` or the `sound` field of the `ProofSystem` structure.

## Layout

```
OpenCsv.lean            # root: imports the three modules
OpenCsv/Interfaces.lean # §6 item 1 — abstract crypto interfaces + ALL assumptions
OpenCsv/State.lean      # §6 item 2 — coin state machine (valid traces)
OpenCsv/Theorems.lean   # §6 item 3 — theorems T1–T4 + corollaries
```

## What the theorems say, and what they correspond to

### T1 — Inflation soundness (`inflation_soundness`, `mints_signed`, `mints_authorized`)

- **Statement.** Along any valid trace, per asset: net value in circulation
  (produced − consumed) = Σ mint `V` − Σ redeem `V`. Moreover every mint step
  carries a valid issuer signature, hence (by the abstract EUF-CMA assumption
  `sig_unforgeable`) was authorized by the issuer key holder.
- **Paper.** §5.1 (the claim and its induction over the PCD tree), with the
  supply function of §4.9 as the right-hand side.
- **Rust.** The mint-side conditions abstract the mint predicate AIR of
  `crates/opencsv-pcd/src/mint.rs` (`Σ v_i = V`, `mint_commit` binding, output
  commitment recomputation) plus the issuer-signature check of
  `crates/opencsv-core/src/accept.rs` (kept off-circuit in the prototype — see
  "Not mechanized" below). The redeem-side conditions abstract the redeem
  circuit described in `crates/opencsv-pcd/src/node.rs` (public `V` = coin
  value, ownership, nullifier). The supply equation is
  `crates/opencsv-core/src/audit.rs` (`supply`).
- **Proof.** Induction over the `ValidTrace` inductive; each step preserves a
  natural-number balance equation (the integer form follows by `omega`).

### T2 — Conservation (`transfer_conservation`, `transfer_pool_unchanged`)

- **Statement.** Every transfer step of a valid trace preserves per-asset
  totals: per asset, output value = input value; hence the per-asset value of
  the live pool is unchanged by a transfer.
- **Paper.** §4.5 item 2 (range-checked exact sums — wrap-around is impossible
  in this model because values are natural numbers, matching the circuit's
  in-circuit range checks).
- **Rust.** The transfer predicate's conservation constraints in
  `crates/opencsv-pcd/src/node.rs` (via `crates/opencsv-pcd/src/value.rs`:
  `enforce_sum_eq`, `range_check_value`).
- **Proof.** Inversion on the trace inductive (`ValidTrace.inv_snoc`) — the
  property is a constructor condition of `StepValid`, proved as a lemma anyway
  per the roadmap.

### T3 — Nullifier uniqueness (`nullifier_unique`, `first_occurrence_unique`,
`later_occurrence_rejected`, `double_spend_conflict`, `double_spend_observable`)

- **Statement.** Two well-formed spends of the same coin emit equal nullifiers
  (ownership `owner = H(osk)` + collision resistance of the owner-key
  derivation force the same `osk`; the nullifier is then determined, since
  `H("null" ∥ osk ∥ C)` is a function). The anchor log is an ordered list with
  a first-occurrence rule (`IsFirstOccurrence`); two positions that both pass
  the first-occurrence check for the same nullifier are equal, and any other
  occurrence is necessarily later and rejected. Hence two recipients cannot
  both finally accept spends of one coin, and any attempt is an observable
  conflict (equal nullifiers at distinct anchor positions).
- **Paper.** §5.2 and §4.7 rules 1–3.
- **Rust.** `crates/opencsv-core/src/coin.rs` (`Coin::nullifier`),
  `crates/opencsv-core/src/anchor.rs` (`AnchorRecord::nullifier_keys`), and the
  first-occurrence scan in `crates/opencsv-core/src/accept.rs`
  (`first_nullifier_occurrence`, `RejectReason::NullifierConflict`).
- **Proof.** `nullifier_unique` is the only step using a hardness assumption
  (`ownerKey_injective` — collision resistance of `owner = H(osk)`); the
  first-occurrence lemmas are pure list reasoning (`later_occurrence_rejected`
  depends on no axioms at all, as the axiom audit confirms).
- **Scope note.** The 0-conf hazard (a conflicting anchor confirmed *first*)
  is Bitcoin's own finality assumption (§4.7 rule 2), not protocol logic; the
  `k ≤ confs` conjunct of `Accept` records where it enters.

### T4 — Receiver correctness (`Accept`, `receiver_correctness`,
`accept_nullifier_no_earlier_occurrence`, `accepted_trace_supply`)

- **Statement.** `Accept` is the §4.8 check list as a Prop: proof verifies,
  the transaction publishes nullifier keys with no earlier occurrence in the
  receiver's verified chain prefix, the anchor has ≥ `k` confirmations, and a
  recipient key derives the owner of at least one claimed output. If `Accept`
  holds, then — modulo proof-system soundness — the received transaction
  extends a trace in the `ValidTrace` inductive and produces the claimed
  outputs; the extended trace satisfies the T1 audit equation
  (`accepted_trace_supply`).
- **Paper.** §4.8 (steps 2–4) composed with §5.1.
- **Rust.** `crates/opencsv-core/src/accept.rs` (`accept`, `AcceptParams`,
  `RejectReason`), with the proof-verifier seam `ProofVerifier` corresponding
  to the abstract `ProofSystem` structure (its `sound` field is what the
  `MockVerifier` in the prototype deliberately does *not* provide).
- **Proof.** One application of the soundness field, then the `snoc`
  constructor of `ValidTrace`.

## Where the cryptographic hardness lives (complete list)

All in `OpenCsv/Interfaces.lean`:

| Assumption | Form | Used by |
|---|---|---|
| `assetId_injective` | collision resistance of the genesis hash | asset binding (stated; the state machine threads `asset_id` directly) |
| `commitHash_injective` | binding of coin commitments | stated for completeness (T3 identifies coins with their openings) |
| `ownerKey_injective` | collision resistance of `owner = H(osk)` | **T3** (`nullifier_unique`) |
| `sig_unforgeable` | EUF-CMA of the issuer scheme, abstractly | **T1** (`mints_authorized`) |
| `ProofSystem.sound` | soundness of `Π`, as a structure field | **T4** (`receiver_correctness`) |

`propext` / `Quot.sound` appearing in the axiom audit are Lean core axioms,
not assumptions of the development.

## Deliberately NOT mechanized

- **AIR/FRI soundness** — the proof system `Π` appears only through its
  abstract soundness field. Proving FRI sound is a proof-system-level result
  for a dedicated formalization (paper §6).
- **Poseidon cryptanalysis** — the hash appears only through the injectivity
  (collision-resistance) hypotheses above. No concrete Poseidon, no BabyBear
  field arithmetic.
- **The off-circuit Ed25519 issuer signature of the prototype** — the Rust
  prototype verifies the issuer signature outside the circuit
  (`crates/opencsv-core`, deviation documented in
  `crates/opencsv-pcd/src/mint.rs`); the formalization models the paper's
  target (issuer authorization as part of the mint predicate's validity
  conditions) via the abstract `SigVerify` / `sig_unforgeable` interface.
- **The hash-compressed multi-input anchor** (`XFERC`, `H(nf_1 ∥ … ∥ nf_m)` in
  `crates/opencsv-core/src/anchor.rs`) — the model's anchor log records
  individual nullifier keys; the compressed variant is an encoding detail of
  the 64-byte budget.
- **Liveness/finality** — reorgs, censorship, and consignment non-delivery
  (§5.4) are not state-machine properties; only the `k ≤ confs` policy check
  is recorded in `Accept`.
- **Privacy** (§5.3) — hiding/unlinkability are not formalized here; the
  roadmap's item 3 covers the soundness side only.
