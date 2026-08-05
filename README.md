# OpenCSV — Lean 4 formalization (paper §6)

Part of [github.com/opencsvnet](https://github.com/opencsvnet): the
scheme paper and explainer site live in
[opencsv](https://github.com/opencsvnet/opencsv), the Rust reference
implementation in [opencsv-rs](https://github.com/opencsvnet/opencsv-rs).
Paths of the form `crates/…` below refer to the `opencsv-rs` repo.

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
The current baseline audits **72 named declarations**: 54 from the reviewed
state/value/scan/batching model, seven v4 one-input specializations, and eleven
recursive-lineage/tree declarations.

## Layout

```
OpenCsv.lean            # root: imports the modules
OpenCsv/Interfaces.lean # §6 item 1 — abstract crypto interfaces + ALL assumptions
OpenCsv/State.lean      # §6 item 2 — coin state machine (valid traces)
OpenCsv/Theorems.lean   # §6 item 3 — theorems T1–T4 + corollaries
OpenCsv/Value.lean      # the u64 limb/carry conservation gadget (value.rs)
OpenCsv/Scan.lean       # scan-first indexing model (paper §4.7.1)
OpenCsv/Batch.lean      # envelope occurrence + co-funded batching v2 model
OpenCsv/Forward.lean    # v4 one-input/two-output forwarding specialization
OpenCsv/Lineage.lean    # unfolded PCD tree, exact edges, distinct inputs, version policy
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
  commitment recomputation) and the authenticated v3/v4 issuer-seed relation
  in `crates/opencsv-pcd/src/issuer.rs` / `node.rs`. Lean's abstract
  `SigVerify` expresses the authorization property, not the retired external
  Ed25519 wire format. The redeem-side conditions abstract the redeem circuit
  in `node.rs` (public `V` = coin value, ownership, nullifier). The supply equation is
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

#### Proof-lineage v4 one-input forwarding (`OpenCsv/Forward.lean`)

- **Statement shape.** `v4OneInputStatement` exposes one real nullifier,
  exactly zero in the compatibility padding slot, and the commitments of the
  recipient and change outputs. `v4_one_input_statement_exact` fixes all four
  fields; `v4_one_input_slots_distinct` shows a nonzero real nullifier cannot
  alias padding. The padding slot never creates a second spend or anchor.
- **Semantics.** `oneInputForwarding` is exactly
  `Step.transfer [spend] [recipient, change] ctx`.
  `one_input_forwarding_valid_iff` expands validity into ownership/nullifier
  correctness, predecessor liveness, and per-asset conservation.
  `one_input_forwarding_conservation` and
  `one_input_forwarding_value_equation` prove recipient plus change equals the
  one consumed coin; `one_input_forwarding_pool_unchanged` specializes T2/T1
  supply preservation; `one_input_forwarding_anchor_exact` proves only the
  real nullifier is context-bound on-chain.
- **Rust correspondence.** These definitions mirror proof lineage v4 in
  `crates/opencsv-pcd/src/node.rs`: one authenticated predecessor, statement
  version 4, `nf_1` real, `nf_2 = 0`, two output commitments, and exact
  conservation. CI checks the exact pinned Rust revision in
  `rust-correspondence-v4.json` and fails if those constants, constraints,
  field ordering, native statement projection, version test, or verifier tag
  drift. The Lean model proves the state semantics and statement projection;
  the source gate only links that model to a reviewed Rust shape. It does not
  claim to verify the AIR implementation or postcard envelope; those remain
  covered by Rust construction/adversarial tests and the explicit proof-system
  trust boundary below.

#### Recursive PCD lineage (`OpenCsv/Lineage.lean`)

- **Tree shape.** `ProofLineage` records the root version/step, immediate
  predecessor proof trees, and output selectors. `EdgesMatch` pairs every
  predecessor and selector with exactly one consumed spend; its length theorem
  rules out silent list truncation. The tree is the unfolded serialized proof
  view; an implementation may cache identical subtrees as a DAG without
  changing any local edge result.
- **Recursive validity.** Every immediate predecessor is itself valid, its
  selected root output equals the consumed coin, ownership/nullifier witnesses
  are valid, and per-asset conservation holds at every transfer root.
  `two_input_lineage_distinct` proves that a two-input recursive node contains
  neither a repeated coin nor a repeated nullifier.
- **Fail-closed migration.** Transfer and redeem nodes are v4. An
  ancestor-free v3 mint may be a migration leaf, while
  `legacy_transfer_lineage_impossible` and
  `legacy_redeem_lineage_impossible` exclude unsafe legacy recursive nodes.
  `v4_one_input_lineage_valid_iff` connects the tree directly to the existing
  recipient-plus-change specialization.
- **Rust correspondence.** CI pins exact `opencsv-rs@9b9eca2` and checks the
  AIR distinct-input selector/inversion constraint, production v4-root gate,
  mint-only v3 predecessor policy, and adversarial Rust receipts as well as the
  earlier one-input statement shape. This remains a source-drift gate, not a
  Lean proof of Rust/AIR/FRI equivalence.

### T3 — Nullifier uniqueness (`nullifier_unique`, `first_occurrence_unique`,
`later_occurrence_rejected`, `payload_binds_one_nullifier`,
`double_spend_conflict`, `double_spend_observable`) and the anti-grief fix
(`copied_record_not_wellformed`, `griefer_copy_invisible`,
`no_occurrence_without_knowledge`, `unknowing_adversary_entry_invisible`)

- **Statement.** Two well-formed spends of the same coin emit equal raw
  nullifiers (ownership `owner = H(osk)` + collision resistance of the
  owner-key derivation force the same `osk`; the nullifier is then determined,
  since `H("null" ∥ osk ∥ C)` is a function). The anchor log is an ordered
  list of **anchor entries `(P, ctx)`** where the on-chain payload is
  `P = H(raw_nf, ctx)` — the raw nullifier never appears on-chain.
  Occurrences are *relative to a verifier-supplied raw nullifier*:
  `wellFormed(e, raw_nf) ⟺ e.P = H(raw_nf, e.ctx)`. The first-occurrence rule
  (`IsFirstOccurrence`) counts only well-formed entries; two positions that
  both pass the check for the same raw nullifier are equal, and any other
  well-formed occurrence is necessarily later and rejected. Hence two
  recipients cannot both finally accept spends of one coin.
- **Paper.** §5.2 and §4.7 rules 1–3.
- **Rust.** `crates/opencsv-core/src/coin.rs` (`Coin::nullifier`),
  `crates/opencsv-core/src/anchor.rs` (`AnchorRecord::nullifier_keys`), and the
  first-occurrence scan in `crates/opencsv-core/src/accept.rs`
  (`first_nullifier_occurrence`, `RejectReason::NullifierConflict`).
- **Proof.** `nullifier_unique` is the only step using a hardness assumption
  (`ownerKey_injective` — collision resistance of `owner = H(osk)`); the
  first-occurrence lemmas are pure list reasoning over the entry model;
  `payload_binds_one_nullifier` (one payload is an occurrence of at most one
  coin) uses `bindHash_injective`.
- **Scope note (observability).** Under the corrected anchor model the raw
  nullifier stays off-chain, so a double-spend conflict is observable **by
  consignment holders** — the parties who know `raw_nf` and whose acceptance
  is at stake — not by arbitrary chain observers. This scoping is intended.
  Separately, the 0-conf hazard (a conflicting anchor confirmed *first*) is
  Bitcoin's own finality assumption (§4.7 rule 2), not protocol logic; the
  `k ≤ confs` conjunct of `Accept` records where it enters.

#### The griefing fix (bound-payload occurrences, corrected)

Anchor records are copyable bytes: a mempool spy could copy a record into
their own transaction and try to win the first-occurrence race, freezing the
victim's coins. A first attempt — a publicly self-consistent binding
`B = H(nf, ctx)` in the record — does **not** fix this: `nf` and `ctx` are
both on-chain, so anyone can recompute the binding. The corrected design
makes the payload itself the bound value `P = H(raw_nf, ctx)` and keeps the
raw nullifier off-chain (consignments/proofs only). In the model:

- `AnchorEntry` = `(P, ctx)`; `AnchorEntry.wellFormed e raw_nf : e.P =
  bindHash raw_nf e.ctx` is relative to the verifier's `raw_nf`;
  `OccurrenceAt` / `IsFirstOccurrence` quantify over well-formed entries
  only; honest steps publish `⟨bindHash sp.nf ctx, ctx⟩` and are well-formed
  by construction (`Step.anchors_wellformed`).
- **Replay** fails by injectivity: `copied_record_not_wellformed` (from
  `bindHash_injective`, a copied payload under `ctx' ≠ ctx` satisfies
  `P ≠ H(raw_nf, ctx')`) and `griefer_copy_invisible` (the copy is no
  occurrence at all, at any position).
- **Recomputation** fails by preimage resistance:
  `no_occurrence_without_knowledge` — an adversary who does not know
  `raw_nf` cannot produce any fresh-context entry well-formed for it (via
  the `occurrence_requires_knowledge` axiom) — and its positioned form
  `unknowing_adversary_entry_invisible`.
- The copier's inability to reproduce `ctx` is a *deployment* hypothesis of
  the fix (ctx is derived from the carrying transaction's own inputs, fresh
  w.r.t. the log); it appears as explicit hypotheses (`ctx' ≠ ctx`,
  freshness) in the theorems, not as an axiom. The new axioms are
  `bindHash_injective` (collision resistance) and
  `occurrence_requires_knowledge` (preimage resistance), replacing the
  earlier `bindHash_ctx_injective`. The axiom audit confirms each theorem's
  exact dependencies.

### T4 — Receiver correctness (`Accept`, `receiver_correctness`,
`accept_nullifier_no_earlier_occurrence`, `accepted_trace_supply`)

- **Statement.** `Accept` is the §4.8 check list as a Prop: proof verifies,
  the transaction publishes nullifier keys with no earlier *well-formed*
  occurrence in the receiver's verified chain prefix (the anti-grief form of
  the first-occurrence check), the anchor has ≥ `k` confirmations, and a
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

### The u64 conservation gadget (`OpenCsv/Value.lean`: `encode_lt`,
`encode_injective`, `encode_surjective`, `range_checked_represents_exactly`,
`per_limb_difference_bound`, `difference_interval_within_half_field`,
`no_wrap`, `carry_sound`, `carry_complete_single`)

- **Statement.** Coin values are u64, decomposed in-circuit into three
  little-endian limbs of 24/24/16 bits. (i) A range-checked triple (each limb
  below its width) represents *exactly* the integers `[0, 2^64)`: bounded,
  injective, surjective (`range_checked_represents_exactly`). (ii) The sum
  constraint's carry chain — per limb `t_i = lhs[0][i] + lhs[1][i] + c_i −
  rhs[0][i] − rhs[1][i]`, `t_i = 2^24·c_{i+1}` in the field, boolean carries,
  final carry zero, uniform radix `2^24` — is sound: if it holds, the integer
  sums are equal (`carry_sound`). (iii) The key lemma: per-limb differences
  lie in `(-2^26, 2^26) ⊂ (-p/2, p/2)` for the BabyBear prime
  `p = 2^31 − 2^27 + 1` (`difference_interval_within_half_field`), so field
  equality of the carry equations is integer equality — wrap-around cannot
  fake balance (`no_wrap`). (iv) The honest direction holds for the mint
  usage `[out0, out1] = [V, 0]` (`carry_complete_single`); the general
  two-addends-both-sides converse is false (the module documents the
  counterexample `(0,1,0) + 0 = (2^24−1,0,0) + (1,0,0)`, which needs carry
  `−1`) — a completeness limitation only, since the prover chooses outputs.
- **Paper.** §4.5 item 2 (conservation with range-checked values: "sums are
  computed over opened witness values with per-value range checks, so
  wrap-around cannot fake balance").
- **Rust.** `crates/opencsv-pcd/src/value.rs` (`u64_to_felts`,
  `range_check_value`, `enforce_sum_eq` — `carryConstraints` in the Lean
  module is a one-to-one model of that function's equations), used by
  `mint.rs` and `node.rs`. Field equality is modeled as congruence modulo
  `p = 2013265921` over the integers; primality of `p` is never used (only
  the size bound), so the module needs **no project axioms at all** — the
  axiom audit shows only Lean core axioms (`propext`/`Quot.sound`/
  `Classical.choice`, via `omega`).
- **Proof.** All arithmetic is closed by `omega` over `Int`/`Nat` (including
  div/mod by literal radices); the only manual steps are the no-wrap
  divisibility argument and the carry telescope.

### Scan-first indexing (`OpenCsv/Scan.lean`: `filter_no_false_negatives`,
`filter_absence_trustless`, `anchor_bearing_is_candidate`,
`scan_exclusion_sound`, `scan_exclusion_sound_iff_absent`,
`marker_zero_authority`, `markers_without_records_no_occurrence`,
`served_list_falsifiable`)

- **Statement.** Production indexing is scan-first (paper §4.7.1, amended):
  anchor transactions carry a protocol-constant marker script so
  BIP158-style compact filters identify anchor-bearing blocks; the wallet
  downloads only candidate blocks and evaluates occurrences locally against
  the bound-payload rule. The module models blocks as script/record sets and
  a compact filter as the *image* of the script set under a deterministic
  `filterItem` map. (i) No false negatives by construction
  (`filter_no_false_negatives` — an image-membership lemma) and trustless
  absence (`filter_absence_trustless` — its contrapositive). (ii) Every
  anchor-bearing block is a candidate (`anchor_bearing_is_candidate`).
  (iii) Headline: a local scan over the index (exactly the records of all
  candidate blocks in the window) finds an occurrence of `raw_nf` iff one
  exists on-chain in the window (`scan_exclusion_sound`, plus the
  exclusion-form `scan_exclusion_sound_iff_absent`). (iv) Marker
  zero-authority: a marked block with no well-formed record for `raw_nf`
  yields no occurrence (`marker_zero_authority`) — the marker never enters
  the occurrence definition. (v) Accelerator fraud provability: with
  `deriveList : Block → List α` deterministic, any served `l ≠ deriveList
  blk` yields an index where the lists differ — a short,
  third-party-checkable witness (`served_list_falsifiable`).
- **Paper.** §4.7.1 (amended): marker scripts, compact-filter candidate
  selection, local occurrence evaluation; the first-occurrence rule itself
  is unchanged (T3 in `Theorems.lean`).
- **Rust.** `crates/opencsv-cbf` — the scan engine: `src/gcs.rs`
  (BIP158 Golomb-coded sets; the model's `filterItem` abstracts the
  keyed SipHash item map), `src/fullscan.rs` (zero-trust self-scan over a
  bounded `[birth, spend]` window — `ChainOccurrence`/`ScanFinds` and the
  window semantics documented there), and the occurrence test
  `H("bind" ∥ raw_nf ∥ ctx)` against each candidate record
  (`AnchorEntry.wellFormed` in `Interfaces.lean`).
- **Hypotheses, not axioms.** The module needs **no new hardness
  assumptions** (audit: only core axioms plus the pre-existing `bindHash`
  constant through `wellFormed`). Two deployment facts appear as explicit
  theorem hypotheses: `hmarked` (every block carrying a well-formed record
  for `raw_nf` carries the marker — the protocol marking rule, coherent
  with the anti-grief results since well-formed records require knowing
  `raw_nf`) and, for the false-positive side, nothing at all — false
  positives are a *remark* (bandwidth, never correctness), matching
  §4.7.1's treatment; the correctness direction of (iii) holds because the
  index contains nothing but real block records.
- **Proof.** Pure set/list reasoning (`mem_map`, `mem_filter`,
  `mem_flatMap`) plus one hand-rolled list-extensionality lemma; no `omega`,
  no arithmetic.

### Batch envelopes and batching v2 (`OpenCsv/Batch.lean`)

- **Envelope occurrence.** The original paper §4.7.2 model remains: a
  length-tagged `bindHash` chain commits an ordered payload envelope and its
  shared input-0 context. `batch_commit_unique`, `batch_occurrence_iff`,
  `batch_exclusion_sound`, and the coordinator anti-forgery theorems retain
  their previous statements.
- **Fail-closed versioning.** `versionedBatchCommit` gives the literal
  `batch` and `batch-v2` domains distinct outer tags.
  `versioned_commit_no_fallback` proves they cannot be reinterpreted across
  versions; `versioned_commit_unique` fixes ordered payloads and context.
  `batch_v2_exclusion_sound` specializes compact-filter scanning to envelopes
  that recompute under the v2 domain.
- **Frozen C1 transaction.** `ProposalV2`, `ParticipantV2`, and `ManifestV2`
  model the implemented signed-stock/co-funded shape. Input 0 is stock;
  outputs 0/1/2 are header, 546-sat marker, and unchanged stock; each later
  input, payload, charge, and change belongs to the same strictly
  fee-outpoint-ordered participant. `manifest_fixed_positions`,
  `manifest_participant_alignment`, and
  `canonical_adjacent_swap_rejected` make those invariants explicit.
- **C1 admission guards.** `ProposalV2.Valid` rejects zero chain/stock
  identifiers, sub-floor reusable stock, and zero or inverted fee policy.
  `ManifestV2.ParticipantFieldsUnique` rejects duplicate operation IDs,
  payloads, and change scripts while strict outpoint ordering rejects duplicate
  fee inputs. `ManifestV2.ChangeOutputsReusable` enforces the frozen 546-sat
  participant-change floor. `manifest_c1_guards` exposes all three receipts
  from the well-formedness relation without a new axiom.
- **Fees and conservation.** The model separates core manifest validity from
  the current Rust/CLI reference profile's 64-participant resource cap,
  `968 + 423*N` WU formula, ceiling virtual size, miner fee, and exact
  quotient/remainder charge vector. It independently checks that charges sum
  to marker plus miner fee and proves both row-wise and whole-transaction
  conservation in `participant_funding_conservation` and
  `manifest_value_conservation`. The executable `c1_two_party_*` receipts
  reproduce the Rust vectors: 908/1,362-sat miner fees and 727/954-sat
  per-participant charges for the initial/replacement epochs.
- **Replay and replacement.** `ProposalV2.id` commits the domain and complete
  proposal;
  `proposal_id_unique` proves equal IDs imply every chain, stock, participant
  count, nonce, expiry, policy, and context field is equal. A
  `ConformingReplacement` preserves the complete protected layout, header,
  stock principal, participant order, payloads, and scripts; advances one
  epoch; strictly raises feerate/miner fee; moves charges/change only in the
  fee-safe direction; and requires the fresh stock-plus-all-participant signer
  roster. Both endpoints must be well formed, so marker value, exact charge
  allocation, conservation, and fee-policy bounds cannot be bypassed merely by
  satisfying the monotonicity relation.
- **Signer capabilities.** `VerifiedTipReceiptV2` makes maximum receipt age and
  sign-time expiry proof-bearing. `SignerReadinessV2` keeps authoritative
  public-input verification distinct from each signer's own private wallet
  reservation; the model does not pretend one participant can prove another
  participant's private lock.
- **Rust correspondence.** These definitions match `BATCHING_V2.md` and
  `opencsv-bitcoin::batch_v2`; v1/v2 occurrence scanning matches
  `opencsv-core::batch` and `opencsv-cbf`.
- **Assumptions.** No new project axiom. Structural ordering, alignment,
  arithmetic, conservation, and replacement results use only Lean logic.
  Commitment/replay uniqueness reuses the existing `bindHash_injective`;
  coordinator anti-forgery continues to reuse only the existing raw-nullifier
  knowledge assumption.

## Where the cryptographic hardness lives (complete list)

All in `OpenCsv/Interfaces.lean`:

| Assumption | Form | Used by |
|---|---|---|
| `assetId_injective` | collision resistance of the genesis hash | asset binding (stated; the state machine threads `asset_id` directly) |
| `commitHash_injective` | binding of coin commitments | stated for completeness (T3 identifies coins with their openings) |
| `ownerKey_injective` | collision resistance of `owner = H(osk)` | **T3** (`nullifier_unique`) |
| `bindHash_injective` | collision resistance of the anchor binding `P = H(raw_nf, ctx)` in both arguments | **anti-grief / conflict soundness** (`payload_binds_one_nullifier`, `copied_record_not_wellformed`, `griefer_copy_invisible`) |
| `occurrence_requires_knowledge` | preimage resistance of the anchor binding: a fresh well-formed occurrence of `raw_nf` requires knowing `raw_nf` | **anti-grief** (`no_occurrence_without_knowledge`, `unknowing_adversary_entry_invisible`) |
| `sig_unforgeable` | EUF-CMA of the issuer scheme, abstractly | **T1** (`mints_authorized`) |
| `ProofSystem.sound` | soundness of `Π`, as a structure field | **T4** (`receiver_correctness`) |

`propext` / `Quot.sound` appearing in the axiom audit are Lean core axioms,
not assumptions of the development.

## Deliberately NOT mechanized

- **AIR/FRI soundness** — the proof system `Π` appears only through its
  abstract soundness field. Proving FRI sound is a proof-system-level result
  for a dedicated formalization (paper §6).
- **Exact root-circuit commitment authorization** — recursive predecessor keys
  are bound and production acceptance is version-gated, but the native verifier
  still accepts self-described root common data. Distribution and enforcement
  of the exact authorized root-circuit identities remains an explicit security
  boundary; the lineage theorems do not claim it is solved.
- **Poseidon cryptanalysis** — the hash appears only through the injectivity
  (collision-resistance) hypotheses above. No concrete Poseidon, no BabyBear
  field arithmetic.
- **Concrete issuer-seed AIR soundness** — authenticated proof lineages v3/v4
  prove issuer-seed knowledge in-circuit. This model captures the authorization
  property through `SigVerify` / `sig_unforgeable`, but does not prove that the
  concrete Poseidon2/AIR constraints implement that abstraction. Retired
  off-circuit Ed25519 records are historical/read-only, not the modeled target.
- **The hash-compressed multi-input anchor** (`XFERC`, `H(nf_1 ∥ … ∥ nf_m)` in
  `crates/opencsv-core/src/anchor.rs`) — the model's anchor log records
  individual nullifier keys; the compressed variant is an encoding detail of
  the 64-byte budget.
- **The concrete `ctx` derivation of the anti-grief fix** — how the anchoring
  context is computed from the carrying transaction's input side (and why a
  copier cannot reproduce it) is a construction detail; the formalization
  assumes its output abstractly as the hypothesis `ctx' ≠ ctx` in the
  anti-grief theorems.
- **Liveness/finality** — reorgs, censorship, and consignment non-delivery
  (§5.4) are not state-machine properties; only the `k ≤ confs` policy check
  is recorded in `Accept`.
- **Privacy** (§5.3) — hiding/unlinkability are not formalized here; the
  roadmap's item 3 covers the soundness side only.
