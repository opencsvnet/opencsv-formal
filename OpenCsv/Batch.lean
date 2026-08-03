import OpenCsv.Theorems
import OpenCsv.Scan

/-!
# Batch envelopes and co-funded batching v2 (paper §4.7.2)

Anchors may be **batched**: one Bitcoin transaction carries an *envelope* of
`N` payloads in its witness, output 0 holds
`batch_commit = H("batch" ∥ P_1 ∥ … ∥ P_n ∥ ctx)`, and all payloads share the
batch's context. Solo anchors remain valid and unchanged. This module models
envelopes over the existing bound-payload development and proves:

* `batch_commit_unique` — a batch commitment determines its payload list
  (from `bindHash_injective` only; **no new hardness assumption**);
* `batch_occurrence_iff` — the occurrence rule for envelopes
  (commitment recomputes ∧ some payload binds `raw_nf` under the shared ctx);
* `batch_exclusion_sound` — the scan-first exclusion theorem of
  `OpenCsv/Scan.lean` extends to envelope-carrying blocks, by viewing
  envelopes as record-carriers;
* `coordinator_cannot_forge` — a coordinator who sees only payloads cannot
  create a new occurrence of `raw_nf` (reuses
  `occurrence_requires_knowledge`).

The batch commitment is modeled as a **length-tagged `bindHash` chain**: the
outer layer binds the payload count (the model's domain separator for the
`"batch"` tag — it excludes cross-length envelope collisions), and each inner
layer binds one payload onto the running hash, ending at the shared `ctx`.
Every layer is a `bindHash` application, so the existing injectivity axiom is
the only hardness used.

The second half of this module models the frozen C1 batching-v2 transaction:
signed stock is input 0; participant rows are strictly ordered by fee outpoint
and keep fee input, payload, charge, and change aligned; outputs are header,
marker, unchanged stock, then participant changes; marker plus miner fee is
split by the exact quotient/remainder rule; and a replacement preserves every
protocol field while monotonically increasing fees with a fresh unanimous
signer roster.  The model also gives `batch` and `batch-v2` distinct commitment
domains, so a witness cannot fall back across versions.
-/

namespace OpenCsv.Batch

/-- The batch hash chain `H(P_1 ∥ H(P_2 ∥ … H(P_n ∥ ctx)))`: every layer a
`bindHash` application, ending at the shared context. -/
noncomputable def batchChain : List F → AnchorCtx → F
  | [], ctx => ctx
  | P :: Ps, ctx => bindHash P (batchChain Ps ctx)

/-- The batch commitment `H("batch" ∥ P_1 ∥ … ∥ P_n ∥ ctx)`: the chain,
wrapped in an outer `bindHash` layer binding the payload count (the model's
`"batch"` domain separation). -/
noncomputable def batchCommit (Ps : List F) (ctx : AnchorCtx) : F :=
  bindHash Ps.length (batchChain Ps ctx)

/-- A batch envelope: the payloads `P_1 … P_n` (each allegedly
`bindHash(raw_nf_i, ctx)` for some coin), the shared context `ctx` of the
carrying transaction, and the on-chain commitment at output 0. -/
structure Envelope where
  /-- The batched payloads. -/
  payloads : List F
  /-- The batch's shared anchoring context. -/
  ctx : AnchorCtx
  /-- The on-chain `batch_commit`. -/
  commit : F

/-- Envelope validity, checked by the wallet on download: the commitment
recomputes over the envelope's payloads. -/
def Envelope.wellFormed (env : Envelope) : Prop :=
  env.commit = batchCommit env.payloads env.ctx

/-- Payload-level occurrence of `raw_nf` in an envelope (commitment
regardless): some payload binds `raw_nf` under the shared ctx. -/
def EnvelopeOccurrence (env : Envelope) (raw_nf : F) : Prop :=
  ∃ P ∈ env.payloads, (⟨P, env.ctx⟩ : AnchorEntry).wellFormed raw_nf

/-- **Occurrence of `raw_nf` in a batch envelope** (the §4.7.2 rule): the
batch commitment recomputes over the envelope's payloads AND some payload
binds `raw_nf` under the shared ctx. -/
def BatchOccurrence (env : Envelope) (raw_nf : F) : Prop :=
  env.wellFormed ∧ EnvelopeOccurrence env raw_nf

/-! ## Commitment uniqueness -/

/-- The chain is injective on equal-length payload lists (straight induction
on `bindHash_injective`). -/
theorem batch_chain_unique {Ps Qs : List F} {ctx ctx' : AnchorCtx}
    (hlen : Ps.length = Qs.length)
    (h : batchChain Ps ctx = batchChain Qs ctx') : Ps = Qs ∧ ctx = ctx' := by
  induction Ps generalizing Qs ctx ctx' with
  | nil =>
    cases Qs with
    | nil => exact ⟨rfl, h⟩
    | cons q qs => simp at hlen
  | cons p ps ih =>
    cases Qs with
    | nil => simp at hlen
    | cons q qs =>
      simp only [List.length_cons] at hlen
      replace hlen : ps.length = qs.length := by omega
      simp only [batchChain] at h
      obtain ⟨hpq, hchain⟩ := bindHash_injective _ _ _ _ h
      obtain ⟨hps, hctx⟩ := ih hlen hchain
      subst hpq; subst hps; subst hctx; exact ⟨rfl, rfl⟩

/-- **Batch commitment uniqueness.** A batch commitment determines its
payload list (and context): two envelopes with equal `batch_commit` are the
same envelope. This is what makes tampering with the envelope detectable —
and it uses only the pre-existing collision resistance of `bindHash`. -/
theorem batch_commit_unique {Ps Qs : List F} {ctx ctx' : AnchorCtx}
    (h : batchCommit Ps ctx = batchCommit Qs ctx') : Ps = Qs ∧ ctx = ctx' := by
  simp only [batchCommit] at h
  obtain ⟨hlen, hchain⟩ := bindHash_injective _ _ _ _ h
  exact batch_chain_unique hlen hchain

/-- **The batch occurrence rule, as a bridge.** An occurrence of `raw_nf`
exists in a batch envelope iff the commitment recomputes over the envelope's
payloads and some payload binds `raw_nf` under the shared ctx. -/
theorem batch_occurrence_iff (env : Envelope) (raw_nf : F) :
    BatchOccurrence env raw_nf ↔
      env.commit = batchCommit env.payloads env.ctx ∧
        ∃ P ∈ env.payloads, (⟨P, env.ctx⟩ : AnchorEntry).wellFormed raw_nf :=
  Iff.rfl

/-! ## Frozen co-funded batching v2 semantics (C1/C3) -/

/-- Fail-closed witness/header commitment version. -/
inductive BatchVersion where
  /-- Legacy `OCSV` / `batch` domain. -/
  | v1
  /-- Signed co-funded `OCS2` / `batch-v2` domain. -/
  | v2
  deriving DecidableEq

/-- Abstract field tags for the two literal commitment domains. -/
def versionTag : BatchVersion → F
  | .v1 => 1
  | .v2 => 2

/-- Versioned batch commitment.  The outer hash binds the literal domain,
the next layer binds the payload count, and `batchChain` binds the ordered
payloads and transaction context. -/
noncomputable def versionedBatchCommit (version : BatchVersion)
    (Ps : List F) (ctx : AnchorCtx) : F :=
  bindHash (versionTag version) (bindHash Ps.length (batchChain Ps ctx))

/-- The exact C1 `batch-v2` commitment domain. -/
noncomputable def batchCommitV2 (Ps : List F) (ctx : AnchorCtx) : F :=
  versionedBatchCommit .v2 Ps ctx

/-- **No version fallback.** Collision resistance makes the two explicit
domain tags disjoint, regardless of payloads or context. -/
theorem versioned_commit_no_fallback (Ps Qs : List F) (ctx ctx' : AnchorCtx) :
    versionedBatchCommit .v1 Ps ctx ≠ versionedBatchCommit .v2 Qs ctx' := by
  intro h
  have htag := (bindHash_injective _ _ _ _ h).1
  simp [versionTag] at htag

/-- Within one selected version, a header fixes the full ordered payload list
and transaction context. -/
theorem versioned_commit_unique {version : BatchVersion} {Ps Qs : List F}
    {ctx ctx' : AnchorCtx}
    (h : versionedBatchCommit version Ps ctx =
      versionedBatchCommit version Qs ctx') : Ps = Qs ∧ ctx = ctx' := by
  simp only [versionedBatchCommit] at h
  obtain ⟨_htag, hbody⟩ := bindHash_injective _ _ _ _ h
  obtain ⟨hlen, hchain⟩ := bindHash_injective _ _ _ _ hbody
  exact batch_chain_unique hlen hchain

/-- V2 envelope validity under the `batch-v2` domain. -/
def Envelope.wellFormedV2 (env : Envelope) : Prop :=
  env.commit = batchCommitV2 env.payloads env.ctx

/-- V2 occurrence: the versioned header recomputes and one ordered payload
binds the supplied raw nullifier under input 0's context. -/
def BatchOccurrenceV2 (env : Envelope) (raw_nf : F) : Prop :=
  env.wellFormedV2 ∧ EnvelopeOccurrence env raw_nf

/-- Bridge theorem for the concrete v2 occurrence rule. -/
theorem batch_v2_occurrence_iff (env : Envelope) (raw_nf : F) :
    BatchOccurrenceV2 env raw_nf ↔
      env.commit = batchCommitV2 env.payloads env.ctx ∧
        ∃ P ∈ env.payloads, (⟨P, env.ctx⟩ : AnchorEntry).wellFormed raw_nf :=
  Iff.rfl

/-- Proposal fields fixed before participant commitments are collected.  The
stock script is derived by the implementation from `stockOwner` and
`participantCount`; the formal model records the resulting script explicitly
so the unchanged-principal/output theorem can mention it. -/
structure ProposalV2 where
  chainId : F
  stockInput : F
  stockValue : Nat
  stockOwner : F
  stockScript : F
  participantCount : Nat
  proposalNonce : F
  observedTip : Nat
  expiryHeight : Nat
  targetFeerate : Nat
  maxFeerate : Nat
  ctx : AnchorCtx
  deriving DecidableEq

/-- A participant's fields that signatures protect across fee replacement. -/
structure ProtectedParticipant where
  operationId : F
  feeInput : F
  feeOwner : F
  feeValue : Nat
  payload : F
  changeScript : F
  maxCharge : Nat
  deriving DecidableEq

/-- One canonically ordered participant row.  `charge` and `changeValue` are
the only row values a conforming replacement may change. -/
structure ParticipantV2 extends ProtectedParticipant where
  charge : Nat
  changeValue : Nat
  deriving DecidableEq

/-- Projection of the fields protected across replacement epochs. -/
def ParticipantV2.protected (p : ParticipantV2) : ProtectedParticipant :=
  p.toProtectedParticipant

/-- Canonical participant order is strict lexicographic fee-outpoint order
(outpoints are abstracted as natural-number identifiers). -/
def CanonicalParticipants (participants : List ParticipantV2) : Prop :=
  participants.Pairwise fun left right => left.feeInput < right.feeInput

/-- A canonical list cannot also accept an adjacent transposition.  This is
the formal coordinator-order-mutation rejection used by C1 signers. -/
theorem canonical_adjacent_swap_rejected {left right : ParticipantV2}
    {rest : List ParticipantV2}
    (h : CanonicalParticipants (left :: right :: rest)) :
    ¬ CanonicalParticipants (right :: left :: rest) := by
  intro hswap
  simp only [CanonicalParticipants, List.pairwise_cons] at h hswap
  have hlr : left.feeInput < right.feeInput :=
    h.1 right (List.mem_cons_self right rest)
  have hrl : right.feeInput < left.feeInput :=
    hswap.1 left (List.mem_cons_self left rest)
  exact (Nat.not_lt_of_ge (Nat.le_of_lt hrl)) hlr

/-- Exact C1 quotient/remainder charge for participant index `index`. -/
def allocatedCharge (total count index : Nat) : Nat :=
  total / count + if index < total % count then 1 else 0

/-- Exact ordered charge vector.  The first `total % count` canonical
participants pay one satoshi more than the remaining participants. -/
def exactCharges (total count : Nat) : List Nat :=
  (List.range count).map (allocatedCharge total count)

theorem exact_charges_length (total count : Nat) :
    (exactCharges total count).length = count := by
  simp [exactCharges]

theorem allocated_charge_high {total count index : Nat}
    (h : index < total % count) :
    allocatedCharge total count index = total / count + 1 := by
  simp [allocatedCharge, h]

theorem allocated_charge_base {total count index : Nat}
    (h : ¬ index < total % count) :
    allocatedCharge total count index = total / count := by
  simp [allocatedCharge, h]

/-- Frozen pessimistic signed weight `968 + 423*N` WU. -/
def maxSignedWeight (participantCount : Nat) : Nat :=
  968 + 423 * participantCount

/-- Frozen pessimistic virtual size `ceil(weight / 4)`. -/
def maxSignedVBytes (participantCount : Nat) : Nat :=
  (maxSignedWeight participantCount + 3) / 4

/-- The protocol cap has the exact reviewed 28,040-WU bound. -/
theorem max_signed_weight_at_cap : maxSignedWeight 64 = 28040 := by
  rfl

/-- Sum a natural-valued projection without importing mathlib. -/
def sumBy {α : Type} (f : α → Nat) : List α → Nat
  | [] => 0
  | value :: rest => f value + sumBy f rest

/-- Each participant funds exactly its charge plus its own change and stays
inside its signed maximum charge. -/
def ParticipantV2.funded (p : ParticipantV2) : Prop :=
  p.charge ≤ p.maxCharge ∧ p.feeValue = p.charge + p.changeValue

/-- Transaction inputs.  The stock outpoint is position 0; fee inputs follow
the canonical participant list one-for-one. -/
inductive BatchInputV2 where
  | stock (outpoint : F)
  | fee (outpoint : F)
  deriving DecidableEq

/-- Transaction outputs.  Positions 0, 1, and 2 are protocol-fixed; change
outputs begin at 3 in canonical participant order. -/
inductive BatchOutputV2 where
  | header (commit : F)
  | marker (value : Nat)
  | stockReturn (value : Nat) (script : F)
  | change (value : Nat) (script : F)
  deriving DecidableEq

/-- Canonical v2 manifest.  `signers` models the authorization roster, not
the ECDSA primitive: cryptographic signature validity remains a Bitcoin-layer
obligation and introduces no new Lean axiom. -/
structure ManifestV2 where
  proposal : ProposalV2
  participants : List ParticipantV2
  markerValue : Nat
  minerFee : Nat
  feerate : Nat
  replacementEpoch : Nat
  signers : List F
  deriving DecidableEq

/-- Protected participant rows in transaction order. -/
def ManifestV2.protectedParticipants (manifest : ManifestV2) :
    List ProtectedParticipant :=
  manifest.participants.map ParticipantV2.protected

/-- Ordered v2 payload envelope. -/
def ManifestV2.payloads (manifest : ManifestV2) : List F :=
  manifest.protectedParticipants.map ProtectedParticipant.payload

/-- Ordered v2 header commitment. -/
noncomputable def ManifestV2.headerCommit (manifest : ManifestV2) : F :=
  batchCommitV2 manifest.payloads manifest.proposal.ctx

/-- Exact stock-first input vector. -/
def ManifestV2.inputs (manifest : ManifestV2) : List BatchInputV2 :=
  .stock manifest.proposal.stockInput ::
    manifest.protectedParticipants.map
      (fun participant => .fee participant.feeInput)

/-- Exact header/marker/stock/change output vector. -/
noncomputable def ManifestV2.outputs (manifest : ManifestV2) : List BatchOutputV2 :=
  .header manifest.headerCommit ::
  .marker manifest.markerValue ::
  .stockReturn manifest.proposal.stockValue manifest.proposal.stockScript ::
    manifest.participants.map
      (fun participant => .change participant.changeValue participant.changeScript)

/-- Every replacement signature is required: stock owner first, then every
participant fee owner in canonical order. -/
def ManifestV2.Unanimous (manifest : ManifestV2) : Prop :=
  manifest.signers = manifest.proposal.stockOwner ::
    manifest.protectedParticipants.map ProtectedParticipant.feeOwner

/-- Complete deterministic C1 validity relation.  The charge-vector equality
freezes the quotient/remainder algorithm; the sum equality independently
checks conservation against marker plus miner fee. -/
def ManifestV2.WellFormed (manifest : ManifestV2) : Prop :=
  0 < manifest.proposal.participantCount ∧
  manifest.proposal.participantCount ≤ 64 ∧
  manifest.proposal.participantCount = manifest.participants.length ∧
  CanonicalParticipants manifest.participants ∧
  manifest.participants.map ParticipantV2.charge =
    exactCharges (manifest.markerValue + manifest.minerFee)
      manifest.proposal.participantCount ∧
  sumBy ParticipantV2.charge manifest.participants =
    manifest.markerValue + manifest.minerFee ∧
  (∀ participant ∈ manifest.participants, participant.funded) ∧
  manifest.markerValue = 546 ∧
  manifest.minerFee = manifest.feerate *
    maxSignedVBytes manifest.proposal.participantCount ∧
  manifest.proposal.observedTip < manifest.proposal.expiryHeight ∧
  manifest.proposal.targetFeerate ≤ manifest.feerate ∧
  manifest.feerate ≤ manifest.proposal.maxFeerate ∧
  manifest.Unanimous

/-- Fixed protocol positions, including unchanged stock value and script. -/
theorem manifest_fixed_positions (manifest : ManifestV2) :
    manifest.inputs.get? 0 = some (.stock manifest.proposal.stockInput) ∧
    manifest.outputs.get? 0 = some (.header manifest.headerCommit) ∧
    manifest.outputs.get? 1 = some (.marker manifest.markerValue) ∧
    manifest.outputs.get? 2 = some
      (.stockReturn manifest.proposal.stockValue manifest.proposal.stockScript) := by
  simp [ManifestV2.inputs, ManifestV2.outputs]

/-- Input/payload/change all select the same participant at every index. -/
theorem manifest_participant_alignment (manifest : ManifestV2) (index : Nat) :
    manifest.inputs.get? (index + 1) =
        Option.map (fun participant => .fee participant.feeInput)
          (manifest.protectedParticipants.get? index) ∧
    manifest.payloads.get? index =
        Option.map ProtectedParticipant.payload
          (manifest.protectedParticipants.get? index) ∧
    manifest.outputs.get? (index + 3) =
        Option.map
          (fun participant =>
            BatchOutputV2.change participant.changeValue participant.changeScript)
          (manifest.participants.get? index) := by
  simp [ManifestV2.inputs, ManifestV2.payloads, ManifestV2.outputs,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The derived vectors have exactly the fixed C1 cardinalities. -/
theorem manifest_vector_lengths (manifest : ManifestV2) :
    manifest.inputs.length = manifest.participants.length + 1 ∧
    manifest.payloads.length = manifest.participants.length ∧
    manifest.outputs.length = manifest.participants.length + 3 := by
  simp [ManifestV2.inputs, ManifestV2.payloads, ManifestV2.outputs,
    ManifestV2.protectedParticipants]

/-- Row-wise fee conservation lifts to the whole participant vector. -/
theorem participant_funding_conservation (participants : List ParticipantV2)
    (hfunded : ∀ participant ∈ participants, participant.funded) :
    sumBy (fun participant => participant.feeValue) participants =
      sumBy (fun participant => participant.charge) participants +
        sumBy (fun participant => participant.changeValue) participants := by
  induction participants with
  | nil => rfl
  | cons participant rest ih =>
      have hhead := hfunded participant (List.mem_cons_self participant rest)
      have hrest : ∀ p ∈ rest, p.funded := by
        intro p hp
        exact hfunded p (List.mem_cons_of_mem participant hp)
      have htail := ih hrest
      simp only [sumBy]
      rw [hhead.2, htail]
      omega

/-- **Whole-transaction conservation.** Input-0 principal returns unchanged;
participant inputs fund only marker, miner fee, and their aligned changes. -/
theorem manifest_value_conservation (manifest : ManifestV2)
    (hvalid : manifest.WellFormed) :
    manifest.proposal.stockValue +
        sumBy (fun participant => participant.feeValue) manifest.participants =
      manifest.proposal.stockValue + manifest.markerValue + manifest.minerFee +
        sumBy (fun participant => participant.changeValue) manifest.participants := by
  rcases hvalid with
    ⟨_hpositive, _hcap, _hcount, _hcanonical, _hexact, hcharges,
      hfunded, _hmarker, _hfee, _hexpiry, _htarget, _hmax, _hunanimous⟩
  have hrows := participant_funding_conservation manifest.participants hfunded
  rw [hrows, hcharges]
  omega

/-- The proposal identifier binds chain, stock, policy, nonce, and context.
It is an abstract nested transcript hash mirroring the Rust canonical body. -/
noncomputable def ProposalV2.id (proposal : ProposalV2) : F :=
  bindHash proposal.chainId
    (bindHash proposal.stockInput
      (bindHash proposal.stockValue
        (bindHash proposal.stockOwner
          (bindHash proposal.stockScript
            (bindHash proposal.participantCount
              (bindHash proposal.proposalNonce
                (bindHash proposal.observedTip
                  (bindHash proposal.expiryHeight
                    (bindHash proposal.targetFeerate
                      (bindHash proposal.maxFeerate proposal.ctx))))))))))

/-- Cross-chain replay would require a collision in the proposal transcript. -/
theorem proposal_id_binds_chain {left right : ProposalV2}
    (h : left.id = right.id) : left.chainId = right.chainId :=
  (bindHash_injective _ _ _ _ h).1

/-- The complete proposal transcript is injective: equal identifiers imply
equal network, stock, membership, expiry, fee policy, nonce, and context. -/
theorem proposal_id_unique {left right : ProposalV2}
    (h : left.id = right.id) : left = right := by
  simp only [ProposalV2.id] at h
  obtain ⟨hchain, h⟩ := bindHash_injective _ _ _ _ h
  obtain ⟨hstock, h⟩ := bindHash_injective _ _ _ _ h
  obtain ⟨hvalue, h⟩ := bindHash_injective _ _ _ _ h
  obtain ⟨howner, h⟩ := bindHash_injective _ _ _ _ h
  obtain ⟨hscript, h⟩ := bindHash_injective _ _ _ _ h
  obtain ⟨hcount, h⟩ := bindHash_injective _ _ _ _ h
  obtain ⟨hnonce, h⟩ := bindHash_injective _ _ _ _ h
  obtain ⟨htip, h⟩ := bindHash_injective _ _ _ _ h
  obtain ⟨hexpiry, h⟩ := bindHash_injective _ _ _ _ h
  obtain ⟨htarget, h⟩ := bindHash_injective _ _ _ _ h
  obtain ⟨hmax, hctx⟩ := bindHash_injective _ _ _ _ h
  cases left
  cases right
  simp_all

/-- Values permitted to change between replacement epochs move only in the
fee-safe direction at every canonical participant position. -/
def replacementFeesMonotone : List ParticipantV2 → List ParticipantV2 → Prop
  | [], [] => True
  | old :: olds, new :: news =>
      old.charge ≤ new.charge ∧ new.changeValue ≤ old.changeValue ∧
        replacementFeesMonotone olds news
  | _, _ => False

/-- Protected-layout fingerprint: exact proposal plus ordered participant
commitments.  Charges, change values, epoch, and signatures are excluded. -/
def ManifestV2.protectedLayout (manifest : ManifestV2) :
    ProposalV2 × List ProtectedParticipant :=
  (manifest.proposal, manifest.protectedParticipants)

/-- Frozen C1 unanimous replacement relation. -/
def ConformingReplacement (old new : ManifestV2) : Prop :=
  old.protectedLayout = new.protectedLayout ∧
  new.replacementEpoch = old.replacementEpoch + 1 ∧
  old.feerate < new.feerate ∧
  old.minerFee < new.minerFee ∧
  replacementFeesMonotone old.participants new.participants ∧
  new.Unanimous

/-- A conforming replacement preserves the header/input/output layout data,
including stock principal, participant order, payloads, and scripts. -/
theorem replacement_preserves_protected_layout {old new : ManifestV2}
    (h : ConformingReplacement old new) :
    old.protectedLayout = new.protectedLayout :=
  h.1

/-- Header commitment is invariant across a conforming replacement. -/
theorem replacement_preserves_header {old new : ManifestV2}
    (h : ConformingReplacement old new) :
    old.headerCommit = new.headerCommit := by
  have hlayout := h.1
  have hproposal : old.proposal = new.proposal := congrArg Prod.fst hlayout
  have hparticipants : old.protectedParticipants = new.protectedParticipants :=
    congrArg Prod.snd hlayout
  simp only [ManifestV2.headerCommit, ManifestV2.payloads]
  rw [hproposal, hparticipants]

/-- Stock principal and its signed return script are replacement invariants. -/
theorem replacement_preserves_stock {old new : ManifestV2}
    (h : ConformingReplacement old new) :
    old.proposal.stockValue = new.proposal.stockValue ∧
      old.proposal.stockScript = new.proposal.stockScript := by
  have hlayout := h.1
  exact
    ⟨congrArg (fun layout => layout.1.stockValue) hlayout,
      congrArg (fun layout => layout.1.stockScript) hlayout⟩

/-- A conforming replacement is epoch- and fee-monotone. -/
theorem replacement_monotone {old new : ManifestV2}
    (h : ConformingReplacement old new) :
    new.replacementEpoch = old.replacementEpoch + 1 ∧
      old.feerate < new.feerate ∧ old.minerFee < new.minerFee :=
  ⟨h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- No unilateral fee bump: the replacement relation requires the complete
stock-plus-participant signer roster for the new manifest. -/
theorem replacement_requires_unanimity {old new : ManifestV2}
    (h : ConformingReplacement old new) : new.Unanimous :=
  h.2.2.2.2.2

/-! ## Executable two-participant C1 receipt -/

/-- Concrete proposal matching the C1 two-participant fee geometry. -/
def c1TwoPartyProposal : ProposalV2 :=
  { chainId := 1
    stockInput := 2
    stockValue := 100000
    stockOwner := 90
    stockScript := 91
    participantCount := 2
    proposalNonce := 3
    observedTip := 100
    expiryHeight := 120
    targetFeerate := 2
    maxFeerate := 10
    ctx := 4 }

/-- Build one concrete funded row for the executable receipt. -/
def c1Participant (operationId feeInput feeOwner payload changeScript charge : Nat) :
    ParticipantV2 :=
  { operationId := operationId
    feeInput := feeInput
    feeOwner := feeOwner
    feeValue := 20000
    payload := payload
    changeScript := changeScript
    maxCharge := 10000
    charge := charge
    changeValue := 20000 - charge }

/-- At 2 sat/vB, 1,814 WU rounds to 454 vB and a 908-sat miner fee;
marker plus fee splits into two 727-sat charges. -/
def c1TwoPartyInitial : ManifestV2 :=
  { proposal := c1TwoPartyProposal
    participants :=
      [c1Participant 1 10 11 31 41 727,
       c1Participant 2 20 22 32 42 727]
    markerValue := 546
    minerFee := 908
    feerate := 2
    replacementEpoch := 0
    signers := [90, 11, 22] }

/-- At 3 sat/vB the same layout pays 1,362 sats to miners and splits marker
plus fee into two 954-sat charges. -/
def c1TwoPartyReplacement : ManifestV2 :=
  { proposal := c1TwoPartyProposal
    participants :=
      [c1Participant 1 10 11 31 41 954,
       c1Participant 2 20 22 32 42 954]
    markerValue := 546
    minerFee := 1362
    feerate := 3
    replacementEpoch := 1
    signers := [90, 11, 22] }

theorem c1_two_party_initial_valid : c1TwoPartyInitial.WellFormed := by
  simp [c1TwoPartyInitial, c1TwoPartyProposal, c1Participant,
    ManifestV2.WellFormed, CanonicalParticipants, ParticipantV2.funded,
    exactCharges, allocatedCharge, maxSignedVBytes, maxSignedWeight, sumBy,
    ManifestV2.Unanimous, ManifestV2.protectedParticipants,
    ParticipantV2.protected]
  decide

theorem c1_two_party_replacement_valid : c1TwoPartyReplacement.WellFormed := by
  simp [c1TwoPartyReplacement, c1TwoPartyProposal, c1Participant,
    ManifestV2.WellFormed, CanonicalParticipants, ParticipantV2.funded,
    exactCharges, allocatedCharge, maxSignedVBytes, maxSignedWeight, sumBy,
    ManifestV2.Unanimous, ManifestV2.protectedParticipants,
    ParticipantV2.protected]
  decide

theorem c1_two_party_replacement_conforms :
    ConformingReplacement c1TwoPartyInitial c1TwoPartyReplacement := by
  simp [ConformingReplacement, c1TwoPartyInitial, c1TwoPartyReplacement,
    c1TwoPartyProposal, c1Participant, ManifestV2.protectedLayout,
    ManifestV2.protectedParticipants, ParticipantV2.protected,
    replacementFeesMonotone, ManifestV2.Unanimous]

/-! ## Envelopes as record-carriers: batch exclusion soundness -/

/-- Envelopes as record-carriers: an envelope contributes one anchor entry
per payload, all under its shared ctx. -/
def envelopeRecords (env : Envelope) : List AnchorEntry :=
  env.payloads.map fun P => ⟨P, env.ctx⟩

/-- Expand one block by the envelopes it carries: its effective records are
its solo records plus every envelope's payload entries. -/
def expandBlock (envs : Scan.Block → List Envelope) (blk : Scan.Block) : Scan.Block :=
  { blk with records := blk.records ++ (envs blk).flatMap envelopeRecords }

theorem expandBlock_records (envs : Scan.Block → List Envelope) (blk : Scan.Block) :
    (expandBlock envs blk).records
      = blk.records ++ (envs blk).flatMap envelopeRecords := rfl

theorem expandBlock_scripts (envs : Scan.Block → List Envelope) (blk : Scan.Block) :
    (expandBlock envs blk).scripts = blk.scripts := rfl

/-- Expand a whole window. -/
def expandWindow (envs : Scan.Block → List Envelope) (window : List Scan.Block) :
    List Scan.Block := window.map (expandBlock envs)

/-- Occurrences over the expanded window are exactly solo occurrences plus
batch occurrences in the original window. (`hvalid`: the wallet only indexes
envelopes whose commitment recomputes — checked on download — so every
payload occurrence in the index comes from a well-formed envelope; this is
where `batch_occurrence_iff` enters.) -/
theorem chainOccurrence_expandWindow (envs : Scan.Block → List Envelope)
    (window : List Scan.Block) (raw_nf : F)
    (hvalid : ∀ blk ∈ window, ∀ env ∈ envs blk, env.wellFormed) :
    Scan.ChainOccurrence (expandWindow envs window) raw_nf ↔
      Scan.ChainOccurrence window raw_nf ∨
        ∃ blk ∈ window, ∃ env ∈ envs blk, BatchOccurrence env raw_nf := by
  constructor
  · rintro ⟨blk', hblk', e, he, hwf⟩
    obtain ⟨blk, hblk, hrfl⟩ := List.mem_map.mp hblk'
    subst hrfl
    rw [expandBlock_records, List.mem_append] at he
    rcases he with he | he
    · exact Or.inl ⟨blk, hblk, e, he, hwf⟩
    · rw [List.mem_flatMap] at he
      obtain ⟨env, henv, he⟩ := he
      rw [envelopeRecords, List.mem_map] at he
      obtain ⟨P, hP, hrfl2⟩ := he
      subst hrfl2
      exact Or.inr ⟨blk, hblk, env, henv, hvalid blk hblk env henv, P, hP, hwf⟩
  · rintro (⟨blk, hblk, e, he, hwf⟩ | ⟨blk, hblk, env, henv, _hwfenv, P, hP, hwf⟩)
    · refine ⟨expandBlock envs blk, List.mem_map.mpr ⟨blk, hblk, rfl⟩, e, ?_, hwf⟩
      rw [expandBlock_records, List.mem_append]
      exact Or.inl he
    · refine ⟨expandBlock envs blk, List.mem_map.mpr ⟨blk, hblk, rfl⟩,
        ⟨P, env.ctx⟩, ?_, hwf⟩
      rw [expandBlock_records, List.mem_append]
      exact Or.inr (List.mem_flatMap.mpr ⟨env, henv, List.mem_map.mpr ⟨P, hP, rfl⟩⟩)

/-- V2 specialization of the record-carrier expansion: only envelopes whose
header recomputes under `batch-v2` contribute batch occurrences. -/
theorem chainOccurrence_expandWindow_v2 (envs : Scan.Block → List Envelope)
    (window : List Scan.Block) (raw_nf : F)
    (hvalid : ∀ blk ∈ window, ∀ env ∈ envs blk, env.wellFormedV2) :
    Scan.ChainOccurrence (expandWindow envs window) raw_nf ↔
      Scan.ChainOccurrence window raw_nf ∨
        ∃ blk ∈ window, ∃ env ∈ envs blk, BatchOccurrenceV2 env raw_nf := by
  constructor
  · rintro ⟨blk', hblk', e, he, hwf⟩
    obtain ⟨blk, hblk, hrfl⟩ := List.mem_map.mp hblk'
    subst hrfl
    rw [expandBlock_records, List.mem_append] at he
    rcases he with he | he
    · exact Or.inl ⟨blk, hblk, e, he, hwf⟩
    · rw [List.mem_flatMap] at he
      obtain ⟨env, henv, he⟩ := he
      rw [envelopeRecords, List.mem_map] at he
      obtain ⟨P, hP, hrfl2⟩ := he
      subst hrfl2
      exact Or.inr ⟨blk, hblk, env, henv, hvalid blk hblk env henv, P, hP, hwf⟩
  · rintro (⟨blk, hblk, e, he, hwf⟩ | ⟨blk, hblk, env, henv, _hwfenv, P, hP, hwf⟩)
    · refine ⟨expandBlock envs blk, List.mem_map.mpr ⟨blk, hblk, rfl⟩, e, ?_, hwf⟩
      rw [expandBlock_records, List.mem_append]
      exact Or.inl he
    · refine ⟨expandBlock envs blk, List.mem_map.mpr ⟨blk, hblk, rfl⟩,
        ⟨P, env.ctx⟩, ?_, hwf⟩
      rw [expandBlock_records, List.mem_append]
      exact Or.inr (List.mem_flatMap.mpr ⟨env, henv, List.mem_map.mpr ⟨P, hP, rfl⟩⟩)

/-- **Batch exclusion soundness.** The scan-first exclusion result extends
to batched anchors: a local scan over candidate blocks that reads envelope
payloads finds an occurrence of `raw_nf` in the window iff one exists
on-chain in the window — as a solo record or inside a batch envelope. This
is `Scan.scan_exclusion_sound` applied to the record-carrier expansion;
the marking hypotheses are the same deployment invariant, once for solo
records and once for envelopes. -/
theorem batch_exclusion_sound (filterItem : Scan.Script → Scan.Script) (marker : Scan.Script)
    (envs : Scan.Block → List Envelope) (window : List Scan.Block) (raw_nf : F)
    (hvalid : ∀ blk ∈ window, ∀ env ∈ envs blk, env.wellFormed)
    (hmarkedSolo : ∀ blk ∈ window, (∃ e ∈ blk.records, e.wellFormed raw_nf) →
      marker ∈ blk.scripts)
    (hmarkedBatch : ∀ blk ∈ window,
      (∃ env ∈ envs blk, EnvelopeOccurrence env raw_nf) → marker ∈ blk.scripts) :
    Scan.ScanFinds (Scan.indexOf filterItem marker (expandWindow envs window)) raw_nf ↔
      Scan.ChainOccurrence window raw_nf ∨
        ∃ blk ∈ window, ∃ env ∈ envs blk, BatchOccurrence env raw_nf := by
  -- Marking lifts to the expanded window: an occurrence in an expanded
  -- block is a solo or an envelope occurrence of the underlying block.
  have hmarkedExp : ∀ blk' ∈ expandWindow envs window,
      (∃ e ∈ blk'.records, e.wellFormed raw_nf) → marker ∈ blk'.scripts := by
    intro blk' hblk' hocc
    obtain ⟨blk, hblk, hrfl⟩ := List.mem_map.mp hblk'
    subst hrfl
    rw [expandBlock_scripts]
    obtain ⟨e, he, hwf⟩ := hocc
    rw [expandBlock_records, List.mem_append] at he
    rcases he with he | he
    · exact hmarkedSolo blk hblk ⟨e, he, hwf⟩
    · rw [List.mem_flatMap] at he
      obtain ⟨env, henv, he⟩ := he
      rw [envelopeRecords, List.mem_map] at he
      obtain ⟨P, hP, hrfl2⟩ := he
      subst hrfl2
      exact hmarkedBatch blk hblk ⟨env, henv, P, hP, hwf⟩
  have hscan := Scan.scan_exclusion_sound filterItem marker
    (expandWindow envs window) raw_nf hmarkedExp
  rw [chainOccurrence_expandWindow envs window raw_nf hvalid] at hscan
  exact hscan

/-- **Batching-v2 exclusion soundness.** Compact-filter discovery plus local
`OCS2`/`batch-v2` validation finds exactly the solo or v2 occurrences in the
window.  A legacy-domain header cannot enter this theorem because `hvalid`
requires `wellFormedV2`. -/
theorem batch_v2_exclusion_sound (filterItem : Scan.Script → Scan.Script)
    (marker : Scan.Script) (envs : Scan.Block → List Envelope)
    (window : List Scan.Block) (raw_nf : F)
    (hvalid : ∀ blk ∈ window, ∀ env ∈ envs blk, env.wellFormedV2)
    (hmarkedSolo : ∀ blk ∈ window, (∃ e ∈ blk.records, e.wellFormed raw_nf) →
      marker ∈ blk.scripts)
    (hmarkedBatch : ∀ blk ∈ window,
      (∃ env ∈ envs blk, EnvelopeOccurrence env raw_nf) → marker ∈ blk.scripts) :
    Scan.ScanFinds (Scan.indexOf filterItem marker (expandWindow envs window)) raw_nf ↔
      Scan.ChainOccurrence window raw_nf ∨
        ∃ blk ∈ window, ∃ env ∈ envs blk, BatchOccurrenceV2 env raw_nf := by
  have hmarkedExp : ∀ blk' ∈ expandWindow envs window,
      (∃ e ∈ blk'.records, e.wellFormed raw_nf) → marker ∈ blk'.scripts := by
    intro blk' hblk' hocc
    obtain ⟨blk, hblk, hrfl⟩ := List.mem_map.mp hblk'
    subst hrfl
    rw [expandBlock_scripts]
    obtain ⟨e, he, hwf⟩ := hocc
    rw [expandBlock_records, List.mem_append] at he
    rcases he with he | he
    · exact hmarkedSolo blk hblk ⟨e, he, hwf⟩
    · rw [List.mem_flatMap] at he
      obtain ⟨env, henv, he⟩ := he
      rw [envelopeRecords, List.mem_map] at he
      obtain ⟨P, hP, hrfl2⟩ := he
      subst hrfl2
      exact hmarkedBatch blk hblk ⟨env, henv, P, hP, hwf⟩
  have hscan := Scan.scan_exclusion_sound filterItem marker
    (expandWindow envs window) raw_nf hmarkedExp
  rw [chainOccurrence_expandWindow_v2 envs window raw_nf hvalid] at hscan
  exact hscan

/-! ## The coordinator cannot forge -/

/-- **The batching coordinator cannot forge occurrences.** A coordinator
sees only the envelope payloads — not `raw_nf`. By preimage resistance
(`occurrence_requires_knowledge`, reused unchanged), any anchor entry with a
context fresh w.r.t. the log that is well-formed for `raw_nf` would witness
knowledge of `raw_nf`; a coordinator who does not know it therefore cannot
produce one, whether as a solo record or as an envelope payload under a
fresh batch context. (Participant-authored payloads are outside this
statement by design: the participant knows `raw_nf` — that is precisely the
knowledge the axiom ties the fresh well-formed entry to — and the
coordinator merely envelopes their payloads.) -/
theorem coordinator_cannot_forge {log : List AnchorEntry} {raw_nf : F}
    (hk : ¬ KnowsRawNf log raw_nf) (e : AnchorEntry)
    (hfresh : ∀ e' ∈ log, e'.ctx ≠ e.ctx) :
    ¬ e.wellFormed raw_nf :=
  OpenCsv.no_occurrence_without_knowledge hk hfresh

/-- Envelope form: a coordinator-produced envelope under a fresh batch
context contains no payload binding `raw_nf` (same scope note as above). -/
theorem coordinator_envelope_no_occurrence {log : List AnchorEntry} {raw_nf : F}
    (hk : ¬ KnowsRawNf log raw_nf) (env : Envelope)
    (hfresh : ∀ e ∈ log, e.ctx ≠ env.ctx) :
    ¬ EnvelopeOccurrence env raw_nf := by
  rintro ⟨P, _hP, hwf⟩
  exact coordinator_cannot_forge hk ⟨P, env.ctx⟩ (fun e' he' => hfresh e' he') hwf

/-! ## Axiom audit -/

#print axioms batch_commit_unique
#print axioms batch_occurrence_iff
#print axioms versioned_commit_no_fallback
#print axioms versioned_commit_unique
#print axioms batch_v2_occurrence_iff
#print axioms canonical_adjacent_swap_rejected
#print axioms allocated_charge_high
#print axioms allocated_charge_base
#print axioms max_signed_weight_at_cap
#print axioms manifest_fixed_positions
#print axioms manifest_participant_alignment
#print axioms manifest_vector_lengths
#print axioms participant_funding_conservation
#print axioms manifest_value_conservation
#print axioms proposal_id_unique
#print axioms chainOccurrence_expandWindow_v2
#print axioms batch_v2_exclusion_sound
#print axioms replacement_preserves_header
#print axioms replacement_preserves_stock
#print axioms replacement_monotone
#print axioms replacement_requires_unanimity
#print axioms c1_two_party_initial_valid
#print axioms c1_two_party_replacement_valid
#print axioms c1_two_party_replacement_conforms
#print axioms chainOccurrence_expandWindow
#print axioms batch_exclusion_sound
#print axioms coordinator_cannot_forge
#print axioms coordinator_envelope_no_occurrence

end OpenCsv.Batch
