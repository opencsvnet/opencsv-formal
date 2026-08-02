import OpenCsv.Theorems
import OpenCsv.Scan

/-!
# Batch envelopes (paper §4.7.2)

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
#print axioms chainOccurrence_expandWindow
#print axioms batch_exclusion_sound
#print axioms coordinator_cannot_forge
#print axioms coordinator_envelope_no_occurrence

end OpenCsv.Batch
