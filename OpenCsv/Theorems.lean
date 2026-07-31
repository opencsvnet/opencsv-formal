import OpenCsv.State

/-!
# Theorems (paper §5, §6 item 3)

The four theorems of the formal-verification roadmap, proved against the state
machine of `State.lean` and conditional only on the assumptions of
`Interfaces.lean`:

* **T1 — inflation soundness** (§5.1): along any valid trace, per-asset net
  value created equals Σ mint `V` - Σ redeem `V`, and every mint carries a
  valid issuer signature (hence, by EUF-CMA, was authorized by the issuer).
* **T2 — conservation** (§4.5 item 2): every transfer step preserves
  per-asset totals. This holds by construction of `StepValid`; we still prove
  it as a lemma, and derive that a transfer leaves the per-asset value of the
  live pool unchanged.
* **T3 — nullifier uniqueness** (§5.2): two spends of the same coin emit equal
  nullifiers; hence any accepted double-spend yields an observable conflict
  (equal nullifiers at distinct anchor positions), and a receiver applying the
  first-occurrence rule at finality rejects the later occurrence. Updated
  for the **anti-grief fix (corrected bound-payload design)**: the on-chain
  payload is `P = H(raw_nf, ctx)`, the raw nullifier stays off-chain, and
  occurrences are well-formed entries relative to a verifier-supplied
  `raw_nf`. New theorems: `copied_record_not_wellformed` /
  `griefer_copy_invisible` (replay fails by injectivity) and
  `no_occurrence_without_knowledge` /
  `unknowing_adversary_entry_invisible` (recomputation fails by preimage
  resistance); double-spend observability is scoped to consignment holders.
* **T4 — receiver correctness** (§4.8): the `Accept` check list implies
  membership in the valid-trace inductive, modulo the stated hypotheses.

No `sorry`, no `admit`, no mathlib.
-/


namespace OpenCsv

/-! ## T1 — Inflation soundness (paper §5.1)

The workhorse is a natural-number balance equation (adding both sides avoids
truncated subtraction); the headline statement over integers follows. -/

/-- **T1, balance form.** Along any valid trace, per asset:
value produced + publicly redeemed = publicly minted + value consumed.
Equivalently, net value created = Σ mints - Σ redeems (see the integer form
below). Proved by induction over the trace; each step preserves the equation:

* mint — produced grows by the outputs, whose per-asset sum is exactly `V`
  (all outputs are in the minted asset), and `mintedBy` grows by the same `V`;
* transfer — produced grows by the outputs, consumed by the inputs, and
  conservation (T2) makes these equal per asset;
* redeem — consumed grows by the coin, whose per-asset value is `V`, and
  `redeemedBy` grows by the same `V`. -/
theorem inflation_soundness_nat {t : List Step} (h : ValidTrace t) (a : F) :
    valueOf a (produced t) + redeemedBy t a
      = mintedBy t a + valueOf a (consumed t) := by
  induction h with
  | nil => simp [produced, consumed, mintedBy, redeemedBy, valueOf]
  | snoc ht hs ih =>
    rename_i t s
    rw [produced_snoc, consumed_snoc, mintedBy_snoc, redeemedBy_snoc,
      valueOf_append, valueOf_append]
    cases s with
    | mint asset V nonce σ outs =>
      -- The new step is a mint: unpack its validity conditions.
      simp only [StepValid] at hs
      obtain ⟨_hsig, hV, hassets⟩ := hs
      -- Reduce the per-step functions at the mint constructor.
      simp only [Step.outputs, Step.consumed, Step.spends, Step.mintedAt, Step.redeemedAt,
        List.map_nil, valueOf]
      -- All outputs are in the minted asset, so the per-asset output sum is
      -- `if assetId asset = a then V else 0` — identical to the mint term.
      rw [valueOf_uniform a (assetId asset) outs hassets, ← hV]
      omega
    | transfer sps outs _ctx =>
      simp only [StepValid] at hs
      obtain ⟨_hwf, _hlive, hcons⟩ := hs
      have hcon := hcons a
      simp only [Step.outputs, Step.consumed, Step.spends, Step.mintedAt, Step.redeemedAt]
      -- Conservation: the per-asset output and input sums are equal.
      rw [hcon]
      omega
    | redeem sp V _ctx =>
      simp only [StepValid] at hs
      obtain ⟨_hwf, _hlive, hV⟩ := hs
      simp only [Step.outputs, Step.consumed, Step.spends, Step.mintedAt, Step.redeemedAt,
        List.map_cons, List.map_nil, valueOf]
      -- The consumed coin's per-asset value equals the public redeem term.
      rw [← hV]
      omega

/-- **T1 — inflation soundness** (§5.1). Along any valid trace, per asset,
the net value in circulation (produced minus consumed) equals the public
supply function of §4.9: Σ mint `V` - Σ redeem `V`. -/
theorem inflation_soundness {t : List Step} (h : ValidTrace t) (a : F) :
    (valueOf a (produced t) : Int) - (valueOf a (consumed t) : Int)
      = (mintedBy t a : Int) - (redeemedBy t a : Int) := by
  have hnat := inflation_soundness_nat h a
  omega

/-- **T1, second half.** Every mint step of a valid trace carries a valid
issuer signature on its mint message (§4.4 item 1). -/
theorem mints_signed {t : List Step} (h : ValidTrace t) :
    ∀ {asset : Asset} {V : Nat} {nonce : F} {σ : Sig} {outs : List Coin},
      Step.mint asset V nonce σ outs ∈ t →
        SigVerify asset.ipk ⟨assetId asset, V, nonce⟩ σ = true := by
  induction h with
  | nil =>
    intro _ _ _ _ _ hmem
    exact absurd hmem (List.not_mem_nil _)
  | snoc ht hs ih =>
    rename_i t s
    intro asset V nonce σ outs hmem
    rw [List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · exact ih hmem
    · rw [List.mem_singleton] at hmem
      cases s with
      | mint asset' V' nonce' σ' outs' =>
        simp only [StepValid] at hs
        obtain ⟨hsig, _, _⟩ := hs
        rw [Step.mint.injEq] at hmem
        obtain ⟨e1, e2, e3, e4, e5⟩ := hmem
        subst e1 e2 e3 e4 e5
        exact hsig
      | transfer _ _ _ => exact Step.noConfusion hmem
      | redeem _ _ _ => exact Step.noConfusion hmem

/-- **T1, issuer-authorization corollary** (§5.1: "the only sources of
per-asset value are signed mints"). By the abstract EUF-CMA assumption, every
mint in a valid trace was authorized by the holder of the issuer key. -/
theorem mints_authorized {t : List Step} (h : ValidTrace t)
    {asset : Asset} {V : Nat} {nonce : F} {σ : Sig} {outs : List Coin}
    (hmem : Step.mint asset V nonce σ outs ∈ t) :
    SignedByIssuer asset.ipk ⟨assetId asset, V, nonce⟩ :=
  sig_unforgeable _ _ _ (mints_signed h hmem)

/-! ## T2 — Conservation (paper §4.5 item 2) -/

/-- **T2 — conservation.** Every transfer step of a valid trace preserves
per-asset totals: the outputs carry exactly the per-asset value of the
consumed inputs. (By construction of `StepValid`; proved as a lemma by
inversion on the trace.) -/
theorem transfer_conservation {t : List Step} {sps : List Spend} {outs : List Coin}
    {ctx : AnchorCtx}
    (h : ValidTrace (t ++ [Step.transfer sps outs ctx])) (a : F) :
    valueOf a outs = valueOf a (sps.map Spend.coin) := by
  obtain ⟨_ht, hs⟩ := ValidTrace.inv_snoc h
  simp only [StepValid] at hs
  exact hs.2.2 a

/-- **T2, corollary.** A transfer leaves the per-asset value of the live pool
(produced - consumed) unchanged: transfers neither create nor destroy value,
which is what makes the §4.9 audit equation exact. -/
theorem transfer_pool_unchanged {t : List Step} {sps : List Spend} {outs : List Coin}
    {ctx : AnchorCtx}
    (h : ValidTrace (t ++ [Step.transfer sps outs ctx])) (a : F) :
    (valueOf a (produced (t ++ [Step.transfer sps outs ctx])) : Int)
      - (valueOf a (consumed (t ++ [Step.transfer sps outs ctx])) : Int)
    = (valueOf a (produced t) : Int) - (valueOf a (consumed t) : Int) := by
  have hcon := transfer_conservation h a
  rw [produced_snoc, consumed_snoc, valueOf_append, valueOf_append]
  simp only [Step.outputs, Step.consumed, Step.spends]
  rw [hcon]
  omega

/-! ## T3 — Nullifier uniqueness and double-spend resistance (paper §5.2)

The anchor log is an ordered list of **anchor entries** `(P, ctx)` where
`P = H(raw_nf, ctx)` (`anchorLog` in `State.lean`); a position is a natural
index into it. The raw nullifier never appears on-chain: occurrences are
*relative to a raw nullifier supplied by the verifier*, so they are
recognizable only to consignment holders — that scoping is intended (see the
anti-grief subsection). The first-occurrence rule of §4.7 is the predicate
`IsFirstOccurrence`, quantifying over well-formed entries only. -/

/-- **T3, step 1 — a coin determines one nullifier** (§4.3: "one coin can only
ever yield one `nf`"). Two spends of the same coin that both demonstrate
ownership (`owner = H(osk)`) must use the same `osk` — by collision resistance
of the owner-key derivation — and therefore emit the same raw nullifier. -/
theorem nullifier_unique {coin : Coin} {osk₁ osk₂ : OwnerSecret}
    (h₁ : ownerKey osk₁ = coin.owner) (h₂ : ownerKey osk₂ = coin.owner) :
    nullHash osk₁ (commitHash coin) = nullHash osk₂ (commitHash coin) := by
  have hosk : osk₁ = osk₂ := ownerKey_injective _ _ (h₁.trans h₂.symm)
  rw [hosk]

/-- **Occurrence** of a raw nullifier at a position: the entry there is
well-formed for `raw_nf`, i.e. its payload is `H(raw_nf, ctx)`. Recognizable
only to verifiers who know `raw_nf`. -/
def OccurrenceAt (log : List AnchorEntry) (raw_nf : F) (q : Nat) : Prop :=
  ∃ e, log[q]? = some e ∧ e.wellFormed raw_nf

/-- The §4.7 rule-1 predicate: `raw_nf` has a well-formed occurrence at
position `p`, and no well-formed occurrence at any earlier position. -/
def IsFirstOccurrence (log : List AnchorEntry) (raw_nf : F) (p : Nat) : Prop :=
  OccurrenceAt log raw_nf p ∧
  ∀ q, q < p → ∀ e, log[q]? = some e → ¬ e.wellFormed raw_nf

/-- **T3, step 2 — first occurrence is unique.** Two positions that both look
like the first well-formed occurrence of the same raw nullifier are equal: a
receiver applying the first-occurrence rule deterministically accepts at most
one position. -/
theorem first_occurrence_unique {log : List AnchorEntry} {raw_nf : F} {p₁ p₂ : Nat}
    (h₁ : IsFirstOccurrence log raw_nf p₁) (h₂ : IsFirstOccurrence log raw_nf p₂) :
    p₁ = p₂ := by
  rcases Nat.lt_trichotomy p₁ p₂ with h | h | h
  · obtain ⟨e, he, hwf⟩ := h₁.1
    exact absurd hwf (h₂.2 p₁ h e he)
  · exact h
  · obtain ⟨e, he, hwf⟩ := h₂.1
    exact absurd hwf (h₁.2 p₂ h e he)

/-- **T3, step 3 — the later occurrence is rejected.** If a receiver accepted
`raw_nf` at its first occurrence `p₁` (at finality depth), then any other
well-formed occurrence `p₂` of `raw_nf` is necessarily later, and fails the
first-occurrence check: a receiver accepting at finality rejects it
(§4.7 rules 1–2). -/
theorem later_occurrence_rejected {log : List AnchorEntry} {raw_nf : F} {p₁ p₂ : Nat}
    (h₁ : IsFirstOccurrence log raw_nf p₁) (h₂ : OccurrenceAt log raw_nf p₂)
    (hne : p₂ ≠ p₁) :
    p₁ < p₂ ∧ ¬ IsFirstOccurrence log raw_nf p₂ := by
  have hlt : p₁ < p₂ := by
    rcases Nat.lt_trichotomy p₁ p₂ with h | h | h
    · exact h
    · exact absurd h.symm hne
    · obtain ⟨e, he, hwf⟩ := h₂
      exact absurd hwf (h₁.2 p₂ h e he)
  refine ⟨hlt, fun hfirst => ?_⟩
  obtain ⟨e, he, hwf⟩ := h₁.1
  exact hfirst.2 p₁ hlt e he hwf

/-- **Conflict soundness — one payload binds one coin.** A single on-chain
entry cannot be a well-formed occurrence of two different raw nullifiers:
from `bindHash_injective`, the payload determines `(raw_nf, ctx)` uniquely.
This keeps the occurrence relation functional — an adversary cannot make one
payload count for two coins. -/
theorem payload_binds_one_nullifier {e : AnchorEntry} {r₁ r₂ : F}
    (h₁ : e.wellFormed r₁) (h₂ : e.wellFormed r₂) : r₁ = r₂ :=
  (bindHash_injective r₁ e.ctx r₂ e.ctx (h₁.symm.trans h₂)).1

/-- **T3 — double-spend resistance** (§5.2). Two well-formed spends of the
same coin emit equal raw nullifiers (by `nullifier_unique`); hence if two
receivers — both consignment holders, hence knowing the raw nullifier — each
see their spend as the first well-formed occurrence, they are looking at the
*same* position: two recipients cannot both finally accept spends of one
coin. (The remaining 0-conf hazard — a conflicting anchor confirmed first —
is exactly Bitcoin's own finality assumption, §4.7 rule 2, and is outside the
protocol logic.) -/
theorem double_spend_conflict {coin : Coin} {sp₁ sp₂ : Spend}
    (hw₁ : sp₁.wellFormed) (hc₁ : sp₁.coin = coin)
    (hw₂ : sp₂.wellFormed) (hc₂ : sp₂.coin = coin)
    {log : List AnchorEntry} {p₁ p₂ : Nat}
    (ha₁ : IsFirstOccurrence log sp₁.nf p₁) (ha₂ : IsFirstOccurrence log sp₂.nf p₂) :
    p₁ = p₂ := by
  have hnf : sp₁.nf = sp₂.nf := by
    have h1 : sp₁.nf = nullHash sp₁.osk (commitHash coin) := by rw [hw₁.2, hc₁]
    have h2 : sp₂.nf = nullHash sp₂.osk (commitHash coin) := by rw [hw₂.2, hc₂]
    rw [h1, h2]
    exact nullifier_unique (by rw [hw₁.1, hc₁]) (by rw [hw₂.1, hc₂])
  exact first_occurrence_unique (hnf ▸ ha₁) ha₂

/-- **T3, observability corollary** (§4.3: a double-spend attempt is "an
*observable conflict*"). Any two attempted spends of one coin anchored as
well-formed entries at distinct positions put well-formed occurrences of the
*same* raw nullifier at two distinct positions — the conflict is observable.
Note the scoping under the corrected anchor model: the raw nullifier never
appears on-chain, so this conflict is observable **to consignment holders**
(who know `raw_nf`) — precisely the parties whose acceptance is at stake. -/
theorem double_spend_observable {coin : Coin} {sp₁ sp₂ : Spend}
    (hw₁ : sp₁.wellFormed) (hc₁ : sp₁.coin = coin)
    (hw₂ : sp₂.wellFormed) (hc₂ : sp₂.coin = coin)
    {log : List AnchorEntry} {p₁ p₂ : Nat} {e₁ e₂ : AnchorEntry}
    (hwf₁ : e₁.wellFormed sp₁.nf) (h₁ : log[p₁]? = some e₁)
    (hwf₂ : e₂.wellFormed sp₂.nf) (h₂ : log[p₂]? = some e₂)
    (hne : p₁ ≠ p₂) :
    ∃ (raw_nf : F) (q₁ q₂ : Nat), q₁ ≠ q₂ ∧
      OccurrenceAt log raw_nf q₁ ∧ OccurrenceAt log raw_nf q₂ := by
  have hnf : sp₁.nf = sp₂.nf := by
    have e1 : sp₁.nf = nullHash sp₁.osk (commitHash coin) := by rw [hw₁.2, hc₁]
    have e2 : sp₂.nf = nullHash sp₂.osk (commitHash coin) := by rw [hw₂.2, hc₂]
    rw [e1, e2]
    exact nullifier_unique (by rw [hw₁.1, hc₁]) (by rw [hw₂.1, hc₂])
  exact ⟨sp₁.nf, p₁, p₂, hne, ⟨e₁, h₁, hwf₁⟩, ⟨e₂, h₂, hnf ▸ hwf₂⟩⟩

/-! ### Anti-grief: the bound payload cannot be replayed or recomputed

Under the corrected design the on-chain payload is `P = H(raw_nf, ctx)`. Two
attack directions, both closed:

1. **Replay.** A mempool spy copies the payload `P` into their own
   transaction — but their transaction's context `ctx'` is derived from its
   own inputs and differs from the original (`ctx' ≠ ctx`, the
   un-reproducibility hypothesis). By injectivity of the binding, the copied
   entry is not well-formed for `raw_nf`
   (`copied_record_not_wellformed`), hence not an occurrence
   (`griefer_copy_invisible`).
2. **Recomputation.** The spy sees only `P` and `ctx`; the raw nullifier
   never appears on-chain. By preimage resistance
   (`occurrence_requires_knowledge`), computing a fresh entry well-formed for
   `raw_nf` requires knowing `raw_nf` — so an adversary who does not know it
   (a pure chain observer, not a consignment holder) cannot create *any*
   well-formed occurrence of the coin (`no_occurrence_without_knowledge`). -/

/-- **Anti-grief 1a — a copied payload is not well-formed under a new
context.** If `P` is the legitimate payload `P = H(raw_nf, ctx)`, then the
entry `(P, ctx')` with `ctx' ≠ ctx` fails the well-formedness check for
`raw_nf`: from `bindHash_injective`, `P ≠ H(raw_nf, ctx')`. -/
theorem copied_record_not_wellformed {raw_nf P : F} {ctx ctx' : AnchorCtx}
    (hP : P = bindHash raw_nf ctx) (hctx : ctx' ≠ ctx) :
    ¬ AnchorEntry.wellFormed ⟨P, ctx'⟩ raw_nf := by
  intro hwf
  -- hwf unfolds to `P = bindHash raw_nf ctx'`; chain with hP and inject.
  exact hctx (bindHash_injective raw_nf ctx raw_nf ctx' (hP.symm.trans hwf)).2.symm

/-- **Anti-grief 1b — a griefer's copy is invisible to the occurrence rule.**
A copied payload anchored under a different context `ctx' ≠ ctx`, at *any*
position `q` of the log, is not a first occurrence of `raw_nf` — indeed not
an occurrence at all. Replaying the record cannot race the legitimate
anchor. -/
theorem griefer_copy_invisible {log : List AnchorEntry} {raw_nf P : F}
    {ctx ctx' : AnchorCtx} {q : Nat}
    (hP : P = bindHash raw_nf ctx) (hctx : ctx' ≠ ctx)
    (hq : log[q]? = some ⟨P, ctx'⟩) :
    ¬ IsFirstOccurrence log raw_nf q := by
  intro hfirst
  obtain ⟨e, he, hwf⟩ := hfirst.1
  rw [hq] at he
  simp only [Option.some.injEq] at he
  subst he
  exact copied_record_not_wellformed hP hctx hwf

/-- **Anti-grief 2 — no occurrence without knowledge of the raw nullifier.**
An adversary who does not know `raw_nf` (`¬ KnowsRawNf log raw_nf` — a pure
chain observer; the raw nullifier never appears on-chain) cannot produce any
entry well-formed for `raw_nf` under a fresh context: by preimage resistance
(`occurrence_requires_knowledge`), a fresh well-formed occurrence would
witness that they know it. (The freshness side condition is the
un-reproducibility property of `ctx`: the adversary's transaction derives a
context not already on-chain.) -/
theorem no_occurrence_without_knowledge {log : List AnchorEntry} {e : AnchorEntry}
    {raw_nf : F}
    (hk : ¬ KnowsRawNf log raw_nf) (hfresh : ∀ e' ∈ log, e'.ctx ≠ e.ctx) :
    ¬ e.wellFormed raw_nf :=
  fun hwf => hk (occurrence_requires_knowledge log e raw_nf hwf hfresh)

/-- **Anti-grief 2, positioned form.** Consequently, no entry an unknowing
adversary can place in the log — at any position — is an occurrence of the
coin: they can neither race the legitimate anchor nor fabricate a conflict. -/
theorem unknowing_adversary_entry_invisible {log : List AnchorEntry} {e : AnchorEntry}
    {raw_nf : F} {q : Nat}
    (hk : ¬ KnowsRawNf log raw_nf) (hfresh : ∀ e' ∈ log, e'.ctx ≠ e.ctx)
    (hq : log[q]? = some e) :
    ¬ IsFirstOccurrence log raw_nf q := by
  intro hfirst
  obtain ⟨e', he', hwf'⟩ := hfirst.1
  rw [hq] at he'
  simp only [Option.some.injEq] at he'
  subst he'
  exact no_occurrence_without_knowledge hk hfresh hwf'

/-! ## T4 — Receiver correctness (paper §4.8)

The `Accept` check list, modeled propositionally. The receiver's chain view is
`priorLog ++ step.anchors` (they verified the prefix against Bitcoin and see
this transaction's anchors at the tail); the claimed anchor position of the
transaction is therefore `priorLog.length`. -/

/-- **The `Accept` check list** (§4.8 steps 2–4):

1. proof check — `Π.Verify(vk, x, π) = 1` on the claim;
2. the transaction publishes at least one nullifier key (transfers and
   redemptions; mints are not received via `Accept` in this model);
3. anchor check — for each of the transaction's raw nullifiers (known to
   the receiver from the consignment/proof; they never appear on-chain), no
   entry in the receiver's verified chain prefix is well-formed for it
   (§4.7 rule 1, anti-grief form: malformed entries — e.g. copied payloads
   under a foreign context — do not count), and the anchor is buried under
   `k` confirmations (rule 2; `confs` is the observed depth);
4. ownership check — one of the recipient's keys derives the owner of at
   least one claimed output. -/
def Accept (P : ProofSystem Claim) (vk : P.Vk) (keys : List OwnerSecret)
    (confs k : Nat) (c : Consignment P) : Prop :=
  P.verify vk c.claim c.proof = true ∧                        -- (1) proof check
  c.claim.step.anchors ≠ [] ∧                                 -- (2) publishes keys
  (∀ nf ∈ c.claim.step.rawNfs, ∀ e ∈ c.claim.priorLog,
      ¬ e.wellFormed nf) ∧                                    -- (3a) no earlier WF occurrence
  k ≤ confs ∧                                                 -- (3b) finality depth
  ∃ osk ∈ keys, ∃ coin ∈ c.claim.outputs, ownerKey osk = coin.owner  -- (4) ownership

/-- **T4 — receiver correctness.** If `Accept` succeeds, then — modulo proof
system soundness (`P.Holds` is the compliance predicate) — the received
transaction extends a valid trace: the claimed outputs were produced by a
trace in the `ValidTrace` inductive. Combined with T1 this says accepted coins
descend from issuer-signed mints with exact per-asset accounting. -/
theorem receiver_correctness (P : ProofSystem Claim) (hP : P.Holds = Compliance)
    (vk : P.Vk) (keys : List OwnerSecret) (confs k : Nat) (c : Consignment P)
    (h : Accept P vk keys confs k c) :
    ∃ t : List Step, ValidTrace (t ++ [c.claim.step]) ∧
      ∀ coin ∈ c.claim.outputs, coin ∈ produced (t ++ [c.claim.step]) := by
  obtain ⟨hverify, _, _, _, _⟩ := h
  -- Proof check + soundness: the compliance predicate held for some witness.
  have hsound : P.Holds c.claim := P.sound vk c.claim c.proof hverify
  rw [hP] at hsound
  obtain ⟨t, ht, _hlog, hstep, houts⟩ := hsound
  -- The witness trace extended by this step is valid, and produces the outputs.
  refine ⟨t, ValidTrace.snoc ht hstep, fun coin hcoin => ?_⟩
  rw [produced_snoc]
  exact List.mem_append_right _ (houts coin hcoin)

/-- Membership in a list, from an indexed lookup. (Small manual lemma.) -/
theorem mem_of_getElem?_eq_some {α : Type} {l : List α} {n : Nat} {a : α}
    (h : l[n]? = some a) : a ∈ l := by
  induction l generalizing n with
  | nil => simp at h
  | cons x xs ih =>
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      rw [← h]
      exact List.mem_cons_self x xs
    | succ n =>
      simp only [List.getElem?_cons_succ] at h
      exact List.mem_cons_of_mem x (ih h)

/-- Lookup into a concatenation at an index in the left part. (Small manual
lemma; core has this as `List.getElem?_append_left`, we reprove it to keep
the development self-contained.) -/
theorem getElem?_append_left' {α : Type} {l₁ l₂ : List α} {n : Nat} (h : n < l₁.length) :
    (l₁ ++ l₂)[n]? = l₁[n]? := by
  induction l₁ generalizing n with
  | nil => simp at h
  | cons x xs ih =>
    cases n with
    | zero => simp only [List.cons_append, List.getElem?_cons_zero]
    | succ n =>
      simp only [List.cons_append, List.getElem?_cons_succ]
      exact ih (by simp only [List.length_cons] at h; omega)

/-- **T4 + T3 glue.** The anchor check of `Accept` does its job: in the
receiver's chain view (`priorLog ++ step.anchors`), every raw nullifier of
the accepted transaction has *no well-formed occurrence* at any position of
the verified prefix — so by `later_occurrence_rejected` (T3), any conflicting
well-formed anchor for the same coin in the prefix would have made this
receiver reject, and any future one will be rejected by others. -/
theorem accept_nullifier_no_earlier_occurrence
    (P : ProofSystem Claim) (vk : P.Vk) (keys : List OwnerSecret)
    (confs k : Nat) (c : Consignment P) (h : Accept P vk keys confs k c)
    {nf : F} (hnf : nf ∈ c.claim.step.rawNfs) (q : Nat)
    (hq : q < c.claim.priorLog.length) :
    ∀ e, (c.claim.priorLog ++ c.claim.step.anchors)[q]? = some e →
      ¬ e.wellFormed nf := by
  intro e heq
  rw [getElem?_append_left' hq] at heq
  exact h.2.2.1 nf hnf e (mem_of_getElem?_eq_some heq)

/-- **T4 + T1 corollary — accepted coins are backed by the public supply
stream.** The trace an accepting receiver ends up with satisfies the §4.9
audit equation: per asset, net value in circulation equals Σ mints - Σ redeems.
This is the formal content of §5.1's claim that "the public stream bounds
total supply exactly". -/
theorem accepted_trace_supply
    (P : ProofSystem Claim) (hP : P.Holds = Compliance)
    (vk : P.Vk) (keys : List OwnerSecret) (confs k : Nat) (c : Consignment P)
    (h : Accept P vk keys confs k c) :
    ∃ u : List Step, ValidTrace u ∧
      (∀ coin ∈ c.claim.outputs, coin ∈ produced u) ∧
      ∀ a : F, (valueOf a (produced u) : Int) - (valueOf a (consumed u) : Int)
        = (mintedBy u a : Int) - (redeemedBy u a : Int) := by
  obtain ⟨t, ht, hprod⟩ := receiver_correctness P hP vk keys confs k c h
  exact ⟨t ++ [c.claim.step], ht, hprod, fun a => inflation_soundness ht a⟩

/-! ## Axiom audit

The following commands print, at build time, exactly which assumptions each
headline theorem depends on. They should list only the labeled cryptographic
assumptions of `Interfaces.lean` — and in particular never `sorryAx`. -/

#print axioms inflation_soundness
#print axioms mints_authorized
#print axioms transfer_conservation
#print axioms double_spend_conflict
#print axioms later_occurrence_rejected
#print axioms payload_binds_one_nullifier
#print axioms copied_record_not_wellformed
#print axioms griefer_copy_invisible
#print axioms no_occurrence_without_knowledge
#print axioms unknowing_adversary_entry_invisible
#print axioms receiver_correctness
#print axioms accepted_trace_supply

end OpenCsv
