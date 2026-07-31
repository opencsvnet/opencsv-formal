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
  first-occurrence rule at finality rejects the later occurrence.
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
    | transfer sps outs =>
      simp only [StepValid] at hs
      obtain ⟨_hwf, _hlive, hcons⟩ := hs
      have hcon := hcons a
      simp only [Step.outputs, Step.consumed, Step.spends, Step.mintedAt, Step.redeemedAt]
      -- Conservation: the per-asset output and input sums are equal.
      rw [hcon]
      omega
    | redeem sp V =>
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
      | transfer _ _ => exact Step.noConfusion hmem
      | redeem _ _ => exact Step.noConfusion hmem

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
    (h : ValidTrace (t ++ [Step.transfer sps outs])) (a : F) :
    valueOf a outs = valueOf a (sps.map Spend.coin) := by
  obtain ⟨_ht, hs⟩ := ValidTrace.inv_snoc h
  simp only [StepValid] at hs
  exact hs.2.2 a

/-- **T2, corollary.** A transfer leaves the per-asset value of the live pool
(produced - consumed) unchanged: transfers neither create nor destroy value,
which is what makes the §4.9 audit equation exact. -/
theorem transfer_pool_unchanged {t : List Step} {sps : List Spend} {outs : List Coin}
    (h : ValidTrace (t ++ [Step.transfer sps outs])) (a : F) :
    (valueOf a (produced (t ++ [Step.transfer sps outs])) : Int)
      - (valueOf a (consumed (t ++ [Step.transfer sps outs])) : Int)
    = (valueOf a (produced t) : Int) - (valueOf a (consumed t) : Int) := by
  have hcon := transfer_conservation h a
  rw [produced_snoc, consumed_snoc, valueOf_append, valueOf_append]
  simp only [Step.outputs, Step.consumed, Step.spends]
  rw [hcon]
  omega

/-! ## T3 — Nullifier uniqueness and double-spend resistance (paper §5.2)

The anchor log is an ordered list (`anchorLog` in `State.lean`); a position is
a natural index into it. The first-occurrence rule of §4.7 is the predicate
`IsFirstOccurrence`. -/

/-- **T3, step 1 — a coin determines one nullifier** (§4.3: "one coin can only
ever yield one `nf`"). Two spends of the same coin that both demonstrate
ownership (`owner = H(osk)`) must use the same `osk` — by collision resistance
of the owner-key derivation — and therefore publish the same nullifier. -/
theorem nullifier_unique {coin : Coin} {osk₁ osk₂ : OwnerSecret}
    (h₁ : ownerKey osk₁ = coin.owner) (h₂ : ownerKey osk₂ = coin.owner) :
    nullHash osk₁ (commitHash coin) = nullHash osk₂ (commitHash coin) := by
  have hosk : osk₁ = osk₂ := ownerKey_injective _ _ (h₁.trans h₂.symm)
  rw [hosk]

/-- The §4.7 rule-1 predicate: `nf` occurs at position `p` of the log, and at
no earlier position. -/
def IsFirstOccurrence (log : List F) (nf : F) (p : Nat) : Prop :=
  log[p]? = some nf ∧ ∀ q, q < p → log[q]? ≠ some nf

/-- **T3, step 2 — first occurrence is unique.** Two positions that both look
like the first occurrence of the same nullifier are equal: a receiver applying
the first-occurrence rule deterministically accepts at most one position. -/
theorem first_occurrence_unique {log : List F} {nf : F} {p₁ p₂ : Nat}
    (h₁ : IsFirstOccurrence log nf p₁) (h₂ : IsFirstOccurrence log nf p₂) :
    p₁ = p₂ := by
  rcases Nat.lt_trichotomy p₁ p₂ with h | h | h
  · exact absurd h₁.1 (h₂.2 p₁ h)
  · exact h
  · exact absurd h₂.1 (h₁.2 p₂ h)

/-- **T3, step 3 — the later occurrence is rejected.** If a receiver accepted
`nf` at its first occurrence `p₁` (at finality depth), then any other
occurrence `p₂` of `nf` is necessarily later, and fails the first-occurrence
check: a receiver accepting at finality rejects it (§4.7 rules 1–2). -/
theorem later_occurrence_rejected {log : List F} {nf : F} {p₁ p₂ : Nat}
    (h₁ : IsFirstOccurrence log nf p₁) (h₂ : log[p₂]? = some nf) (hne : p₂ ≠ p₁) :
    p₁ < p₂ ∧ ¬ IsFirstOccurrence log nf p₂ := by
  have hlt : p₁ < p₂ := by
    rcases Nat.lt_trichotomy p₁ p₂ with h | h | h
    · exact h
    · exact absurd h.symm hne
    · exact absurd h₂ (h₁.2 p₂ h)
  refine ⟨hlt, ?_⟩
  intro hfirst
  exact hfirst.2 p₁ hlt h₁.1

/-- **T3 — double-spend resistance** (§5.2). Two well-formed spends of the
same coin emit equal nullifiers (by `nullifier_unique`); hence if two
receivers each see their spend as the first occurrence, they are looking at
the *same* position — two recipients cannot both finally accept spends of one
coin. (The remaining 0-conf hazard — a conflicting anchor confirmed first —
is exactly Bitcoin's own finality assumption, §4.7 rule 2, and is outside the
protocol logic.) -/
theorem double_spend_conflict {coin : Coin} {sp₁ sp₂ : Spend}
    (hw₁ : sp₁.wellFormed) (hc₁ : sp₁.coin = coin)
    (hw₂ : sp₂.wellFormed) (hc₂ : sp₂.coin = coin)
    {log : List F} {p₁ p₂ : Nat}
    (ha₁ : IsFirstOccurrence log sp₁.nf p₁) (ha₂ : IsFirstOccurrence log sp₂.nf p₂) :
    p₁ = p₂ := by
  have hnf : sp₁.nf = sp₂.nf := by
    have h1 : sp₁.nf = nullHash sp₁.osk (commitHash coin) := by rw [hw₁.2, hc₁]
    have h2 : sp₂.nf = nullHash sp₂.osk (commitHash coin) := by rw [hw₂.2, hc₂]
    rw [h1, h2]
    exact nullifier_unique (by rw [hw₁.1, hc₁]) (by rw [hw₂.1, hc₂])
  exact first_occurrence_unique (hnf ▸ ha₁) ha₂

/-- **T3, observability corollary** (§4.3: a double-spend attempt is "an
*observable conflict*"). Any two attempted spends of one coin anchored at
distinct positions put the *same* nullifier at two distinct positions of the
public log — the conflict is visible to every client. -/
theorem double_spend_observable {coin : Coin} {sp₁ sp₂ : Spend}
    (hw₁ : sp₁.wellFormed) (hc₁ : sp₁.coin = coin)
    (hw₂ : sp₂.wellFormed) (hc₂ : sp₂.coin = coin)
    {log : List F} {p₁ p₂ : Nat}
    (h₁ : log[p₁]? = some sp₁.nf) (h₂ : log[p₂]? = some sp₂.nf) (hne : p₁ ≠ p₂) :
    ∃ (nf : F) (q₁ q₂ : Nat), q₁ ≠ q₂ ∧ log[q₁]? = some nf ∧ log[q₂]? = some nf := by
  have hnf : sp₁.nf = sp₂.nf := by
    have e1 : sp₁.nf = nullHash sp₁.osk (commitHash coin) := by rw [hw₁.2, hc₁]
    have e2 : sp₂.nf = nullHash sp₂.osk (commitHash coin) := by rw [hw₂.2, hc₂]
    rw [e1, e2]
    exact nullifier_unique (by rw [hw₁.1, hc₁]) (by rw [hw₂.1, hc₂])
  exact ⟨sp₁.nf, p₁, p₂, hne, h₁, hnf ▸ h₂⟩

/-! ## T4 — Receiver correctness (paper §4.8)

The `Accept` check list, modeled propositionally. The receiver's chain view is
`priorLog ++ step.anchors` (they verified the prefix against Bitcoin and see
this transaction's anchors at the tail); the claimed anchor position of the
transaction is therefore `priorLog.length`. -/

/-- **The `Accept` check list** (§4.8 steps 2–4):

1. proof check — `Π.Verify(vk, x, π) = 1` on the claim;
2. the transaction publishes at least one nullifier key (transfers and
   redemptions; mints are not received via `Accept` in this model);
3. anchor check — every published nullifier has no earlier occurrence in the
   receiver's verified chain view (§4.7 rule 1), and the anchor is buried
   under `k` confirmations (rule 2; `confs` is the observed depth);
4. ownership check — one of the recipient's keys derives the owner of at
   least one claimed output. -/
def Accept (P : ProofSystem Claim) (vk : P.Vk) (keys : List OwnerSecret)
    (confs k : Nat) (c : Consignment P) : Prop :=
  P.verify vk c.claim c.proof = true ∧                        -- (1) proof check
  c.claim.step.anchors ≠ [] ∧                                 -- (2) publishes keys
  (∀ nf ∈ c.claim.step.anchors, nf ∉ c.claim.priorLog) ∧      -- (3a) no earlier occurrence
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
receiver's chain view (`priorLog ++ step.anchors`), every published nullifier
of the accepted transaction has *no* occurrence at any position of the
verified prefix — so by `later_occurrence_rejected` (T3), any conflicting
anchor for the same coin in the prefix would have made this receiver reject,
and any future one will be rejected by others. -/
theorem accept_nullifier_no_earlier_occurrence
    (P : ProofSystem Claim) (vk : P.Vk) (keys : List OwnerSecret)
    (confs k : Nat) (c : Consignment P) (h : Accept P vk keys confs k c)
    {nf : F} (hnf : nf ∈ c.claim.step.anchors) (q : Nat)
    (hq : q < c.claim.priorLog.length) :
    (c.claim.priorLog ++ c.claim.step.anchors)[q]? ≠ some nf := by
  rw [getElem?_append_left' hq]
  intro heq
  exact h.2.2.1 nf hnf (mem_of_getElem?_eq_some heq)

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
#print axioms receiver_correctness
#print axioms accepted_trace_supply

end OpenCsv
