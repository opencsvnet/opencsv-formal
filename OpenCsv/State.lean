import OpenCsv.Interfaces

/-!
# Coin state machine (paper §4.4–4.7, §6 item 2)

An inductive definition of *valid coin traces*, mirroring the three transaction
types of the construction:

* **mint** (§4.4) — creates coins; requires a valid issuer signature on
  `(asset_id, V, mint_nonce)`, and `V = Σ v_i` over the outputs;
* **transfer** (§4.5) — consumes live coins and creates new ones; requires
  ownership knowledge and correct nullifiers for every input, per-asset
  conservation `Σ_in v = Σ_out v`, and valid predecessor traces for each input
  (here: the input must be *live* in the trace so far — produced and not yet
  consumed — which is the linear-trace form of the PCD recursion condition);
* **redeem** (§4.6) — consumes one live coin; the public `V` equals the coin's
  committed value.

A *trace* is a list of steps, built left-to-right (`ValidTrace`), each step
validated against its prefix. The anchor log (§4.7) is the ordered list of
nullifiers the steps publish.

Everything in this file is protocol logic — no cryptography beyond the
interfaces of `Interfaces.lean`, and no `sorry` anywhere in the project.
-/


namespace OpenCsv

/-! ## Basic objects -/

/-- One consumed coin together with its spending witness: the owner secret
`osk` and the nullifier `nf` the spend publishes on-chain (§4.5 item 1). -/
structure Spend where
  /-- The coin being consumed. -/
  coin : Coin
  /-- Owner secret key offered as proof of ownership. -/
  osk : OwnerSecret
  /-- Nullifier emitted by this spend. -/
  nf : F

/-- A spend is *well-formed* when the witness really owns the coin and the
published nullifier is the coin's nullifier (§4.5 items 1 and 3):
`owner = H(osk)` and `nf = H("null" ∥ osk ∥ C)`. -/
def Spend.wellFormed (sp : Spend) : Prop :=
  ownerKey sp.osk = sp.coin.owner ∧ sp.nf = nullHash sp.osk (commitHash sp.coin)

/-- A protocol step: one transaction (§4.4–4.6). -/
inductive Step where
  /-- Mint (§4.4): creates `outputs` totaling public `V` under issuer
  signature `σ` on `(asset_id, V, nonce)`. -/
  | mint (asset : Asset) (V : Nat) (nonce : F) (σ : Sig) (outputs : List Coin)
  /-- Shielded transfer (§4.5): consumes the `spends`, creates `outputs`. -/
  | transfer (spends : List Spend) (outputs : List Coin)
  /-- Redemption (§4.6): consumes one coin, burning public value `V`. -/
  | redeem (spend : Spend) (V : Nat)

/-- Coins created by a step (redemption creates none). -/
def Step.outputs : Step → List Coin
  | Step.mint _ _ _ _ outs => outs
  | Step.transfer _ outs => outs
  | Step.redeem _ _ => []

/-- The spends of a step. -/
def Step.spends : Step → List Spend
  | Step.transfer sps _ => sps
  | Step.redeem sp _ => [sp]
  | Step.mint _ _ _ _ _ => []

/-- Coins consumed by a step. -/
def Step.consumed (s : Step) : List Coin := s.spends.map Spend.coin

/-- Nullifier keys a step publishes on-chain (§4.7). Mints publish none.
(The prototype's hash-compressed multi-input anchor `H(nf_1 ∥ … ∥ nf_m)` is
abstracted away here: the log records the individual keys.) -/
def Step.anchors : Step → List F
  | Step.transfer sps _ => sps.map Spend.nf
  | Step.redeem sp _ => [sp.nf]
  | Step.mint _ _ _ _ _ => []

/-- Public value minted by a step, per asset (§4.9: the `+` terms).
(`noncomputable` because `assetId` is an opaque hash.) -/
noncomputable def Step.mintedAt : Step → F → Nat
  | Step.mint asset V _ _ _, a => if assetId asset = a then V else 0
  | _, _ => 0

/-- Public value redeemed by a step, per asset (§4.9: the `−` terms).
The public redeem record carries the coin's asset and `V = coin.value`
(the latter is enforced by validity, below). -/
def Step.redeemedAt : Step → F → Nat
  | Step.redeem sp V, a => if sp.coin.asset = a then V else 0
  | _, _ => 0

/-! ## Value accounting -/

/-- Total value of a list of coins. -/
def totalValue : List Coin → Nat
  | [] => 0
  | c :: cs => c.value + totalValue cs

/-- Total value of a list of coins in asset `a` (per-asset sum, §4.5 item 2). -/
def valueOf (a : F) : List Coin → Nat
  | [] => 0
  | c :: cs => (if c.asset = a then c.value else 0) + valueOf a cs

/-- Coins produced by a trace: outputs of every step, in order. -/
def produced : List Step → List Coin
  | [] => []
  | s :: t => s.outputs ++ produced t

/-- Coins consumed by a trace: inputs of every step, in order. -/
def consumed : List Step → List Coin
  | [] => []
  | s :: t => s.consumed ++ consumed t

/-- A coin is *live* in a trace if it was produced and not yet consumed —
the on-paper "unspent" predicate (§4.5 item 4, §4.7). -/
def Live (t : List Step) (c : Coin) : Prop := c ∈ produced t ∧ c ∉ consumed t

/-- The on-chain anchor log of a trace: the ordered list of published
nullifier keys (§4.7 rule 1: order is block order, then in-block order). -/
def anchorLog : List Step → List F
  | [] => []
  | s :: t => s.anchors ++ anchorLog t

/-- Public minted total of a trace, per asset (§4.9). -/
noncomputable def mintedBy : List Step → F → Nat
  | [], _ => 0
  | s :: t, a => s.mintedAt a + mintedBy t a

/-- Public redeemed total of a trace, per asset (§4.9). -/
def redeemedBy : List Step → F → Nat
  | [], _ => 0
  | s :: t, a => s.redeemedAt a + redeemedBy t a

/-! ## Step and trace validity -/

/-- Validity of a single step `s` against its predecessor trace `t`
(the "local predicate φ" of the PCD, §2.3):

* mint — issuer authorization (`Σ.Verify` on the mint message, §4.4 item 1),
  the public total equals the sum of shielded outputs (item 3), and every
  output is in the minted asset;
* transfer — every input is spent with ownership knowledge and the correct
  nullifier (item 1), every input is live in the predecessor trace (the
  recursion condition, item 4, in linear-trace form), and per-asset
  conservation holds (item 2);
* redeem — ownership/nullifier correctness and liveness as in a transfer,
  and the public `V` equals the coin's value (§4.6). -/
def StepValid (t : List Step) (s : Step) : Prop :=
  match s with
  | Step.mint asset V nonce σ outputs =>
      SigVerify asset.ipk ⟨assetId asset, V, nonce⟩ σ = true ∧
      V = totalValue outputs ∧
      ∀ c ∈ outputs, c.asset = assetId asset
  | Step.transfer spends outputs =>
      (∀ sp ∈ spends, sp.wellFormed) ∧
      (∀ sp ∈ spends, Live t sp.coin) ∧
      ∀ a : F, valueOf a outputs = valueOf a (spends.map Spend.coin)
  | Step.redeem sp V =>
      sp.wellFormed ∧ Live t sp.coin ∧ V = sp.coin.value

/-- **Valid coin traces** (§6 item 2), built one step at a time:
the empty trace is valid, and appending a step that is valid against its
prefix preserves validity. -/
inductive ValidTrace : List Step → Prop where
  /-- The empty trace is valid. -/
  | nil : ValidTrace []
  /-- Appending a valid step to a valid trace. -/
  | snoc {t : List Step} {s : Step} : ValidTrace t → StepValid t s → ValidTrace (t ++ [s])

/-! ## The statement a proof attests, and the consignment (§4.8) -/

/-- The public statement carried by a consignment's proof: the receiver's
verified anchor log before this transaction, the transaction itself, and the
recipient's claimed outputs (the "coin openings" of §4.8). -/
structure Claim where
  /-- Anchor log before this transaction (the receiver's chain view). -/
  priorLog : List F
  /-- The transaction being received. -/
  step : Step
  /-- The recipient's claimed outputs. -/
  outputs : List Coin

/-- The compliance predicate the PCD proof attests (§4.5 item 4, §4.8 step 2):
there exists a valid trace whose anchor log is the receiver's verified prefix,
against which the transaction is a valid step, and the claimed outputs are
really outputs of the transaction. -/
def Compliance (x : Claim) : Prop :=
  ∃ t : List Step, ValidTrace t ∧ anchorLog t = x.priorLog ∧ StepValid t x.step ∧
    ∀ c ∈ x.outputs, c ∈ x.step.outputs

/-- A consignment (§4.8): a claim plus its PCD proof. The `anchor_ref` of the
paper is modeled inside the acceptance check (see `Accept` in
`Theorems.lean`), where the receiver's chain view is `priorLog ++ anchors`. -/
structure Consignment (P : ProofSystem Claim) where
  /-- The public statement. -/
  claim : Claim
  /-- The PCD proof `π`. -/
  proof : P.Proof

/-! ## List lemmas used by the theorems

These are small, deliberately manual inductions — the development avoids
brittle automation and external libraries (no mathlib). -/

/-- `produced` of an extended trace. -/
theorem produced_snoc (t : List Step) (s : Step) :
    produced (t ++ [s]) = produced t ++ s.outputs := by
  induction t with
  | nil => simp [produced]
  | cons x xs ih => simp [List.cons_append, produced, ih, List.append_assoc]

/-- `consumed` of an extended trace. -/
theorem consumed_snoc (t : List Step) (s : Step) :
    consumed (t ++ [s]) = consumed t ++ s.consumed := by
  induction t with
  | nil => simp [consumed]
  | cons x xs ih => simp [List.cons_append, consumed, ih, List.append_assoc]

/-- Per-asset value is additive over concatenation of coin lists. -/
theorem valueOf_append (a : F) (l₁ l₂ : List Coin) :
    valueOf a (l₁ ++ l₂) = valueOf a l₁ + valueOf a l₂ := by
  induction l₁ with
  | nil => simp [valueOf]
  | cons c cs ih => simp [valueOf, ih]; omega

/-- `mintedBy` of an extended trace. -/
theorem mintedBy_snoc (t : List Step) (s : Step) (a : F) :
    mintedBy (t ++ [s]) a = mintedBy t a + s.mintedAt a := by
  induction t with
  | nil => simp [mintedBy]
  | cons x xs ih => simp [mintedBy, ih]; omega

/-- `redeemedBy` of an extended trace. -/
theorem redeemedBy_snoc (t : List Step) (s : Step) (a : F) :
    redeemedBy (t ++ [s]) a = redeemedBy t a + s.redeemedAt a := by
  induction t with
  | nil => simp [redeemedBy]
  | cons x xs ih => simp [redeemedBy, ih]; omega

/-- If every coin of `cs` is in asset `aid`, then the per-asset sum for `a`
is either everything (`a = aid`) or nothing. Used in the mint case of T1. -/
theorem valueOf_uniform (a aid : F) (cs : List Coin) (h : ∀ c ∈ cs, c.asset = aid) :
    valueOf a cs = if aid = a then totalValue cs else 0 := by
  induction cs with
  | nil => split <;> rfl
  | cons c cs ih =>
    have hc : c.asset = aid := h c (List.mem_cons_self c cs)
    have htl := ih (fun c' hc' => h c' (List.mem_cons_of_mem c hc'))
    simp only [valueOf, totalValue]
    rw [hc, htl]
    by_cases ha : aid = a
    · subst ha; rw [if_pos rfl, if_pos rfl, if_pos rfl]
    · rw [if_neg ha, if_neg ha, if_neg ha]

/-- A singleton-appended list is never empty. -/
theorem snoc_ne_nil {α : Type} {t : List α} {s : α} : t ++ [s] ≠ [] := by
  intro h
  have h2 := congrArg List.length h
  simp only [List.length_append, List.length_cons, List.length_nil] at h2
  omega

/-- Injectivity of singleton-append, in both components. -/
theorem snoc_inj {α : Type} {t t' : List α} {s s' : α} (h : t ++ [s] = t' ++ [s']) :
    t = t' ∧ s = s' := by
  induction t generalizing t' with
  | nil =>
    cases t' with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at h
      exact ⟨rfl, h.1⟩
    | cons x xs =>
      exfalso
      have h2 := congrArg List.length h
      simp only [List.length_append, List.length_cons, List.length_nil] at h2
      omega
  | cons y ys ih =>
    cases t' with
    | nil =>
      exfalso
      have h2 := congrArg List.length h
      simp only [List.length_append, List.length_cons, List.length_nil] at h2
      omega
    | cons x xs =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨hyx, hrest⟩ := h
      obtain ⟨ht, hs⟩ := ih hrest
      subst hyx; subst ht; subst hs; exact ⟨rfl, rfl⟩

/-- Inversion for `ValidTrace`: a valid trace is either empty or a valid
prefix extended by a valid step. -/
theorem ValidTrace.inv {u : List Step} (h : ValidTrace u) :
    u = [] ∨ ∃ t s, u = t ++ [s] ∧ ValidTrace t ∧ StepValid t s := by
  cases h with
  | nil => exact Or.inl rfl
  | snoc ht hs => exact Or.inr ⟨_, _, rfl, ht, hs⟩

/-- Inversion at an extended trace: the prefix is valid and the last step is
valid against it. (This is what makes T2 provable by projection.) -/
theorem ValidTrace.inv_snoc {t : List Step} {s : Step} (h : ValidTrace (t ++ [s])) :
    ValidTrace t ∧ StepValid t s := by
  rcases h.inv with hnil | ⟨t', s', heq, ht', hs'⟩
  · exact absurd hnil snoc_ne_nil
  · obtain ⟨rfl, rfl⟩ := snoc_inj heq
    exact ⟨ht', hs'⟩

end OpenCsv
