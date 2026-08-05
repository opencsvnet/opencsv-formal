import OpenCsv.Theorems

/-!
# Proof-lineage v4 one-input forwarding

The executable v4 circuit in `opencsv-rs` consumes one authenticated
predecessor coin and creates two outputs (recipient plus optional change). It
retains the fixed public statement width used by v3: the first nullifier slot
is real and the unused second slot is exactly zero.

The base state machine already quantifies over arbitrary input and output
lists, so its conservation and supply theorems cover this shape. This file
makes that correspondence explicit and auditable instead of relying on an
informal “one input is a special case” argument. It models protocol semantics,
not AIR/FRI soundness or the byte encoding of the Rust statement.
-/

namespace OpenCsv

/-- Public semantic projection of the v4 one-input statement fields that
matter to the state machine. The Rust circuit carries these values in a wider
fixed table; unrelated context and mode fields are deliberately outside this
small projection. -/
structure V4OneInputStatement where
  /-- The one real nullifier, derived from the consumed coin. -/
  nf1 : F
  /-- Fixed padding slot retained for v3 statement-width compatibility. -/
  nf2 : F
  /-- Commitment of the recipient output. -/
  output0 : F
  /-- Commitment of the optional change output. -/
  output1 : F

/-- The exact state-machine step represented by a v4 one-input proof. -/
def oneInputForwarding
    (spend : Spend) (recipient change : Coin) (ctx : AnchorCtx) : Step :=
  Step.transfer [spend] [recipient, change] ctx

/-- Project a one-input transfer into the four v4 public fields modeled here.
The second nullifier slot is zero by construction; no fake spend is introduced.
(`noncomputable` because coin commitments are opaque hashes.) -/
noncomputable def v4OneInputStatement
    (spend : Spend) (recipient change : Coin) : V4OneInputStatement :=
  ⟨spend.nf, 0, commitHash recipient, commitHash change⟩

/-- The v4 statement has one real nullifier and an exact zero padding slot,
while both output slots bind the two created coins. -/
theorem v4_one_input_statement_exact
    (spend : Spend) (recipient change : Coin) :
    let s := v4OneInputStatement spend recipient change
    s.nf1 = spend.nf ∧ s.nf2 = 0 ∧
      s.output0 = commitHash recipient ∧ s.output1 = commitHash change := by
  simp [v4OneInputStatement]

/-- If the real nullifier is nonzero, it cannot alias the padding slot. This is
the formal statement-shape counterpart of the Rust duplicate-nullifier guard. -/
theorem v4_one_input_slots_distinct
    (spend : Spend) (recipient change : Coin) (hnf : spend.nf ≠ 0) :
    let s := v4OneInputStatement spend recipient change
    s.nf1 ≠ s.nf2 := by
  simpa [v4OneInputStatement] using hnf

/-- Exact characterization of validity for the v4 specialization: ownership
and nullifier correctness, liveness of the one predecessor, and per-asset
conservation across recipient plus change. -/
theorem one_input_forwarding_valid_iff
    (t : List Step) (spend : Spend) (recipient change : Coin) (ctx : AnchorCtx) :
    StepValid t (oneInputForwarding spend recipient change ctx) ↔
      spend.wellFormed ∧ Live t spend.coin ∧
        ∀ a : F, valueOf a [recipient, change] = valueOf a [spend.coin] := by
  simp [oneInputForwarding, StepValid]

/-- A valid v4 forwarding step preserves every asset total. This is the
one-input/two-output specialization of T2, proved from the same trace theorem
used by the generic transfer path. -/
theorem one_input_forwarding_conservation
    {t : List Step} {spend : Spend} {recipient change : Coin} {ctx : AnchorCtx}
    (h : ValidTrace (t ++ [oneInputForwarding spend recipient change ctx]))
    (a : F) :
    valueOf a [recipient, change] = valueOf a [spend.coin] := by
  simpa [oneInputForwarding] using
    (transfer_conservation (t := t) (sps := [spend])
      (outs := [recipient, change]) (ctx := ctx) h a)

/-- In the single-asset wallet case, conservation specializes to the familiar
payment-plus-change equation. -/
theorem one_input_forwarding_value_equation
    {t : List Step} {spend : Spend} {recipient change : Coin} {ctx : AnchorCtx}
    (h : ValidTrace (t ++ [oneInputForwarding spend recipient change ctx]))
    (hrecipient : recipient.asset = spend.coin.asset)
    (hchange : change.asset = spend.coin.asset) :
    recipient.value + change.value = spend.coin.value := by
  have hcon := one_input_forwarding_conservation h spend.coin.asset
  simpa [valueOf, hrecipient, hchange] using hcon

/-- V4 emits exactly one anchor occurrence, bound to the real nullifier and the
carrying transaction context. The zero padding slot never enters the log. -/
theorem one_input_forwarding_anchor_exact
    (spend : Spend) (recipient change : Coin) (ctx : AnchorCtx) :
    (oneInputForwarding spend recipient change ctx).anchors =
      [⟨bindHash spend.nf ctx, ctx⟩] := by
  rfl

/-- The generic live-pool theorem covers v4 without an extra supply assumption:
one-input forwarding neither mints nor burns value. -/
theorem one_input_forwarding_pool_unchanged
    {t : List Step} {spend : Spend} {recipient change : Coin} {ctx : AnchorCtx}
    (h : ValidTrace (t ++ [oneInputForwarding spend recipient change ctx]))
    (a : F) :
    (valueOf a (produced (t ++ [oneInputForwarding spend recipient change ctx])) : Int)
        - (valueOf a (consumed (t ++ [oneInputForwarding spend recipient change ctx])) : Int)
      = (valueOf a (produced t) : Int) - (valueOf a (consumed t) : Int) := by
  simpa [oneInputForwarding] using
    (transfer_pool_unchanged (t := t) (sps := [spend])
      (outs := [recipient, change]) (ctx := ctx) h a)

/-! ## Axiom audit

These specialization theorems should introduce no new assumptions. The
statement-shape and validity lemmas are definitional; the conservation and
pool results reuse the existing T2 theorem.
-/

#print axioms v4_one_input_statement_exact
#print axioms v4_one_input_slots_distinct
#print axioms one_input_forwarding_valid_iff
#print axioms one_input_forwarding_conservation
#print axioms one_input_forwarding_value_equation
#print axioms one_input_forwarding_anchor_exact
#print axioms one_input_forwarding_pool_unchanged

end OpenCsv
