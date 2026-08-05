import OpenCsv.Forward

/-!
# Recursive proof lineage

`ValidTrace` is the ordered chain-view model used by acceptance and supply
auditing. The recursive prover has a different shape: every transfer or redeem
verifies the proofs that created its immediate inputs. This file models that
unfolded PCD tree directly.

The model records the proof-lineage version, root step, predecessor subtrees,
and predecessor-output selectors. `EdgesMatch` is the exact recursive chaining
relation. `LineageValid` then enforces recursive predecessor validity, selected
output equality, local ownership/value rules, and distinct input coins and
nullifiers for a two-input transfer.

The distinction between tree and DAG is intentional: a serialized proof
contains an unfolded recursive tree, while implementations may cache or share
identical predecessor proofs. Sharing does not change any local edge theorem.

Version policy mirrors the executable boundary after the duplicate-input
hardening: new transfer/redeem nodes are v4; an ancestor-free v3 mint may be a
migration leaf; a v3 transfer or redeem cannot be a valid recursive node. This
is protocol semantics, not a proof of the Rust AIR, FRI, or root-circuit
allowlist.
-/

namespace OpenCsv

/-- Legacy authenticated lineage retained only for ancestor-free mint leaves. -/
def legacyProofVersion : Nat := 3

/-- Current proof lineage. -/
def currentProofVersion : Nat := 4

/-- An unfolded recursive proof node. `selectors[i]` chooses the output of
`predecessors[i]` consumed by the corresponding spend. -/
inductive ProofLineage where
  | node (version : Nat) (step : Step)
      (predecessors : List ProofLineage) (selectors : List Nat)

namespace ProofLineage

/-- Version carried by the root proof. -/
def version : ProofLineage → Nat
  | .node version _ _ _ => version

/-- Protocol step proved by the root. -/
def rootStep : ProofLineage → Step
  | .node _ step _ _ => step

/-- Immediate predecessor proof trees. -/
def predecessors : ProofLineage → List ProofLineage
  | .node _ _ predecessors _ => predecessors

/-- Output selectors paired with the immediate predecessors. -/
def selectors : ProofLineage → List Nat
  | .node _ _ _ selectors => selectors

end ProofLineage

/-- Exact correspondence between predecessor proofs, their selected outputs,
and the spends consumed by the successor. The constructors force all three
lists to have the same length. -/
inductive EdgesMatch : List ProofLineage → List Nat → List Spend → Prop where
  | nil : EdgesMatch [] [] []
  | cons {predecessor predecessors selector selectors spend spends}
      (selected : predecessor.rootStep.outputs[selector]? = some spend.coin)
      (tail : EdgesMatch predecessors selectors spends) :
      EdgesMatch (predecessor :: predecessors) (selector :: selectors) (spend :: spends)

/-- Validity of an unfolded recursive proof tree.

Mint leaves have no predecessors. Transfer and redeem nodes are current-v4
nodes whose immediate predecessor trees are valid and whose selected outputs
equal the consumed coin commitments/openings. The distinctness premises match
the circuit and receiver defense-in-depth boundary; they prevent the same
authenticated predecessor value from being counted twice in one successor. -/
inductive LineageValid : ProofLineage → Prop where
  | mint {version asset V nonce σ outputs}
      (supported : version = legacyProofVersion ∨ version = currentProofVersion)
      (signature : SigVerify asset.ipk ⟨assetId asset, V, nonce⟩ σ = true)
      (value : V = totalValue outputs)
      (assets : ∀ coin ∈ outputs, coin.asset = assetId asset) :
      LineageValid (.node version (.mint asset V nonce σ outputs) [] [])
  | transfer {spends outputs ctx predecessors selectors}
      (predecessorsValid : ∀ predecessor ∈ predecessors, LineageValid predecessor)
      (edges : EdgesMatch predecessors selectors spends)
      (inputsDistinct : (spends.map Spend.coin).Nodup)
      (nullifiersDistinct : (spends.map Spend.nf).Nodup)
      (spendsValid : ∀ spend ∈ spends, spend.wellFormed)
      (conservation : ∀ asset : F,
        valueOf asset outputs = valueOf asset (spends.map Spend.coin)) :
      LineageValid
        (.node currentProofVersion (.transfer spends outputs ctx) predecessors selectors)
  | redeem {spend V ctx predecessor selector}
      (predecessorValid : LineageValid predecessor)
      (selected : predecessor.rootStep.outputs[selector]? = some spend.coin)
      (spendValid : spend.wellFormed)
      (value : V = spend.coin.value) :
      LineageValid
        (.node currentProofVersion (.redeem spend V ctx) [predecessor] [selector])

/-- Recursive edges cannot silently truncate one of the paired lists. -/
theorem EdgesMatch.lengths {predecessors selectors spends}
    (h : EdgesMatch predecessors selectors spends) :
    predecessors.length = selectors.length ∧ selectors.length = spends.length := by
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | cons _ _ ih =>
    constructor <;> simp only [List.length_cons] <;> omega

/-- Every valid recursive transfer belongs to the current proof lineage. -/
theorem transfer_lineage_current {version spends outputs ctx predecessors selectors}
    (h : LineageValid (.node version (.transfer spends outputs ctx) predecessors selectors)) :
    version = currentProofVersion := by
  cases h
  rfl

/-- Every immediate predecessor of a valid transfer is itself a valid proof
lineage, giving the induction hypothesis used by the recursive verifier. -/
theorem transfer_lineage_predecessors_valid
    {spends outputs ctx predecessors selectors}
    (h : LineageValid
      (.node currentProofVersion (.transfer spends outputs ctx) predecessors selectors)) :
    ∀ predecessor ∈ predecessors, LineageValid predecessor := by
  cases h with
  | transfer predecessorsValid _ _ _ _ _ => exact predecessorsValid

/-- A valid transfer consumes exactly selected outputs of its immediate
predecessor proofs. -/
theorem transfer_lineage_edges_match
    {spends outputs ctx predecessors selectors}
    (h : LineageValid
      (.node currentProofVersion (.transfer spends outputs ctx) predecessors selectors)) :
    EdgesMatch predecessors selectors spends := by
  cases h with
  | transfer _ edges _ _ _ _ => exact edges

/-- Input openings cannot be repeated within one valid recursive transfer. -/
theorem transfer_lineage_inputs_nodup
    {spends outputs ctx predecessors selectors}
    (h : LineageValid
      (.node currentProofVersion (.transfer spends outputs ctx) predecessors selectors)) :
    (spends.map Spend.coin).Nodup := by
  cases h with
  | transfer _ _ inputsDistinct _ _ _ => exact inputsDistinct

/-- Public nullifiers cannot be repeated within one valid recursive transfer. -/
theorem transfer_lineage_nullifiers_nodup
    {spends outputs ctx predecessors selectors}
    (h : LineageValid
      (.node currentProofVersion (.transfer spends outputs ctx) predecessors selectors)) :
    (spends.map Spend.nf).Nodup := by
  cases h with
  | transfer _ _ _ nullifiersDistinct _ _ => exact nullifiersDistinct

/-- Local per-asset conservation holds at every valid transfer root,
independently of recursive depth. -/
theorem transfer_lineage_conservation
    {spends outputs ctx predecessors selectors}
    (h : LineageValid
      (.node currentProofVersion (.transfer spends outputs ctx) predecessors selectors))
    (asset : F) :
    valueOf asset outputs = valueOf asset (spends.map Spend.coin) := by
  cases h with
  | transfer _ _ _ _ _ conservation => exact conservation asset

/-- The concrete two-input shape requires both different input coins and
different nullifiers. This is the model-level statement of the Rust AIR plus
receiver defense-in-depth invariant. -/
theorem two_input_lineage_distinct
    {left right : Spend} {outputs ctx predecessors selectors}
    (h : LineageValid
      (.node currentProofVersion (.transfer [left, right] outputs ctx)
        predecessors selectors)) :
    left.coin ≠ right.coin ∧ left.nf ≠ right.nf := by
  constructor
  · simpa using transfer_lineage_inputs_nodup h
  · simpa using transfer_lineage_nullifiers_nodup h

/-- A legacy transfer cannot enter the recursively valid lineage. -/
theorem legacy_transfer_lineage_impossible
    {spends outputs ctx predecessors selectors} :
    ¬ LineageValid
      (.node legacyProofVersion (.transfer spends outputs ctx) predecessors selectors) := by
  intro h
  have hv := transfer_lineage_current h
  simp [legacyProofVersion, currentProofVersion] at hv

/-- A legacy redeem cannot enter the recursively valid lineage. -/
theorem legacy_redeem_lineage_impossible
    {spend V ctx predecessors selectors} :
    ¬ LineageValid
      (.node legacyProofVersion (.redeem spend V ctx) predecessors selectors) := by
  intro h
  cases h

/-- The v4 one-input forwarding node is valid exactly when its predecessor is
valid, the selector names the consumed coin, the spend is well formed, and the
recipient-plus-change outputs conserve every asset. Singleton input and
nullifier lists are distinct by construction. -/
theorem v4_one_input_lineage_valid_iff
    (predecessor : ProofLineage) (selector : Nat) (spend : Spend)
    (recipient change : Coin) (ctx : AnchorCtx) :
    LineageValid
      (.node currentProofVersion (oneInputForwarding spend recipient change ctx)
        [predecessor] [selector]) ↔
      LineageValid predecessor ∧
      predecessor.rootStep.outputs[selector]? = some spend.coin ∧
      spend.wellFormed ∧
      ∀ asset : F, valueOf asset [recipient, change] = valueOf asset [spend.coin] := by
  constructor
  · intro h
    cases h with
    | transfer predecessorsValid edges _ _ spendsValid conservation =>
      have hpredecessor : LineageValid predecessor :=
        predecessorsValid predecessor (by simp)
      have hselected : predecessor.rootStep.outputs[selector]? = some spend.coin := by
        cases edges with
        | cons selected _ => exact selected
      have hspend : spend.wellFormed := spendsValid spend (by simp)
      exact ⟨hpredecessor, hselected, hspend, conservation⟩
  · rintro ⟨hpredecessor, hselected, hspend, hconservation⟩
    apply LineageValid.transfer
    · intro candidate hcandidate
      simp only [List.mem_singleton] at hcandidate
      subst candidate
      exact hpredecessor
    · exact EdgesMatch.cons hselected EdgesMatch.nil
    · simp
    · simp
    · intro candidate hcandidate
      simp only [List.mem_singleton] at hcandidate
      subst candidate
      exact hspend
    · exact hconservation

/-! ## Axiom audit -/

#print axioms EdgesMatch.lengths
#print axioms transfer_lineage_current
#print axioms transfer_lineage_predecessors_valid
#print axioms transfer_lineage_edges_match
#print axioms transfer_lineage_inputs_nodup
#print axioms transfer_lineage_nullifiers_nodup
#print axioms transfer_lineage_conservation
#print axioms two_input_lineage_distinct
#print axioms legacy_transfer_lineage_impossible
#print axioms legacy_redeem_lineage_impossible
#print axioms v4_one_input_lineage_valid_iff

end OpenCsv
