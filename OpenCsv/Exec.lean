import OpenCsv.State

/-!
# Executable state machine and differential corpus

`State.lean` deliberately leaves cryptography opaque.  This module separates
the executable protocol logic from that boundary: `Backend` supplies runnable
hash/signature operations, while `Refines` states when such a backend agrees
with the abstract interfaces.  The interpreter returns a typed first error.

The corpus generator at the end uses a small deterministic backend and PRNG.
It is test data, not a claim that the toy arithmetic hashes implement the
production cryptography.
-/

namespace OpenCsv.Exec

/-- Runnable operations needed by the state machine. -/
structure Backend where
  SigRep : Type
  assetId : Asset → F
  commitHash : Coin → F
  ownerKey : OwnerSecret → F
  nullHash : OwnerSecret → F → F
  sigVerify : F → MintMsg → SigRep → Bool

/-- Executable counterpart of `OpenCsv.Spend`. -/
structure Spend where
  coin : Coin
  osk : OwnerSecret
  nf : F

/-- Executable counterpart of `OpenCsv.Step`. -/
inductive Step (B : Backend) where
  | mint (asset : Asset) (V : Nat) (nonce : F) (σ : B.SigRep) (outputs : List Coin)
  | transfer (spends : List Spend) (outputs : List Coin) (ctx : AnchorCtx)
  | redeem (spend : Spend) (V : Nat) (ctx : AnchorCtx)

def Step.outputs {B : Backend} : Step B → List Coin
  | .mint _ _ _ _ outputs => outputs
  | .transfer _ outputs _ => outputs
  | .redeem _ _ _ => []

def Step.spends {B : Backend} : Step B → List Spend
  | .mint _ _ _ _ _ => []
  | .transfer spends _ _ => spends
  | .redeem spend _ _ => [spend]

def produced {B : Backend} : List (Step B) → List Coin
  | [] => []
  | step :: trace => step.outputs ++ produced trace

def consumed {B : Backend} : List (Step B) → List Coin
  | [] => []
  | step :: trace => step.spends.map Spend.coin ++ consumed trace

/-- Boolean coin equality, kept explicit because the relational structures do
not install global `DecidableEq` instances. -/
def coinEq (a b : Coin) : Bool :=
  a.asset == b.asset && a.value == b.value && a.owner == b.owner && a.r == b.r

theorem coinEq_eq_true {a b : Coin} : coinEq a b = true ↔ a = b := by
  constructor
  · cases a with
    | mk aa av ao ar =>
      cases b with
      | mk ba bv bo br =>
        simp only [coinEq, Bool.and_eq_true, beq_iff_eq]
        rintro ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
        rfl
  · rintro rfl
    simp [coinEq]

def containsCoin (coins : List Coin) (coin : Coin) : Bool :=
  coins.any (coinEq coin)

theorem containsCoin_eq_true {coins : List Coin} {coin : Coin} :
    containsCoin coins coin = true ↔ coin ∈ coins := by
  simp only [containsCoin, List.any_eq_true]
  constructor
  · rintro ⟨candidate, hmem, heq⟩
    exact coinEq_eq_true.mp heq ▸ hmem
  · intro hmem
    exact ⟨coin, hmem, coinEq_eq_true.mpr rfl⟩

theorem containsCoin_eq_false {coins : List Coin} {coin : Coin} :
    containsCoin coins coin = false ↔ coin ∉ coins := by
  rw [← Bool.not_eq_true, containsCoin_eq_true]

def live {B : Backend} (trace : List (Step B)) (coin : Coin) : Bool :=
  containsCoin (produced trace) coin && !containsCoin (consumed trace) coin

theorem live_eq_true {B : Backend} {trace : List (Step B)} {coin : Coin} :
    live trace coin = true ↔ coin ∈ produced trace ∧ coin ∉ consumed trace := by
  simp [live, containsCoin_eq_true, containsCoin_eq_false]

def assets (coins : List Coin) : List F := coins.map Coin.asset

/-- It is enough to check conservation on the finite support of the two coin
lists; every other asset has value zero on both sides. -/
def balanced (outputs inputs : List Coin) : Bool :=
  (assets (outputs ++ inputs)).all
    (fun asset => valueOf asset outputs == valueOf asset inputs)

theorem valueOf_eq_zero_of_not_mem {asset : F} {coins : List Coin}
    (h : asset ∉ assets coins) : valueOf asset coins = 0 := by
  induction coins with
  | nil => rfl
  | cons coin coins ih =>
    simp only [assets, List.map_cons, List.mem_cons, not_or] at h
    have hne : coin.asset ≠ asset := fun heq => h.1 heq.symm
    simp [valueOf, hne, ih h.2]

theorem balanced_eq_true {outputs inputs : List Coin} :
    balanced outputs inputs = true ↔
      ∀ asset : F, valueOf asset outputs = valueOf asset inputs := by
  constructor
  · intro h asset
    by_cases hmem : asset ∈ assets (outputs ++ inputs)
    · have hall := (List.all_eq_true.mp h) asset hmem
      exact (beq_iff_eq.mp hall)
    · have hsplit : asset ∉ assets outputs ∧ asset ∉ assets inputs := by
        simpa [assets, List.map_append] using hmem
      rw [valueOf_eq_zero_of_not_mem hsplit.1, valueOf_eq_zero_of_not_mem hsplit.2]
  · intro h
    apply List.all_eq_true.mpr
    intro asset _
    exact beq_iff_eq.mpr (h asset)

/-- Typed rejection surface of the executable model. -/
inductive Error where
  | invalidSignature
  | unbalancedMint
  | wrongAsset
  | wrongOwner
  | wrongNullifier
  | coinNotLive
  | unbalancedValue
  | wrongRedeemValue
  deriving Repr, DecidableEq

def checkSpend (B : Backend) (spend : Spend) : Except Error Unit :=
  if B.ownerKey spend.osk = spend.coin.owner then
    if B.nullHash spend.osk (B.commitHash spend.coin) = spend.nf then .ok ()
    else .error .wrongNullifier
  else .error .wrongOwner

def checkSpends (B : Backend) : List Spend → Except Error Unit
  | [] => .ok ()
  | spend :: spends =>
      match checkSpend B spend with
      | .error error => .error error
      | .ok _ => checkSpends B spends

def checkLive {B : Backend} (trace : List (Step B)) : List Spend → Except Error Unit
  | [] => .ok ()
  | spend :: spends =>
      if live trace spend.coin = true then checkLive trace spends
      else .error .coinNotLive

/-- Decidable transition check against the predecessor trace. -/
def checkStep (B : Backend) (trace : List (Step B)) : Step B → Except Error Unit
  | .mint asset V nonce σ outputs =>
      if B.sigVerify asset.ipk ⟨B.assetId asset, V, nonce⟩ σ = true then
        if V = totalValue outputs then
          if outputs.all (fun coin => coin.asset == B.assetId asset) = true then .ok ()
          else .error .wrongAsset
        else .error .unbalancedMint
      else .error .invalidSignature
  | .transfer spends outputs _ => do
      match checkSpends B spends with
      | .error error => .error error
      | .ok _ =>
        match checkLive trace spends with
        | .error error => .error error
        | .ok _ =>
          if balanced outputs (spends.map Spend.coin) = true then .ok ()
          else .error .unbalancedValue
  | .redeem spend V _ =>
      match checkSpend B spend with
      | .error error => .error error
      | .ok _ =>
        match checkLive trace [spend] with
        | .error error => .error error
        | .ok _ =>
          if V = spend.coin.value then .ok () else .error .wrongRedeemValue

def runAux (B : Backend) (pre : List (Step B)) : List (Step B) → Except Error Unit
  | [] => .ok ()
  | step :: tail =>
      match checkStep B pre step with
      | .error error => .error error
      | .ok _ => runAux B (pre ++ [step]) tail

/-- Run a trace left-to-right, returning its first typed error. -/
def run (B : Backend) (steps : List (Step B)) : Except Error Unit :=
  runAux B [] steps

/-! ## Refinement bridge to the relational state machine -/

/-- Evidence that a runnable backend implements the opaque functions used by
`State.lean`.  These are hypotheses, not new axioms. -/
structure Refines (B : Backend) where
  embedSig : B.SigRep → OpenCsv.Sig
  assetId_eq : ∀ asset, B.assetId asset = OpenCsv.assetId asset
  commitHash_eq : ∀ coin, B.commitHash coin = OpenCsv.commitHash coin
  ownerKey_eq : ∀ osk, B.ownerKey osk = OpenCsv.ownerKey osk
  nullHash_eq : ∀ osk commitment,
    B.nullHash osk commitment = OpenCsv.nullHash osk commitment
  sigVerify_eq : ∀ ipk msg σ,
    B.sigVerify ipk msg σ = OpenCsv.SigVerify ipk msg (embedSig σ)

def Spend.erase (spend : Spend) : OpenCsv.Spend :=
  ⟨spend.coin, spend.osk, spend.nf⟩

def Step.erase {B : Backend} (R : Refines B) : Step B → OpenCsv.Step
  | .mint asset V nonce σ outputs =>
      .mint asset V nonce (R.embedSig σ) outputs
  | .transfer spends outputs ctx =>
      .transfer (spends.map Spend.erase) outputs ctx
  | .redeem spend V ctx => .redeem spend.erase V ctx

theorem erase_outputs {B : Backend} (R : Refines B) (step : Step B) :
    (step.erase R).outputs = step.outputs := by
  cases step <;> rfl

theorem erase_spends {B : Backend} (R : Refines B) (step : Step B) :
    (step.erase R).spends = step.spends.map Spend.erase := by
  cases step <;> rfl

theorem erase_consumed {B : Backend} (R : Refines B) (step : Step B) :
    (step.erase R).consumed = step.spends.map Spend.coin := by
  cases step <;>
    simp [Step.erase, Step.spends, OpenCsv.Step.consumed, OpenCsv.Step.spends,
      Spend.erase, Function.comp_def]

theorem produced_erase {B : Backend} (R : Refines B) (trace : List (Step B)) :
    OpenCsv.produced (trace.map (Step.erase R)) = produced trace := by
  induction trace with
  | nil => rfl
  | cons step trace ih => simp [OpenCsv.produced, produced, erase_outputs, ih]

theorem consumed_erase {B : Backend} (R : Refines B) (trace : List (Step B)) :
    OpenCsv.consumed (trace.map (Step.erase R)) = consumed trace := by
  induction trace with
  | nil => rfl
  | cons step trace ih =>
    simp [OpenCsv.consumed, consumed, erase_consumed, ih]

theorem checkSpend_sound {B : Backend} (R : Refines B) {spend : Spend}
    (h : checkSpend B spend = .ok ()) : spend.erase.wellFormed := by
  simp only [checkSpend] at h
  split at h
  next howner =>
    split at h
    next hnf =>
      simp only [Spend.erase, OpenCsv.Spend.wellFormed]
      constructor
      · rw [← R.ownerKey_eq]
        exact howner
      · rw [← R.commitHash_eq, ← R.nullHash_eq]
        exact hnf.symm
    next => contradiction
  next => contradiction

theorem checkSpends_sound {B : Backend} (R : Refines B) {spends : List Spend}
    (h : checkSpends B spends = .ok ()) :
    ∀ spend ∈ spends, spend.erase.wellFormed := by
  induction spends with
  | nil => simp
  | cons spend spends ih =>
    simp only [checkSpends] at h
    cases hs : checkSpend B spend with
    | error error => simp [checkSpends, hs] at h
    | ok value =>
      cases value
      simp only [hs] at h
      intro candidate hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact checkSpend_sound R hs
      · exact ih h candidate hmem

theorem checkLive_sound {B : Backend} (R : Refines B) {trace : List (Step B)}
    {spends : List Spend} (h : checkLive trace spends = .ok ()) :
    ∀ spend ∈ spends, OpenCsv.Live (trace.map (Step.erase R)) spend.coin := by
  induction spends with
  | nil => simp
  | cons spend spends ih =>
    simp only [checkLive] at h
    split at h
    next hlive =>
      intro candidate hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · rw [OpenCsv.Live, produced_erase, consumed_erase]
        exact live_eq_true.mp hlive
      · exact ih h candidate hmem
    next => contradiction

theorem checkStep_sound {B : Backend} (R : Refines B) {trace : List (Step B)}
    {step : Step B} (h : checkStep B trace step = .ok ()) :
    OpenCsv.StepValid (trace.map (Step.erase R)) (step.erase R) := by
  cases step with
  | mint asset V nonce σ outputs =>
    simp only [checkStep] at h
    split at h
    next hsig =>
      split at h
      next hvalue =>
        split at h
        next hassets =>
          simp only [Step.erase, OpenCsv.StepValid]
          constructor
          · rw [R.assetId_eq] at hsig
            rw [← R.sigVerify_eq]
            exact hsig
          constructor
          · exact hvalue
          · intro coin hmem
            have hall := (List.all_eq_true.mp hassets) coin hmem
            rw [← R.assetId_eq]
            exact beq_iff_eq.mp hall
        next => contradiction
      next => contradiction
    next => contradiction
  | transfer spends outputs ctx =>
    simp only [checkStep] at h
    cases hs : checkSpends B spends with
    | error error => simp [checkStep, hs] at h
    | ok value =>
      cases value
      simp only [hs] at h
      cases hl : checkLive trace spends with
      | error error => simp [checkStep, hs, hl] at h
      | ok value =>
        cases value
        simp only [hl] at h
        split at h
        next hbalance =>
          simp only [Step.erase, OpenCsv.StepValid, List.map_map]
          refine ⟨?_, ?_, ?_⟩
          · intro erasedSpend hmem
            simp only [List.mem_map] at hmem
            obtain ⟨spend, hmem, rfl⟩ := hmem
            exact checkSpends_sound R hs spend hmem
          · intro erasedSpend hmem
            simp only [List.mem_map] at hmem
            obtain ⟨spend, hmem, rfl⟩ := hmem
            exact checkLive_sound R hl spend hmem
          · simpa [Function.comp_def, Spend.erase] using balanced_eq_true.mp hbalance
        next => contradiction
  | redeem spend V ctx =>
    simp only [checkStep] at h
    cases hs : checkSpend B spend with
    | error error => simp [checkStep, hs] at h
    | ok value =>
      cases value
      simp only [hs] at h
      cases hl : checkLive trace [spend] with
      | error error => simp [checkStep, hs, hl] at h
      | ok value =>
        cases value
        simp only [hl] at h
        split at h
        next hvalue =>
          simp only [Step.erase, OpenCsv.StepValid]
          refine ⟨checkSpend_sound R hs, ?_, hvalue⟩
          exact checkLive_sound R hl spend (List.mem_singleton_self spend)
        next => contradiction

theorem runAux_sound {B : Backend} (R : Refines B) (pre remaining : List (Step B))
    (hp : OpenCsv.ValidTrace (pre.map (Step.erase R)))
    (h : runAux B pre remaining = .ok ()) :
    OpenCsv.ValidTrace ((pre ++ remaining).map (Step.erase R)) := by
  induction remaining generalizing pre with
  | nil => simpa using hp
  | cons step remaining ih =>
    simp only [runAux] at h
    cases hs : checkStep B pre step with
    | error error => simp [runAux, hs] at h
    | ok value =>
      cases value
      simp only [hs] at h
      have hp' : OpenCsv.ValidTrace ((pre ++ [step]).map (Step.erase R)) := by
        rw [List.map_append]
        exact OpenCsv.ValidTrace.snoc hp (checkStep_sound R hs)
      simpa [List.append_assoc] using ih (pre ++ [step]) hp' h

/-- Soundness bridge: every trace accepted by the executable interpreter is
a `ValidTrace` after refinement into the existing relational model. -/
theorem run_sound {B : Backend} (R : Refines B) (trace : List (Step B))
    (h : run B trace = .ok ()) :
    OpenCsv.ValidTrace (trace.map (Step.erase R)) := by
  exact runAux_sound R [] trace OpenCsv.ValidTrace.nil h

#print axioms run_sound

end OpenCsv.Exec
