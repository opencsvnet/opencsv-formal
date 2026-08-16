import OpenCsv.Exec

/-!
# Deterministic model-differential corpus generator

The JSON writer is intentionally tiny and dependency-free.  Every case is
derived from one fixed LCG seed.  The emitted scalar seeds are expanded by the
Rust harness into production byte types and exercised through the real
`opencsv_core::accept` driver.
-/

namespace OpenCsv.Corpus

open OpenCsv Exec

private def modulus : Nat := 4294967296

structure PRNG where
  state : Nat

def PRNG.next (g : PRNG) : Nat × PRNG :=
  let next := (1664525 * g.state + 1013904223) % modulus
  (next, ⟨next⟩)

def PRNG.below (g : PRNG) (upper : Nat) : Nat × PRNG :=
  let (word, g') := g.next
  (word % upper, g')

private def mix (a b : Nat) : Nat :=
  (a * 16777619 + b * 2166136261 + 97) % 2147483647

def concreteBackend : Exec.Backend where
  SigRep := Nat
  assetId := fun asset => mix (mix asset.ipk asset.currency) (mix asset.termsHash asset.nonce)
  commitHash := fun coin =>
    mix (mix coin.asset coin.value) (mix coin.owner coin.r)
  ownerKey := fun osk => mix osk 17
  nullHash := fun osk commitment => mix (mix osk commitment) 23
  sigVerify := fun ipk msg σ => σ == mix (mix ipk msg.asset) (mix msg.value msg.nonce)

def signature (asset : Asset) (V nonce : Nat) : Nat :=
  mix (mix asset.ipk (concreteBackend.assetId asset)) (mix V nonce)

inductive Class where
  | valid
  | unbalancedValue
  | wrongOwner
  | reusedNullifier
  | badAnchor
  | missingAnchor
  deriving DecidableEq

def Class.name : Class → String
  | .valid => "valid"
  | .unbalancedValue => "unbalanced_value"
  | .wrongOwner => "wrong_owner"
  | .reusedNullifier => "reused_nullifier"
  | .badAnchor => "bad_anchor"
  | .missingAnchor => "missing_anchor"

structure Case where
  id : Nat
  mutation : Class
  caseSeed : Nat
  issuerSeed : Nat
  termsSeed : Nat
  senderSeed : Nat
  recipientSeed : Nat
  randomnessSeed : Nat
  value : Nat

def makeCase (id : Nat) (mutation : Class) (g : PRNG) : Case × PRNG :=
  let (caseSeed, g) := g.next
  let (issuerSeed, g) := g.below 251
  let (termsSeed, g) := g.below 251
  let (senderSeed, g) := g.below 251
  let (recipientDelta, g) := g.below 249
  let (randomnessSeed, g) := g.below 251
  let (valueDelta, g) := g.below 1000000
  let recipientSeed := (senderSeed + recipientDelta + 1) % 251
  (⟨id, mutation, caseSeed, issuerSeed + 1, termsSeed + 1, senderSeed + 1,
      recipientSeed + 1, randomnessSeed + 1, valueDelta + 1⟩, g)

def makeTrace (c : Case) : List (Exec.Step concreteBackend) :=
  let asset : Asset :=
    ⟨c.issuerSeed, 840, c.termsSeed, c.caseSeed⟩
  let assetId := concreteBackend.assetId asset
  let senderOwner := concreteBackend.ownerKey c.senderSeed
  let recipientOwner := concreteBackend.ownerKey c.recipientSeed
  let minted : Coin := ⟨assetId, c.value, senderOwner, c.randomnessSeed⟩
  let transferredValue := if c.mutation = .unbalancedValue then c.value + 1 else c.value
  let received : Coin := ⟨assetId, transferredValue, recipientOwner, c.randomnessSeed + 1⟩
  let spendSecret := if c.mutation = .wrongOwner then c.senderSeed + 1 else c.senderSeed
  let mintSpend : Exec.Spend :=
    ⟨minted, spendSecret,
      concreteBackend.nullHash c.senderSeed (concreteBackend.commitHash minted)⟩
  let receiveSpend : Exec.Spend :=
    ⟨received, c.recipientSeed,
      concreteBackend.nullHash c.recipientSeed (concreteBackend.commitHash received)⟩
  let mint : Exec.Step concreteBackend :=
    .mint asset c.value c.caseSeed (signature asset c.value c.caseSeed) [minted]
  let transfer : Exec.Step concreteBackend := .transfer [mintSpend] [received] (c.caseSeed + 1)
  if c.mutation = .reusedNullifier then
    let replayOut : Coin := ⟨assetId, c.value, recipientOwner, c.randomnessSeed + 2⟩
    [mint, transfer, .transfer [mintSpend] [replayOut] (c.caseSeed + 2)]
  else
    [mint, transfer, .redeem receiveSpend transferredValue (c.caseSeed + 2)]

def expectedRun : Class → Except Exec.Error Unit
  | .valid | .badAnchor | .missingAnchor => .ok ()
  | .unbalancedValue => .error .unbalancedValue
  | .wrongOwner => .error .wrongOwner
  | .reusedNullifier => .error .coinNotLive

def resultEq : Except Exec.Error Unit → Except Exec.Error Unit → Bool
  | .ok _, .ok _ => true
  | .error a, .error b => a == b
  | _, _ => false

def validateCase (c : Case) : Bool :=
  resultEq (Exec.run concreteBackend (makeTrace c)) (expectedRun c.mutation)

def classAt (id : Nat) : Class :=
  match id % 6 with
  | 0 => .valid
  | 1 => .unbalancedValue
  | 2 => .wrongOwner
  | 3 => .reusedNullifier
  | 4 => .badAnchor
  | _ => .missingAnchor

def generateLoop : Nat → Nat → PRNG → List Case → List Case × PRNG
  | 0, _, g, acc => (acc.reverse, g)
  | remaining + 1, id, g, acc =>
      let mutation := classAt id
      let (c, g') := makeCase id mutation g
      generateLoop remaining (id + 1) g' (c :: acc)

/-- The checked-in corpus has 32 cases in each of six classes. -/
def generate : List Case :=
  (generateLoop 192 0 ⟨0x4f50454e⟩ []).1

def expectedAccept (mutation : Class) : Bool := mutation = .valid

def proofValid (mutation : Class) : Bool :=
  mutation != .unbalancedValue && mutation != .wrongOwner

def anchorMode : Class → String
  | .badAnchor => "bad"
  | .missingAnchor => "missing"
  | .reusedNullifier => "reused"
  | _ => "valid"

def traceShape : Class → String
  | .reusedNullifier => "genesis_mint_transfer_transfer_reuse"
  | _ => "genesis_mint_transfer_redeem"

def boolJson (b : Bool) : String := if b then "true" else "false"

def caseJson (c : Case) : String :=
  "{" ++
  s!"\"id\":{c.id}," ++
  s!"\"class\":\"{c.mutation.name}\"," ++
  s!"\"trace_shape\":\"{traceShape c.mutation}\"," ++
  s!"\"case_seed\":{c.caseSeed}," ++
  s!"\"issuer_seed\":{c.issuerSeed}," ++
  s!"\"terms_seed\":{c.termsSeed}," ++
  s!"\"sender_seed\":{c.senderSeed}," ++
  s!"\"recipient_seed\":{c.recipientSeed}," ++
  s!"\"randomness_seed\":{c.randomnessSeed}," ++
  s!"\"value\":{c.value}," ++
  s!"\"proof_valid\":{boolJson (proofValid c.mutation)}," ++
  s!"\"anchor_mode\":\"{anchorMode c.mutation}\"," ++
  s!"\"expected_accept\":{boolJson (expectedAccept c.mutation)}" ++
  "}"

def corpusJson (cases : List Case) : String :=
  "{\"schema\":1,\"generator_seed\":1330660686,\"cases\":[" ++
    String.intercalate "," (cases.map caseJson) ++ "]}\n"

def allValid (cases : List Case) : Bool := cases.all validateCase

def runMain (args : List String) : IO Unit := do
  let cases := generate
  unless allValid cases do
    throw <| IO.userError "internal executable-model expectation failed"
  match args with
  | [] => IO.print (corpusJson cases)
  | [path] => IO.FS.writeFile path (corpusJson cases)
  | _ => throw <| IO.userError "usage: lake exe gen-model-corpus [output.json]"

end OpenCsv.Corpus

def main (args : List String) : IO Unit := OpenCsv.Corpus.runMain args
