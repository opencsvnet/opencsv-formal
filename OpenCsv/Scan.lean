import OpenCsv.State

/-!
# Scan-first anchoring: the indexing model (paper §4.7.1, amended)

Production indexing is **scan-first**: anchor-carrying transactions include a
protocol-constant *marker script*, so BIP158-style compact filters
(`opencsv-cbf`) can identify anchor-bearing blocks; the wallet downloads only
the candidate blocks and evaluates occurrences locally against the
bound-payload rule `P = H(raw_nf, ctx)` of `Interfaces.lean`. This module
closes the gap between that deployment and the single-log acceptance model of
`Theorems.lean`: it proves that a local scan over a filter-built index is
sound and complete for on-chain occurrences — **with no new cryptographic
assumptions** (the marker/filter machinery is pure set reasoning; the
occurrence rule is unchanged).

Model:

* blocks are abstract: a set of scripts and a set of anchor records
  (`Block`);
* a compact filter is the *image* of the block's scripts under a
  deterministic filter-item map (`mkFilter`) — no-false-negatives then falls
  out of the construction (it is an image-membership lemma);
* the false-positive rate of real Golomb-coded sets is a parameter of the
  deployment, stated here only as a remark: false positives cost bandwidth
  (extra candidate blocks), never correctness, because occurrences are
  re-checked locally against real block records.
-/

namespace OpenCsv.Scan

/-- Output scripts, modeled abstractly as field elements (the protocol
constant marker is one of them). -/
abbrev Script := F

/-- A block, abstractly: the scripts of its transactions and the OpenCSV
anchor records they carry. -/
structure Block where
  /-- All output scripts of the block's transactions. -/
  scripts : List Script
  /-- The block's anchor records `(P, ctx)` (the 64-byte payloads). -/
  records : List AnchorEntry

/-! ## The compact filter and no-false-negatives -/

/-- A BIP158-style compact filter: the image of the block's scripts under
the (deterministic) filter-item map. Real filters hash with SipHash and
Golomb-encode; the model keeps only what the security argument uses — a
deterministic function of the script set. -/
def mkFilter (filterItem : Script → Script) (blk : Block) : List Script :=
  blk.scripts.map filterItem

/-- **No false negatives, by construction.** If the marker script is in the
block, its filter item is in the filter — an image-membership lemma. -/
theorem filter_no_false_negatives (filterItem : Script → Script) (blk : Block)
    (marker : Script) (h : marker ∈ blk.scripts) :
    filterItem marker ∈ mkFilter filterItem blk :=
  List.mem_map.mpr ⟨marker, h, rfl⟩

/-- **Trustless absence (contrapositive).** If the marker's filter item is
absent from the filter, the marker is absent from the block — the wallet
needs no trust in the filter server to *exclude* a block. -/
theorem filter_absence_trustless (filterItem : Script → Script) (blk : Block)
    (marker : Script) (h : filterItem marker ∉ mkFilter filterItem blk) :
    marker ∉ blk.scripts :=
  fun hm => h (filter_no_false_negatives filterItem blk marker hm)

/-! ## Candidates and candidate completeness -/

/-- A block is anchor-bearing when it contains the protocol-constant marker
script (every OpenCSV anchor transaction carries it, by protocol rule). -/
def IsAnchorBearing (marker : Script) (blk : Block) : Prop := marker ∈ blk.scripts

/-- A block is a *candidate* — worth downloading — when the marker's filter
item is in its compact filter. (Candidates may include false positives;
see the module remark.) -/
def IsCandidate (filterItem : Script → Script) (marker : Script) (blk : Block) : Prop :=
  filterItem marker ∈ mkFilter filterItem blk

/-- **Candidate completeness.** Every anchor-bearing block is a candidate:
the filter never hides a block the wallet must see. -/
theorem anchor_bearing_is_candidate (filterItem : Script → Script) (marker : Script)
    (blk : Block) (h : IsAnchorBearing marker blk) : IsCandidate filterItem marker blk :=
  filter_no_false_negatives filterItem blk marker h

/-- Window form of candidate completeness. -/
theorem anchor_bearing_in_window_is_candidate (filterItem : Script → Script) (marker : Script)
    (window : List Block) (blk : Block) (_hmem : blk ∈ window)
    (h : IsAnchorBearing marker blk) : IsCandidate filterItem marker blk :=
  anchor_bearing_is_candidate filterItem marker blk h

/-! ## The index and the headline theorem -/

/-- Candidatehood is decidable (script lists carry decidable equality). -/
instance (filterItem : Script → Script) (marker : Script) (blk : Block) :
    Decidable (IsCandidate filterItem marker blk) :=
  inferInstanceAs (Decidable (filterItem marker ∈ mkFilter filterItem blk))

/-- The wallet's local index over a window `[birth, spend]` (abstracted as a
list of blocks): exactly the records of all candidate blocks in the window. -/
def indexOf (filterItem : Script → Script) (marker : Script) (window : List Block) :
    List AnchorEntry :=
  (window.filter (fun blk => decide (IsCandidate filterItem marker blk))).flatMap Block.records

/-- Semantic on-chain occurrence in a window: a well-formed record for
`raw_nf` in some block (the `OccurrenceAt` of `Theorems.lean`, at block
granularity). -/
def ChainOccurrence (window : List Block) (raw_nf : F) : Prop :=
  ∃ blk ∈ window, ∃ e ∈ blk.records, e.wellFormed raw_nf

/-- Local scan result over the index. -/
def ScanFinds (index : List AnchorEntry) (raw_nf : F) : Prop :=
  ∃ e ∈ index, e.wellFormed raw_nf

/-- **Scan exclusion soundness (headline).** A local scan over the
filter-built index finds an occurrence of `raw_nf` in the window if and only
if one exists on-chain in the window — hence "finds nothing" on both sides
coincide (the exclusion check the wallet actually relies on).

* *Completeness* (⟸): occurrence-carrying blocks are marked (hypothesis
  `hmarked` — the deployment invariant that every anchor transaction carries
  the protocol-constant marker; justified because honest anchoring attaches
  it, and by the anti-grief results a well-formed record for `raw_nf` can
  only be produced by a party that knows `raw_nf`, i.e. a participant
  following the protocol), marked blocks are candidates
  (`anchor_bearing_is_candidate`), and the index contains every candidate's
  records.
* *Correctness* (⟹): the index contains *nothing but* real records of real
  window blocks, so anything the scan finds genuinely occurred on-chain.
  Filter false positives only add extra blocks to the index — they cannot
  fabricate an occurrence, because the record must still sit in a real block
  and pass `wellFormed`. -/
theorem scan_exclusion_sound (filterItem : Script → Script) (marker : Script)
    (window : List Block) (raw_nf : F)
    (hmarked : ∀ blk ∈ window, (∃ e ∈ blk.records, e.wellFormed raw_nf) →
      marker ∈ blk.scripts) :
    ScanFinds (indexOf filterItem marker window) raw_nf ↔ ChainOccurrence window raw_nf := by
  constructor
  · -- Correctness: unpack the index membership back to a real block.
    rintro ⟨e, he, hwf⟩
    rw [indexOf, List.mem_flatMap] at he
    obtain ⟨blk, hblk, he_rec⟩ := he
    rw [List.mem_filter] at hblk
    exact ⟨blk, hblk.1, e, he_rec, hwf⟩
  · -- Completeness: marked → candidate → its records are in the index.
    rintro ⟨blk, hblk, e, he_rec, hwf⟩
    have hcand : IsCandidate filterItem marker blk :=
      anchor_bearing_is_candidate filterItem marker blk
        (hmarked blk hblk ⟨e, he_rec, hwf⟩)
    refine ⟨e, List.mem_flatMap.mpr ⟨blk, ?_, he_rec⟩, hwf⟩
    exact List.mem_filter.mpr ⟨hblk, by rw [decide_eq_true_eq]; exact hcand⟩

/-- Contrapositive (wallet form): the scan excludes `raw_nf` from the window
iff the chain has no occurrence of `raw_nf` in the window. -/
theorem scan_exclusion_sound_iff_absent (filterItem : Script → Script) (marker : Script)
    (window : List Block) (raw_nf : F)
    (hmarked : ∀ blk ∈ window, (∃ e ∈ blk.records, e.wellFormed raw_nf) →
      marker ∈ blk.scripts) :
    ¬ ScanFinds (indexOf filterItem marker window) raw_nf ↔
      ¬ ChainOccurrence window raw_nf := by
  have h := scan_exclusion_sound filterItem marker window raw_nf hmarked
  exact ⟨fun hscan hchain => hscan (h.mpr hchain),
         fun hchain hscan => hchain (h.mp hscan)⟩

/-! ## Marker zero-authority -/

/-- **Marker zero-authority.** A block containing the marker but no
well-formed record for `raw_nf` yields no occurrence of `raw_nf`:
occurrences require the bound record (`P = H(raw_nf, ctx)`); the marker
never enters the occurrence definition — it is a discovery hint with no
authority. -/
theorem marker_zero_authority (blk : Block) (marker : Script) (raw_nf : F)
    (_hmarker : marker ∈ blk.scripts)
    (hnone : ∀ e ∈ blk.records, ¬ e.wellFormed raw_nf) :
    ¬ ∃ e ∈ blk.records, e.wellFormed raw_nf := by
  rintro ⟨e, he, hwf⟩
  exact hnone e he hwf

/-- Window form: markers everywhere, no well-formed records anywhere — no
on-chain occurrence. -/
theorem markers_without_records_no_occurrence (marker : Script) (raw_nf : F)
    (window : List Block)
    (_hallmarked : ∀ blk ∈ window, marker ∈ blk.scripts)
    (hnone : ∀ blk ∈ window, ∀ e ∈ blk.records, ¬ e.wellFormed raw_nf) :
    ¬ ChainOccurrence window raw_nf := by
  rintro ⟨blk, hblk, e, he, hwf⟩
  exact hnone blk hblk e he hwf

/-! ## Accelerator fraud provability -/

/-- Pointwise equality of lookup forces list equality. (Core has this as
`List.ext_getElem?`; proved here to keep the module self-contained.) -/
theorem list_eq_of_getElem?_eq {α : Type} {l₁ l₂ : List α}
    (h : ∀ i : Nat, l₁[i]? = l₂[i]?) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons y ys =>
      have h0 := h 0
      simp at h0
  | cons x xs ih =>
    cases l₂ with
    | nil =>
      have h0 := h 0
      simp at h0
    | cons y ys =>
      have h0 := h 0
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
      have hs : ∀ i : Nat, xs[i]? = ys[i]? := fun i => by
        have hi := h (i + 1)
        simp only [List.getElem?_cons_succ] at hi
        exact hi
      rw [h0, ih hs]

/-- **Accelerator fraud is provable.** An accelerator serves occurrence
lists; `deriveList` is a deterministic function of the block (a function in
the model — determinism by construction). Any served list different from
`deriveList blk` is falsified by exhibiting `blk` and a single index where
the two lists differ: the fraud proof is short and checkable by any third
party that recomputes `deriveList blk`. -/
theorem served_list_falsifiable {α : Type} (deriveList : Block → List α)
    (blk : Block) (l : List α) (h : l ≠ deriveList blk) :
    ∃ i : Nat, l[i]? ≠ (deriveList blk)[i]? :=
  Classical.byContradiction fun hnone =>
    h (list_eq_of_getElem?_eq fun i =>
      Classical.byContradiction fun hne => hnone ⟨i, hne⟩)

/-! ## Axiom audit -/

#print axioms filter_no_false_negatives
#print axioms filter_absence_trustless
#print axioms anchor_bearing_is_candidate
#print axioms scan_exclusion_sound
#print axioms marker_zero_authority
#print axioms served_list_falsifiable

end OpenCsv.Scan
