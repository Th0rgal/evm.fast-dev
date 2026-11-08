import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase2Strong

/-!
# Wave 8 / R16k closer: the `h12` Phase 1 × Phase 2 backing composition

`R16Shards.PtxPhase34R11.gbody_process_transaction_backing_strong_of_h12`
(line 9679) reduces the backing-aware `process_transaction` export to the `h12`
hypothesis:

```
∀ tail b, TerminatingProgBoundedOn
    (fun s => (PtxMessageReady s ∧ TxBacking s) ∧ PtxPhase4LocalShapes s) tail b →
  TerminatingProgBoundedOn TxReadyBackingStrong (ptxPhase1 (ptxPhase2 tail))
    (ptxCost1 + (ptxCost2 + b))
```

`ptxPhase2 tail = spinePlug 64 (spineAt 34 ptxCode) tail` covers guest spine
positions 34..98. This file decomposes `h12` along the wave's file boundaries
and discharges the composition exactly:

* **Phase 1 (spine 0..34)**, the scope of `PtxPhase2Strong.ptxPhase1_cut_strong`
  (line 948), strengthened to thread `TxBacking` through the seventeen Phase 1
  callee steps: `PtxPhase1BackingCut`.
* **Phase 2 (spine 34..98)**, the composed scope of `PtxPhase2Strong`
  (34..77: the allocation entry `te_new`/`tx_has_access_list` region, the count
  loop at 48 and the packing copy loop at 51, the blob/setcode/keccak region and
  `msg_new` at 69), `PtxPhase2StrongTail` (77..87: `htab_new` for the message
  accesses table, the `htab_set` WHILEs at spine 82/84, the auth-key `htab_new`
  at 86) and `PtxPhase2StrongTail2` (87..98: the auth-key table WHILE at 88, the
  `alloc` at 90, the `get_account` vs `alloc`+`compute_contract_address` ite at
  91, and the receipts stores through 98): `PtxPhase2BackingCut`.

The two cuts compose definitionally: the Phase 2 cut's postcondition
`PtxValidatedBackingStrong` at spine 34 is exactly the Phase 1 cut's
precondition, and the budget splits as `ptxCost1 + (ptxCost2 + b)`
(`ptxPhase12_cost_split`). Hence `ptxPhase12_backing_strong_of_cuts` is the
full `h12`. Feeding it to the existing `PtxCallees` machinery
(`R16Shards.gbody_process_transaction_backing_strong_of_h12`, line 9679, with
`resume_pmc_backing` discharging the message-call resume) closes the
backing-aware transaction export modulo the Phase 4 cut `h4`
(`gbody_process_transaction_backing_strong_pmc_of_cuts`).

The non-backing companion `ptxPhase12_strong_of_phase2_cut` composes a
non-backing Phase 2 cut with the *proved* `ptxPhase1_cut_strong`, so only the
Phase 2 side remains an integration obligation there.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.R13Shards

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.Wave8GuestInv.R16Shards

/-! ### Guards -/

/-- Phase 2 entry guard at guest spine 34: `PtxValidatedStrong` with the two
block-out list data pointers live (`TxBacking`,
`R16Shards/PtxPhase34R11.55`). This is the postcondition the Phase 2 cut hands
to the Phase 1 cut. -/
def PtxValidatedBackingStrong : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => PtxValidatedStrong s ∧ TxBacking s

/-- The `h12` tail guard at guest spine 98: message-ready with backing and the
Phase 4 local shapes (`R16Shards/PtxPhase34R11.134`). This is the guard of the
tail handed to `ptxPhase2` by `ptxPhase345_cut_pmc_backing_strong_cutover`. -/
def PtxTailBackingGuard : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => (PtxMessageReady s ∧ TxBacking s) ∧ PtxPhase4LocalShapes s

/-- `PtxTailBackingGuard` is definitionally the hypothesis guard of `h12`. -/
theorem ptxTailBackingGuard_iff {F : Type} (s : PanSemStateFiniteExact 64 F) :
    PtxTailBackingGuard s ↔ (PtxMessageReady s ∧ TxBacking s) ∧ PtxPhase4LocalShapes s :=
  Iff.rfl

/-- `PtxValidatedBackingStrong` strengthens `PtxValidatedStrong` by exactly the
`TxBacking` conjunct that `h12` threads. -/
theorem ptxValidatedBackingStrong_iff {F : Type} (s : PanSemStateFiniteExact 64 F) :
    PtxValidatedBackingStrong s ↔ PtxValidatedStrong s ∧ TxBacking s :=
  Iff.rfl

/-! ### The two backing cuts -/

/-- **Phase 1 backing cut** (spine 0..34): `ptxPhase1_cut_strong`
(`PtxPhase2Strong.948`, proved) strengthened to thread `TxBacking` from the
entry guard through the seventeen Phase 1 callee steps
(`state_fresh_tx`, `encode_transaction`, `tx_chain_id`, `alloc`,
`recover_sender_with_chain_id`, `validate_transaction`, `check_transaction`,
`calculate_total_blob_gas`, `get_account`, `calculate_blob_gas_price`,
`fee_mul`, `min`, `increment_nonce`, `u256_sub`, `set_account_balance`) to
`TxReadyBackingStrong`. -/
def PtxPhase1BackingCut : Prop :=
  ∀ (tail : ProgHOL 64) (b : Nat),
    TerminatingProgBoundedOn PtxValidatedBackingStrong tail b →
    TerminatingProgBoundedOn TxReadyBackingStrong (ptxPhase1 tail) (ptxCost1 + b)

/-- **Phase 2 backing cut** (spine 34..98): the composed scope of
`PtxPhase2Strong` (34..77), `PtxPhase2StrongTail` (77..87) and
`PtxPhase2StrongTail2` (87..98). The `TxBacking` conjunct is threaded from
`msg_new` at spine 69 onward (the `PtxB2aQ`-style region), through the
`htab_set` WHILEs at 82/84 and 88 and the ite at 91, back to spine 34. -/
def PtxPhase2BackingCut : Prop :=
  ∀ (tail : ProgHOL 64) (b : Nat),
    TerminatingProgBoundedOn PtxTailBackingGuard tail b →
    TerminatingProgBoundedOn PtxValidatedBackingStrong (ptxPhase2 tail) (ptxCost2 + b)

/-- The full R16k integration obligation for `h12`, as one `Prop`. -/
structure PtxPhase12BackingCuts : Prop where
  phase1 : PtxPhase1BackingCut
  phase2 : PtxPhase2BackingCut

/-- The `h12` budget splits exactly at the Phase 1 / Phase 2 boundary. -/
theorem ptxPhase12_cost_split (b : Nat) :
    ptxCost1 + (ptxCost2 + b) = (ptxCost1 + ptxCost2) + b := by omega

/-! ### Guard adapters -/

/-- Guard adapter for the Phase 1 cut: a cut proved under a stronger entry guard
`G` (every `G`-state validates with backing) is a `PtxPhase1BackingCut`. -/
theorem ptxPhase1BackingCut_of_guard
    (G : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (hG : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), G s → PtxValidatedBackingStrong s)
    (hp1 : ∀ (tail : ProgHOL 64) (b : Nat),
      TerminatingProgBoundedOn G tail b →
      TerminatingProgBoundedOn TxReadyBackingStrong (ptxPhase1 tail) (ptxCost1 + b)) :
    PtxPhase1BackingCut :=
  fun tail b ht => hp1 tail b (PtxP1.bound_mono ht hG)

/-- Guard adapter for the Phase 2 cut: a cut proved under a stronger tail guard
`G` (every `G`-state is an `h12` tail-guard state) is a `PtxPhase2BackingCut`. -/
theorem ptxPhase2BackingCut_of_guard
    (G : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (hG : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), G s → PtxTailBackingGuard s)
    (hp2 : ∀ (tail : ProgHOL 64) (b : Nat),
      TerminatingProgBoundedOn G tail b →
      TerminatingProgBoundedOn PtxValidatedBackingStrong (ptxPhase2 tail) (ptxCost2 + b)) :
    PtxPhase2BackingCut :=
  fun tail b ht => hp2 tail b (PtxP1.bound_mono ht hG)

/-! ### The composition -/

/-- **The `h12` closer**: compose the Phase 1 and Phase 2 backing cuts into the
exact `h12` hypothesis of
`R16Shards.gbody_process_transaction_backing_strong_of_h12_cutover`. The Phase 2
cut's postcondition `PtxValidatedBackingStrong` at spine 34 is precisely the
Phase 1 cut's precondition, and the budget splits as
`ptxCost1 + (ptxCost2 + b)`. -/
theorem ptxPhase12_backing_strong_of_cuts
    (hp1 : PtxPhase1BackingCut) (hp2 : PtxPhase2BackingCut) :
    ∀ (tail : ProgHOL 64) (b : Nat),
      TerminatingProgBoundedOn
        (fun s => (PtxMessageReady s ∧ TxBacking s) ∧ PtxPhase4LocalShapes s) tail b →
      TerminatingProgBoundedOn TxReadyBackingStrong (ptxPhase1 (ptxPhase2 tail))
        (ptxCost1 + (ptxCost2 + b)) :=
  fun tail b ht => hp1 (ptxPhase2 tail) (ptxCost2 + b) (hp2 tail b ht)

/-- Bundled form of `ptxPhase12_backing_strong_of_cuts`. -/
theorem ptxPhase12_backing_strong (hc : PtxPhase12BackingCuts) :
    ∀ (tail : ProgHOL 64) (b : Nat),
      TerminatingProgBoundedOn
        (fun s => (PtxMessageReady s ∧ TxBacking s) ∧ PtxPhase4LocalShapes s) tail b →
      TerminatingProgBoundedOn TxReadyBackingStrong (ptxPhase1 (ptxPhase2 tail))
        (ptxCost1 + (ptxCost2 + b)) :=
  ptxPhase12_backing_strong_of_cuts hc.phase1 hc.phase2

/-- Non-backing companion: a plain (non-`TxBacking`-threading) Phase 2 cut
composes with the *proved* `ptxPhase1_cut_strong` (`PtxPhase2Strong.948`) to
give the `TxReadyStrong` (non-backing) `h12`. Only the Phase 2 side is an
integration obligation here; the Phase 1 side is fully discharged. -/
theorem ptxPhase12_strong_of_phase2_cut (h : PtxCallees)
    (hp2 : ∀ (tail : ProgHOL 64) (b : Nat),
      TerminatingProgBoundedOn (fun s => PtxMessageReady s ∧ PtxPhase4LocalShapes s) tail b →
      TerminatingProgBoundedOn PtxValidatedStrong (ptxPhase2 tail) (ptxCost2 + b)) :
    ∀ (tail : ProgHOL 64) (b : Nat),
      TerminatingProgBoundedOn (fun s => PtxMessageReady s ∧ PtxPhase4LocalShapes s) tail b →
      TerminatingProgBoundedOn TxReadyStrong (ptxPhase1 (ptxPhase2 tail))
        (ptxCost1 + (ptxCost2 + b)) :=
  fun tail b ht => ptxPhase1_cut_strong h (hp2 tail b ht)

/-! ### Transaction export -/

/-- Full backing-aware transaction export over `PtxCallees`: the two cuts give
`h12`, `resume_pmc_backing` discharges the message-call backing resume, and the
Phase 4 cut `h4` remains an explicit integration obligation, exactly as in
`R16Shards.gbody_process_transaction_backing_strong_of_h12` (line 9679). -/
theorem gbody_process_transaction_backing_strong_pmc_of_cuts
    (h : PtxCallees) (hwk : PtxP34.PmcStrong) (hkeep : PmcBackingStrong)
    (hp1 : PtxPhase1BackingCut) (hp2 : PtxPhase2BackingCut)
    (h4 : ∀ (tail : ProgHOL 64) (b : Nat),
      TerminatingProgBoundedOn PtxReceiptsDone tail b →
      TerminatingProgBoundedOn (fun s => TxAfterCallBackingStrong s ∧ PtxPhase4LocalShapes s)
        (ptxPhase4 tail) (ptxCost4 + b)) :
    TerminatingFunBoundedOn TxReadyBackingStrong (ofString "process_transaction")
      K.«process_transaction» :=
  gbody_process_transaction_backing_strong_of_h12 h hwk (resume_pmc_backing hkeep)
    (ptxPhase12_backing_strong_of_cuts hp1 hp2) h4

end InitECandidate.Solver.Wave8GuestInv.R13Shards
