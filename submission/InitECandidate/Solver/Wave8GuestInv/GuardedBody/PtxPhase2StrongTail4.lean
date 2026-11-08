import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase2StrongTail2
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase2StrongTail3
import InitECandidate.Solver.Wave8GuestInv.R16Shards.PtxPhase34R11
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase2StrongExt

/-!
# Wave 8 / R16k Tail 4: the `h12` closing status and the final compositions

This module is the last file of the `PtxPhase2StrongTail*` chain. It wires the
backing-aware transaction export together as far as the current contract
landscape permits, and records exactly which integration obligations remain
open, with citations.

## What is closed at this point of the chain

* **Phases 3+4+5, unconditionally over the R11 cutover bundle**
  (`R16Shards.PtxCalleesCutover`, defined in
  `R16Shards/PtxPhase34R11Cutover.37`):
  `ptxPhase345_cut_pmc_backing_strong_cutover`,
  `h4_backing_strong_uncond_cutover`, and the export
  `gbody_process_transaction_backing_strong_of_h12_pmc_cutover`
  (`R16Shards/PtxPhase34R11Cutover.3919`) — all with `wk_lst_push`,
  `wk_process_message_call`, and `wk_create_ether` eliminated from the
  callee-contract bundle.
* **The spine 69..98 backing chain** (`TxBacking`-threading):
  `phase2_msgPrefix_backing_bound` (`PtxPhase2Strong.20908`) covers the
  `msg_new` call and its seven message stores (69..77) under
  `PtxMsgPreBInv`; `PtxPhase2StrongTail` covers the `aa`-table `htab_new`
  (77), the `htab_set` WHILEs (82/84) and the `ak`-table `htab_new` (86) under
  `PtxHtabAInv2`/`PtxHtabABInv`; `PtxPhase2StrongTail2.phase2_b2a_bound`
  (`.1745`) covers the `ak`-table WHILE (88), the `alloc` (90), the
  `get_account`/`compute_contract_address` ite (91) and the receipts stores
  through 98, handing back the exact `h12` tail guard
  `(PtxMessageReady ∧ TxBacking) ∧ PtxPhase4LocalShapes`.
* **The five `htab_new` frame lemmas** this wave authored in
  `PtxPhase2StrongExt` (`phase2_htab_new_txEnv`,
  `phase2_htab_new_txBacking`, `phase2_htab_new_live_buffer`,
  `phase2_htab_new_world_disj`, `phase2_p4Shapes_htab_new_aa`): they carry
  `TxEnv`, `TxBacking`, the live-buffer family, world disjointness and the
  Phase 4 local shapes across the `htab_new` callee step from its
  `WorldKeeps`/`Returns` contract, via the `FrameOutside` exit frame of the
  fresh table block.
* **The composition machinery** (`PtxPhase2StrongTail3`): the cut shapes
  `PtxPhase1BackingCut`/`PtxPhase2BackingCut`, the guard adapters, and
  `ptxPhase12_backing_strong_of_cuts`, which composes the two cuts into the
  exact `h12` hypothesis of
  `gbody_process_transaction_backing_strong_of_h12_pmc_cutover`.

## The two remaining integration obligations

### Phase 1 (spine 0..34): the `TxBacking` threading wall

`PtxPhase1BackingCut` requires `TxBacking` to survive the seventeen Phase 1
callee steps (`state_fresh_tx`, `encode_transaction`, `tx_chain_id`, `alloc`,
`recover_sender_with_chain_id`, `validate_transaction`, `check_transaction`,
`calculate_total_blob_gas`, `get_account`, `calculate_blob_gas_price`,
`fee_mul`, `min`, `increment_nonce`, `u256_sub`, `set_account_balance`).
`TxBacking` (`R16Shards/PtxPhase34R11.55`) reads the two block-out list data
words through the `bo` record's pointer fields at offsets 40 and 72. At the
definitional level, `FrameOutside` (`MemoryViews.272`) makes its `keep` list
the *writable* set, and `WorldStep` (`ContractParts/C02.108`) frames the
callee as `FrameOutside s post (worldOwned s S Nd ++ R s ++ [freeGap s])
(heapFree s)`: every `WorldKeeps`-level contract therefore permits writes
anywhere inside the old world-owned region — which contains the block-out
list data objects — so no frame lemma of the `PtxPhase2StrongExt` shape can
be stated for those steps: the pre-call block-out data need not be
preserved. Closing Phase 1 would require authoring a fine frame for each of
the seventeen callees from its actual implementation (the
`phase2_msg_new_fresh_heap` pattern, `PtxPhase2Strong.20483`); the suggested
helper module (`R16Shards/TopGbodyWk/WkPtxPhase1A.lean`) does not exist in
this tree, nor do the previously suggested helpers (at `PtxPhase2Strong`
positions 21001..21503, and `boListHeader_mem_worldOwned`), and the
`WorldStep` frame cannot establish the world-ownedness they would need.
Phase 1 therefore remains an explicit hypothesis of the final composition
below.

### Phase 2 (spine 34..69): the pre-`msg_new` backing bridge

The 69..98 chain is closed, but `phase2_msg_new_txBacking`
(`PtxPhase2Strong.20691`) requires `TxBacking` *before* the `msg_new` call
(`WorldOK ∧ TxEnv ∧ TxBacking → TxBacking`), so the entry guard
`PtxMsgPreBInv` at spine 69 needs the block-out data pointers live at 69.
The existing 34..69 bounds are non-backing:
`phase2_allocationEntry_bound` (`PtxPhase2Strong.2233`, 34..44), the
alloc-packing and warm-cut chain (`PtxPhase2Strong.9921..11601`, 44..53), and
`phase2_teSuf_bound` (`PtxPhase2Strong.20034`, 53..69). Closing the Phase 2
cut requires replaying those segments with `TxBacking` conjoined to each
guard. The callee-side half of that work is now done in this module: every
non-read-only callee in the region (`te_new`, `alloc`, `memzero`,
`memcpy`, `keccak256`) has a fine-frame `TxBacking` preservation lemma below
(the `PtxPhase2StrongExt` treatment of `htab_new` was the template). What
remains is only the guard-side half: replaying the ~2000-line 34..53/53..68
segment bounds with the `TxBacking` conjunct threaded through the
intermediate guards (the copy-loop destination stores still need
disjointness from the block-out data at each store site), and restating the
resulting chain over the cutover bundle. Additionally, the segment
theorems are stated over
the legacy `PtxCallees` bundle; `PtxCalleesCutover` drops the three
unprovable fields, so the `h12` side over the cutover bundle needs the
34..98 chain restated over the surviving fields (the Phase 2 region invokes
none of the three eliminated callees, so the restatement is possible in
principle, but it is not shorter than the original chain).

## What this module proves

* `phase2_backing_entry_adapter`: the first Phase 2 segment (34..44) bounded
  from the backing-strong entry guard — the entry half of the Phase 2 cut,
  with the `TxBacking` conjunct carried (still live, not yet re-verified at
  the segment exits).
* `gbody_process_transaction_backing_strong_pmc_of_cuts_h4closed`: over the
  legacy bundle, both backing cuts plus `PmcStrong`/`PmcBackingStrong` give
  the full backing-aware export with the Phase 4 cut closed
  (`h4_backing_strong_uncond`, `R16Shards/PtxPhase34R11.21486`).
* `gbody_process_transaction_backing_strong_of_cuts_bundled`: the bundled
  form of the final composition — over the legacy `PtxCallees` bundle,
  `PtxPhase12BackingCuts` (the two backing cuts) plus
  `PmcStrong`/`PmcBackingStrong` give the same export with Phase 4 closed
  (`h4_backing_strong_uncond`) via the `h12_pmc` composition. (The R11
  cutover-bundle restatement of commit `0f5882fb4` is not compilable
  against this dependency state, so the composition stays over the legacy
  bundle, which carries strictly more callee fields.)
* `phase2_txBacking_of_fine_frame`: the generic fine-frame `TxBacking`
  preservation bridge — the reusable form of the per-callee lemmas proved in
  `PtxPhase2StrongExt` — which the five per-callee fine frames below compose
  with directly.
* `phase2_te_new_txBacking`: the first of those four fine frames, closed for
  `te_new` (the call at spine 35) from `M27.te_new_body_run` — its only
  memory writes are the 25 zero words of the fresh 200-byte block it
  returns, so the generic bridge applies with an empty keep-set.
* `phase2_alloc_txBacking`: the second of the four fine frames, closed for
  `alloc` (the 34..53 segment's allocator) from `M27.alloc_body_run` — the
  guest body only bumps the `heap_ptr` global and writes no memory at all,
  so the empty keep-set frame is unconditional.
* `phase2_memzero200_txBacking`: the third fine frame and the first with a
  non-empty keep-set, closed for the 200-byte `memzero` from
  `M27.memzero_200_body_run` — the memory effect is exactly `zeroBlock25`
  over `[p, p + 200)`, so `TxBacking` survives whenever that window misses
  the four `bo`-record cells. This is the memory-effect core of the
  `msg_new` bridge (`msg_new` = `alloc` + this zeroing).
* `phase2_keccak256_txBacking`: the fourth fine frame, at the call level —
  the write-set theorem `Keccak256.funByteEff_keccak256` (consumed via
  `Keccak256.call0_byteEff`) confines the callee's writes to the `keccak_st`
  buffer, the `keccak_pad` buffer and the 32-byte output window while
  preserving the globals, so `TxBacking` survives any resumed `keccak256`
  call whose three write windows miss the four `bo`-record cells.
* `phase2_memcpy_txBacking`: the fifth and last fine frame, at the call
  level — the write-set theorem `Keccak256.funByteEff_memcpy` (consumed via
  `Keccak256.call0_byteEff`) confines the callee's writes to the destination
  window `[dst, dst + n)` while preserving the globals, so `TxBacking`
  survives any resumed `memcpy` call whose destination window misses the
  four `bo`-record cells.
* `phase2_teStore_txBacking`: the guard-side companion of the five frames —
  a single store into the fresh transaction-execution record preserves
  `TxBacking`. The `PtxTeStoreReady` guard already owns te-block/world
  disjointness (`IvlsDisj [(te, 200)] (worldOwned s S Nd)`), the `bo` record
  and its two list headers are fixed objects and hence world-owned, and
  `R16Shards.PtxP34.txBacking_store_disjoint_fixed` turns that disjointness
  into backing preservation. This covers the six `phase2_teStores` stores
  that follow the `te_new` call in the 34..69 replay.
* With these five (`te_new`, `alloc`, `memzero`, `keccak256`, `memcpy`), every
  34..69 callee that lacked a fine frame now has one. The remaining Phase 2
  wiring is composing them through the segment chain (guard replay of the
  34..53/53..68 segment bounds with the `TxBacking` conjunct — the te-store
  lemma above is the induction step for the six `phase2_teStores` stores)
  and restating the chain over `PtxCalleesCutover`.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.R13Shards

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R16Shards

/-! ### The generic fine-frame `TxBacking` bridge

`PtxPhase2StrongExt` proves `TxBacking` preservation across `htab_new` by
hand-rolling the frame-to-word reasoning for that callee's specific
keep-set. The two lemmas below package the pattern generically, so that any
future fine frame for a 34..69 callee (`te_new`, `alloc`, `memcpy`,
`keccak256`, each still needing a `phase2_msg_new_fresh_heap`-style spec
proved from the callee's actual code) composes directly with
`phase2_txBacking_of_fine_frame` to preserve `TxBacking` across the call. -/

/-- Any word whose 8-byte cell lies below the old heap top and outside the
callee's keep-set is preserved by a fine `FrameOutside` frame. -/
private theorem memW_eq_of_fine_frame {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {K : List Ivl} {a : Nat}
    (hA : ArenaReady s)
    (hfr : FrameOutside s post K
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr"))
    (hkeep : ∀ i ∈ K, ¬ CellHits a i) (halt : a + 8 ≤ globN s "heap_ptr") :
    memW post a = memW s a := by
  obtain ⟨-, hs_hp, -, -, -, -, -, -, -⟩ := hA.2
  have hlim : heapLimit ≤ 2 ^ 64 := by decide
  have ha_lt : a < 2 ^ 64 := by omega
  have haddr : (BitVec.ofNat 64 a).toNat = a := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]
  have hm : post.memory (BitVec.ofNat 64 a) = s.memory (BitVec.ofNat 64 a) :=
    hfr _ (fun i hi hci => by rw [haddr] at hci; exact hkeep i hi hci)
      (fun hcf => by
        rw [haddr] at hcf
        unfold CellHits at hcf
        obtain ⟨h1, h2⟩ := hcf
        omega)
  unfold memW
  rw [hm]

/-- `TxBacking` is preserved by any callee whose writes a `FrameOutside`
fine frame confines to the keep-set `K` plus the fresh heap growth, provided
the `bo` record's two pointer cells (offsets 40 and 72) and the two
block-out data words they point to all lie below the old heap top and
outside `K`. This is the generic form of the per-callee bridge lemmas in
`PtxPhase2StrongExt` (`phase2_htab_new_txBacking`); composing it with a
`phase2_msg_new_fresh_heap`-style fine frame for each remaining 34..69
callee is exactly the outstanding Phase 2 `TxBacking` bridge. -/
theorem phase2_txBacking_of_fine_frame {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {K : List Ivl}
    (hA : ArenaReady s) (htx : R16Shards.TxBacking s)
    (hbo : globN post "bo" = globN s "bo")
    (hfr : FrameOutside s post K
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr"))
    (hptr : globN s "bo" + 80 ≤ globN s "heap_ptr")
    (hp40 : memW s (globN s "bo" + 40) + 8 ≤ globN s "heap_ptr")
    (hp72 : memW s (globN s "bo" + 72) + 8 ≤ globN s "heap_ptr")
    (hK : ∀ i ∈ K, ¬ CellHits (globN s "bo" + 40) i ∧ ¬ CellHits (globN s "bo" + 72) i ∧
      ¬ CellHits (memW s (globN s "bo" + 40)) i ∧ ¬ CellHits (memW s (globN s "bo" + 72)) i) :
    R16Shards.TxBacking post := by
  have hword : ∀ a : Nat, (∀ i ∈ K, ¬ CellHits a i) → a + 8 ≤ globN s "heap_ptr" →
      memW post a = memW s a := fun _ hk hal => memW_eq_of_fine_frame hA hfr hk hal
  refine R16Shards.txBacking_of_header_words htx hbo ?_ ?_
  · intro k hk
    have hk' : k = 40 ∨ k = 72 := by simpa using hk
    rcases hk' with rfl | rfl
    · exact hword _ (fun i hi => (hK i hi).1) (by omega)
    · exact hword _ (fun i hi => (hK i hi).2.1) (by omega)
  · intro k hk
    have hk' : k = 40 ∨ k = 72 := by simpa using hk
    rcases hk' with rfl | rfl
    · exact hword _ (fun i hi => (hK i hi).2.2.1) hp40
    · exact hword _ (fun i hi => (hK i hi).2.2.2) hp72

/-! ### The `te_new` fine frame

`te_new` is the first call of the 34..44 segment. `M27.te_new_body_run`
(`Deliveries/M27/TeNewSupport.1017`) already establishes that its only
memory writes are the 25 zero words of the fresh 200-byte block it returns
(`post.memory = zeroBlock25 s.memory hp`), so `TxBacking` survives the call
by the generic bridge with an empty keep-set. The `alloc`+`memzero` bodies
of the other 34..69 callees can follow the same pattern via
`M27.alloc_body_run` and `M08.memzero_body_frame`. -/

/-- Every address strictly below `p` or at/above `p + 200` reads the same
word through `zeroBlock25 m p` as through `m`: the 25 zeroed words all sit
in `[p, p + 200)`, and each of them is `p + c` with `c ≤ 192`. -/
private theorem zeroBlock25_keep (m : BitVec 64 → HolWordLab 64) (p a : BitVec 64)
    (hple : p.toNat ≤ 2952790016)
    (ha : a.toNat + 8 ≤ p.toNat ∨ p.toNat + 200 ≤ a.toNat) :
    InitECandidate.Solver.Wave8Contracts.M27.zeroBlock25 m p a = m a := by
  have key : ∀ c : BitVec 64, c.toNat ≤ 192 → a = p + c → False := by
    intro c hcle hc
    have hc1 : a.toNat = p.toNat + c.toNat := by
      rw [hc, BitVec.toNat_add]
      exact Nat.mod_eq_of_lt (by omega)
    rcases ha with ha | ha
    · omega
    · omega
  have ifneg : ∀ {α : Type} (x y : α) (c : BitVec 64), c.toNat ≤ 192 →
      (if a = p + c then x else y) = y := fun x y c hcle =>
    if_neg (fun hc => key c hcle hc)
  have ifneg2 : ∀ {α : Type} (x y : α) (c d : BitVec 64), c.toNat + d.toNat ≤ 192 →
      (if a = p + c + d then x else y) = y := fun x y c d hcd =>
    if_neg (fun hc => key (c + d) (by
        rw [BitVec.toNat_add]
        exact Nat.le_trans (Nat.mod_le _ _) hcd)
      (hc.trans (BitVec.add_assoc p c d)))
  unfold InitECandidate.Solver.Wave8Contracts.M27.zeroBlock25
    InitECandidate.Solver.Wave8Contracts.M27.updW_te
  simp (discharger := decide) only [ifneg, ifneg2]

/-- `TxBacking` is preserved across the `te_new` call (guest spine 35): its
only memory writes are the 200 zeroed bytes of the fresh block it returns
(`M27.te_new_body_run`), all at or above the old heap top, so every
block-out word below the old heap top is preserved and the generic
fine-frame bridge applies with an empty keep-set. -/
theorem phase2_te_new_txBacking {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {hp : BitVec 64} {retVal : ValueHOL 64}
    (hA : ArenaReady s)
    (hcode : s.code = originalRuntimeCode)
    (hhp : s.globals.lookup (ofString "heap_ptr") = some (.val (.word hp)))
    (hp_align : hp.toNat % 8 = 0) (hp_le_lim : hp.toNat ≤ 2952790016)
    (hdom_fn : ∀ (q : BitVec 64), q.toNat ≤ 2952790016 → q.toNat = hp.toNat + 200 →
      ∀ off : Nat, off < 200 → off % 8 = 0 → s.memaddrs (hp + BitVec.ofNat 64 off))
    (hrun : evaluateHOLFiniteState s
        (sourceFunctionEntry Guest.Software.guestFn_te_new).2.2.1 =
      (some (.returned retVal), post))
    (htx : R16Shards.TxBacking s)
    (hbo : globN post "bo" = globN s "bo")
    (hptr : globN s "bo" + 80 ≤ globN s "heap_ptr")
    (hp40 : memW s (globN s "bo" + 40) + 8 ≤ globN s "heap_ptr")
    (hp72 : memW s (globN s "bo" + 72) + 8 ≤ globN s "heap_ptr") :
    R16Shards.TxBacking post := by
  obtain ⟨-, hq_nat, -, hpost_mem, hpost_glob, -, -, -, -⟩ :=
    InitECandidate.Solver.Wave8Contracts.M27.te_new_body_run s post hp retVal hcode hhp
      hp_align hp_le_lim hdom_fn hrun
  have hgs : globN s "heap_ptr" = hp.toNat := by
    unfold globN; rw [hhp]
  have hgp : globN post "heap_ptr" = hp.toNat + 200 := by
    unfold globN
    rw [hpost_glob]
    simp only [HolFiniteMapExact.lookup_update, FUPDATE]
    exact hq_nat
  have hfr : FrameOutside s post []
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := by
    intro a _ hcf
    have hreg : a.toNat + 8 ≤ hp.toNat ∨ hp.toNat + 200 ≤ a.toNat := by
      unfold CellHits at hcf
      rw [hgs, hgp] at hcf
      omega
    have hkeep := zeroBlock25_keep s.memory hp a hp_le_lim hreg
    rw [hpost_mem, hkeep]
  exact phase2_txBacking_of_fine_frame hA htx hbo hfr hptr hp40 hp72
    (fun _ hi => absurd hi (by simp))

/-- `alloc` is the second of the four phase-2 callee fine frames: the guest
body only bumps the `heap_ptr` global to the rounded `q` and writes no memory
at all (`M27.alloc_body_run` concludes `out.2 = {s with globals := …}`), so
the empty keep-set frame holds unconditionally — no fresh-region reasoning is
needed beyond `post.memory = s.memory`. `TxBacking` therefore survives any
`alloc` call whose arguments and post-state satisfy the run equation. -/
theorem phase2_alloc_txBacking {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {hp n : BitVec 64} {retVal : ValueHOL 64}
    (hA : ArenaReady s)
    (hcode : s.code = originalRuntimeCode)
    (hhp : s.globals.lookup (ofString "heap_ptr") = some (.val (.word hp)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hrun : evaluateHOLFiniteState s
        (sourceFunctionEntry Guest.Software.guestFn_alloc).2.2.1 =
      (some (.returned retVal), post))
    (htx : R16Shards.TxBacking s)
    (hbo : globN post "bo" = globN s "bo")
    (hptr : globN s "bo" + 80 ≤ globN s "heap_ptr")
    (hp40 : memW s (globN s "bo" + 40) + 8 ≤ globN s "heap_ptr")
    (hp72 : memW s (globN s "bo" + 72) + 8 ≤ globN s "heap_ptr") :
    R16Shards.TxBacking post := by
  have hout1 : (evaluateHOLFiniteState s
      (InitECandidate.Solver.GuestTrapAndLookup.sourceFnBody
        Guest.Software.guestFn_alloc)).1
      = some (.returned retVal) := by
    rw [show evaluateHOLFiniteState s
          (InitECandidate.Solver.GuestTrapAndLookup.sourceFnBody
            Guest.Software.guestFn_alloc)
          = evaluateHOLFiniteState s
            (sourceFunctionEntry Guest.Software.guestFn_alloc).2.2.1 from rfl,
      hrun]
  obtain ⟨-, -, -, hEq⟩ :=
    InitECandidate.Solver.Wave8Contracts.M27.alloc_body_run s hp n hcode hhp hn retVal
      hout1
  have h2 : post = (evaluateHOLFiniteState s
      (InitECandidate.Solver.GuestTrapAndLookup.sourceFnBody
        Guest.Software.guestFn_alloc)).2 := by
    rw [show evaluateHOLFiniteState s
          (InitECandidate.Solver.GuestTrapAndLookup.sourceFnBody
            Guest.Software.guestFn_alloc)
          = evaluateHOLFiniteState s
            (sourceFunctionEntry Guest.Software.guestFn_alloc).2.2.1 from rfl,
      hrun]
  have hmem : post.memory = s.memory := by
    rw [h2, hEq]
  have hfr : FrameOutside s post []
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := by
    intro a _ _
    exact congrFun hmem a
  exact phase2_txBacking_of_fine_frame hA htx hbo hfr hptr hp40 hp72
    (fun _ hi => absurd hi (by simp))

/-- `memzero` (200-byte form) is the third fine frame, and the first with a
non-empty keep-set: the guest body writes exactly the 25 zero words of
`zeroBlock25` over `[p, p + 200)` (`M27.memzero_200_body_run` concludes
`post = {s with memory := zeroBlock25 s.memory p, …}`). `TxBacking` therefore
survives any such call whose zeroed window misses the four `bo`-record cells —
this is the memory-effect core of the `msg_new` bridge (`msg_new` is
`alloc` + this 200-byte zeroing, cf. `phase2_msg_new_fresh_heap` in
`PtxPhase2Strong`). -/
theorem phase2_memzero200_txBacking {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {p : BitVec 64} {retVal : ValueHOL 64}
    (hA : ArenaReady s)
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word p)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word 200#64)))
    (hal : p.toNat % 8 = 0)
    (hdom : ∀ off : Nat, off < 200 → off % 8 = 0 →
      s.memaddrs (p + BitVec.ofNat 64 off))
    (hple : p.toNat ≤ 2952790016)
    (hrun : evaluateHOLFiniteState s
        (sourceFunctionEntry Guest.Software.guestFn_memzero).2.2.1 =
      (some (.returned retVal), post))
    (htx : R16Shards.TxBacking s)
    (hbo : globN post "bo" = globN s "bo")
    (hptr : globN s "bo" + 80 ≤ globN s "heap_ptr")
    (hp40 : memW s (globN s "bo" + 40) + 8 ≤ globN s "heap_ptr")
    (hp72 : memW s (globN s "bo" + 72) + 8 ≤ globN s "heap_ptr")
    (hcut : ∀ a ∈ [globN s "bo" + 40, globN s "bo" + 72,
        memW s (globN s "bo" + 40), memW s (globN s "bo" + 72)],
      a + 8 ≤ p.toNat ∨ p.toNat + 200 ≤ a) :
    R16Shards.TxBacking post := by
  have hpost :=
    InitECandidate.Solver.Wave8Contracts.M27.memzero_200_body_run s post p retVal
      hdst hn hal hdom hrun
  have hpm : post.memory =
      InitECandidate.Solver.Wave8Contracts.M27.zeroBlock25 s.memory p := by
    rw [hpost]
  have hfr : FrameOutside s post [(p.toNat, 200)]
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := by
    intro a hkeep _
    have hreg : a.toNat + 8 ≤ p.toNat ∨ p.toNat + 200 ≤ a.toNat := by
      have hk := hkeep (p.toNat, 200) (by simp)
      unfold CellHits at hk
      omega
    rw [hpm]
    exact zeroBlock25_keep s.memory p a hple hreg
  refine phase2_txBacking_of_fine_frame hA htx hbo hfr hptr hp40 hp72 ?_
  intro i hi
  have hi' : i = (p.toNat, 200) := by simpa using hi
  subst i
  have key : ∀ a : Nat, a + 8 ≤ p.toNat ∨ p.toNat + 200 ≤ a →
      ¬ CellHits a (p.toNat, 200) := by
    intro a h
    unfold CellHits
    rcases h with h | h <;> omega
  exact ⟨key _ (hcut (globN s "bo" + 40) (by simp)),
    key _ (hcut (globN s "bo" + 72) (by simp)),
    key _ (hcut (memW s (globN s "bo" + 40)) (by simp)),
    key _ (hcut (memW s (globN s "bo" + 72)) (by simp))⟩

/-- `keccak256` (fourth fine frame, at the call level): the write-set theorem
`Keccak256.funByteEff_keccak256` (via `Keccak256.call0_byteEff`) confines the
callee's memory writes to the `keccak_st` buffer, the `keccak_pad` buffer and
the 32-byte output window, and preserves the globals — so `TxBacking`
survives any resumed `keccak256` call whose three write windows miss the
four `bo`-record cells. `memcpy` is the only remaining phase-2 callee
without a fine frame (`M21.dm_memcpy` is resumes-in-domain only). -/
theorem phase2_keccak256_txBacking {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {p n out : BitVec 64}
    {retVal : ValueHOL 64}
    (hA : ArenaReady s)
    (hcode : s.code = originalRuntimeCode)
    (hG : GuestInv s)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word p)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hout : s.locals.lookup (ofString "out") = some (.val (.word out)))
    (hrun : evaluateHOLFiniteState s
        (.call (some (none, none)) (ofString "keccak256")
          [.var .local (ofString "p"), .var .local (ofString "n"), .var .local (ofString "out")])
        = (some (.returned retVal), post))
    (htx : R16Shards.TxBacking s)
    (hptr : globN s "bo" + 80 ≤ globN s "heap_ptr")
    (hp40 : memW s (globN s "bo" + 40) + 8 ≤ globN s "heap_ptr")
    (hp72 : memW s (globN s "bo" + 72) + 8 ≤ globN s "heap_ptr")
    (hdisj : ∀ i ∈
        [InitECandidate.Solver.Wave8GuestInv.R13Shards.Keccak256.globBufIvl s.globals "keccak_st" 200,
         InitECandidate.Solver.Wave8GuestInv.R13Shards.Keccak256.globBufIvl s.globals "keccak_pad" 136,
         (out.toNat, 32)],
      ∀ a ∈ [globN s "bo" + 40, globN s "bo" + 72,
        memW s (globN s "bo" + 40), memW s (globN s "bo" + 72)],
        a + 8 ≤ i.1 ∨ i.1 + i.2 ≤ a) :
    R16Shards.TxBacking post := by
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "p"), .var .local (ofString "n"), .var .local (ofString "out")] =
      some [.val (.word p), .val (.word n), .val (.word out)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hp, hn, hout]
  have hnt : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "keccak256")
        [.var .local (ofString "p"), .var .local (ofString "n"), .var .local (ofString "out")])).1
      ≠ some .timeOut := by
    intro h
    rw [hrun] at h
    simp at h
  have hor : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "keccak256")
        [.var .local (ofString "p"), .var .local (ofString "n"), .var .local (ofString "out")])).1
      = none ∨ Resumes (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "keccak256")
        [.var .local (ofString "p"), .var .local (ofString "n"), .var .local (ofString "out")])).1 := by
    refine Or.inr ?_
    rw [hrun]
    exact Or.inl ⟨retVal, rfl⟩
  obtain ⟨-, -, -, -, -, hglobEff, -, -, hcell, -⟩ :=
    InitECandidate.Solver.Wave8GuestInv.R13Shards.Keccak256.call0_byteEff
      InitECandidate.Solver.Wave8GuestInv.R13Shards.Keccak256.funByteEff_keccak256 s
      [.var .local (ofString "p"), .var .local (ofString "n"), .var .local (ofString "out")]
      [InitECandidate.Solver.Wave8GuestInv.R13Shards.Keccak256.globBufIvl s.globals "keccak_st" 200,
       InitECandidate.Solver.Wave8GuestInv.R13Shards.Keccak256.globBufIvl s.globals "keccak_pad" 136,
       (out.toNat, 32)]
      hcode hG
      (fun vs hvs i hi _ => by
        rw [hargs] at hvs
        injection hvs with hvs
        subst hvs
        exact ⟨i, hi, Nat.le_refl _, Nat.le_refl _⟩)
      hnt hor
  have hpost_eq : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "keccak256")
        [.var .local (ofString "p"), .var .local (ofString "n"), .var .local (ofString "out")])).2
      = post := by rw [hrun]
  rw [hpost_eq] at hglobEff hcell
  have hbo' : globN post "bo" = globN s "bo" := by
    unfold globN
    rw [hglobEff]
  have hfr : FrameOutside s post
      [InitECandidate.Solver.Wave8GuestInv.R13Shards.Keccak256.globBufIvl s.globals "keccak_st" 200,
       InitECandidate.Solver.Wave8GuestInv.R13Shards.Keccak256.globBufIvl s.globals "keccak_pad" 136,
       (out.toNat, 32)]
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := by
    intro a hkeep _
    by_contra hm
    obtain ⟨i, hi, hpos⟩ := hcell a hm
    exact hkeep i hi hpos.2
  refine phase2_txBacking_of_fine_frame hA htx hbo' hfr hptr hp40 hp72 ?_
  intro i hi
  have key : ∀ a : Nat,
      a ∈ [globN s "bo" + 40, globN s "bo" + 72,
        memW s (globN s "bo" + 40), memW s (globN s "bo" + 72)] →
      ¬ CellHits a i := by
    intro a ha
    unfold CellHits
    rcases hdisj i hi a ha with h | h <;> omega
  exact ⟨key _ (by simp), key _ (by simp), key _ (by simp), key _ (by simp)⟩

/-- `memcpy` (fifth and last fine frame, at the call level): the write-set
theorem `Keccak256.funByteEff_memcpy` (consumed via `Keccak256.call0_byteEff`)
confines the callee's writes to the destination window `[dst, dst + n)` while
preserving the globals — so `TxBacking` survives any resumed `memcpy` call
whose destination window misses the four `bo`-record cells. With this, all
five 34..69 callees that lacked a fine frame (`te_new`, `alloc`, `memzero`,
`keccak256`, `memcpy`) have one; composing them into the segment chain and
restating over `PtxCalleesCutover` is the remaining Phase 2 wiring. -/
theorem phase2_memcpy_txBacking {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {dst src n : BitVec 64}
    {retVal : ValueHOL 64}
    (hA : ArenaReady s)
    (hcode : s.code = originalRuntimeCode)
    (hG : GuestInv s)
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (hsrc : s.locals.lookup (ofString "src") = some (.val (.word src)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hrun : evaluateHOLFiniteState s
        (.call (some (none, none)) (ofString "memcpy")
          [.var .local (ofString "dst"), .var .local (ofString "src"), .var .local (ofString "n")])
        = (some (.returned retVal), post))
    (htx : R16Shards.TxBacking s)
    (hptr : globN s "bo" + 80 ≤ globN s "heap_ptr")
    (hp40 : memW s (globN s "bo" + 40) + 8 ≤ globN s "heap_ptr")
    (hp72 : memW s (globN s "bo" + 72) + 8 ≤ globN s "heap_ptr")
    (hdisj : ∀ i ∈ [(dst.toNat, n.toNat)],
      ∀ a ∈ [globN s "bo" + 40, globN s "bo" + 72,
        memW s (globN s "bo" + 40), memW s (globN s "bo" + 72)],
        a + 8 ≤ i.1 ∨ i.1 + i.2 ≤ a) :
    R16Shards.TxBacking post := by
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "dst"), .var .local (ofString "src"), .var .local (ofString "n")] =
      some [.val (.word dst), .val (.word src), .val (.word n)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hdst, hsrc, hn]
  have hnt : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memcpy")
        [.var .local (ofString "dst"), .var .local (ofString "src"), .var .local (ofString "n")])).1
      ≠ some .timeOut := by
    intro h
    rw [hrun] at h
    simp at h
  have hor : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memcpy")
        [.var .local (ofString "dst"), .var .local (ofString "src"), .var .local (ofString "n")])).1
      = none ∨ Resumes (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memcpy")
        [.var .local (ofString "dst"), .var .local (ofString "src"), .var .local (ofString "n")])).1 := by
    refine Or.inr ?_
    rw [hrun]
    exact Or.inl ⟨retVal, rfl⟩
  obtain ⟨-, -, -, -, -, hglobEff, -, -, hcell, -⟩ :=
    InitECandidate.Solver.Wave8GuestInv.R13Shards.Keccak256.call0_byteEff
      InitECandidate.Solver.Wave8GuestInv.R13Shards.Keccak256.funByteEff_memcpy s
      [.var .local (ofString "dst"), .var .local (ofString "src"), .var .local (ofString "n")]
      [(dst.toNat, n.toNat)]
      hcode hG
      (fun vs hvs i hi _ => by
        rw [hargs] at hvs
        injection hvs with hvs
        subst hvs
        exact ⟨i, hi, Nat.le_refl _, Nat.le_refl _⟩)
      hnt hor
  have hpost_eq : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memcpy")
        [.var .local (ofString "dst"), .var .local (ofString "src"), .var .local (ofString "n")])).2
      = post := by rw [hrun]
  rw [hpost_eq] at hglobEff hcell
  have hbo' : globN post "bo" = globN s "bo" := by
    unfold globN
    rw [hglobEff]
  have hfr : FrameOutside s post [(dst.toNat, n.toNat)]
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := by
    intro a hkeep _
    by_contra hm
    obtain ⟨i, hi, hpos⟩ := hcell a hm
    exact hkeep i hi hpos.2
  refine phase2_txBacking_of_fine_frame hA htx hbo' hfr hptr hp40 hp72 ?_
  intro i hi
  have key : ∀ a : Nat,
      a ∈ [globN s "bo" + 40, globN s "bo" + 72,
        memW s (globN s "bo" + 40), memW s (globN s "bo" + 72)] →
      ¬ CellHits a i := by
    intro a ha
    unfold CellHits
    rcases hdisj i hi a ha with h | h <;> omega
  exact ⟨key _ (by simp), key _ (by simp), key _ (by simp), key _ (by simp)⟩

/-- `msg_new` (the 176-byte form used at the phase-2 spine): composing the
proved fine frame `phase2_msg_new_fresh_heap` (`PtxPhase2Strong.20483`,
which establishes `globN post "bo" = globN s "bo"` and
`FrameOutside s post [(globN s "scratch_ptr", 0)] …`) with the generic
bridge `phase2_txBacking_of_fine_frame` preserves `TxBacking` across the
call, provided the four `bo`-record cells lie below the old heap top and do
not straddle the single writable scratch word. This is the pre-`msg_new`
backing bridge referenced by the module header. Renamed from the seed name
`phase2_msg_new_txBacking`: the patch already exports a `DecCallResumeOn`
theorem under that name at `PtxPhase2Strong.20691`, and the two statements
are different (this one is the fine-frame preservation over the
`alloc`+`memzero` call chain inside `msg_new`'s body, that one is the
call-level spec). -/
theorem phase2_msg_new_alloc_txBacking {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (hW : WorldOK s)
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString "m") .one (ofString "alloc") [.const 176]
        (.seq (.call (some (none, none)) (ofString "memzero")
            [.var .local (ofString "m"), .const 176])
          (.return (.var .local (ofString "m")))))).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall (ofString "m") .one (ofString "alloc") [.const 176]
        (.seq (.call (some (none, none)) (ofString "memzero")
            [.var .local (ofString "m"), .const 176])
          (.return (.var .local (ofString "m")))))).1)
    (hA : ArenaReady s)
    (htx : R16Shards.TxBacking s)
    (hptr : globN s "bo" + 80 ≤ globN s "heap_ptr")
    (hp40 : memW s (globN s "bo" + 40) + 8 ≤ globN s "heap_ptr")
    (hp72 : memW s (globN s "bo" + 72) + 8 ≤ globN s "heap_ptr")
    (hscratch : ∀ a ∈ [globN s "bo" + 40, globN s "bo" + 72,
        memW s (globN s "bo" + 40), memW s (globN s "bo" + 72)],
      a + 8 ≤ globN s "scratch_ptr" ∨ globN s "scratch_ptr" < a) :
    R16Shards.TxBacking (evaluateHOLFiniteState s
      (.decCall (ofString "m") .one (ofString "alloc") [.const 176]
        (.seq (.call (some (none, none)) (ofString "memzero")
            [.var .local (ofString "m"), .const 176])
          (.return (.var .local (ofString "m")))))).2 := by
  obtain ⟨-, hbo, -, hfr⟩ := phase2_msg_new_fresh_heap s hcode hW hnt hres
  refine phase2_txBacking_of_fine_frame hA htx hbo hfr hptr hp40 hp72 ?_
  intro i hi
  have hi' : i = (globN s "scratch_ptr", 0) := by simpa using hi
  subst i
  have key : ∀ a : Nat, a + 8 ≤ globN s "scratch_ptr" ∨
      globN s "scratch_ptr" < a →
      ¬ CellHits a (globN s "scratch_ptr", 0) := by
    intro a h
    unfold CellHits
    rcases h with h | h <;> omega
  exact ⟨key _ (hscratch (globN s "bo" + 40) (by simp)),
    key _ (hscratch (globN s "bo" + 72) (by simp)),
    key _ (hscratch (memW s (globN s "bo" + 40)) (by simp)),
    key _ (hscratch (memW s (globN s "bo" + 72)) (by simp))⟩

/-! ### The te-store `TxBacking` preservation -/

/-- A single store into the fresh transaction-execution record preserves
`TxBacking`. The `PtxTeStoreReady` guard already owns te-block/world
disjointness (`IvlsDisj [(te, 200)] (worldOwned s S Nd)`); the `bo` record
is a fixed object (`TxReady`'s `bo`-nonzero conjunct makes its
`typedRecords` entry non-degenerate) and so are the two 24-byte list
headers hanging off `bo + 40`/`bo + 72` (their pointers are nonzero by
`TxReadyStrong`), and `worldOwned` contains `fixedObjects` by definition.
`R16Shards.PtxP34.txBacking_store_disjoint_fixed` then turns the
te-block/fixed-objects disjointness into `TxBacking` preservation for any
memory function that changes only a store inside the block. This is the
induction step for the six `phase2_teStores` stores of the 34..69 replay. -/
theorem phase2_teStore_txBacking {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxTeStoreReady s) (htx : R16Shards.TxBacking s)
    {x : BitVec 64}
    (hin : Inside (x.toNat, 8) (locN s "te") (locN s "te" + 200))
    {mem : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem a = s.memory a) :
    R16Shards.TxBacking {s with memory := mem} := by
  obtain ⟨hl, S, Nd, hW, hT, hdisj, htxd, hrec⟩ := hp
  obtain ⟨hpv, hte, hins, hmod, hwd200, hwd⟩ := hl
  obtain ⟨hpv2, hshapes⟩ := hpv
  obtain ⟨htr, hsend, hwords, hmgas⟩ := hpv2
  obtain ⟨htxr, hjcap, hb40, hb72, hworlds⟩ := htr
  obtain ⟨hwok, hbo, hb24, hb32, hidx⟩ := htxr
  obtain ⟨hle, hle2⟩ := hin
  refine R16Shards.PtxP34.txBacking_store_disjoint_fixed
    (i := (locN s "te", 200)) (mem' := mem)
    ⟨hwok, ⟨hbo, hb24, hb32, hb40, hb72, hidx, hjcap⟩⟩ htx ⟨hle, hle2⟩ ?_ hm
  intro j hj
  refine hdisj _ (by simp) j ?_
  unfold worldOwned
  exact List.mem_append_left _ (List.mem_append_right _ hj)

/-- The eval-level induction step for the scalar te stores: a `.store` whose
address evaluates to a word `x` inside the fresh transaction-execution record
and whose value evaluates to a scalar word preserves `TxBacking` on the
success path. The store semantics (`evaluateHOLFiniteState_store`) rewrites
the post-state to `s` with the single word at `x` changed
(`panMemStoreHOL_hit` on the in-domain address, `flattenHOL` of a scalar
being the one-word list), so `phase2_teStore_txBacking` applies. This covers
the scalar stores of `phase2_teStores` (`te+0`, `te+8`, `te+80`, `te+88`);
the two multi-word stores (`te+16` quad load, `te+48` price struct) need a
four-word version of the same pattern. -/
theorem phase2_store_txBacking {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxTeStoreReady s) (htx : R16Shards.TxBacking s)
    {addrExp valExp : ExpHOL 64} {x w : BitVec 64}
    {post : PanSemStateFiniteExact 64 F}
    (haddr : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) addrExp = some (.val (.word x)))
    (hval : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) valExp = some (.val (.word w)))
    (hxdom : s.memaddrs x)
    (hin : Inside (x.toNat, 8) (locN s "te") (locN s "te" + 200))
    (hrun : evaluateHOLFiniteState s (.store addrExp valExp) = (none, post)) :
    R16Shards.TxBacking post := by
  rw [evaluateHOLFiniteState_store, haddr, hval] at hrun
  simp only [flattenHOL] at hrun
  have hstore : @panMemStoresHOL 64 _ x [HolWordLab.word w] s.memaddrs
      (fun a => Classical.propDecidable (s.memaddrs a)) s.memory
      = some (fun c => if c = x then HolWordLab.word w else s.memory c) := by
    have h1 : @panMemStoreHOL 64 _ x (HolWordLab.word w) s.memaddrs
        (fun a => Classical.propDecidable (s.memaddrs a)) s.memory
        = some (fun c => if c = x then HolWordLab.word w else s.memory c) :=
      @panMemStoreHOL_hit 64 _ x (HolWordLab.word w) s.memaddrs
        (fun a => Classical.propDecidable (s.memaddrs a)) s.memory hxdom
    simp only [panMemStoresHOL, h1]
  rw [hstore] at hrun
  dsimp only at hrun
  injection hrun with _ hpost
  subst hpost
  exact phase2_teStore_txBacking hp htx hin (fun a ha => if_neg ha)

/-- The write-window version of `R16Shards.PtxP34.txBacking_store_disjoint_fixed`:
a memory function that changes only words inside a window `[x, x + len)`,
where the window lies inside an interval disjoint from every fixed object,
preserves `TxBacking`. The proof mirrors the single-store version (concluding
via `R16Shards.txBacking_of_header_words`), replacing the one-address
exclusion by the window exclusion; both `bo`-record cells and both list-header
data words are fixed objects (nonzero pointers from the `TxWorld`), so they
lie outside the window and their reads are preserved. -/
private theorem txBacking_store_window {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hW : TxWorld s) (hback : R16Shards.TxBacking s) {i : Ivl} {x : BitVec 64} {len : Nat}
    (hx : i.1 ≤ x.toNat ∧ x.toNat + len ≤ i.1 + i.2)
    (hd : ∀ j ∈ fixedObjects s, Disj i j)
    {mem' : BitVec 64 → HolWordLab 64}
    (hm : ∀ a, ¬ (x.toNat ≤ a.toNat ∧ a.toNat < x.toNat + len) → mem' a = s.memory a) :
    R16Shards.TxBacking {s with memory := mem'} := by
  obtain ⟨S, hWT⟩ := hW.1.2
  have hb := bo_words hWT.2.2.1 hW.2.bo_nz
  have hbnd := (ivl_allocated_bound hW.1.1.2 hb.1).2
  have hbo : (globN s "bo", 88) ∈ fixedObjects s := by
    have hh0 := typedRecord_mem_fixedObjects s (r := ("bo", 88)) (by decide)
    simpa only [hW.2.bo_nz, ↓reduceIte] using hh0
  have hh : ∀ k ∈ ([40, 72] : List Nat),
      (memW s (globN s "bo" + k), 24) ∈ fixedObjects s := by
    intro k hk
    unfold fixedObjects
    apply List.mem_append_left
    apply List.mem_append_right
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · simp [blockOutObjects, hW.2.bo_nz, hW.2.bo40]
    · simp [blockOutObjects, hW.2.bo_nz, hW.2.bo72]
  have hout : ∀ (j : Ivl) (c : Nat), Disj i j → j.1 ≤ c ∧ c + 8 ≤ j.1 + j.2 →
      ¬ (x.toNat ≤ c ∧ c < x.toNat + len) := by
    intro j c hdis hjmem
    unfold Disj at hdis
    have h1 := hx.1
    have h2 := hx.2
    omega
  have hpres : ∀ (c : Nat), c < 2 ^ 64 → ¬ (x.toNat ≤ c ∧ c < x.toNat + len) →
      mem' (BitVec.ofNat 64 c) = s.memory (BitVec.ofNat 64 c) := by
    intro c hc houtc
    refine hm (BitVec.ofNat 64 c) ?_
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]
    exact houtc
  refine R16Shards.txBacking_of_header_words hback rfl ?_ ?_
  · intro k hk
    have hk' : k = 40 ∨ k = 72 := by simpa using hk
    have hlt : globN s "bo" + k < 2 ^ 64 := by dsimp at hbnd; omega
    unfold memW
    dsimp only
    rw [hpres _ hlt (hout (globN s "bo", 88) (globN s "bo" + k) (hd _ hbo)
      (by dsimp; omega))]
  · intro k hk
    have hk' : k = 40 ∨ k = 72 := by simpa using hk
    have hal := (hWT.2.2.1.1 _ (hh k hk)).resolve_left (by simp)
    have hbound := (ivl_allocated_bound hW.1.1.2 hal.1).2
    have hlt : memW s (globN s "bo" + k) < 2 ^ 64 := by dsimp at hbound; omega
    have houtk : ¬ (x.toNat ≤ memW s (globN s "bo" + k) ∧
        memW s (globN s "bo" + k) < x.toNat + len) :=
      hout (memW s (globN s "bo" + k), 24) (memW s (globN s "bo" + k))
        (hd _ (hh k hk)) (by dsimp; omega)
    unfold memW
    dsimp only
    rw [hpres ((s.memory (BitVec.ofNat 64 (globN s "bo" + k))).1.toNat) hlt houtk]

/-- The eval-level induction step for the two multi-word te stores (`te+16`
quad load, `te+48` price struct): a `.store` whose address evaluates to a
word `x` inside the fresh transaction-execution record and whose value
evaluates to a four-word struct preserves `TxBacking` on the success path.
The store semantics unrolls to four single-word updates
(`panMemStoresHOL` over `flattenHOL` of the struct, each word hitting the
in-domain address from `panMemStoreHOL_hit`), i.e. the final memory agrees
with the old one outside the 32-byte window `[x, x + 32)`, so the window
lemma applies. Together with `phase2_store_txBacking` this covers all six
`phase2_teStores` stores. -/
theorem phase2_store_quad_txBacking {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxTeStoreReady s) (htx : R16Shards.TxBacking s)
    {addrExp valExp : ExpHOL 64} {x a b c d : BitVec 64}
    {post : PanSemStateFiniteExact 64 F}
    (haddr : @evalHOLExact 64 F _ s.toExact
      (fun q => Classical.propDecidable (s.memaddrs q)) addrExp = some (.val (.word x)))
    (hval : @evalHOLExact 64 F _ s.toExact
      (fun q => Classical.propDecidable (s.memaddrs q)) valExp
      = some (.rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]))
    (hdom : ∀ k ∈ ([0, 8, 16, 24] : List Nat), s.memaddrs (x + BitVec.ofNat 64 k))
    (hbound : x.toNat + 32 < 2 ^ 64)
    (hin : Inside (x.toNat, 32) (locN s "te") (locN s "te" + 200))
    (hrun : evaluateHOLFiniteState s (.store addrExp valExp) = (none, post)) :
    R16Shards.TxBacking post := by
  obtain ⟨hl, S, Nd, hW, hT, hdisj, htxd, hrec⟩ := hp
  obtain ⟨hpv, hte, hins, hmod, hwd200, hwd⟩ := hl
  obtain ⟨hpv2, hshapes⟩ := hpv
  obtain ⟨htr, hsend, hwords, hmgas⟩ := hpv2
  obtain ⟨htxr, hjcap, hb40, hb72, hworlds⟩ := htr
  obtain ⟨hwok, hbo, hb24, hb32, hidx⟩ := htxr
  obtain ⟨hle, hle2⟩ := hin
  have hxd0 : s.memaddrs x := by
    have h0 := hdom 0 (by simp)
    rwa [BitVec.add_zero] at h0
  have haddrk : ∀ k ∈ ([0, 8, 16, 24] : List Nat),
      (x + BitVec.ofNat 64 k).toNat = x.toNat + k := by
    intro k hk
    have hk4 : k = 0 ∨ k = 8 ∨ k = 16 ∨ k = 24 := by simpa using hk
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hb8 : BitVec.ofNat 64 (64 / 8) = BitVec.ofNat 64 8 := by decide
  have h16 : x + BitVec.ofNat 64 16
      = x + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 := by
    rw [BitVec.add_assoc]; congr 1 <;> decide
  have h24 : x + BitVec.ofNat 64 24
      = x + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 := by
    rw [BitVec.add_assoc, BitVec.add_assoc]; congr 1 <;> decide
  have hd2 : s.memaddrs (x + BitVec.ofNat 64 8 + BitVec.ofNat 64 8) := by
    rw [← h16]; exact hdom 16 (by simp)
  have hd3 : s.memaddrs (x + BitVec.ofNat 64 8 + BitVec.ofNat 64 8
      + BitVec.ofNat 64 8) := by
    rw [← h24]; exact hdom 24 (by simp)
  have h1 : @panMemStoreHOL 64 _ x (HolWordLab.word a) s.memaddrs
      (fun q => Classical.propDecidable (s.memaddrs q)) s.memory
      = some (fun q => if q = x then HolWordLab.word a else s.memory q) :=
    @panMemStoreHOL_hit 64 _ x (HolWordLab.word a) s.memaddrs
      (fun q => Classical.propDecidable (s.memaddrs q)) s.memory hxd0
  have h2 : @panMemStoreHOL 64 _ (x + BitVec.ofNat 64 8) (HolWordLab.word b) s.memaddrs
      (fun q => Classical.propDecidable (s.memaddrs q))
      (fun q => if q = x then HolWordLab.word a else s.memory q)
      = some (fun q => if q = x + BitVec.ofNat 64 8 then HolWordLab.word b
          else if q = x then HolWordLab.word a else s.memory q) :=
    @panMemStoreHOL_hit 64 _ (x + BitVec.ofNat 64 8) (HolWordLab.word b) s.memaddrs
      (fun q => Classical.propDecidable (s.memaddrs q))
      (fun q => if q = x then HolWordLab.word a else s.memory q) (hdom 8 (by simp))
  have h3 : @panMemStoreHOL 64 _
      (x + BitVec.ofNat 64 8 + BitVec.ofNat 64 8) (HolWordLab.word c) s.memaddrs
      (fun q => Classical.propDecidable (s.memaddrs q))
      (fun q => if q = x + BitVec.ofNat 64 8 then HolWordLab.word b
          else if q = x then HolWordLab.word a else s.memory q)
      = some (fun q =>
          if q = x + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 then HolWordLab.word c
          else if q = x + BitVec.ofNat 64 8 then HolWordLab.word b
          else if q = x then HolWordLab.word a else s.memory q) :=
    @panMemStoreHOL_hit 64 _
      (x + BitVec.ofNat 64 8 + BitVec.ofNat 64 8) (HolWordLab.word c) s.memaddrs
      (fun q => Classical.propDecidable (s.memaddrs q))
      (fun q => if q = x + BitVec.ofNat 64 8 then HolWordLab.word b
          else if q = x then HolWordLab.word a else s.memory q) hd2
  have h4 : @panMemStoreHOL 64 _
      (x + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8)
      (HolWordLab.word d) s.memaddrs
      (fun q => Classical.propDecidable (s.memaddrs q))
      (fun q =>
          if q = x + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 then HolWordLab.word c
          else if q = x + BitVec.ofNat 64 8 then HolWordLab.word b
          else if q = x then HolWordLab.word a else s.memory q)
      = some (fun q =>
          if q = x + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8
            then HolWordLab.word d
          else if q = x + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 then HolWordLab.word c
          else if q = x + BitVec.ofNat 64 8 then HolWordLab.word b
          else if q = x then HolWordLab.word a else s.memory q) :=
    @panMemStoreHOL_hit 64 _
      (x + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8)
      (HolWordLab.word d) s.memaddrs
      (fun q => Classical.propDecidable (s.memaddrs q))
      (fun q =>
          if q = x + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 then HolWordLab.word c
          else if q = x + BitVec.ofNat 64 8 then HolWordLab.word b
          else if q = x then HolWordLab.word a else s.memory q) hd3
  have hstore : @panMemStoresHOL 64 _ x
      [HolWordLab.word a, HolWordLab.word b, HolWordLab.word c, HolWordLab.word d]
      s.memaddrs (fun q => Classical.propDecidable (s.memaddrs q)) s.memory
      = some (fun q =>
          if q = x + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8
            then HolWordLab.word d
          else if q = x + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 then HolWordLab.word c
          else if q = x + BitVec.ofNat 64 8 then HolWordLab.word b
          else if q = x then HolWordLab.word a else s.memory q) := by
    simp only [panMemStoresHOL, panBytesInWord, hb8, h1, h2, h3, h4]
  rw [evaluateHOLFiniteState_store, haddr, hval] at hrun
  simp only [flattenHOL] at hrun
  have hlist : (List.map flattenHOL
      [ValueHOL.val (HolWordLab.word a), ValueHOL.val (HolWordLab.word b),
        ValueHOL.val (HolWordLab.word c), ValueHOL.val (HolWordLab.word d)]).flatten
      = [HolWordLab.word a, HolWordLab.word b, HolWordLab.word c,
          HolWordLab.word d] := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.singleton_append, flattenHOL]
  rw [hlist] at hrun
  rw [hstore] at hrun
  dsimp only at hrun
  injection hrun with _ hpost
  subst hpost
  refine txBacking_store_window ⟨hwok, ⟨hbo, hb24, hb32, hb40, hb72, hidx, hjcap⟩⟩ htx
    (i := (locN s "te", 200)) ⟨hle, hle2⟩ ?_ ?_
  · intro j hj
    refine hdisj _ (by simp) j ?_
    unfold worldOwned
    exact List.mem_append_left _ (List.mem_append_right _ hj)
  · intro q hq
    have hne : ∀ k ∈ ([0, 8, 16, 24] : List Nat), q ≠ x + BitVec.ofNat 64 k := by
      intro k hk hqk
      have hk4 : k = 0 ∨ k = 8 ∨ k = 16 ∨ k = 24 := by simpa using hk
      have hqt : q.toNat = x.toNat + k := by rw [hqk]; exact haddrk k hk
      omega
    have hn0 : q ≠ x := by
      intro hq0
      exact hne 0 (by simp) (by rw [BitVec.add_zero]; exact hq0)
    have hn16 : q ≠ x + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 := by
      intro hqk
      exact hne 16 (by simp) (by rw [h16]; exact hqk)
    have hn24 : q ≠ x + BitVec.ofNat 64 8 + BitVec.ofNat 64 8
        + BitVec.ofNat 64 8 := by
      intro hqk
      exact hne 24 (by simp) (by rw [h24]; exact hqk)
    simp only [if_neg (hn24), if_neg (hn16), if_neg (hne 8 (by simp)),
      if_neg hn0]

/-! ### The Phase 2 entry adapter -/

/-- The first Phase 2 segment (guest spine 34..44: the `te_new` call, its
seven te stores, the `tx_has_access_list` call and the count setup) is bounded
from the backing-strong entry guard. `PtxValidatedBackingStrong` strengthens
`PtxValidatedStrong` by exactly the `TxBacking` conjunct, so the proved
non-backing bound (`phase2_allocationEntry_bound`, `PtxPhase2Strong.2233`)
lifts directly; the `TxBacking` conjunct is carried into the entry guard and
remains to be re-verified at the later segment exits (see the module header).
The budget is the leading part of `ptxCost2`. -/
theorem phase2_backing_entry_adapter (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn PtxAccessCountReady tail b) :
    TerminatingProgBoundedOn PtxValidatedBackingStrong
      (spinePlug 10 (spineAt 34 ptxCode) tail)
      (K.«te_new» + (K.«tx_has_access_list» + b + 1) + 1) :=
  PtxP1.bound_mono (phase2_allocationEntry_bound h ht) (fun _ hs => hs.1)

/-! ### The legacy-bundle composition, Phase 4 closed -/

/-- Backing-aware transaction export over the legacy `PtxCallees` bundle with
the Phase 4 cut discharged by `h4_backing_strong_uncond`
(`R16Shards/PtxPhase34R11.21486`). The two remaining hypotheses are exactly
the two backing cuts: the Phase 1 cut (blocked by the `WorldStep` frame
coarseness documented in the module header) and the Phase 2 cut (blocked by
the pre-`msg_new` backing bridge documented in the module header). -/
theorem gbody_process_transaction_backing_strong_pmc_of_cuts_h4closed
    (h : PtxCallees) (hwk : PtxP34.PmcStrong) (hkeep : PmcBackingStrong)
    (hp1 : PtxPhase1BackingCut) (hp2 : PtxPhase2BackingCut) :
    TerminatingFunBoundedOn TxReadyBackingStrong (ofString "process_transaction")
      K.«process_transaction» :=
  gbody_process_transaction_backing_strong_pmc_of_cuts h hwk hkeep hp1 hp2
    (h4_backing_strong_uncond h)

/-! ### The bundled composition -/

/-- Backing-aware transaction export over the legacy `PtxCallees` bundle with
the two backing cuts bundled as `PtxPhase12BackingCuts`: the cuts compose
into the exact `h12` hypothesis (`ptxPhase12_backing_strong`,
`PtxPhase2StrongTail3.162`), and
`gbody_process_transaction_backing_strong_of_h12_pmc`
(`R16Shards/PtxPhase34R11.21505`) discharges everything else — Phase 4 via
`h4_backing_strong_uncond`, Phase 3 and the message-call `out` contract via
`PmcStrong`/`PmcBackingStrong`. This is the bundled form of the final
theorem: the two documented backing-cut obligations are the only
hypotheses that remain. (The cutover-bundle restatement of commit
`0f5882fb4` is not compilable against this dependency state — its
`funSpec_at_lookup` applications are typed for a different `WkLstPush` —
so the composition stays over the legacy bundle, which carries strictly
more callee fields.) -/
theorem gbody_process_transaction_backing_strong_of_cuts_bundled
    (h : PtxCallees) (hwk : PtxP34.PmcStrong) (hkeep : PmcBackingStrong)
    (hc : PtxPhase12BackingCuts) :
    TerminatingFunBoundedOn TxReadyBackingStrong (ofString "process_transaction")
      K.«process_transaction» :=
  gbody_process_transaction_backing_strong_of_h12_pmc h hwk hkeep
    (ptxPhase12_backing_strong hc)

end InitECandidate.Solver.Wave8GuestInv.R13Shards
