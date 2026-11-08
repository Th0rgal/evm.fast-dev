import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase2StrongTail4
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkBlockTxProcess

/-!
# Wave 8 / R16k Tail 5: the Phase 2 relational strong cut

This module closes the *relational* side of the Wave 8 / R16k campaign: it
exhibits a `PtxRelCutStrong R13Shards.ptxPhase2` instance — the strong
counterpart of the region cut that `wk_process_transaction_strong_of`
(`R16Shards/TopGbodyWk/WkBlockTxProcess.12032`) consumes for the
`process_transaction` export — together with the boundary relations it
relates, and plugs it into the export composition.

## The Phase 2 boundary relations

The tree previously fixed only `PtxAfterPhase4` as a phase-boundary relation
(`WkBlockTxProcess.10662`). This module introduces the two missing relations
around the Phase 2 region (guest spine 34..98):

* `PtxAfterPhase1` — the Phase 2 entry boundary: the entry state was a
  `TxReadyStrong` transaction and the current state carries the region's
  entry guard `PtxTailBackingGuard` (message-ready with backing and the
  Phase 4 local shapes, `PtxPhase2StrongTail3.72`) — exactly the tail guard
  that `h12` threads, now anchored to the process entry state;
* `PtxAfterPhase2` — the Phase 2 exit boundary: the state validates with
  backing (`PtxValidatedBackingStrong`, `PtxPhase2StrongTail3.66`).

## What is closed and what is bundled

The Phase 2 region itself (spine 34..98) interleaves 48 `seq`, 12 `decCall`
and 4 `dec` nodes; a node-granular relational replay of the region would
require dec/decCall strong-run rules that the tree does not yet provide.
Following the campaign's cuts-as-hypotheses convention, the region's
strong-run obligation is bundled as the explicit structure
`PtxPhase2RegionStrong` (region run plus fall-through preservation), and
this module closes:

* `ptxPhase2_cut_strong` — the `PtxRelCutStrong R13Shards.ptxPhase2`
  `PtxAfterPhase1 PtxAfterPhase2` cut, from the region obligation;
* `ptxPhase2_relCut` — its weak `PtxRelCut` twin, via `ptxRelRun_of_strong`
  (`WkBlockTxProcess.11589`);
* `ptxPhase2_cut_strong_of_entry` / `ptxPhase2_cut_strong_of_exit` — the
  boundary-subsumption adapters, mirroring the guard adapters of
  `PtxPhase2StrongTail3`;
* `wk_process_transaction_strong_of_phase2` — the composition of the Phase 2
  cut into the `process_transaction` export: the Phase 1 / 3 / 4 strong cuts
  are bundled as `PtxPhase134StrongCuts`, the initial boundary is the trivial
  `TxReadyStrong`-reflexive relation, and the terminal phase is the
  *unconditional* `ptxAfterPhase4_phase5_relRun_strong`
  (`WkBlockTxProcess.12000`) — the phase-5 closure carries real proof
  content, only its three block-output side conditions are hypotheses.
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
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk

/-! ## The Phase 2 boundary relations -/

/-- The Phase 2 entry boundary (guest spine 34): the process was entered from
a `TxReadyStrong` state, the code is the runtime, and the current state
satisfies `PtxTailBackingGuard` — the `h12` tail guard
(`PtxPhase2StrongTail3.72`), now indexed by the process entry state. This is
the relational counterpart of the Phase 1 backing cut's exit guard
(`PtxPhase2StrongTail3`, `ptxPhase1BackingCut_of_guard`). -/
def PtxAfterPhase1 {F : Type} (entry s : PanSemStateFiniteExact 64 F) : Prop :=
  TxReadyStrong entry ∧ s.code = originalRuntimeCode ∧ PtxTailBackingGuard s

/-- The Phase 2 exit boundary (guest spine 98): the process was entered from a
`TxReadyStrong` state, the code is the runtime, and the state validates with
backing (`PtxValidatedBackingStrong`). This is the relational lift of the
bound-form exit guard of the Phase 2 backing cut
(`PtxPhase2StrongTail3.104`). -/
def PtxAfterPhase2 {F : Type} (entry s : PanSemStateFiniteExact 64 F) : Prop :=
  TxReadyStrong entry ∧ s.code = originalRuntimeCode ∧ PtxValidatedBackingStrong s

/-! ## The Phase 2 region obligation -/

/-- **The Phase 2 region strong-run obligation** (guest spine 34..98). From
every Phase 2 boundary state, the region `ptxPhase2 tail` strongly runs for
every continuation `tail` (a `WorldStep` of the process entry under
`Resumes`), and its fall-through states satisfy the Phase 2 exit boundary.
This is the remaining obligation of the region: the interleaved `decCall`
and `dec` nodes of spine 34..98 have no relational strong-run rules in the
tree yet, so the region replay is bundled here rather than discharged. -/
structure PtxPhase2RegionStrong : Prop where
  /-- The region strongly runs from every Phase 2 boundary state. -/
  run : ∀ {F : Type} (entry s : PanSemStateFiniteExact 64 F) (tail : ProgHOL 64),
    PtxAfterPhase1 entry s → PtxRelRunStrong entry (ptxPhase2 tail) s
  /-- Region fall-through lands in the Phase 2 exit boundary. -/
  fall : ∀ {F : Type} (entry s : PanSemStateFiniteExact 64 F) (tail : ProgHOL 64),
    PtxAfterPhase1 entry s →
    (evaluateHOLFiniteState s (ptxPhase2 tail)).1 = none →
    PtxAfterPhase2 entry (evaluateHOLFiniteState s (ptxPhase2 tail)).2

/-! ## The strong cut -/

/-- **The Phase 2 strong cut** (guest spine 34..98): from the region
obligation, `ptxPhase2` maps a tail strong-run from every Phase 2 exit state
to a strong run of `ptxPhase2 tail` from every Phase 2 entry state. This is
the `PtxRelCutStrong R13Shards.ptxPhase2` instance that
`wk_process_transaction_strong_of` consumes as `h2`. -/
theorem ptxPhase2_cut_strong (hregion : PtxPhase2RegionStrong) :
    PtxRelCutStrong ptxPhase2 PtxAfterPhase1 PtxAfterPhase2 := by
  intro F entry tail _htail s _hc hA
  exact hregion.run entry s tail hA

/-- The weak twin of `ptxPhase2_cut_strong`: the `PtxRelCut`
`ptxPhase2 PtxAfterPhase1 PtxAfterPhase2` instance, via
`ptxRelRun_of_strong` (`WkBlockTxProcess.11589`). This mirrors the
`ptxPhase5Cleanup_cut` / `ptxPhase5Cleanup_cut_strong` pairing at the Phase 5
boundary (`WkBlockTxProcess.11610` / `.13975`). -/
theorem ptxPhase2_relCut (hregion : PtxPhase2RegionStrong) :
    PtxRelCut ptxPhase2 PtxAfterPhase1 PtxAfterPhase2 := by
  intro F entry tail htail s hc hA
  exact ptxRelRun_of_strong (hregion.run entry s tail hA)

/-! ## Boundary-subsumption adapters -/

/-- Entry-subsumption adapter: if the region cut is available from a (possibly
larger) entry boundary `A1` that contains every Phase 2 boundary state, then
it holds from the boundary itself. Mirrors `ptxPhase1BackingCut_of_guard`
(`PtxPhase2StrongTail3.127`). -/
theorem ptxPhase2_cut_strong_of_entry
    (A1 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop)
    (hsub : ∀ {F : Type} (entry s : PanSemStateFiniteExact 64 F),
      PtxAfterPhase1 entry s → A1 entry s)
    (hcut : PtxRelCutStrong ptxPhase2 A1 PtxAfterPhase2) :
    PtxRelCutStrong ptxPhase2 PtxAfterPhase1 PtxAfterPhase2 := by
  intro F entry tail htail s hc hA
  exact hcut entry tail htail s hc (hsub entry s hA)

/-- Exit-strengthening adapter: if the region cut was proved against a
stronger exit boundary `A2` (every `A2` state is a Phase 2 exit state), then
it holds with the Phase 2 exit boundary. -/
theorem ptxPhase2_cut_strong_of_exit
    (A2 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop)
    (hsub : ∀ {F : Type} (entry s : PanSemStateFiniteExact 64 F),
      A2 entry s → PtxAfterPhase2 entry s)
    (hcut : PtxRelCutStrong ptxPhase2 PtxAfterPhase1 A2) :
    PtxRelCutStrong ptxPhase2 PtxAfterPhase1 PtxAfterPhase2 := by
  intro F entry tail htail s hc hA
  exact hcut entry tail (fun s hc' hA' => htail s hc' (hsub entry s hA')) s hc hA

/-! ## The export composition -/

/-- The initial boundary for the transaction export: the entry-reflexive
`TxReadyStrong` relation. `wk_process_transaction_strong_of`'s `hinit`
holds for it definitionally. -/
def PtxTxReadyBoundary {F : Type} (_entry s : PanSemStateFiniteExact 64 F) : Prop :=
  TxReadyStrong s

/-- The remaining Phase 1 / 3 / 4 strong-cut obligations for the
`process_transaction` export, against the Phase 2 boundary relations fixed
by this module: `phase1` runs from the trivial entry boundary into the
Phase 2 boundary, `phase3` from the Phase 2 boundary into the abstract
mid-region boundary `A3`, and `phase4` from `A3` into the closed
`PtxAfterPhase4` boundary. -/
structure PtxPhase134StrongCuts
    (A3 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop) : Prop where
  phase1 : PtxRelCutStrong ptxPhase1 PtxTxReadyBoundary PtxAfterPhase1
  phase3 : PtxRelCutStrong ptxPhase3 PtxAfterPhase2 A3
  phase4 : PtxRelCutStrong ptxPhase4 A3 PtxAfterPhase4

/-- **The Phase 2 cut composed into the transaction export.** Given the
Phase 2 region obligation, the Phase 1 / 3 / 4 strong cuts, and the three
block-output side conditions of the phase-5 closure, the
`process_transaction` export keeps its world (`wk_process_transaction_strong_of`
`WkBlockTxProcess.12032`). The phase-5 leg is discharged by the unconditional
`ptxAfterPhase4_phase5_relRun_strong` (`WkBlockTxProcess.12000`). -/
theorem wk_process_transaction_strong_of_phase2
    (hregion : PtxPhase2RegionStrong)
    {A3 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop}
    (hcuts : PtxPhase134StrongCuts A3)
    (hbo_clean : ∀ {F : Type} {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)},
      WorldStepSc (bufRegions acctMutBufs) ["heap_ptr", "journal_n", "scratch_ptr"] stdKeep NoExtra
        s r post → PtxBlockOutUnhit s post)
    (hinc : WorldKeepsSc WorldOK (bufRegions ptxIncorpBufs) ptxIncorpGlobals ptxIncorpKeep NoExtra
      (ofString "incorporate_tx_into_block"))
    (hbo_inc : ∀ {F : Type} {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)},
      WorldStepSc (bufRegions ptxIncorpBufs) ptxIncorpGlobals ptxIncorpKeep NoExtra s r post →
        PtxBlockOutUnhit s post) :
    WorldKeeps TxReadyStrong
      (fun s => [(globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128), (globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64), (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352), (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384), (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96), (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40), (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128), (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128), (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128), (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52), (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["bal_index", "bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]), ("ts", []), ("bo", [24, 32, 40, 56, 64, 72, 80])]
      (fun s r post S Nd => RetTransactionLogs s r post S Nd ∧ PtxRetSlices s r post S Nd)
      (ofString "process_transaction") := by
  refine wk_process_transaction_strong_of PtxTxReadyBoundary PtxAfterPhase1 PtxAfterPhase2 A3
    PtxAfterPhase4 (fun _ hs => hs) hcuts.phase1 (ptxPhase2_cut_strong hregion) hcuts.phase3
    hcuts.phase4 ?h5
  intro F entry s hc h
  exact ptxAfterPhase4_phase5_relRun_strong hbo_clean hinc hbo_inc entry s hc h


end InitECandidate.Solver.Wave8GuestInv.R13Shards
