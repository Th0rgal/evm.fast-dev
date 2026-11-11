import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase1
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxRelBasePhase3
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPmcMarksBo
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkProcessTransactionR31

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.EvmBase (stdKeep)
open InitECandidate.Solver.Wave8GuestInv.R13Shards
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
open InitECandidate.Solver.Wave8GuestInv.R16Shards.HeaderHashRecover
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
open InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs

/-! # `WkProcessTransactionBridgeR31`: field-mapping bridges for the R31 statement

Thin bridges connecting the already-proven local fields to the open hypotheses of
`WkProcessTransactionStmt` (`WkProcessTransactionR31.lean`):

* `ptxPhase3_relCut_strong_of_marks` closes the phase-3 `PmcMarksBoStrong` callee
  hypothesis behind the two message-marks fields (`hpm`, `hpcm`) via
  `WkPmcMarksBo.wk_process_message_call_marks_bo_of_callees` and the proved
  `WkPtxRelBasePhase3.ptxPhase3_relCut_strong`.
* `wkProcessTransactionStrongStmt_of_decode_witness` re-assembles the strong R31
  statement through the independent `WkBlockTxProcess` decode-witness route
  (`wk_process_transaction_strong_of_decode_witness`, with the phase-5 run
  discharged internally by `ptxAfterPhase4_phase5_relRun_strong_of_decode_witness`)
  instead of the `WkBlockTxProcessTail` callee route — the two routes agree on the
  same field set `{ExtraGuard, hdw, hdb, hent, hpm, hpcm, h2, hG6, hG8}`, with the
  phase-1 cut supplied by the proved `WkPtxPhase1.ptxPhase1_relCut_strong`.

The plain (non-strong) `PtxRelCut` route through
`WkBlockTxProcess.wk_process_transaction_of_decode_witness` is intentionally NOT
bridged here: `WkBlockTxProcessTail.ptxRelCut_of_strong` requires an additional
`htail_logs` (`PtxRelRun → PtxRelRunStrong`) bridge per phase cut, which is not a
thin lemma; the Tail-route `wkProcessTransactionStmt_of` already covers the plain
statement. -/

/-- Phase-3 strong cut from the two message-marks fields: discharges the
`PmcMarksBoStrong` callee hypothesis of `ptxPhase3_relCut_strong`. -/
theorem ptxPhase3_relCut_strong_of_marks
    (hpm : WorldKeepsIn MsgReady pmcTables pmcRegions pmcGlobals pmcKeep
      RetFrameResultMarksExactBo (ofString "process_message"))
    (hpcm : WorldKeepsIn MsgReady pmcTables pmcRegions pmcGlobals pmcKeep
      RetFrameResultMarksBo (ofString "process_create_message")) :
    PtxRelCutStrong R13Shards.ptxPhase3 PtxAfterPhase2 PtxAfterPhase3 :=
  ptxPhase3_relCut_strong (wk_process_message_call_marks_bo_of_callees hpm hpcm)

/-- The strong R31 `process_transaction` statement via the decode-witness route:
phase-1 and phase-3 cuts and the phase-5 run are all discharged by local proofs;
`h2` (phase-2 lane), `hent`, `hdw`/`hdb`, the marks fields, and the two phase-4
lanes (`hG6`, `hG8`) remain explicit. -/
theorem wkProcessTransactionStrongStmt_of_decode_witness
    {ExtraGuard : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat → Prop}
    (hdw : WkBalStateInit.DecodeWitnessToMptSpec @ExtraGuard)
    (hdb : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      WorldOK s → globN s "ws" ≠ 0 → ExtraGuard s (memW s (globN s "ws")))
    (hent : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), TxReadyStrong s → TxReadyFullStrong s)
    (hpm : WorldKeepsIn MsgReady pmcTables pmcRegions pmcGlobals pmcKeep
      RetFrameResultMarksExactBo (ofString "process_message"))
    (hpcm : WorldKeepsIn MsgReady pmcTables pmcRegions pmcGlobals pmcKeep
      RetFrameResultMarksBo (ofString "process_create_message"))
    (h2 : PtxRelCutStrong R13Shards.ptxPhase2 PtxAfterPhase1 PtxAfterPhase2)
    (hG6 : PtxPhase4OStep) (hG8 : PtxPhase4QStep) :
    WkProcessTransactionStrongStmt :=
  wk_process_transaction_strong_of_decode_witness hdw hdb PtxEntryFull PtxAfterPhase1
    PtxAfterPhase2 PtxAfterPhase3
    (fun s h => txReadyFullStrong_init s (hent s h))
    ptxPhase1_relCut_strong h2
    (ptxPhase3_relCut_strong_of_marks hpm hpcm)
    (ptxPhase4_relCut_strong_of hG6 hG8)

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
