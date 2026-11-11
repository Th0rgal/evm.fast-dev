import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkBlockTxProcessTail
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase4Wire

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

/-! # `WkProcessTransactionR31`: the `process_transaction` statement, phase-4 wired

The three statements below (`WkProcessTransactionStmt`, `WkProcessTransactionStrongStmt`,
`WkProcessTransactionFullStrongStmt`) are destined for
`ContractParts/StrongBridgesR31.lean`. Each is derived from the corresponding
`WkBlockTxProcessTail` callee theorem with the phase-4 cut supplied by
`WkPtxPhase4Wire.ptxPhase4_relCut_strong_of` over the two open lane theorems
(`PtxPhase4OStep` = `WkPtxPhase4O.p4Run_g6`, `PtxPhase4QStep` = `WkPtxPhase4Q.p4Run_g8`).

All other open fields (entry strengthening `hent`, decode-witness `hdw`/`hdb`, the
message-callee marks contracts `hpm`/`hpcm`, and the phase-2 cut `h2`) are
parameterized; the phase-1 and phase-3 cuts, phase-5 run, and all 14 already-proven
fields are consumed internally by `WkBlockTxProcessTail` / `WkBlockTxProcess`. -/

/-- The R31 `process_transaction` statement (plain `RetTransactionLogs`). -/
def WkProcessTransactionStmt : Prop :=
WorldKeeps TxReadyStrong
      (fun s => [(globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128), (globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64), (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352), (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384), (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96), (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40), (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128), (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128), (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128), (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52), (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["bal_index", "bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]), ("ts", []), ("bo", [24, 32, 40, 56, 64, 72, 80])]
      RetTransactionLogs (ofString "process_transaction")

/-- The R31 `process_transaction` statement (strong: `TxReadyStrong`, logs and slices). -/
def WkProcessTransactionStrongStmt : Prop :=
WorldKeeps TxReadyStrong
      (fun s => [(globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128), (globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64), (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352), (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384), (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96), (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40), (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128), (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128), (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128), (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52), (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["bal_index", "bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]), ("ts", []), ("bo", [24, 32, 40, 56, 64, 72, 80])]
      (fun s r post S Nd => RetTransactionLogs s r post S Nd ∧ PtxRetSlices s r post S Nd)
      (ofString "process_transaction")

/-- The R31 `process_transaction` statement (full-strong entry). -/
def WkProcessTransactionFullStrongStmt : Prop :=
WorldKeeps TxReadyFullStrong
      (fun s => [(globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128), (globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64), (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352), (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384), (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96), (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40), (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128), (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128), (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128), (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52), (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["bal_index", "bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]), ("ts", []), ("bo", [24, 32, 40, 56, 64, 72, 80])]
      (fun s r post S Nd => RetTransactionLogs s r post S Nd ∧ PtxRetSlices s r post S Nd)
      (ofString "process_transaction")

theorem wkProcessTransactionFullStrongStmt_of
    {ExtraGuard : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat → Prop}
    (hdw : WkBalStateInit.DecodeWitnessToMptSpec @ExtraGuard)
    (hdb : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      WorldOK s → globN s "ws" ≠ 0 → ExtraGuard s (memW s (globN s "ws")))
    (hpm : WorldKeepsIn MsgReady pmcTables pmcRegions pmcGlobals pmcKeep
      RetFrameResultMarksExactBo (ofString "process_message"))
    (hpcm : WorldKeepsIn MsgReady pmcTables pmcRegions pmcGlobals pmcKeep
      RetFrameResultMarksBo (ofString "process_create_message"))
    (h2 : PtxRelCutStrong R13Shards.ptxPhase2 PtxAfterPhase1 PtxAfterPhase2)
    (hG6 : PtxPhase4OStep) (hG8 : PtxPhase4QStep) :
    WkProcessTransactionFullStrongStmt :=
  wk_process_transaction_full_strong_of_callees hdw hdb hpm hpcm h2
    (ptxPhase4_relCut_strong_of hG6 hG8)

theorem wkProcessTransactionStrongStmt_of
    {ExtraGuard : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat → Prop}
    (hent : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), TxReadyStrong s → TxReadyFullStrong s)
    (hdw : WkBalStateInit.DecodeWitnessToMptSpec @ExtraGuard)
    (hdb : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      WorldOK s → globN s "ws" ≠ 0 → ExtraGuard s (memW s (globN s "ws")))
    (hpm : WorldKeepsIn MsgReady pmcTables pmcRegions pmcGlobals pmcKeep
      RetFrameResultMarksExactBo (ofString "process_message"))
    (hpcm : WorldKeepsIn MsgReady pmcTables pmcRegions pmcGlobals pmcKeep
      RetFrameResultMarksBo (ofString "process_create_message"))
    (h2 : PtxRelCutStrong R13Shards.ptxPhase2 PtxAfterPhase1 PtxAfterPhase2)
    (hG6 : PtxPhase4OStep) (hG8 : PtxPhase4QStep) :
    WkProcessTransactionStrongStmt :=
  wk_process_transaction_strong_of_callees_and_entry hent hdw hdb hpm hpcm h2
    (ptxPhase4_relCut_strong_of hG6 hG8)

theorem wkProcessTransactionStmt_of
    {ExtraGuard : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat → Prop}
    (hent : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), TxReadyStrong s → TxReadyFullStrong s)
    (hdw : WkBalStateInit.DecodeWitnessToMptSpec @ExtraGuard)
    (hdb : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      WorldOK s → globN s "ws" ≠ 0 → ExtraGuard s (memW s (globN s "ws")))
    (hpm : WorldKeepsIn MsgReady pmcTables pmcRegions pmcGlobals pmcKeep
      RetFrameResultMarksExactBo (ofString "process_message"))
    (hpcm : WorldKeepsIn MsgReady pmcTables pmcRegions pmcGlobals pmcKeep
      RetFrameResultMarksBo (ofString "process_create_message"))
    (h2 : PtxRelCutStrong R13Shards.ptxPhase2 PtxAfterPhase1 PtxAfterPhase2)
    (hG6 : PtxPhase4OStep) (hG8 : PtxPhase4QStep) :
    WkProcessTransactionStmt :=
  wk_process_transaction_of_callees_and_entry hent hdw hdb hpm hpcm h2
    (ptxPhase4_relCut_strong_of hG6 hG8)

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
