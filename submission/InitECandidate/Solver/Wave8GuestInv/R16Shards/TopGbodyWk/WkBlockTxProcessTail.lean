import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkBlockTxProcess
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPmcMarksBo
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase1

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

/-! # Top-Level `process_transaction` Tail Cutover (`WkBlockTxProcessTail`) -/

theorem ptxRelCut_of_strong {phase : ProgHOL 64 → ProgHOL 64}
    {A B : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop}
    (h : PtxRelCutStrong phase A B)
    (htail_logs : ∀ {F : Type} {entry s : PanSemStateFiniteExact 64 F} {tail : ProgHOL 64},
      s.code = originalRuntimeCode → B entry s → PtxRelRun entry tail s → PtxRelRunStrong entry tail s) :
    PtxRelCut phase A B := by
  intro F entry tail htail s hc hA
  exact ptxRelRun_of_strong (h entry tail (fun mid hcm hB => htail_logs hcm hB (htail mid hcm hB)) s hc hA)

theorem wk_process_transaction_full_strong_of_callees
    {ExtraGuard : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat → Prop}
    (hdw : WkBalStateInit.DecodeWitnessToMptSpec @ExtraGuard)
    (hdb : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      WorldOK s → globN s "ws" ≠ 0 → ExtraGuard s (memW s (globN s "ws")))
    (hpm : WorldKeepsIn MsgReady pmcTables pmcRegions pmcGlobals pmcKeep
      RetFrameResultMarksExactBo (ofString "process_message"))
    (hpcm : WorldKeepsIn MsgReady pmcTables pmcRegions pmcGlobals pmcKeep
      RetFrameResultMarksBo (ofString "process_create_message"))
    (h2 : PtxRelCutStrong R13Shards.ptxPhase2 PtxAfterPhase1 PtxAfterPhase2)
    (h4 : PtxRelCutStrong R13Shards.ptxPhase4 PtxAfterPhase3 PtxAfterPhase4) :
    WorldKeeps TxReadyFullStrong
      (fun s => [(globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128), (globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64), (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352), (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384), (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96), (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40), (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128), (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128), (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128), (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52), (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["bal_index", "bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]), ("ts", []), ("bo", [24, 32, 40, 56, 64, 72, 80])]
      (fun s r post S Nd => RetTransactionLogs s r post S Nd ∧ PtxRetSlices s r post S Nd)
      (ofString "process_transaction") := by
  have hpmc : PmcMarksBoStrong := wk_process_message_call_marks_bo_of_callees hpm hpcm
  have h3 : PtxRelCutStrong R13Shards.ptxPhase3 PtxAfterPhase2 PtxAfterPhase3 :=
    ptxPhase3_relCut_strong hpmc
  refine ⟨_, _, _, R13Shards.ptx_lookup, ?_⟩
  intro F s hcode hready _hparams _hnt
  have hb := ptxPhase1_relCut_strong s _
    (h2 s _ (h3 s _ (h4 s _ (ptxAfterPhase4_phase5_relRun_strong_of_decode_witness hdw hdb s))))
    s hcode (txReadyFullStrong_init s hready)
  rw [← R13Shards.ptx_phases_eq] at hb
  unfold PtxRelRunStrong PtxLogsAndSlices R13Shards.ptxCode ptxRegions ptxGlobals ptxKeep at hb
  exact hb

theorem wk_process_transaction_strong_of_callees_and_entry
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
    (h4 : PtxRelCutStrong R13Shards.ptxPhase4 PtxAfterPhase3 PtxAfterPhase4) :
    WorldKeeps TxReadyStrong
      (fun s => [(globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128), (globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64), (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352), (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384), (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96), (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40), (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128), (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128), (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128), (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52), (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["bal_index", "bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]), ("ts", []), ("bo", [24, 32, 40, 56, 64, 72, 80])]
      (fun s r post S Nd => RetTransactionLogs s r post S Nd ∧ PtxRetSlices s r post S Nd)
      (ofString "process_transaction") := by
  have hpmc : PmcMarksBoStrong := wk_process_message_call_marks_bo_of_callees hpm hpcm
  exact wk_process_transaction_strong_of_decode_witness hdw hdb
    PtxEntryFull PtxAfterPhase1 PtxAfterPhase2 PtxAfterPhase3
    (fun s hr => txReadyFullStrong_init s (hent s hr))
    ptxPhase1_relCut_strong h2 (ptxPhase3_relCut_strong hpmc) h4

theorem wk_process_transaction_of_callees_and_entry
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
    (h4 : PtxRelCutStrong R13Shards.ptxPhase4 PtxAfterPhase3 PtxAfterPhase4) :
    WorldKeeps TxReadyStrong
      (fun s => [(globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128), (globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64), (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352), (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384), (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96), (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40), (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128), (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128), (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128), (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52), (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["bal_index", "bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]), ("ts", []), ("bo", [24, 32, 40, 56, 64, 72, 80])]
      RetTransactionLogs
      (ofString "process_transaction") := by
  rcases wk_process_transaction_strong_of_callees_and_entry hent hdw hdb hpm hpcm h2 h4 with
    ⟨ps, body, ret, hlook, hrun⟩
  refine ⟨ps, body, ret, hlook, fun {F} s hcode hready hcall hnt hres => ?_⟩
  have hs := hrun s hcode hready hcall hnt hres
  exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, fun S Nd hW hD => by
    obtain ⟨S', Nd', hsub, hWT, hOG, hFO, hQ⟩ := hs.2.2.2.2 S Nd hW hD
    exact ⟨S', Nd', hsub, hWT, hOG, hFO, hQ.1⟩⟩

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
