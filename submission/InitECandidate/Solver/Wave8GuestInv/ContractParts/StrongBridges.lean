import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.DecodeTransaction
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.EncodeTransaction
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBalStateInit.WkLstPush
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBalStateInit.WkIdxStateInit
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.GbodyRunAttempt
import InitECandidate.Solver.Wave8GuestInv.R16Shards.HeaderHashRecover.HeaderHash
import InitECandidate.Solver.Wave8GuestInv.R16Shards.HeaderHashRecover.RecoverSender
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group08
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.FramePrologueException
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.FramePrologueCallees
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.GbodySysTxExecBlock
import InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12.MptSetRootKeeps
import InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12.NodeRlpFill
import InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12.BuildMptIndexed
import InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12.BuildMptIndexedWalk3
import InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12.BuildMptIndexedWalk4
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.StorageCreateFinish
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkHostPayloadHeaders
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.Depth0FrameOpen
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group09LogReturnRevert
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group10CallsCreates
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group10CallsCreatesTail
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemAlignedBridge
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.FrameStartFinishChildStep1
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.FrameStartFinishChildStep4b
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.FrameStartFinishChildStep5
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.FrameStartFinishChildStep6
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase2StrongTail2
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase2StrongTail3
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase2StrongExt
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase2StrongTail4
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase2StrongTail5
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.Group05bEnv
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.Group06Stack
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.RouterCutover
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.RouterChainCutover
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkBlockTxProcess
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkSysTxLeaves

/-! Closed strengthened contracts for the cutover rehearsal. Callers must establish
the stated entry guards before these bridges can replace weaker primitive fields. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridges

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanTerminatingBounded
open R11Shards

/-- The closed ext-code world contract preserves the EVM and chain cells.
The stronger opcode contract still requires gas and all head-frame words. -/
theorem ext_code_of_chain_strong :
    EvmKeeps (EvmAvoids (fun _ => [])) ["heap_ptr", "scratch_ptr"] (ofString "ext_code_of") ∧
    R16Shards.OpHandlersB.HeadMemBridge.ChainCellsKept
      (EvmAvoids (fun _ => [])) (ofString "ext_code_of") :=
  R16Shards.EvmEkFkPrologue.worldKeepsSc_to_evmKeeps_cc
    R16Shards.EvmEkFk.validBufList_extCodeBufs
    R16Shards.EvmEkFk.safeStepGlobals_hp_sp
    (fun _ h => h)
    (fun s hav => worldOK_of_evmInv s ⟨hav.1, hav.2.elim fun S hS => ⟨S, hS.1⟩⟩)
    R16Shards.EvmEkFk.wkSc_ext_code_of

theorem frame_chain_cells_iff {F : Type}
    (s post : Flapjack.PanSemStateFiniteExact 64 F) :
    R16Shards.EvmEkFkPrologue.ChainCellsAgree s post ↔
      R16Shards.EvmEkFk.ChainCellsAgree s post := Iff.rfl

theorem frame_chain_wf_iff {F : Type} (s : Flapjack.PanSemStateFiniteExact 64 F) :
    R16Shards.OpHandlersB.HeadMemBridge.HeadMemChainWF s ↔
      R16Shards.EvmEkFk.HeadMemChainWF s :=
  R16Shards.OpHandlersB.HeadMemBridge.headMemChainWF_iff_finishChild s

theorem frame_exception_aligned_strong :
    R16Shards.OpHandlersB.HeadMemBridge.FrameExceptionSpecA :=
  R16Shards.EvmEkFkPrologue.frame_exception_headMemChainWF

/-- The remaining prologue callee obligations stay explicit at the integration boundary. -/
theorem frame_start_strong
    (h : R16Shards.EvmEkFkPrologue.FramePrologueCalleeSpecs) :
    EvmKeeps EvmInv R16Shards.EvmEkFkPrologue.frameStartGw (ofString "frame_start") :=
  R16Shards.EvmEkFkPrologue.ek_frame_start_evmInv_of_callees h

theorem finish_child_memory_strong
    (h : R16Shards.EvmEkFk.FinishChildMemSpec) :
    R16Shards.OpHandlersB.HeadMemBridge.FinishChildMemSpec :=
  R16Shards.OpHandlersB.HeadMemBridge.finishChildMemSpec_of_leaf h

/-- Frame-start preservation expressed in the finish-child chain vocabulary. -/
theorem frame_start_aligned_strong
    (h : R16Shards.EvmEkFkPrologue.FramePrologueCalleeSpecs) :
    FunSpec (fun s => EvmInv s ∧ R16Shards.EvmEkFk.HeadMemChainWF s)
      (fun s r post => InitECandidate.Solver.Wave8Contracts.M23.Resumes r →
        InitECandidate.Solver.Wave8Contracts.M23.EvmStep
          R16Shards.EvmEkFkPrologue.frameStartGw s post ∧
        R16Shards.EvmEkFk.HeadMemChainWF post)
      (ofString "frame_start") := by
  obtain ⟨ps, body, rt, hl, hr⟩ :=
    R16Shards.EvmEkFkPrologue.frame_start_aligned_evmInv_of_callees h
  refine ⟨ps, body, rt, hl, fun s hc hs hex hnt hres => ?_⟩
  obtain ⟨hstep, hchain⟩ := hr s hc
    ⟨hs.1, (frame_chain_wf_iff s).mpr hs.2⟩ hex hnt hres
  exact ⟨hstep, (frame_chain_wf_iff _).mp hchain⟩

theorem op_mstore_aligned_spec :
    FunSpec (fun s => EvmRun s ∧ R16Shards.OpHandlersB.HeadMemAligned s)
      OpDispatchSpec.OpDispatchPost (ofString "op_mstore") :=
  R16Shards.OpHandlersB.op_mstore_aligned_spec

theorem op_mstore8_aligned_spec :
    FunSpec (fun s => EvmRun s ∧ R16Shards.OpHandlersB.HeadMemAligned s)
      OpDispatchSpec.OpDispatchPost (ofString "op_mstore8") :=
  R16Shards.OpHandlersB.op_mstore8_aligned_spec

theorem op_calldatacopy_aligned_spec :
    FunSpec (fun s => EvmRun s ∧ R16Shards.OpHandlersB.HeadMemAligned s)
      OpDispatchSpec.OpDispatchPost (ofString "op_calldatacopy") :=
  R16Shards.OpHandlersB.op_calldatacopy_aligned_spec

theorem op_codecopy_aligned_spec :
    FunSpec (fun s => EvmRun s ∧ R16Shards.OpHandlersB.HeadMemAligned s)
      OpDispatchSpec.OpDispatchPost (ofString "op_codecopy") :=
  R16Shards.OpHandlersB.op_codecopy_aligned_spec

theorem op_returndatacopy_aligned_spec :
    FunSpec (fun s => EvmRun s ∧ R16Shards.OpHandlersB.HeadMemAligned s)
      OpDispatchSpec.OpDispatchPost (ofString "op_returndatacopy") :=
  R16Shards.OpHandlersB.op_returndatacopy_aligned_spec

theorem op_mcopy_aligned_spec :
    FunSpec (fun s => EvmRun s ∧ R16Shards.OpHandlersB.HeadMemAligned s)
      OpDispatchSpec.OpDispatchPost (ofString "op_mcopy") :=
  R16Shards.OpHandlersB.op_mcopy_aligned_spec

theorem op_mload_aligned_spec :
    FunSpec (fun s => EvmRun s ∧ R16Shards.OpHandlersB.HeadMemAligned s)
      OpDispatchSpec.OpDispatchPost (ofString "op_mload") :=
  R16Shards.OpHandlersB.op_mload_aligned_spec

/-- The extcodecopy handler additionally requires preservation of every aligned
head-frame word by ext_code_of. This premise must be discharged separately. -/
theorem op_extcodecopy_aligned_spec
    (h_ext_code_of : R16Shards.OpHandlersB.ExtCodeOfHeadSpec) :
    FunSpec (fun s => EvmRun s ∧ R16Shards.OpHandlersB.HeadMemAligned s)
      OpDispatchSpec.OpDispatchPost (ofString "op_extcodecopy") :=
  R16Shards.OpHandlersB.op_extcodecopy_aligned_spec h_ext_code_of

theorem wk_header_hash_strong :
    WorldKeeps
      (fun s => WorldOK s ∧ R16Shards.HeaderHashRecover.HeaderOKStrong s ∧
        IvlsDisj [(locN s "out", 32)]
          ((locN s "h", 248) :: R16Shards.HeaderHashRecover.headerSlices s (locN s "h")))
      (fun s => [(locN s "out", 32),
        (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "header_hash") :=
  R16Shards.HeaderHashRecover.wk_header_hash_strong

theorem wk_recover_sender_with_chain_id_strong :
    WorldKeeps (fun s => WorldOK s ∧ R16Shards.HeaderHashRecover.TxValidRecoverReady s)
      (fun s =>
        [(locN s "out20", 20),
         (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
         (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
         (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "recover_sender_with_chain_id") :=
  R16Shards.HeaderHashRecover.wk_recover_sender_with_chain_id_strong

theorem wk_encode_transaction_strong :
    WorldKeeps (fun s => WorldOK s ∧ R16Shards.WkBlockTxEnc.TxValidEncodeReady s)
      (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "encode_transaction") :=
  R16Shards.WkBlockTxEnc.wk_encode_transaction_strong

theorem wk_decode_transaction_strong :
    WorldKeeps (fun s => WorldOK s ∧ R16Shards.WkBlockTxEnc.DecodeTxReady s)
      (fun _ => []) ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetDecodedTx (ofString "decode_transaction") :=
  R16Shards.WkBlockTxEnc.wk_decode_transaction_strong

theorem wk_decode_transaction_noExtra :
    WorldKeeps WorldOK (fun _ => []) ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "decode_transaction") :=
  R16Shards.WkBlockTxEnc.wk_decode_transaction_noExtra

theorem wk_lst_push_strong :
    WorldKeeps R16Shards.WkBal.BoListArgStrong (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetListSlot (ofString "lst_push") :=
  R16Shards.WkBal.wk_lst_push_strong

theorem gbody_run_attempt_strong : R16Shards.TopGbodyWk.GBody.run_attempt_strong :=
  R16Shards.TopGbodyWk.gbody_run_attempt_strong_of

/-- Whole-function termination under the strengthened block entry and slice-preservation
contracts. These premises must be established before replacing the primitive field. -/
theorem gbody_execute_block_strong : R16Shards.TopGbodyWk.GBody.execute_block_strong :=
  R16Shards.TopGbodyWk.gbody_execute_block_strong

theorem mk_mpt_root_strong :
    R16Shards.MptC10C12.MptKeepsStrong R16Shards.MptC10C12.MptObjReadyStrong
      (fun s => [(locN s "out", 32),
                 (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]),
       ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (ofString "mpt_root") :=
  R16Shards.MptC10C12.«mk_mpt_root_strong»

theorem mk_mpt_set_strong :
    R16Shards.MptC10C12.MptKeepsStrong R16Shards.MptC10C12.MptSetReadyStrong
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]),
       ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (ofString "mpt_set") :=
  R16Shards.MptC10C12.«mk_mpt_set_strong»

theorem wk_mpt_from_witness_strong :
    WorldKeeps R16Shards.EvmEkFk.StorageCreateFinish.MptFromWitnessReady (fun _ => [])
      ["heap_ptr", "scratch_ptr"] EvmBase.stdKeep RetMptObj (ofString "mpt_from_witness") :=
  R16Shards.EvmEkFk.«wk_mpt_from_witness_strong»

theorem decode_witness_to_mpt_spec :
    R16Shards.EvmEkFk.StorageCreateFinish.DecodeWitnessToMptSpec
      @R16Shards.EvmEkFk.StorageCreateFinish.NodeDbSlicesBounded :=
  R16Shards.EvmEkFk.StorageCreateFinish.decode_witness_to_mpt_spec

theorem decode_witness_to_mpt_spec_wkBal :
    R16Shards.WkBalStateInit.DecodeWitnessToMptSpec
      @R16Shards.EvmEkFk.StorageCreateFinish.NodeDbSlicesBounded :=
  R16Shards.EvmEkFk.StorageCreateFinish.decode_witness_to_mpt_spec

theorem wk_state_init_strong :
    WorldReturnsIn
      (fun s => StateInitReady s ∧
        R16Shards.EvmEkFk.StorageCreateFinish.NodeDbSlicesBounded s (locN s "nodedb"))
      (fun s => if locN s "codedb" = 0 then [] else [locN s "codedb"])
      (fun _ => [])
      ["bs", "heap_ptr", "journal", "journal_cap", "journal_n", "scratch_ptr", "sk_buf", "ts", "ws"]
      [("ws", []), ("bs", []),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetStateInit (ofString "state_init") :=
  R16Shards.WkBalStateInit.wk_state_init_of_decode_witness
    decode_witness_to_mpt_spec_wkBal
    (fun _ _ _ hAs hAb _ hhp hfr h =>
      R16Shards.EvmEkFk.StorageCreateFinish.dbTableAt_of_frame_so hAs hAb hhp hfr h)

theorem mpt_from_witness_preserves_witnessDbOK :
    FunSpec (fun s => R16Shards.EvmEkFk.StorageCreateFinish.MptFromWitnessReady s ∧
        R16Shards.EvmEkFk.StorageCreateFinish.WitnessDbOK s)
      (fun s r post => Resumes r →
        WorldStep (fun _ => []) ["heap_ptr", "scratch_ptr"] EvmBase.stdKeep RetMptObj s r post ∧
        globN post "scratch_ptr" = globN s "scratch_ptr" ∧
        R16Shards.EvmEkFk.StorageCreateFinish.WitnessDbOK post)
      (ofString "mpt_from_witness") :=
  R16Shards.EvmEkFk.StorageCreateFinish.mpt_from_witness_preserves_witnessDbOK

theorem wk_nodedb_build_strong :
    WorldKeeps R16Shards.TopGbodyWk.NodeDbBuildReady
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetNodeDb (ofString "nodedb_build") :=
  R16Shards.TopGbodyWk.«wk_nodedb_build_strong»

theorem wk_nodedb_build_nodedb_bounded :
    WorldKeeps R16Shards.TopGbodyWk.NodeDbSlicesReady
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      R16Shards.TopGbodyWk.RetNodeDbBounded (ofString "nodedb_build") :=
  R16Shards.TopGbodyWk.«wk_nodedb_build_nodedb_bounded»

theorem fk_frame_open_bounded :
    KeepsOn R16Shards.OpHandlersB.HeadMemBridge.FrameOpenReadyB EvmMsgReady
      (ofString "frame_open") :=
  R16Shards.EvmEkFk.fk_frame_open_bounded

theorem fk_frame_open_codeStrong :
    KeepsOn R16Shards.EvmEkFk.FrameOpenReadyCodeStrong R16Shards.EvmEkFk.EvmMsgReadyCodeStrong
      (ofString "frame_open") :=
  R16Shards.EvmEkFk.fk_frame_open_codeStrong

theorem frame_open_headMemChainWF_B' :
    KeepsOn R16Shards.OpHandlersB.HeadMemBridge.FrameOpenReadyB
      R16Shards.OpHandlersB.HeadMemBridge.HeadMemChainWF (ofString "frame_open") :=
  R16Shards.OpHandlersB.HeadMemBridge.frame_open_headMemChainWF_B'

theorem gbody_node_rlp_strong
    (hf : TerminatingFunBoundedOn R16Shards.MptC10C12.NrfStrong.NodeRlpReadyStrong
      (ofString "_node_rlp_fill") K.«_node_rlp_fill»)
    (hm : TerminatingFunBoundedOn GuestInv (ofString "mpt_fail") K.«mpt_fail»)
    (hr : ReadOnlyFn (ofString "mpt_fail")) :
    TerminatingFunBoundedOn R16Shards.MptC10C12.NrfStrong.NodeRlpReadyNonNull
      (ofString "node_rlp") K.«node_rlp» :=
  R16Shards.MptC10C12.NrfStrong.gbody_node_rlp_strong hf hm hr

theorem gbody_node_hash_strong
    (ha : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (hk : TerminatingFunBoundedOn GuestInv (ofString "keccak256") K.«keccak256»)
    (hn : TerminatingFunBoundedOn R16Shards.MptC10C12.NrfStrong.NodeRlpReadyNonNull
      (ofString "node_rlp") K.«node_rlp») :
    TerminatingFunBoundedOn R16Shards.MptC10C12.NrfStrong.NodeRlpReadyNonNull
      (ofString "node_hash") K.«node_hash» :=
  R16Shards.MptC10C12.NrfStrong.gbody_node_hash_strong ha hk hn

theorem gbody__node_rlp_fill_strong :
    R16Shards.MptC10C12.NrfStrong.GBody.«_node_rlp_fill_strong» :=
  R16Shards.MptC10C12.NrfStrong.«gbody__node_rlp_fill_strong»

theorem gbody_mpt_root_strong
    (hm : TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy»)
    (hn : TerminatingFunBoundedOn R16Shards.MptC10C12.NrfStrong.NodeRlpReadyNonNull
      (ofString "node_hash") K.«node_hash») :
    TerminatingFunBoundedOn R16Shards.MptC10C12.NrfStrong.MptObjReadyStrong
      (ofString "mpt_root") K.«mpt_root» :=
  R16Shards.MptC10C12.NrfStrong.gbody_mpt_root_strong hm hn

theorem gbody_build_mpt_indexed_strong :
    type_of% @R16Shards.MptC10C12.gbody_build_mpt_indexed_strong :=
  R16Shards.MptC10C12.gbody_build_mpt_indexed_strong

theorem wkSc_ws_storage_trie_strong :
    R16WkAcctWs.WorldKeepsSc (fun s => WorldOK s ∧ R16Shards.EvmEkFk.StorageCreateFinish.WitnessDbOK s)
      (R16WkAcctWs.bufRegions []) ["heap_ptr", "scratch_ptr"] EvmBase.stdKeep NoExtra
      (ofString "ws_storage_trie") :=
  R16Shards.EvmEkFk.wkSc_ws_storage_trie_strong

theorem wk_ws_storage_trie_strong :
    WorldKeeps (fun s => WorldOK s ∧ R16Shards.EvmEkFk.StorageCreateFinish.WitnessDbOK s)
      (fun _ => []) ["heap_ptr", "scratch_ptr"] EvmBase.stdKeep NoExtra
      (ofString "ws_storage_trie") :=
  R16Shards.EvmEkFk.wk_ws_storage_trie_strong

theorem wk_ws_get_storage_strong :
    WorldKeeps (fun s => WorldOK s ∧ R16Shards.EvmEkFk.StorageCreateFinish.WitnessDbOK s)
      (R16WkAcctWs.bufRegions R16Shards.EvmEkFk.wsAcctBufs)
      ["heap_ptr", "scratch_ptr"] EvmBase.stdKeep NoExtra (ofString "ws_get_storage") :=
  R16Shards.EvmEkFk.«wk_ws_get_storage_strong»

theorem wk_get_storage_original_strong :
    WorldKeeps (fun s => WorldOK s ∧ R16Shards.EvmEkFk.StorageCreateFinish.WitnessDbOK s)
      (R16WkAcctWs.bufRegions R16Shards.EvmEkFk.wsAcctBufs)
      ["heap_ptr", "scratch_ptr"] EvmBase.stdKeep NoExtra (ofString "get_storage_original") :=
  R16Shards.EvmEkFk.«wk_get_storage_original_strong»

theorem wk_get_storage_strong :
    WorldKeeps (fun s => WorldOK s ∧ R16Shards.EvmEkFk.StorageCreateFinish.WitnessDbOK s)
      (R16WkAcctWs.bufRegions R16Shards.EvmEkFk.extCodeBufs)
      ["heap_ptr", "scratch_ptr"] EvmBase.stdKeep NoExtra (ofString "get_storage") :=
  R16Shards.EvmEkFk.«wk_get_storage_strong»

theorem ek_get_storage_original_strong :
    EvmKeeps
      (fun s =>
        EvmAvoids
          (fun s =>
            [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
             (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
             (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64)]) s ∧
        R16Shards.EvmEkFk.StorageCreateFinish.WitnessDbOK s)
      ["heap_ptr", "scratch_ptr"] (ofString "get_storage_original") :=
  R16Shards.EvmEkFk.«ek_get_storage_original_strong»

theorem ek_get_storage_strong :
    EvmKeeps
      (fun s =>
        EvmAvoids (R16WkAcctWs.bufRegions R16Shards.EvmEkFk.extCodeBufs) s ∧
        R16Shards.EvmEkFk.StorageCreateFinish.WitnessDbOK s)
      ["heap_ptr", "scratch_ptr"] (ofString "get_storage") :=
  R16Shards.EvmEkFk.«ek_get_storage_strong»

theorem eps_get_storage_original_strong :
    R14Shards.OpHandlersA.EvmPreservingSpec
      R16Shards.EvmEkFk.StorageCreateFinish.WitnessDbOK
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧
        R11Shards.OpDispatchSpec.evmR post = R11Shards.OpDispatchSpec.evmR s ∧
        R16Shards.EvmEkFk.StorageCreateFinish.WitnessDbOK post)
      (ofString "get_storage_original") :=
  R16Shards.EvmEkFk.eps_get_storage_original_strong

theorem eps_get_storage_strong :
    R14Shards.OpHandlersA.EvmPreservingSpec
      R16Shards.EvmEkFk.StorageCreateFinish.WitnessDbOK
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧
        R11Shards.OpDispatchSpec.evmR post = R11Shards.OpDispatchSpec.evmR s ∧
        R16Shards.EvmEkFk.StorageCreateFinish.WitnessDbOK post)
      (ofString "get_storage") :=
  R16Shards.EvmEkFk.eps_get_storage_strong

theorem evm_cells_get_storage_original_strong :
    FunSpec (fun s => EvmInv s ∧ R16Shards.EvmEkFk.StorageCreateFinish.WitnessDbOK s)
      (fun s r post => InitECandidate.Solver.Wave8Contracts.M23.Resumes r →
        EvmStep ["heap_ptr", "scratch_ptr"] s post ∧
        R16Shards.EvmEkFk.StorageCreateFinish.WitnessDbOK post ∧
        R11Shards.OpDispatchSpec.evmR post = R11Shards.OpDispatchSpec.evmR s ∧
        ∀ ec ∈ evmChain s,
          memW post (ec.1 + 24) = memW s (ec.1 + 24) ∧
          memW post (ec.1 + 32) = memW s (ec.1 + 32) ∧
          memW post (ec.1 + 40) = memW s (ec.1 + 40) ∧
          memW post (ec.2 + 48) = memW s (ec.2 + 48) ∧
          memW post (ec.2 + 56) = memW s (ec.2 + 56))
      (ofString "get_storage_original") :=
  R16Shards.EvmEkFk.evm_cells_get_storage_original_strong

theorem evm_cells_get_storage_strong :
    FunSpec (fun s => EvmInv s ∧ R16Shards.EvmEkFk.StorageCreateFinish.WitnessDbOK s)
      (fun s r post => InitECandidate.Solver.Wave8Contracts.M23.Resumes r →
        EvmStep ["heap_ptr", "scratch_ptr"] s post ∧
        R16Shards.EvmEkFk.StorageCreateFinish.WitnessDbOK post ∧
        R11Shards.OpDispatchSpec.evmR post = R11Shards.OpDispatchSpec.evmR s ∧
        ∀ ec ∈ evmChain s,
          memW post (ec.1 + 24) = memW s (ec.1 + 24) ∧
          memW post (ec.1 + 32) = memW s (ec.1 + 32) ∧
          memW post (ec.1 + 40) = memW s (ec.1 + 40) ∧
          memW post (ec.2 + 48) = memW s (ec.2 + 48) ∧
          memW post (ec.2 + 56) = memW s (ec.2 + 56))
      (ofString "get_storage") :=
  R16Shards.EvmEkFk.evm_cells_get_storage_strong

theorem op_return_specA :
    R16Shards.OpHandlersB.Group09ChainWF.OpHandlerSpecA (ofString "op_return") :=
  R16Shards.OpHandlersB.Group09ChainWF.op_return_specA

theorem op_revert_specA :
    R16Shards.OpHandlersB.Group09ChainWF.OpHandlerSpecA (ofString "op_revert") :=
  R16Shards.OpHandlersB.Group09ChainWF.op_revert_specA

theorem op_mcopy_specA :
    R16Shards.OpHandlersB.Group09ChainWF.OpHandlerSpecA (ofString "op_mcopy") :=
  R16Shards.OpHandlersB.Group09ChainWF.op_mcopy_specA

theorem fcStackPushW : R16Shards.OpHandlersB.HeadMemBridge.FcClosed.FcStackPushStepW :=
  R16Shards.OpHandlersB.HeadMemBridge.FcClosed.fcStackPushW

theorem fcAddrToU256W : R16Shards.OpHandlersB.HeadMemBridge.FcClosed.FcAddrToU256StepW :=
  R16Shards.OpHandlersB.HeadMemBridge.FcClosed.fcAddrToU256W

theorem fcSetRetdataW : R16Shards.OpHandlersB.HeadMemBridge.FcClosed.FcSetRetdataStepW :=
  R16Shards.OpHandlersB.HeadMemBridge.FcClosed.fcSetRetdataW

theorem fcMinTailW : R16Shards.OpHandlersB.HeadMemBridge.FcClosed.FcMinTailStepW :=
  R16Shards.OpHandlersB.HeadMemBridge.FcClosed.fcMinTailW

theorem create_finish_specs : R16Shards.EvmEkFk.CreateFinishSpecs :=
  R16Shards.EvmEkFk.create_finish_specs

theorem finish_child_finishPost :
    FunSpec FinishReady R16Shards.EvmEkFk.FinishPost (ofString "finish_child") :=
  R16Shards.EvmEkFk.finish_child_finishPost

theorem finish_child_spec_closed :
    type_of% @Wave8GuestInv.finish_child_spec :=
  R16Shards.EvmEkFk.finish_child_spec_c00

theorem finishChildMemSpec :
    R16Shards.OpHandlersB.HeadMemBridge.FinishChildMemSpec :=
  R16Shards.EvmEkFk.headMemBridge_finishChildMemSpec

theorem finishChildSpecA :
    R16Shards.OpHandlersB.HeadMemBridge.FinishChildSpecA :=
  R16Shards.OpHandlersB.HeadMemBridge.finish_child_spec_aligned
    R16Shards.EvmEkFk.headMemBridge_finishChildSpecU
    R16Shards.EvmEkFk.headMemBridge_finishChildMemSpec

theorem gbody_run_frames_aligned_closed :
    type_of% @(R16Shards.OpHandlersB.HeadMemBridge.gbody_run_frames_aligned_of_createFinish
      (hCF := R16Shards.EvmEkFk.create_finish_specs)) :=
  fun bf be bx bd hd =>
    R16Shards.OpHandlersB.HeadMemBridge.gbody_run_frames_aligned_fc
      bf be bx bd
      R16Shards.EvmEkFk.headMemBridge_finishChildSpecU
      R16Shards.EvmEkFk.headMemBridge_finishChildMemSpec
      hd

theorem op_selfdestruct_specA_g10 :
    type_of% @R16Shards.OpHandlersB.op_selfdestruct_specA :=
  R16Shards.OpHandlersB.op_selfdestruct_specA

theorem op_create_specA_g10 :
    type_of% @R16Shards.OpHandlersB.op_create_specA_g10 :=
  R16Shards.OpHandlersB.op_create_specA_g10

theorem op_create2_specA_g10 :
    type_of% @R16Shards.OpHandlersB.op_create2_specA_g10 :=
  R16Shards.OpHandlersB.op_create2_specA_g10

theorem epsA_calculate_message_call_gas_vals_g10 :
    type_of% @R16Shards.OpHandlersB.epsA_calculate_message_call_gas_vals_g10 :=
  R16Shards.OpHandlersB.epsA_calculate_message_call_gas_vals_g10

theorem epsA_calculate_delegation_cost_g10 :
    type_of% @R16Shards.OpHandlersB.epsA_calculate_delegation_cost_g10 :=
  R16Shards.OpHandlersB.epsA_calculate_delegation_cost_g10

theorem epsA_charge_gas_exact_g10 :
    type_of% @R16Shards.OpHandlersB.epsA_charge_gas_exact_g10 :=
  R16Shards.OpHandlersB.epsA_charge_gas_exact_g10

theorem epsA_add_sat_ge_g10 :
    type_of% @R16Shards.OpHandlersB.epsA_add_sat_ge_g10 :=
  R16Shards.OpHandlersB.epsA_add_sat_ge_g10

theorem phase2_b2a_l8_empty_alloc_bound :
    type_of% @R13Shards.phase2_b2a_l8_empty_alloc_bound :=
  R13Shards.phase2_b2a_l8_empty_alloc_bound

theorem log_append_body_unified_g09 :
    type_of% @R16Shards.OpHandlersB.log_append_body_unified_g09 :=
  R16Shards.OpHandlersB.log_append_body_unified_g09

theorem op_log_tail_log_append_pc_ret_g09 :
    type_of% @R16Shards.OpHandlersB.op_log_tail_log_append_pc_ret_g09 :=
  R16Shards.OpHandlersB.op_log_tail_log_append_pc_ret_g09

theorem op_log_topic_while_both_g09 :
    type_of% @R16Shards.OpHandlersB.op_log_topic_while_both_g09 :=
  R16Shards.OpHandlersB.op_log_topic_while_both_g09

theorem phase2_b2a_l9_ite_bound :
    type_of% @R13Shards.phase2_b2a_l9_ite_bound :=
  R13Shards.phase2_b2a_l9_ite_bound

theorem mk_mpt_set_eff_strong :
    type_of% @R16Shards.MptC10C12.mk_mpt_set_eff_strong :=
  R16Shards.MptC10C12.mk_mpt_set_eff_strong

theorem wk_build_mpt_indexed_strong :
    type_of% @R16Shards.MptC10C12.wk_build_mpt_indexed_strong :=
  R16Shards.MptC10C12.wk_build_mpt_indexed_strong

theorem fcStackPushStepW_s23 :
    type_of% @R16Shards.EvmEkFk.fcStackPushStepW :=
  R16Shards.EvmEkFk.fcStackPushStepW

theorem fcAddrToU256StepW_s23 :
    type_of% @R16Shards.EvmEkFk.fcAddrToU256StepW :=
  R16Shards.EvmEkFk.fcAddrToU256StepW

theorem fcMinTailStepW_s23 :
    type_of% @R16Shards.EvmEkFk.fcMinTailStepW :=
  R16Shards.EvmEkFk.fcMinTailStepW

theorem fcSetRetdataStepW_s4b :
    type_of% @R16Shards.EvmEkFk.fcSetRetdataStepW :=
  R16Shards.EvmEkFk.fcSetRetdataStepW

theorem fcLogLoop_step_s5 :
    type_of% @R16Shards.EvmEkFk.fcLogLoop_step :=
  R16Shards.EvmEkFk.fcLogLoop_step

private theorem worldStepSc_preserves_head_ev_words {F : Type}
    {B : R16WkAcctWs.BufList} {gw : List String} {keep : List (String × List Nat)}
    {s post : Flapjack.PanSemStateFiniteExact 64 F}
    {r : Option (Flapjack.PanSemResultExact 64)}
    (hB : R16WkAcctWs.ValidBufList B)
    (hInv : EvmInv s)
    (hstep : R16WkAcctWs.WorldStepSc (R16WkAcctWs.bufRegions B) gw keep NoExtra s r post) :
    ∀ off, off + 8 ≤ 280 → off % 8 = 0 →
      memW post (globN s "ev" + off) = memW s (globN s "ev" + off) := by
  intro off hoff hoff8
  obtain ⟨hAs, S, hInvAt⟩ := hInv
  obtain ⟨hW, _, _, _, hFW_all, _, _, _, hFO_disj, hAT_fo, _, hRoles, _⟩ := hInvAt
  obtain ⟨Nd_at, hTr_at, hAT_at⟩ := hAT_fo
  set L : List Nat := S.filter (fun t => decide (∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ t))
  have hL_local : ∀ t ∈ L, ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ t :=
    fun t ht => of_decide_eq_true (List.mem_filter.1 ht).2
  have hWT_at_s : WorldTypedWith s S Nd_at := ⟨hW.1, hW.2.1, hW.2.2.1, hTr_at⟩
  obtain ⟨S0, hS0_sub, _, _, hWT0⟩ :=
    R16Shards.EvmEkFk.StorageCreateFinish.worldTypedWith_erase_many hWT_at_s L hL_local
  obtain ⟨⟨hAp, hhp, _, _, hWS⟩, _⟩ := hstep
  obtain ⟨S0', Nd', _, _, hog0, hfr0, _⟩ :=
    hWS S0 Nd_at hWT0 (R16WkAcctWs.validBufList_disj hB hWT0)
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s :=
    R16Shards.OpHandlersB.HeadMemBridge.head_mem_evmChain s
  have hFW := hFW_all _ hhead
  obtain ⟨hb1, _, _, _⟩ := InitECandidate.Solver.Wave8Contracts.M23.frameWF_bounds hAs.2 hFW
  have he1_8 : (globN s "ev") % 8 = 0 := (hFW.1 (globN s "ev", 280) (by simp)).2.1
  have hal : Allocated s (globN s "ev", 280) := by
    rcases R16Shards.EvmEkFk.StorageCreateFinish.frameObject_zero_or_allocated hAs.2 hFW
        (o := (globN s "ev", 280)) (by simp [frameObjects]) with hz | hal | hin
    · simp at hz
    · exact hal
    · exfalso
      have hin_scr := (hFW.1 (globN s "ev", 280) (by simp)).1
      dsimp only [Inside] at hin hin_scr
      have hfm_le : globN s "frame_mem_ptr" ≤ globN s "scratch_ptr" := hAs.2.2.2.2.1
      omega
  have ho_fl : (globN s "ev", 280) ∈ ((evmChain s).map (frameObjects s)).flatten :=
    List.mem_flatten.2 ⟨frameObjects s (globN s "ev", globN s "cur_cont"),
      List.mem_map.2 ⟨_, hhead, rfl⟩, by simp [frameObjects]⟩
  have ho_ow0 : ∀ j ∈ worldOwned s S0 Nd_at, Disj (globN s "ev", 280) j := by
    intro j hj
    unfold worldOwned at hj
    rcases List.mem_append.1 hj with hj1 | hj_nd
    · rcases List.mem_append.1 hj1 with hj_tab | hj_fix
      · obtain ⟨u, hu0, hi⟩ := List.mem_flatMap.1 hj_tab
        exact (hFO_disj _ hhead _ (by simp [frameObjects])).1 u (hS0_sub u hu0) j hi
      · exact (hFO_disj _ hhead _ (by simp [frameObjects])).2 j hj_fix
    · exact hAT_at _ ho_fl j hj_nd
  have ho_bufs : ∀ j ∈ R16WkAcctWs.bufRegions B s, Disj (globN s "ev", 280) j := by
    intro j hj
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hj
    obtain ⟨sz, hgb, _, hle_sz⟩ := hB p hp
    have hfix : bufferRegion s (p.1, sz) ∈ fixedObjects s := by
      unfold fixedObjects
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
      exact List.mem_map.2 ⟨(p.1, sz), hgb, rfl⟩
    have hd := (hFO_disj _ hhead (globN s "ev", 280) (by simp [frameObjects])).2 _ hfix
    by_cases hz : globN s p.1 = 0
    · exact Or.inr (Or.inl (by simp [bufferRegion, hz]))
    · simp only [bufferRegion, hz, ↓reduceIte] at hd ⊢
      rcases hd with h0 | h0 | h1 | h2
      · exact Or.inl h0
      · exact Or.inr (Or.inl (by dsimp only at h0 ⊢; omega))
      · exact Or.inr (Or.inr (Or.inl h1))
      · exact Or.inr (Or.inr (Or.inr (by dsimp only at h2 ⊢; omega)))
  have hkeep_shape : ∀ j ∈ worldOwned s S0 Nd_at ++ R16WkAcctWs.bufRegions B s ++ [freeGap s],
      j = (0, 0) ∨ j.1 % 8 = 0 ∨ j.2 ≠ 0 := by
    intro j hj
    rcases List.mem_append.1 hj with hj12 | hfg
    · rcases List.mem_append.1 hj12 with hj_ow | hj_R
      · exact R16Shards.EvmEkFk.StorageCreateFinish.worldOwned_well_shaped hWT0 j hj_ow
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hj_R
        unfold bufferRegion
        by_cases hz : globN s p.1 = 0
        · exact Or.inl (by simp [hz])
        · by_cases hp2 : p.2 = 0
          · right; left
            obtain ⟨sz, hgb, _⟩ := hB p hp
            have hfix : (globN s p.1, if globN s p.1 = 0 then 0 else sz) ∈ fixedObjects s := by
              unfold fixedObjects
              apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
              exact List.mem_map.2 ⟨(p.1, sz), hgb, rfl⟩
            rcases hWT0.2.2.1.1 _ hfix with h0 | ⟨_, hw⟩
            · simp [hz] at h0
              exact absurd h0 ((by decide : ∀ gn ∈ globalBuffers, gn.2 ≠ 0) (p.1, sz) hgb)
            · exact hw.1
          · exact Or.inr (Or.inr (by simp [hz, hp2]))
    · rw [List.mem_singleton] at hfg; subst hfg
      exact Or.inr (Or.inl hAs.2.2.2.2.2.2.2.1)
  have hunhit : (InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post (globN s "ev", 280)) :=
    (R16Shards.EvmEkFk.StorageCreateFinish.allocated_survives_world_frame
      hAs.2 hAp.2 hhp hal ho_ow0 ho_bufs hkeep_shape hfr0 hog0).1
  exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit
    hunhit (by omega) hb1 ⟨by dsimp only; omega, by dsimp only; omega⟩

theorem extCodeOfHeadSpec_closed : R16Shards.OpHandlersB.ExtCodeOfHeadSpec := by
  obtain ⟨ps, body, rt, hlk, hbody⟩ := R16Shards.EvmEkFk.wkSc_ext_code_of
  refine ⟨ps, body, rt, hlk, ?_⟩
  intro F s hc hInv _ hvalid hnt
  have hW : WorldOK s := ⟨hInv.1, let ⟨S, hInvAt⟩ := hInv.2; ⟨S, hInvAt.1⟩⟩
  constructor
  · intro v hrv
    have hres : InitECandidate.Solver.Wave8Contracts.M23.Resumes
        (Flapjack.PanSemStateFiniteExact.evaluateHOLFiniteState s body).1 := Or.inl ⟨v, hrv⟩
    have hstep := hbody s hc hW hvalid hnt hres
    obtain ⟨hevm, hevmR, _⟩ :=
      R16Shards.EvmEkFk.StorageCreateFinish.evmStep_and_cells_of_worldStepSc
        R16Shards.EvmEkFk.validBufList_extCodeBufs R16Shards.EvmEkFk.safeStepGlobals_hp_sp
        hInv.1 hInv.2 hstep
    exact ⟨hevm.1, hevm.2.2.2, le_of_eq hevmR,
      ⟨hevm.2.2.1, hevmR,
       worldStepSc_preserves_head_ev_words
         R16Shards.EvmEkFk.validBufList_extCodeBufs hInv hstep⟩⟩
  · intro herr
    obtain ⟨ev, hev⟩ := herr
    have hres : InitECandidate.Solver.Wave8Contracts.M23.Resumes
        (Flapjack.PanSemStateFiniteExact.evaluateHOLFiniteState s body).1 :=
      Or.inr ⟨ofString "EvmErr", ev, hev, by decide⟩
    have hstep := hbody s hc hW hvalid hnt hres
    obtain ⟨hevm, hevmR, _⟩ :=
      R16Shards.EvmEkFk.StorageCreateFinish.evmStep_and_cells_of_worldStepSc
        R16Shards.EvmEkFk.validBufList_extCodeBufs R16Shards.EvmEkFk.safeStepGlobals_hp_sp
        hInv.1 hInv.2 hstep
    exact ⟨hevm.1, hevm.2.2.2, le_of_eq hevmR⟩

theorem op_extcodecopy_aligned_spec_closed :
    FunSpec (fun s => EvmRun s ∧ R16Shards.OpHandlersB.HeadMemAligned s)
      OpDispatchSpec.OpDispatchPost (ofString "op_extcodecopy") :=
  R16Shards.OpHandlersB.op_extcodecopy_aligned_spec extCodeOfHeadSpec_closed

theorem op_delegatecall_specA_g10 :
    type_of% @R16Shards.OpHandlersB.op_delegatecall_specA_g10 :=
  R16Shards.OpHandlersB.op_delegatecall_specA_g10

theorem phase2_b2a_bound :
    type_of% @R13Shards.phase2_b2a_bound :=
  R13Shards.phase2_b2a_bound

theorem ek_frame_start_c08_of :
    type_of% @R16Shards.EvmEkFk.ek_frame_start_c08_of :=
  R16Shards.EvmEkFk.ek_frame_start_c08_of

private theorem chainLinks_g10_iff_bridge (m : Nat → Nat) :
    ∀ xs : List Ivl, R16Shards.OpHandlersB.Group10.ChainLinks m xs ↔
      R16Shards.OpHandlersB.HeadMemBridge.ChainLinks m xs
  | [] => Iff.rfl
  | [_] => Iff.rfl
  | _ :: b :: rest =>
    and_congr_right fun _ => chainLinks_g10_iff_bridge m (b :: rest)

private theorem chainLinks_g09_iff_bridge (m : Nat → Nat) :
    ∀ xs : List Ivl, R16Shards.OpHandlersB.Group09ChainWF.ChainLinks m xs ↔
      R16Shards.OpHandlersB.HeadMemBridge.ChainLinks m xs
  | [] => Iff.rfl
  | [_] => Iff.rfl
  | _ :: b :: rest =>
    and_congr_right fun _ => chainLinks_g09_iff_bridge m (b :: rest)

theorem headMemChainWF_g10_iff_bridge {F : Type}
    (s : Flapjack.PanSemStateFiniteExact 64 F) :
    R16Shards.OpHandlersB.Group10.HeadMemChainWF s ↔
      R16Shards.OpHandlersB.HeadMemBridge.HeadMemChainWF s :=
  and_congr_right fun _ =>
    and_congr_right fun _ => chainLinks_g10_iff_bridge (memW s) (evmChain s)

theorem headMemChainWF_g09_iff_bridge {F : Type}
    (s : Flapjack.PanSemStateFiniteExact 64 F) :
    R16Shards.OpHandlersB.Group09ChainWF.HeadMemChainWF s ↔
      R16Shards.OpHandlersB.HeadMemBridge.HeadMemChainWF s :=
  and_congr_right fun _ =>
    and_congr_right fun _ => chainLinks_g09_iff_bridge (memW s) (evmChain s)

/-- Unified `HeadMemBridge.HeadMemChainWF`-carrying opcode handler contract matching
`HeadMemBridge.OpDispatchSpecA`'s precondition and postcondition. -/
def OpHandlerChainSpecA (fname : Flapjack.Pancake.PanLang.MlS) : Prop :=
  FunSpec (fun s => EvmInv s ∧ R16Shards.OpHandlersB.HeadMemBridge.HeadMemChainWF s ∧ ¬ EvmDone s)
    (fun s r post =>
      ((∃ v, r = some (.returned v)) →
        (EvmInv post ∧ R16Shards.OpHandlersB.HeadMemBridge.HeadMemChainWF post) ∧
          evmPot post < evmPot s) ∧
      (IsEvmErr r →
        (EvmInv post ∧ R16Shards.OpHandlersB.HeadMemBridge.HeadMemChainWF post) ∧
          (evmChain post).length = (evmChain s).length ∧
          Wave8GuestInv.evmR post ≤ Wave8GuestInv.evmR s))
    fname

theorem opHandlerChainSpecA_of_g10 {fname : Flapjack.Pancake.PanLang.MlS}
    (h : R16Shards.OpHandlersB.OpHandlerSpecA fname) :
    OpHandlerChainSpecA fname := by
  obtain ⟨params, body, retShape, hlk, hbody⟩ := h
  refine ⟨params, body, retShape, hlk, fun {F} s hc ⟨hinv, hwf, hnd⟩ hval hto => ?_⟩
  have hstep := hbody s hc ⟨hinv, (headMemChainWF_g10_iff_bridge s).mpr hwf, hnd⟩ hval hto
  refine ⟨fun hret => ?_, fun herr => ?_⟩
  · obtain ⟨⟨hinv', hwf'⟩, hpot⟩ := hstep.1 hret
    exact ⟨⟨hinv', (headMemChainWF_g10_iff_bridge _).mp hwf'⟩, hpot⟩
  · obtain ⟨⟨hinv', hwf'⟩, hlen, hr⟩ := hstep.2 herr
    exact ⟨⟨hinv', (headMemChainWF_g10_iff_bridge _).mp hwf'⟩, hlen, hr⟩

theorem opHandlerChainSpecA_of_g09 {fname : Flapjack.Pancake.PanLang.MlS}
    (h : R16Shards.OpHandlersB.Group09ChainWF.OpHandlerSpecA fname) :
    OpHandlerChainSpecA fname := by
  obtain ⟨params, body, retShape, hlk, hbody⟩ := h
  refine ⟨params, body, retShape, hlk, fun {F} s hc ⟨hinv, hwf, hnd⟩ hval hto => ?_⟩
  have hstep := hbody s hc ⟨hinv, (headMemChainWF_g09_iff_bridge s).mpr hwf, hnd⟩ hval hto
  refine ⟨fun hret => ?_, fun herr => ?_⟩
  · obtain ⟨⟨hinv', hwf'⟩, hpot⟩ := hstep.1 hret
    exact ⟨⟨hinv', (headMemChainWF_g09_iff_bridge _).mp hwf'⟩, hpot⟩
  · obtain ⟨⟨hinv', hwf'⟩, hlen, hr⟩ := hstep.2 herr
    exact ⟨⟨hinv', (headMemChainWF_g09_iff_bridge _).mp hwf'⟩, hlen, hr⟩

theorem op_return_chainSpecA : OpHandlerChainSpecA (ofString "op_return") :=
  opHandlerChainSpecA_of_g09 R16Shards.OpHandlersB.Group09ChainWF.op_return_specA

theorem op_revert_chainSpecA : OpHandlerChainSpecA (ofString "op_revert") :=
  opHandlerChainSpecA_of_g09 R16Shards.OpHandlersB.Group09ChainWF.op_revert_specA

theorem op_mcopy_chainSpecA : OpHandlerChainSpecA (ofString "op_mcopy") :=
  opHandlerChainSpecA_of_g09 R16Shards.OpHandlersB.Group09ChainWF.op_mcopy_specA

theorem op_selfdestruct_chainSpecA (hW : R16Shards.OpHandlersB.WorldAccountSpecsA) :
    OpHandlerChainSpecA (ofString "op_selfdestruct") :=
  opHandlerChainSpecA_of_g10 (R16Shards.OpHandlersB.op_selfdestruct_specA hW)

theorem op_create_chainSpecA (hW : R16Shards.OpHandlersB.WorldAccountSpecsA)
    (hcc : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "compute_contract_address"))
    (hgc : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "generic_create")) :
    OpHandlerChainSpecA (ofString "op_create") :=
  opHandlerChainSpecA_of_g10 (R16Shards.OpHandlersB.op_create_specA_g10 hW hcc hgc)

theorem op_create2_chainSpecA
    (hU : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "u256_to_be32"))
    (hW : R16Shards.OpHandlersB.WorldAccountSpecsA)
    (hcc2 : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "compute_create2_contract_address"))
    (hgc : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "generic_create")) :
    OpHandlerChainSpecA (ofString "op_create2") :=
  opHandlerChainSpecA_of_g10 (R16Shards.OpHandlersB.op_create2_specA_g10 hU hW hcc2 hgc)

theorem op_delegatecall_chainSpecA (hW : R16Shards.OpHandlersB.WorldAccountSpecsA)
    (hgc : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "generic_call")) :
    OpHandlerChainSpecA (ofString "op_delegatecall") :=
  opHandlerChainSpecA_of_g10 (R16Shards.OpHandlersB.op_delegatecall_specA_g10 hW hgc)

theorem ptxPhase12_backing_strong_of_cuts :
    type_of% @R13Shards.ptxPhase12_backing_strong_of_cuts :=
  R13Shards.ptxPhase12_backing_strong_of_cuts

theorem ptxPhase12_strong_of_phase2_cut :
    type_of% @R13Shards.ptxPhase12_strong_of_phase2_cut :=
  R13Shards.ptxPhase12_strong_of_phase2_cut

theorem gbody_process_transaction_backing_strong_pmc_of_cuts :
    type_of% @R13Shards.gbody_process_transaction_backing_strong_pmc_of_cuts :=
  R13Shards.gbody_process_transaction_backing_strong_pmc_of_cuts

theorem gbody_process_transaction_backing_strong_pmc_cutover_of_cuts
    (h : R16Shards.PtxCalleesCutover)
    (hwk : R16Shards.PtxP34.PmcStrong)
    (hkeep : R16Shards.PmcBackingStrong)
    (hp1 : R13Shards.PtxPhase1BackingCut)
    (hp2 : R13Shards.PtxPhase2BackingCut) :
    TerminatingFunBoundedOn
      R16Shards.TxReadyBackingStrong (ofString "process_transaction")
      K.«process_transaction» :=
  R16Shards.gbody_process_transaction_backing_strong_of_h12_pmc_cutover h hwk hkeep
    (R13Shards.ptxPhase12_backing_strong_of_cuts hp1 hp2)

theorem ek_depth0_prepare_of_ek :
    type_of% @R16Shards.EvmEkFk.ek_depth0_prepare_of_ek :=
  R16Shards.EvmEkFk.ek_depth0_prepare_of_ek

theorem wk_process_message_call_strong_of_callees :
    type_of% @R16Shards.TopGbodyWk.wk_process_message_call_strong_of_callees :=
  R16Shards.TopGbodyWk.wk_process_message_call_strong_of_callees

theorem wk_process_unchecked_system_transaction_of_sc :
    type_of% @R16Shards.TopGbodyWk.«wk_process_unchecked_system_transaction_of_sc» :=
  R16Shards.TopGbodyWk.«wk_process_unchecked_system_transaction_of_sc»

theorem ptxAfterPhase4_phase5_relRun_strong :
    type_of% @(R16Shards.TopGbodyWk.ptxAfterPhase4_phase5_relRun_strong_of_decode_witness
      decode_witness_to_mpt_spec_wkBal) :=
  R16Shards.TopGbodyWk.ptxAfterPhase4_phase5_relRun_strong_of_decode_witness
    decode_witness_to_mpt_spec_wkBal

theorem wk_process_transaction_strong_of_witnessDb :
    type_of% @(R16Shards.TopGbodyWk.wk_process_transaction_strong_of_decode_witness
      decode_witness_to_mpt_spec_wkBal) :=
  R16Shards.TopGbodyWk.wk_process_transaction_strong_of_decode_witness
    decode_witness_to_mpt_spec_wkBal

/-! ## Wave 8 R27 Cutover Wiring: A-Side Handlers, Cutover Routers & Phase 2 Strong Cuts -/

theorem remainingOpHandlersASpecAligned_closed :
    R16Shards.OpHandlers.RemainingOpHandlersASpecAligned :=
  R16Shards.OpHandlers.remainingOpHandlersASpecAligned_proved

theorem op_blockhash_spec : OpDispatchSpec.OpHandlerSpec (ofString "op_blockhash") :=
  R16Shards.OpHandlers.op_blockhash_spec

theorem op_coinbase_spec : OpDispatchSpec.OpHandlerSpec (ofString "op_coinbase") :=
  R16Shards.OpHandlers.op_coinbase_spec

theorem op_timestamp_spec : OpDispatchSpec.OpHandlerSpec (ofString "op_timestamp") :=
  R16Shards.OpHandlers.op_timestamp_spec

theorem op_number_spec : OpDispatchSpec.OpHandlerSpec (ofString "op_number") :=
  R16Shards.OpHandlers.op_number_spec

theorem op_prevrandao_spec : OpDispatchSpec.OpHandlerSpec (ofString "op_prevrandao") :=
  R16Shards.OpHandlers.op_prevrandao_spec

theorem op_gaslimit_spec : OpDispatchSpec.OpHandlerSpec (ofString "op_gaslimit") :=
  R16Shards.OpHandlers.op_gaslimit_spec

theorem op_chainid_spec : OpDispatchSpec.OpHandlerSpec (ofString "op_chainid") :=
  R16Shards.OpHandlers.op_chainid_spec

theorem op_basefee_spec : OpDispatchSpec.OpHandlerSpec (ofString "op_basefee") :=
  R16Shards.OpHandlers.op_basefee_spec

theorem op_blobhash_spec : OpDispatchSpec.OpHandlerSpec (ofString "op_blobhash") :=
  R16Shards.OpHandlers.op_blobhash_spec

theorem op_blobbasefee_spec : OpDispatchSpec.OpHandlerSpec (ofString "op_blobbasefee") :=
  R16Shards.OpHandlers.op_blobbasefee_spec

theorem op_slotnum_spec : OpDispatchSpec.OpHandlerSpec (ofString "op_slotnum") :=
  R16Shards.OpHandlers.op_slotnum_spec

theorem op_pop_spec : OpDispatchSpec.OpHandlerSpec (ofString "op_pop") :=
  R16Shards.OpHandlers.op_pop_spec

theorem op_msize_spec : OpDispatchSpec.OpHandlerSpec (ofString "op_msize") :=
  R16Shards.OpHandlers.op_msize_spec

theorem op_dup_spec : OpDispatchSpec.OpHandlerSpec (ofString "op_dup") :=
  R16Shards.OpHandlers.op_dup_spec

theorem op_swap_spec : OpDispatchSpec.OpHandlerSpec (ofString "op_swap") :=
  R16Shards.OpHandlers.op_swap_spec

theorem op_dupn_spec : OpDispatchSpec.OpHandlerSpec (ofString "op_dupn") :=
  R16Shards.OpHandlers.op_dupn_spec

theorem op_swapn_spec : OpDispatchSpec.OpHandlerSpec (ofString "op_swapn") :=
  R16Shards.OpHandlers.op_swapn_spec

theorem op_exchange_spec : OpDispatchSpec.OpHandlerSpec (ofString "op_exchange") :=
  R16Shards.OpHandlers.op_exchange_spec

theorem op_push_bounded_spec :
    type_of% @R16Shards.OpHandlers.op_push_bounded_spec :=
  R16Shards.OpHandlers.op_push_bounded_spec

theorem op_push_bounded_aligned_spec :
    R16Shards.OpHandlersB.OpPushBoundedAlignedSpec :=
  R16Shards.OpHandlersB.op_push_bounded_aligned_spec

/-- Aligned `op_dispatch` cutover router with `ext_code_of` head-word preservation discharged,
closing 80/87 aligned handlers modulo `WorldAccountSpecs` and the 7 remaining call/create/log specs. -/
theorem op_dispatch_aligned_spec_cutover_closed
    (hW : R16Shards.OpHandlersB.WorldAccountSpecs)
    (hrem : R16Shards.OpHandlersB.RemainingCallCreateLogAlignedSpecs) :
    R16Shards.OpHandlersB.RouterAligned.OpDispatchAlignedSpec :=
  R16Shards.OpHandlersB.op_dispatch_aligned_spec_cutover hW extCodeOfHeadSpec_closed hrem

/-- Definitional bridge between `StrongBridges.OpHandlerChainSpecA` and
`R16Shards.OpHandlersB.OpHandlerChainSpec`. -/
theorem opHandlerChainSpec_iff (fname : Flapjack.Pancake.PanLang.MlS) :
    OpHandlerChainSpecA fname ↔ R16Shards.OpHandlersB.OpHandlerChainSpec fname := Iff.rfl

/-- Remaining chain-WF handler obligations after discharging the 7 already-proved
chain-WF opcodes (`op_return`, `op_revert`, `op_mcopy`, `op_selfdestruct`,
`op_create`, `op_create2`, `op_delegatecall`). -/
structure RemainingChainHandlersCutover : Prop where
  op_stop : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_stop")
  op_add : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_add")
  op_mul : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_mul")
  op_sub : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_sub")
  op_div : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_div")
  op_sdiv : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_sdiv")
  op_mod : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_mod")
  op_smod : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_smod")
  op_addmod : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_addmod")
  op_mulmod : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_mulmod")
  op_exp : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_exp")
  op_signextend : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_signextend")
  op_lt : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_lt")
  op_gt : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_gt")
  op_slt : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_slt")
  op_sgt : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_sgt")
  op_eq : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_eq")
  op_iszero : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_iszero")
  op_and : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_and")
  op_or : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_or")
  op_xor : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_xor")
  op_not : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_not")
  op_byte : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_byte")
  op_shl : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_shl")
  op_shr : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_shr")
  op_sar : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_sar")
  op_clz : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_clz")
  op_keccak : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_keccak")
  op_address : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_address")
  op_balance : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_balance")
  op_origin : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_origin")
  op_caller : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_caller")
  op_callvalue : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_callvalue")
  op_calldataload : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_calldataload")
  op_calldatasize : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_calldatasize")
  op_calldatacopy : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_calldatacopy")
  op_codesize : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_codesize")
  op_codecopy : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_codecopy")
  op_gasprice : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_gasprice")
  op_extcodesize : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_extcodesize")
  op_extcodecopy : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_extcodecopy")
  op_returndatasize : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_returndatasize")
  op_returndatacopy : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_returndatacopy")
  op_extcodehash : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_extcodehash")
  op_blockhash : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_blockhash")
  op_coinbase : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_coinbase")
  op_timestamp : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_timestamp")
  op_number : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_number")
  op_prevrandao : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_prevrandao")
  op_gaslimit : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_gaslimit")
  op_chainid : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_chainid")
  op_selfbalance : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_selfbalance")
  op_basefee : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_basefee")
  op_blobhash : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_blobhash")
  op_blobbasefee : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_blobbasefee")
  op_slotnum : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_slotnum")
  op_pop : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_pop")
  op_mload : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_mload")
  op_mstore : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_mstore")
  op_mstore8 : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_mstore8")
  op_sload : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_sload")
  op_sstore : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_sstore")
  op_jump : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_jump")
  op_jumpi : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_jumpi")
  op_pc : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_pc")
  op_msize : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_msize")
  op_gas : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_gas")
  op_jumpdest : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_jumpdest")
  op_tload : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_tload")
  op_tstore : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_tstore")
  op_push : R16Shards.OpHandlersB.OpPushBoundedChainSpec
  op_dup : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_dup")
  op_swap : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_swap")
  op_log : R16Shards.OpHandlersB.OpLogBoundedChainSpec
  op_dupn : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_dupn")
  op_swapn : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_swapn")
  op_exchange : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_exchange")
  op_call : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_call")
  op_callcode : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_callcode")
  op_staticcall : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_staticcall")

/-- Assemble `OpDispatchChainHandlersCutover` from `RemainingChainHandlersCutover`,
plugging in the 7 proved chain-WF handlers (`op_return`, `op_revert`, `op_mcopy`,
`op_selfdestruct`, `op_create`, `op_create2`, `op_delegatecall`). -/
theorem opDispatchChainHandlersCutover_of_remaining
    (hW : R16Shards.OpHandlersB.WorldAccountSpecsA)
    (hU : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "u256_to_be32"))
    (hcc : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "compute_contract_address"))
    (hcc2 : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "compute_create2_contract_address"))
    (hgcr : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "generic_create"))
    (hgca : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "generic_call"))
    (hrem : RemainingChainHandlersCutover) :
    R16Shards.OpHandlersB.OpDispatchChainHandlersCutover where
  op_stop := hrem.op_stop
  op_add := hrem.op_add
  op_mul := hrem.op_mul
  op_sub := hrem.op_sub
  op_div := hrem.op_div
  op_sdiv := hrem.op_sdiv
  op_mod := hrem.op_mod
  op_smod := hrem.op_smod
  op_addmod := hrem.op_addmod
  op_mulmod := hrem.op_mulmod
  op_exp := hrem.op_exp
  op_signextend := hrem.op_signextend
  op_lt := hrem.op_lt
  op_gt := hrem.op_gt
  op_slt := hrem.op_slt
  op_sgt := hrem.op_sgt
  op_eq := hrem.op_eq
  op_iszero := hrem.op_iszero
  op_and := hrem.op_and
  op_or := hrem.op_or
  op_xor := hrem.op_xor
  op_not := hrem.op_not
  op_byte := hrem.op_byte
  op_shl := hrem.op_shl
  op_shr := hrem.op_shr
  op_sar := hrem.op_sar
  op_clz := hrem.op_clz
  op_keccak := hrem.op_keccak
  op_address := hrem.op_address
  op_balance := hrem.op_balance
  op_origin := hrem.op_origin
  op_caller := hrem.op_caller
  op_callvalue := hrem.op_callvalue
  op_calldataload := hrem.op_calldataload
  op_calldatasize := hrem.op_calldatasize
  op_calldatacopy := hrem.op_calldatacopy
  op_codesize := hrem.op_codesize
  op_codecopy := hrem.op_codecopy
  op_gasprice := hrem.op_gasprice
  op_extcodesize := hrem.op_extcodesize
  op_extcodecopy := hrem.op_extcodecopy
  op_returndatasize := hrem.op_returndatasize
  op_returndatacopy := hrem.op_returndatacopy
  op_extcodehash := hrem.op_extcodehash
  op_blockhash := hrem.op_blockhash
  op_coinbase := hrem.op_coinbase
  op_timestamp := hrem.op_timestamp
  op_number := hrem.op_number
  op_prevrandao := hrem.op_prevrandao
  op_gaslimit := hrem.op_gaslimit
  op_chainid := hrem.op_chainid
  op_selfbalance := hrem.op_selfbalance
  op_basefee := hrem.op_basefee
  op_blobhash := hrem.op_blobhash
  op_blobbasefee := hrem.op_blobbasefee
  op_slotnum := hrem.op_slotnum
  op_pop := hrem.op_pop
  op_mload := hrem.op_mload
  op_mstore := hrem.op_mstore
  op_mstore8 := hrem.op_mstore8
  op_sload := hrem.op_sload
  op_sstore := hrem.op_sstore
  op_jump := hrem.op_jump
  op_jumpi := hrem.op_jumpi
  op_pc := hrem.op_pc
  op_msize := hrem.op_msize
  op_gas := hrem.op_gas
  op_jumpdest := hrem.op_jumpdest
  op_tload := hrem.op_tload
  op_tstore := hrem.op_tstore
  op_mcopy := op_mcopy_chainSpecA
  op_push := hrem.op_push
  op_dup := hrem.op_dup
  op_swap := hrem.op_swap
  op_log := hrem.op_log
  op_dupn := hrem.op_dupn
  op_swapn := hrem.op_swapn
  op_exchange := hrem.op_exchange
  op_create := op_create_chainSpecA hW hcc hgcr
  op_call := hrem.op_call
  op_callcode := hrem.op_callcode
  op_return := op_return_chainSpecA
  op_delegatecall := op_delegatecall_chainSpecA hW hgca
  op_create2 := op_create2_chainSpecA hU hW hcc2 hgcr
  op_staticcall := hrem.op_staticcall
  op_revert := op_revert_chainSpecA
  op_selfdestruct := op_selfdestruct_chainSpecA hW

theorem op_dispatch_chain_spec_cutover :
    type_of% @R16Shards.OpHandlersB.op_dispatch_chain_spec_cutover :=
  R16Shards.OpHandlersB.op_dispatch_chain_spec_cutover

theorem op_dispatch_chain_spec_of_remaining
    (hW : R16Shards.OpHandlersB.WorldAccountSpecsA)
    (hU : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "u256_to_be32"))
    (hcc : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "compute_contract_address"))
    (hcc2 : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "compute_create2_contract_address"))
    (hgcr : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "generic_create"))
    (hgca : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "generic_call"))
    (hrem : RemainingChainHandlersCutover) :
    R16Shards.OpHandlersB.HeadMemBridge.OpDispatchSpecA :=
  R16Shards.OpHandlersB.op_dispatch_chain_spec_cutover
    (opDispatchChainHandlersCutover_of_remaining hW hU hcc hcc2 hgcr hgca hrem)

/-- End-to-end aligned `run_frames` bound directly from `OpDispatchChainHandlersCutover`
and the closed `finish_child` / `frame_epilogue` / `frame_exception` bridges. -/
theorem gbody_run_frames_aligned_of_chain_handlers
    (bf : TerminatingFunBoundedOn R16Shards.OpHandlersB.HeadMemBridge.FinishReadyA
      (ofString "finish_child") K.«finish_child»)
    (be : TerminatingFunBoundedOn GuestInv (ofString "frame_epilogue") K.«frame_epilogue»)
    (bx : TerminatingFunBoundedOn GuestInv (ofString "frame_exception") K.«frame_exception»)
    (bd : TerminatingFunBoundedOn R16Shards.OpHandlersB.HeadMemBridge.EvmRunA
      (ofString "op_dispatch") K.«op_dispatch»)
    (h : R16Shards.OpHandlersB.OpDispatchChainHandlersCutover) :
    TerminatingFunBoundedOn (fun s => EvmInv s ∧ R16Shards.OpHandlersB.HeadMemBridge.HeadMemChainWF s)
      (ofString "run_frames") K.«run_frames» :=
  gbody_run_frames_aligned_closed bf be bx bd (R16Shards.OpHandlersB.op_dispatch_chain_spec_cutover h)

/-! ### Phase 2 `htab_new` exit transports, backing compositions, and relational strong cut -/

theorem phase2_htab_new_txEnv :
    type_of% @R13Shards.phase2_htab_new_txEnv :=
  R13Shards.phase2_htab_new_txEnv

theorem phase2_htab_new_txBacking :
    type_of% @R13Shards.phase2_htab_new_txBacking :=
  R13Shards.phase2_htab_new_txBacking

theorem phase2_htab_new_live_buffer :
    type_of% @R13Shards.phase2_htab_new_live_buffer :=
  R13Shards.phase2_htab_new_live_buffer

theorem phase2_htab_new_world_disj :
    type_of% @R13Shards.phase2_htab_new_world_disj :=
  R13Shards.phase2_htab_new_world_disj

theorem phase2_p4Shapes_htab_new_aa :
    type_of% @R13Shards.phase2_p4Shapes_htab_new_aa :=
  R13Shards.phase2_p4Shapes_htab_new_aa

theorem phase2_backing_entry_adapter :
    type_of% @R13Shards.phase2_backing_entry_adapter :=
  R13Shards.phase2_backing_entry_adapter

theorem gbody_process_transaction_backing_strong_pmc_of_cuts_h4closed :
    type_of% @R13Shards.gbody_process_transaction_backing_strong_pmc_of_cuts_h4closed :=
  R13Shards.gbody_process_transaction_backing_strong_pmc_of_cuts_h4closed

theorem gbody_process_transaction_backing_strong_of_cuts_bundled :
    type_of% @R13Shards.gbody_process_transaction_backing_strong_of_cuts_bundled :=
  R13Shards.gbody_process_transaction_backing_strong_of_cuts_bundled

theorem gbody_process_transaction_backing_strong_pmc_cutover_of_cuts_bundled
    (h : R16Shards.PtxCalleesCutover)
    (hwk : R16Shards.PtxP34.PmcStrong)
    (hkeep : R16Shards.PmcBackingStrong)
    (hc : R13Shards.PtxPhase12BackingCuts) :
    TerminatingFunBoundedOn
      R16Shards.TxReadyBackingStrong (ofString "process_transaction")
      K.«process_transaction» :=
  R16Shards.gbody_process_transaction_backing_strong_of_h12_pmc_cutover h hwk hkeep
    (R13Shards.ptxPhase12_backing_strong hc)

theorem ptxPhase2_cut_strong :
    type_of% @R13Shards.ptxPhase2_cut_strong :=
  R13Shards.ptxPhase2_cut_strong

theorem ptxPhase2_relCut :
    type_of% @R13Shards.ptxPhase2_relCut :=
  R13Shards.ptxPhase2_relCut

theorem wk_process_transaction_strong_of_phase2 :
    type_of% @R13Shards.wk_process_transaction_strong_of_phase2 :=
  R13Shards.wk_process_transaction_strong_of_phase2

/-- `wk_process_transaction` under `TxReadyStrong` with Phase 2 closed from
`PtxPhase2RegionStrong` and Phase 5 closed from `decode_witness_to_mpt_spec_wkBal`
(eliminating the three raw Phase-5 block-output hypotheses of `wk_process_transaction_strong_of_phase2`). -/
theorem wk_process_transaction_strong_of_phase2_and_witnessDb
    (hdb : ∀ {F : Type} (s : Flapjack.PanSemStateFiniteExact 64 F),
      WorldOK s → globN s "ws" ≠ 0 →
        R16Shards.EvmEkFk.StorageCreateFinish.NodeDbSlicesBounded s (memW s (globN s "ws")))
    (hregion : R13Shards.PtxPhase2RegionStrong)
    {A3 : ∀ {F : Type},
      Flapjack.PanSemStateFiniteExact 64 F → Flapjack.PanSemStateFiniteExact 64 F → Prop}
    (hcuts : R13Shards.PtxPhase134StrongCuts A3) :
    WorldKeeps TxReadyStrong
      (fun s => [(globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128),
        (globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64),
        (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352),
        (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384),
        (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32),
        (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
        (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64),
        (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96),
        (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40),
        (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128),
        (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128),
        (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128),
        (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64),
        (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52),
        (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["bal_index", "bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr",
       "heap_ptr", "journal_n", "scratch_ptr", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]),
       ("ts", []), ("bo", [24, 32, 40, 56, 64, 72, 80])]
      (fun s r post S Nd =>
        RetTransactionLogs s r post S Nd ∧ R16Shards.TopGbodyWk.PtxRetSlices s r post S Nd)
      (ofString "process_transaction") :=
  wk_process_transaction_strong_of_witnessDb hdb
    R13Shards.PtxTxReadyBoundary R13Shards.PtxAfterPhase1 R13Shards.PtxAfterPhase2 A3
    (fun _ hs => hs) hcuts.phase1 (R13Shards.ptxPhase2_cut_strong hregion) hcuts.phase3 hcuts.phase4

end InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridges
