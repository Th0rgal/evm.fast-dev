import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.DecodeTransaction
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.EncodeTransaction
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBalStateInit.WkLstPush
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
import InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12.BuildMptIndexedWalk
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.StorageCreateFinish
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkHostPayloadHeaders
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.Depth0FrameOpen
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group09LogReturnRevert
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group10CallsCreates
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemAlignedBridge
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.FrameStartFinishChildStep1
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase2StrongTail2

/-! Closed strengthened contracts for the cutover rehearsal. Callers must establish
the stated entry guards before these bridges can replace weaker primitive fields. -/

set_option autoImplicit false

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridges

open Flapjack.Basis.Pure.MlString
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
    type_of% @R16Shards.MptC10C12.gbody_build_mpt_indexed :=
  R16Shards.MptC10C12.gbody_build_mpt_indexed

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
  R16Shards.OpHandlersB.HeadMemBridge.finish_child_finishPost_of_createFinish
    R16Shards.EvmEkFk.create_finish_specs

theorem finish_child_spec_closed :
    type_of% @Wave8GuestInv.finish_child_spec :=
  R16Shards.OpHandlersB.HeadMemBridge.finishChildSpecU_of_createFinish
    R16Shards.EvmEkFk.create_finish_specs

theorem finishChildMemSpec :
    R16Shards.OpHandlersB.HeadMemBridge.FinishChildMemSpec :=
  R16Shards.OpHandlersB.HeadMemBridge.finishChildMemSpec_of_createFinish
    R16Shards.EvmEkFk.create_finish_specs

theorem finishChildSpecA :
    R16Shards.OpHandlersB.HeadMemBridge.FinishChildSpecA :=
  R16Shards.OpHandlersB.HeadMemBridge.finishChildSpecA_of_createFinish
    R16Shards.EvmEkFk.create_finish_specs

theorem gbody_run_frames_aligned_closed :
    type_of% @(R16Shards.OpHandlersB.HeadMemBridge.gbody_run_frames_aligned_of_createFinish
      (hCF := R16Shards.EvmEkFk.create_finish_specs)) :=
  fun bf be bx bd hd =>
    R16Shards.OpHandlersB.HeadMemBridge.gbody_run_frames_aligned_of_createFinish
      bf be bx bd R16Shards.EvmEkFk.create_finish_specs hd

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

theorem bmiWkWW_mpt_set :
    type_of% @R16Shards.MptC10C12.bmiWkWW_mpt_set :=
  R16Shards.MptC10C12.bmiWkWW_mpt_set

theorem bmiWkLoop_hRl :
    type_of% @R16Shards.MptC10C12.bmiWkLoop_hRl :=
  R16Shards.MptC10C12.bmiWkLoop_hRl

end InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridges
