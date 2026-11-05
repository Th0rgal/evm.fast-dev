import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.DecodeTransaction
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.EncodeTransaction
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBalStateInit.WkLstPush
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.GbodyRunAttempt
import InitECandidate.Solver.Wave8GuestInv.R16Shards.HeaderHashRecover.HeaderHash
import InitECandidate.Solver.Wave8GuestInv.R16Shards.HeaderHashRecover.RecoverSender
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group08

/-! Closed strengthened contracts for the cutover rehearsal. Callers must establish
the stated entry guards before these bridges can replace weaker primitive fields. -/

set_option autoImplicit false

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridges

open Flapjack.Basis.Pure.MlString
open R11Shards

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

end InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridges
