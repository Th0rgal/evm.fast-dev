import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.DecodeTransaction
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.EncodeTransaction
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBalStateInit.WkLstPush
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.GbodyRunAttempt
import InitECandidate.Solver.Wave8GuestInv.R16Shards.HeaderHashRecover.HeaderHash
import InitECandidate.Solver.Wave8GuestInv.R16Shards.HeaderHashRecover.RecoverSender

/-! Closed strengthened contracts for the cutover rehearsal. Callers must establish
the stated entry guards before these bridges can replace weaker primitive fields. -/

set_option autoImplicit false

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridges

open Flapjack.Basis.Pure.MlString

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
