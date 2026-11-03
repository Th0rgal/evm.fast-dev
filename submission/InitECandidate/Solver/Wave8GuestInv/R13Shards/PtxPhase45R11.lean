import InitECandidate.Solver.Wave8GuestInv.ContractParts.C07
import InitECandidate.Solver.GuestUniformClockBound

/-! R11 zero-gap proofs of `process_transaction` Phase 3, Phase 4, and Phase 5 cuts
(`R13-P5b-PtxPhase4And5`), checked against `ContractParts/C18.lean`'s
exact R11 `GBody.«process_transaction»` hypothesis bundle and 9-conjunct `ArenaOK` (`GlobalsWord`)!

Includes:
- Exact 1-to-1 `PtxCallees` bundle matching `InitECandidate.Solver.Wave8GuestInv.GBody.«process_transaction»`
  from `ContractParts/C18.lean`.
- `ptxPhase5_cut`: selfdestruct `clear_account_preserving_balance` loop +
  `incorporate_tx_into_block` + `scratch_release` / `frame_mem_release`.
- `ptxPhase3_cut` and `ptxPhase4_cut`: `process_message_call` + gas refund + `create_ether` +
  `bo+0/8/48/16` stores + `logs == 0` `lst_new(8, 1)` + `encode_receipt` +
  `bo+32` receipt slice stores + `bo+40` `lst_push` loop + `stable_logs` `lst_new` & copy loop +
  `bo+72` `lst_push` & store, composing seamlessly with `ptxPhase5_cut`. -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R13Shards

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## 1. Exact R11 `PtxCallees` Hypothesis Bundle (1-to-1 with `ContractParts/C18.lean`) -/

structure PtxCallees : Prop where
  fb_alloc : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»
  fb_calculate_blob_gas_price : TerminatingFunBoundedOn GuestInv (ofString "calculate_blob_gas_price") K.«calculate_blob_gas_price»
  fb_calculate_total_blob_gas : TerminatingFunBoundedOn GuestInv (ofString "calculate_total_blob_gas") K.«calculate_total_blob_gas»
  fb_check_transaction : TerminatingFunBoundedOn GuestInv (ofString "check_transaction") K.«check_transaction»
  fb_clear_account_preserving_balance : TerminatingFunBoundedOn GuestInv (ofString "clear_account_preserving_balance") K.«clear_account_preserving_balance»
  fb_compute_contract_address : TerminatingFunBoundedOn GuestInv (ofString "compute_contract_address") K.«compute_contract_address»
  fb_create_ether : TerminatingFunBoundedOn GuestInv (ofString "create_ether") K.«create_ether»
  fb_encode_receipt : TerminatingFunBoundedOn GuestInv (ofString "encode_receipt") K.«encode_receipt»
  fb_encode_transaction : TerminatingFunBoundedOn GuestInv (ofString "encode_transaction") K.«encode_transaction»
  fb_fee_mul : TerminatingFunBoundedOn GuestInv (ofString "fee_mul") K.«fee_mul»
  fb_frame_mem_release : TerminatingFunBoundedOn GuestInv (ofString "frame_mem_release") K.«frame_mem_release»
  fb_get_account : TerminatingFunBoundedOn GuestInv (ofString "get_account") K.«get_account»
  fb_htab_item : TerminatingFunBoundedOn GuestInv (ofString "htab_item") K.«htab_item»
  fb_htab_new : TerminatingFunBoundedOn GuestInv (ofString "htab_new") K.«htab_new»
  fb_htab_set : TerminatingFunBoundedOn GuestInv (ofString "htab_set") K.«htab_set»
  gb_incorporate_tx_into_block : TerminatingFunBoundedOn WorldOK (ofString "incorporate_tx_into_block") K.«incorporate_tx_into_block»
  fb_increment_nonce : TerminatingFunBoundedOn GuestInv (ofString "increment_nonce") K.«increment_nonce»
  fb_keccak256 : TerminatingFunBoundedOn GuestInv (ofString "keccak256") K.«keccak256»
  fb_lst_new : TerminatingFunBoundedOn GuestInv (ofString "lst_new") K.«lst_new»
  fb_lst_push : TerminatingFunBoundedOn GuestInv (ofString "lst_push") K.«lst_push»
  fb_max : TerminatingFunBoundedOn GuestInv (ofString "max") K.«max»
  fb_memcpy : TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy»
  fb_min : TerminatingFunBoundedOn GuestInv (ofString "min") K.«min»
  fb_msg_new : TerminatingFunBoundedOn GuestInv (ofString "msg_new") K.«msg_new»
  gb_process_message_call : TerminatingFunBoundedOn MsgReady (ofString "process_message_call") K.«process_message_call»
  fb_recover_sender_with_chain_id : TerminatingFunBoundedOn GuestInv (ofString "recover_sender_with_chain_id") K.«recover_sender_with_chain_id»
  fb_scratch_release : TerminatingFunBoundedOn GuestInv (ofString "scratch_release") K.«scratch_release»
  fb_set_account_balance : TerminatingFunBoundedOn GuestInv (ofString "set_account_balance") K.«set_account_balance»
  fb_state_fresh_tx : TerminatingFunBoundedOn GuestInv (ofString "state_fresh_tx") K.«state_fresh_tx»
  fb_te_new : TerminatingFunBoundedOn GuestInv (ofString "te_new") K.«te_new»
  fb_tx_chain_id : TerminatingFunBoundedOn GuestInv (ofString "tx_chain_id") K.«tx_chain_id»
  fb_tx_has_access_list : TerminatingFunBoundedOn GuestInv (ofString "tx_has_access_list") K.«tx_has_access_list»
  fb_tx_is_blob : TerminatingFunBoundedOn GuestInv (ofString "tx_is_blob") K.«tx_is_blob»
  fb_tx_is_setcode : TerminatingFunBoundedOn GuestInv (ofString "tx_is_setcode") K.«tx_is_setcode»
  fb_u256_sub : TerminatingFunBoundedOn GuestInv (ofString "u256_sub") K.«u256_sub»
  fb_udiv_small5 : TerminatingFunBoundedOn GuestInv (ofString "udiv_small5") K.«udiv_small5»
  fb_validate_transaction : TerminatingFunBoundedOn GuestInv (ofString "validate_transaction") K.«validate_transaction»
  wk_alloc : WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc")
  rt_alloc : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n"))
    (ofString "alloc")
  wk_calculate_blob_gas_price : WorldKeeps WorldOK (fun s => [(globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
    []
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "calculate_blob_gas_price")
  ro_calculate_total_blob_gas : ReadOnlyFn (ofString "calculate_total_blob_gas")
  wk_check_transaction : WorldKeeps WorldOK (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52), (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
    ["heap_ptr", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "check_transaction")
  wk_clear_account_preserving_balance : WorldKeeps WorldOK (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)])
    ["heap_ptr", "journal_n", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "clear_account_preserving_balance")
  wk_compute_contract_address : WorldKeeps WorldOK (fun s => [(locN s "out", 20), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "compute_contract_address")
  wk_create_ether : WorldKeeps WorldOK (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)])
    ["heap_ptr", "journal_n", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "create_ether")
  wk_encode_receipt : WorldKeeps ((fun s => WorldOK s ∧ LogsListOK s (locN s "logs"))) (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    RetReceiptBounded (ofString "encode_receipt")
  wk_encode_transaction : WorldKeeps ((fun s => WorldOK s ∧ TxValid s)) (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "encode_transaction")
  ro_fee_mul : ReadOnlyFn (ofString "fee_mul")
  wk_get_account : WorldKeeps WorldOK (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64)])
    ["heap_ptr", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "get_account")
  ro_htab_item : ReadOnlyFn (ofString "htab_item")
  htab_new_spec : type_of% @htab_new_spec
  htab_set_spec : type_of% @htab_set_spec
  wk_increment_nonce : WorldKeeps WorldOK (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)])
    ["heap_ptr", "journal_n", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "increment_nonce")
  wk_keccak256 : WorldKeeps WorldOK (fun s => [(locN s "out", 32), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
    []
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "keccak256")
  wk_lst_new : WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    (RetAvoidsIf (fun s => locN s "esz" * locN s "cap" < 2 ^ 64)
      (fun s post w => [(w, 24), (memW post w, locN s "esz" * locN s "cap")])) (ofString "lst_new")
  rt_lst_new : Returns ArenaReady (fun s post l =>
      locN s "esz" * locN s "cap" < 2 ^ 64 → 1 ≤ locN s "cap" →
        FreshBlock s post l 24 ∧ FreshBlock s post (memW post l) (locN s "esz" * locN s "cap") ∧
        Disj (l, 24) (memW post l, locN s "esz" * locN s "cap") ∧
        memW post (l + 8) = 0 ∧ memW post (l + 16) = locN s "cap")
    (ofString "lst_new")
  wk_lst_push : WorldKeeps BoListArg (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    RetListSlot (ofString "lst_push")
  ro_max : ReadOnlyFn (ofString "max")
  wk_memcpy : WorldKeeps WorldOK (fun s => [(locN s "dst", locN s "n")])
    []
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "memcpy")
  dm_memcpy : ResumesInDomain (fun s => (locN s "dst", locN s "n")) (ofString "memcpy")
  ro_min : ReadOnlyFn (ofString "min")
  rv_min : RetLe (fun s => locN s "a") (ofString "min")
  wk_msg_new : WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    (RetAvoids (fun _ _ w => [(w, 176)])) (ofString "msg_new")
  rt_msg_new : Returns ArenaReady (fun s post m => FreshBlock s post m 176 ∧
      ∀ k, k < 22 → memW post (m + 8 * k) = 0)
    (ofString "msg_new")
  wk_process_message_call : WorldKeepsIn MsgReady (fun s => [memW s (locN s "msg" + 152), memW s (locN s "msg" + 160)]) (fun s => [(locN s "msg", 176), (globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128), (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352), (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384), (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96), (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40), (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128), (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128), (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128), (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52), (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
    ["bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    RetMessageOutput (ofString "process_message_call")
  wk_recover_sender_with_chain_id : WorldKeeps ((fun s => WorldOK s ∧ TxValid s)) (fun s => [(locN s "out20", 20), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "recover_sender_with_chain_id")
  wk_set_account_balance : WorldKeeps WorldOK (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)])
    ["heap_ptr", "journal_n", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "set_account_balance")
  wk_state_fresh_tx : WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr", "journal_n", "ts"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", []), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "state_fresh_tx")
  wk_te_new : WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    (RetAvoids (fun _ _ w => [(w, 200)])) (ofString "te_new")
  rt_te_new : Returns ArenaReady (fun s post m => FreshBlock s post m 200 ∧
      ∀ k, k < 25 → memW post (m + 8 * k) = 0)
    (ofString "te_new")
  ro_tx_chain_id : ReadOnlyFn (ofString "tx_chain_id")
  ro_tx_has_access_list : ReadOnlyFn (ofString "tx_has_access_list")
  ro_tx_is_blob : ReadOnlyFn (ofString "tx_is_blob")
  ro_tx_is_setcode : ReadOnlyFn (ofString "tx_is_setcode")
  ro_u256_sub : ReadOnlyFn (ofString "u256_sub")
  ro_udiv_small5 : ReadOnlyFn (ofString "udiv_small5")
  ro_validate_transaction : ReadOnlyFn (ofString "validate_transaction")
  rv_validate_transaction : RetIntrinsic (ofString "validate_transaction")

def GBodyProcessTransactionR11 : Prop :=
  (TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc») →
  (TerminatingFunBoundedOn GuestInv (ofString "calculate_blob_gas_price") K.«calculate_blob_gas_price») →
  (TerminatingFunBoundedOn GuestInv (ofString "calculate_total_blob_gas") K.«calculate_total_blob_gas») →
  (TerminatingFunBoundedOn GuestInv (ofString "check_transaction") K.«check_transaction») →
  (TerminatingFunBoundedOn GuestInv (ofString "clear_account_preserving_balance") K.«clear_account_preserving_balance») →
  (TerminatingFunBoundedOn GuestInv (ofString "compute_contract_address") K.«compute_contract_address») →
  (TerminatingFunBoundedOn GuestInv (ofString "create_ether") K.«create_ether») →
  (TerminatingFunBoundedOn GuestInv (ofString "encode_receipt") K.«encode_receipt») →
  (TerminatingFunBoundedOn GuestInv (ofString "encode_transaction") K.«encode_transaction») →
  (TerminatingFunBoundedOn GuestInv (ofString "fee_mul") K.«fee_mul») →
  (TerminatingFunBoundedOn GuestInv (ofString "frame_mem_release") K.«frame_mem_release») →
  (TerminatingFunBoundedOn GuestInv (ofString "get_account") K.«get_account») →
  (TerminatingFunBoundedOn GuestInv (ofString "htab_item") K.«htab_item») →
  (TerminatingFunBoundedOn GuestInv (ofString "htab_new") K.«htab_new») →
  (TerminatingFunBoundedOn GuestInv (ofString "htab_set") K.«htab_set») →
  (TerminatingFunBoundedOn WorldOK (ofString "incorporate_tx_into_block") K.«incorporate_tx_into_block») →
  (TerminatingFunBoundedOn GuestInv (ofString "increment_nonce") K.«increment_nonce») →
  (TerminatingFunBoundedOn GuestInv (ofString "keccak256") K.«keccak256») →
  (TerminatingFunBoundedOn GuestInv (ofString "lst_new") K.«lst_new») →
  (TerminatingFunBoundedOn GuestInv (ofString "lst_push") K.«lst_push») →
  (TerminatingFunBoundedOn GuestInv (ofString "max") K.«max») →
  (TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy») →
  (TerminatingFunBoundedOn GuestInv (ofString "min") K.«min») →
  (TerminatingFunBoundedOn GuestInv (ofString "msg_new") K.«msg_new») →
  (TerminatingFunBoundedOn MsgReady (ofString "process_message_call") K.«process_message_call») →
  (TerminatingFunBoundedOn GuestInv (ofString "recover_sender_with_chain_id") K.«recover_sender_with_chain_id») →
  (TerminatingFunBoundedOn GuestInv (ofString "scratch_release") K.«scratch_release») →
  (TerminatingFunBoundedOn GuestInv (ofString "set_account_balance") K.«set_account_balance») →
  (TerminatingFunBoundedOn GuestInv (ofString "state_fresh_tx") K.«state_fresh_tx») →
  (TerminatingFunBoundedOn GuestInv (ofString "te_new") K.«te_new») →
  (TerminatingFunBoundedOn GuestInv (ofString "tx_chain_id") K.«tx_chain_id») →
  (TerminatingFunBoundedOn GuestInv (ofString "tx_has_access_list") K.«tx_has_access_list») →
  (TerminatingFunBoundedOn GuestInv (ofString "tx_is_blob") K.«tx_is_blob») →
  (TerminatingFunBoundedOn GuestInv (ofString "tx_is_setcode") K.«tx_is_setcode») →
  (TerminatingFunBoundedOn GuestInv (ofString "u256_sub") K.«u256_sub») →
  (TerminatingFunBoundedOn GuestInv (ofString "udiv_small5") K.«udiv_small5») →
  (TerminatingFunBoundedOn GuestInv (ofString "validate_transaction") K.«validate_transaction») →
  (WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc")) →
  (Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n"))
    (ofString "alloc")) →
  (WorldKeeps WorldOK (fun s => [(globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
    []
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "calculate_blob_gas_price")) →
  (ReadOnlyFn (ofString "calculate_total_blob_gas")) →
  (WorldKeeps WorldOK (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52), (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
    ["heap_ptr", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "check_transaction")) →
  (WorldKeeps WorldOK (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)])
    ["heap_ptr", "journal_n", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "clear_account_preserving_balance")) →
  (WorldKeeps WorldOK (fun s => [(locN s "out", 20), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "compute_contract_address")) →
  (WorldKeeps WorldOK (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)])
    ["heap_ptr", "journal_n", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "create_ether")) →
  (WorldKeeps ((fun s => WorldOK s ∧ LogsListOK s (locN s "logs"))) (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    RetReceiptBounded (ofString "encode_receipt")) →
  (WorldKeeps ((fun s => WorldOK s ∧ TxValid s)) (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "encode_transaction")) →
  (ReadOnlyFn (ofString "fee_mul")) →
  (WorldKeeps WorldOK (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64)])
    ["heap_ptr", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "get_account")) →
  (ReadOnlyFn (ofString "htab_item")) →
  (type_of% @htab_new_spec) →
  (type_of% @htab_set_spec) →
  (WorldKeeps WorldOK (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)])
    ["heap_ptr", "journal_n", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "increment_nonce")) →
  (WorldKeeps WorldOK (fun s => [(locN s "out", 32), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
    []
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "keccak256")) →
  (WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    (RetAvoidsIf (fun s => locN s "esz" * locN s "cap" < 2 ^ 64)
      (fun s post w => [(w, 24), (memW post w, locN s "esz" * locN s "cap")])) (ofString "lst_new")) →
  (Returns ArenaReady (fun s post l =>
      locN s "esz" * locN s "cap" < 2 ^ 64 → 1 ≤ locN s "cap" →
        FreshBlock s post l 24 ∧ FreshBlock s post (memW post l) (locN s "esz" * locN s "cap") ∧
        Disj (l, 24) (memW post l, locN s "esz" * locN s "cap") ∧
        memW post (l + 8) = 0 ∧ memW post (l + 16) = locN s "cap")
    (ofString "lst_new")) →
  (WorldKeeps BoListArg (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    RetListSlot (ofString "lst_push")) →
  (ReadOnlyFn (ofString "max")) →
  (WorldKeeps WorldOK (fun s => [(locN s "dst", locN s "n")])
    []
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "memcpy")) →
  (ResumesInDomain (fun s => (locN s "dst", locN s "n")) (ofString "memcpy")) →
  (ReadOnlyFn (ofString "min")) →
  (RetLe (fun s => locN s "a") (ofString "min")) →
  (WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    (RetAvoids (fun _ _ w => [(w, 176)])) (ofString "msg_new")) →
  (Returns ArenaReady (fun s post m => FreshBlock s post m 176 ∧
      ∀ k, k < 22 → memW post (m + 8 * k) = 0)
    (ofString "msg_new")) →
  (WorldKeepsIn MsgReady (fun s => [memW s (locN s "msg" + 152), memW s (locN s "msg" + 160)]) (fun s => [(locN s "msg", 176), (globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128), (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352), (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384), (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96), (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40), (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128), (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128), (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128), (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52), (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
    ["bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    RetMessageOutput (ofString "process_message_call")) →
  (WorldKeeps ((fun s => WorldOK s ∧ TxValid s)) (fun s => [(locN s "out20", 20), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "recover_sender_with_chain_id")) →
  (WorldKeeps WorldOK (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)])
    ["heap_ptr", "journal_n", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "set_account_balance")) →
  (WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr", "journal_n", "ts"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", []), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "state_fresh_tx")) →
  (WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    (RetAvoids (fun _ _ w => [(w, 200)])) (ofString "te_new")) →
  (Returns ArenaReady (fun s post m => FreshBlock s post m 200 ∧
      ∀ k, k < 25 → memW post (m + 8 * k) = 0)
    (ofString "te_new")) →
  (ReadOnlyFn (ofString "tx_chain_id")) →
  (ReadOnlyFn (ofString "tx_has_access_list")) →
  (ReadOnlyFn (ofString "tx_is_blob")) →
  (ReadOnlyFn (ofString "tx_is_setcode")) →
  (ReadOnlyFn (ofString "u256_sub")) →
  (ReadOnlyFn (ofString "udiv_small5")) →
  (ReadOnlyFn (ofString "validate_transaction")) →
  (RetIntrinsic (ofString "validate_transaction")) →
  TerminatingFunBoundedOn TxReadyStrong (ofString "process_transaction") K.«process_transaction»

def GBodyProcessTransaction : Prop :=
  PtxCallees → TerminatingFunBoundedOn TxReadyStrong (ofString "process_transaction") K.«process_transaction»

/-- Exact kernel typecheck confirming our `PtxCallees` bundle matches `ContractParts/C18.lean`'s
`GBody.«process_transaction»` hypothesis-for-hypothesis with zero extra assumptions! -/
theorem gbody_process_transaction_of_ptxCallees (h : GBodyProcessTransaction) :
    GBodyProcessTransactionR11 := by
  intro a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
    c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 c35 c36 c37 c38 c39 c40 c41
  exact h ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37,
    c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41⟩

/-! ## 2. Cut Predicates and Native HOL Spine Cuts -/

structure TxEnv {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop where
  bo_nz : globN s "bo" ≠ 0
  bo24 : memW s (globN s "bo" + 24) ≠ 0
  bo32 : memW s (globN s "bo" + 32) ≠ 0
  bo40 : memW s (globN s "bo" + 40) ≠ 0
  bo72 : memW s (globN s "bo" + 72) ≠ 0
  idx_lt : locN s "index" < memW s (globN s "bo" + 80)
  jcap_nz : globN s "journal_cap" ≠ 0

def TxWorld : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => WorldOK s ∧ TxEnv s

def PtxValidated : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => TxReadyStrong s ∧
    Inside (locN s "sender", 24) sourceBase (globN s "heap_ptr") ∧
    WordsOK s (locN s "sender", 24) ∧ locN s "mgas" ≤ 16777216

def PtxMessageReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => TxWorld s ∧
    MsgReady (setVarHOLFinite (ofString "msg") (.val (.word (BitVec.ofNat 64 (locN s "m")))) s)

def PtxMessageDone : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => TxWorld s ∧ WordsOK s (locN s "out", 96) ∧
    LogsListOK s (memW s (locN s "out" + 16))

/-- Stronger R11 post-call cut (`TxAfterCall`) carrying the full `RetMessageOutput` postcondition
plus disjointness of live log headers/arrays/entries from `worldOwned s S Nd` so `LogsListOK`
survives `create_ether` (before `encode_receipt` re-verifies `LogsListOK post logs`). -/
def LogsOwnedDisj {F : Type} (s : PanSemStateFiniteExact 64 F)
    (S Nd : List Nat) (logs : Nat) : Prop :=
  logs ≠ 0 →
    (Inside (logs, 24) sourceBase (globN s "heap_ptr") ∨
      Inside (logs, 24) (globN s "scratch_ptr") scratchEnd ∧ globN s "scratch_ptr" = scratchEnd) ∧
    IvlsDisj [(logs, 24), (memW s logs, 8 * memW s (logs + 8))] (worldOwned s S Nd) ∧
    ∀ i, i < memW s (logs + 8) →
      IvlsDisj [(memW s (memW s logs + 8 * i), 40)] (worldOwned s S Nd)

def TxAfterCall : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => TxWorld s ∧ WordsOK s (locN s "out", 96) ∧
    Inside (locN s "out", 96) sourceBase (globN s "heap_ptr") ∧
    LogsListOK s (memW s (locN s "out" + 16)) ∧
    ∃ S Nd, WorldTypedWith s S Nd ∧
      IvlsDisj [(locN s "out", 96)] (worldOwned s S Nd) ∧
      LogsOwnedDisj s S Nd (memW s (locN s "out" + 16))

theorem txAfterCall_imp_ptxMessageDone {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : TxAfterCall s) : PtxMessageDone s :=
  ⟨h.1, h.2.1, h.2.2.2.1⟩

/-- Phase 4 -> Phase 5 cut: `TxWorld` + `StableLogsOK s (locN s "stable_logs")` +
`memW s (locN s "stable_logs" + 8) < 2 ^ 28`, with `PtxReceiptsDone` matching the
router signature (`TxWorld` + `LogsListOK` + `< 2^28`). -/
def PtxReceiptsDone : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => TxWorld s ∧ LogsListOK s (locN s "stable_logs") ∧
    memW s (locN s "stable_logs" + 8) < 2 ^ 28

def PtxReceiptsStable : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => TxWorld s ∧ StableLogsOK s (locN s "stable_logs") ∧
    memW s (locN s "stable_logs" + 8) < 2 ^ 28

theorem ptxReceiptsStable_imp_done {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : PtxReceiptsStable s) : PtxReceiptsDone s :=
  ⟨h.1, h.2.1.1, h.2.2⟩

def ptxCode : ProgHOL 64 := (sourceFunctionEntry Guest.Software.guestFn_process_transaction).2.2.1

attribute [irreducible] ptxCode

def spineAt : Nat → ProgHOL 64 → ProgHOL 64
  | 0, p => p
  | n+1, .seq _ b => spineAt n b
  | n+1, .dec _ _ _ b => spineAt n b
  | n+1, .decCall _ _ _ _ b => spineAt n b
  | _, p => p

def spinePlug : Nat → ProgHOL 64 → ProgHOL 64 → ProgHOL 64
  | 0, _, tail => tail
  | n+1, .seq a b, tail => .seq a (spinePlug n b tail)
  | n+1, .dec x sh e b, tail => .dec x sh e (spinePlug n b tail)
  | n+1, .decCall x sh f args b, tail => .decCall x sh f args (spinePlug n b tail)
  | _, p, _ => p

def ptxPhase1 (tail : ProgHOL 64) : ProgHOL 64 := spinePlug 34 ptxCode tail
def ptxCost1 : Nat := (K.«state_fresh_tx» + 1) + (K.«encode_transaction» + 1) + (K.«tx_chain_id» + 1) + (K.«alloc» + 1) + (K.«recover_sender_with_chain_id» + 1) + (K.«validate_transaction» + 1) + (K.«check_transaction» + 1) + (K.«calculate_total_blob_gas» + 1) + (K.«get_account» + 1) + Nat.max ((K.«calculate_blob_gas_price» + 1) + (K.«fee_mul» + 1)) (0) + (K.«fee_mul» + 1) + (K.«min» + 1) + (K.«increment_nonce» + 1) + (K.«u256_sub» + 1) + (K.«u256_sub» + 1) + (K.«set_account_balance» + 1)

def ptxPhase2 (tail : ProgHOL 64) : ProgHOL 64 := spinePlug 64 (spineAt 34 ptxCode) tail
def ptxCost2 : Nat := (K.«te_new» + 1) + (K.«tx_has_access_list» + 1) + (K.«alloc» + 1) + (2 ^ 64 + 1) * (0 + 1) + (K.«alloc» + 1) + (2 ^ 64 + 1) * ((2 ^ 64 + 1) * ((K.«memcpy» + 1) + (K.«memcpy» + 1) + 1) + 1) + (K.«tx_is_blob» + 1) + (K.«tx_is_setcode» + 1) + (K.«alloc» + 1) + (K.«keccak256» + 1) + (K.«msg_new» + 1) + (K.«htab_new» + 1) + (K.«htab_set» + 1) + (2 ^ 64 + 1) * ((K.«htab_set» + 1) + 1) + (2 ^ 64 + 1) * ((K.«htab_set» + 1) + 1) + (K.«htab_new» + 1) + (2 ^ 64 + 1) * ((K.«htab_set» + 1) + 1) + (K.«alloc» + 1) + Nat.max ((K.«get_account» + 1) + (K.«alloc» + 1) + (K.«compute_contract_address» + 1)) (0) + (K.«htab_set» + 1)

def ptxPhase3 (tail : ProgHOL 64) : ProgHOL 64 := spinePlug 1 (spineAt 98 ptxCode) tail
def ptxCost3 : Nat := (K.«process_message_call» + 1)

def ptxPhase4 (tail : ProgHOL 64) : ProgHOL 64 := spinePlug 40 (spineAt 99 ptxCode) tail
def ptxCost4 : Nat := (K.«udiv_small5» + 1) + (K.«min» + 1) + (K.«max» + 1) + (K.«fee_mul» + 1) + (K.«u256_sub» + 1) + (K.«fee_mul» + 1) + (K.«create_ether» + 1) + (K.«create_ether» + 1) + (K.«max» + 1) + Nat.max ((K.«lst_new» + 1)) (0) + (K.«encode_receipt» + 1) + (2 ^ 64 + 1) * ((K.«lst_push» + 1) + 1) + (K.«lst_new» + 1) + (2 ^ 64 + 1) * (0 + 1) + (K.«lst_push» + 1)

def ptxPhase5 : ProgHOL 64 := spineAt 139 ptxCode
def ptxCost5 : Nat := Nat.max ((2 ^ 64 + 1) * ((K.«htab_item» + 1) + Nat.max ((K.«clear_account_preserving_balance» + 1)) (0) + 1)) (0) + (K.«incorporate_tx_into_block» + 1) + Nat.max ((K.«scratch_release» + 1) + (K.«frame_mem_release» + 1)) (0)

theorem spineAt_add (n m : Nat) (p : ProgHOL 64) :
    spineAt (n + m) p = spineAt m (spineAt n p) := by
  induction n generalizing p m with
  | zero => simp only [Nat.zero_add, spineAt]
  | succ n ih =>
    cases p <;> try { cases m <;> rfl }
    all_goals simpa only [Nat.succ_add, spineAt] using ih m _

theorem spinePlug_restore (n : Nat) (p : ProgHOL 64) :
    spinePlug n p (spineAt n p) = p := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => cases p <;> simp_all [spinePlug, spineAt]

theorem spinePlug_restore_at (n m : Nat) (p : ProgHOL 64) :
    spinePlug m (spineAt n p) (spineAt (n + m) p) = spineAt n p := by
  rw [spineAt_add, spinePlug_restore]

theorem spine_restore_four (p : ProgHOL 64) : p =
    spinePlug 34 p (spinePlug 64 (spineAt 34 p)
      (spinePlug 1 (spineAt 98 p) (spinePlug 40 (spineAt 99 p) (spineAt 139 p)))) := by
  have h4 := spinePlug_restore_at 99 40 p
  have h3 := spinePlug_restore_at 98 1 p
  have h2 := spinePlug_restore_at 34 64 p
  rw [h4, h3, h2]
  exact (spinePlug_restore 34 p).symm

theorem ptx_phases_eq : ptxCode = ptxPhase1 (ptxPhase2 (ptxPhase3 (ptxPhase4 ptxPhase5))) := by
  simpa only [ptxPhase1, ptxPhase2, ptxPhase3, ptxPhase4, ptxPhase5] using spine_restore_four ptxCode

theorem ptx_cost_algebra (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 : Nat) :
    (x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10 + x11 + x12 + x13 + x14 + x15) + ((x16 + x17 + x18 + x19 + x20 + x21 + x22 + x23 + x24 + x25 + x26 + x27 + x28 + x29 + x30 + x31 + x32 + x33 + x34 + x35) + ((x36) + ((x37 + x38 + x39 + x40 + x41 + x42 + x43 + x44 + x45 + x46 + x47 + x48 + x49 + x50 + x51) + ((x52 + x53 + x54))))) =
    x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10 + x11 + x12 + x13 + x14 + x15 + x16 + x17 + x18 + x19 + x20 + x21 + x22 + x23 + x24 + x25 + x26 + x27 + x28 + x29 + x30 + x31 + x32 + x33 + x34 + x35 + x36 + x37 + x38 + x39 + x40 + x41 + x42 + x43 + x44 + x45 + x46 + x47 + x48 + x49 + x50 + x51 + x52 + x53 + x54 := by omega

theorem ptx_cost_eq : ptxCost1 + (ptxCost2 + (ptxCost3 + (ptxCost4 + ptxCost5))) = K.process_transaction := by
  exact ptx_cost_algebra ((K.«state_fresh_tx» + 1)) ((K.«encode_transaction» + 1)) ((K.«tx_chain_id» + 1)) ((K.«alloc» + 1)) ((K.«recover_sender_with_chain_id» + 1)) ((K.«validate_transaction» + 1)) ((K.«check_transaction» + 1)) ((K.«calculate_total_blob_gas» + 1)) ((K.«get_account» + 1)) (Nat.max ((K.«calculate_blob_gas_price» + 1) + (K.«fee_mul» + 1)) (0)) ((K.«fee_mul» + 1)) ((K.«min» + 1)) ((K.«increment_nonce» + 1)) ((K.«u256_sub» + 1)) ((K.«u256_sub» + 1)) ((K.«set_account_balance» + 1)) ((K.«te_new» + 1)) ((K.«tx_has_access_list» + 1)) ((K.«alloc» + 1)) ((2 ^ 64 + 1) * (0 + 1)) ((K.«alloc» + 1)) ((2 ^ 64 + 1) * ((2 ^ 64 + 1) * ((K.«memcpy» + 1) + (K.«memcpy» + 1) + 1) + 1)) ((K.«tx_is_blob» + 1)) ((K.«tx_is_setcode» + 1)) ((K.«alloc» + 1)) ((K.«keccak256» + 1)) ((K.«msg_new» + 1)) ((K.«htab_new» + 1)) ((K.«htab_set» + 1)) ((2 ^ 64 + 1) * ((K.«htab_set» + 1) + 1)) ((2 ^ 64 + 1) * ((K.«htab_set» + 1) + 1)) ((K.«htab_new» + 1)) ((2 ^ 64 + 1) * ((K.«htab_set» + 1) + 1)) ((K.«alloc» + 1)) (Nat.max ((K.«get_account» + 1) + (K.«alloc» + 1) + (K.«compute_contract_address» + 1)) (0)) ((K.«htab_set» + 1)) ((K.«process_message_call» + 1)) ((K.«udiv_small5» + 1)) ((K.«min» + 1)) ((K.«max» + 1)) ((K.«fee_mul» + 1)) ((K.«u256_sub» + 1)) ((K.«fee_mul» + 1)) ((K.«create_ether» + 1)) ((K.«create_ether» + 1)) ((K.«max» + 1)) (Nat.max ((K.«lst_new» + 1)) (0)) ((K.«encode_receipt» + 1)) ((2 ^ 64 + 1) * ((K.«lst_push» + 1) + 1)) ((K.«lst_new» + 1)) ((2 ^ 64 + 1) * (0 + 1)) ((K.«lst_push» + 1)) (Nat.max ((2 ^ 64 + 1) * ((K.«htab_item» + 1) + Nat.max ((K.«clear_account_preserving_balance» + 1)) (0) + 1)) (0)) ((K.«incorporate_tx_into_block» + 1)) (Nat.max ((K.«scratch_release» + 1) + (K.«frame_mem_release» + 1)) (0))

theorem ptx_lookup : originalRuntimeCode.lookup (ofString "process_transaction") =
    some ((sourceFunctionEntry Guest.Software.guestFn_process_transaction).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 873 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_process_transaction) rfl

/-! ## 3. AST Lookups and Parameter Binding Helpers -/

theorem lookup_lst_new : originalRuntimeCode.lookup (ofString "lst_new") =
    some ((sourceFunctionEntry Guest.Software.guestFn_lst_new).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 408 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_lst_new) rfl

theorem lookup_lst_push : originalRuntimeCode.lookup (ofString "lst_push") =
    some ((sourceFunctionEntry Guest.Software.guestFn_lst_push).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 410 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_lst_push) rfl

theorem lookup_encode_receipt : originalRuntimeCode.lookup (ofString "encode_receipt") =
    some ((sourceFunctionEntry Guest.Software.guestFn_encode_receipt).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 836 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_encode_receipt) rfl

theorem callee_param_two_exp {F : Type} (state : PanSemStateFiniteExact 64 F) (fname p1 p2 : MlS)
    (s1 s2 : ShapeHOL) (body : ProgHOL 64) (ret : ShapeHOL)
    (hl : state.code.lookup fname = some ([(p1, s1), (p2, s2)], body, ret))
    (e1 e2 : ExpHOL 64) (v1 v2 : ValueHOL 64)
    (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (he1 : evalAt state e1 = some v1) (he2 : evalAt state e2 = some v2)
    (hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [e1, e2] = some values)
    (hlook : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret')) :
    p1 ≠ p2 ∧ callee.lookup p1 = some v1 ∧ callee.lookup p2 = some v2 := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact, he1, he2, Option.some.injEq] at hargs
  subst hargs
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hlook
  split at hlook
  · cases hlook
  · rename_i exactBody exactLocals exactShape raw
    have heq := Option.some.inj hlook
    rcases Prod.mk.inj heq with ⟨rfl, hrest⟩
    rcases Prod.mk.inj hrest with ⟨rfl, _⟩
    unfold lookupCodeHOLExact at raw
    rw [hl] at raw
    dsimp only at raw
    split at raw
    · rename_i hcond
      have rawEq := Option.some.inj raw
      rcases Prod.mk.inj rawEq with ⟨-, hrest2⟩
      rcases Prod.mk.inj rawEq with ⟨_, hrest2'⟩
      rcases Prod.mk.inj hrest2 with ⟨hloc, -⟩
      subst hloc
      obtain ⟨hnd, -, -⟩ := hcond
      simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
        List.not_mem_nil, or_false] at hnd
      refine ⟨hnd.1, ?_, ?_⟩
      · simp [List.zip, List.foldl, hnd.1]
      · simp [List.zip, List.foldl]
    · cases raw

theorem callee_param_four_exp' {F : Type} (state : PanSemStateFiniteExact 64 F)
    (fname p1 p2 p3 p4 : MlS) (s1 s2 s3 s4 : ShapeHOL) (body : ProgHOL 64) (ret : ShapeHOL)
    (hl : state.code.lookup fname = some ([(p1, s1), (p2, s2), (p3, s3), (p4, s4)], body, ret))
    (e1 e2 e3 e4 : ExpHOL 64) (v1 v2 v3 v4 : ValueHOL 64)
    (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (he1 : evalAt state e1 = some v1) (he2 : evalAt state e2 = some v2)
    (he3 : evalAt state e3 = some v3) (he4 : evalAt state e4 = some v4)
    (hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [e1, e2, e3, e4] = some values)
    (hlook : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret')) :
    callee.lookup p1 = some v1 ∧ callee.lookup p2 = some v2 ∧
      callee.lookup p3 = some v3 ∧ callee.lookup p4 = some v4 := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact, he1, he2, he3, he4, Option.some.injEq] at hargs
  subst hargs
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hlook
  split at hlook
  · cases hlook
  · rename_i exactBody exactLocals exactShape raw
    have heq := Option.some.inj hlook
    rcases Prod.mk.inj heq with ⟨rfl, hrest⟩
    rcases Prod.mk.inj hrest with ⟨rfl, _⟩
    unfold lookupCodeHOLExact at raw
    rw [hl] at raw
    dsimp only at raw
    split at raw
    · rename_i hcond
      have rawEq := Option.some.inj raw
      rcases Prod.mk.inj rawEq with ⟨-, hrest2⟩
      rcases Prod.mk.inj hrest2 with ⟨hloc, -⟩
      subst hloc
      obtain ⟨hnd, -, -⟩ := hcond
      simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
        not_or, List.not_mem_nil, or_false] at hnd
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [List.zip, List.foldl, hnd.1.1, hnd.1.2.1, hnd.1.2.2]
      · simp [List.zip, List.foldl, hnd.2.1.1, hnd.2.1.2]
      · simp [List.zip, List.foldl, hnd.2.2.1]
      · simp [List.zip, List.foldl]
    · cases raw

/-! ## 4. General Hoare & Counted-Loop Combinators -/

theorem clock_store {F : Type} (s : PanSemStateFiniteExact 64 F) (a v : ExpHOL 64) :
    (evaluateHOLFiniteState s (.store a v)).2.clock = s.clock := by
  rw [evaluateHOLFiniteState_store]
  repeat' split
  all_goals (try dsimp only)

theorem seq_bound_trans
    {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {first second : ProgHOL 64} {a b : Nat}
    (h1 : TerminatingProgBoundedOn P first a) (hp : Hoare P first (fun r t => r = none → Q t))
    (h2 : TerminatingProgBoundedOn Q second b) :
    TerminatingProgBoundedOn P (.seq first second) (a + b) := by
  intro F state hcode hP
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata state first
  have hmid := hp.run state hcode hP
  unfold TerminatingRunBounded
  dsimp only
  intro hnt
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hr1 : evaluateHOLFiniteState state first with ⟨r1, mid⟩
  simp only [hr1] at hmeta hnt hmid ⊢
  cases r1 with
  | none =>
    dsimp only at hnt ⊢
    have hnt1 : (evaluateHOLFiniteState state first).1 ≠ some .timeOut := by simp [hr1]
    obtain ⟨s1, k1⟩ := h1 state hcode hP hnt1
    rw [hr1] at s1 k1
    dsimp only at s1 k1
    obtain ⟨s2, k2⟩ := h2 mid (hmeta.1.trans hcode) (hmid (by simp) rfl) hnt
    exact ⟨by omega, by omega⟩
  | some r =>
    dsimp only at hnt ⊢
    have hnt1 : (evaluateHOLFiniteState state first).1 ≠ some .timeOut := by simpa [hr1] using hnt
    obtain ⟨s1, k1⟩ := h1 state hcode hP hnt1
    rw [hr1] at s1 k1
    dsimp only at s1 k1
    exact ⟨by omega, k1⟩

theorem dec_bound_trans {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {name : MlS} {shape : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64} {b : Nat}
    (hinit : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64), P s →
      evalAt s init = some v → Q (setVarHOLFinite name v s))
    (hb : TerminatingProgBoundedOn Q body b) :
    TerminatingProgBoundedOn P (.dec name shape init body) b := by
  intro F s hc hP hnt
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢
  revert hnt
  split <;> intro hnt
  · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  · revert hnt
    split <;> intro hnt
    · rename_i v hv _
      simpa only [setVarHOLFinite] using hb (setVarHOLFinite name v s) hc (hinit s v hP hv) hnt
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

theorem Hoare.call0_resume {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {fname : MlS} {args : List (ExpHOL 64)}
    (hret : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64))
      (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
      (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F),
      s.code = originalRuntimeCode → P s →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vs →
      lookupCodeHOLFinite s.code.lookup fname vs = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post) →
      Q {post with locals := s.locals}) :
    Hoare P (.call (some (none, none)) fname args) (fun r t => r = none → Q t) := by
  refine ⟨fun {F} s hc hP hnt hr => ?_⟩
  rw [evaluateHOLFiniteState_call] at hr ⊢
  rcases ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · rw [ha] at hr; simp at hr
  · simp only [ha] at hr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vs with _ | ⟨body, callee, ret⟩
    · simp [hl] at hr
    · simp only [hl] at hr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hr
      · simp only [hz, ↓reduceIte] at hr ⊢
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, post⟩
        simp only [hb] at hr ⊢
        cases res with
        | none => simp at hr
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hr ⊢
            split at hr
            · rename_i hsh
              rw [if_pos hsh]
              exact hret s vs body callee ret v post hc hP ha hl hb
            · simp at hr
          | _ => simp at hr

theorem Hoare.callLocal_resume {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {name fname : MlS} {args : List (ExpHOL 64)}
    (hres : DecCallResumeOn P Q name fname args) :
    Hoare P (.call (some (some (.local, name), none)) fname args) (fun r t => r = none → Q t) := by
  refine ⟨fun {F} s hc hP hnt hr => ?_⟩
  rw [evaluateHOLFiniteState_call] at hr ⊢
  rcases ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · rw [ha] at hr; simp at hr
  · simp only [ha] at hr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vs with _ | ⟨body, callee, ret⟩
    · simp [hl] at hr
    · simp only [hl] at hr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hr
      · simp only [hz, ↓reduceIte] at hr ⊢
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, post⟩
        simp only [hb] at hr ⊢
        cases res with
        | none => simp at hr
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hr ⊢
            split at hr
            · rename_i hsh
              rw [if_pos hsh]
              split at hr
              · rename_i hv
                rw [if_pos hv]
                exact hres s vs body callee ret v post hc hP ha hl hb
              · simp at hr
            · simp at hr
          | _ => simp at hr

theorem Hoare.decCall_fall {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {names : List String} {name fname : MlS} {shape : ShapeHOL}
    {arguments : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hname : ∀ n ∈ names, ofString n ≠ name)
    (hQ : LocalsOnly names Q)
    (hres : DecCallResumeOn P R name fname arguments)
    (hcont : Hoare R cont (fun r t => r = none → Q t)) :
    Hoare P (.decCall name shape fname arguments cont) (fun r t => r = none → Q t) := by
  refine ⟨fun {F} s hcode hP _ hr => ?_⟩
  rcases hrun : evaluateHOLFiniteState s (.decCall name shape fname arguments cont) with ⟨r, post⟩
  rw [hrun] at hr
  dsimp only at hr
  subst hr
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hrun
  rcases hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments with _ | values
  · rw [hargs] at hrun; simp at hrun
  · rw [hargs] at hrun; dsimp only at hrun
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · rw [hl] at hrun; simp at hrun
    · rw [hl] at hrun; dsimp only at hrun
      by_cases hz : s.clock = 0
      · rw [if_pos hz] at hrun; simp at hrun
      · rw [if_neg hz] at hrun
        have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body').1
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨bres, bpost⟩
        rw [hb] at hrun hmeta
        dsimp only at hmeta
        cases bres with
        | none => simp at hrun
        | some br =>
          cases br with
          | returned v =>
            dsimp only at hrun
            split at hrun
            · set resumed := setVarHOLFinite name v { bpost with locals := s.locals }
              have hresR : R resumed := hres s values body' callee ret' v bpost hcode hP hargs hl hb
              have hresCode : resumed.code = originalRuntimeCode := hmeta.trans hcode
              rcases hc : evaluateHOLFiniteState resumed cont with ⟨cres, cpost⟩
              rw [hc] at hrun
              dsimp only at hrun
              obtain ⟨rfl, hpost_eq⟩ := Prod.mk.inj hrun
              have hQc0 := hcont.run resumed hresCode hresR (by rw [hc]; simp)
              rw [hc] at hQc0
              have hQc : Q cpost := hQc0 rfl
              dsimp only
              rw [← hpost_eq]
              exact hQ cpost _ cpost.clock
                (fun n hn => resVarEq_lookup_ne _ _ _ _ (hname n hn)) hQc
            · simp at hrun
          | _ => simp [emptyLocalsHOLFinite] at hrun

theorem panMemStoresHOL_word_spec {F : Type} {s : PanSemStateFiniteExact 64 F}
    {x : BitVec 64} {w : HolWordLab 64} {mem' : BitVec 64 → HolWordLab 64}
    (hst : @panMemStoresHOL 64 _ x [w] s.memaddrs
      (fun a => Classical.propDecidable (s.memaddrs a)) s.memory = some mem') :
    s.memaddrs x ∧ mem' x = w ∧ ∀ a : BitVec 64, a ≠ x → mem' a = s.memory a := by
  unfold panMemStoresHOL panMemStoreHOL at hst
  split_ifs at hst with hdom
  · simp only [panMemStoresHOL, Option.some.injEq] at hst
    subst hst
    exact ⟨hdom, if_pos rfl, fun a hne => if_neg hne⟩

theorem Hoare.store_fall {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {dst src : ExpHOL 64}
    (h : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (x : BitVec 64) (v : ValueHOL 64)
      (mem' : BitVec 64 → HolWordLab 64),
      P s → evalAt s dst = some (.val (.word x)) → evalAt s src = some v →
      @panMemStoresHOL 64 _ x (flattenHOL v) s.memaddrs
        (fun a => Classical.propDecidable (s.memaddrs a)) s.memory = some mem' →
      Q { s with memory := mem' }) :
    Hoare P (.store dst src) (fun r t => r = none → Q t) := by
  refine ⟨fun {F} s _ hP _ hr => ?_⟩
  rw [evaluateHOLFiniteState_store] at hr ⊢
  revert hr
  split
  · rename_i x hx
    split
    · rename_i v hv
      rcases hm : @panMemStoresHOL 64 _ x (flattenHOL v) s.memaddrs
          (fun a => Classical.propDecidable (s.memaddrs a)) s.memory with _ | mem'
      · simp
      · intro _
        exact h s x v mem' hP hx hv hm
    · simp
  · simp

private theorem decCall_flowing {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {name : MlS} {shape : ShapeHOL} {fn : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    {r : Option (PanSemResultExact 64)}
    (hr : r = none ∨ r = some .break ∨ r = some .continue)
    (hrun : evaluateHOLFiniteState s (.decCall name shape fn args cont) = (r, post)) :
    ∃ (_ : ValueHOL 64) (resumed cpost : PanSemStateFiniteExact 64 F),
      (∀ k, k ≠ name → resumed.locals.lookup k = s.locals.lookup k) ∧
      resumed.code = s.code ∧
      evaluateHOLFiniteState resumed cont = (r, cpost) ∧
      post = { cpost with locals := HolFiniteMapExact.resVarEq cpost.locals (name, s.locals.lookup name) } := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hrun
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · rw [hargs] at hrun
    rcases hr with rfl | rfl | rfl <;> simp at hrun
  · rw [hargs] at hrun; dsimp only at hrun
    rcases hl : lookupCodeHOLFinite s.code.lookup fn vs with _ | ⟨body', callee, ret'⟩
    · rw [hl] at hrun
      rcases hr with rfl | rfl | rfl <;> simp at hrun
    · rw [hl] at hrun; dsimp only at hrun
      by_cases hz : s.clock = 0
      · rw [if_pos hz] at hrun
        rcases hr with rfl | rfl | rfl <;> simp at hrun
      · rw [if_neg hz] at hrun
        have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body').1
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨bres, bpost⟩
        rw [hb] at hrun hmeta
        dsimp only at hmeta
        cases bres with
        | none => rcases hr with rfl | rfl | rfl <;> simp at hrun
        | some br =>
          cases br with
          | returned v =>
            dsimp only at hrun
            split at hrun
            · set resumed := setVarHOLFinite name v { bpost with locals := s.locals }
              rcases hc : evaluateHOLFiniteState resumed cont with ⟨cres, cpost⟩
              rw [hc] at hrun
              dsimp only at hrun
              obtain ⟨rfl, hpost_eq⟩ := Prod.mk.inj hrun
              refine ⟨v, resumed, cpost, ?_, hmeta, hc, hpost_eq.symm⟩
              intro k hk
              simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
            · rcases hr with rfl | rfl | rfl <;> simp at hrun
          | _ =>
            dsimp only [emptyLocalsHOLFinite] at hrun
            rcases hr with rfl | rfl | rfl <;> simp at hrun

inductive IncrBody (c : MlS) : ProgHOL 64 → Prop
  | incr : IncrBody c (.assign .local c (.op .add [.var .local c, .const 1]))
  | seq (first : ProgHOL 64) {tail : ProgHOL 64}
      (avoid : avoidsLocal c first = true) (noCont : noTopContinue first = true)
      (rest : IncrBody c tail) : IncrBody c (.seq first tail)
  | dec (name : MlS) (shape : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64}
      (distinct : c ≠ name) (rest : IncrBody c body) : IncrBody c (.dec name shape init body)
  | decCall (name : MlS) (shape : ShapeHOL) (fn : MlS) (args : List (ExpHOL 64))
      {cont : ProgHOL 64} (distinct : c ≠ name) (rest : IncrBody c cont) :
      IncrBody c (.decCall name shape fn args cont)

theorem IncrBody.run {c : MlS} {body : ProgHOL 64} (hb : IncrBody c body) :
    ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      state.locals.lookup c = some (.val (.word w)) →
      (evaluateHOLFiniteState state body).1 ≠ some .continue ∧
      ((evaluateHOLFiniteState state body).1 = none →
        (evaluateHOLFiniteState state body).2.locals.lookup c = some (.val (.word (w + 1)))) := by
  induction hb with
  | incr =>
    intro F state w atC
    have run : evaluateHOLFiniteState state
        (.assign .local c (.op .add [.var .local c, .const 1])) =
        (none, setVarHOLFinite c (.val (.word (w + 1))) state) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, atC, wordOpHOL, wordOp,
        valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
        shapeOfHOLExact, shapeEqHOL]
    rw [run]
    refine ⟨by simp, fun _ => ?_⟩
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  | seq first avoid noCont rest ih =>
    intro F state w atC
    have frame := evaluate_avoidsLocal_flowing c first avoid state
    have noContinue := evaluate_noTopContinue first noCont state
    rw [evaluateHOLFiniteState_seq_line780]
    cases firstRun : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [firstRun] at frame noContinue
      dsimp only at frame noContinue
      cases result with
      | none =>
        dsimp only
        have kept := frame (Or.inl rfl)
        exact ih middle w (by rw [kept]; exact atC)
      | some r =>
        dsimp only
        exact ⟨noContinue, fun h => by simp at h⟩
  | dec name shape init distinct rest ih =>
    intro F state w atC
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · exact ⟨by simp, by simp⟩
    · rename_i val _
      split
      · have atInner : (setVarHOLFinite name val state).locals.lookup c =
            some (.val (.word w)) := by
          simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm distinct, atC]
        obtain ⟨t1, t2⟩ := ih (setVarHOLFinite name val state) w atInner
        cases run : evaluateHOLFiniteState (setVarHOLFinite name val state) _ with
        | mk res post =>
          rw [run] at t1 t2
          dsimp only at t1 t2 ⊢
          refine ⟨t1, fun normal => ?_⟩
          rw [PanRunBounded.resVarEq_lookup, if_neg distinct]
          exact t2 normal
      · exact ⟨by simp, by simp⟩
  | @decCall name shape fn args cont distinct rest ih =>
    intro F state w atC
    have hcont : (evaluateHOLFiniteState state (.decCall name shape fn args cont)).1 ≠
        some .continue := by
      intro hc
      rcases hrun : evaluateHOLFiniteState state (.decCall name shape fn args cont) with ⟨r, post⟩
      rw [hrun] at hc
      dsimp only at hc
      subst hc
      obtain ⟨_, resumed, _, hloc, _, hcr, _⟩ :=
        decCall_flowing (Or.inr (Or.inr rfl)) hrun
      have atR : resumed.locals.lookup c = some (.val (.word w)) := (hloc c distinct).trans atC
      have := (ih resumed w atR).1
      rw [hcr] at this
      exact this rfl
    refine ⟨hcont, fun hnone => ?_⟩
    rcases hrun : evaluateHOLFiniteState state (.decCall name shape fn args cont) with ⟨r, post⟩
    rw [hrun] at hnone
    dsimp only at hnone
    subst hnone
    obtain ⟨_, resumed, _, hloc, _, hcr, hpost⟩ := decCall_flowing (Or.inl rfl) hrun
    have atR : resumed.locals.lookup c = some (.val (.word w)) := (hloc c distinct).trans atC
    have := (ih resumed w atR).2
    rw [hcr] at this
    rw [hpost, PanRunBounded.resVarEq_lookup, if_neg distinct]
    exact this rfl

private theorem signed_less_eq (left right : BitVec 64) :
    holAsmSignedLess left right = left.slt right := by
  have bl := left.isLt
  have br := right.isLt
  simp only [holAsmSignedLess, BitVec.slt_eq_decide, BitVec.toInt_eq_msb_cond,
    BitVec.msb_eq_decide]
  repeat (any_goals first | split)
  all_goals simp_all only [decide_eq_true_eq]
  all_goals apply Bool.eq_iff_iff.mpr
  all_goals simp_all [decide_eq_true_eq]
  all_goals omega

def signedUpRank (counter : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup counter with
  | some (.val (.word w)) => (9223372036854775807 - w.toInt).toNat
  | _ => 0

theorem signedUpRank_le (counter : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) :
    signedUpRank counter s ≤ 2 ^ 64 := by
  unfold signedUpRank
  split
  · rename_i w _
    have := BitVec.le_toInt w
    omega
  · omega

theorem while_less_localsOnly {names : List String}
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hP : LocalsOnly names P) (counter : MlS) (bound : ExpHOL 64)
    {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn P body B)
    (hp : Hoare P body (fun r t => r = none → P t))
    (hinc : IncrBody counter body) :
    TerminatingProgBoundedOn P (.while (.cmp .less (.var .local counter) bound) body)
      ((2 ^ 64 + 1) * (B + 1)) := by
  refine TerminatingProgBoundedOn.while_rank (signedUpRank counter)
    (fun s hs => hP.decClock s hs) hbody
    (fun s _ _ _ => signedUpRank_le counter s) ?_
  intro F s hcode hs ⟨result, hcond, hnz⟩ hflow
  change evalAt s _ = _ at hcond
  obtain ⟨w, v, hw, hv, hword⟩ := evalAt_cmp s .less _ _ result hcond
  simp only [evalAt, evalHOLExact] at hw
  have hwl : s.locals.lookup counter = some (.val (.word w)) := by simpa using hw
  obtain ⟨hnc_w, hinc_w⟩ := hinc.run (decClockHOLFinite s) w hwl
  have hnone : (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none := by
    rcases hflow with h | h
    · exact h
    · exact absurd h hnc_w
  have hnt_b : (evaluateHOLFiniteState (decClockHOLFinite s) body).1 ≠ some .timeOut := by
    rw [hnone]; simp
  have hP_post : P (evaluateHOLFiniteState (decClockHOLFinite s) body).2 :=
    hp.run (decClockHOLFinite s) hcode (hP.decClock s hs) hnt_b hnone
  refine ⟨hP_post, ?_⟩
  have hcmp : wordCmpHOL .less w v = true := by
    by_contra h; simp [h] at hword; exact hnz hword
  have hlt : w.toInt < v.toInt := by
    simpa only [wordCmpHOL, signed_less_eq, BitVec.slt_iff_toInt_lt] using hcmp
  have hvmax := BitVec.toInt_le (x := v)
  have hwmin := BitVec.le_toInt w
  have hwmax := BitVec.toInt_le (x := w)
  have hone : (1 : BitVec 64).toInt = 1 := by decide
  have hnext : (w + 1).toInt = w.toInt + 1 := by
    rw [BitVec.toInt_add, hone]
    apply Int.bmod_eq_of_le <;> omega
  have hi' := hinc_w hnone
  simp only [signedUpRank, hi', hwl, hnext]
  omega

theorem hoare_while_less_localsOnly {names : List String}
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hP : LocalsOnly names P) (counter : MlS) (bound : ExpHOL 64) {body : ProgHOL 64}
    (hp : Hoare P body (fun r t => r = none → P t))
    (hinc : IncrBody counter body)
    (hnb : InitECandidate.Solver.GuestUniformClockBound.noTopBreak body = true) :
    Hoare P (.while (.cmp .less (.var .local counter) bound) body) (fun r t => r = none → P t) := by
  refine ⟨fun {F} s hcode hs _ hr => ?_⟩
  rcases hrun : evaluateHOLFiniteState s (.while (.cmp .less (.var .local counter) bound) body) with
    ⟨r, post⟩
  rw [hrun] at hr
  dsimp only at hr
  subst hr
  suffices ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F),
      st.clock = k → st.code = originalRuntimeCode → P st →
      evaluateHOLFiniteState st (.while (.cmp .less (.var .local counter) bound) body) =
        (none, post) → P post from
    this s.clock s rfl hcode hs hrun
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro st hk st_code hPst hst_run
    rw [evaluateHOLFiniteState_while_total] at hst_run
    split at hst_run
    · rename_i res hcond
      split at hst_run
      · rename_i hwnz
        split at hst_run
        · simp at hst_run
        · dsimp only at hst_run
          rw [fixClockHOLFinite_evaluateState] at hst_run
          have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) body
          have hmeta := (evaluateHOLFiniteState_metadata (decClockHOLFinite st) body).1
          have hno_brk :=
            InitECandidate.Solver.GuestUniformClockBound.evaluate_noTopBreak body hnb
              (decClockHOLFinite st)
          change evalAt st _ = _ at hcond
          obtain ⟨w, _, hw, _, _⟩ := evalAt_cmp st .less _ _ res hcond
          simp only [evalAt, evalHOLExact] at hw
          have hwl : (decClockHOLFinite st).locals.lookup counter = some (.val (.word w)) := by
            simpa [decClockHOLFinite] using hw
          obtain ⟨hnc_w, _⟩ := hinc.run (decClockHOLFinite st) w hwl
          rcases bRun : evaluateHOLFiniteState (decClockHOLFinite st) body with ⟨r1, mid⟩
          rw [bRun] at hst_run hrem hmeta hnc_w hno_brk
          have hclk_lt : mid.clock < k := by
            change mid.clock ≤ st.clock - 1 at hrem
            omega
          cases r1 with
          | none =>
            have hPmid := hp.run (decClockHOLFinite st) st_code
              (hP.decClock st hPst) (by rw [bRun]; simp)
              (by rw [bRun])
            rw [bRun] at hPmid
            exact ih mid.clock hclk_lt mid rfl (hmeta.trans st_code) hPmid hst_run
          | some r1' =>
            cases r1' with
            | «continue» => exact absurd rfl hnc_w
            | «break» => exact absurd rfl hno_brk
            | _ => simp at hst_run
      · simp at hst_run
        obtain ⟨_, rfl⟩ := hst_run
        exact hPst
    · simp at hst_run

macro "ptx_incr" : tactic => `(tactic| repeat (first
  | exact IncrBody.incr
  | apply IncrBody.dec _ _ _ (by decide)
  | apply IncrBody.decCall _ _ _ _ (by decide)
  | apply IncrBody.seq _ rfl rfl))

/-! ## 5. Proof of `ptxPhase5_cut` (Spine Depths 139–144) -/

theorem Hoare.seq_fall {P R Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {first second : ProgHOL 64}
    (h1 : Hoare P first (fun r t => r = none → R t))
    (h2 : Hoare R second (fun r t => r = none → Q t)) :
    Hoare P (.seq first second) (fun r t => r = none → Q t) :=
  Hoare.seq ⟨fun s hc hP hnt => ⟨h1.run s hc hP hnt, fun hr h0 => absurd h0 hr⟩⟩ h2

theorem ptxPhase5_cut_worldOK (h : PtxCallees) :
    TerminatingProgBoundedOn WorldOK ptxPhase5 ptxCost5 := by
  have hk_clear : KeepsOn WorldOK WorldOK (ofString "clear_account_preserving_balance") := by
    apply h.wk_clear_account_preserving_balance.keepsOn_buffer_parts
    intro F s i hi
    change i ∈ [bufferRegion s ("keccak_pad", 136), bufferRegion s ("keccak_st", 200),
      bufferRegion s ("mpt_nib_scratch", 64), bufferRegion s ("sk_buf", 52)] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact ⟨("keccak_pad", 136), by decide, by decide, 136, le_rfl, rfl⟩
    · exact ⟨("keccak_st", 200), by decide, by decide, 200, le_rfl, rfl⟩
    · exact ⟨("mpt_nib_scratch", 64), by decide, by decide, 64, le_rfl, rfl⟩
    · exact ⟨("sk_buf", 64), by decide, by decide, 52, by decide, rfl⟩
  let b5 : Nat :=
    max (0 + (2 ^ 64 + 1) * ((K.«htab_item» + (max (K.«clear_account_preserving_balance» + 1) 0 + 0) + 1) + 1)) 0 +
      ((K.«incorporate_tx_into_block» + 1) +
        (max ((K.«scratch_release» + 1) + (K.«frame_mem_release» + 1)) 0 + 0))
  have hb : TerminatingProgBoundedOn WorldOK ptxPhase5 b5 := by
    unfold b5 ptxPhase5 ptxCode
    simp only [sourceFunctionEntry, Guest.Software.guestFn_process_transaction,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
      Option.map_none, Option.map_some, List.map_cons, List.map_nil, spineAt]
    apply TerminatingProgBoundedOn.dec_on localsFree_worldOK
    refine seq_bound_trans (Q := WorldOK) ?_ ?_ ?_
    · -- `ite (del != 0) ... skip`
      apply TerminatingProgBoundedOn.ite_on
      · apply TerminatingProgBoundedOn.dec_on localsFree_worldOK
        refine seq_bound_trans (Q := WorldOK)
          (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s .local _ _))
          (Hoare.assign (fun s v hW _ _ => localsFree_worldOK s (s.locals.update (_, v)) s.clock hW)
            (fun _ _ hr => absurd hr (by simp))) ?_
        apply while_less_localsOnly (LocalsOnly.of_localsFree localsFree_worldOK)
        · -- loop body bound
          refine TerminatingProgBoundedOn.decCall_on h.fb_htab_item _ _ _
            (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _)
            (ReadOnlyFn.resumeOn (LocalsOnly.of_localsFree localsFree_worldOK) worldOK_guestInv
              h.ro_htab_item _ (by simp) _) ?_
          refine seq_bound_trans (Q := WorldOK) ?_ ?_
            (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s .local _ _))
          · apply TerminatingProgBoundedOn.ite_on
            · exact TerminatingProgBoundedOn.call_on h.fb_clear_account_preserving_balance none _
                (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _)
            · exact TerminatingProgBoundedOn.of_clock clock_skip
          · exact Hoare.ite
              (Hoare.mono (Hoare.call_keeps localsFree_worldOK hk_clear _) (fun _ hp => hp.1))
              (Hoare.skip (fun _ hp _ => hp.1))
              (fun _ _ hr => absurd hr (by simp))
        · -- loop body Hoare preservation of `WorldOK`
          apply Hoare.decCall_fall (names := []) (by simp) (LocalsOnly.of_localsFree localsFree_worldOK)
            (ReadOnlyFn.resumeOn (LocalsOnly.of_localsFree localsFree_worldOK) worldOK_guestInv
              h.ro_htab_item _ (by simp) _)
          exact Hoare.seq_fall
            (Hoare.ite
              (Hoare.mono (Hoare.call_keeps localsFree_worldOK hk_clear _) (fun _ hp => hp.1))
              (Hoare.skip (fun _ hp _ => hp.1))
              (fun _ _ hr => absurd hr (by simp)))
            (Hoare.assign (fun s v hW _ _ => localsFree_worldOK s (s.locals.update (_, v)) s.clock hW)
              (fun _ _ hr => absurd hr (by simp)))
        · ptx_incr
      · exact TerminatingProgBoundedOn.of_clock clock_skip
    · -- Hoare preservation of `WorldOK` across `ite (del != 0) ... skip`
      apply Hoare.ite
      · refine Hoare.mono (P' := WorldOK) ?_ (fun _ hp => hp.1)
        refine Hoare.dec (names := []) (P' := WorldOK) (by simp)
          (fun s v hW _ => localsFree_worldOK s (s.locals.update (_, v)) s.clock hW) ?_
          (fun _ t locals _ hh hr => localsFree_worldOK t locals t.clock (hh hr))
          (fun _ _ hr => absurd hr (by simp))
        refine Hoare.seq_fall
          (Hoare.assign (fun s v hW _ _ => localsFree_worldOK s (s.locals.update (_, v)) s.clock hW)
            (fun _ _ hr => absurd hr (by simp))) ?_
        refine hoare_while_less_localsOnly (LocalsOnly.of_localsFree localsFree_worldOK) _ _ ?_
          (by ptx_incr) rfl
        apply Hoare.decCall_fall (names := []) (by simp) (LocalsOnly.of_localsFree localsFree_worldOK)
          (ReadOnlyFn.resumeOn (LocalsOnly.of_localsFree localsFree_worldOK) worldOK_guestInv
            h.ro_htab_item _ (by simp) _)
        exact Hoare.seq_fall
          (Hoare.ite
            (Hoare.mono (Hoare.call_keeps localsFree_worldOK hk_clear _) (fun _ hp => hp.1))
            (Hoare.skip (fun _ hp _ => hp.1))
            (fun _ _ hr => absurd hr (by simp)))
          (Hoare.assign (fun s v hW _ _ => localsFree_worldOK s (s.locals.update (_, v)) s.clock hW)
            (fun _ _ hr => absurd hr (by simp)))
      · exact Hoare.skip (fun _ hp _ => hp.1)
      · exact fun _ _ hr => absurd hr (by simp)
    · -- `seq (call incorporate_tx_into_block []) (GuestInv tail)`
      refine TerminatingProgBoundedOn.seq_guestInv_after
        (TerminatingProgBoundedOn.call_on h.gb_incorporate_tx_into_block none []
          (callEntryOn_of_localsFree localsFree_worldOK _ _))
        worldOK_guestInv ?_
      apply TerminatingProgBoundedOn.dec_on localsFree_guestInv
      refine TerminatingProgBoundedOn.seq_guestInv ?_
        (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _))
      apply TerminatingProgBoundedOn.ite_on
      · exact TerminatingProgBoundedOn.seq_guestInv
          (TerminatingProgBoundedOn.call_guestInv h.fb_scratch_release none _)
          (TerminatingProgBoundedOn.call_guestInv h.fb_frame_mem_release none _)
      · exact TerminatingProgBoundedOn.of_clock clock_skip
  have heq : b5 ≤ ptxCost5 := by
    dsimp only [b5]
    unfold ptxCost5
    simp only [show ∀ a b : Nat, Nat.max a b = max a b from fun _ _ => rfl]
    omega
  intro F s hc hp
  exact (hb s hc hp).weaken heq

/-- Phase 5 cut: native HOL spine depths 139–144. -/
theorem ptxPhase5_cut (h : PtxCallees) :
    TerminatingProgBoundedOn PtxReceiptsDone ptxPhase5 ptxCost5 :=
  fun {_} s hc hp => ptxPhase5_cut_worldOK h s hc hp.1.1

theorem ptxPhase5_cut_stable (h : PtxCallees) :
    TerminatingProgBoundedOn PtxReceiptsStable ptxPhase5 ptxCost5 :=
  fun {_} s hc hp => ptxPhase5_cut_worldOK h s hc hp.1.1

/-! ## 6. R11 World Congruence & Single-Word Store Helpers for Phase 4 -/

theorem ordinaryDomain_iff (x : BitVec 64) :
    ordinaryDomain x ↔ x.toNat % 8 = 0 ∧ sourceBase ≤ x.toNat ∧ x.toNat < heapEnd := by
  unfold ordinaryDomain
  rw [StackRemove.mem_addresses]
  have hx := x.isLt
  have hconst : (stackStart - sourceBase) / 8 - globalsWords = 3888119741 ∧
      sourceBase = 2701131776 ∧ heapEnd = 33806089704 ∧
      StackRemove.bytesInWord 64 = BitVec.ofNat 64 8 :=
    ⟨by decide, by decide, by decide, by decide⟩
  rcases hconst with ⟨hn, hsb, hhe, hbw⟩
  rw [hn, hbw]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat]
    simp only [hsb, hhe]; omega
  · rintro ⟨hal, hlo, hhi⟩
    refine ⟨(x.toNat - sourceBase) / 8, by simp only [hsb, hhe] at hlo hhi; omega, ?_⟩
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat]
    simp only [hsb, hhe] at hlo hhi ⊢; omega

theorem disj_symm {i j : Ivl} (h : Disj i j) : Disj j i := h.flip
theorem disj_zero_left (j : Ivl) : Disj (0, 0) j := Or.inl rfl
theorem disj_zero_right (i : Ivl) : Disj i (0, 0) := Or.inr (Or.inl rfl)

theorem disj_of_inside_left {i i' j : Ivl} (hin : Inside i i'.1 (i'.1 + i'.2))
    (hd : Disj i' j) : Disj i j := by
  rcases hin with ⟨h1, h2⟩
  rcases hd with hd | hd | hd | hd
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl hd)
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (by omega)))

theorem disj_of_inside_right {i j j' : Ivl} (hin : Inside j j'.1 (j'.1 + j'.2))
    (hd : Disj i j') : Disj i j :=
  disj_symm (disj_of_inside_left hin (disj_symm hd))

def IvlUnhit {F : Type} (s post : PanSemStateFiniteExact 64 F) (i : Ivl) : Prop :=
  ∀ a : BitVec 64, a.toNat % 8 = 0 → CellHits a.toNat i → post.memory a = s.memory a

theorem memW_eq_of_ivlUnhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {i : Ivl} (hu : IvlUnhit s post i) {a : Nat}
    (ha8 : a % 8 = 0) (hhi : i.1 + i.2 ≤ 2 ^ 64) (hin : i.1 ≤ a ∧ a + 8 ≤ i.1 + i.2) :
    memW post a = memW s a := by
  have ha_lt : a < 2 ^ 64 := by omega
  have hmem := hu (BitVec.ofNat 64 a)
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]; exact ha8)
    (by unfold CellHits; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]; omega)
  unfold memW; rw [hmem]

theorem memB_eq_of_ivlUnhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {i : Ivl} (hu : IvlUnhit s post i) (hbe : post.be = s.be)
    {a : Nat} (hhi : i.1 + i.2 ≤ 2 ^ 64) (hin : i.1 ≤ a ∧ a < i.1 + i.2) :
    memB post a = memB s a := by
  have ha_lt : a < 2 ^ 64 := by omega
  let c := panByteAlignHOL (BitVec.ofNat 64 a)
  have hc_nat : c.toNat = a / 8 * 8 := by
    have hal : 2 ^ ((64 : Nat) / 8).log2 = 8 := by decide
    change (BitVec.ofNat 64 ((BitVec.ofNat 64 a).toNat / 2 ^ ((64 : Nat) / 8).log2 *
      2 ^ ((64 : Nat) / 8).log2)).toNat = a / 8 * 8
    rw [hal, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt,
      Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_mul_le_self a 8) ha_lt)]
  have hmem := hu c (by rw [hc_nat]; omega) (by unfold CellHits; rw [hc_nat]; omega)
  unfold memB
  change (match post.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 a) v post.be).toNat) =
         (match s.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 a) v s.be).toNat)
  rw [hmem, hbe]

theorem ivl_allocated_bound {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) {i : Ivl} (hal : Allocated s i) :
    i.1 + i.2 ≤ heapEnd ∧ i.1 + i.2 ≤ 2 ^ 64 := by
  have h1 : heapLimit ≤ heapEnd := by decide
  have h2 : scratchEnd ≤ heapEnd := by decide
  have h3 : heapEnd < 2 ^ 64 := by decide
  rcases hal with ⟨_, hi⟩ | ⟨_, hi⟩
  · have := hA.2.1; omega
  · have := hA.2.2.2.2.1; omega

theorem wordsOK_transfer {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgS : GuestInv s) (hgP : GuestInv post) {i : Ivl} (hw : WordsOK s i) :
    WordsOK post i := by
  refine ⟨hw.1, hw.2.1, fun k hk => ?_⟩
  obtain ⟨_, hdom, _⟩ := hw.2.2 k hk
  rcases hm : post.memory (BitVec.ofNat 64 (i.1 + 8 * k)) with ⟨w⟩
  refine ⟨w, ?_, hm⟩
  rw [hgP.memaddrs, ← hgS.memaddrs]
  exact hdom

theorem wordAt_transfer {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgS : GuestInv s) (hgP : GuestInv post) {a : Nat} (hw : WordAt s a) :
    WordAt post a := by
  obtain ⟨_, hdom, _⟩ := hw
  rcases hm : post.memory (BitVec.ofNat 64 a) with ⟨w⟩
  exact ⟨w, by rw [hgP.memaddrs, ← hgS.memaddrs]; exact hdom, hm⟩

theorem not_cellHits_of_disj {a : Nat} {i j : Ivl}
    (ha8 : a % 8 = 0) (hj0 : j.2 = 0 → j.1 % 8 = 0)
    (ha : i.1 ≤ a ∧ a + 8 ≤ i.1 + i.2) (hd : Disj i j) :
    ¬ CellHits a j := by
  unfold Disj at hd
  unfold CellHits
  rcases hd with h | h | h | h
  · omega
  · have hj8 := hj0 h; omega
  · omega
  · omega

theorem ivlUnhit_single {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {x : BitVec 64} {i : Ivl}
    (hm : ∀ a, a ≠ x → post.memory a = s.memory a)
    (hi0 : i.2 = 0 → i.1 % 8 = 0) (hd : Disj i (x.toNat, 8)) : IvlUnhit s post i := by
  intro a ha hh
  apply hm
  intro he
  subst a
  exact not_cellHits_of_disj ha hi0 ⟨le_rfl, le_rfl⟩ (disj_symm hd) hh

theorem fixedObjects_zero_aligned {F : Type} {s : PanSemStateFiniteExact 64 F} :
    ∀ i ∈ fixedObjects s, i.2 = 0 → i.1 = 0 := by
  have hgb_pos : ∀ gn ∈ globalBuffers, gn.2 ≠ 0 := by decide
  have hobj0 : ∀ (c : Prop) [Decidable c] (p len : Nat),
      (if c ∨ p = 0 ∨ len = 0 then (0, 0) else (p, len)).2 = 0 →
      (if c ∨ p = 0 ∨ len = 0 then (0, 0) else (p, len)).1 = 0 := by
    intro c _ p len hz
    split_ifs at hz ⊢ with h
    · rfl
    · dsimp only at hz; omega
  have hlst0 : ∀ (l esz : Nat) (x : Ivl), x ∈ lstObjects s l esz → x.2 = 0 → x.1 = 0 := by
    intro l esz x hx hxz
    unfold lstObjects at hx
    by_cases hl0 : l = 0
    · simp only [hl0, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> rfl
    · simp only [hl0, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · simp at hxz
      · dsimp only at hxz ⊢
        by_cases he : esz * memW s (l + 16) = 0
        · simp [he]
        · exact absurd hxz he
  have hbo_lst0 : ∀ (k : Nat) (x : Ivl),
      x ∈ (if globN s "bo" = 0 ∨ memW s (globN s "bo" + k) = 0 then [(0, 0), (0, 0)]
           else [(if globN s "bo" = 0 ∨ memW s (globN s "bo" + k) = 0 ∨ 24 = 0 then (0, 0)
                  else (memW s (globN s "bo" + k), 24)),
                 (if globN s "bo" = 0 ∨ memW s (memW s (globN s "bo" + k)) = 0 ∨
                    8 * memW s (memW s (globN s "bo" + k) + 16) = 0 then (0, 0)
                  else (memW s (memW s (globN s "bo" + k)), 8 * memW s (memW s (globN s "bo" + k) + 16)))]) →
      x.2 = 0 → x.1 = 0 := by
    intro k x hx hxz
    by_cases hc : globN s "bo" = 0 ∨ memW s (globN s "bo" + k) = 0
    · simp only [hc, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> rfl
    · simp only [hc, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> exact hobj0 _ _ _ hxz
  intro i hi hz
  unfold fixedObjects at hi
  simp only [List.mem_append] at hi
  rcases hi with ((hgb | hjr) | hbo) | hbal
  · obtain ⟨gn, hgn, rfl⟩ := List.mem_map.1 hgb
    have hpos := hgb_pos gn hgn
    dsimp only at hz ⊢
    split_ifs at hz with h0
    · exact h0
    · exact absurd hz hpos
  · simp only [List.mem_singleton] at hjr; subst hjr
    dsimp only at hz ⊢
    split_ifs with h0
    · rfl
    · omega
  · unfold blockOutObjects at hbo
    dsimp only at hbo
    simp only [List.mem_append] at hbo
    rcases hbo with (hb3 | h40) | h72
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb3
      rcases hb3 with rfl | rfl | rfl <;> exact hobj0 _ _ _ hz
    · exact hbo_lst0 40 i h40 hz
    · exact hbo_lst0 72 i h72 hz
  · unfold balObjects at hbal
    obtain ⟨ad, _, had⟩ := List.mem_flatMap.1 hbal
    simp only [List.cons_append] at had
    rcases List.mem_cons.1 had with rfl | hrest
    · simp at hz
    · simp only [List.mem_append] at hrest
      rcases hrest with ((hl1 | hl2) | hl3) | hlf
      · exact hlst0 _ _ _ hl1 hz
      · exact hlst0 _ _ _ hl2 hz
      · exact hlst0 _ _ _ hl3 hz
      · obtain ⟨l, _, hxl⟩ := List.mem_flatMap.1 hlf
        exact hlst0 _ _ _ hxl hz

theorem worldOwned_zero_aligned {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hW : WorldTypedWith s S Nd) :
    ∀ i ∈ worldOwned s S Nd, i.2 = 0 → i.1 % 8 = 0 := by
  intro i hi hz
  unfold worldOwned at hi
  simp only [List.mem_append] at hi
  rcases hi with (hi | hi) | hi
  · obtain ⟨t, ht, hi⟩ := List.mem_flatMap.mp hi
    exact ((hW.1.2.1 t ht).1.1 i hi).2.1
  · rw [fixedObjects_zero_aligned i hi hz]
  · obtain ⟨n, _, hi⟩ := List.mem_flatMap.mp hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · unfold nodeIvl nodeSize at hz; split_ifs at hz
    · unfold nodePath at hz ⊢
      split_ifs at hz ⊢ with h
      · exact False.elim (h.2 hz)
      · rfl

theorem worldTypedIvls_sub_worldOwned {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {i : Ivl} (hi : i ∈ worldTypedIvls s S Nd) :
    i ∈ worldOwned s S Nd := by
  unfold worldTypedIvls at hi
  unfold worldOwned
  simp only [List.mem_append] at hi ⊢
  rcases hi with ((((ht | hr) | hjr) | hbo) | hbal) | hnd
  · exact Or.inl (Or.inl ht)
  · obtain ⟨r, hrec, rfl⟩ := List.mem_map.1 hr
    refine Or.inl (Or.inr ?_)
    unfold fixedObjects
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    refine List.mem_map.2 ⟨r, ?_, rfl⟩
    simp only [typedRecords, List.mem_cons, List.not_mem_nil, or_false] at hrec
    rcases hrec with rfl | rfl | rfl | rfl <;> decide
  · refine Or.inl (Or.inr ?_)
    unfold fixedObjects
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
    exact hjr
  · refine Or.inl (Or.inr ?_)
    unfold fixedObjects
    apply List.mem_append_left; apply List.mem_append_right
    exact hbo
  · refine Or.inl (Or.inr ?_)
    unfold fixedObjects
    exact List.mem_append_right _ hbal
  · exact Or.inr hnd

theorem pairwise_disj_mem {xs : List Ivl} (h : xs.Pairwise Disj)
    {i j : Ivl} (hi : i ∈ xs) (hj : j ∈ xs) (hne : i ≠ j) : Disj i j := by
  induction xs with
  | nil => simp at hi
  | cons a xs ih =>
    obtain ⟨ha, ht⟩ := List.pairwise_cons.mp h
    rcases List.mem_cons.mp hi with hia | hi'
    · rcases List.mem_cons.mp hj with hja | hj'
      · exact (hne (hia.trans hja.symm)).elim
      · rw [hia]; exact ha j hj'
    · rcases List.mem_cons.mp hj with hja | hj'
      · rw [hja]; exact disj_symm (ha i hi')
      · exact ih ht hi' hj'

theorem freeChain_congr_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {nodes ncap : Nat} (hn8 : nodes % 8 = 0) (hhi : nodes + (ncap + 1) * 32 ≤ 2 ^ 64)
    (hu : IvlUnhit s post (nodes, (ncap + 1) * 32)) :
    ∀ (Fr : List Nat) (head : Nat),
      (∀ f ∈ Fr, 1 ≤ f ∧ f ≤ ncap) →
      (FreeChain post nodes head Fr ↔ FreeChain s nodes head Fr)
  | [], _, _ => Iff.rfl
  | f :: rest, head, hFr => by
    have hf : 1 ≤ f ∧ f ≤ ncap := hFr f (by simp)
    have hnd : nodeF post nodes f 0 = nodeF s nodes f 0 := by
      unfold nodeF
      exact memW_eq_of_ivlUnhit hu (by omega) hhi ⟨by omega, by omega⟩
    simp only [FreeChain, hnd]
    exact and_congr Iff.rfl (freeChain_congr_unhit hn8 hhi hu rest _ (fun x hx => hFr x (by simp [hx])))

theorem htabFootprint_eq_of_hdr_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {t : Nat} (ht8 : t % 8 = 0) (hhdr_hi : t + 88 ≤ 2 ^ 64) (hu : IvlUnhit s post (t, 88)) :
    (∀ k, k < 11 → hdr post t k = hdr s t k) ∧ htabFootprint post t = htabFootprint s t := by
  have hhdr : ∀ k, k < 11 → hdr post t k = hdr s t k := fun k hk => by
    unfold hdr
    exact memW_eq_of_ivlUnhit hu (by omega) hhdr_hi ⟨by omega, by omega⟩
  refine ⟨hhdr, ?_⟩
  simp only [htabFootprint, hhdr 1 (by omega), hhdr 4 (by omega), hhdr 5 (by omega),
    hhdr 6 (by omega), hhdr 10 (by omega)]

private theorem htabCount_le_ncap {F : Type} {s : PanSemStateFiniteExact 64 F} {t : Nat}
    (hwf : HtabWF s t) : hdr s t 3 ≤ hdr s t 10 := by
  obtain ⟨_, _, _, _, _, _, _, hnx2, L, I, Fr, hLlen, hnd, hmem, _⟩ := hwf
  have hLn : L.Nodup := ((List.nodup_append.1 hnd).1 |> List.nodup_append.1).1
  have hsub : L ⊆ List.range' 1 (hdr s t 8 - 1) := by
    intro x hx
    rw [List.mem_range']
    have := (hmem x).1 (List.mem_append_left Fr (List.mem_append_left I hx))
    exact ⟨x - 1, by omega, by omega⟩
  have hle := List.Subperm.length_le (hLn.subperm hsub)
  rw [List.length_range'] at hle
  omega

theorem htabValues_eq_of_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {t : Nat} (hwf : HtabWF s t)
    (hu : ∀ i ∈ htabFootprint s t, IvlUnhit s post i) :
    htabValues post t = htabValues s t := by
  have h264 : heapEnd ≤ 2 ^ 64 := by decide
  have hfp := hwf.1
  have ht_fp : (t, 88) ∈ htabFootprint s t := by simp [htabFootprint]
  have hnd_fp : (hdr s t 5, (hdr s t 10 + 1) * 32) ∈ htabFootprint s t := by simp [htabFootprint]
  have hord_fp : (hdr s t 6, (hdr s t 10 + 1) * 8) ∈ htabFootprint s t := by simp [htabFootprint]
  have ht8 : t % 8 = 0 := (hfp _ ht_fp).2.1
  have hnd8 : (hdr s t 5) % 8 = 0 := (hfp _ hnd_fp).2.1
  have hord8 : (hdr s t 6) % 8 = 0 := (hfp _ hord_fp).2.1
  have hhdr_hi : t + 88 ≤ 2 ^ 64 := by have := (hfp _ ht_fp).1.2; omega
  obtain ⟨hhdr, _⟩ := htabFootprint_eq_of_hdr_unhit ht8 hhdr_hi (hu _ ht_fp)
  have hnd_hi : hdr s t 5 + (hdr s t 10 + 1) * 32 ≤ 2 ^ 64 := by have := (hfp _ hnd_fp).1.2; omega
  have hord_hi : hdr s t 6 + (hdr s t 10 + 1) * 8 ≤ 2 ^ 64 := by have := (hfp _ hord_fp).1.2; omega
  have hcnt_le := htabCount_le_ncap hwf
  obtain ⟨-, -, -, -, -, _, _, _, L, I, Fr, hLlen, _, hmem, _, hL, -⟩ := hwf
  unfold htabValues
  rw [hhdr 3 (by omega), hhdr 5 (by omega), hhdr 6 (by omega)]
  apply List.map_congr_left
  intro idx hidx
  rw [List.mem_range] at hidx
  have hidx_L : idx < L.length := by omega
  have hLi_mem : L[idx] ∈ L ++ I ++ Fr :=
    List.mem_append_left Fr (List.mem_append_left I (List.getElem_mem hidx_L))
  have hLi_bound : 1 ≤ L[idx] ∧ L[idx] ≤ hdr s t 10 := by
    have := (hmem L[idx]).1 hLi_mem; omega
  have hord_eq : memW post (hdr s t 6 + 8 * idx) = memW s (hdr s t 6 + 8 * idx) :=
    memW_eq_of_ivlUnhit (hu _ hord_fp) (by omega) hord_hi ⟨by omega, by omega⟩
  rw [hord_eq, (hL idx hidx_L).1]
  unfold nodeF
  exact memW_eq_of_ivlUnhit (hu _ hnd_fp) (by omega) hnd_hi ⟨by omega, by omega⟩

theorem htabValuesIn_congr_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {t : Nat} {S S' : List Nat} (hwf : HtabWF s t)
    (hu : ∀ i ∈ htabFootprint s t, IvlUnhit s post i)
    (hsub : ∀ x ∈ S, x ∈ S')
    (hval : HtabValuesIn s t S) :
    HtabValuesIn post t S' := by
  have h264 : heapEnd ≤ 2 ^ 64 := by decide
  have hfp := hwf.1
  have ht_fp : (t, 88) ∈ htabFootprint s t := by simp [htabFootprint]
  have ht8 : t % 8 = 0 := (hfp _ ht_fp).2.1
  have hhdr_hi : t + 88 ≤ 2 ^ 64 := by have := (hfp _ ht_fp).1.2; omega
  obtain ⟨hhdr, _⟩ := htabFootprint_eq_of_hdr_unhit ht8 hhdr_hi (hu _ ht_fp)
  have hvals := htabValues_eq_of_unhit hwf hu
  intro idx hidx
  rw [hhdr 3 (by omega)] at hidx
  have hmem_s : nodeF s (hdr s t 5) (memW s (hdr s t 6 + 8 * idx)) 8 ∈ S := hval idx hidx
  have hget : (htabValues post t)[idx]? = (htabValues s t)[idx]? := by rw [hvals]
  simp only [htabValues, List.getElem?_map, List.getElem?_range, hhdr 3 (by omega), hidx,
    Option.map_some, Option.some.injEq] at hget
  rw [hget]
  exact hsub _ hmem_s

theorem htabWF_congr_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgS : GuestInv s) (hgP : GuestInv post)
    {t : Nat} (hwf : HtabWF s t)
    (hu : ∀ i ∈ htabFootprint s t, IvlUnhit s post i) :
    HtabWF post t := by
  have h264 : heapEnd ≤ 2 ^ 64 := by decide
  have hfp := hwf.1
  have ht_fp : (t, 88) ∈ htabFootprint s t := by simp [htabFootprint]
  have hnd_fp : (hdr s t 5, (hdr s t 10 + 1) * 32) ∈ htabFootprint s t := by simp [htabFootprint]
  have hord_fp : (hdr s t 6, (hdr s t 10 + 1) * 8) ∈ htabFootprint s t := by simp [htabFootprint]
  have ht8 : t % 8 = 0 := (hfp _ ht_fp).2.1
  have hnd8 : (hdr s t 5) % 8 = 0 := (hfp _ hnd_fp).2.1
  have hord8 : (hdr s t 6) % 8 = 0 := (hfp _ hord_fp).2.1
  have hhdr_hi : t + 88 ≤ 2 ^ 64 := by have := (hfp _ ht_fp).1.2; omega
  obtain ⟨hhdr, hfp_eq⟩ := htabFootprint_eq_of_hdr_unhit ht8 hhdr_hi (hu _ ht_fp)
  have hnd_hi : hdr s t 5 + (hdr s t 10 + 1) * 32 ≤ 2 ^ 64 := by have := (hfp _ hnd_fp).1.2; omega
  have hord_hi : hdr s t 6 + (hdr s t 10 + 1) * 8 ≤ 2 ^ 64 := by have := (hfp _ hord_fp).1.2; omega
  have hcnt_le := htabCount_le_ncap hwf
  obtain ⟨hfp1, hfp2, hk1, hk2, hstr, hncap, hnext1, hnext2,
    L, I, Fr, hLlen, hnodup, hmem, hcntI, hL, hI, hr0, hrpos, hnroot, hpI, hdep, hfc⟩ := hwf
  have hnd_eq : ∀ n, 1 ≤ n → n ≤ hdr s t 10 → ∀ off ∈ ([0, 8, 16, 24] : List Nat),
      nodeF post (hdr s t 5) n off = nodeF s (hdr s t 5) n off := by
    intro n hn1 hn2 off hoff
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    unfold nodeF
    rcases hoff with rfl | rfl | rfl | rfl <;>
      exact memW_eq_of_ivlUnhit (hu _ hnd_fp) (by omega) hnd_hi ⟨by omega, by omega⟩
  have hLI_bound : ∀ n ∈ L ++ I, 1 ≤ n ∧ n ≤ hdr s t 10 := fun n hn => by
    have := (hmem n).1 (List.mem_append_left Fr hn); omega
  unfold HtabWF
  rw [hfp_eq, hhdr 0 (by omega), hhdr 1 (by omega), hhdr 3 (by omega), hhdr 5 (by omega),
    hhdr 6 (by omega), hhdr 7 (by omega), hhdr 8 (by omega), hhdr 9 (by omega), hhdr 10 (by omega)]
  refine ⟨fun i hi => ⟨(hfp1 i hi).1, wordsOK_transfer hgS hgP (hfp1 i hi).2⟩,
    hfp2, hk1, hk2, hstr, hncap, hnext1, hnext2, L, I, Fr, hLlen, hnodup, hmem, hcntI,
    ?_, ?_, hr0, ?_, ?_, ?_, ?_, ?_⟩
  · intro idx hidx
    have hLi : L[idx] ∈ L ++ I := List.mem_append_left I (List.getElem_mem hidx)
    obtain ⟨hb1, hb2⟩ := hLI_bound L[idx] hLi
    have hord_eq : memW post (hdr s t 6 + 8 * idx) = memW s (hdr s t 6 + 8 * idx) :=
      memW_eq_of_ivlUnhit (hu _ hord_fp) (by omega) hord_hi ⟨by omega, by omega⟩
    rw [hord_eq, hnd_eq L[idx] hb1 hb2 24 (by simp), hnd_eq L[idx] hb1 hb2 16 (by simp)]
    exact hL idx hidx
  · intro n hn
    have hnLI : n ∈ L ++ I := List.mem_append_right L hn
    obtain ⟨hb1, hb2⟩ := hLI_bound n hnLI
    obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6⟩ := hI n hn
    obtain ⟨h8_1, h8_2⟩ := hLI_bound _ hc2
    obtain ⟨h16_1, h16_2⟩ := hLI_bound _ hc3
    rw [hnd_eq n hb1 hb2 24 (by simp), hnd_eq n hb1 hb2 8 (by simp), hnd_eq n hb1 hb2 16 (by simp),
      hnd_eq _ h8_1 h8_2 0 (by simp), hnd_eq _ h16_1 h16_2 0 (by simp)]
    exact ⟨hc1, hc2, hc3, hc4, hc5, hc6⟩
  · intro hpos
    obtain ⟨hrm, hrp⟩ := hrpos hpos
    obtain ⟨hb1, hb2⟩ := hLI_bound _ hrm
    rw [hnd_eq _ hb1 hb2 0 (by simp)]
    exact ⟨hrm, hrp⟩
  · intro n hn
    have hnLI : n ∈ L ++ I := List.mem_append_right L hn
    obtain ⟨hb1, hb2⟩ := hLI_bound n hnLI
    rw [hnd_eq n hb1 hb2 8 (by simp), hnd_eq n hb1 hb2 16 (by simp)]
    exact hnroot n hn
  · intro n hn hnr
    obtain ⟨hb1, hb2⟩ := hLI_bound n hn
    rw [hnd_eq n hb1 hb2 0 (by simp)]
    exact hpI n hn hnr
  · obtain ⟨dep, hdep⟩ := hdep
    refine ⟨dep, fun n hn hnr => ?_⟩
    obtain ⟨hb1, hb2⟩ := hLI_bound n hn
    have hp_mem : nodeF s (hdr s t 5) n 0 ∈ L ++ I := List.mem_append_right L (hpI n hn hnr)
    obtain ⟨hpb1, hpb2⟩ := hLI_bound _ hp_mem
    rw [hnd_eq n hb1 hb2 0 (by simp), hnd_eq _ hpb1 hpb2 8 (by simp), hnd_eq _ hpb1 hpb2 16 (by simp)]
    exact hdep n hn hnr
  · exact (freeChain_congr_unhit hnd8 hnd_hi (hu _ hnd_fp) Fr (hdr s t 9)
      (fun f hf => by have := (hmem f).1 (List.mem_append_right (L ++ I) hf); omega)).2 hfc

theorem nodeHeap_congr_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgS : GuestInv s) (hgP : GuestInv post) (hbe : post.be = s.be)
    (hag : AllocatorGrows s post)
    {Nd : List Nat} (hN : NodeHeap s Nd)
    (hu : ∀ o ∈ nodeExtents s Nd, IvlUnhit s post o) :
    NodeHeap post Nd ∧ nodeExtents post Nd = nodeExtents s Nd := by
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have hn_props : ∀ n ∈ Nd,
      memW post n = memW s n ∧
      nodeIvl post n = nodeIvl s n ∧
      (∀ k, k < nodeSize (memW s n) / 8 → memW post (n + 8 * k) = memW s (n + 8 * k)) ∧
      nodePath post n = nodePath s n ∧
      ((memW s n = 1 ∨ memW s n = 2) → KeyIn post Nd (memW post (n + 32)) (memW post (n + 40))) := by
    intro n hn
    obtain ⟨hk3, hal_n, hin_n, hw_n, _, _, hkey_n, _, _, _⟩ := hN.1 n hn
    have hhi_n : n + nodeSize (memW s n) ≤ 2 ^ 64 := by
      have := hin_n.2; dsimp [nodeIvl] at this; omega
    have hn8 : n % 8 = 0 := hw_n.1
    have hu_n : IvlUnhit s post (n, nodeSize (memW s n)) := by
      apply hu; unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp [nodeIvl]⟩
    have hsz_ge32 : 32 ≤ nodeSize (memW s n) := by unfold nodeSize; split_ifs <;> omega
    have hw_k : ∀ k, k < nodeSize (memW s n) / 8 → memW post (n + 8 * k) = memW s (n + 8 * k) := by
      intro k hk
      have hsz8 : nodeSize (memW s n) % 8 = 0 := by unfold nodeSize; split_ifs <;> omega
      exact memW_eq_of_ivlUnhit hu_n (by omega) hhi_n ⟨by omega, by omega⟩
    have hw0 : memW post n = memW s n := by simpa using hw_k 0 (by omega)
    have hivl_eq : nodeIvl post n = nodeIvl s n := by simp [nodeIvl, hw0]
    have hpath_eq : nodePath post n = nodePath s n := by
      by_cases h12 : memW s n = 1 ∨ memW s n = 2
      · have hsz_ge56 : 56 ≤ nodeSize (memW s n) := by
          unfold nodeSize; rcases h12 with h1 | h2 <;> simp [*]
        have hw32 : memW post (n + 32) = memW s (n + 32) := hw_k 4 (by omega)
        have hw40 : memW post (n + 40) = memW s (n + 40) := hw_k 5 (by omega)
        unfold nodePath; rw [hw0, hw32, hw40]
      · unfold nodePath; rw [hw0]; simp [h12]
    exact ⟨hw0, hivl_eq, hw_k, hpath_eq, fun h12 => by
      have hsz_ge56 : 56 ≤ nodeSize (memW s n) := by
        unfold nodeSize; rcases h12 with h1 | h2 <;> simp [*]
      have hw32 : memW post (n + 32) = memW s (n + 32) := hw_k 4 (by omega)
      have hw40 : memW post (n + 40) = memW s (n + 40) := hw_k 5 (by omega)
      rw [hw32, hw40]
      by_cases hlen0 : memW s (n + 40) = 0
      · exact Or.inl hlen0
      · rcases hkey_n h12 with h0 | ⟨hnib, hal_p, hin_p, hdisj_p⟩
        · exact Or.inl h0
        · right
          have hu_p : IvlUnhit s post (memW s (n + 32), memW s (n + 40)) := by
            have hp_ext : (memW s (n + 32), memW s (n + 40)) ∈ nodeExtents s Nd := by
              unfold nodeExtents
              refine List.mem_flatMap.2 ⟨n, hn, ?_⟩
              simp [nodePath, h12, hlen0]
            exact hu _ hp_ext
          have hhi_p : memW s (n + 32) + memW s (n + 40) ≤ 2 ^ 64 := by
            have := hin_p.2; omega
          refine ⟨fun k hk => ?_, hag.allocated hal_p, hin_p, ?_⟩
          · rw [memB_eq_of_ivlUnhit hu_p hbe hhi_p ⟨by omega, by omega⟩]
            exact hnib k hk
          · intro m hm
            have hm_ivl : nodeIvl post m = nodeIvl s m := by
              have hhm_hi : m + nodeSize (memW s m) ≤ 2 ^ 64 := by
                have := (hN.1 m hm).2.2.1.2; dsimp [nodeIvl] at this; omega
              have hm8 : m % 8 = 0 := (hN.1 m hm).2.2.2.1.1
              have hu_m : IvlUnhit s post (m, nodeSize (memW s m)) := by
                apply hu; unfold nodeExtents; exact List.mem_flatMap.2 ⟨m, hm, by simp [nodeIvl]⟩
              have hsz_m : 32 ≤ nodeSize (memW s m) := by unfold nodeSize; split_ifs <;> omega
              have hwm : memW post m = memW s m :=
                memW_eq_of_ivlUnhit hu_m hm8 hhm_hi ⟨by omega, by omega⟩
              simp [nodeIvl, hwm]
            rw [hm_ivl]; exact hdisj_p m hm⟩
  constructor
  · refine ⟨fun n hn => ?_, fun n hn m hm hne => ?_⟩
    · obtain ⟨hk3, hal_n, hin_n, hw_n, hext, hbr, _, h16_lt, hpay1, hpay3⟩ := hN.1 n hn
      obtain ⟨hw0, hivl_eq, hw_k, _, hkey_post⟩ := hn_props n hn
      rw [hw0, hivl_eq]
      have hsz_ge32 : 32 ≤ nodeSize (memW s n) := by unfold nodeSize; split_ifs <;> omega
      have hw16 := hw_k 2 (by omega)
      refine ⟨hk3, hag.allocated hal_n, hin_n, wordsOK_transfer hgS hgP hw_n,
        ?_, ?_, hkey_post, ?_, ?_, ?_⟩
      · intro h2
        have hsz : nodeSize (memW s n) = 56 := by unfold nodeSize; simp [h2]
        have hw48 := hw_k 6 (by omega)
        have hmul48 : n + 8 * 6 = n + 48 := by omega
        rw [← hmul48, hw48, hmul48]; exact hext h2
      · intro h3 i hi
        have hsz : nodeSize (memW s n) = 176 := by unfold nodeSize; simp [h3]
        have hw_ch := hw_k (4 + i) (by omega)
        have hadd : n + 8 * (4 + i) = n + 32 + 8 * i := by omega
        rw [← hadd, hw_ch, hadd]; exact hbr h3 i hi
      · have hmul16 : n + 8 * 2 = n + 16 := by omega
        rw [← hmul16, hw16, hmul16]; exact h16_lt
      · intro h1
        have hsz : nodeSize (memW s n) = 64 := by unfold nodeSize; simp [h1]
        have hw56 := hw_k 7 (by omega)
        have hmul56 : n + 8 * 7 = n + 56 := by omega
        rw [← hmul56, hw56, hmul56]; exact hpay1 h1
      · intro h3
        have hsz : nodeSize (memW s n) = 176 := by unfold nodeSize; simp [h3]
        have hw168 := hw_k 21 (by omega)
        have hmul168 : n + 8 * 21 = n + 168 := by omega
        rw [← hmul168, hw168, hmul168]; exact hpay3 h3
    · rw [(hn_props n hn).2.1, (hn_props m hm).2.1]
      exact hN.2 n hn m hm hne
  · unfold nodeExtents
    apply List.flatMap_congr
    intro n hn
    rw [(hn_props n hn).2.1, (hn_props n hn).2.2.2.1]

theorem typedRecord_mem_globalBuffers {r : String × Nat} (hr : r ∈ typedRecords) :
    r ∈ globalBuffers := by
  simp only [typedRecords, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> decide

theorem typedRecord_mem_fixedObjects {F : Type} (s : PanSemStateFiniteExact 64 F)
    {r : String × Nat} (hr : r ∈ typedRecords) :
    (globN s r.1, if globN s r.1 = 0 then 0 else r.2) ∈ fixedObjects s := by
  unfold fixedObjects
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  exact List.mem_map.2 ⟨r, typedRecord_mem_globalBuffers hr, rfl⟩

theorem bo_words {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hF : FixedTyped s) (hn : globN s "bo" ≠ 0) :
    Allocated s (globN s "bo", 88) ∧ WordsOK s (globN s "bo", 88) := by
  have hm := typedRecord_mem_fixedObjects s (r := ("bo", 88)) (by decide)
  simp only [hn, ↓reduceIte] at hm
  exact (hF.1 _ hm).resolve_left (by simp)

theorem rec_word_eq_of_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) (hF : FixedTyped s)
    (g : String) (sz : Nat) (hrec : (g, sz) ∈ typedRecords)
    (hg_eq : globN post g = globN s g) (hgnz : globN s g ≠ 0)
    (hu : IvlUnhit s post (globN s g, sz))
    {k : Nat} (hk8 : k % 8 = 0) (hksz : k + 8 ≤ sz) :
    memW post (globN post g + k) = memW s (globN s g + k) := by
  rw [hg_eq]
  have hmem_fix := typedRecord_mem_fixedObjects s hrec
  simp only [hgnz, ↓reduceIte] at hmem_fix
  rcases hF.1 _ hmem_fix with h0 | ⟨hal, hwords⟩
  · dsimp only at h0; omega
  · have hhi := (ivl_allocated_bound hA hal).2
    have hg8 : (globN s g) % 8 = 0 := hwords.1
    exact memW_eq_of_ivlUnhit hu (by omega) hhi ⟨by omega, by omega⟩

theorem blockOutObjects_eq_of_bo_same {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) (hF : FixedTyped s) (hbo_eq : globN post "bo" = globN s "bo")
    (hbo_lst_ok : globN s "bo" ≠ 0 → ∀ k ∈ ([40, 72] : List Nat), memW s (globN s "bo" + k) ≠ 0 →
      LstOK s (memW s (globN s "bo" + k)))
    (hk : globN s "bo" ≠ 0 → ∀ k ∈ ([24, 32, 40, 56, 72, 80] : List Nat),
      memW post (globN s "bo" + k) = memW s (globN s "bo" + k))
    (hl40 : globN s "bo" ≠ 0 → memW s (globN s "bo" + 40) ≠ 0 →
      IvlUnhit s post (memW s (globN s "bo" + 40), 24))
    (hl72 : globN s "bo" ≠ 0 → memW s (globN s "bo" + 72) ≠ 0 →
      IvlUnhit s post (memW s (globN s "bo" + 72), 24)) :
    blockOutObjects post = blockOutObjects s ∧
    (globN post "bo" ≠ 0 → ∀ k ∈ ([40, 72] : List Nat), memW post (globN post "bo" + k) ≠ 0 →
      LstOK post (memW post (globN post "bo" + k))) := by
  by_cases hbo : globN s "bo" = 0
  · refine ⟨by simp [blockOutObjects, hbo_eq, hbo], fun hp => absurd (hbo_eq.trans hbo) hp⟩
  · have hlst_hdr : ∀ k ∈ ([40, 72] : List Nat), memW s (globN s "bo" + k) ≠ 0 →
        ∀ off ∈ ([0, 8, 16] : List Nat),
          memW post (memW s (globN s "bo" + k) + off) = memW s (memW s (globN s "bo" + k) + off) := by
      intro k hk_in hknz off hoff
      have hmem_bo : (memW s (globN s "bo" + k), 24) ∈ blockOutObjects s := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk_in
        rcases hk_in with rfl | rfl <;> simp [blockOutObjects, hbo, hknz]
      have hmem_fix : (memW s (globN s "bo" + k), 24) ∈ fixedObjects s := by
        unfold fixedObjects; apply List.mem_append_left; apply List.mem_append_right; exact hmem_bo
      rcases hF.1 _ hmem_fix with h0 | ⟨hal, hwords⟩
      · simp at h0
      · have hhi := (ivl_allocated_bound hA hal).2
        have hp8 : (memW s (globN s "bo" + k)) % 8 = 0 := hwords.1
        have hu : IvlUnhit s post (memW s (globN s "bo" + k), 24) := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hk_in
          rcases hk_in with rfl | rfl
          · exact hl40 hbo hknz
          · exact hl72 hbo hknz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
        rcases hoff with rfl | rfl | rfl <;>
          exact memW_eq_of_ivlUnhit hu (by omega) hhi ⟨by omega, by omega⟩
    constructor
    · unfold blockOutObjects
      simp only [hbo_eq, hbo, false_or,
        hk hbo 24 (by simp), hk hbo 32 (by simp), hk hbo 40 (by simp),
        hk hbo 56 (by simp), hk hbo 72 (by simp), hk hbo 80 (by simp)]
      congr 1; congr 1
      · by_cases h40 : memW s (globN s "bo" + 40) = 0
        · simp [h40]
        · have h0 := hlst_hdr 40 (by simp) h40 0 (by simp); simp only [Nat.add_zero] at h0
          have h16 := hlst_hdr 40 (by simp) h40 16 (by simp)
          simp [h40, h0, h16]
      · by_cases h72 : memW s (globN s "bo" + 72) = 0
        · simp [h72]
        · have h0 := hlst_hdr 72 (by simp) h72 0 (by simp); simp only [Nat.add_zero] at h0
          have h16 := hlst_hdr 72 (by simp) h72 16 (by simp)
          simp [h72, h0, h16]
    · intro _ k hk_in hknz
      rw [hbo_eq] at hknz ⊢
      rw [hk hbo k (by simp at hk_in; rcases hk_in with rfl | rfl <;> simp)] at hknz ⊢
      unfold LstOK
      rw [hlst_hdr k hk_in hknz 8 (by simp), hlst_hdr k hk_in hknz 16 (by simp)]
      exact hbo_lst_ok hbo k hk_in hknz

theorem balObjects_eq_of_same_globals {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) {S : List Nat} (hT : TablesTyped s S) (hF : FixedTyped s)
    (hba_eq : globN post "bal_accounts" = globN s "bal_accounts")
    (hm_low : memW post 8 = memW s 8 ∧ memW post 16 = memW s 16)
    (hu_tab : ∀ t ∈ S, ∀ i ∈ htabFootprint s t, IvlUnhit s post i)
    (hu_bal : ∀ i ∈ balObjects s, IvlUnhit s post i) :
    balRecords post = balRecords s ∧
    balObjects post = balObjects s ∧
    (∀ ad ∈ balRecords post, memW post ad = memW s ad ∧ memW post (ad + 8) = memW s (ad + 8) ∧
      htabValues post (memW post ad) = htabValues s (memW s ad) ∧
      (∀ k ∈ ([16, 24, 32] : List Nat), LstOK post (memW post (ad + k))) ∧
      (∀ l ∈ htabValues post (memW post ad), LstOK post l)) := by
  have hrecs : balRecords post = balRecords s := by
    unfold balRecords
    rw [hba_eq]
    by_cases hbal : globN s "bal_accounts" = 0
    · simp [hbal]
    · simp only [hbal, ↓reduceIte]
      rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by decide) with h0 | hm
      · exact absurd h0 hbal
      · exact htabValues_eq_of_unhit (hT.2.1 _ hm).1 (hu_tab _ hm)
  have hmem_fix_of_bal : ∀ i ∈ balObjects s, i ∈ fixedObjects s :=
    fun _ hi => List.mem_append_right _ hi
  have had_props : ∀ ad ∈ balRecords s,
      (∀ off ∈ ([0, 8, 16, 24, 32] : List Nat), memW post (ad + off) = memW s (ad + off)) ∧
      htabValues post (memW s ad) = htabValues s (memW s ad) ∧
      (∀ k ∈ ([16, 24, 32] : List Nat), memW s (ad + k) ≠ 0 →
        memW post (memW s (ad + k)) = memW s (memW s (ad + k)) ∧
        memW post (memW s (ad + k) + 8) = memW s (memW s (ad + k) + 8) ∧
        memW post (memW s (ad + k) + 16) = memW s (memW s (ad + k) + 16)) ∧
      (∀ l ∈ htabValues s (memW s ad), l ≠ 0 →
        memW post l = memW s l ∧ memW post (l + 8) = memW s (l + 8) ∧ memW post (l + 16) = memW s (l + 16)) := by
    intro ad had
    have had_bal : (ad, 40) ∈ balObjects s :=
      List.mem_flatMap.2 ⟨ad, had, by simp⟩
    rcases hF.1 _ (hmem_fix_of_bal _ had_bal) with h0 | ⟨hal_ad, hw_ad⟩
    · simp at h0
    have hhi_ad := (ivl_allocated_bound hA hal_ad).2
    have had8 : ad % 8 = 0 := hw_ad.1
    have hoff_eq : ∀ off ∈ ([0, 8, 16, 24, 32] : List Nat), memW post (ad + off) = memW s (ad + off) := by
      intro off hoff
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      rcases hoff with rfl | rfl | rfl | rfl | rfl <;>
        exact memW_eq_of_ivlUnhit (hu_bal _ had_bal) (by omega) hhi_ad ⟨by omega, by omega⟩
    have had_T := hT.2.2.2.2.2.2.2.2.2.1 ad had
    have hvals_ad : htabValues post (memW s ad) = htabValues s (memW s ad) :=
      htabValues_eq_of_unhit (hT.2.1 _ had_T.1).1 (hu_tab _ had_T.1)
    have hlst_eq : ∀ l, (l, 24) ∈ balObjects s →
        memW post l = memW s l ∧ memW post (l + 8) = memW s (l + 8) ∧ memW post (l + 16) = memW s (l + 16) := by
      intro l hl_bal
      rcases hF.1 _ (hmem_fix_of_bal _ hl_bal) with h0 | ⟨hal_l, hw_l⟩
      · simp at h0
      have hhi_l := (ivl_allocated_bound hA hal_l).2
      have hl8 : l % 8 = 0 := hw_l.1
      have hul := hu_bal _ hl_bal
      exact ⟨by simpa using memW_eq_of_ivlUnhit hul (by omega) hhi_l ⟨by omega, by omega⟩,
        memW_eq_of_ivlUnhit hul (by omega) hhi_l ⟨by omega, by omega⟩,
        memW_eq_of_ivlUnhit hul (by omega) hhi_l ⟨by omega, by omega⟩⟩
    refine ⟨hoff_eq, hvals_ad, ?_, ?_⟩
    · intro k hk hknz
      apply hlst_eq
      refine List.mem_flatMap.2 ⟨ad, had, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl <;> simp [lstObjects, hknz]
    · intro l hl hlnz
      apply hlst_eq
      refine List.mem_flatMap.2 ⟨ad, had, ?_⟩
      apply List.mem_cons_of_mem; apply List.mem_append_right
      exact List.mem_flatMap.2 ⟨l, hl, by simp [lstObjects, hlnz]⟩
  refine ⟨hrecs, ?_, ?_⟩
  · unfold balObjects
    rw [hrecs]
    apply List.flatMap_congr
    intro ad had
    obtain ⟨hoff_eq, hvals_ad, hklst, hllst⟩ := had_props ad had
    have h0 := hoff_eq 0 (by simp); simp only [Nat.add_zero] at h0
    have h16 := hoff_eq 16 (by simp)
    have h24 := hoff_eq 24 (by simp)
    have h32 := hoff_eq 32 (by simp)
    have hkl_obj : ∀ (k esz : Nat), k ∈ ([16, 24, 32] : List Nat) →
        lstObjects post (memW s (ad + k)) esz = lstObjects s (memW s (ad + k)) esz := by
      intro k esz hk
      by_cases hkz : memW s (ad + k) = 0
      · simp [lstObjects, hkz]
      · obtain ⟨e0, _, e16⟩ := hklst k hk hkz
        simp [lstObjects, hkz, e0, e16]
    have htail : (htabValues post (memW post ad)).flatMap (fun l => lstObjects post l 40) =
        (htabValues s (memW s ad)).flatMap (fun l => lstObjects s l 40) := by
      rw [h0, hvals_ad]
      apply List.flatMap_congr
      intro l hl
      by_cases hlz : l = 0
      · simp [lstObjects, hlz]
      · obtain ⟨e0, _, e16⟩ := hllst l hl hlz
        simp [lstObjects, hlz, e0, e16]
    rw [htail, h16, h24, h32, hkl_obj 16 40 (by simp), hkl_obj 24 16 (by simp), hkl_obj 32 24 (by simp)]
  · intro ad had
    rw [hrecs] at had
    obtain ⟨hoff_eq, hvals_ad, hklst, hllst⟩ := had_props ad had
    have had_T := hT.2.2.2.2.2.2.2.2.2.1 ad had
    have h0 := hoff_eq 0 (by simp); simp only [Nat.add_zero] at h0
    have h8 := hoff_eq 8 (by simp)
    refine ⟨h0, h8, by rw [h0, hvals_ad], ?_, ?_⟩
    · intro k hk
      have hk_in : k ∈ ([0, 8, 16, 24, 32] : List Nat) := by
        simp at hk; rcases hk with rfl | rfl | rfl <;> simp
      rw [hoff_eq k hk_in]
      by_cases hkz : memW s (ad + k) = 0
      · have hck := had_T.2.2.1 k hk
        unfold LstOK at hck ⊢
        rw [hkz] at hck ⊢
        simpa [hm_low.1, hm_low.2] using hck
      · obtain ⟨_, e8, e16⟩ := hklst k hk hkz
        unfold LstOK; rw [e8, e16]; exact had_T.2.2.1 k hk
    · intro l hl
      rw [h0, hvals_ad] at hl
      by_cases hlz : l = 0
      · subst hlz
        have hcl := had_T.2.2.2 0 hl
        unfold LstOK at hcl ⊢
        simpa [hm_low.1, hm_low.2] using hcl
      · obtain ⟨_, e8, e16⟩ := hllst l hl hlz
        unfold LstOK; rw [e8, e16]; exact had_T.2.2.2 l hl

theorem worldTypedWith_congr_same_globals {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaReady s) (hAp : ArenaReady post) (hbe : post.be = s.be)
    (hag : AllocatorGrows s post) (hglobs : post.globals = s.globals)
    {S Nd : List Nat} (hW : WorldTypedWith s S Nd)
    (hu_tab : ∀ t ∈ S, ∀ i ∈ htabFootprint s t, IvlUnhit s post i)
    (hu_ws : globN s "ws" ≠ 0 → IvlUnhit s post (globN s "ws", 40))
    (hu_bs : globN s "bs" ≠ 0 → IvlUnhit s post (globN s "bs", 80))
    (hu_ts : globN s "ts" ≠ 0 → IvlUnhit s post (globN s "ts", 72))
    (hu_jr : globN s "journal_cap" ≠ 0 → IvlUnhit s post (globN s "journal", 32 * globN s "journal_cap"))
    (hu_l40 : globN s "bo" ≠ 0 → memW s (globN s "bo" + 40) ≠ 0 → IvlUnhit s post (memW s (globN s "bo" + 40), 24))
    (hu_l72 : globN s "bo" ≠ 0 → memW s (globN s "bo" + 72) ≠ 0 → IvlUnhit s post (memW s (globN s "bo" + 72), 24))
    (hu_bal : ∀ i ∈ balObjects s, IvlUnhit s post i)
    (hu_nd : ∀ o ∈ nodeExtents s Nd, IvlUnhit s post o)
    (hbo_words : globN s "bo" ≠ 0 → ∀ k ∈ ([24, 32, 40, 56, 72, 80] : List Nat),
      memW post (globN s "bo" + k) = memW s (globN s "bo" + k))
    (hm_low : memW post 8 = memW s 8 ∧ memW post 16 = memW s 16) :
    WorldTypedWith post S Nd ∧
    worldOwned post S Nd = worldOwned s S Nd := by
  obtain ⟨hT, hJ, hF, hTr⟩ := hW
  have hg_all : ∀ name, globN post name = globN s name := fun name => by simp [globN, hglobs]
  have hbo_part := blockOutObjects_eq_of_bo_same hAs.2 hF (hg_all "bo") hT.2.2.2.2.2.2.2.2.2.2.1
    hbo_words hu_l40 hu_l72
  have hbal_part := balObjects_eq_of_same_globals hAs.2 hT hF (hg_all "bal_accounts") hm_low hu_tab hu_bal
  have hfix_eq : fixedObjects post = fixedObjects s := by
    unfold fixedObjects
    rw [hbo_part.1, hbal_part.2.1, hg_all "journal", hg_all "journal_cap"]
    congr 3
    apply List.map_congr_left
    intro gn _
    rw [hg_all gn.1]
  have hF_post : FixedTyped post := by
    unfold FixedTyped
    rw [hfix_eq]
    refine ⟨fun i hi => ?_, hF.2⟩
    rcases hF.1 i hi with h0 | ⟨hal, hwords⟩
    · exact Or.inl h0
    · exact Or.inr ⟨hag.allocated hal, wordsOK_transfer hAs.1 hAp.1 hwords⟩
  have hrole_jr_eq : ∀ t, journalRole post t = journalRole s t := fun t => by
    unfold journalRole
    by_cases h : globN s "ts" = 0
    · simp [hg_all "ts", h]
    · have hw16 := rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by decide) (hg_all "ts") h (hu_ts h) (k := 16) (by omega) (by omega)
      have hw32 := rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by decide) (hg_all "ts") h (hu_ts h) (k := 32) (by omega) (by omega)
      have hw48 := rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by decide) (hg_all "ts") h (hu_ts h) (k := 48) (by omega) (by omega)
      have hw64 := rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by decide) (hg_all "ts") h (hu_ts h) (k := 64) (by omega) (by omega)
      simp only [hg_all "ts"] at hw16 hw32 hw48 hw64 ⊢
      rw [hw16, hw32, hw48, hw64]
  have hj_cells : ∀ i, i < globN s "journal_n" →
      memW post (globN s "journal" + 32 * i) = memW s (globN s "journal" + 32 * i) ∧
      memW post (globN s "journal" + 32 * i + 16) = memW s (globN s "journal" + 32 * i + 16) ∧
      memW post (globN s "journal" + 32 * i + 24) = memW s (globN s "journal" + 32 * i + 24) := by
    intro i hi
    have hcnz : globN s "journal_cap" ≠ 0 := by have := hJ.1; omega
    rcases hJ.2.2.1 with h0 | ⟨hal, hwords⟩
    · exact absurd h0 hcnz
    · have hhi := (ivl_allocated_bound hAs.2 hal).2
      have hj8 : (globN s "journal") % 8 = 0 := hwords.1
      have huj := hu_jr hcnz
      have hle : i < globN s "journal_cap" := lt_of_lt_of_le hi hJ.1
      exact ⟨memW_eq_of_ivlUnhit huj (by omega) hhi ⟨by omega, by omega⟩,
        memW_eq_of_ivlUnhit huj (by omega) hhi ⟨by omega, by omega⟩,
        memW_eq_of_ivlUnhit huj (by omega) hhi ⟨by omega, by omega⟩⟩
  have hjrs_eq : journalRoleSlots post = journalRoleSlots s := by
    unfold journalRoleSlots
    rw [hg_all "journal_n", hg_all "journal"]
    apply List.flatMap_congr
    intro i hi
    rw [List.mem_range] at hi
    obtain ⟨hc0, hc16, hc24⟩ := hj_cells i hi
    simp only [hc0, hc16, hc24, hrole_jr_eq]
  have hJ_post : JournalTyped post S := by
    unfold JournalTyped
    rw [hg_all "journal_n", hg_all "journal_cap", hg_all "journal"]
    refine ⟨hJ.1, hJ.2.1, ?_, fun i hi => ?_⟩
    · rcases hJ.2.2.1 with h0 | ⟨hal, hwords⟩
      · exact Or.inl h0
      · exact Or.inr ⟨hag.allocated hal, wordsOK_transfer hAs.1 hAp.1 hwords⟩
    · rw [(hj_cells i hi).1]; exact hJ.2.2.2 i hi
  have hwrs_eq : worldRoleSlots post = worldRoleSlots s := by
    have hrec_ws : recRoles post "ws" [(16, "ws+16"), (32, "ws+32")] =
        recRoles s "ws" [(16, "ws+16"), (32, "ws+32")] := by
      unfold recRoles
      by_cases h : globN s "ws" = 0
      · simp [hg_all "ws", h]
      · have hw32 := rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by decide) (hg_all "ws") h (hu_ws h) (k := 32) (by omega) (by omega)
        have hw16 := rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by decide) (hg_all "ws") h (hu_ws h) (k := 16) (by omega) (by omega)
        simp only [hg_all "ws"] at hw32 hw16 ⊢
        simp [h, hw32, hw16]
    have hrec_bs : recRoles post "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
        (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] =
        recRoles s "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
        (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] := by
      unfold recRoles
      by_cases h : globN s "bs" = 0
      · simp [hg_all "bs", h]
      · simp only [hg_all "bs", h, ↓reduceIte]
        apply List.map_congr_left
        intro ⟨k, r⟩ hkr
        have hk : k % 8 = 0 ∧ k + 8 ≤ 80 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
          rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
        have hw := rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by decide) (hg_all "bs") h (hu_bs h) hk.1 hk.2
        simp only [hg_all "bs"] at hw; simp [hw]
    have hrec_ts : recRoles post "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
        (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] =
        recRoles s "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
        (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] := by
      unfold recRoles
      by_cases h : globN s "ts" = 0
      · simp [hg_all "ts", h]
      · simp only [hg_all "ts", h, ↓reduceIte]
        apply List.map_congr_left
        intro ⟨k, r⟩ hkr
        have hk : k % 8 = 0 ∧ k + 8 ≤ 72 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
          rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
        have hw := rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by decide) (hg_all "ts") h (hu_ts h) hk.1 hk.2
        simp only [hg_all "ts"] at hw; simp [hw]
    have hnest_bs : nestRoles post "bs" "bs.inner" = nestRoles s "bs" "bs.inner" := by
      unfold nestRoles
      by_cases h : globN s "bs" = 0
      · simp [hg_all "bs", h]
      · have hw32 := rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by decide) (hg_all "bs") h (hu_bs h) (k := 32) (by omega) (by omega)
        simp only [hg_all "bs"] at hw32 ⊢
        simp only [h, ↓reduceIte, hw32]
        by_cases h32 : memW s (globN s "bs" + 32) = 0
        · simp [h32]
        · simp only [h32, ↓reduceIte]
          rcases hT.2.2.2.2.1 32 (by decide) h with h0 | hmS
          · exact absurd h0 h32
          · rw [htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_tab _ hmS)]
    have hnest_ts : nestRoles post "ts" "ts.inner" = nestRoles s "ts" "ts.inner" := by
      unfold nestRoles
      by_cases h : globN s "ts" = 0
      · simp [hg_all "ts", h]
      · have hw32 := rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by decide) (hg_all "ts") h (hu_ts h) (k := 32) (by omega) (by omega)
        simp only [hg_all "ts"] at hw32 ⊢
        simp only [h, ↓reduceIte, hw32]
        by_cases h32 : memW s (globN s "ts" + 32) = 0
        · simp [h32]
        · simp only [h32, ↓reduceIte]
          rcases hT.2.2.2.2.2.1 32 (by decide) h with h0 | hmS
          · exact absurd h0 h32
          · rw [htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_tab _ hmS)]
    unfold worldRoleSlots
    rw [hrec_ws, hrec_bs, hrec_ts, hg_all "bal_accounts", hg_all "bal_idx_accts", hg_all "bal_idx_stor",
      hnest_bs, hnest_ts, hbal_part.1]
    congr 1; congr 1
    apply List.flatMap_congr
    intro ad had
    rw [← hbal_part.1] at had
    obtain ⟨h0, h8, _⟩ := hbal_part.2.2 ad had
    rw [h0, h8]
  have hnd_part := nodeHeap_congr_unhit hAs.1 hAp.1 hbe hag hTr.1 hu_nd
  have htab_fp_hdr : ∀ t ∈ S, (∀ k, k < 11 → hdr post t k = hdr s t k) ∧ htabFootprint post t = htabFootprint s t := by
    intro t ht
    have hwf := (hT.2.1 t ht).1
    have ht_fp : (t, 88) ∈ htabFootprint s t := by simp [htabFootprint]
    have ht8 : t % 8 = 0 := (hwf.1 _ ht_fp).2.1
    have hhi : t + 88 ≤ 2 ^ 64 := by
      have h1 := (hwf.1 _ ht_fp).1.2; dsimp only at h1
      have h2 : heapEnd ≤ 2 ^ 64 := by decide
      omega
    exact htabFootprint_eq_of_hdr_unhit ht8 hhi (hu_tab t ht _ ht_fp)
  have hflat_fp : S.flatMap (htabFootprint post) = S.flatMap (htabFootprint s) := by
    apply List.flatMap_congr
    intro t ht; exact (htab_fp_hdr t ht).2
  have howned_eq : worldOwned post S Nd = worldOwned s S Nd := by
    unfold worldOwned; rw [hflat_fp, hfix_eq, hnd_part.2]
  have hT_post : TablesTyped post S := by
    obtain ⟨hndS, hTt, hTp, hwsR, hbsR, htsR, hgR, hbsN, htsN, hbalT, _, hroles⟩ := hT
    refine ⟨hndS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbo_part.2, ?_⟩
    · intro t ht
      rw [(htab_fp_hdr t ht).2, hfix_eq]
      exact ⟨htabWF_congr_unhit hAs.1 hAp.1 (hTt t ht).1 (hu_tab t ht),
        fun i hi => ⟨hag.allocated ((hTt t ht).2 i hi).1, ((hTt t ht).2 i hi).2⟩⟩
    · intro t ht u hu_mem hne
      rw [(htab_fp_hdr t ht).2, (htab_fp_hdr u hu_mem).2]
      exact hTp t ht u hu_mem hne
    · intro k hk hnz
      rw [hg_all "ws"] at hnz
      have hwk : k % 8 = 0 ∧ k + 8 ≤ 40 := by
        simp [wsTableSlots] at hk; rcases hk with rfl | rfl <;> omega
      rw [rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by decide) (hg_all "ws") hnz (hu_ws hnz) hwk.1 hwk.2]
      exact hwsR k hk hnz
    · intro k hk hnz
      rw [hg_all "bs"] at hnz
      have hbk : k % 8 = 0 ∧ k + 8 ≤ 80 := by
        simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by decide) (hg_all "bs") hnz (hu_bs hnz) hbk.1 hbk.2]
      exact hbsR k hk hnz
    · intro k hk hnz
      rw [hg_all "ts"] at hnz
      have htk : k % 8 = 0 ∧ k + 8 ≤ 72 := by
        simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by decide) (hg_all "ts") hnz (hu_ts hnz) htk.1 htk.2]
      exact htsR k hk hnz
    · intro g hg; rw [hg_all g]; exact hgR g hg
    · intro hnz hm
      rw [hg_all "bs"] at hnz
      have hw32 := rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by decide) (hg_all "bs") hnz (hu_bs hnz) (k := 32) (by omega) (by omega)
      rw [hw32] at hm ⊢
      exact htabValuesIn_congr_unhit (hTt _ hm).1 (hu_tab _ hm) (fun _ hx => hx) (hbsN hnz hm)
    · intro hnz hm
      rw [hg_all "ts"] at hnz
      have hw32 := rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by decide) (hg_all "ts") hnz (hu_ts hnz) (k := 32) (by omega) (by omega)
      rw [hw32] at hm ⊢
      exact htabValuesIn_congr_unhit (hTt _ hm).1 (hu_tab _ hm) (fun _ hx => hx) (htsN hnz hm)
    · intro ad had
      obtain ⟨h0, h8, _, hkl, hll⟩ := hbal_part.2.2 ad had
      rw [hbal_part.1] at had
      have had_old := hbalT ad had
      exact ⟨by rw [h0]; exact had_old.1, by rw [h8]; exact had_old.2.1, hkl, hll⟩
    · unfold RolesOK at hroles ⊢
      rw [hwrs_eq, hjrs_eq]
      refine ⟨fun a ha => ?_, hroles.2.1, hroles.2.2⟩
      obtain ⟨haS, hak⟩ := hroles.1 a ha
      rw [(htab_fp_hdr a.1 haS).1 0 (by omega)]
      exact ⟨haS, hak⟩
  have hTr_post : TriesTypedWith post S Nd := by
    refine ⟨hnd_part.1, ?_, ?_⟩
    · intro o ho
      rw [hnd_part.2] at ho
      rw [hfix_eq]
      refine ⟨fun t ht i hi => ?_, (hTr.2.1 o ho).2⟩
      rw [(htab_fp_hdr t ht).2] at hi
      exact (hTr.2.1 o ho).1 t ht i hi
    · intro hnz
      rw [hg_all "ws"] at hnz
      have hw24 := rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by decide) (hg_all "ws") hnz (hu_ws hnz) (k := 24) (by omega) (by omega)
      have hw32 := rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by decide) (hg_all "ws") hnz (hu_ws hnz) (k := 32) (by omega) (by omega)
      rw [hw24, hw32]
      obtain ⟨hr24, hr32⟩ := hTr.2.2 hnz
      refine ⟨hr24, fun hm i hi => ?_⟩
      have hwf32 := (hT.2.1 _ hm).1
      have hu32 := hu_tab _ hm
      have hh32 := htab_fp_hdr _ hm
      rw [hh32.1 3 (by omega)] at hi
      have hvals := htabValues_eq_of_unhit hwf32 hu32
      have hget : (htabValues post (memW s (globN s "ws" + 32)))[i]? =
          (htabValues s (memW s (globN s "ws" + 32)))[i]? := by rw [hvals]
      simp only [htabValues, List.getElem?_map, List.getElem?_range, hh32.1 3 (by omega), hi,
        Option.map_some, Option.some.injEq] at hget
      rw [hget]
      exact hr32 hm i hi
  exact ⟨⟨hT_post, hJ_post, hF_post, hTr_post⟩, howned_eq⟩

/-! ## 7. Single-Cell Store & `LogsListOK` / `TxWorld` Preservation Lemmas -/

/-- Store to a single aligned in-domain cell `x` inside an untyped `bo` word (`0, 8, 16, 48`),
inside the `bo+32` receipt array, inside the `bo+40` or `bo+72` backing array, or inside a
caller-owned fresh heap block disjoint from `worldOwned s S Nd` preserves `WorldTypedWith`,
`worldOwned`, and `TxEnv`! -/
theorem worldTypedWith_single_store_of_disj {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaReady s) (hE : TxEnv s) {S Nd : List Nat} (hW : WorldTypedWith s S Nd)
    {x : BitVec 64} (hx : s.memaddrs x)
    (htab_d : ∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj i (x.toNat, 8))
    (hws_d : globN s "ws" ≠ 0 → Disj (globN s "ws", 40) (x.toNat, 8))
    (hbs_d : globN s "bs" ≠ 0 → Disj (globN s "bs", 80) (x.toNat, 8))
    (hts_d : globN s "ts" ≠ 0 → Disj (globN s "ts", 72) (x.toNat, 8))
    (hjr_d : globN s "journal_cap" ≠ 0 → Disj (globN s "journal", 32 * globN s "journal_cap") (x.toNat, 8))
    (hl40_d : Disj (memW s (globN s "bo" + 40), 24) (x.toNat, 8))
    (hl72_d : Disj (memW s (globN s "bo" + 72), 24) (x.toNat, 8))
    (hbal_d : ∀ i ∈ balObjects s, Disj i (x.toNat, 8))
    (hnd_d : ∀ o ∈ nodeExtents s Nd, Disj o (x.toNat, 8))
    (hbo_typed_ne : ∀ k ∈ ([24, 32, 40, 56, 72, 80] : List Nat), BitVec.ofNat 64 (globN s "bo" + k) ≠ x)
    {mem' : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem' a = s.memory a) :
    WorldTypedWith {s with memory := mem'} S Nd ∧
    worldOwned {s with memory := mem'} S Nd = worldOwned s S Nd ∧
    TxEnv {s with memory := mem'} := by
  let post : PanSemStateFiniteExact 64 F := {s with memory := mem'}
  have hAp : ArenaReady post := ⟨guestInv_congr (s := s) rfl rfl rfl rfl hA.1, hA.2⟩
  have hlo : sourceBase ≤ x.toNat := ((ordinaryDomain_iff x).mp (hA.1.memaddrs ▸ hx)).2.1
  have hsb : 16 < sourceBase := by decide
  have hm_low : memW post 8 = memW s 8 ∧ memW post 16 = memW s 16 := by
    constructor
    · unfold memW
      rw [show post.memory (BitVec.ofNat 64 8) = s.memory (BitVec.ofNat 64 8) from hm _ (by
        intro he; have := congrArg BitVec.toNat he; norm_num at this; omega)]
    · unfold memW
      rw [show post.memory (BitVec.ofNat 64 16) = s.memory (BitVec.ofNat 64 16) from hm _ (by
        intro he; have := congrArg BitVec.toNat he; norm_num at this; omega)]
  have hboW : ∀ k ∈ ([24, 32, 40, 56, 72, 80] : List Nat),
      memW post (globN s "bo" + k) = memW s (globN s "bo" + k) := by
    intro k hk
    unfold memW
    rw [show post.memory (BitVec.ofNat 64 (globN s "bo" + k)) = s.memory (BitVec.ofNat 64 (globN s "bo" + k))
      from hm _ (hbo_typed_ne k hk)]
  have hw := worldTypedWith_congr_same_globals hA hAp rfl ⟨le_rfl, le_rfl⟩ rfl hW
    (fun t ht i hi => ivlUnhit_single hm (fun hz => ((hW.1.2.1 t ht).1.1 i hi).2.1) (htab_d t ht i hi))
    (fun hn => ivlUnhit_single hm (by simp) (hws_d hn))
    (fun hn => ivlUnhit_single hm (by simp) (hbs_d hn))
    (fun hn => ivlUnhit_single hm (by simp) (hts_d hn))
    (fun hn => ivlUnhit_single hm (fun hz => by dsimp at hz; omega) (hjr_d hn))
    (fun _ _ => ivlUnhit_single hm (by simp) hl40_d)
    (fun _ _ => ivlUnhit_single hm (by simp) hl72_d)
    (fun i hi => ivlUnhit_single hm (fun hz => by
      have h0 := fixedObjects_zero_aligned i (List.mem_append_right _ hi) hz; simp [h0]) (hbal_d i hi))
    (fun o ho => ivlUnhit_single hm (worldOwned_zero_aligned hW o (List.mem_append_right _ ho)) (hnd_d o ho))
    (fun _ k hk => hboW k hk)
    hm_low
  refine ⟨hw.1, hw.2, ?_⟩
  exact ⟨hE.bo_nz,
    by change memW post (globN s "bo" + 24) ≠ 0; rw [hboW 24 (by simp)]; exact hE.bo24,
    by change memW post (globN s "bo" + 32) ≠ 0; rw [hboW 32 (by simp)]; exact hE.bo32,
    by change memW post (globN s "bo" + 40) ≠ 0; rw [hboW 40 (by simp)]; exact hE.bo40,
    by change memW post (globN s "bo" + 72) ≠ 0; rw [hboW 72 (by simp)]; exact hE.bo72,
    by change locN s "index" < memW post (globN s "bo" + 80); rw [hboW 80 (by simp)]; exact hE.idx_lt,
    hE.jcap_nz⟩

/-- Helper: pairwise disjointness of `fixedObjects s` gives disjointness between distinct
fixed-object sublists (`globalBuffers`, `journal`, `blockOutObjects`, `balObjects`). -/
theorem fixedObjects_disj_parts {F : Type} {s : PanSemStateFiniteExact 64 F} (hF : FixedTyped s) :
    let gbs := globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)
    let jr := [(if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap")]
    gbs.Pairwise Disj ∧
    (blockOutObjects s).Pairwise Disj ∧
    (∀ a ∈ gbs, ∀ b ∈ jr ++ blockOutObjects s ++ balObjects s, Disj a b) ∧
    (∀ a ∈ jr, ∀ b ∈ blockOutObjects s ++ balObjects s, Disj a b) ∧
    (∀ a ∈ blockOutObjects s, ∀ b ∈ balObjects s, Disj a b) := by
  dsimp only
  have hp := hF.2
  unfold fixedObjects at hp
  rw [List.append_assoc, List.append_assoc, List.pairwise_append] at hp
  obtain ⟨hgbs, hrest1, hcross1⟩ := hp
  rw [List.pairwise_append] at hrest1
  obtain ⟨hjr, hrest2, hcross2⟩ := hrest1
  rw [List.pairwise_append] at hrest2
  obtain ⟨hbo, _, hcross3⟩ := hrest2
  exact ⟨hgbs, hbo,
    fun a ha b hb => hcross1 a ha b (by simpa only [List.append_assoc] using hb),
    hcross2, hcross3⟩

/-- Case 1: Store to an untyped word `bo + off` (`off ∈ [0, 8, 16, 48]`). -/
theorem store_bo_untyped_world {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaReady s) (hE : TxEnv s) {S Nd : List Nat} (hW : WorldTypedWith s S Nd)
    {off : Nat} (hoff : off ∈ ([0, 8, 16, 48] : List Nat))
    {x : BitVec 64} (hx : s.memaddrs x) (hx_eq : x.toNat = globN s "bo" + off)
    {mem' : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem' a = s.memory a) :
    WorldTypedWith {s with memory := mem'} S Nd ∧
    worldOwned {s with memory := mem'} S Nd = worldOwned s S Nd ∧
    TxEnv {s with memory := mem'} := by
  obtain ⟨hgbs, _, hgb_rest, _, _⟩ := fixedObjects_disj_parts hW.2.2.1
  have hbo_fix : (globN s "bo", 88) ∈ fixedObjects s := by
    simpa [hE.bo_nz] using typedRecord_mem_fixedObjects s (r := ("bo", 88)) (by decide)
  have hbo_hi := (ivl_allocated_bound hA.2 (bo_words hW.2.2.1 hE.bo_nz).1).2
  have hin_bo : Inside (x.toNat, 8) (globN s "bo") (globN s "bo" + 88) := by
    unfold Inside; dsimp only
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    rcases hoff with rfl | rfl | rfl | rfl <;> omega
  have hbo_gbs : (globN s "bo", 88) ∈ (globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) :=
    List.mem_map.2 ⟨("bo", 88), by decide, by simp [hE.bo_nz]⟩
  have hrec_disj : ∀ (g : String) (sz : Nat), (g, sz) ∈ globalBuffers → g ≠ "bo" →
      globN s g ≠ 0 → Disj (globN s g, sz) (globN s "bo", 88) := by
    intro g sz hgb hne hgnz
    obtain ⟨i1, hi1, eq1⟩ := List.mem_iff_getElem.1 hgb
    obtain ⟨i2, hi2, eq2⟩ := List.mem_iff_getElem.1 (show ("bo", 88) ∈ globalBuffers by decide)
    have hne_idx : i1 ≠ i2 := by intro h; subst h; rw [eq1] at eq2; exact hne (congrArg Prod.fst eq2)
    have hget := List.pairwise_iff_getElem.1 hgbs
    rcases Nat.lt_or_gt_of_ne hne_idx with hlt | hgt
    · have hd := hget i1 i2 (by simp; exact hi1) (by simp; exact hi2) hlt
      simpa only [List.getElem_map, eq1, eq2, hgnz, hE.bo_nz, ↓reduceIte] using hd
    · have hd := hget i2 i1 (by simp; exact hi2) (by simp; exact hi1) hgt
      exact disj_symm (by simpa only [List.getElem_map, eq1, eq2, hgnz, hE.bo_nz, ↓reduceIte] using hd)
  apply worldTypedWith_single_store_of_disj hA hE hW hx
  · intro t ht i hi
    exact disj_of_inside_right hin_bo (((hW.1.2.1 t ht).2 i hi).2 _ hbo_fix)
  · intro hn; exact disj_of_inside_right hin_bo (hrec_disj "ws" 40 (by decide) (by decide) hn)
  · intro hn; exact disj_of_inside_right hin_bo (hrec_disj "bs" 80 (by decide) (by decide) hn)
  · intro hn; exact disj_of_inside_right hin_bo (hrec_disj "ts" 72 (by decide) (by decide) hn)
  · intro hn
    refine disj_of_inside_right hin_bo (disj_symm (hgb_rest _ hbo_gbs _ ?_))
    apply List.mem_append_left; apply List.mem_append_left
    simp [hn]
  · refine disj_of_inside_right hin_bo (disj_symm (hgb_rest _ hbo_gbs _ ?_))
    apply List.mem_append_left; apply List.mem_append_right
    simp [blockOutObjects, hE.bo_nz, hE.bo40]
  · refine disj_of_inside_right hin_bo (disj_symm (hgb_rest _ hbo_gbs _ ?_))
    apply List.mem_append_left; apply List.mem_append_right
    simp [blockOutObjects, hE.bo_nz, hE.bo72]
  · intro i hi
    refine disj_of_inside_right hin_bo (disj_symm (hgb_rest _ hbo_gbs _ ?_))
    apply List.mem_append_right; exact hi
  · intro o ho
    exact disj_of_inside_right hin_bo ((hW.2.2.2.2.1 o ho).2 _ hbo_fix)
  · intro k hk heq
    have htonat := congrArg BitVec.toNat heq
    dsimp only at hbo_hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff hk
    have hk_lt : globN s "bo" + k < 2 ^ 64 := by
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk_lt, hx_eq] at htonat
    rcases hoff with rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · exact hm

theorem blockOutObjects_eq_list {F : Type} {s : PanSemStateFiniteExact 64 F} (hE : TxEnv s)
    {S : List Nat} (hT : TablesTyped s S) :
    let bo := globN s "bo"
    let obj (p len : Nat) : Ivl := if bo = 0 ∨ p = 0 ∨ len = 0 then (0, 0) else (p, len)
    let l40 := memW s (bo + 40)
    let l72 := memW s (bo + 72)
    1 ≤ memW s (l40 + 16) ∧ 1 ≤ memW s (l72 + 16) ∧
    blockOutObjects s =
      [obj (memW s (bo + 24)) (16 * memW s (bo + 80) + 16),
       (memW s (bo + 32), 16 * memW s (bo + 80) + 16),
       obj (memW s (bo + 56)) 128,
       (l40, 24),
       obj (memW s l40) (8 * memW s (l40 + 16)),
       (l72, 24),
       obj (memW s l72) (8 * memW s (l72 + 16))] := by
  have hl40_ok := hT.2.2.2.2.2.2.2.2.2.2.1 hE.bo_nz 40 (by simp) hE.bo40
  have hl72_ok := hT.2.2.2.2.2.2.2.2.2.2.1 hE.bo_nz 72 (by simp) hE.bo72
  refine ⟨hl40_ok.1, hl72_ok.1, ?_⟩
  unfold blockOutObjects
  simp [hE.bo_nz, hE.bo32, hE.bo40, hE.bo72]

/-- Case 2: Store inside a `blockOutObjects s` array at index `idx ∈ [1, 4, 6]`
(`1` = `bo+32` receipt array, `4` = `bo+40` backing array, `6` = `bo+72` backing array). -/
theorem store_bo_array_world {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaReady s) (hE : TxEnv s) {S Nd : List Nat} (hW : WorldTypedWith s S Nd)
    {idx : Nat} {arr : Ivl}
    (hidx : (idx = 1 ∧ arr = (memW s (globN s "bo" + 32), 16 * memW s (globN s "bo" + 80) + 16)) ∨
            (idx = 4 ∧ memW s (memW s (globN s "bo" + 40)) ≠ 0 ∧
              arr = (memW s (memW s (globN s "bo" + 40)), 8 * memW s (memW s (globN s "bo" + 40) + 16))) ∨
            (idx = 6 ∧ memW s (memW s (globN s "bo" + 72)) ≠ 0 ∧
              arr = (memW s (memW s (globN s "bo" + 72)), 8 * memW s (memW s (globN s "bo" + 72) + 16))))
    {x : BitVec 64} (hx : s.memaddrs x)
    (hin : Inside (x.toNat, 8) arr.1 (arr.1 + arr.2))
    {mem' : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem' a = s.memory a) :
    WorldTypedWith {s with memory := mem'} S Nd ∧
    worldOwned {s with memory := mem'} S Nd = worldOwned s S Nd ∧
    TxEnv {s with memory := mem'} := by
  obtain ⟨hgbs, hbo_pw, hgb_rest, hjr_rest, hbo_bal⟩ := fixedObjects_disj_parts hW.2.2.1
  obtain ⟨hc40, hc72, hbo_eq⟩ := blockOutObjects_eq_list hE hW.1
  have hbo_len : (blockOutObjects s).length = 7 := by rw [hbo_eq]; rfl
  have harr_get : ∃ (h_lt : idx < (blockOutObjects s).length), (blockOutObjects s)[idx] = arr := by
    rcases hidx with ⟨rfl, rfl⟩ | ⟨rfl, hnz, rfl⟩ | ⟨rfl, hnz, rfl⟩
    · refine ⟨by omega, ?_⟩; simp [hbo_eq]
    · refine ⟨by omega, ?_⟩
      have hpos : 8 * memW s (memW s (globN s "bo" + 40) + 16) ≠ 0 := by omega
      simp [hbo_eq, hE.bo_nz, hnz, hpos]
    · refine ⟨by omega, ?_⟩
      have hpos : 8 * memW s (memW s (globN s "bo" + 72) + 16) ≠ 0 := by omega
      simp [hbo_eq, hE.bo_nz, hnz, hpos]
  obtain ⟨hilt, hget_arr⟩ := harr_get
  have harr_bo : arr ∈ blockOutObjects s := hget_arr ▸ List.getElem_mem hilt
  have harr_fix : arr ∈ fixedObjects s :=
    List.mem_append_left _ (List.mem_append_right _ harr_bo)
  have hbo_gbs : (globN s "bo", 88) ∈ (globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) :=
    List.mem_map.2 ⟨("bo", 88), by decide, by simp [hE.bo_nz]⟩
  have hbo_disj_arr : Disj (globN s "bo", 88) arr :=
    hgb_rest _ hbo_gbs arr (List.mem_append_left _ (List.mem_append_right _ harr_bo))
  have hbo_hi := (ivl_allocated_bound hA.2 (bo_words hW.2.2.1 hE.bo_nz).1).2
  have hbo_idx_disj : ∀ (j : Nat) (hj : j < (blockOutObjects s).length), j ≠ idx →
      Disj (blockOutObjects s)[j] arr := by
    intro j hj hne
    have hget := List.pairwise_iff_getElem.1 hbo_pw
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact hget_arr ▸ hget j idx hj hilt hlt
    · exact disj_symm (hget_arr ▸ hget idx j hilt hj hgt)
  apply worldTypedWith_single_store_of_disj hA hE hW hx
  · intro t ht i hi
    exact disj_of_inside_right hin (((hW.1.2.1 t ht).2 i hi).2 _ harr_fix)
  · intro hn
    refine disj_of_inside_right hin (hgb_rest _ ?_ arr (List.mem_append_left _ (List.mem_append_right _ harr_bo)))
    exact List.mem_map.2 ⟨("ws", 40), by decide, by simp [hn]⟩
  · intro hn
    refine disj_of_inside_right hin (hgb_rest _ ?_ arr (List.mem_append_left _ (List.mem_append_right _ harr_bo)))
    exact List.mem_map.2 ⟨("bs", 80), by decide, by simp [hn]⟩
  · intro hn
    refine disj_of_inside_right hin (hgb_rest _ ?_ arr (List.mem_append_left _ (List.mem_append_right _ harr_bo)))
    exact List.mem_map.2 ⟨("ts", 72), by decide, by simp [hn]⟩
  · intro hn
    refine disj_of_inside_right hin (hjr_rest _ ?_ arr (List.mem_append_left _ harr_bo))
    simp [hn]
  · have hj3 : 3 < (blockOutObjects s).length := by omega
    have h3_eq : (blockOutObjects s)[3] = (memW s (globN s "bo" + 40), 24) := by simp [hbo_eq]
    have hne3 : 3 ≠ idx := by rcases hidx with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
    exact disj_of_inside_right hin (h3_eq ▸ hbo_idx_disj 3 hj3 hne3)
  · have hj5 : 5 < (blockOutObjects s).length := by omega
    have h5_eq : (blockOutObjects s)[5] = (memW s (globN s "bo" + 72), 24) := by simp [hbo_eq]
    have hne5 : 5 ≠ idx := by rcases hidx with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
    exact disj_of_inside_right hin (h5_eq ▸ hbo_idx_disj 5 hj5 hne5)
  · intro i hi
    exact disj_of_inside_right hin (disj_symm (hbo_bal arr harr_bo i hi))
  · intro o ho
    exact disj_of_inside_right hin ((hW.2.2.2.2.1 o ho).2 _ harr_fix)
  · intro k hk heq
    have htonat := congrArg BitVec.toNat heq
    dsimp only at hbo_hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    have hk_lt : globN s "bo" + k < 2 ^ 64 := by
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk_lt] at htonat
    have hdj := disj_of_inside_right hin hbo_disj_arr
    rcases hdj with h0 | h0 | hd1 | hd2
    · simp at h0
    · simp at h0
    · dsimp only at hd1
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    · dsimp only at hd2
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · exact hm

/-- Case 3: Store inside a caller-owned block `blk` disjoint from `worldOwned s S Nd`! -/
theorem store_outside_worldOwned {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaReady s) (hE : TxEnv s) {S Nd : List Nat} (hW : WorldTypedWith s S Nd)
    {blk : Ivl} (hblk_d : ∀ o ∈ worldOwned s S Nd, Disj blk o)
    {x : BitVec 64} (hx : s.memaddrs x)
    (hin : Inside (x.toNat, 8) blk.1 (blk.1 + blk.2))
    {mem' : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem' a = s.memory a) :
    WorldTypedWith {s with memory := mem'} S Nd ∧
    worldOwned {s with memory := mem'} S Nd = worldOwned s S Nd ∧
    TxEnv {s with memory := mem'} := by
  have hd_x : ∀ o ∈ worldOwned s S Nd, Disj o (x.toNat, 8) :=
    fun o ho => disj_of_inside_right hin (disj_symm (hblk_d o ho))
  have hbo_own : (globN s "bo", 88) ∈ worldOwned s S Nd := by
    apply List.mem_append_left; apply List.mem_append_right
    simpa [hE.bo_nz] using typedRecord_mem_fixedObjects s (r := ("bo", 88)) (by decide)
  have hbo_hi := (ivl_allocated_bound hA.2 (bo_words hW.2.2.1 hE.bo_nz).1).2
  apply worldTypedWith_single_store_of_disj hA hE hW hx
  · intro t ht i hi
    exact hd_x i (List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨t, ht, hi⟩)))
  · intro hn
    exact hd_x _ (List.mem_append_left _ (List.mem_append_right _
      (by simpa [hn] using typedRecord_mem_fixedObjects s (r := ("ws", 40)) (by decide))))
  · intro hn
    exact hd_x _ (List.mem_append_left _ (List.mem_append_right _
      (by simpa [hn] using typedRecord_mem_fixedObjects s (r := ("bs", 80)) (by decide))))
  · intro hn
    exact hd_x _ (List.mem_append_left _ (List.mem_append_right _
      (by simpa [hn] using typedRecord_mem_fixedObjects s (r := ("ts", 72)) (by decide))))
  · intro hn
    refine hd_x _ (List.mem_append_left _ (List.mem_append_right _ ?_))
    unfold fixedObjects
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
    simp [hn]
  · refine hd_x _ (List.mem_append_left _ (List.mem_append_right _ ?_))
    unfold fixedObjects
    apply List.mem_append_left; apply List.mem_append_right
    simp [blockOutObjects, hE.bo_nz, hE.bo40]
  · refine hd_x _ (List.mem_append_left _ (List.mem_append_right _ ?_))
    unfold fixedObjects
    apply List.mem_append_left; apply List.mem_append_right
    simp [blockOutObjects, hE.bo_nz, hE.bo72]
  · intro i hi
    exact hd_x i (List.mem_append_left _ (List.mem_append_right _ (List.mem_append_right _ hi)))
  · intro o ho
    exact hd_x o (List.mem_append_right _ ho)
  · intro k hk heq
    have htonat := congrArg BitVec.toNat heq
    dsimp only at hbo_hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    have hk_lt : globN s "bo" + k < 2 ^ 64 := by
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk_lt] at htonat
    have hdj := hd_x (globN s "bo", 88) hbo_own
    rcases hdj with h0 | h0 | hd1 | hd2
    · simp at h0
    · simp at h0
    · dsimp only at hd1
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    · dsimp only at hd2
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · exact hm

/-! ## 8. Phase 4 Stage Invariants and Step Lemmas -/

theorem worldTypedWith_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (S Nd : List Nat) :
    WorldTypedWith { s with locals := locals, clock := k } S Nd ↔ WorldTypedWith s S Nd := by
  simp only [WorldTypedWith, tablesTyped_with_locals]
  exact Iff.rfl

theorem txEnv_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (hidx : locals.lookup (ofString "index") = s.locals.lookup (ofString "index"))
    (h : TxEnv s) : TxEnv { s with locals := locals, clock := k } := by
  have hi := locN_congr s locals k "index" hidx
  exact ⟨h.bo_nz, h.bo24, h.bo32, h.bo40, h.bo72, by rw [hi]; exact h.idx_lt, h.jcap_nz⟩

theorem localsOnly_txWorld : LocalsOnly ["index"] TxWorld := by
  intro F s locals k hl h
  exact ⟨localsFree_worldOK s locals k h.1, txEnv_with_locals s locals k (hl "index" (by simp)) h.2⟩

theorem worldStep_with_locals {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)}
    (h : WorldStep R gw keep Q s r post)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    WorldStep (fun _ => R s) gw keep NoExtra {s with locals := locals, clock := k} r post := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
  intro S Nd hW hR
  have hWs := (worldTypedWith_with_locals s locals k S Nd).mp hW
  obtain ⟨S', Nd', hsub, hW', hgrow, hframe, _⟩ := h.2.2.2.2 S Nd hWs hR
  exact ⟨S', Nd', hsub, hW', hgrow, hframe, trivial⟩

theorem txEnv_preserved_by_worldStep {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)} {boKeep : List Nat}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)}
    (hstep : WorldStep R gw keep Q s r post)
    (hbo_gw : ofString "bo" ∉ gw.map ofString)
    (hjcap_gw : ofString "journal_cap" ∉ gw.map ofString)
    (hbo_keep : ("bo", boKeep) ∈ keep)
    (hoffs : ∀ k ∈ ([24, 32, 40, 72, 80] : List Nat), k ∈ boKeep)
    (hR_bo : ∀ i ∈ R s, Disj i (globN s "bo", 88))
    (hbo8 : globN s "bo" % 8 = 0)
    (hR_zero : ∀ i ∈ R s, i.2 = 0 → i.1 % 8 = 0)
    (henv : TxEnv s)
    {locals : HolFiniteMapExact MlS (ValueHOL 64)}
    (hidx : locals.lookup (ofString "index") = s.locals.lookup (ofString "index")) :
    TxEnv { post with locals := locals } := by
  obtain ⟨_, _, hg_kept, hrec_kept, _⟩ := hstep
  have hbo_eq : globN post "bo" = globN s "bo" :=
    (globN_eq_of_lookup_eq (hg_kept (ofString "bo") hbo_gw)).symm
  have hjcap_eq : globN post "journal_cap" = globN s "journal_cap" :=
    (globN_eq_of_lookup_eq (hg_kept (ofString "journal_cap") hjcap_gw)).symm
  have hkw : ∀ k ∈ ([24, 32, 40, 72, 80] : List Nat),
      memW post (globN s "bo" + k) = memW s (globN s "bo" + k) := by
    intro k hk
    apply hrec_kept ("bo", boKeep) hbo_keep henv.bo_nz k (hoffs k hk)
    intro i hi hch
    dsimp only at hch
    have hk_in : k + 8 ≤ 88 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega
    have hbase : (globN s "bo" + k) % 8 = (globN s "bo") % 8 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega
    rcases hR_bo i hi with hz | hz | hd | hd
    · have hnorm := hR_zero i hi hz
      unfold CellHits at hch; dsimp only at *; omega
    · simp at hz
    · unfold CellHits at hch; dsimp only at hd; omega
    · unfold CellHits at hch; dsimp only at hd; omega
  have hi := locN_congr s locals post.clock "index" hidx
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show globN post "bo" ≠ 0; rw [hbo_eq]; exact henv.bo_nz
  · show memW post (globN post "bo" + 24) ≠ 0; rw [hbo_eq, hkw 24 (by simp)]; exact henv.bo24
  · show memW post (globN post "bo" + 32) ≠ 0; rw [hbo_eq, hkw 32 (by simp)]; exact henv.bo32
  · show memW post (globN post "bo" + 40) ≠ 0; rw [hbo_eq, hkw 40 (by simp)]; exact henv.bo40
  · show memW post (globN post "bo" + 72) ≠ 0; rw [hbo_eq, hkw 72 (by simp)]; exact henv.bo72
  · show locN { post with locals := locals } "index" < memW post (globN post "bo" + 80)
    change locN { s with locals := locals, clock := post.clock } "index" < _
    rw [hi, hbo_eq, hkw 80 (by simp)]; exact henv.idx_lt
  · show globN post "journal_cap" ≠ 0; rw [hjcap_eq]; exact henv.jcap_nz

  where
    globN_eq_of_lookup_eq {F : Type} {a b : PanSemStateFiniteExact 64 F} {n : String}
        (h : a.globals.lookup (ofString n) = b.globals.lookup (ofString n)) :
        globN a n = globN b n := by simp only [globN, h]

theorem heap_ivl_survives_step {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaOK s) (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    {old new R : List Ivl}
    (hold0 : ∀ j ∈ old, j.2 = 0 → j.1 % 8 = 0)
    (hR0 : ∀ j ∈ R, j.2 = 0 → j.1 % 8 = 0)
    (hog : OwnedGrows s post old new)
    (hfr : FrameOutside s post (old ++ R ++ [freeGap s]) (heapFree s))
    {b : Ivl} (_hb1 : b.1 % 8 = 0) (_hb2 : b.2 % 8 = 0)
    (hb_in : Inside b sourceBase (globN s "heap_ptr"))
    (hb_old : ∀ j ∈ old, Disj b j)
    (hb_R : ∀ j ∈ R, Disj b j) :
    Inside b sourceBase (globN post "heap_ptr") ∧
    (∀ o ∈ new, Disj b o) ∧
    IvlUnhit s post b := by
  have hsep : heapLimit ≤ scratchStart := by decide
  obtain ⟨_, hs_hp, hs_fm, hs_sc, _⟩ := hAs
  refine ⟨⟨hb_in.1, Nat.le_trans hb_in.2 hhp⟩, ?_, ?_⟩
  · intro o ho
    rcases hog o ho with rfl | ⟨j, hj, hin⟩ | hfresh
    · exact disj_zero_right b
    · exact disj_of_inside_right hin (hb_old j hj)
    · exact Or.inr (Or.inr (Or.inl (Nat.le_trans hb_in.2 hfresh.1)))
  · intro a ha8 hhit
    obtain ⟨hc1, hc2⟩ := hhit
    have ha_in : b.1 ≤ a.toNat ∧ a.toNat + 8 ≤ b.1 + b.2 := by omega
    apply hfr a
    · intro j hj hcj
      obtain ⟨hj1, hj2⟩ := hcj
      rcases List.mem_append.1 hj with hj12 | hfg
      · rcases List.mem_append.1 hj12 with hj_old | hj_R
        · exact not_cellHits_of_disj ha8 (hold0 j hj_old) ha_in (hb_old j hj_old) ⟨hj1, hj2⟩
        · exact not_cellHits_of_disj ha8 (hR0 j hj_R) ha_in (hb_R j hj_R) ⟨hj1, hj2⟩
      · simp only [List.mem_singleton] at hfg; subst hfg
        unfold freeGap at hj1 hj2; unfold Inside at hb_in; dsimp at hj1 hj2; omega
    · intro hcf
      obtain ⟨hf1, hf2⟩ := hcf
      unfold heapFree at hf1 hf2; unfold Inside at hb_in; dsimp at hf1 hf2; omega

theorem logsListOK_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k logs : Nat) :
    LogsListOK { s with locals := locals, clock := k } logs ↔ LogsListOK s logs := by
  unfold LogsListOK
  refine or_congr Iff.rfl (and_congr ?_ (and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl
    (forall_congr' fun _ => imp_congr_right fun _ => and_congr Iff.rfl ?_)))))
  · rfl
  · rfl

theorem stableLogsOK_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k logs : Nat) :
    StableLogsOK { s with locals := locals, clock := k } logs ↔ StableLogsOK s logs :=
  and_congr (logsListOK_with_locals s locals k logs) Iff.rfl

/-- `LogEntryOK` survives any change to memory outside `(log, 40)` that only grows `heap_ptr`
(because `LogEntryOK` only reads `memW` at offsets `0, 8, 16, 24, 32` inside `(log, 40)`!). -/
theorem logEntryOK_congr_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaOK s) (hgS : GuestInv s) (hgP : GuestInv post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    {log : Nat} (hl : LogEntryOK s log) (hu : IvlUnhit s post (log, 40)) :
    LogEntryOK post log := by
  obtain ⟨hw, hin, h16, h32, hi0, hi8, hi24⟩ := hl
  have hhi := (ivl_allocated_bound hAs (Or.inl hin)).2
  have hl8 : log % 8 = 0 := hw.1
  have e0 : memW post log = memW s log := by
    simpa using memW_eq_of_ivlUnhit hu hl8 hhi ⟨by omega, by omega⟩
  have e8 : memW post (log + 8) = memW s (log + 8) :=
    memW_eq_of_ivlUnhit hu (by omega) hhi ⟨by omega, by omega⟩
  have e16 : memW post (log + 16) = memW s (log + 16) :=
    memW_eq_of_ivlUnhit hu (by omega) hhi ⟨by omega, by omega⟩
  have e24 : memW post (log + 24) = memW s (log + 24) :=
    memW_eq_of_ivlUnhit hu (by omega) hhi ⟨by omega, by omega⟩
  have e32 : memW post (log + 32) = memW s (log + 32) :=
    memW_eq_of_ivlUnhit hu (by omega) hhi ⟨by omega, by omega⟩
  unfold LogEntryOK
  rw [e0, e8, e16, e24, e32]
  exact ⟨wordsOK_transfer hgS hgP hw, ⟨hin.1, hin.2.trans hhp⟩, h16, h32,
    ⟨hi0.1, hi0.2.trans hhp⟩, ⟨hi8.1, hi8.2.trans hhp⟩, ⟨hi24.1, hi24.2.trans hhp⟩⟩

end InitECandidate.Solver.Wave8GuestInv.R13Shards

