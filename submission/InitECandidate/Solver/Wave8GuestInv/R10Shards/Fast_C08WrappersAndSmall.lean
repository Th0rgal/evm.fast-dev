import InitECandidate.Solver.Wave8GuestInv.ContractParts.C07
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M05.wk_extract_deposit_data
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M08.wk_memcpy
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M08.wk_memzero
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M11.wk_rlp_encode_bytes
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M11.wk_rlp_encode_word
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M12.wk_st_le64
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M13.wk_u256_to_be_min
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M17.ro_tx_chain_id
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M17.ro_tx_has_access_list
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M17.ro_tx_is_blob
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M17.ro_tx_is_setcode
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.ro_u256_mul
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.ro_u256_sub
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.ro_udiv_small5
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.ro_validate_block_access_list_gas_limit
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.ro_validate_transaction
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M25.nf_node_invalidate
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M25.rt_alloc
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M26.rt_lst_new
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M26.rt_msg_new
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M26.rt_node_new_ext
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M26.rt_scratch_alloc
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M27.rt_te_new
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M27.rv_common_prefix_length
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M27.rv_min
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M27.rv_rlp_encode_bytes
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M27.rv_u256_to_be_min
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M27.rv_validate_transaction
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M28.ww_memzero
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M29.zv_memzero
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P02
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28_ForkEvm

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 1200000
set_option exponentiation.threshold 2000
set_option linter.style.nameCheck false
set_option linter.unusedSimpArgs false

namespace InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_C08WrappersAndSmall

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## Part 1: Exact `C08` signature adapters for `Deliveries/M*` -/

theorem «nf_node_invalidate» :
    NodeFn ["nd"]
    (fun _ _ => True)
    (ofString "node_invalidate") :=
  InitECandidate.Solver.Wave8Contracts.M25.«nf_node_invalidate»

private def feeMulCallees (f : MlS) : Bool :=
  f == ofString "mul64x64" || f == ofString "u256_mul_full"

private theorem feeMulCallees_good :
    ∀ function, feeMulCallees function = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup function values =
        some (body, callee, rs) →
      InitECandidate.Solver.Wave8Contracts.M18.readOnlyProg feeMulCallees body = true := by
  intro function hfn values body callee rs hfound
  simp only [feeMulCallees, Bool.or_eq_true, beq_iff_eq] at hfn
  rcases hfn with rfl | rfl
  · exact InitECandidate.Solver.Wave8Contracts.M18.installed_body_readOnly 59
      (by rw [guestAst_len]; decide) Guest.Software.guestFn_mul64x64 rfl feeMulCallees rfl hfound
  · exact InitECandidate.Solver.Wave8Contracts.M18.installed_body_readOnly 61
      (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_mul_full rfl feeMulCallees rfl hfound

private def nodedbLookupCallees (f : MlS) : Bool :=
  f == ofString "memeq" || f == ofString "htab_find_leaf" || f == ofString "htab_get"

private theorem nodedbLookupCallees_good :
    ∀ function, nodedbLookupCallees function = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup function values =
        some (body, callee, rs) →
      InitECandidate.Solver.Wave8Contracts.M18.readOnlyProg nodedbLookupCallees body = true := by
  intro function hfn values body callee rs hfound
  simp only [nodedbLookupCallees, Bool.or_eq_true, beq_iff_eq] at hfn
  rcases hfn with ((rfl | rfl) | rfl)
  · exact InitECandidate.Solver.Wave8Contracts.M18.installed_body_readOnly 18
      (by rw [guestAst_len]; decide) Guest.Software.guestFn_memeq rfl nodedbLookupCallees rfl hfound
  · exact InitECandidate.Solver.Wave8Contracts.M18.installed_body_readOnly 131
      (by rw [guestAst_len]; decide) Guest.Software.guestFn_htab_find_leaf rfl nodedbLookupCallees rfl hfound
  · exact InitECandidate.Solver.Wave8Contracts.M18.installed_body_readOnly 132
      (by rw [guestAst_len]; decide) Guest.Software.guestFn_htab_get rfl nodedbLookupCallees rfl hfound

theorem «ro_calculate_total_blob_gas» :
    ReadOnlyFn (ofString "calculate_total_blob_gas") :=
  InitECandidate.Solver.Wave8Contracts.M18.readOnlyFn_of_guestAst 317
    (by rw [guestAst_len]; decide) Guest.Software.guestFn_calculate_total_blob_gas rfl
    (fun _ => false) (fun _ h => by cases h) rfl

theorem «ro_check_gas_limit» :
    ReadOnlyFn (ofString "check_gas_limit") :=
  InitECandidate.Solver.Wave8Contracts.M18.readOnlyFn_of_guestAst 235
    (by rw [guestAst_len]; decide) Guest.Software.guestFn_check_gas_limit rfl
    InitECandidate.Solver.Wave8Contracts.M18.m18Callees
    InitECandidate.Solver.Wave8Contracts.M18.m18Callees_good rfl

theorem «ro_fee_mul» :
    ReadOnlyFn (ofString "fee_mul") :=
  InitECandidate.Solver.Wave8Contracts.M18.readOnlyFn_of_guestAst 867
    (by rw [guestAst_len]; decide) Guest.Software.guestFn_fee_mul rfl
    feeMulCallees feeMulCallees_good rfl

theorem «ro__node_needs_rlp» :
    ReadOnlyFn (ofString "_node_needs_rlp") :=
  InitECandidate.Solver.Wave8Contracts.M18.readOnlyFn_of_guestAst 283
    (by rw [guestAst_len]; decide) Guest.Software.guestFn__node_needs_rlp rfl
    (fun _ => false) (fun _ h => by cases h) rfl

theorem «ro_mpt_fail» :
    ReadOnlyFn (ofString "mpt_fail") :=
  InitECandidate.Solver.Wave8Contracts.M18.readOnlyFn_of_guestAst 246
    (by rw [guestAst_len]; decide) Guest.Software.guestFn_mpt_fail rfl
    (fun _ => false) (fun _ h => by cases h) rfl

theorem «ro_nodedb_lookup» :
    ReadOnlyFn (ofString "nodedb_lookup") :=
  InitECandidate.Solver.Wave8Contracts.M18.readOnlyFn_of_guestAst 254
    (by rw [guestAst_len]; decide) Guest.Software.guestFn_nodedb_lookup rfl
    nodedbLookupCallees nodedbLookupCallees_good rfl

theorem «ro_secp256k1_init» :
    ReadOnlyFn (ofString "secp256k1_init") :=
  InitECandidate.Solver.Wave8Contracts.M18.readOnlyFn_of_guestAst 148
    (by rw [guestAst_len]; decide) Guest.Software.guestFn_secp256k1_init rfl
    (fun _ => false) (fun _ h => by cases h) rfl

theorem «ro_tx_chain_id» :
    ReadOnlyFn (ofString "tx_chain_id") :=
  InitECandidate.Solver.Wave8GuestInv.M17.ro_tx_chain_id

theorem «ro_tx_has_access_list» :
    ReadOnlyFn (ofString "tx_has_access_list") :=
  InitECandidate.Solver.Wave8GuestInv.M17.ro_tx_has_access_list

theorem «ro_tx_is_blob» :
    ReadOnlyFn (ofString "tx_is_blob") :=
  InitECandidate.Solver.Wave8GuestInv.M17.ro_tx_is_blob

theorem «ro_tx_is_setcode» :
    ReadOnlyFn (ofString "tx_is_setcode") :=
  InitECandidate.Solver.Wave8GuestInv.M17.ro_tx_is_setcode

theorem «ro_u256_mul» :
    ReadOnlyFn (ofString "u256_mul") :=
  InitECandidate.Solver.Wave8Contracts.M18.«ro_u256_mul»

theorem «ro_u256_sub» :
    ReadOnlyFn (ofString "u256_sub") :=
  InitECandidate.Solver.Wave8Contracts.M18.«ro_u256_sub»

theorem «ro_udiv_small5» :
    ReadOnlyFn (ofString "udiv_small5") :=
  InitECandidate.Solver.Wave8Contracts.M18.«ro_udiv_small5»

theorem «ro_validate_block_access_list_gas_limit» :
    ReadOnlyFn (ofString "validate_block_access_list_gas_limit") :=
  InitECandidate.Solver.Wave8Contracts.M18.«ro_validate_block_access_list_gas_limit»

theorem «ro_validate_transaction» :
    ReadOnlyFn (ofString "validate_transaction") :=
  InitECandidate.Solver.Wave8Contracts.M18.«ro_validate_transaction»

theorem «rt_alloc» :
    Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n"))
      (ofString "alloc") :=
  InitECandidate.Solver.Wave8Contracts.M25.«rt_alloc»

theorem «rt_lst_new» :
    Returns ArenaReady (fun s post l => locN s "esz" * locN s "cap" < 2 ^ 64 → 1 ≤ locN s "cap" →
      FreshBlock s post l 24 ∧ FreshBlock s post (memW post l) (locN s "esz" * locN s "cap") ∧
        Disj (l, 24) (memW post l, locN s "esz" * locN s "cap") ∧
        memW post (l + 8) = 0 ∧ memW post (l + 16) = locN s "cap")
      (ofString "lst_new") :=
  InitECandidate.Solver.Wave8Contracts.M26.rt_lst_new

theorem «rt_msg_new» :
    Returns ArenaReady (fun s post m => FreshBlock s post m 176 ∧ ∀ k, k < 22 → memW post (m + 8 * k) = 0)
      (ofString "msg_new") :=
  InitECandidate.Solver.Wave8Contracts.M26.rt_msg_new

theorem «rt_node_new_ext» :
    Returns ArenaReady (fun s post p => FreshBlock s post p 56)
      (ofString "node_new_ext") :=
  InitECandidate.Solver.Wave8Contracts.M26.rt_node_new_ext

theorem «rt_scratch_alloc» :
    Returns ArenaReady (fun s post p => FreshScratch s post p (locN s "n") ∧ globN post "scratch_ptr" = p)
      (ofString "scratch_alloc") :=
  InitECandidate.Solver.Wave8Contracts.M26.rt_scratch_alloc

theorem «rt_te_new» :
    Returns ArenaReady (fun s post m => FreshBlock s post m 200 ∧ ∀ k, k < 25 → memW post (m + 8 * k) = 0)
      (ofString "te_new") :=
  InitECandidate.Solver.Wave8Contracts.M27.rt_te_new

theorem «rv_common_prefix_length» :
    RetLe (fun s => min (locN s "al") (locN s "bl")) (ofString "common_prefix_length") :=
  InitECandidate.Solver.Wave8Contracts.M27.rv_common_prefix_length

theorem «rv_min» :
    RetLe (fun s => locN s "a") (ofString "min") :=
  InitECandidate.Solver.Wave8Contracts.M27.rv_min

theorem «rv_rlp_encode_bytes» :
    RetLe (fun s => locN s "n" + 9) (ofString "rlp_encode_bytes") :=
  InitECandidate.Solver.Wave8Contracts.M27.rv_rlp_encode_bytes

theorem «rv_u256_to_be_min» :
    RetLe (fun _ => 32) (ofString "u256_to_be_min") :=
  InitECandidate.Solver.Wave8Contracts.M27.rv_u256_to_be_min

theorem «rv_validate_transaction» :
    RetIntrinsic (ofString "validate_transaction") :=
  InitECandidate.Solver.Wave8Contracts.M27.rv_validate_transaction

theorem «wk_extract_deposit_data» :
    WorldKeeps WorldOK (fun s => [(locN s "out", 192)])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "extract_deposit_data") :=
  InitECandidate.Solver.Wave8Contracts.M05.«wk_extract_deposit_data»

theorem «wk_memcpy» :
    WorldKeeps WorldOK (fun s => [(locN s "dst", locN s "n")])
    []
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "memcpy") :=
  InitECandidate.Solver.Wave8Contracts.M08.«wk_memcpy»

theorem «wk_memzero» :
    WorldKeeps WorldOK (fun s => [(locN s "dst", locN s "n")])
    []
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "memzero") :=
  InitECandidate.Solver.Wave8Contracts.M08.«wk_memzero»

theorem «wk_rlp_encode_bytes» :
    WorldKeeps WorldOK (fun s => [(locN s "dst", locN s "n" + 9)])
    []
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "rlp_encode_bytes") :=
  InitECandidate.Solver.Wave8GuestInv.M11.«wk_rlp_encode_bytes»

theorem «wk_rlp_encode_word» :
    WorldKeeps WorldOK (fun s => [(locN s "dst", 9)])
    []
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "rlp_encode_word") :=
  InitECandidate.Solver.Wave8GuestInv.M11.«wk_rlp_encode_word»

theorem «wk_st_le64» :
    WorldKeeps WorldOK (fun s => [(locN s "p", 8)])
    []
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "st_le64") :=
  InitECandidate.Solver.Wave8Contracts.M12.«wk_st_le64»

theorem «wk_u256_to_be_min» :
    WorldKeeps WorldOK (fun s => [(locN s "out", 32)])
    []
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "u256_to_be_min") :=
  InitECandidate.Solver.Wave8GuestInv.M13.«wk_u256_to_be_min»

theorem «ww_memzero» :
    WritesWithin (fun s => [(locN s "dst", locN s "n")])
    [] (ofString "memzero") :=
  InitECandidate.Solver.Wave8Contracts.M28.«ww_memzero»

theorem «ww_node_new_ext» :
    WritesWithin (fun _ => [])
    ["heap_ptr"] (ofString "node_new_ext") :=
  InitECandidate.Solver.Wave8GuestInv.R10Shards.P02.ww_node_new_ext

theorem «ww_rlp_item» :
    WritesWithin (fun _ => [])
    ["scratch_ptr"] (ofString "rlp_item") :=
  InitECandidate.Solver.Wave8GuestInv.R10Shards.P02.ww_rlp_item

theorem «ww_scratch_alloc» :
    WritesWithin (fun _ => [])
    ["scratch_ptr"] (ofString "scratch_alloc") :=
  InitECandidate.Solver.Wave8GuestInv.R10Shards.P02.ww_scratch_alloc

theorem «wk_blake2_init» :
    WorldKeeps WorldOK (fun s => [(globN s "b2_iv", if globN s "b2_iv" = 0 then 0 else 64), (globN s "b2_sigma", if globN s "b2_sigma" = 0 then 0 else 80)])
    ["b2_iv", "b2_sigma", "b2_v", "heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "blake2_init") :=
  InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28.wk_blake2_init

theorem «wk_bls_precompiles_init» :
    WorldKeeps WorldOK (fun s => [(globN s "bls_c", if globN s "bls_c" = 0 then 0 else 7136), (globN s "bls_discount", if globN s "bls_discount" = 0 then 0 else 2048)])
    ["bls_c", "bls_discount", "heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "bls_precompiles_init") :=
  InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28.wk_bls_precompiles_init

theorem «wk_bn254_init» :
    WorldKeeps WorldOK (fun s => [(globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352), (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384)])
    ["bn_expw", "bn_gamma", "heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "bn254_init") :=
  InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28.wk_bn254_init

theorem «wk_evm_init» :
    WorldKeeps WorldOK (fun s => [(globN s "evm_empty", if globN s "evm_empty" = 0 then 0 else 8), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "null_address", if globN s "null_address" = 0 then 0 else 24), (globN s "transfer_topic", if globN s "transfer_topic" = 0 then 0 else 32), (globN s "vm_system_address", if globN s "vm_system_address" = 0 then 0 else 24)])
    ["evm_empty", "evm_key_buf", "heap_ptr", "null_address", "pre_hdr_buf", "transfer_topic", "vm_system_address"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "evm_init") :=
  InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28.wk_evm_init

theorem «wk_fork_init» :
    WorldKeeps WorldOK (fun s => [(globN s "beacon_roots_address", if globN s "beacon_roots_address" = 0 then 0 else 24), (globN s "builder_deposit_address", if globN s "builder_deposit_address" = 0 then 0 else 24), (globN s "builder_exit_address", if globN s "builder_exit_address" = 0 then 0 else 24), (globN s "consolidation_request_address", if globN s "consolidation_request_address" = 0 then 0 else 24), (globN s "deposit_contract_address", if globN s "deposit_contract_address" = 0 then 0 else 24), (globN s "deposit_event_signature_hash", if globN s "deposit_event_signature_hash" = 0 then 0 else 32), (globN s "history_storage_address", if globN s "history_storage_address" = 0 then 0 else 24), (globN s "precompile_addrs", if globN s "precompile_addrs" = 0 then 0 else 360), (globN s "withdrawal_request_address", if globN s "withdrawal_request_address" = 0 then 0 else 24), (globN s "zero32", if globN s "zero32" = 0 then 0 else 32)])
    ["beacon_roots_address", "builder_deposit_address", "builder_exit_address", "consolidation_request_address", "deposit_contract_address", "deposit_event_signature_hash", "heap_ptr", "history_storage_address", "precompile_addrs", "withdrawal_request_address", "zero32"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "fork_init") :=
  InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28.wk_fork_init

theorem «wk_header_init» :
    WorldKeeps WorldOK (fun s => [(globN s "hdr_zero8", if globN s "hdr_zero8" = 0 then 0 else 8)])
    ["hdr_zero8", "heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "header_init") :=
  InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28.wk_header_init

theorem «wk_keccak_init» :
    WorldKeeps WorldOK (fun s => [(globN s "keccak_rc", if globN s "keccak_rc" = 0 then 0 else 192)])
    ["heap_ptr", "keccak_pad", "keccak_rc", "keccak_st"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "keccak_init") :=
  InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28.wk_keccak_init

theorem «wk_mpt_init» :
    WorldKeeps WorldOK (fun s => [(globN s "empty_code_hash", if globN s "empty_code_hash" = 0 then 0 else 32), (globN s "empty_trie_root", if globN s "empty_trie_root" = 0 then 0 else 32), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40)])
    ["empty_code_hash", "empty_trie_root", "heap_ptr", "mpt_hash_scratch", "mpt_key_scratch", "mpt_nib_scratch"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "mpt_init") :=
  InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28.wk_mpt_init

theorem «wk_ripemd160_init» :
    WorldKeeps WorldOK (fun s => [(globN s "rmd_tab", if globN s "rmd_tab" = 0 then 0 else 160)])
    ["heap_ptr", "rmd_h", "rmd_pad", "rmd_tab", "rmd_x"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "ripemd160_init") :=
  InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28.wk_ripemd160_init

theorem «wk_sha256_init» :
    WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr", "sha_pad", "sha_st"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "sha256_init") :=
  InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28.wk_sha256_init

theorem «wk_ssz_init» :
    WorldKeeps WorldOK (fun s => [(globN s "zero_hashes", if globN s "zero_hashes" = 0 then 0 else 2048)])
    ["heap_ptr", "ssz_len_chunk", "ssz_offs", "zero_hashes"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "ssz_init") :=
  InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28.wk_ssz_init

theorem «wk_u256_ws_init» :
    WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr", "u256_ws"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "u256_ws_init") :=
  InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28.wk_u256_ws_init

theorem «zv_memzero» :
    ZeroFills (ofString "memzero") :=
  InitECandidate.Solver.Wave8Contracts.M29.«zv_memzero»

/-! ## Part 2: Small unmatched `C08` helper contracts -/

section NodeRlpArena
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential

private def encodingGood (f : MlS) : Bool :=
  (["_node_rlp_begin", "_node_rlp_finish", "alloc", "keccak256", "keccak_absorb_block",
    "keccak_f1600", "memcpy", "memzero", "mpt_fail", "nibble_list_to_compact",
    "node_hash_cached", "node_ref_len", "node_write_ref", "rlp_be_len",
    "rlp_bytes_encoded_len", "rlp_encode_bytes", "rlp_encode_list_header",
    "rlp_header_len", "rlp_list_header_len", "rlp_put_be", "rlp_value_encoded_len",
    "rlp_write_header", "trap_with"] : List String).map ofString |>.contains f

private def heapSafeProg : ProgHOL 64 → Bool
  | .dec _ _ _ body => heapSafeProg body
  | .seq first second => heapSafeProg first && heapSafeProg second
  | .ite _ yes no => heapSafeProg yes && heapSafeProg no
  | .while _ body => heapSafeProg body
  | .assign .local _ _ => true
  | .store _ _ | .storeByte _ _ | .shMemStore _ _ _ => true
  | .skip | .break | .continue | .annot _ _ | .raise _ _ | .return _ => true
  | .extCall _ _ _ _ _ | .primitive _ _ _ => true
  | .decCall _ _ function _ continuation => encodingGood function && heapSafeProg continuation
  | .call none function _ => encodingGood function
  | .call (some (none, none)) function _ => encodingGood function
  | .call (some (some (.local, _), none)) function _ => encodingGood function
  | _ => false

private theorem lookup_alloc_r10 :
    originalRuntimeCode.lookup (ofString "alloc") =
      some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_alloc, .one) :=
  lookup_of_guestAst_getElem 7 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_alloc) rfl

private theorem alloc_body_heap_mono {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hA : ArenaOK s) :
    let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)).2
    ArenaOK post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" := by
  dsimp only
  have hbody : sourceFnBody Guest.Software.guestFn_alloc =
      .dec (ofString "p") .one (.var .global (ofString "heap_ptr"))
        (.seq
          (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
              (.var .local (ofString "n")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1])
            .skip)
          (.dec (ofString "q") .one
            (.op .and [.op .add [.var .local (ofString "p"), .var .local (ofString "n"), .const 7],
              .op .sub [.const 0, .const 8]])
            (.seq
              (.ite (.cmp .lower (.const cMax) (.var .local (ofString "q")))
                (.call (some (none, none)) (ofString "trap_with") [.const 1])
                .skip)
              (.seq
                (.assign .global (ofString "heap_ptr") (.var .local (ofString "q")))
                (.return (.var .local (ofString "p"))))))) := rfl
  rcases hA with ⟨hp_lo, hp_hi, hfm_lo, hfm_hi, hsp_hi, hp_al, hfm_al, hsp_al, hgw_s⟩
  have hp_word : ∃ p : BitVec 64, s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) := by
    rcases hg : s.globals.lookup (ofString "heap_ptr") with _ | gv
    · simp [globN, hg, sourceBase] at hp_lo
    · rcases gv with ⟨⟨p⟩⟩ | _ | _
      · exact ⟨p, rfl⟩
      · simp [globN, hg, sourceBase] at hp_lo
      · simp [globN, hg, sourceBase] at hp_lo
  obtain ⟨p, hp_lk⟩ := hp_word
  have hp_glob : globN s "heap_ptr" = p.toNat := by simp [globN, hp_lk]
  have hsame : ∀ t : PanSemStateFiniteExact 64 F, t.globals = s.globals →
      ArenaOK t ∧ globN s "heap_ptr" ≤ globN t "heap_ptr" := by
    intro t hg
    exact ⟨arenaOK_congr hg ⟨hp_lo, hp_hi, hfm_lo, hfm_hi, hsp_hi, hp_al, hfm_al, hsp_al, hgw_s⟩,
      by simp [globN, hg]⟩
  have htrap_globals : ∀ t : PanSemStateFiniteExact 64 F, t.code = originalRuntimeCode →
      (evaluateHOLFiniteState t (.call (some (none, none)) (ofString "trap_with") [.const 1])).2.globals = t.globals := by
    intro t htc
    apply HolFiniteMapExact.ext_lookup
    intro key
    refine InitECandidate.Solver.GuestGlobalKeep.evaluate_keepsG key (fun f => f == ofString "trap_with") ?_ _ rfl t htc
    intro f hf vs b callee rs hl
    have hfn : f = ofString "trap_with" := by simpa only [beq_iff_eq] using hf
    subst hfn
    have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ b _ rs vs callee lookup_trap_with hl
    subst hb; rfl
  rw [hbody, evaluateHOLFiniteState_dec_total]
  have hp_ev : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .global (ofString "heap_ptr")) = some (.val (.word p)) := hp_lk
  dsimp only; rw [hp_ev]; dsimp only
  have hsh_p : shapeEqHOL .one (shapeOfHOLExact (.val (.word p))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos hsh_p]; dsimp only
  let pState := setVarHOLFinite (ofString "p") (.val (.word p)) s
  have hp_loc : pState.locals.lookup (ofString "p") = some (.val (.word p)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hn_lk : s.locals.lookup (ofString "n") with _ | nv
  · have hnl : pState.locals.lookup (ofString "n") = none := by
      simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn_lk,
        show ofString "p" ≠ ofString "n" by decide]
    have herr : evaluateHOLFiniteState pState
        (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const 1])
          .skip) = (some .error, pState) := by
      rw [evaluateHOLFiniteState_ite]; simp [evalHOLExact, evalListHOLExact, hnl]
    rw [herr]; exact hsame _ rfl
  · rcases nv with ⟨⟨n⟩⟩ | fs | ⟨nm, fs⟩
    · have hn_loc : pState.locals.lookup (ofString "n") = some (.val (.word n)) := by
        simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn_lk,
          show ofString "p" ≠ ofString "n" by decide]
      have hev1 : @evalHOLExact 64 F _ pState.toExact
          (fun a => Classical.propDecidable (pState.memaddrs a))
          (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
            (.var .local (ofString "n"))) =
          some (.val (.word (if (cMax - p).toNat < n.toNat then 1 else 0))) := by
        simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
          Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]; rfl
      by_cases hcmp1 : (cMax - p).toNat < n.toNat
      · have hite1 : evaluateHOLFiniteState pState
            (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
                (.var .local (ofString "n")))
              (.call (some (none, none)) (ofString "trap_with") [.const 1])
              .skip) =
            evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 1]) := by
          rw [evaluateHOLFiniteState_ite, hev1, if_pos hcmp1]; simp
        rw [hite1]
        have hno_none := evaluate_call_trap_with_no_none pState 1 hc
        have htg := htrap_globals pState hc
        rcases htr : evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r1, s1⟩
        rw [htr] at hno_none htg
        cases r1 with
        | none => exact absurd rfl hno_none
        | some _ => exact hsame _ htg
      · have hite1 : evaluateHOLFiniteState pState
            (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
                (.var .local (ofString "n")))
              (.call (some (none, none)) (ofString "trap_with") [.const 1])
              .skip) = (none, pState) := by
          rw [evaluateHOLFiniteState_ite, hev1, if_neg hcmp1]; simp [evaluateHOLFiniteState_skip]
        rw [hite1]; dsimp only; rw [evaluateHOLFiniteState_dec_total]
        let q : BitVec 64 := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
        have hq_eval : @evalHOLExact 64 F _ pState.toExact
            (fun a => Classical.propDecidable (pState.memaddrs a))
            (.op .and [.op .add [.var .local (ofString "p"), .var .local (ofString "n"), .const 7],
              .op .sub [.const 0, .const 8]]) = some (.val (.word q)) := by
          simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
            wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
          exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word w))) (alloc_q_word_eq p n)
        dsimp only; rw [hq_eval]; dsimp only
        have hsh_q : shapeEqHOL .one (shapeOfHOLExact (.val (.word q))) = true := by
          simp [shapeEqHOL, shapeOfHOLExact]
        rw [if_pos hsh_q]; dsimp only
        let qState := setVarHOLFinite (ofString "q") (.val (.word q)) pState
        have hq_loc : qState.locals.lookup (ofString "q") = some (.val (.word q)) := by
          simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hp_loc_q : qState.locals.lookup (ofString "p") = some (.val (.word p)) := by
          simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp_loc,
            show ofString "q" ≠ ofString "p" by decide]
        rw [evaluateHOLFiniteState_seq_line780]
        have hev2 : @evalHOLExact 64 F _ qState.toExact
            (fun a => Classical.propDecidable (qState.memaddrs a))
            (.cmp .lower (.const cMax) (.var .local (ofString "q"))) =
            some (.val (.word (if cMax.toNat < q.toNat then 1 else 0))) := by
          simp only [evalHOLExact, hq_loc, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
        by_cases hcmp2 : cMax.toNat < q.toNat
        · have hite2 : evaluateHOLFiniteState qState
              (.ite (.cmp .lower (.const cMax) (.var .local (ofString "q")))
                (.call (some (none, none)) (ofString "trap_with") [.const 1])
                .skip) =
              evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 1]) := by
            rw [evaluateHOLFiniteState_ite, hev2, if_pos hcmp2]; simp
          rw [hite2]
          have hno_none := evaluate_call_trap_with_no_none qState 1 hc
          have htg := htrap_globals qState hc
          rcases htr : evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r2, s2⟩
          rw [htr] at hno_none htg
          cases r2 with
          | none => exact absurd rfl hno_none
          | some _ => exact hsame _ htg
        · have hite2 : evaluateHOLFiniteState qState
              (.ite (.cmp .lower (.const cMax) (.var .local (ofString "q")))
                (.call (some (none, none)) (ofString "trap_with") [.const 1])
                .skip) = (none, qState) := by
            rw [evaluateHOLFiniteState_ite, hev2, if_neg hcmp2]; simp [evaluateHOLFiniteState_skip]
          rw [hite2]; dsimp only
          have hp_g : qState.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) := hp_lk
          have heval_end : evaluateHOLFiniteState qState
              (.seq (.assign .global (ofString "heap_ptr") (.var .local (ofString "q")))
                (.return (.var .local (ofString "p")))) =
              (some (.returned (.val (.word p))),
                emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word q)) qState)) := by
            rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
            simp [evalHOLExact, hq_loc, hp_loc_q, isValidValueHOLExact, lookupKvarHOLExact, hp_g,
              shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite,
              evaluateHOLFiniteState_return, sizeOfShapeWithContextHOL]
          rw [heval_end]; dsimp only
          have hcMax_val : cMax.toNat = 2952790016 := rfl
          have hhl_val : heapLimit = 2952790016 := rfl
          have hp_le_cMax : p.toNat ≤ cMax.toNat := by omega
          have hsub_toNat : (cMax - p).toNat = cMax.toNat - p.toNat := by
            rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hp_le_cMax)]
          have h7 : (7 : BitVec 64).toNat = 7 := rfl
          have hn7 : (n + 7).toNat = n.toNat + 7 := by rw [BitVec.toNat_add, h7]; omega
          have hsum : (p + (n + 7)).toNat = p.toNat + n.toNat + 7 := by rw [BitVec.toNat_add, hn7]; omega
          have hq_toNat : q.toNat = (p.toNat + n.toNat + 7) / 8 * 8 := by
            have hq1 := and_neg8_toNat (p + (n + 7))
            change q.toNat = _ at hq1
            rw [hq1, hsum]
          set fin := emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word q)) qState)
          have hfin_hp : globN fin "heap_ptr" = q.toNat := by
            simp [fin, globN, emptyLocalsHOLFinite, setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hfin_fm : globN fin "frame_mem_ptr" = globN s "frame_mem_ptr" := by
            simp [fin, qState, pState, globN, emptyLocalsHOLFinite, setGlobalHOLFinite, setVarHOLFinite,
              HolFiniteMapExact.lookup_update, FUPDATE, show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide]
          have hfin_sp : globN fin "scratch_ptr" = globN s "scratch_ptr" := by
            simp [fin, qState, pState, globN, emptyLocalsHOLFinite, setGlobalHOLFinite, setVarHOLFinite,
              HolFiniteMapExact.lookup_update, FUPDATE, show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
          change ArenaOK { fin with locals := _ } ∧ globN s "heap_ptr" ≤ globN { fin with locals := _ } "heap_ptr"
          have hfin_ok : ArenaOK fin := by
            unfold ArenaOK
            rw [hfin_hp, hfin_fm, hfin_sp]
            exact ⟨by omega, by omega, hfm_lo, hfm_hi, hsp_hi, by omega, hfm_al, hsp_al,
              globalsWord_update (s := s) (t := fin) (ofString "heap_ptr") q rfl hgw_s⟩
          have hfin_le : globN s "heap_ptr" ≤ globN fin "heap_ptr" := by
            rw [hp_glob, hfin_hp]; omega
          exact ⟨hfin_ok, hfin_le⟩
    · have hnl : pState.locals.lookup (ofString "n") = some (.rStruct fs) := by
        simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn_lk,
          show ofString "p" ≠ ofString "n" by decide]
      have herr : evaluateHOLFiniteState pState
          (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
              (.var .local (ofString "n")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1])
            .skip) = (some .error, pState) := by
        rw [evaluateHOLFiniteState_ite]; simp [evalHOLExact, evalListHOLExact, hnl, valueIsWord]
      rw [herr]; exact hsame _ rfl
    · have hnl : pState.locals.lookup (ofString "n") = some (.nStruct nm fs) := by
        simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn_lk,
          show ofString "p" ≠ ofString "n" by decide]
      have herr : evaluateHOLFiniteState pState
          (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
              (.var .local (ofString "n")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1])
            .skip) = (some .error, pState) := by
        rw [evaluateHOLFiniteState_ite]; simp [evalHOLExact, evalListHOLExact, hnl, valueIsWord]
      rw [herr]; exact hsame _ rfl

private theorem encoding_body_heapSafe (f : MlS) (hf : encodingGood f = true)
    (values : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (rs : ShapeHOL)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body, callee, rs)) :
    (f = ofString "alloc" ∧ body = sourceFnBody Guest.Software.guestFn_alloc) ∨
      heapSafeProg body = true := by
  simp only [encodingGood, List.map_cons, List.map_nil, List.contains_cons, List.contains_nil,
    Bool.or_eq_true, beq_iff_eq, Bool.false_eq_true, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 281 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn__node_rlp_begin) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 282 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn__node_rlp_finish) rfl) hl; subst hb; rfl
  · left; exact ⟨rfl, lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee lookup_alloc_r10 hl⟩
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 103 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_keccak256) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 102 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_keccak_absorb_block) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 101 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_keccak_f1600) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 16 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_memcpy) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 17 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_memzero) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 246 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_mpt_fail) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 250 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_nibble_list_to_compact) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 288 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_node_hash_cached) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 287 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_node_ref_len) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 289 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_node_write_ref) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 118 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_rlp_be_len) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 125 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_rlp_bytes_encoded_len) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 122 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_rlp_encode_bytes) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 124 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_rlp_encode_list_header) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 121 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_rlp_header_len) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 126 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_rlp_list_header_len) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 119 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_rlp_put_be) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 286 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_rlp_value_encoded_len) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 120 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_rlp_write_header) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee lookup_trap_with hl; subst hb; rfl

private theorem arenaOK_congr_globals {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (hg : t.globals = s.globals) (h : ArenaOK s) : ArenaOK t :=
  arenaOK_congr hg h

private theorem evaluate_heapSafeProg {F : Type} (program : ProgHOL 64)
    (supported : heapSafeProg program = true)
    (state : PanSemStateFiniteExact 64 F) (code : state.code = originalRuntimeCode)
    (hA : ArenaOK state) :
    ArenaOK (evaluateHOLFiniteState state program).2 ∧
      globN state "heap_ptr" ≤ globN (evaluateHOLFiniteState state program).2 "heap_ptr" := by
  cases shape : program with
  | skip => rw [evaluateHOLFiniteState_skip]; exact ⟨hA, Nat.le_refl _⟩
  | dec name kind initializer body =>
    have child : heapSafeProg body = true := by simpa only [shape, heapSafeProg] using supported
    rw [evaluateHOLFiniteState_dec_total]; dsimp only
    split
    · exact ⟨hA, Nat.le_refl _⟩
    · rename_i val _
      split
      · obtain ⟨hAb, hle⟩ := evaluate_heapSafeProg body child (setVarHOLFinite name val state) code hA
        exact ⟨arenaOK_congr_globals rfl hAb, hle⟩
      · exact ⟨hA, Nat.le_refl _⟩
  | decCall name kind function arguments continuation =>
    have children : encodingGood function = true ∧ heapSafeProg continuation = true := by
      simpa only [shape, heapSafeProg, Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_decCall_total]
    split
    · exact ⟨hA, Nat.le_refl _⟩
    · rename_i values _
      split
      · exact ⟨hA, Nat.le_refl _⟩
      · rename_i body callee rs found
        rw [code] at found
        split
        · exact ⟨hA, Nat.le_refl _⟩
        · rename_i nonzero
          dsimp only
          have hbodyA : ArenaOK (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).2 ∧
              globN state "heap_ptr" ≤ globN (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).2 "heap_ptr" := by
            rcases encoding_body_heapSafe function children.1 values body callee rs found with ⟨_, rfl⟩ | hsafe
            · exact alloc_body_heap_mono (callEntryStateHOLFinite state callee) code hA
            · exact evaluate_heapSafeProg body hsafe (callEntryStateHOLFinite state callee) code hA
          have meta' := InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) body
          have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
          generalize evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = out at hbodyA meta' cl
          obtain ⟨r, st⟩ := out
          dsimp only at hbodyA meta' cl ⊢
          change st.clock ≤ state.clock - 1 at cl
          have stCode : st.code = originalRuntimeCode := meta'.1.trans code
          rcases r with _ | (_ | _ | _ | _ | v | _ | _)
          all_goals (dsimp only [fixClockHOLFinite])
          all_goals (try exact hbodyA)
          split
          · have small : (if state.clock - 1 < st.clock then state.clock - 1 else st.clock) < state.clock := by
              split <;> omega
            let resumed : PanSemStateFiniteExact 64 F :=
              setVarHOLFinite name v
                { st with locals := state.locals,
                          clock := if (callEntryStateHOLFinite state callee).clock < st.clock
                                   then (callEntryStateHOLFinite state callee).clock else st.clock }
            obtain ⟨hAc, hlec⟩ := evaluate_heapSafeProg continuation children.2 resumed
              stCode (arenaOK_congr_globals rfl hbodyA.1)
            exact ⟨arenaOK_congr_globals rfl hAc, Nat.le_trans hbodyA.2 hlec⟩
          · exact hbodyA
  | assign kind name value =>
    cases kind with
    | global => simp [shape, heapSafeProg] at supported
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · exact ⟨hA, Nat.le_refl _⟩
      · split <;> exact ⟨arenaOK_congr_globals rfl hA, Nat.le_refl _⟩
  | seq first second =>
    have children : heapSafeProg first = true ∧ heapSafeProg second = true := by
      simpa only [shape, heapSafeProg, Bool.and_eq_true] using supported
    have hA1 := evaluate_heapSafeProg first children.1 state code hA
    have remaining := evaluateHOLFiniteState_clock_le state first
    have meta' := InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata state first
    rw [evaluateHOLFiniteState_seq_line780]
    cases firstRun : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [firstRun] at hA1 remaining meta'
      dsimp only at hA1 remaining meta'
      cases result with
      | none =>
        have _mclock : middle.clock ≤ state.clock := remaining
        obtain ⟨hA2, hle2⟩ := evaluate_heapSafeProg second children.2 middle (meta'.1.trans code) hA1.1
        exact ⟨hA2, Nat.le_trans hA1.2 hle2⟩
      | some _ => exact hA1
  | ite condition yes no =>
    have children : heapSafeProg yes = true ∧ heapSafeProg no = true := by
      simpa only [shape, heapSafeProg, Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_heapSafeProg no children.2 state code hA
      · exact evaluate_heapSafeProg yes children.1 state code hA
    · exact ⟨hA, Nat.le_refl _⟩
  | «while» condition body =>
    have child : heapSafeProg body = true := by simpa only [shape, heapSafeProg] using supported
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · exact ⟨hA, Nat.le_refl _⟩
        · rename_i nonzero
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have hAb := evaluate_heapSafeProg body child (decClockHOLFinite state) code hA
          have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body
          have meta' := InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata (decClockHOLFinite state) body
          cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
          | mk result middle =>
            rw [bodyRun] at hAb remaining meta'
            dsimp only at hAb remaining meta'
            have _smaller : middle.clock < state.clock := by
              change middle.clock ≤ state.clock - 1 at remaining; omega
            have mCode : middle.code = originalRuntimeCode := meta'.1.trans code
            cases result with
            | none =>
              obtain ⟨hAw, hlew⟩ := evaluate_heapSafeProg (.while condition body) (by simpa [heapSafeProg] using child) middle mCode hAb.1
              exact ⟨hAw, Nat.le_trans hAb.2 hlew⟩
            | some r =>
              cases r with
              | «continue» =>
                obtain ⟨hAw, hlew⟩ := evaluate_heapSafeProg (.while condition body) (by simpa [heapSafeProg] using child) middle mCode hAb.1
                exact ⟨hAw, Nat.le_trans hAb.2 hlew⟩
              | _ => exact hAb
      · exact ⟨hA, Nat.le_refl _⟩
    · exact ⟨hA, Nat.le_refl _⟩
  | «break» => rw [evaluateHOLFiniteState_break]; exact ⟨hA, Nat.le_refl _⟩
  | «continue» => rw [evaluateHOLFiniteState_continue]; exact ⟨hA, Nat.le_refl _⟩
  | annot tag text => rw [evaluateHOLFiniteState_annot]; exact ⟨hA, Nat.le_refl _⟩
  | raise name value =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> exact ⟨hA, Nat.le_refl _⟩
    · exact ⟨hA, Nat.le_refl _⟩
  | «return» value =>
    rw [evaluateHOLFiniteState_return]
    split
    · exact ⟨hA, Nat.le_refl _⟩
    · split <;> exact ⟨hA, Nat.le_refl _⟩
  | store destination value =>
    rw [evaluateHOLFiniteState_store]
    split <;> try exact ⟨hA, Nat.le_refl _⟩
    split <;> try exact ⟨hA, Nat.le_refl _⟩
    split <;> exact ⟨hA, Nat.le_refl _⟩
  | storeByte destination value =>
    rw [evaluateHOLFiniteState_storeByte]
    split <;> try exact ⟨hA, Nat.le_refl _⟩
    split <;> try exact ⟨hA, Nat.le_refl _⟩
    split <;> exact ⟨hA, Nat.le_refl _⟩
  | shMemStore op a v =>
    have hg : (evaluateHOLFiniteState state (.shMemStore op a v)).2.globals = state.globals := by
      apply HolFiniteMapExact.ext_lookup
      intro k; exact InitECandidate.Solver.GuestGlobalKeep.shMemStore_globals state op a v k
    exact ⟨arenaOK_congr_globals hg hA, by unfold globN; rw [hg]⟩
  | extCall name a b c d =>
    rw [evaluateHOLFiniteState_extCall_source]
    split <;> try exact ⟨hA, Nat.le_refl _⟩
    split <;> try exact ⟨hA, Nat.le_refl _⟩
    split <;> exact ⟨arenaOK_congr_globals (by simp [emptyLocalsHOLFinite, ofExact, toExact]) hA,
      by simp [globN, emptyLocalsHOLFinite, ofExact, toExact]⟩
  | primitive name op args =>
    rw [evaluateHOLFiniteState_primitive]
    split <;> try exact ⟨hA, Nat.le_refl _⟩
    split <;> try exact ⟨hA, Nat.le_refl _⟩
    split <;> exact ⟨hA, Nat.le_refl _⟩
  | call info function arguments =>
    have hk : encodingGood function = true ∧
        (info = none ∨ info = some (none, none) ∨ ∃ nm, info = some (some (.local, nm), none)) := by
      rcases info with _ | ⟨_ | ⟨kind, nm⟩, _ | _⟩
      · exact ⟨by simpa [shape, heapSafeProg] using supported, Or.inl rfl⟩
      · exact ⟨by simpa [shape, heapSafeProg] using supported, Or.inr (Or.inl rfl)⟩
      · simp [shape, heapSafeProg] at supported
      · cases kind
        · exact ⟨by simpa [shape, heapSafeProg] using supported, Or.inr (Or.inr ⟨nm, rfl⟩)⟩
        · simp [shape, heapSafeProg] at supported
      · simp [shape, heapSafeProg] at supported
    rw [evaluateHOLFiniteState_call]
    split
    · exact ⟨hA, Nat.le_refl _⟩
    · rename_i values _
      split
      · exact ⟨hA, Nat.le_refl _⟩
      · rename_i body callee rs found
        rw [code] at found
        split
        · exact ⟨hA, Nat.le_refl _⟩
        · rename_i nonzero
          have hbodyA : let out := (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).2
              ArenaOK out ∧ globN state "heap_ptr" ≤ globN out "heap_ptr" := by
            rcases encoding_body_heapSafe function hk.1 values body callee rs found with ⟨_, rfl⟩ | hsafe
            · exact alloc_body_heap_mono (callEntryStateHOLFinite state callee) code hA
            · exact evaluate_heapSafeProg body hsafe (callEntryStateHOLFinite state callee) code hA
          generalize evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = out at hbodyA
          obtain ⟨r, st⟩ := out
          dsimp only at hbodyA ⊢
          rcases hk.2 with rfl | rfl | ⟨nm, rfl⟩
          · rcases r with _ | (_ | _ | _ | _ | v | _ | _) <;> dsimp only <;> (repeat' split) <;>
              exact ⟨arenaOK_congr_globals (by simp [emptyLocalsHOLFinite]) hbodyA.1,
                by simpa [globN, emptyLocalsHOLFinite] using hbodyA.2⟩
          · rcases r with _ | (_ | _ | _ | _ | v | _ | _) <;> dsimp only <;> (repeat' split) <;>
              exact ⟨arenaOK_congr_globals (by simp [emptyLocalsHOLFinite]) hbodyA.1,
                by simpa [globN, emptyLocalsHOLFinite] using hbodyA.2⟩
          · rcases r with _ | (_ | _ | _ | _ | v | _ | _) <;> dsimp only <;> (repeat' split) <;>
              exact ⟨arenaOK_congr_globals (by simp [setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite]) hbodyA.1,
                by simpa [globN, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite] using hbodyA.2⟩
  | _ => simp [shape, heapSafeProg] at supported
termination_by (state.clock, sizeOf program)
decreasing_by
  all_goals
    simp_wf
    apply InitECandidate.Solver.GuestGlobalKeep.lex_of
    try subst shape
    try simp only [setVarHOLFinite, decClockHOLFinite, callEntryStateHOLFinite, ProgHOL.seq.sizeOf_spec,
      ProgHOL.ite.sizeOf_spec, ProgHOL.dec.sizeOf_spec, ProgHOL.while.sizeOf_spec, ProgHOL.decCall.sizeOf_spec, true_and]
    first
      | exact Or.inl small
      | omega

end NodeRlpArena

theorem «ak__node_rlp_begin» :
    KeepsOn ArenaReady ArenaReady (ofString "_node_rlp_begin") := by
  refine ⟨_, _, _,
    InitECandidate.Solver.GuestTrapAndLookup.lookup_of_guestAst_getElem 281
      (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn__node_rlp_begin) rfl, ?_⟩
  intro F s hc hAR _ _ _
  exact ⟨guestInv_evaluate s _ hAR.1,
    (evaluate_heapSafeProg _ rfl s hc hAR.2).1⟩

theorem «ak__node_rlp_finish» :
    KeepsOn ArenaReady ArenaReady (ofString "_node_rlp_finish") := by
  refine ⟨_, _, _,
    InitECandidate.Solver.GuestTrapAndLookup.lookup_of_guestAst_getElem 282
      (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn__node_rlp_finish) rfl, ?_⟩
  intro F s hc hAR _ _ _
  exact ⟨guestInv_evaluate s _ hAR.1,
    (evaluate_heapSafeProg _ rfl s hc hAR.2).1⟩

section RtMptNew
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.Wave8Contracts.M26
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28

private theorem lookup_mpt_new_r10 :
    originalRuntimeCode.lookup (ofString "mpt_new") =
      some ([(ofString "root_node", .one), (ofString "secured", .one)],
        sourceFnBody Guest.Software.guestFn_mpt_new, .one) :=
  lookup_of_guestAst_getElem 268 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_mpt_new) rfl

theorem «rt_mpt_new» :
    Returns ArenaReady (fun s post m => FreshBlock s post m 16 ∧
      memW post m = locN s "root_node" ∧ memW post (m + 8) = locN s "secured")
    (ofString "mpt_new") := by
  refine ⟨_, _, _, lookup_mpt_new_r10, ?_⟩
  intro F s hcode hAR hlookup _hnt v hret
  obtain ⟨vals, hvals⟩ := hlookup
  obtain ⟨w_rn, w_sec, _, hrn_s, hsec_s⟩ :=
    lookupCode_two_words (by decide) lookup_mpt_new_r10 hvals
  obtain ⟨hG, hA⟩ := hAR
  obtain ⟨hp, fp, sp, hhp, hhp_eq, hfp, hfp_eq, hsp, hsp_eq⟩ := arenaOK_globals s hA
  have hbody : sourceFnBody Guest.Software.guestFn_mpt_new =
      .decCall (ofString "m") .one (ofString "alloc") [.const 16]
        (.seq (.store (.op .add [.var .local (ofString "m"), .const 0]) (.var .local (ofString "root_node")))
          (.seq (.store (.op .add [.var .local (ofString "m"), .const 8]) (.var .local (ofString "secured")))
            (.return (.var .local (ofString "m"))))) := rfl
  have hrun : Ret s (sourceFnBody Guest.Software.guestFn_mpt_new)
      (fun rv post => ∃ w : BitVec 64, rv = .val (.word w) ∧
        ArenaReady post ∧ AllocatorGrows s post ∧
        FreshBlock s post w.toNat 16 ∧
        memW post w.toNat = locN s "root_node" ∧ memW post (w.toNat + 8) = locN s "secured") := by
    rw [hbody]
    apply Ret.of_NS
    refine Ret.ns_alloc hcode 16 rfl hp hhp ?_
    intro hcmp1 hcmp2
    set q : BitVec 64 := (hp + (16 + 7)) &&& ((0 : BitVec 64) - 8)
    set L1 := s.locals.update (ofString "m", .val (.word hp))
    set G1 := s.globals.update (ofString "heap_ptr", .val (.word q))
    have hev_m0 : ev (NS s L1 G1 s.memory (s.clock - 1))
        (.op .add [.var .local (ofString "m"), .const 0]) = some (.val (.word (hp + 0))) := by
      simp [ev, evalHOLExact, evalListHOLExact, L1, HolFiniteMapExact.lookup_update, FUPDATE,
        valueIsWord, valueWord, wordOpHOL, wordOp]
    have hev_rn : ev (NS s L1 G1 s.memory (s.clock - 1))
        (.var .local (ofString "root_node")) = some (.val (.word w_rn)) := by
      simp [ev, evalHOLExact, L1, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "m" ≠ ofString "root_node" by decide, hrn_s]
    refine Ret.ns_storeW (hp + 0) w_rn hev_m0 hev_rn ?_
    intro _hdom0
    set M1 := updW s.memory (hp + 0) w_rn
    have hev_m8 : ev (NS s L1 G1 M1 (s.clock - 1))
        (.op .add [.var .local (ofString "m"), .const 8]) = some (.val (.word (hp + 8))) := by
      simp [ev, evalHOLExact, evalListHOLExact, L1, HolFiniteMapExact.lookup_update, FUPDATE,
        valueIsWord, valueWord, wordOpHOL, wordOp]
    have hev_sec : ev (NS s L1 G1 M1 (s.clock - 1))
        (.var .local (ofString "secured")) = some (.val (.word w_sec)) := by
      simp [ev, evalHOLExact, L1, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "m" ≠ ofString "secured" by decide, hsec_s]
    refine Ret.ns_storeW (hp + 8) w_sec hev_m8 hev_sec ?_
    intro _hdom8
    set M2 := updW M1 (hp + 8) w_sec
    refine Ret.ns_ret ?_
    intro val hval
    have hval_eq : val = .val (.word hp) := by
      simp [ev, evalHOLExact, L1, HolFiniteMapExact.lookup_update, FUPDATE] at hval
      exact hval.symm
    subst hval_eq
    refine ⟨hp, rfl, ?_⟩
    set post : PanSemStateFiniteExact 64 F :=
      { locals := HolFiniteMapExact.resVarEq
          (emptyLocalsHOLFinite (NS s L1 G1 M2 (s.clock - 1))).locals
          (ofString "m", s.locals.lookup (ofString "m")),
        globals := G1,
        structs := s.structs,
        code := s.code,
        eshapes := s.eshapes,
        memory := M2,
        memaddrs := s.memaddrs,
        shMemaddrs := s.shMemaddrs,
        clock := s.clock - 1,
        be := s.be,
        ffi := s.ffi,
        baseAddr := s.baseAddr,
        topAddr := s.topAddr }
    have hhp_hi : hp.toNat ≤ heapLimit := by rw [hhp_eq]; exact hA.2.1
    have hhp_al : hp.toNat % 8 = 0 := by rw [hhp_eq]; exact hA.2.2.2.2.2.1
    obtain ⟨hq_eq, hq_hi, hq_al, hp_le_q⟩ := alloc_arith hp 16 hhp_hi hhp_al hcmp1 hcmp2
    change q.toNat = _ at hq_eq
    change q.toNat ≤ heapLimit at hq_hi
    change q.toNat % 8 = 0 at hq_al
    change hp.toNat ≤ q.toNat at hp_le_q
    have h16 : ((16 : BitVec 64).toNat + 7) / 8 * 8 = 16 := by decide
    rw [h16] at hq_eq
    have hpost_hp : globN post "heap_ptr" = q.toNat := by
      simp [post, G1, globN, HolFiniteMapExact.lookup_update, FUPDATE]
    have hpost_fp : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := by
      simp [post, G1, globN, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide]
    have hpost_sp : globN post "scratch_ptr" = globN s "scratch_ptr" := by
      simp [post, G1, globN, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
    have hG_post : GuestInv post := ⟨hG.code, hG.memaddrs, hG.shMemaddrs, hG.baseAddr⟩
    have hsb_le : sourceBase ≤ hp.toNat := by rw [hhp_eq]; exact hA.1
    have hA_post : ArenaOK post := by
      unfold ArenaOK
      rw [hpost_hp, hpost_fp, hpost_sp]
      exact ⟨by omega, hq_hi, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2.1, hq_al, hA.2.2.2.2.2.2.1,
        hA.2.2.2.2.2.2.2.1,
        globalsWord_update (s := s) (t := post) (ofString "heap_ptr") q rfl hA.2.2.2.2.2.2.2.2⟩
    have hAG : AllocatorGrows s post := by
      refine ⟨?_, by rw [hpost_sp]⟩
      rw [hpost_hp, ← hhp_eq]; exact hp_le_q
    have hlim_le_he : heapLimit ≤ heapEnd := by decide
    have hFB : FreshBlock s post hp.toNat 16 := by
      refine ⟨hhp_al, ?_, ?_⟩
      · change Inside (hp.toNat, 16) (globN s "heap_ptr") (globN post "heap_ptr")
        rw [← hhp_eq, hpost_hp]
        exact ⟨le_rfl, le_of_eq hq_eq.symm⟩
      · change WordsOK post (hp.toNat, 16)
        exact wordsOK_of_guestInv post hG_post hp.toNat 16 hhp_al (by decide) hsb_le (by omega)
    have hp0_ne_8 : hp + 0 ≠ hp + 8 := by
      intro h; have h1 := congrArg BitVec.toNat h; simp [BitVec.toNat_add] at h1; omega
    have hp_eq_0 : BitVec.ofNat 64 hp.toNat = hp + 0 := by simp [BitVec.ofNat_toNat]
    have hp8_eq : BitVec.ofNat 64 (hp.toNat + 8) = hp + 8 := ofNat_add_toNat_eq hp 8
    have hmem0 : memW post hp.toNat = locN s "root_node" := by
      simp only [locN, hrn_s]
      unfold memW
      change (match M2 (BitVec.ofNat 64 hp.toNat) with | .word w => w.toNat) = w_rn.toNat
      rw [show M2 (BitVec.ofNat 64 hp.toNat) = .word w_rn by
        rw [hp_eq_0]; simp only [M2, M1, updW, hp0_ne_8, ↓reduceIte]]
    have hmem8 : memW post (hp.toNat + 8) = locN s "secured" := by
      simp only [locN, hsec_s]
      unfold memW
      change (match M2 (BitVec.ofNat 64 (hp.toNat + 8)) with | .word w => w.toNat) = w_sec.toNat
      rw [show M2 (BitVec.ofNat 64 (hp.toNat + 8)) = .word w_sec by
        rw [hp8_eq]; simp only [M2, updW, ↓reduceIte]]
    exact ⟨⟨hG_post, hA_post⟩, hAG, hFB, hmem0, hmem8⟩
  exact hrun v hret

end RtMptNew

section KeyToNibblesAndMptNibbleKey
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28

private theorem lookup_resVarEq_ne (m : HolFiniteMapExact MlS (ValueHOL 64))
    (x k : MlS) (ox : Option (ValueHOL 64)) (hne : k ≠ x) :
    (m.resVarEq (x, ox)).lookup k = m.lookup k := by
  simp only [HolFiniteMapExact.resVarEq]
  cases ox <;> simp [FDOMSUB_HOL, FUPDATE_HOL, hne, Ne.symm hne]

private def KeyNibInv {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (key0 n0 out0 : BitVec 64) (s : PanSemStateFiniteExact 64 F) : Prop :=
  s.code = originalRuntimeCode ∧ GuestInv s ∧
  ByteEff s0 s [(out0.toNat, 2 * n0.toNat)] ∧
  s.locals.lookup (ofString "key") = some (.val (.word key0)) ∧
  s.locals.lookup (ofString "n") = some (.val (.word n0)) ∧
  s.locals.lookup (ofString "out") = some (.val (.word out0)) ∧
  ∃ iw : BitVec 64,
    s.locals.lookup (ofString "i") = some (.val (.word iw)) ∧
    iw.toNat ≤ n0.toNat ∧
    (0 < iw.toNat → sourceBase ≤ out0.toNat ∧ out0.toNat + 2 * iw.toNat ≤ heapEnd)

private theorem noRetOrRaise_seq {F : Type} {a b : ProgHOL 64} {s : PanSemStateFiniteExact 64 F}
    (ha : ¬ Resumes (evaluateHOLFiniteState s a).1)
    (hb : ∀ m, (evaluateHOLFiniteState s a) = (none, m) → ¬ Resumes (evaluateHOLFiniteState m b).1) :
    ¬ Resumes (evaluateHOLFiniteState s (.seq a b)).1 := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hr : evaluateHOLFiniteState s a with ⟨r1, m⟩
  rw [hr] at ha
  cases r1 with
  | none => exact hb m hr
  | some _ => exact ha

private theorem noRetOrRaise_storeByte {F : Type} (s : PanSemStateFiniteExact 64 F) (d e : ExpHOL 64) :
    ¬ Resumes (evaluateHOLFiniteState s (.storeByte d e)).1 := by
  rw [evaluateHOLFiniteState_storeByte]
  repeat' split
  all_goals (rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)

private theorem noRetOrRaise_assign {F : Type} (s : PanSemStateFiniteExact 64 F) (k : VarKind) (nm : MlS) (e : ExpHOL 64) :
    ¬ Resumes (evaluateHOLFiniteState s (.assign k nm e)).1 := by
  rw [evaluateHOLFiniteState_assign]
  repeat' split
  all_goals (rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)

private theorem noRetOrRaise_dec {F : Type} (s : PanSemStateFiniteExact 64 F) (nm : MlS) (sh : ShapeHOL) (e : ExpHOL 64)
    {b : ProgHOL 64} (hb : ∀ v, ¬ Resumes (evaluateHOLFiniteState (setVarHOLFinite nm v s) b).1) :
    ¬ Resumes (evaluateHOLFiniteState s (.dec nm sh e b)).1 := by
  rw [evaluateHOLFiniteState_dec_total]; dsimp only
  split
  · exact not_resumes_error
  · rename_i v _; split
    · exact hb v
    · exact not_resumes_error

private theorem noRetOrRaise_while {F : Type} (cond : ExpHOL 64) (body : ProgHOL 64)
    (hb : ∀ t : PanSemStateFiniteExact 64 F, ¬ Resumes (evaluateHOLFiniteState t body).1)
    (k : Nat) (s : PanSemStateFiniteExact 64 F) (hk : s.clock ≤ k) :
    ¬ Resumes (evaluateHOLFiniteState s (.while cond body)).1 := by
  induction k generalizing s with
  | zero =>
    rw [evaluateHOLFiniteState_while_total]
    repeat' split
    all_goals (try omega)
    all_goals (rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
  | succ k ih =>
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
        · dsimp only; rw [fixClockHOLFinite_evaluateState]
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          have hnb := hb (decClockHOLFinite s)
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at rem hnb
          have hlt : mid.clock ≤ k := by change mid.clock ≤ s.clock - 1 at rem; omega
          cases r1 with
          | none => exact ih mid hlt
          | some res =>
            cases res with
            | «continue» => exact ih mid hlt
            | «break» => rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
            | _ => exact hnb
      · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
    · exact not_resumes_error

private theorem while_keyNibInv {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {key0 n0 out0 : BitVec 64}
    (cond : ExpHOL 64) (body : ProgHOL 64)
    (hnobc : ∀ t : PanSemStateFiniteExact 64 F,
      (evaluateHOLFiniteState t body).1 ≠ some .break ∧
      (evaluateHOLFiniteState t body).1 ≠ some .continue)
    (hstep : ∀ (s : PanSemStateFiniteExact 64 F) (cw : BitVec 64),
      KeyNibInv s0 key0 n0 out0 s →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond =
        some (.val (.word cw)) → cw ≠ 0 →
      (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      KeyNibInv s0 key0 n0 out0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2)
    (k : Nat) (s post : PanSemStateFiniteExact 64 F) (hk : s.clock ≤ k)
    (hinv : KeyNibInv s0 key0 n0 out0 s)
    (hrun : evaluateHOLFiniteState s (.while cond body) = (none, post)) :
    KeyNibInv s0 key0 n0 out0 post ∧
    @evalHOLExact 64 F _ post.toExact (fun a => Classical.propDecidable (post.memaddrs a)) cond =
      some (.val (.word 0)) := by
  induction k generalizing s with
  | zero =>
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i cw hcond
      split at hrun
      · split at hrun <;> [simp at hrun; omega]
      · rename_i hnotnz
        have hcw0 : cw = 0 := Classical.not_not.1 hnotnz
        subst hcw0; simp at hrun; subst hrun; exact ⟨hinv, hcond⟩
    · simp at hrun
  | succ k ih =>
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i cw hcond
      split at hrun
      · rename_i hnz
        split at hrun
        · simp at hrun
        · dsimp only at hrun
          rw [fixClockHOLFinite_evaluateState] at hrun
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          have hbc := hnobc (decClockHOLFinite s)
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at hrun rem hbc
          cases r1 with
          | none =>
            have hmid : KeyNibInv s0 key0 n0 out0 mid := by
              have hb := hstep s cw hinv hcond hnz (by rw [hbr])
              rw [hbr] at hb; exact hb
            exact ih mid (by change mid.clock ≤ s.clock - 1 at rem; omega) hmid hrun
          | some r1 =>
            cases r1 with
            | «continue» => exact absurd rfl hbc.2
            | «break» => exact absurd rfl hbc.1
            | _ => simp at hrun
      · rename_i hnotnz
        have hcw0 : cw = 0 := Classical.not_not.1 hnotnz
        subst hcw0; simp at hrun; subst hrun; exact ⟨hinv, hcond⟩
    · simp at hrun

private theorem dec_none_inv {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {nm : MlS} {e : ExpHOL 64} {b : ProgHOL 64}
    (h : evaluateHOLFiniteState s (.dec nm .one e b) = (none, post)) :
    ∃ w : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e =
        some (.val (.word w)) ∧
      (evaluateHOLFiniteState (setVarHOLFinite nm (.val (.word w)) s) b).1 = none ∧
      post = { (evaluateHOLFiniteState (setVarHOLFinite nm (.val (.word w)) s) b).2 with
        locals := HolFiniteMapExact.resVarEq
          (evaluateHOLFiniteState (setVarHOLFinite nm (.val (.word w)) s) b).2.locals
          (nm, s.locals.lookup nm) } := by
  rw [evaluateHOLFiniteState_dec_total] at h; dsimp only at h
  split at h
  · simp at h
  · rename_i v hv
    split at h
    · rename_i hsh
      rcases v with ⟨⟨w⟩⟩ | _ | _ <;> simp [shapeEqHOL, shapeOfHOLExact] at hsh
      refine ⟨w, hv, ?_, ?_⟩
      · injection h
      · injection h with _ hp; exact hp.symm
    · simp at h

private theorem seq_storeByte_none_inv {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {d e : ExpHOL 64} {b : ProgHOL 64}
    (hG : GuestInv s) (addr : BitVec 64)
    (hd : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) d =
      some (.val (.word addr)))
    (hin : sourceBase ≤ addr.toNat → addr.toNat + 1 ≤ heapEnd → ∃ iv ∈ Rl, InIvl addr.toNat iv)
    (h : evaluateHOLFiniteState s (.seq (.storeByte d e) b) = (none, post)) :
    ∃ mid : PanSemStateFiniteExact 64 F,
      sourceBase ≤ addr.toNat ∧ addr.toNat + 1 ≤ heapEnd ∧
      ByteEff s mid Rl ∧ mid.locals = s.locals ∧ mid.code = s.code ∧ GuestInv mid ∧
      evaluateHOLFiniteState mid b = (none, post) := by
  rw [evaluateHOLFiniteState_seq_line780] at h
  have hbs := byteEff_storeByte (Rl := Rl) hG d e (fun x hx hdom => by
    rw [hd] at hx; cases hx
    have hord : (panByteAlignHOL addr).toNat % 8 = 0 ∧
        sourceBase ≤ (panByteAlignHOL addr).toNat ∧ (panByteAlignHOL addr).toNat < heapEnd := by
      rwa [hG.memaddrs, ordinaryDomain_iff] at hdom
    have hhe8 : heapEnd % 8 = 0 := by decide
    have hsb8 : sourceBase % 8 = 0 := by decide
    have hal := panByteAlign_toNat64 addr
    exact hin (by omega) (by omega))
  rcases h1 : evaluateHOLFiniteState s (.storeByte d e) with ⟨r1, mid⟩
  rw [h1] at h hbs
  cases r1 with
  | some _ => simp at h
  | none =>
    obtain ⟨x, hx, hlo, hhi⟩ := hbs.2 rfl
    rw [hd] at hx; cases hx
    have hloc : mid.locals = s.locals := by
      rw [evaluateHOLFiniteState_storeByte] at h1
      revert h1; repeat' split
      all_goals intro h1 <;> injection h1 with _ hm <;> subst hm <;> rfl
    exact ⟨mid, hlo, hhi, hbs.1, hloc, hbs.1.code,
      guestInv_congr hbs.1.code hbs.1.memaddrs hbs.1.shMemaddrs hbs.1.baseAddr hG, h⟩

private theorem one_byte_nibbles_step {F : Type} {s0 s post : PanSemStateFiniteExact 64 F}
    {key0 n0 out0 iw : BitVec 64} (bnm : MlS) (kOff : ExpHOL 64)
    (outOff0 outOff1 : ExpHOL 64) (d0 : Nat) {rest : ProgHOL 64}
    (hb_ne_out : bnm ≠ ofString "out") (hb_ne_i : bnm ≠ ofString "i")
    (hb_ne_key : bnm ≠ ofString "key") (hb_ne_n : bnm ≠ ofString "n")
    (hc : s.code = originalRuntimeCode) (hG : GuestInv s)
    (heff : ByteEff s0 s [(out0.toNat, 2 * n0.toNat)])
    (hk : s.locals.lookup (ofString "key") = some (.val (.word key0)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (ho : s.locals.lookup (ofString "out") = some (.val (.word out0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (ho0 : ∀ bw : BitVec 64,
      let sb := setVarHOLFinite bnm (.val (.word bw)) s
      @evalHOLExact 64 F _ sb.toExact (fun a => Classical.propDecidable (sb.memaddrs a)) outOff0 =
        some (.val (.word (out0 + 2#64 * iw + BitVec.ofNat 64 d0))))
    (ho1 : ∀ (bw : BitVec 64) (m : PanSemStateFiniteExact 64 F),
      m.locals = (setVarHOLFinite bnm (.val (.word bw)) s).locals →
      @evalHOLExact 64 F _ m.toExact (fun a => Classical.propDecidable (m.memaddrs a)) outOff1 =
        some (.val (.word (out0 + 2#64 * iw + BitVec.ofNat 64 (d0 + 1)))))
    (hin0 : sourceBase ≤ (out0 + 2#64 * iw + BitVec.ofNat 64 d0).toNat →
      (out0 + 2#64 * iw + BitVec.ofNat 64 d0).toNat + 1 ≤ heapEnd →
      InIvl (out0 + 2#64 * iw + BitVec.ofNat 64 d0).toNat (out0.toNat, 2 * n0.toNat))
    (hin1 : sourceBase ≤ (out0 + 2#64 * iw + BitVec.ofNat 64 d0).toNat →
      (out0 + 2#64 * iw + BitVec.ofNat 64 d0).toNat + 1 ≤ heapEnd →
      sourceBase ≤ (out0 + 2#64 * iw + BitVec.ofNat 64 (d0 + 1)).toNat →
      (out0 + 2#64 * iw + BitVec.ofNat 64 (d0 + 1)).toNat + 1 ≤ heapEnd →
      InIvl (out0 + 2#64 * iw + BitVec.ofNat 64 (d0 + 1)).toNat (out0.toNat, 2 * n0.toNat))
    (hrun : evaluateHOLFiniteState s
      (.dec bnm .one (.loadByte kOff)
        (.seq (.storeByte outOff0 (.shift .lsr (.var .local bnm) (.const 4)))
          (.seq (.storeByte outOff1 (.op .and [.var .local bnm, .const 15]))
            rest))) = (none, post)) :
    ∃ m2 : PanSemStateFiniteExact 64 F,
      sourceBase ≤ (out0 + 2#64 * iw + BitVec.ofNat 64 d0).toNat ∧
      (out0 + 2#64 * iw + BitVec.ofNat 64 d0).toNat + 1 ≤ heapEnd ∧
      sourceBase ≤ (out0 + 2#64 * iw + BitVec.ofNat 64 (d0 + 1)).toNat ∧
      (out0 + 2#64 * iw + BitVec.ofNat 64 (d0 + 1)).toNat + 1 ≤ heapEnd ∧
      m2.code = originalRuntimeCode ∧ GuestInv m2 ∧
      ByteEff s0 m2 [(out0.toNat, 2 * n0.toNat)] ∧
      m2.locals.lookup (ofString "key") = some (.val (.word key0)) ∧
      m2.locals.lookup (ofString "n") = some (.val (.word n0)) ∧
      m2.locals.lookup (ofString "out") = some (.val (.word out0)) ∧
      m2.locals.lookup (ofString "i") = some (.val (.word iw)) ∧
      (evaluateHOLFiniteState m2 rest).1 = none ∧
      post = { (evaluateHOLFiniteState m2 rest).2 with
        locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState m2 rest).2.locals
          (bnm, s.locals.lookup bnm) } := by
  obtain ⟨bw, _, hrest1, hpost_eq⟩ := dec_none_inv hrun
  set sb := setVarHOLFinite bnm (.val (.word bw)) s
  have hG_sb : GuestInv sb := guestInv_setVar _ _ s hG
  have heff_sb : ByteEff s0 sb [(out0.toNat, 2 * n0.toNat)] := heff.locals_clock _ s.clock
  rcases h_eq : evaluateHOLFiniteState sb
      (.seq (.storeByte outOff0 (.shift .lsr (.var .local bnm) (.const 4)))
        (.seq (.storeByte outOff1 (.op .and [.var .local bnm, .const 15])) rest)) with ⟨r_end, p_end⟩
  have hr_none : r_end = none := by rw [h_eq] at hrest1; exact hrest1
  subst hr_none
  obtain ⟨m1, hlo0, hhi0, heff1, hloc1, hc1, hG1, hseq2⟩ :=
    seq_storeByte_none_inv (Rl := [(out0.toNat, 2 * n0.toNat)]) hG_sb
      (out0 + 2#64 * iw + BitVec.ofNat 64 d0) (ho0 bw)
      (fun h1 h2 => ⟨_, List.mem_singleton.mpr rfl, hin0 h1 h2⟩) h_eq
  obtain ⟨m2, hlo1, hhi1, heff2, hloc2, hc2, hG2, hrest2⟩ :=
    seq_storeByte_none_inv (Rl := [(out0.toNat, 2 * n0.toNat)]) hG1
      (out0 + 2#64 * iw + BitVec.ofNat 64 (d0 + 1)) (ho1 bw m1 hloc1)
      (fun h1 h2 => ⟨_, List.mem_singleton.mpr rfl, hin1 hlo0 hhi0 h1 h2⟩) hseq2
  have hloc_m2 : m2.locals = sb.locals := hloc2.trans hloc1
  refine ⟨m2, hlo0, hhi0, hlo1, hhi1, hc2.trans (hc1.trans hc), hG2,
    (heff_sb.trans heff1).trans heff2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hloc_m2]; simp [sb, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hk, hb_ne_key]
  · rw [hloc_m2]; simp [sb, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn, hb_ne_n]
  · rw [hloc_m2]; simp [sb, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ho, hb_ne_out]
  · rw [hloc_m2]; simp [sb, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hi, hb_ne_i]
  · rw [hrest2]
  · rw [hpost_eq, h_eq, hrest2]

private theorem nib_addr_nowrap (out0 iw n0 : BitVec 64) (step : Nat)
    (hprev : 0 < iw.toNat → sourceBase ≤ out0.toNat ∧ out0.toNat + 2 * iw.toNat ≤ heapEnd)
    (hstep_cond : iw.toNat + step ≤ n0.toNat ∨ ¬ (n0 < iw + BitVec.ofNat 64 step))
    (hstep_le : step ≤ 4) (hstep_pos : 0 < step)
    (h0_lo : sourceBase ≤ (out0 + 2#64 * iw + 0#64).toNat)
    (h0_hi : (out0 + 2#64 * iw + 0#64).toNat + 1 ≤ heapEnd) :
    (2#64 * iw).toNat = 2 * iw.toNat ∧
    (out0 + 2#64 * iw).toNat = out0.toNat + 2 * iw.toNat ∧
    (iw + BitVec.ofNat 64 step).toNat = iw.toNat + step ∧
    iw.toNat + step ≤ n0.toNat ∧
    sourceBase ≤ out0.toNat ∧
    ∀ d : Nat, d < 2 * step →
      (out0 + 2#64 * iw + BitVec.ofNat 64 d).toNat = out0.toNat + 2 * iw.toNat + d ∧
      InIvl (out0 + 2#64 * iw + BitVec.ofNat 64 d).toNat (out0.toNat, 2 * n0.toNat) := by
  have hsb : sourceBase = 2701131776 := rfl
  have hhe : heapEnd = 33806089704 := by decide
  rw [BitVec.add_zero] at h0_lo h0_hi
  have holt := out0.isLt; have hilt := iw.isLt; have hnlt := n0.isLt
  by_cases hiz : iw.toNat = 0
  · have hi0 : iw = 0 := BitVec.eq_of_toNat_eq hiz
    subst hi0
    have hz : 2#64 * (0 : BitVec 64) = (0 : BitVec 64) := rfl
    have hao : out0 + (0 : BitVec 64) = out0 := BitVec.add_zero out0
    rw [hz, hao] at h0_lo h0_hi ⊢
    have h0_nat : (0 : BitVec 64).toNat = 0 := rfl
    have hstep_bv : ((0 : BitVec 64) + BitVec.ofNat 64 step).toNat = step := by
      rw [zero_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hle_n : step ≤ n0.toNat := by
      rcases hstep_cond with h | h
      · omega
      · rw [BitVec.lt_def, hstep_bv] at h; omega
    refine ⟨rfl, by simp [h0_nat], by omega, by omega, h0_lo, fun d hd => ?_⟩
    have hd_nat : (BitVec.ofNat 64 d).toNat = d := Nat.mod_eq_of_lt (by omega)
    have hadd_d : (out0 + BitVec.ofNat 64 d).toNat = out0.toNat + d := by
      rw [BitVec.toNat_add, hd_nat, Nat.mod_eq_of_lt (by omega)]
    rw [hadd_d, h0_nat]
    exact ⟨by omega, ⟨by omega, by omega⟩⟩
  · obtain ⟨hdlo, hdhi⟩ := hprev (by omega)
    have h2i : (2#64 * iw).toNat = 2 * iw.toNat := by
      rw [BitVec.toNat_mul]
      have h2_nat : (2#64).toNat = 2 := rfl
      rw [h2_nat, Nat.mod_eq_of_lt (by omega)]
    have ho2i : (out0 + 2#64 * iw).toNat = out0.toNat + 2 * iw.toNat := by
      rw [BitVec.toNat_add, h2i, Nat.mod_eq_of_lt (by omega)]
    have his : (iw + BitVec.ofNat 64 step).toNat = iw.toNat + step := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have hle_n : iw.toNat + step ≤ n0.toNat := by
      rcases hstep_cond with h | h
      · exact h
      · rw [BitVec.lt_def, his] at h; omega
    refine ⟨h2i, ho2i, his, hle_n, hdlo, fun d hd => ?_⟩
    have hadd_d : (out0 + 2#64 * iw + BitVec.ofNat 64 d).toNat = out0.toNat + 2 * iw.toNat + d := by
      rw [BitVec.toNat_add, ho2i, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hadd_d]
    exact ⟨rfl, ⟨by omega, by omega⟩⟩

private theorem eval_out_2i {F : Type} (s : PanSemStateFiniteExact 64 F) (out0 iw : BitVec 64)
    (ho : s.locals.lookup (ofString "out") = some (.val (.word out0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString "out"), .panop .mul [.const 2, .var .local (ofString "i")]]) =
      some (.val (.word (out0 + 2#64 * iw + 0#64))) := by
  simp [evalHOLExact, evalListHOLExact, ho, hi, valueIsWord, valueWord, panOpHOL, wordOpHOL, wordOp]

private theorem eval_out_2i_c {F : Type} (s : PanSemStateFiniteExact 64 F) (out0 iw : BitVec 64) (d : Nat)
    (ho : s.locals.lookup (ofString "out") = some (.val (.word out0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString "out"), .panop .mul [.const 2, .var .local (ofString "i")], .const (BitVec.ofNat 64 d)]) =
      some (.val (.word (out0 + 2#64 * iw + BitVec.ofNat 64 d))) := by
  simp [evalHOLExact, evalListHOLExact, ho, hi, valueIsWord, valueWord, panOpHOL, wordOpHOL, wordOp, BitVec.add_assoc]

private theorem noBreakCont_noLoop :
    ∀ p : ProgHOL 64,
      (match p with
       | .dec _ _ _ _ | .seq _ _ | .storeByte _ _ | .assign _ _ _ => true
       | _ => false) = true → True := fun _ _ => trivial

private theorem key_to_nibbles_body_eff {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (key0 n0 out0 : BitVec 64)
    (hc : s0.code = originalRuntimeCode) (hG : GuestInv s0)
    (hk0 : s0.locals.lookup (ofString "key") = some (.val (.word key0)))
    (hn0 : s0.locals.lookup (ofString "n") = some (.val (.word n0)))
    (ho0 : s0.locals.lookup (ofString "out") = some (.val (.word out0)))
    (hres : Resumes (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_key_to_nibbles)).1) :
    ByteEff s0 (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_key_to_nibbles)).2
      [(out0.toNat, 2 * n0.toNat)] ∧
    (0 < n0.toNat → sourceBase ≤ out0.toNat ∧ out0.toNat + 2 * n0.toNat ≤ heapEnd) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_key_to_nibbles,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hres ⊢
  rw [evaluateHOLFiniteState_dec_total] at hres ⊢; dsimp only at hres ⊢
  have hev0 : @evalHOLExact 64 F _ s0.toExact (fun a => Classical.propDecidable (s0.memaddrs a))
      (.const (BitVec.ofNat 64 0)) = some (.val (.word (BitVec.ofNat 64 0))) := rfl
  rw [hev0] at hres ⊢; dsimp only at hres ⊢
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word (BitVec.ofNat 64 0)))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos hsh0] at hres ⊢; dsimp only at hres ⊢
  set s1 := setVarHOLFinite (ofString "i") (.val (.word (BitVec.ofNat 64 0))) s0
  have hinv1 : KeyNibInv s0 key0 n0 out0 s1 := by
    refine ⟨hc, guestInv_setVar _ _ s0 hG, (ByteEff.refl s0 _).locals_clock _ s0.clock, ?_, ?_, ?_, BitVec.ofNat 64 0, ?_, Nat.zero_le _, fun h => by simp at h⟩
    · simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hk0, show ofString "i" ≠ ofString "key" by decide]
    · simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn0, show ofString "i" ≠ ofString "n" by decide]
    · simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ho0, show ofString "i" ≠ ofString "out" by decide]
    · simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
  set w4 : ProgHOL 64 := .while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 4)])) _
  have hw4_nrr : ¬ Resumes (evaluateHOLFiniteState s1 w4).1 := by
    refine noRetOrRaise_while _ _ (fun t => ?_) s1.clock s1 le_rfl
    exact noRetOrRaise_dec _ _ _ _ fun _ =>
      noRetOrRaise_seq (noRetOrRaise_storeByte _ _ _) fun _ _ =>
      noRetOrRaise_seq (noRetOrRaise_storeByte _ _ _) fun _ _ =>
      noRetOrRaise_dec _ _ _ _ fun _ =>
      noRetOrRaise_seq (noRetOrRaise_storeByte _ _ _) fun _ _ =>
      noRetOrRaise_seq (noRetOrRaise_storeByte _ _ _) fun _ _ =>
      noRetOrRaise_dec _ _ _ _ fun _ =>
      noRetOrRaise_seq (noRetOrRaise_storeByte _ _ _) fun _ _ =>
      noRetOrRaise_seq (noRetOrRaise_storeByte _ _ _) fun _ _ =>
      noRetOrRaise_dec _ _ _ _ fun _ =>
      noRetOrRaise_seq (noRetOrRaise_storeByte _ _ _) fun _ _ =>
      noRetOrRaise_seq (noRetOrRaise_storeByte _ _ _) fun _ _ =>
      noRetOrRaise_assign _ _ _ _
  rcases hr4 : evaluateHOLFiniteState s1 w4 with ⟨r4, s2⟩
  cases r4 with
  | some _ => rw [hr4] at hres hw4_nrr; exact absurd hres hw4_nrr
  | none =>
    dsimp only at hres ⊢
    have hnbc_dec : ∀ {p : ProgHOL 64},
        (∀ t : PanSemStateFiniteExact 64 F, (evaluateHOLFiniteState t p).1 ≠ some .break ∧ (evaluateHOLFiniteState t p).1 ≠ some .continue) →
        ∀ nm e (t : PanSemStateFiniteExact 64 F),
          (evaluateHOLFiniteState t (.dec nm .one e p)).1 ≠ some .break ∧
          (evaluateHOLFiniteState t (.dec nm .one e p)).1 ≠ some .continue := by
      intro p hp nm e t
      rw [evaluateHOLFiniteState_dec_total]; dsimp only
      split
      · simp
      · rename_i v _; split
        · exact hp (setVarHOLFinite nm v t)
        · simp
    have hnbc_seq_sb : ∀ {p : ProgHOL 64},
        (∀ t : PanSemStateFiniteExact 64 F, (evaluateHOLFiniteState t p).1 ≠ some .break ∧ (evaluateHOLFiniteState t p).1 ≠ some .continue) →
        ∀ d e (t : PanSemStateFiniteExact 64 F),
          (evaluateHOLFiniteState t (.seq (.storeByte d e) p)).1 ≠ some .break ∧
          (evaluateHOLFiniteState t (.seq (.storeByte d e) p)).1 ≠ some .continue := by
      intro p hp d e t
      rw [evaluateHOLFiniteState_seq_line780]
      rcases hs : evaluateHOLFiniteState t (.storeByte d e) with ⟨rs, ms⟩
      cases rs with
      | none => exact hp ms
      | some _ =>
        rw [evaluateHOLFiniteState_storeByte] at hs
        revert hs; repeat' split
        all_goals (intro hs; cases hs; try simp)
    have hnbc_asgn : ∀ nm e (t : PanSemStateFiniteExact 64 F),
        (evaluateHOLFiniteState t (.assign .local nm e)).1 ≠ some .break ∧
        (evaluateHOLFiniteState t (.assign .local nm e)).1 ≠ some .continue := by
      intro nm e t; rw [evaluateHOLFiniteState_assign]
      repeat' split
      all_goals simp
    have hinv2_pair := while_keyNibInv _ _
      (by
        intro t
        apply hnbc_dec; apply hnbc_seq_sb; apply hnbc_seq_sb
        apply hnbc_dec; apply hnbc_seq_sb; apply hnbc_seq_sb
        apply hnbc_dec; apply hnbc_seq_sb; apply hnbc_seq_sb
        apply hnbc_dec; apply hnbc_seq_sb; apply hnbc_seq_sb
        exact hnbc_asgn _ _)
      (by
        intro st cw hinv hcond hnz hbody_none
        obtain ⟨hst_c, hst_G, hst_eff, hst_k, hst_n, hst_o, iw, hst_i, hiw_le, hprev⟩ := hinv
        have hnotlt : ¬ (n0 < iw + 4#64) := by
          simp only [evalHOLExact, evalListHOLExact, hst_n, hst_i, wordOpHOL, wordOp, valueIsWord, valueWord,
            List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr, add_zero,
            Compiler.Encoders.Asm.wordCmpHOL] at hcond
          intro hlt
          have hnotle : ¬ (iw + 4#64 ≤ n0) := BitVec.not_le.mpr hlt
          simp [hnotle] at hcond
          exact hnz hcond.symm
        let st' := decClockHOLFinite st
        have hst'_c : st'.code = originalRuntimeCode := hst_c
        have hG' : GuestInv st' := guestInv_congr (s := st) rfl rfl rfl rfl hst_G
        have heff' : ByteEff s0 st' [(out0.toNat, 2 * n0.toNat)] := hst_eff.locals_clock _ _
        rcases hpst : evaluateHOLFiniteState st' _ with ⟨pst_r, pst⟩
        rw [hpst] at hbody_none; dsimp only at hbody_none; subst hbody_none
        obtain ⟨u1, h0lo, h0hi, h1lo, h1hi, hu1c, hu1G, hu1eff, hu1k, hu1n, hu1o, hu1i, hu1r, hpst1⟩ :=
          one_byte_nibbles_step (s := st') (ofString "b0") _ _ _ 0
            (by decide) (by decide) (by decide) (by decide)
            hst'_c hG' heff' hst_k hst_n hst_o hst_i
            (fun bw => eval_out_2i _ out0 iw
              (by simp [st', decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hst_o, show ofString "b0" ≠ ofString "out" by decide])
              (by simp [st', decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hst_i, show ofString "b0" ≠ ofString "i" by decide]))
            (fun bw m hm => eval_out_2i_c _ out0 iw 1
              (by rw [hm]; simp [st', decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hst_o, show ofString "b0" ≠ ofString "out" by decide])
              (by rw [hm]; simp [st', decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hst_i, show ofString "b0" ≠ ofString "i" by decide]))
            (fun hlo hhi => (nib_addr_nowrap out0 iw n0 4 hprev (Or.inr hnotlt) (by omega) (by omega) hlo hhi).2.2.2.2.2 0 (by omega) |>.2)
            (fun hlo hhi _ _ => (nib_addr_nowrap out0 iw n0 4 hprev (Or.inr hnotlt) (by omega) (by omega) hlo hhi).2.2.2.2.2 1 (by omega) |>.2)
            hpst
        have hnw := nib_addr_nowrap out0 iw n0 4 hprev (Or.inr hnotlt) (by omega) (by omega) h0lo h0hi
        rcases h_u1 : evaluateHOLFiniteState u1 _ with ⟨r_u1, p_u1⟩
        rw [h_u1] at hu1r; dsimp only at hu1r; subst hu1r
        obtain ⟨u2, _, _, _, _, hu2c, hu2G, hu2eff, hu2k, hu2n, hu2o, hu2i, hu2r, hpst2⟩ :=
          one_byte_nibbles_step (ofString "b1") _ _ _ 2
            (by decide) (by decide) (by decide) (by decide)
            hu1c hu1G hu1eff hu1k hu1n hu1o hu1i
            (fun bw => eval_out_2i_c _ out0 iw 2
              (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu1o, show ofString "b1" ≠ ofString "out" by decide])
              (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu1i, show ofString "b1" ≠ ofString "i" by decide]))
            (fun bw m hm => eval_out_2i_c _ out0 iw 3
              (by rw [hm]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu1o, show ofString "b1" ≠ ofString "out" by decide])
              (by rw [hm]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu1i, show ofString "b1" ≠ ofString "i" by decide]))
            (fun _ _ => (hnw.2.2.2.2.2 2 (by omega)).2)
            (fun _ _ _ _ => (hnw.2.2.2.2.2 3 (by omega)).2)
            h_u1
        rcases h_u2 : evaluateHOLFiniteState u2 _ with ⟨r_u2, p_u2⟩
        rw [h_u2] at hu2r; dsimp only at hu2r; subst hu2r
        obtain ⟨u3, _, _, _, _, hu3c, hu3G, hu3eff, hu3k, hu3n, hu3o, hu3i, hu3r, hpst3⟩ :=
          one_byte_nibbles_step (ofString "b2") _ _ _ 4
            (by decide) (by decide) (by decide) (by decide)
            hu2c hu2G hu2eff hu2k hu2n hu2o hu2i
            (fun bw => eval_out_2i_c _ out0 iw 4
              (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu2o, show ofString "b2" ≠ ofString "out" by decide])
              (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu2i, show ofString "b2" ≠ ofString "i" by decide]))
            (fun bw m hm => eval_out_2i_c _ out0 iw 5
              (by rw [hm]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu2o, show ofString "b2" ≠ ofString "out" by decide])
              (by rw [hm]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu2i, show ofString "b2" ≠ ofString "i" by decide]))
            (fun _ _ => (hnw.2.2.2.2.2 4 (by omega)).2)
            (fun _ _ _ _ => (hnw.2.2.2.2.2 5 (by omega)).2)
            h_u2
        rcases h_u3 : evaluateHOLFiniteState u3 _ with ⟨r_u3, p_u3⟩
        rw [h_u3] at hu3r; dsimp only at hu3r; subst hu3r
        obtain ⟨u4, _, _, _, h7hi, hu4c, hu4G, hu4eff, hu4k, hu4n, hu4o, hu4i, hu4r, hpst4⟩ :=
          one_byte_nibbles_step (ofString "b3") _ _ _ 6
            (by decide) (by decide) (by decide) (by decide)
            hu3c hu3G hu3eff hu3k hu3n hu3o hu3i
            (fun bw => eval_out_2i_c _ out0 iw 6
              (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu3o, show ofString "b3" ≠ ofString "out" by decide])
              (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu3i, show ofString "b3" ≠ ofString "i" by decide]))
            (fun bw m hm => eval_out_2i_c _ out0 iw 7
              (by rw [hm]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu3o, show ofString "b3" ≠ ofString "out" by decide])
              (by rw [hm]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu3i, show ofString "b3" ≠ ofString "i" by decide]))
            (fun _ _ => (hnw.2.2.2.2.2 6 (by omega)).2)
            (fun _ _ _ _ => (hnw.2.2.2.2.2 7 (by omega)).2)
            h_u3
        have hasgn : evaluateHOLFiniteState u4
            (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 4)])) =
            (none, setVarHOLFinite (ofString "i") (.val (.word (iw + 4#64))) u4) := by
          simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hu4i, wordOpHOL, wordOp,
            valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
            shapeOfHOLExact, shapeEqHOL]
        have h7_eq := (hnw.2.2.2.2.2 7 (by omega)).1
        rw [h7_eq] at h7hi
        set L_new :=
          HolFiniteMapExact.resVarEq (HolFiniteMapExact.resVarEq (HolFiniteMapExact.resVarEq (HolFiniteMapExact.resVarEq
            (setVarHOLFinite (ofString "i") (.val (.word (iw + 4#64))) u4).locals
            (ofString "b3", u3.locals.lookup (ofString "b3")))
            (ofString "b2", u2.locals.lookup (ofString "b2")))
            (ofString "b1", u1.locals.lookup (ofString "b1")))
            (ofString "b0", st'.locals.lookup (ofString "b0"))
        have hpst_all : pst = { u4 with locals := L_new } := by
          rw [hpst1, h_u1, hpst2, h_u2, hpst3, h_u3, hpst4, hasgn]; rfl
        dsimp only
        rw [hpst_all]
        refine ⟨hu4c, guestInv_congr (s := u4) rfl rfl rfl rfl hu4G, hu4eff.locals_clock _ _, ?_, ?_, ?_,
          iw + 4#64, ?_, by rw [hnw.2.2.1]; exact hnw.2.2.2.1,
          fun _ => ⟨hnw.2.2.2.2.1, by rw [hnw.2.2.1]; omega⟩⟩
        · simp [L_new, lookup_resVarEq_ne, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu4k,
            show ofString "key" ≠ ofString "b0" by decide, show ofString "key" ≠ ofString "b1" by decide,
            show ofString "key" ≠ ofString "b2" by decide, show ofString "key" ≠ ofString "b3" by decide,
            show ofString "i" ≠ ofString "key" by decide]
        · simp [L_new, lookup_resVarEq_ne, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu4n,
            show ofString "n" ≠ ofString "b0" by decide, show ofString "n" ≠ ofString "b1" by decide,
            show ofString "n" ≠ ofString "b2" by decide, show ofString "n" ≠ ofString "b3" by decide,
            show ofString "i" ≠ ofString "n" by decide]
        · simp [L_new, lookup_resVarEq_ne, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu4o,
            show ofString "out" ≠ ofString "b0" by decide, show ofString "out" ≠ ofString "b1" by decide,
            show ofString "out" ≠ ofString "b2" by decide, show ofString "out" ≠ ofString "b3" by decide,
            show ofString "i" ≠ ofString "out" by decide]
        · simp [L_new, lookup_resVarEq_ne, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "i" ≠ ofString "b0" by decide, show ofString "i" ≠ ofString "b1" by decide,
            show ofString "i" ≠ ofString "b2" by decide, show ofString "i" ≠ ofString "b3" by decide])
      s1.clock s1 s2 le_rfl hinv1 hr4
    rw [hr4] at hres; dsimp only at hres
    rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
    set w1 : ProgHOL 64 := .while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) _
    have hw1_nrr : ¬ Resumes (evaluateHOLFiniteState s2 w1).1 := by
      refine noRetOrRaise_while _ _ (fun t => ?_) s2.clock s2 le_rfl
      exact noRetOrRaise_dec _ _ _ _ fun _ =>
        noRetOrRaise_seq (noRetOrRaise_storeByte _ _ _) fun _ _ =>
        noRetOrRaise_seq (noRetOrRaise_storeByte _ _ _) fun _ _ =>
        noRetOrRaise_assign _ _ _ _
    rcases hr1 : evaluateHOLFiniteState s2 w1 with ⟨r1, s3⟩
    cases r1 with
    | some _ => rw [hr1] at hres hw1_nrr; exact absurd hres hw1_nrr
    | none =>
      dsimp only at ⊢
      obtain ⟨hinv3, hcond3⟩ := while_keyNibInv _ _
        (by
          intro t
          apply hnbc_dec; apply hnbc_seq_sb; apply hnbc_seq_sb
          exact hnbc_asgn _ _)
        (by
          intro st cw hinv hcond hnz hbody_none
          obtain ⟨hst_c, hst_G, hst_eff, hst_k, hst_n, hst_o, iw, hst_i, hiw_le, hprev⟩ := hinv
          have hlt : iw.toNat < n0.toNat := by
            simp [evalHOLExact, hst_n, hst_i, Compiler.Encoders.Asm.wordCmpHOL] at hcond
            by_contra hge; have hge' : ¬ (iw < n0) := by rw [BitVec.lt_def]; omega
            simp [hge'] at hcond; exact hnz hcond.symm
          let st' := decClockHOLFinite st
          have hst'_c : st'.code = originalRuntimeCode := hst_c
          have hG' : GuestInv st' := guestInv_congr (s := st) rfl rfl rfl rfl hst_G
          have heff' : ByteEff s0 st' [(out0.toNat, 2 * n0.toNat)] := hst_eff.locals_clock _ _
          rcases hpst : evaluateHOLFiniteState st' _ with ⟨pst_r, pst⟩
          rw [hpst] at hbody_none; dsimp only at hbody_none; subst hbody_none
          obtain ⟨u1, h0lo, h0hi, _, h1hi, hu1c, hu1G, hu1eff, hu1k, hu1n, hu1o, hu1i, hu1r, hpst1⟩ :=
            one_byte_nibbles_step (s := st') (ofString "b") _ _ _ 0
              (by decide) (by decide) (by decide) (by decide)
              hst'_c hG' heff' hst_k hst_n hst_o hst_i
              (fun bw => eval_out_2i _ out0 iw
                (by simp [st', decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hst_o, show ofString "b" ≠ ofString "out" by decide])
                (by simp [st', decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hst_i, show ofString "b" ≠ ofString "i" by decide]))
              (fun bw m hm => eval_out_2i_c _ out0 iw 1
                (by rw [hm]; simp [st', decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hst_o, show ofString "b" ≠ ofString "out" by decide])
                (by rw [hm]; simp [st', decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hst_i, show ofString "b" ≠ ofString "i" by decide]))
              (fun hlo hhi => (nib_addr_nowrap out0 iw n0 1 hprev (Or.inl (by omega)) (by omega) (by omega) hlo hhi).2.2.2.2.2 0 (by omega) |>.2)
              (fun hlo hhi _ _ => (nib_addr_nowrap out0 iw n0 1 hprev (Or.inl (by omega)) (by omega) (by omega) hlo hhi).2.2.2.2.2 1 (by omega) |>.2)
              hpst
          have hnw := nib_addr_nowrap out0 iw n0 1 hprev (Or.inl (by omega)) (by omega) (by omega) h0lo h0hi
          have hasgn : evaluateHOLFiniteState u1
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)])) =
              (none, setVarHOLFinite (ofString "i") (.val (.word (iw + 1#64))) u1) := by
            simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hu1i, wordOpHOL, wordOp,
              valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
              shapeOfHOLExact, shapeEqHOL]
          have h1_eq := (hnw.2.2.2.2.2 1 (by omega)).1
          rw [h1_eq] at h1hi
          dsimp only
          rw [hpst1, hasgn]
          refine ⟨hu1c, guestInv_congr (s := u1) rfl rfl rfl rfl hu1G, hu1eff.locals_clock _ _, ?_, ?_, ?_,
            iw + 1#64, ?_, by rw [hnw.2.2.1]; exact hnw.2.2.2.1,
            fun _ => ⟨hnw.2.2.2.2.1, by rw [hnw.2.2.1]; omega⟩⟩
          · simp [lookup_resVarEq_ne, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu1k,
              show ofString "key" ≠ ofString "b" by decide, show ofString "i" ≠ ofString "key" by decide]
          · simp [lookup_resVarEq_ne, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu1n,
              show ofString "n" ≠ ofString "b" by decide, show ofString "i" ≠ ofString "n" by decide]
          · simp [lookup_resVarEq_ne, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu1o,
              show ofString "out" ≠ ofString "b" by decide, show ofString "i" ≠ ofString "out" by decide]
          · simp [lookup_resVarEq_ne, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "i" ≠ ofString "b" by decide])
        s2.clock s2 s3 le_rfl hinv2_pair.1 hr1
      obtain ⟨_, _, heff3, _, hst3_n, _, iw3, hst3_i, hiw3_le, hdom3⟩ := hinv3
      have hge3 : ¬ (iw3 < n0) := by
        intro hlt
        simp [evalHOLExact, hst3_n, hst3_i, Compiler.Encoders.Asm.wordCmpHOL, hlt] at hcond3
      rw [BitVec.lt_def] at hge3
      have hiw3_eq : iw3.toNat = n0.toNat := by omega
      have hret_run : (evaluateHOLFiniteState s3 (.return (.const (BitVec.ofNat 64 0)))).2 = emptyLocalsHOLFinite s3 := by
        rw [evaluateHOLFiniteState_return]
        simp [evalHOLExact, isValidValueHOLExact, shapeEqHOL, shapeOfHOLExact]
      rw [hret_run]
      refine ⟨heff3.locals_clock _ s3.clock, fun hpos => ?_⟩
      rw [← hiw3_eq] at hpos ⊢
      exact hdom3 hpos

private theorem lookup_key_to_nibbles_r10 :
    originalRuntimeCode.lookup (ofString "key_to_nibbles") =
      some ([(ofString "key", .one), (ofString "n", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_key_to_nibbles, .one) :=
  lookup_of_guestAst_getElem 248 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_key_to_nibbles) rfl

private theorem call0_key_to_nibbles_eff {F : Type}
    (s : PanSemStateFiniteExact 64 F) (kExp nExp oExp : ExpHOL 64)
    (hc : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hnt : (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "key_to_nibbles") [kExp, nExp, oExp])).1 ≠ some .timeOut)
    (hor : (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "key_to_nibbles") [kExp, nExp, oExp])).1 = none ∨
      Resumes (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "key_to_nibbles") [kExp, nExp, oExp])).1) :
    ∃ kw nw ow : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) kExp = some (.val (.word kw)) ∧
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp = some (.val (.word nw)) ∧
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) oExp = some (.val (.word ow)) ∧
      ByteEff s (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "key_to_nibbles") [kExp, nExp, oExp])).2
        [(ow.toNat, 2 * nw.toNat)] ∧
      True ∧
      (0 < nw.toNat → sourceBase ≤ ow.toNat ∧ ow.toNat + 2 * nw.toNat ≤ heapEnd) := by
  have not_or_err : ¬ (some (.error : PanSemResultExact 64) = none ∨ Resumes (some .error)) := by
    rintro (h | h)
    · cases h
    · exact not_resumes_error h
  rw [evaluateHOLFiniteState_call] at hnt hor ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [kExp, nExp, oExp] with _ | vals
  · simp only [hargs] at hor; exact absurd hor not_or_err
  · simp only [hargs] at hnt hor ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "key_to_nibbles") vals with _ | ⟨body', callee, ret'⟩
    · simp only [hl] at hor; exact absurd hor not_or_err
    · simp only [hl] at hnt hor ⊢
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "key_to_nibbles") _ _ body'
        _ ret' vals callee (by rw [hc]; exact lookup_key_to_nibbles_r10) hl
      subst hsame
      have hret := lookupCodeHOLFinite_installed_return s (ofString "key_to_nibbles") _ _ _
        _ ret' vals callee (by rw [hc]; exact lookup_key_to_nibbles_r10) hl
      subst hret
      have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "key_to_nibbles") vals =
          some (sourceFnBody Guest.Software.guestFn_key_to_nibbles, callee, .one) := by
        simpa [hc] using hl
      obtain ⟨kw, nw, ow, rfl, hkw, hnw, how⟩ :=
        lookupCode_three_words (by decide) (by decide) (by decide) lookup_key_to_nibbles_r10 hl'
      have hvals_ev :
          @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) kExp = some (.val (.word kw)) ∧
          @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp = some (.val (.word nw)) ∧
          @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) oExp = some (.val (.word ow)) := by
        rw [evalListHOLFinite_eq_toExact] at hargs
        simp only [evalListHOLExact] at hargs
        rcases he1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) kExp with _ | v1
        · simp [he1] at hargs
        · rcases he2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp with _ | v2
          · simp [he1, he2] at hargs
          · rcases he3 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) oExp with _ | v3
            · simp [he1, he2, he3] at hargs
            · simp [he1, he2, he3] at hargs
              obtain ⟨rfl, rfl, rfl⟩ := hargs
              exact ⟨rfl, rfl, rfl⟩
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt hor ⊢
        let entry := callEntryStateHOLFinite s callee
        have hGe : GuestInv entry := guestInv_callEntry s callee hG
        rcases hrun : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_key_to_nibbles) with ⟨res, post⟩
        dsimp only [entry] at hrun
        simp only [hrun] at hnt hor ⊢
        have hres_b : Resumes res := by
          cases res with
          | none => exfalso; rcases hor with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
          | some r =>
            cases r with
            | returned v => exact Or.inl ⟨v, rfl⟩
            | exception eid ev => exact hor.resolve_left (by simp)
            | _ => exfalso; rcases hor with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
        obtain ⟨heff_b, hdom_b⟩ := key_to_nibbles_body_eff entry kw nw ow hc hGe hkw hnw how
          (by dsimp only [entry]; rw [hrun]; exact hres_b)
        dsimp only [entry] at heff_b
        rw [hrun] at heff_b
        have heff_s : ByteEff s post [(ow.toNat, 2 * nw.toNat)] :=
          ((ByteEff.refl s _).locals_clock _ _).trans heff_b
        cases res with
        | none => exfalso; rcases hres_b with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hor ⊢
            split
            · exact ⟨kw, nw, ow, hvals_ev.1, hvals_ev.2.1, hvals_ev.2.2, heff_s.locals_clock _ _, trivial, hdom_b⟩
            · rename_i hbad; rw [if_neg hbad] at hor; exact absurd hor not_or_err
          | exception eid ev =>
            exact ⟨kw, nw, ow, hvals_ev.1, hvals_ev.2.1, hvals_ev.2.2, heff_s.locals_clock _ _, trivial, hdom_b⟩
          | _ => exfalso; rcases hres_b with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h

private theorem decCall_alloc_resumes_inv {F : Type}
    (s : PanSemStateFiniteExact 64 F) (x : MlS) (szExp : ExpHOL 64) (cont : ProgHOL 64)
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hnt : (evaluateHOLFiniteState s (.decCall x .one (ofString "alloc") [szExp] cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (.decCall x .one (ofString "alloc") [szExp] cont)).1) :
    ∃ hp sz q : BitVec 64, ∃ mid : PanSemStateFiniteExact 64 F,
      s.globals.lookup (ofString "heap_ptr") = some (.val (.word hp)) ∧
      hp.toNat = globN s "heap_ptr" ∧
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) szExp = some (.val (.word sz)) ∧
      q = (hp + (sz + 7)) &&& ((0 : BitVec 64) - 8) ∧
      q.toNat = hp.toNat + (sz.toNat + 7) / 8 * 8 ∧
      hp.toNat ≤ q.toNat ∧ q.toNat ≤ heapLimit ∧ q.toNat % 8 = 0 ∧
      mid.code = originalRuntimeCode ∧ ArenaReady mid ∧
      mid.memory = s.memory ∧ mid.be = s.be ∧
      mid.globals = s.globals.update (ofString "heap_ptr", .val (.word q)) ∧
      mid.locals = s.locals.update (x, .val (.word hp)) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s (.decCall x .one (ofString "alloc") [szExp] cont)).2 =
        { (evaluateHOLFiniteState mid cont).2 with
          locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals (x, s.locals.lookup x) } := by
  obtain ⟨hG, hA⟩ := hAR
  obtain ⟨hp, _, _, hhp, hhp_eq, _, _, _, _⟩ := InitECandidate.Solver.Wave8GuestInv.R10Shards.P02.arenaOK_globals s hA
  have hlook : originalRuntimeCode.lookup (ofString "alloc") =
      some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_alloc, .one) :=
    lookup_of_guestAst_getElem 7 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_alloc) rfl
  rw [evaluateHOLFiniteState_decCall_total] at hnt hres ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [szExp] with _ | vals
  · simp only [hargs] at hres; exact absurd hres not_resumes_error
  · simp only [hargs] at hnt hres ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "alloc") vals with _ | ⟨body', callee, ret'⟩
    · simp only [hl] at hres; exact absurd hres not_resumes_error
    · simp only [hl] at hnt hres ⊢
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "alloc") _ _ body'
        _ ret' vals callee (by rw [hc]; exact hlook) hl
      subst hsame
      have hret := lookupCodeHOLFinite_installed_return s (ofString "alloc") _ _ _
        _ ret' vals callee (by rw [hc]; exact hlook) hl
      subst hret
      have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "alloc") vals =
          some (sourceFnBody Guest.Software.guestFn_alloc, callee, .one) := by simpa [hc] using hl
      obtain ⟨sz, rfl, hsz_c⟩ := lookupCode_one_word hlook hl'
      have hsz_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) szExp =
          some (.val (.word sz)) := by
        rw [evalListHOLFinite_eq_toExact] at hargs
        simp only [evalListHOLExact] at hargs
        rcases he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) szExp with _ | v1
        · simp [he] at hargs
        · simp [he] at hargs; subst hargs; rfl
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt hres ⊢
        let entry := callEntryStateHOLFinite s callee
        have hal_res : Resumes (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_alloc)).1 := by
          rcases hr : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_alloc) with ⟨ra, pa⟩
          dsimp only [entry] at hr hnt hres ⊢
          rw [hr] at hnt hres
          dsimp only at hnt hres ⊢
          cases ra with
          | none => exact absurd hres not_resumes_error
          | some r =>
            cases r with
            | returned v => exact Or.inl ⟨v, rfl⟩
            | exception eid ev =>
              dsimp only [fixClockHOLFinite] at hres
              rcases hres with ⟨_, h⟩ | ⟨e', v', h, hne⟩
              · simp at h
              · cases h
                exact Or.inr ⟨eid, ev, Eq.refl _, hne⟩
            | _ => exfalso; rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp [fixClockHOLFinite] at h
        obtain ⟨hal_ret, hal_post, hnot_cMax⟩ :=
          evaluate_alloc_body_resumes entry hp sz hc hhp hsz_c hal_res
        rcases hr : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_alloc) with ⟨ra, pa⟩
        dsimp only [entry] at hr hal_ret hal_post
        rw [hr] at hal_ret hal_post
        dsimp only at hal_ret hal_post
        subst hal_ret
        simp only [hr, fixClockHOLFinite] at hnt hres ⊢
        have hsh_hp : (shapeEqHOL (shapeOfHOLExact (.val (.word hp))) .one &&
            shapeEqHOL (shapeOfHOLExact (.val (.word hp))) .one) = true := by
          simp [shapeEqHOL, shapeOfHOLExact]
        rw [if_pos hsh_hp] at hnt hres ⊢
        dsimp only at hnt hres ⊢
        let q : BitVec 64 := (hp + (sz + 7)) &&& ((0 : BitVec 64) - 8)
        -- Also check `(cMax - hp).toNat < sz.toNat` could not have held!
        have hnot_sub : ¬ ((cMax - hp).toNat < sz.toNat) := by
          intro hcmp1
          have hbody_eq : sourceFnBody Guest.Software.guestFn_alloc =
              .dec (ofString "p") .one (.var .global (ofString "heap_ptr"))
                (.seq
                  (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
                      (.var .local (ofString "n")))
                    (.call (some (none, none)) (ofString "trap_with") [.const 1])
                    .skip)
                  (.dec (ofString "q") .one
                    (.op .and [.op .add [.var .local (ofString "p"), .var .local (ofString "n"), .const 7],
                      .op .sub [.const 0, .const 8]])
                    (.seq
                      (.ite (.cmp .lower (.const cMax) (.var .local (ofString "q")))
                        (.call (some (none, none)) (ofString "trap_with") [.const 1])
                        .skip)
                      (.seq
                        (.assign .global (ofString "heap_ptr") (.var .local (ofString "q")))
                        (.return (.var .local (ofString "p"))))))) := rfl
          have hr' := hr
          rw [hbody_eq, evaluateHOLFiniteState_dec_total] at hr'; dsimp only at hr'
          have hpev : @evalHOLExact 64 F _ (callEntryStateHOLFinite s callee).toExact
              (fun a => Classical.propDecidable ((callEntryStateHOLFinite s callee).memaddrs a))
              (.var .global (ofString "heap_ptr")) = some (.val (.word hp)) := hhp
          have hsh1 : shapeEqHOL .one (shapeOfHOLExact (.val (.word hp))) = true := by
            simp [shapeEqHOL, shapeOfHOLExact]
          rw [hpev] at hr'; simp only [hsh1, ↓reduceIte] at hr'
          rw [evaluateHOLFiniteState_seq_line780] at hr'
          let ps := setVarHOLFinite (ofString "p") (.val (.word hp)) (callEntryStateHOLFinite s callee)
          have hev_c : @evalHOLExact 64 F _ ps.toExact (fun a => Classical.propDecidable (ps.memaddrs a))
              (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")]) (.var .local (ofString "n"))) =
              some (.val (.word (if (cMax - hp).toNat < sz.toNat then 1 else 0))) := by
            have hpl : ps.locals.lookup (ofString "p") = some (.val (.word hp)) := by
              simp [ps, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            have hnl : ps.locals.lookup (ofString "n") = some (.val (.word sz)) := by
              simp [ps, callEntryStateHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsz_c,
                show ofString "p" ≠ ofString "n" by decide]
            simp only [evalHOLExact, evalListHOLExact, hpl, hnl, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]; rfl
          have hite_tr : evaluateHOLFiniteState ps
              (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")]) (.var .local (ofString "n")))
                (.call (some (none, none)) (ofString "trap_with") [.const 1]) .skip) =
              evaluateHOLFiniteState ps (.call (some (none, none)) (ofString "trap_with") [.const 1]) := by
            rw [evaluateHOLFiniteState_ite, hev_c, if_pos hcmp1]; simp
          rw [hite_tr] at hr'
          have hnr_tr := evaluate_call_trap_with_no_resumes ps 1 hc
          have hnn_tr := evaluate_call_trap_with_no_none ps 1 hc
          rcases htr : evaluateHOLFiniteState ps (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨rt, st⟩
          rw [htr] at hr' hnr_tr hnn_tr
          cases rt with
          | none => exact hnn_tr rfl
          | some r => injection hr' with hr_eq _; rw [hr_eq] at hnr_tr; exact hnr_tr (Or.inl ⟨_, rfl⟩)
        have hhp_hi : hp.toNat ≤ heapLimit := by rw [hhp_eq]; exact hA.2.1
        have hhp_al : hp.toNat % 8 = 0 := by rw [hhp_eq]; exact hA.2.2.2.2.2.1
        obtain ⟨hq_eq, hq_hi, hq_al, hp_le_q⟩ :=
          InitECandidate.Solver.Wave8GuestInv.R10Shards.P02.alloc_arith hp sz hhp_hi hhp_al hnot_sub hnot_cMax
        change q.toNat = _ at hq_eq
        let mid := setVarHOLFinite x (.val (.word hp))
          { pa with locals := s.locals,
                    clock := if (callEntryStateHOLFinite s callee).clock < pa.clock
                             then (callEntryStateHOLFinite s callee).clock else pa.clock }
        have hmid_eq : mid =
            { s with locals := s.locals.update (x, .val (.word hp)),
                     globals := s.globals.update (ofString "heap_ptr", .val (.word q)),
                     clock := mid.clock } := by
          dsimp only [mid, setVarHOLFinite]; rw [hal_post]; rfl
        have hmid_AR : ArenaReady mid := by
          rw [hmid_eq]
          refine ⟨⟨hG.code, hG.memaddrs, hG.shMemaddrs, hG.baseAddr⟩, ?_⟩
          unfold ArenaOK
          have h1 : globN { s with locals := s.locals.update (x, .val (.word hp)), globals := s.globals.update (ofString "heap_ptr", .val (.word q)), clock := mid.clock } "heap_ptr" = q.toNat := by
            simp [globN, HolFiniteMapExact.lookup_update, FUPDATE]
          have h2 : globN { s with locals := s.locals.update (x, .val (.word hp)), globals := s.globals.update (ofString "heap_ptr", .val (.word q)), clock := mid.clock } "frame_mem_ptr" = globN s "frame_mem_ptr" := by
            simp [globN, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide]
          have h3 : globN { s with locals := s.locals.update (x, .val (.word hp)), globals := s.globals.update (ofString "heap_ptr", .val (.word q)), clock := mid.clock } "scratch_ptr" = globN s "scratch_ptr" := by
            simp [globN, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
          rw [h1, h2, h3]
          have hsb : sourceBase ≤ hp.toNat := by rw [hhp_eq]; exact hA.1
          exact ⟨by omega, hq_hi, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2.1, hq_al, hA.2.2.2.2.2.2.1,
            hA.2.2.2.2.2.2.2.1,
            globalsWord_update (s := s) (ofString "heap_ptr") q rfl hA.2.2.2.2.2.2.2.2⟩
        refine ⟨hp, sz, q, mid, hhp, hhp_eq, hsz_ev, rfl, hq_eq, hp_le_q, hq_hi, hq_al,
          by rw [hmid_eq]; exact hc, hmid_AR,
          by rw [hmid_eq], by rw [hmid_eq], by rw [hmid_eq], by rw [hmid_eq],
          hnt, hres, rfl⟩

theorem «ww_mpt_nibble_key» :
    WritesWithin (fun s => [(globN s "keccak_pad", 136), (globN s "keccak_st", 200), (globN s "mpt_hash_scratch", 40)])
    ["heap_ptr"] (ofString "mpt_nibble_key") := by
  have hlook : originalRuntimeCode.lookup (ofString "mpt_nibble_key") =
      some ([(ofString "m", .one), (ofString "key", .one), (ofString "klen", .one)],
        sourceFnBody Guest.Software.guestFn_mpt_nibble_key, .comb [.one, .one]) :=
    lookup_of_guestAst_getElem 270 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_mpt_nibble_key) rfl
  refine ⟨_, _, _, hlook, ?_⟩
  intro F s hc hAR _ hnt hres
  let R0 : List Ivl := [(globN s "keccak_pad", 136), (globN s "keccak_st", 200), (globN s "mpt_hash_scratch", 40)]
  have finish_ww : ∀ (post : PanSemStateFiniteExact 64 F),
      ArenaReady post →
      globN s "heap_ptr" ≤ globN post "heap_ptr" →
      (∀ k : MlS, k ≠ ofString "heap_ptr" → post.globals.lookup k = s.globals.lookup k) →
      ByteEff s post (R0 ++ [(globN s "heap_ptr", heapLimit - globN s "heap_ptr")]) →
      ArenaReady post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
        globN post "scratch_ptr" ≤ globN s "scratch_ptr" ∧
        FrameOutside s post
          (R0 ++ [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")])
          (globN s "heap_ptr", heapLimit - globN s "heap_ptr") ∧
        ∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString → s.globals.lookup k = post.globals.lookup k := by
    intro post hAR_p hhp_le hg_eq heff
    refine ⟨hAR_p, hhp_le, ?_, ?_, ?_⟩
    · have hsp : post.globals.lookup (ofString "scratch_ptr") = s.globals.lookup (ofString "scratch_ptr") :=
        hg_eq _ (by decide)
      unfold globN; rw [hsp]
    · intro a hkeep hfresh
      by_contra hne
      obtain ⟨iv, hiv, _, hc1, hc2⟩ := heff.cell_frame a hne
      simp only [List.mem_append, List.mem_singleton] at hiv
      rcases hiv with hR0 | rfl
      · exact hkeep iv (List.mem_append_left _ hR0) ⟨hc1, hc2⟩
      · exact hfresh ⟨hc1, hc2⟩
    · intro k hk
      have hne : k ≠ ofString "heap_ptr" := by simpa using hk
      exact (hg_eq k hne).symm
  let ret1 : ExpHOL 64 := InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural
    (Exp.rStruct [Exp.var VarKind.local "nb", Exp.const (BitVec.ofNat 64 64)])
  let ret2 : ExpHOL 64 := InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural
    (Exp.rStruct [Exp.var VarKind.local "nb2", Exp.panOp PanOp.mul [Exp.const (BitVec.ofNat 64 2), Exp.var VarKind.local "klen"]])
  set c_kec : ProgHOL 64 := .call (some (none, none)) (ofString "keccak256")
    [.var .local (ofString "key"), .var .local (ofString "klen"), .var .global (ofString "mpt_hash_scratch")]
  set dc_nb : ProgHOL 64 := .decCall (ofString "nb") .one (ofString "alloc") [.const 64#64]
    (.seq
      (.call (some (none, none)) (ofString "key_to_nibbles")
        [.var .global (ofString "mpt_hash_scratch"), .const 32#64, .var .local (ofString "nb")])
      (.return ret1))
  have hbody : sourceFnBody Guest.Software.guestFn_mpt_nibble_key =
      .seq
        (.ite (.cmp .notEqual (.load .one (.op .add [.var .local (ofString "m"), .const 8#64])) (.const 0#64))
          (.seq c_kec dc_nb)
          .skip)
        (.decCall (ofString "nb2") .one (ofString "alloc")
          [.panop .mul [.const 2#64, .var .local (ofString "klen")]]
          (.seq
            (.call (some (none, none)) (ofString "key_to_nibbles")
              [.var .local (ofString "key"), .var .local (ofString "klen"), .var .local (ofString "nb2")])
            (.return ret2))) := rfl
  rw [hbody, evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
  rw [evaluateHOLFiniteState_ite] at hnt hres ⊢
  rcases hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notEqual (.load .one (.op .add [.var .local (ofString "m"), .const 8#64])) (.const 0#64)) with _ | cv
  · simp [hcond] at hres; exact absurd hres not_resumes_error
  · rcases cv with ⟨⟨cw⟩⟩ | _ | _
    · simp only [hcond] at hnt hres ⊢
      by_cases hcw0 : cw = 0
      · -- Branch 2 (`cw = 0`): `skip`, then `nb2 := alloc(2 * klen); key_to_nibbles(key, klen, nb2); return ...`
        simp only [hcw0, ↓reduceIte, evaluateHOLFiniteState_skip] at hnt hres ⊢
        obtain ⟨hp, sz, q, mid, _, hhp_eq, hsz_ev, _, hq_eq, hp_le_q, hq_hi, _,
            hmid_c, hmid_AR, hmid_mem, hmid_be, hmid_glob, hmid_loc, hcont_nt, hcont_res, hpost_eq⟩ :=
          decCall_alloc_resumes_inv s (ofString "nb2") _ _ hc hAR hnt hres
        rw [hpost_eq]
        -- Extract `klen` word from `hsz_ev`
        have hklen_word : ∃ klen_w : BitVec 64,
            s.locals.lookup (ofString "klen") = some (.val (.word klen_w)) ∧ sz = 2#64 * klen_w := by
          simp only [evalHOLExact, evalListHOLExact] at hsz_ev
          rcases hkl : s.locals.lookup (ofString "klen") with _ | kv
          · simp [hkl] at hsz_ev
          · rcases kv with ⟨⟨kw⟩⟩ | _ | _
            · simp [hkl, valueIsWord, valueWord, panOpHOL] at hsz_ev
              exact ⟨kw, rfl, hsz_ev.symm⟩
            · simp [hkl, List.all, valueIsWord] at hsz_ev
            · simp [hkl, List.all, valueIsWord] at hsz_ev
        obtain ⟨klen_w, hklen_s, rfl⟩ := hklen_word
        rw [evaluateHOLFiniteState_seq_line780] at hcont_nt hcont_res ⊢
        set c_ktn : ProgHOL 64 := .call (some (none, none)) (ofString "key_to_nibbles")
          [.var .local (ofString "key"), .var .local (ofString "klen"), .var .local (ofString "nb2")]
        have hc_nt : (evaluateHOLFiniteState mid c_ktn).1 ≠ some .timeOut := by
          rcases hr : evaluateHOLFiniteState mid c_ktn with ⟨r1, _⟩
          rw [hr] at hcont_nt; intro h; subst h; simp at hcont_nt
        have hc_or : (evaluateHOLFiniteState mid c_ktn).1 = none ∨
            Resumes (evaluateHOLFiniteState mid c_ktn).1 := by
          rcases hr : evaluateHOLFiniteState mid c_ktn with ⟨r1, _⟩
          rw [hr] at hcont_res
          cases r1 with
          | none => exact Or.inl rfl
          | some _ => exact Or.inr hcont_res
        obtain ⟨_, nw, ow, _, hnw_ev, how_ev, heff_ktn, _, hdom_ktn⟩ :=
          call0_key_to_nibbles_eff mid _ _ _ hmid_c hmid_AR.1 hc_nt hc_or
        have hnw_eq : klen_w = nw := by
          simp [evalHOLExact, hmid_loc, HolFiniteMapExact.lookup_update, FUPDATE, hklen_s,
            show ofString "nb2" ≠ ofString "klen" by decide] at hnw_ev
          exact hnw_ev
        have how_eq : hp = ow := by
          simp [evalHOLExact, hmid_loc, HolFiniteMapExact.lookup_update, FUPDATE] at how_ev
          exact how_ev
        subst hnw_eq how_eq
        rcases hr_ktn : evaluateHOLFiniteState mid c_ktn with ⟨r_ktn, m_after⟩
        change ByteEff mid (evaluateHOLFiniteState mid c_ktn).2 _ at heff_ktn
        rw [hr_ktn] at heff_ktn
        dsimp only at heff_ktn hcont_res ⊢
        have heff_ktn_free : ByteEff mid m_after (R0 ++ [(globN s "heap_ptr", heapLimit - globN s "heap_ptr")]) := by
          refine heff_ktn.mono (fun iv hiv hipos => ?_)
          simp only [List.mem_singleton] at hiv; subst hiv
          have hpos_kl : 0 < klen_w.toNat := by omega
          obtain ⟨_, hhi_he⟩ := hdom_ktn hpos_kl
          have hhe_lt : heapEnd < 2 ^ 64 := by decide
          have h2kl : (2#64 * klen_w).toNat = 2 * klen_w.toNat := by
            rw [BitVec.toNat_mul]
            have h2_nat : (2#64).toNat = 2 := rfl
            rw [h2_nat, Nat.mod_eq_of_lt (by omega)]
          rw [h2kl] at hq_eq
          refine ⟨(globN s "heap_ptr", heapLimit - globN s "heap_ptr"),
            List.mem_append_right _ (List.mem_singleton.mpr rfl), ?_, ?_⟩ <;> omega
        cases r_ktn with
        | some _ =>
          dsimp only
          have hm_AR : ArenaReady { m_after with locals := m_after.locals.resVarEq (ofString "nb2", s.locals.lookup (ofString "nb2")) } :=
            localsFree_arenaReady m_after (m_after.locals.resVarEq (ofString "nb2", s.locals.lookup (ofString "nb2"))) m_after.clock
              ⟨guestInv_congr heff_ktn.code heff_ktn.memaddrs heff_ktn.shMemaddrs heff_ktn.baseAddr hmid_AR.1,
               arenaOK_congr heff_ktn.globals hmid_AR.2⟩
          refine ⟨hm_AR, ?_, ?_, ?_, ?_⟩
          · rw [← hhp_eq]; simp [globN, heff_ktn.globals, hmid_glob, HolFiniteMapExact.lookup_update, FUPDATE, FUPDATE_HOL]; exact hp_le_q
          · simp [globN, heff_ktn.globals, hmid_glob, HolFiniteMapExact.lookup_update, FUPDATE, FUPDATE_HOL,
              show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
          · intro a hkeep hfresh; by_contra hne
            rw [← hmid_mem] at hne
            obtain ⟨iv, hiv, _, hc1, hc2⟩ := heff_ktn_free.cell_frame a hne
            simp only [List.mem_append, List.mem_singleton] at hiv
            rcases hiv with hR0 | rfl
            · exact hkeep iv (List.mem_append_left _ hR0) ⟨hc1, hc2⟩
            · exact hfresh ⟨hc1, hc2⟩
          · intro k hk
            have hne : k ≠ ofString "heap_ptr" := by simpa using hk
            simp [heff_ktn.globals, hmid_glob, HolFiniteMapExact.lookup_update, FUPDATE, FUPDATE_HOL, hne, Ne.symm hne]
        | none =>
          have hret_eff := byteEff_return m_after ret2 (R0 ++ [(globN s "heap_ptr", heapLimit - globN s "heap_ptr")])
          have heff_tot := heff_ktn_free.trans hret_eff
          set fin := (evaluateHOLFiniteState m_after (.return ret2)).2
          have hm_AR : ArenaReady { fin with locals := fin.locals.resVarEq (ofString "nb2", s.locals.lookup (ofString "nb2")) } :=
            localsFree_arenaReady fin (fin.locals.resVarEq (ofString "nb2", s.locals.lookup (ofString "nb2"))) fin.clock
              ⟨guestInv_congr heff_tot.code heff_tot.memaddrs heff_tot.shMemaddrs heff_tot.baseAddr hmid_AR.1,
               arenaOK_congr heff_tot.globals hmid_AR.2⟩
          refine ⟨hm_AR, ?_, ?_, ?_, ?_⟩
          · rw [← hhp_eq]; simp [globN, heff_tot.globals, hmid_glob, HolFiniteMapExact.lookup_update, FUPDATE, FUPDATE_HOL]; exact hp_le_q
          · simp [globN, heff_tot.globals, hmid_glob, HolFiniteMapExact.lookup_update, FUPDATE, FUPDATE_HOL,
              show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
          · intro a hkeep hfresh; by_contra hne
            rw [← hmid_mem] at hne
            obtain ⟨iv, hiv, _, hc1, hc2⟩ := heff_tot.cell_frame a hne
            simp only [List.mem_append, List.mem_singleton] at hiv
            rcases hiv with hR0 | rfl
            · exact hkeep iv (List.mem_append_left _ hR0) ⟨hc1, hc2⟩
            · exact hfresh ⟨hc1, hc2⟩
          · intro k hk
            have hne : k ≠ ofString "heap_ptr" := by simpa using hk
            simp [heff_tot.globals, hmid_glob, HolFiniteMapExact.lookup_update, FUPDATE, FUPDATE_HOL, hne, Ne.symm hne]
      · -- Branch 1 (`cw ≠ 0`): `keccak256`, then `nb := alloc(64)`, then `key_to_nibbles(..., 32, nb)`, then `return`
        simp only [hcw0, ↓reduceIte] at hnt hres ⊢
        -- Note `dc_nb` never falls through (`none`), so `.seq c_kec dc_nb` never falls through (`none`)!
        have hdc_no_none : ∀ t : PanSemStateFiniteExact 64 F, (evaluateHOLFiniteState t dc_nb).1 ≠ none := by
          intro t; dsimp only [dc_nb]; rw [evaluateHOLFiniteState_decCall_total]
          rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) [.const 64#64] with _ | vals
          · simp
          · simp only
            rcases hl : lookupCodeHOLFinite t.code.lookup (ofString "alloc") vals with _ | ⟨body', callee', ret'⟩
            · simp
            · simp only
              split
              · simp
              · rcases hr : evaluateHOLFiniteState (callEntryStateHOLFinite t callee') body' with ⟨ra, pa⟩
                simp only [hr]
                cases ra with
                | none => simp
                | some r =>
                  cases r with
                  | returned v =>
                    dsimp only [fixClockHOLFinite]
                    split
                    · dsimp only
                      rw [evaluateHOLFiniteState_seq_line780]
                      rcases evaluateHOLFiniteState _ _ with ⟨r_k, t_k⟩
                      cases r_k with
                      | some _ => simp
                      | none => dsimp only; exact return_ne_none t_k _
                    · simp
                  | _ => simp [fixClockHOLFinite]
        have hyes_no_none : (evaluateHOLFiniteState s (.seq c_kec dc_nb)).1 ≠ none := by
          rw [evaluateHOLFiniteState_seq_line780]
          rcases evaluateHOLFiniteState s c_kec with ⟨r1, m1⟩
          cases r1 with
          | some _ => simp
          | none => exact hdc_no_none m1
        rcases hyes : evaluateHOLFiniteState s (.seq c_kec dc_nb) with ⟨r_yes, p_yes⟩
        cases r_yes with
        | none => exact absurd (by rw [hyes]) hyes_no_none
        | some ry =>
          rw [hyes] at hnt hres
          dsimp only at hnt hres ⊢
          rw [evaluateHOLFiniteState_seq_line780] at hyes
          have hkec_sub : ∀ vals,
              evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
                [.var .local (ofString "key"), .var .local (ofString "klen"), .var .global (ofString "mpt_hash_scratch")] = some vals →
              ∀ i ∈ [globBufIvl s.globals "keccak_st" 200, globBufIvl s.globals "keccak_pad" 136,
                     (valWordNat (vals[2]?.getD (.rStruct [])), 32)],
                0 < i.2 → ∃ j ∈ R0, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2 := by
            intro vals hvals i hi hipos
            rw [evalListHOLFinite_eq_toExact] at hvals
            simp only [evalListHOLExact, evalHOLExact] at hvals
            rcases he1 : s.locals.lookup (ofString "key") with _ | v1 <;>
              rcases he2 : s.locals.lookup (ofString "klen") with _ | v2 <;>
              rcases he3 : s.globals.lookup (ofString "mpt_hash_scratch") with _ | v3
            all_goals (try simp [he1, he2, he3] at hvals)
            subst hvals
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl | rfl
            · rw [globBufIvl_eq_bufferRegion] at hipos ⊢
              by_cases hz : globN s "keccak_st" = 0
              · simp [bufferRegion, hz] at hipos
              · simp only [bufferRegion, hz, ↓reduceIte]
                exact ⟨(globN s "keccak_st", 200), by simp [R0], le_rfl, le_rfl⟩
            · rw [globBufIvl_eq_bufferRegion] at hipos ⊢
              by_cases hz : globN s "keccak_pad" = 0
              · simp [bufferRegion, hz] at hipos
              · simp only [bufferRegion, hz, ↓reduceIte]
                exact ⟨(globN s "keccak_pad", 136), by simp [R0], le_rfl, le_rfl⟩
            · have hv3 : valWordNat v3 = globN s "mpt_hash_scratch" := by
                unfold globN; rw [he3]; rcases v3 with ⟨⟨w⟩⟩ | _ | _ <;> rfl
              simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, hv3]
              exact ⟨(globN s "mpt_hash_scratch", 40), by simp [R0], le_rfl, by omega⟩
          rcases hkec : evaluateHOLFiniteState s c_kec with ⟨r_kec, m1⟩
          have hkec_nt : r_kec ≠ some .timeOut := by
            rw [hkec] at hyes; intro h; subst h; cases hyes; exact hnt rfl
          cases r_kec with
          | some rk =>
            rw [hkec] at hyes; dsimp only at hyes; cases hyes
            have heff1 := call0_byteEff funByteEff_keccak256 s _ R0 hc hAR.1 hkec_sub
              (by rw [hkec]; exact hkec_nt) (by rw [hkec]; exact Or.inr hres)
            change ByteEff s (evaluateHOLFiniteState s c_kec).2 R0 at heff1
            rw [hkec] at heff1; dsimp only at heff1
            have hm1_AR : ArenaReady p_yes :=
              ⟨guestInv_congr heff1.code heff1.memaddrs heff1.shMemaddrs heff1.baseAddr hAR.1,
               arenaOK_congr heff1.globals hAR.2⟩
            exact finish_ww p_yes hm1_AR
              (by simp [globN, heff1.globals])
              (fun k _ => by rw [heff1.globals])
              (heff1.mono fun iv hiv _ => ⟨iv, List.mem_append_left _ hiv, le_rfl, le_rfl⟩)
          | none =>
            have heff1 := call0_byteEff funByteEff_keccak256 s _ R0 hc hAR.1 hkec_sub
              (by rw [hkec]; simp) (by rw [hkec]; exact Or.inl rfl)
            change ByteEff s (evaluateHOLFiniteState s c_kec).2 R0 at heff1
            rw [hkec] at heff1 hyes; dsimp only at heff1 hyes
            have hm1_c : m1.code = originalRuntimeCode := heff1.code.trans hc
            have hm1_AR : ArenaReady m1 :=
              ⟨guestInv_congr heff1.code heff1.memaddrs heff1.shMemaddrs heff1.baseAddr hAR.1,
               arenaOK_congr heff1.globals hAR.2⟩
            have hdc_nt : (evaluateHOLFiniteState m1 dc_nb).1 ≠ some .timeOut := by
              rw [hyes]; exact hnt
            have hdc_res : Resumes (evaluateHOLFiniteState m1 dc_nb).1 := by
              rw [hyes]; exact hres
            obtain ⟨hp, sz, q, mid, _, hhp_eq, hsz_ev, _, hq_eq, hp_le_q, hq_hi, _,
                hmid_c, hmid_AR, hmid_mem, hmid_be, hmid_glob, hmid_loc, hcont_nt, hcont_res, hpost_eq⟩ :=
              decCall_alloc_resumes_inv m1 (ofString "nb") _ _ hm1_c hm1_AR hdc_nt hdc_res
            have hsz64 : sz = 64#64 := by simp [evalHOLExact] at hsz_ev; exact hsz_ev.symm
            subst hsz64
            have hhp_s : globN m1 "heap_ptr" = globN s "heap_ptr" := by simp [globN, heff1.globals]
            change (evaluateHOLFiniteState m1 dc_nb).2 = _ at hpost_eq
            rw [hyes] at hpost_eq; dsimp only at hpost_eq
            rw [hpost_eq]
            rw [evaluateHOLFiniteState_seq_line780] at hcont_nt hcont_res ⊢
            set c_ktn : ProgHOL 64 := .call (some (none, none)) (ofString "key_to_nibbles")
              [.var .global (ofString "mpt_hash_scratch"), .const 32#64, .var .local (ofString "nb")]
            have hc_nt : (evaluateHOLFiniteState mid c_ktn).1 ≠ some .timeOut := by
              rcases hr : evaluateHOLFiniteState mid c_ktn with ⟨r1, _⟩
              rw [hr] at hcont_nt; intro h; subst h; simp at hcont_nt
            have hc_or : (evaluateHOLFiniteState mid c_ktn).1 = none ∨
                Resumes (evaluateHOLFiniteState mid c_ktn).1 := by
              rcases hr : evaluateHOLFiniteState mid c_ktn with ⟨r1, _⟩
              rw [hr] at hcont_res
              cases r1 with
              | none => exact Or.inl rfl
              | some _ => exact Or.inr hcont_res
            obtain ⟨_, nw, ow, _, hnw_ev, how_ev, heff_ktn, _, _⟩ :=
              call0_key_to_nibbles_eff mid _ _ _ hmid_c hmid_AR.1 hc_nt hc_or
            have hnw32 : nw = 32#64 := by simp [evalHOLExact] at hnw_ev; exact hnw_ev.symm
            have how_hp : ow = hp := by
              simp [evalHOLExact, hmid_loc, HolFiniteMapExact.lookup_update, FUPDATE] at how_ev
              exact how_ev.symm
            subst hnw32 how_hp
            rcases hr_ktn : evaluateHOLFiniteState mid c_ktn with ⟨r_ktn, m_after⟩
            change ByteEff mid (evaluateHOLFiniteState mid c_ktn).2 _ at heff_ktn
            rw [hr_ktn] at heff_ktn
            dsimp only at heff_ktn hcont_res ⊢
            have heff1_w : ByteEff s m1 (R0 ++ [(globN s "heap_ptr", heapLimit - globN s "heap_ptr")]) :=
              heff1.mono fun iv hiv _ => ⟨iv, List.mem_append_left _ hiv, le_rfl, le_rfl⟩
            have heff_ktn_w : ByteEff mid m_after (R0 ++ [(globN s "heap_ptr", heapLimit - globN s "heap_ptr")]) := by
              refine heff_ktn.mono (fun iv hiv _ => ?_)
              simp only [List.mem_singleton] at hiv; subst hiv
              have h64_nat : (64#64).toNat = 64 := rfl
              have h32_nat : (32#64).toNat = 32 := rfl
              rw [h64_nat] at hq_eq
              rw [h32_nat]
              refine ⟨(globN s "heap_ptr", heapLimit - globN s "heap_ptr"),
                List.mem_append_right _ (List.mem_singleton.mpr rfl), ?_, ?_⟩ <;> omega
            cases r_ktn with
            | some _ =>
              dsimp only
              have hm_AR : ArenaReady { m_after with locals := m_after.locals.resVarEq (ofString "nb", m1.locals.lookup (ofString "nb")) } :=
                localsFree_arenaReady m_after (m_after.locals.resVarEq (ofString "nb", m1.locals.lookup (ofString "nb"))) m_after.clock
                  ⟨guestInv_congr heff_ktn.code heff_ktn.memaddrs heff_ktn.shMemaddrs heff_ktn.baseAddr hmid_AR.1,
                   arenaOK_congr heff_ktn.globals hmid_AR.2⟩
              refine ⟨hm_AR, ?_, ?_, ?_, ?_⟩
              · rw [← hhp_s, ← hhp_eq]; simp [globN, heff_ktn.globals, hmid_glob, HolFiniteMapExact.lookup_update, FUPDATE, FUPDATE_HOL]; exact hp_le_q
              · simp [globN, heff_ktn.globals, hmid_glob, heff1.globals, HolFiniteMapExact.lookup_update, FUPDATE, FUPDATE_HOL,
                  show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
              · intro a hkeep hfresh; by_contra hne
                by_cases hma : m_after.memory a = m1.memory a
                · rw [hma] at hne
                  obtain ⟨iv, hiv, _, hc1, hc2⟩ := heff1_w.cell_frame a hne
                  simp only [List.mem_append, List.mem_singleton] at hiv
                  rcases hiv with hR0 | rfl
                  · exact hkeep iv (List.mem_append_left _ hR0) ⟨hc1, hc2⟩
                  · exact hfresh ⟨hc1, hc2⟩
                · rw [← hmid_mem] at hma
                  obtain ⟨iv, hiv, _, hc1, hc2⟩ := heff_ktn_w.cell_frame a hma
                  simp only [List.mem_append, List.mem_singleton] at hiv
                  rcases hiv with hR0 | rfl
                  · exact hkeep iv (List.mem_append_left _ hR0) ⟨hc1, hc2⟩
                  · exact hfresh ⟨hc1, hc2⟩
              · intro k hk
                have hne : k ≠ ofString "heap_ptr" := by simpa using hk
                simp [heff_ktn.globals, hmid_glob, heff1.globals, HolFiniteMapExact.lookup_update, FUPDATE, FUPDATE_HOL, hne, Ne.symm hne]
            | none =>
              have hret_eff := byteEff_return m_after ret1 (R0 ++ [(globN s "heap_ptr", heapLimit - globN s "heap_ptr")])
              have heff_tot := heff_ktn_w.trans hret_eff
              set fin := (evaluateHOLFiniteState m_after (.return ret1)).2
              have hm_AR : ArenaReady { fin with locals := fin.locals.resVarEq (ofString "nb", m1.locals.lookup (ofString "nb")) } :=
                localsFree_arenaReady fin (fin.locals.resVarEq (ofString "nb", m1.locals.lookup (ofString "nb"))) fin.clock
                  ⟨guestInv_congr heff_tot.code heff_tot.memaddrs heff_tot.shMemaddrs heff_tot.baseAddr hmid_AR.1,
                   arenaOK_congr heff_tot.globals hmid_AR.2⟩
              refine ⟨hm_AR, ?_, ?_, ?_, ?_⟩
              · rw [← hhp_s, ← hhp_eq]; simp [globN, heff_tot.globals, hmid_glob, HolFiniteMapExact.lookup_update, FUPDATE, FUPDATE_HOL]; exact hp_le_q
              · simp [globN, heff_tot.globals, hmid_glob, heff1.globals, HolFiniteMapExact.lookup_update, FUPDATE, FUPDATE_HOL,
                  show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
              · intro a hkeep hfresh; by_contra hne
                by_cases hma : fin.memory a = m1.memory a
                · rw [hma] at hne
                  obtain ⟨iv, hiv, _, hc1, hc2⟩ := heff1_w.cell_frame a hne
                  simp only [List.mem_append, List.mem_singleton] at hiv
                  rcases hiv with hR0 | rfl
                  · exact hkeep iv (List.mem_append_left _ hR0) ⟨hc1, hc2⟩
                  · exact hfresh ⟨hc1, hc2⟩
                · rw [← hmid_mem] at hma
                  obtain ⟨iv, hiv, _, hc1, hc2⟩ := heff_tot.cell_frame a hma
                  simp only [List.mem_append, List.mem_singleton] at hiv
                  rcases hiv with hR0 | rfl
                  · exact hkeep iv (List.mem_append_left _ hR0) ⟨hc1, hc2⟩
                  · exact hfresh ⟨hc1, hc2⟩
              · intro k hk
                have hne : k ≠ ofString "heap_ptr" := by simpa using hk
                simp [heff_tot.globals, hmid_glob, heff1.globals, HolFiniteMapExact.lookup_update, FUPDATE, FUPDATE_HOL, hne, Ne.symm hne]
    · simp [hcond] at hres; exact absurd hres not_resumes_error
    · simp [hcond] at hres; exact absurd hres not_resumes_error

end KeyToNibblesAndMptNibbleKey

section ResolveAndDecodeStep
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.Wave8Contracts.M26
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28

/-- Composable `ArenaReady` write-frame invariant allowing both heap growth `[hp0, heapLimit)`
and free-scratch growth `[fp0, sp0)` while keeping `frame_mem_ptr = fp0` and all globals outside
`["heap_ptr", "scratch_ptr"]` fixed. -/
private def StepFrame {F : Type} (s0 s : PanSemStateFiniteExact 64 F) : Prop :=
  ArenaReady s ∧
  globN s0 "heap_ptr" ≤ globN s "heap_ptr" ∧
  globN s "frame_mem_ptr" = globN s0 "frame_mem_ptr" ∧
  globN s "scratch_ptr" ≤ globN s0 "scratch_ptr" ∧
  FrameOutside s0 s
    [(globN s0 "frame_mem_ptr", globN s0 "scratch_ptr" - globN s0 "frame_mem_ptr")]
    (globN s0 "heap_ptr", heapLimit - globN s0 "heap_ptr") ∧
  ∀ k : MlS, k ∉ (["heap_ptr", "scratch_ptr"] : List String).map ofString →
    s0.globals.lookup k = s.globals.lookup k

private theorem stepFrame_refl {F : Type} {s : PanSemStateFiniteExact 64 F} (hA : ArenaReady s) :
    StepFrame s s :=
  ⟨hA, le_rfl, rfl, le_rfl, fun _ _ _ => rfl, fun _ _ => rfl⟩

private theorem stepFrame_locals_clock {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (h : StepFrame s0 s) (L : HolFiniteMapExact MlS (ValueHOL 64)) (c : Nat) :
    StepFrame s0 { s with locals := L, clock := c } :=
  ⟨localsFree_arenaReady s L c h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

private theorem stepFrame_trans {F : Type} {a b c : PanSemStateFiniteExact 64 F}
    (h1 : StepFrame a b) (h2 : StepFrame b c) : StepFrame a c := by
  refine ⟨h2.1, Nat.le_trans h1.2.1 h2.2.1, h2.2.2.1.trans h1.2.2.1,
    Nat.le_trans h2.2.2.2.1 h1.2.2.2.1, ?_, ?_⟩
  · intro x hkeep hfresh
    have hkb : ∀ i ∈ [(globN b "frame_mem_ptr", globN b "scratch_ptr" - globN b "frame_mem_ptr")],
        ¬ CellHits x.toNat i := by
      intro i hi hch; simp only [List.mem_singleton] at hi; subst hi
      apply hkeep (globN a "frame_mem_ptr", globN a "scratch_ptr" - globN a "frame_mem_ptr")
        (List.mem_singleton.mpr rfl)
      unfold CellHits at hch ⊢; have := h1.2.2.1; have := h1.2.2.2.1; omega
    have hfb : ¬ CellHits x.toNat (globN b "heap_ptr", heapLimit - globN b "heap_ptr") := by
      intro hch; apply hfresh; unfold CellHits at hch ⊢
      have := h1.2.1; have := h1.1.2.2.1; omega
    exact (h2.2.2.2.2.1 x hkb hfb).trans (h1.2.2.2.2.1 x hkeep hfresh)
  · intro k hk
    exact (h1.2.2.2.2.2 k hk).trans (h2.2.2.2.2.2 k hk)

private theorem stepFrame_to_ww {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (h : StepFrame s post) :
    ArenaReady post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
    globN post "scratch_ptr" ≤ globN s "scratch_ptr" ∧
    FrameOutside s post
      ([] ++ [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")])
      (globN s "heap_ptr", heapLimit - globN s "heap_ptr") ∧
    ∀ k ∉ (["heap_ptr", "scratch_ptr"] : List String).map ofString,
      s.globals.lookup k = post.globals.lookup k :=
  ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

private theorem stepFrame_of_ww_sub {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {gw : List String}
    (hsub : ∀ x ∈ gw, x ∈ ["heap_ptr", "scratch_ptr"])
    (hAR : ArenaReady post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hsp : globN post "scratch_ptr" ≤ globN s "scratch_ptr")
    (hfo : FrameOutside s post
      ([] ++ [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")])
      (globN s "heap_ptr", heapLimit - globN s "heap_ptr"))
    (hgl : ∀ k ∉ gw.map ofString, s.globals.lookup k = post.globals.lookup k) :
    StepFrame s post := by
  have hfp_not : ofString "frame_mem_ptr" ∉ gw.map ofString := by
    intro hm
    rcases List.mem_map.mp hm with ⟨x, hx, heq⟩
    have hx' := hsub x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
    rcases hx' with rfl | rfl <;> revert heq <;> decide
  have hfp_eq : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := by
    unfold globN; rw [← hgl _ hfp_not]
  refine ⟨hAR, hhp, hfp_eq, hsp, hfo, ?_⟩
  intro k hk
  refine hgl k (fun hm => hk ?_)
  rcases List.mem_map.mp hm with ⟨x, hx, rfl⟩
  exact List.mem_map.mpr ⟨x, hsub x hx, rfl⟩

private theorem stepFrame_of_byteEff_heap {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAR : ArenaReady s)
    (heff : ByteEff s post [(globN s "heap_ptr", heapLimit - globN s "heap_ptr")]) :
    StepFrame s post := by
  refine ⟨⟨guestInv_congr heff.code heff.memaddrs heff.shMemaddrs heff.baseAddr hAR.1,
           arenaOK_congr heff.globals hAR.2⟩,
    by simp [globN, heff.globals],
    by simp [globN, heff.globals],
    by simp [globN, heff.globals],
    ?_, fun _ _ => by rw [heff.globals]⟩
  intro a _ hfresh; by_contra hne
  obtain ⟨iv, hiv, _, hc1, hc2⟩ := heff.cell_frame a hne
  simp only [List.mem_singleton] at hiv; subst hiv
  exact hfresh ⟨hc1, hc2⟩

private def FlowsOrResumes (r : Option (PanSemResultExact 64)) : Prop :=
  r = none ∨ r = some .break ∨ r = some .continue ∨ Resumes r

private def StepFlowProg (prog : ProgHOL 64) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
    s.code = originalRuntimeCode → ArenaReady s →
    (evaluateHOLFiniteState s prog).1 ≠ some .timeOut →
    FlowsOrResumes (evaluateHOLFiniteState s prog).1 →
    StepFrame s (evaluateHOLFiniteState s prog).2

private theorem StepFlowProg.skip : StepFlowProg .skip := by
  intro _ s _ hAR _ _; rw [evaluateHOLFiniteState_skip]; exact stepFrame_refl hAR

private theorem StepFlowProg.ret (e : ExpHOL 64) : StepFlowProg (.return e) := by
  intro _ s _ hAR _ _
  rw [evaluateHOLFiniteState_return]
  split
  · exact stepFrame_refl hAR
  · split
    · exact stepFrame_locals_clock (stepFrame_refl hAR) _ s.clock
    · exact stepFrame_refl hAR

private theorem StepFlowProg.raise (eid : MlS) (e : ExpHOL 64) : StepFlowProg (.raise eid e) := by
  intro _ s _ hAR _ _
  rw [evaluateHOLFiniteState_raise]
  split
  · dsimp only
    split
    · exact stepFrame_locals_clock (stepFrame_refl hAR) _ s.clock
    · exact stepFrame_refl hAR
  · exact stepFrame_refl hAR

private theorem StepFlowProg.assign_local (name : MlS) (e : ExpHOL 64) :
    StepFlowProg (.assign .local name e) := by
  intro _ s _ hAR _ _
  rw [evaluateHOLFiniteState_assign]
  split
  · exact stepFrame_refl hAR
  · split
    · exact stepFrame_locals_clock (stepFrame_refl hAR) _ s.clock
    · exact stepFrame_refl hAR

private theorem StepFlowProg.seq {a b : ProgHOL 64}
    (ha : StepFlowProg a) (hb : StepFlowProg b) :
    StepFlowProg (.seq a b) := by
  intro F s hc hAR hnt hfr
  rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
  rcases hr1 : evaluateHOLFiniteState s a with ⟨r1, mid⟩
  simp only [hr1] at hnt hfr ⊢
  cases r1 with
  | none =>
    have h1 := ha s hc hAR (by rw [hr1]; simp) (by rw [hr1]; exact Or.inl rfl)
    rw [hr1] at h1; dsimp only at h1 hnt hfr ⊢
    exact stepFrame_trans h1 (hb mid h1.1.1.code h1.1 hnt hfr)
  | some _ =>
    have h1 := ha s hc hAR (by rw [hr1]; exact hnt) (by rw [hr1]; exact hfr)
    rw [hr1] at h1; exact h1

private theorem StepFlowProg.ite (cond : ExpHOL 64) {yes no : ProgHOL 64}
    (hy : StepFlowProg yes) (hn : StepFlowProg no) :
    StepFlowProg (.ite cond yes no) := by
  intro F s hc hAR hnt hfr
  rw [evaluateHOLFiniteState_ite] at hnt hfr ⊢
  revert hnt hfr
  split <;> intro hnt hfr
  · split at hnt
    · rename_i hz; simp only [hz, ↓reduceIte] at hfr ⊢; exact hn s hc hAR hnt hfr
    · rename_i hz; simp only [hz, ↓reduceIte] at hfr ⊢; exact hy s hc hAR hnt hfr
  · exact stepFrame_refl hAR

private theorem StepFlowProg.dec (name : MlS) (sh : ShapeHOL) (init : ExpHOL 64)
    {body : ProgHOL 64} (hb : StepFlowProg body) :
    StepFlowProg (.dec name sh init body) := by
  intro F s hc hAR hnt hfr
  rw [evaluateHOLFiniteState_dec_total] at hnt hfr ⊢
  dsimp only at hnt hfr ⊢
  revert hnt hfr
  split <;> intro hnt hfr
  · exact stepFrame_refl hAR
  · rename_i v _
    by_cases hsh : shapeEqHOL sh (shapeOfHOLExact v) = true
    · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
      have hAR' : ArenaReady (setVarHOLFinite name v s) :=
        ⟨guestInv_setVar name v s hAR.1, hAR.2⟩
      have hpre : StepFrame s (setVarHOLFinite name v s) :=
        stepFrame_locals_clock (stepFrame_refl hAR) _ s.clock
      exact stepFrame_locals_clock (stepFrame_trans hpre (hb _ hc hAR' hnt hfr)) _ _
    · simp only [hsh, Bool.false_eq_true, ↓reduceIte]; exact stepFrame_refl hAR

private theorem StepFlowProg.while_loop (cond : ExpHOL 64) {body : ProgHOL 64}
    (hbody : StepFlowProg body) :
    StepFlowProg (.while cond body) := by
  intro F s hc hAR hnt hfr
  generalize hk : s.clock = k
  induction k using Nat.strongRecOn generalizing s with
  | ind k ih =>
    subst hk
    rw [evaluateHOLFiniteState_while_total] at hnt hfr ⊢
    revert hnt hfr
    split <;> intro hnt hfr
    · rename_i w _
      by_cases hnz : w = 0
      · subst hnz; simp only [ne_eq, not_true_eq_false, ↓reduceIte]; exact stepFrame_refl hAR
      · rw [if_pos hnz] at hnt hfr ⊢
        by_cases hclk : s.clock = 0
        · rw [if_pos hclk] at hnt; simp at hnt
        · rw [if_neg hclk] at hnt hfr ⊢
          dsimp only at hnt hfr ⊢
          rw [fixClockHOLFinite_evaluateState] at hnt hfr ⊢
          have hARd : ArenaReady (decClockHOLFinite s) :=
            localsFree_arenaReady s s.locals (s.clock - 1) hAR
          have hdecF : StepFrame s (decClockHOLFinite s) :=
            stepFrame_locals_clock (stepFrame_refl hAR) _ _
          have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          rcases hrun : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          simp only [hrun] at hrem hnt hfr ⊢
          change mid.clock ≤ s.clock - 1 at hrem
          have hlt : mid.clock < s.clock := by omega
          cases r1 with
          | none =>
            have hb1 := hbody (decClockHOLFinite s) hc hARd (by rw [hrun]; simp) (by rw [hrun]; exact Or.inl rfl)
            rw [hrun] at hb1; dsimp only at hb1
            exact stepFrame_trans (stepFrame_trans hdecF hb1)
              (ih mid.clock hlt mid hb1.1.1.code hb1.1 hnt hfr rfl)
          | some res =>
            cases res with
            | «continue» =>
              have hb1 := hbody (decClockHOLFinite s) hc hARd (by rw [hrun]; simp) (by rw [hrun]; exact Or.inr (Or.inr (Or.inl rfl)))
              rw [hrun] at hb1; dsimp only at hb1
              exact stepFrame_trans (stepFrame_trans hdecF hb1)
                (ih mid.clock hlt mid hb1.1.1.code hb1.1 hnt hfr rfl)
            | «break» =>
              have hb1 := hbody (decClockHOLFinite s) hc hARd (by rw [hrun]; simp) (by rw [hrun]; exact Or.inr (Or.inl rfl))
              rw [hrun] at hb1; exact stepFrame_trans hdecF hb1
            | timeOut => simp at hnt
            | returned v =>
              have hb1 := hbody (decClockHOLFinite s) hc hARd (by rw [hrun]; simp) (by rw [hrun]; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨v, rfl⟩))))
              rw [hrun] at hb1; exact stepFrame_trans hdecF hb1
            | exception e v =>
              have hres : Resumes (some (.exception e v)) := by
                rcases hfr with h | h | h | hr <;> [simp at h; simp at h; simp at h; exact hr]
              have hb1 := hbody (decClockHOLFinite s) hc hARd (by rw [hrun]; simp) (by rw [hrun]; exact Or.inr (Or.inr (Or.inr hres)))
              rw [hrun] at hb1; exact stepFrame_trans hdecF hb1
            | error =>
              rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
            | finalFfi _ =>
              rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
    · exact stepFrame_refl hAR

private theorem stepFrame_of_ro {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAR : ArenaReady s) (heq : post = { s with locals := post.locals, clock := post.clock }) :
    StepFrame s post := by
  rw [heq]; exact stepFrame_locals_clock (stepFrame_refl hAR) _ _

private theorem StepFlowProg.call0_ro {fname : MlS} (hf : ReadOnlyFn fname) (args : List (ExpHOL 64)) :
    StepFlowProg (.call (some (none, none)) fname args) := by
  obtain ⟨params, body, ret, hlook, hspec⟩ := hf
  intro F s hc hAR hnt hfr
  rw [evaluateHOLFiniteState_call] at hnt hfr ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · exact stepFrame_refl hAR
  · simp only [hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body', callee, ret'⟩
    · exact stepFrame_refl hAR
    · simp only [hl] at hnt hfr ⊢
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup fname params body body'
        ret ret' vals callee (by rw [hc]; exact hlook) hl
      subst hsame
      have hret := lookupCodeHOLFinite_installed_return s fname params body' body'
        ret ret' vals callee (by rw [hc]; exact hlook) hl
      subst hret
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt hfr ⊢
        let entry := callEntryStateHOLFinite s callee
        have hex : ∃ vs, lookupCodeHOLFinite originalRuntimeCode.lookup fname vs =
            some (body', entry.locals, ret') := ⟨vals, by simpa [hc, entry, callEntryStateHOLFinite] using hl⟩
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, post⟩
        simp only [hrun] at hnt hfr ⊢
        cases res with
        | none => rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hfr ⊢
            split
            · have hro := hspec entry hc (guestInv_callEntry s callee hAR.1) hex
                (by dsimp only [entry]; rw [hrun]; simp) (by dsimp only [entry]; rw [hrun]; exact Or.inl ⟨v, rfl⟩)
              dsimp only [entry] at hro; rw [hrun] at hro; dsimp only at hro
              have hp : post = { s with locals := post.locals, clock := post.clock } := by
                rw [hro]; cases s; rfl
              exact stepFrame_locals_clock (stepFrame_of_ro hAR hp) _ _
            · rename_i hbad; rw [if_neg hbad] at hfr
              rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
          | exception e v =>
            have hres : Resumes (some (.exception e v)) := by
              rcases hfr with h | h | h | hr <;> [simp at h; simp at h; simp at h; exact hr]
            have hro := hspec entry hc (guestInv_callEntry s callee hAR.1) hex
              (by dsimp only [entry]; rw [hrun]; simp) (by dsimp only [entry]; rw [hrun]; exact hres)
            dsimp only [entry] at hro; rw [hrun] at hro; dsimp only at hro
            have hp : post = { s with locals := post.locals, clock := post.clock } := by
              rw [hro]; cases s; rfl
            exact stepFrame_locals_clock (stepFrame_of_ro hAR hp) _ _
          | timeOut => simp at hnt
          | _ => rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h

private theorem StepFlowProg.decCall_ro {fname : MlS} (hf : ReadOnlyFn fname)
    (name : MlS) (sh : ShapeHOL) (args : List (ExpHOL 64)) {cont : ProgHOL 64}
    (hcont : StepFlowProg cont) :
    StepFlowProg (.decCall name sh fname args cont) := by
  obtain ⟨params, body, ret, hlook, hspec⟩ := hf
  intro F s hc hAR hnt hfr
  rw [evaluateHOLFiniteState_decCall_total] at hnt hfr ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · exact stepFrame_refl hAR
  · simp only [hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body', callee, ret'⟩
    · exact stepFrame_refl hAR
    · simp only [hl] at hnt hfr ⊢
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup fname params body body'
        ret ret' vals callee (by rw [hc]; exact hlook) hl
      subst hsame
      have hret := lookupCodeHOLFinite_installed_return s fname params body' body'
        ret ret' vals callee (by rw [hc]; exact hlook) hl
      subst hret
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt hfr ⊢
        try dsimp only at hnt hfr ⊢
        rw [fixClockHOLFinite_evaluateState] at hnt hfr ⊢
        let entry := callEntryStateHOLFinite s callee
        have hex : ∃ vs, lookupCodeHOLFinite originalRuntimeCode.lookup fname vs =
            some (body', entry.locals, ret') := ⟨vals, by simpa [hc, entry, callEntryStateHOLFinite] using hl⟩
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, post⟩
        simp only [hrun] at hnt hfr ⊢
        cases res with
        | none => rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hnt hfr ⊢
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact v) sh &&
                shapeEqHOL (shapeOfHOLExact v) ret') = true
            · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
              have hro := hspec entry hc (guestInv_callEntry s callee hAR.1) hex
                (by dsimp only [entry]; rw [hrun]; simp) (by dsimp only [entry]; rw [hrun]; exact Or.inl ⟨v, rfl⟩)
              dsimp only [entry] at hro; rw [hrun] at hro; dsimp only at hro
              have hp : post = { s with locals := post.locals, clock := post.clock } := by
                rw [hro]; cases s; rfl
              let cstate := setVarHOLFinite name v { post with locals := s.locals }
              have hcstate : cstate = { s with locals := cstate.locals, clock := post.clock } := by
                dsimp only [cstate, setVarHOLFinite]; rw [hp]
              have hpre : StepFrame s cstate := stepFrame_of_ro hAR hcstate
              exact stepFrame_locals_clock (stepFrame_trans hpre (hcont cstate hpre.1.1.code hpre.1 hnt hfr)) _ _
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hfr
              rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
          | exception e v =>
            have hres : Resumes (some (.exception e v)) := by
              rcases hfr with h | h | h | hr <;> [simp at h; simp at h; simp at h; exact hr]
            have hro := hspec entry hc (guestInv_callEntry s callee hAR.1) hex
              (by dsimp only [entry]; rw [hrun]; simp) (by dsimp only [entry]; rw [hrun]; exact hres)
            dsimp only [entry] at hro; rw [hrun] at hro; dsimp only at hro
            have hp : post = { s with locals := post.locals, clock := post.clock } := by
              rw [hro]; cases s; rfl
            exact stepFrame_locals_clock (stepFrame_of_ro hAR hp) _ _
          | timeOut => simp at hnt
          | _ => rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h

private theorem StepFlowProg.decCall_ww {fname : MlS} {gw : List String}
    (hsub : ∀ x ∈ gw, x ∈ ["heap_ptr", "scratch_ptr"])
    (hf : WritesWithin (fun _ => []) gw fname)
    (name : MlS) (sh : ShapeHOL) (args : List (ExpHOL 64)) {cont : ProgHOL 64}
    (hcont : StepFlowProg cont) :
    StepFlowProg (.decCall name sh fname args cont) := by
  obtain ⟨params, body, ret, hlook, hspec⟩ := hf
  intro F s hc hAR hnt hfr
  rw [evaluateHOLFiniteState_decCall_total] at hnt hfr ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · exact stepFrame_refl hAR
  · simp only [hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body', callee, ret'⟩
    · exact stepFrame_refl hAR
    · simp only [hl] at hnt hfr ⊢
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup fname params body body'
        ret ret' vals callee (by rw [hc]; exact hlook) hl
      subst hsame
      have hret := lookupCodeHOLFinite_installed_return s fname params body' body'
        ret ret' vals callee (by rw [hc]; exact hlook) hl
      subst hret
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt hfr ⊢
        try dsimp only at hnt hfr ⊢
        rw [fixClockHOLFinite_evaluateState] at hnt hfr ⊢
        let entry := callEntryStateHOLFinite s callee
        have hARe : ArenaReady entry := localsFree_arenaReady s callee (s.clock - 1) hAR
        have hex : ∃ vs, lookupCodeHOLFinite originalRuntimeCode.lookup fname vs =
            some (body', entry.locals, ret') := ⟨vals, by simpa [hc, entry, callEntryStateHOLFinite] using hl⟩
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, post⟩
        simp only [hrun] at hnt hfr ⊢
        cases res with
        | none => rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hnt hfr ⊢
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact v) sh &&
                shapeEqHOL (shapeOfHOLExact v) ret') = true
            · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
              obtain ⟨hARp, hhp, hsp, hfo, hgl⟩ := hspec entry hc hARe hex
                (by dsimp only [entry]; rw [hrun]; simp) (by dsimp only [entry]; rw [hrun]; exact Or.inl ⟨v, rfl⟩)
              dsimp only [entry] at hARp hhp hsp hfo hgl
              rw [hrun] at hARp hhp hsp hfo hgl
              have hsf1 : StepFrame entry post := stepFrame_of_ww_sub hsub hARp hhp hsp hfo hgl
              have hsf_s : StepFrame s post :=
                stepFrame_trans (stepFrame_locals_clock (stepFrame_refl hAR) _ _) hsf1
              let cstate := setVarHOLFinite name v { post with locals := s.locals }
              have hpre : StepFrame s cstate := stepFrame_locals_clock hsf_s cstate.locals post.clock
              exact stepFrame_locals_clock (stepFrame_trans hpre (hcont cstate hpre.1.1.code hpre.1 hnt hfr)) _ _
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hfr
              rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
          | exception e v =>
            have hres : Resumes (some (.exception e v)) := by
              rcases hfr with h | h | h | hr <;> [simp at h; simp at h; simp at h; exact hr]
            obtain ⟨hARp, hhp, hsp, hfo, hgl⟩ := hspec entry hc hARe hex
              (by dsimp only [entry]; rw [hrun]; simp) (by dsimp only [entry]; rw [hrun]; exact hres)
            dsimp only [entry] at hARp hhp hsp hfo hgl
            rw [hrun] at hARp hhp hsp hfo hgl
            have hsf1 : StepFrame entry post := stepFrame_of_ww_sub hsub hARp hhp hsp hfo hgl
            have hsf_s : StepFrame s post :=
              stepFrame_trans (stepFrame_locals_clock (stepFrame_refl hAR) _ _) hsf1
            exact stepFrame_locals_clock hsf_s _ post.clock
          | timeOut => simp at hnt
          | _ => rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h

private theorem StepFlowProg.handledCall_ww {fname : MlS} {gw : List String}
    (hsub : ∀ x ∈ gw, x ∈ ["heap_ptr", "scratch_ptr"])
    (hf : WritesWithin (fun _ => []) gw fname)
    (destVar : MlS) (eid evar : MlS) (hntrap_eid : eid ≠ ofString "TrapErr") {handler : ProgHOL 64}
    (hhand : StepFlowProg handler) (args : List (ExpHOL 64)) :
    StepFlowProg (.call (some (some (.local, destVar), some (eid, evar, handler))) fname args) := by
  obtain ⟨params, body, ret, hlook, hspec⟩ := hf
  intro F s hc hAR hnt hfr
  rw [evaluateHOLFiniteState_call] at hnt hfr ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · exact stepFrame_refl hAR
  · simp only [hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body', callee, ret'⟩
    · exact stepFrame_refl hAR
    · simp only [hl] at hnt hfr ⊢
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup fname params body body'
        ret ret' vals callee (by rw [hc]; exact hlook) hl
      subst hsame
      have hret := lookupCodeHOLFinite_installed_return s fname params body' body'
        ret ret' vals callee (by rw [hc]; exact hlook) hl
      subst hret
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt hfr ⊢
        let entry := callEntryStateHOLFinite s callee
        have hARe : ArenaReady entry := localsFree_arenaReady s callee (s.clock - 1) hAR
        have hex : ∃ vs, lookupCodeHOLFinite originalRuntimeCode.lookup fname vs =
            some (body', entry.locals, ret') := ⟨vals, by simpa [hc, entry, callEntryStateHOLFinite] using hl⟩
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, post⟩
        simp only [hrun] at hnt hfr ⊢
        cases res with
        | none => rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hnt hfr ⊢
            split
            · try dsimp only at hnt hfr ⊢
              split
              · obtain ⟨hARp, hhp, hsp, hfo, hgl⟩ := hspec entry hc hARe hex
                  (by dsimp only [entry]; rw [hrun]; simp) (by dsimp only [entry]; rw [hrun]; exact Or.inl ⟨v, rfl⟩)
                dsimp only [entry] at hARp hhp hsp hfo hgl
                rw [hrun] at hARp hhp hsp hfo hgl
                have hsf_s : StepFrame s post :=
                  stepFrame_trans (stepFrame_locals_clock (stepFrame_refl hAR) _ _)
                    (stepFrame_of_ww_sub hsub hARp hhp hsp hfo hgl)
                exact stepFrame_locals_clock hsf_s _ post.clock
              · rename_i hbad; rw [if_neg hbad] at hfr
                rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
            · rename_i hbad; rw [if_neg hbad] at hfr
              rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
          | exception exId exVal =>
            dsimp only at hnt hfr ⊢
            by_cases heq : exId = eid
            · subst exId
              rw [if_pos rfl] at hnt hfr ⊢
              have hsf_s : StepFrame s post := by
                obtain ⟨hARp, hhp, hsp, hfo, hgl⟩ := hspec entry hc hARe hex
                  (by dsimp only [entry]; rw [hrun]; simp)
                  (by dsimp only [entry]; rw [hrun]; exact Or.inr ⟨eid, exVal, rfl, hntrap_eid⟩)
                dsimp only [entry] at hARp hhp hsp hfo hgl
                rw [hrun] at hARp hhp hsp hfo hgl
                exact stepFrame_trans (stepFrame_locals_clock (stepFrame_refl hAR) _ _)
                  (stepFrame_of_ww_sub hsub hARp hhp hsp hfo hgl)
              rcases hes : s.eshapes.lookup eid with _ | declSh
              · simp only [hes] at hfr
                rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
              · simp only [hes] at hnt hfr ⊢
                by_cases hsh : (shapeEqHOL (shapeOfHOLExact exVal) declSh &&
                    isValidValueHOLExact s.toExact .local evar exVal) = true
                · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
                  let hstate := setVarHOLFinite evar exVal { post with locals := s.locals }
                  have hpre : StepFrame s hstate := stepFrame_locals_clock hsf_s hstate.locals post.clock
                  exact stepFrame_locals_clock (stepFrame_trans hpre (hhand hstate hpre.1.1.code hpre.1 hnt hfr)) _ _
                · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hfr
                  rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
            · rw [if_neg heq] at hnt hfr ⊢
              have hres : Resumes (some (.exception exId exVal)) := by
                rcases hfr with h | h | h | hr <;> [simp at h; simp at h; simp at h; exact hr]
              have hntrap : exId ≠ ofString "TrapErr" := by
                rcases hres with ⟨_, h⟩ | ⟨e', v', h, hnt⟩
                · simp at h
                · injection h with h; injection h with he1 _; exact he1 ▸ hnt
              obtain ⟨hARp, hhp, hsp, hfo, hgl⟩ := hspec entry hc hARe hex
                (by dsimp only [entry]; rw [hrun]; simp)
                (by dsimp only [entry]; rw [hrun]; exact Or.inr ⟨exId, exVal, rfl, hntrap⟩)
              dsimp only [entry] at hARp hhp hsp hfo hgl
              rw [hrun] at hARp hhp hsp hfo hgl
              have hsf_s : StepFrame s post :=
                stepFrame_trans (stepFrame_locals_clock (stepFrame_refl hAR) _ _)
                  (stepFrame_of_ww_sub hsub hARp hhp hsp hfo hgl)
              exact stepFrame_locals_clock hsf_s _ post.clock
          | timeOut => simp at hnt
          | _ => rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h

private theorem stepFrame_storeW_at {F : Type} {s : PanSemStateFiniteExact 64 F}
    {d e : ExpHOL 64} (addr w : BitVec 64)
    (hAR : ArenaReady s)
    (hd : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) d =
      some (.val (.word addr)))
    (he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e =
      some (.val (.word w)))
    (hin : CellHits addr.toNat (globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr") ∨
           CellHits addr.toNat (globN s "heap_ptr", heapLimit - globN s "heap_ptr")) :
    StepFrame s (evaluateHOLFiniteState s (.store d e)).2 ∧
    ∀ m, evaluateHOLFiniteState s (.store d e) = (none, m) →
      m = { s with memory := updW s.memory addr w } := by
  rw [evaluateHOLFiniteState_store, hd, he]
  dsimp only
  rcases hm : @panMemStoresHOL 64 _ addr (flattenHOL (.val (.word w))) s.memaddrs
      (fun x => Classical.propDecidable (s.memaddrs x)) s.memory with _ | mem'
  · exact ⟨stepFrame_refl hAR, fun _ h => by simp at h⟩
  · obtain ⟨_, rfl⟩ := stores_word _ hm
    refine ⟨?_, fun m h => by injection h with _ hm'; exact hm'.symm⟩
    refine ⟨⟨⟨hAR.1.code, hAR.1.memaddrs, hAR.1.shMemaddrs, hAR.1.baseAddr⟩, hAR.2⟩,
      le_rfl, rfl, le_rfl, ?_, fun _ _ => rfl⟩
    intro a hkeep hfresh
    have hne : a ≠ addr := by
      rintro rfl
      rcases hin with hk | hf
      · exact hkeep _ (List.mem_singleton.mpr rfl) hk
      · exact hfresh hf
    simp [updW, hne]

private theorem stepFrame_seq_storeW {F : Type} {s : PanSemStateFiniteExact 64 F}
    {d e : ExpHOL 64} {rest : ProgHOL 64} (addr w : BitVec 64)
    (hAR : ArenaReady s)
    (hd : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) d =
      some (.val (.word addr)))
    (he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e =
      some (.val (.word w)))
    (hin : CellHits addr.toNat (globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr") ∨
           CellHits addr.toNat (globN s "heap_ptr", heapLimit - globN s "heap_ptr"))
    (hrest : StepFrame { s with memory := updW s.memory addr w }
      (evaluateHOLFiniteState { s with memory := updW s.memory addr w } rest).2) :
    StepFrame s (evaluateHOLFiniteState s (.seq (.store d e) rest)).2 := by
  obtain ⟨hsf1, hnone⟩ := stepFrame_storeW_at addr w hAR hd he hin
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hr : evaluateHOLFiniteState s (.store d e) with ⟨r1, m⟩
  rw [hr] at hsf1
  cases r1 with
  | some _ => exact hsf1
  | none =>
    have hm := hnone m hr
    subst hm
    exact stepFrame_trans hsf1 hrest

private theorem lookup_node_new_hashed_r10 :
    originalRuntimeCode.lookup (ofString "node_new_hashed") =
      some ([(ofString "hash", .one)], sourceFnBody Guest.Software.guestFn_node_new_hashed, .one) :=
  lookup_of_guestAst_getElem 255 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_node_new_hashed) rfl

private structure PureMemFrame {F : Type} (s0 s : PanSemStateFiniteExact 64 F) (fresh : Ivl) : Prop where
  code       : s.code = s0.code
  memaddrs   : s.memaddrs = s0.memaddrs
  shMemaddrs : s.shMemaddrs = s0.shMemaddrs
  baseAddr   : s.baseAddr = s0.baseAddr
  globals    : s.globals = s0.globals
  frame      : FrameOutside s0 s [] fresh

private theorem pureMemFrame_refl {F : Type} (s : PanSemStateFiniteExact 64 F) (fresh : Ivl) :
    PureMemFrame s s fresh :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩

private theorem pureMemFrame_return {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) (fresh : Ivl) :
    PureMemFrame s (evaluateHOLFiniteState s (.return e)).2 fresh := by
  rw [evaluateHOLFiniteState_return]
  split
  · exact pureMemFrame_refl s fresh
  · split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩

private theorem pureMemFrame_seq_storeW {F : Type} {s : PanSemStateFiniteExact 64 F}
    {d e : ExpHOL 64} {rest : ProgHOL 64} {fresh : Ivl} (addr w : BitVec 64)
    (hd : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) d =
      some (.val (.word addr)))
    (he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e =
      some (.val (.word w)))
    (hin : CellHits addr.toNat fresh)
    (hrest : ∀ M, PureMemFrame { s with memory := M }
      (evaluateHOLFiniteState { s with memory := M } rest).2 fresh) :
    PureMemFrame s (evaluateHOLFiniteState s (.seq (.store d e) rest)).2 fresh := by
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_store, hd, he]; dsimp only
  rcases hm : @panMemStoresHOL 64 _ addr (flattenHOL (.val (.word w))) s.memaddrs
      (fun x => Classical.propDecidable (s.memaddrs x)) s.memory with _ | mem'
  · exact pureMemFrame_refl s fresh
  · obtain ⟨_, rfl⟩ := stores_word _ hm
    dsimp only
    have hr := hrest (updW s.memory addr w)
    refine ⟨hr.code, hr.memaddrs, hr.shMemaddrs, hr.baseAddr, hr.globals, ?_⟩
    intro a hkeep hfresh
    rw [hr.frame a hkeep hfresh]
    have hne : a ≠ addr := by rintro rfl; exact hfresh hin
    simp [updW, hne]

private theorem ww_node_new_hashed_aux :
    WritesWithin (fun _ => []) ["heap_ptr"] (ofString "node_new_hashed") := by
  refine ⟨_, _, _, lookup_node_new_hashed_r10, ?_⟩
  intro F s hc hAR hlookup hnt hres
  obtain ⟨vals, hvals⟩ := hlookup
  obtain ⟨wh, _, hwh_s⟩ := lookupCode_one_word lookup_node_new_hashed_r10 hvals
  have hbody : sourceFnBody Guest.Software.guestFn_node_new_hashed =
      .decCall (ofString "nd") .one (ofString "alloc") [.const 32#64]
        (.seq (.store (.op .add [.var .local (ofString "nd"), .const 0#64]) (.const 0#64))
          (.seq (.store (.op .add [.var .local (ofString "nd"), .const 8#64]) (.const 0#64))
            (.seq (.store (.op .add [.var .local (ofString "nd"), .const 16#64]) (.const 0#64))
              (.seq (.store (.op .add [.var .local (ofString "nd"), .const 24#64]) (.var .local (ofString "hash")))
                (.return (.var .local (ofString "nd"))))))) := rfl
  rw [hbody] at hnt hres ⊢
  obtain ⟨hp, sz, q, mid, _, hhp_eq, hsz_ev, _, hq_eq, hp_le_q, hq_hi, _,
      _, hmid_AR, hmid_mem, _, hmid_glob, hmid_loc, _, _, hpost_eq⟩ :=
    decCall_alloc_resumes_inv s (ofString "nd") _ _ hc hAR hnt hres
  have hsz32 : sz = 32#64 := by simp [evalHOLExact] at hsz_ev; exact hsz_ev.symm
  subst hsz32
  have h32_nat : (32#64).toNat = 32 := rfl
  rw [h32_nat] at hq_eq
  rw [hpost_eq]
  let fresh : Ivl := (globN s "heap_ptr", heapLimit - globN s "heap_ptr")
  have hcell : ∀ off : BitVec 64, off.toNat ≤ 24 → CellHits (hp + off).toNat fresh := by
    intro off hoff
    have hhe : heapLimit < 2 ^ 64 := by decide
    have htn : (hp + off).toNat = hp.toNat + off.toNat := by
      simp only [BitVec.toNat_add]; omega
    unfold CellHits; dsimp only [fresh]; rw [htn, ← hhp_eq]; omega
  have hnd_add : ∀ (t : PanSemStateFiniteExact 64 F) (off : BitVec 64), t.locals = mid.locals →
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
        (.op .add [.var .local (ofString "nd"), .const off]) = some (.val (.word (hp + off))) := by
    intro t off htl
    simp [evalHOLExact, evalListHOLExact, htl, hmid_loc, HolFiniteMapExact.lookup_update, FUPDATE,
      valueIsWord, valueWord, wordOpHOL, wordOp]
  have hpmf : PureMemFrame mid (evaluateHOLFiniteState mid
      (.seq (.store (.op .add [.var .local (ofString "nd"), .const 0#64]) (.const 0#64))
        (.seq (.store (.op .add [.var .local (ofString "nd"), .const 8#64]) (.const 0#64))
          (.seq (.store (.op .add [.var .local (ofString "nd"), .const 16#64]) (.const 0#64))
            (.seq (.store (.op .add [.var .local (ofString "nd"), .const 24#64]) (.var .local (ofString "hash")))
              (.return (.var .local (ofString "nd")))))))).2 fresh := by
    refine pureMemFrame_seq_storeW (hp + 0#64) 0#64 (hnd_add _ _ rfl) rfl (hcell 0#64 (by decide)) fun M1 => ?_
    refine pureMemFrame_seq_storeW (hp + 8#64) 0#64 (hnd_add _ _ rfl) rfl (hcell 8#64 (by decide)) fun M2 => ?_
    refine pureMemFrame_seq_storeW (hp + 16#64) 0#64 (hnd_add _ _ rfl) rfl (hcell 16#64 (by decide)) fun M3 => ?_
    refine pureMemFrame_seq_storeW (hp + 24#64) wh (hnd_add _ _ rfl)
      (by simp [evalHOLExact, hmid_loc, HolFiniteMapExact.lookup_update, FUPDATE, hwh_s,
            show ofString "nd" ≠ ofString "hash" by decide])
      (hcell 24#64 (by decide)) fun M4 => ?_
    exact pureMemFrame_return _ _ fresh
  set fin := (evaluateHOLFiniteState mid
      (.seq (.store (.op .add [.var .local (ofString "nd"), .const 0#64]) (.const 0#64))
        (.seq (.store (.op .add [.var .local (ofString "nd"), .const 8#64]) (.const 0#64))
          (.seq (.store (.op .add [.var .local (ofString "nd"), .const 16#64]) (.const 0#64))
            (.seq (.store (.op .add [.var .local (ofString "nd"), .const 24#64]) (.var .local (ofString "hash")))
              (.return (.var .local (ofString "nd")))))))).2
  have hfin_AR : ArenaReady { fin with locals := fin.locals.resVarEq (ofString "nd", s.locals.lookup (ofString "nd")) } :=
    localsFree_arenaReady fin _ fin.clock
      ⟨guestInv_congr hpmf.code hpmf.memaddrs hpmf.shMemaddrs hpmf.baseAddr hmid_AR.1,
       arenaOK_congr hpmf.globals hmid_AR.2⟩
  refine ⟨hfin_AR, ?_, ?_, ?_, ?_⟩
  · rw [← hhp_eq]; simp [globN, hpmf.globals, hmid_glob, HolFiniteMapExact.lookup_update, FUPDATE, FUPDATE_HOL]; exact hp_le_q
  · simp [globN, hpmf.globals, hmid_glob, HolFiniteMapExact.lookup_update, FUPDATE, FUPDATE_HOL,
      show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
  · intro a _ hfresh
    exact (hpmf.frame a (fun _ h => nomatch h) hfresh).trans (congrFun hmid_mem a)
  · intro k hk
    have hne : k ≠ ofString "heap_ptr" := by simpa using hk
    simp [hpmf.globals, hmid_glob, HolFiniteMapExact.lookup_update, FUPDATE, FUPDATE_HOL, hne, Ne.symm hne]

private theorem rt_node_new_hashed_aux :
    Returns ArenaReady (fun s post nd => FreshBlock s post nd 32) (ofString "node_new_hashed") := by
  refine ⟨_, _, _, lookup_node_new_hashed_r10, ?_⟩
  intro F s hc hAR hlookup _hnt v hret
  obtain ⟨vals, hvals⟩ := hlookup
  obtain ⟨wh, _, hwh_s⟩ := lookupCode_one_word lookup_node_new_hashed_r10 hvals
  obtain ⟨hG, hA⟩ := hAR
  obtain ⟨hp, _, _, hhp, hhp_eq, _, _, _, _⟩ := arenaOK_globals s hA
  have hbody : sourceFnBody Guest.Software.guestFn_node_new_hashed =
      .decCall (ofString "nd") .one (ofString "alloc") [.const 32#64]
        (.seq (.store (.op .add [.var .local (ofString "nd"), .const 0#64]) (.const 0#64))
          (.seq (.store (.op .add [.var .local (ofString "nd"), .const 8#64]) (.const 0#64))
            (.seq (.store (.op .add [.var .local (ofString "nd"), .const 16#64]) (.const 0#64))
              (.seq (.store (.op .add [.var .local (ofString "nd"), .const 24#64]) (.var .local (ofString "hash")))
                (.return (.var .local (ofString "nd"))))))) := rfl
  have hrun : Ret s (sourceFnBody Guest.Software.guestFn_node_new_hashed)
      (fun val post => ∃ w : BitVec 64, val = .val (.word w) ∧
        ArenaReady post ∧ AllocatorGrows s post ∧ FreshBlock s post w.toNat 32) := by
    rw [hbody]
    apply Ret.of_NS
    refine Ret.ns_alloc hc 32#64 rfl hp hhp ?_
    intro hcmp1 hcmp2
    set q : BitVec 64 := (hp + (32#64 + 7)) &&& ((0 : BitVec 64) - 8)
    set L1 := s.locals.update (ofString "nd", .val (.word hp))
    set G1 := s.globals.update (ofString "heap_ptr", .val (.word q))
    have hnd_ev : ∀ M off, ev (NS s L1 G1 M (s.clock - 1))
        (.op .add [.var .local (ofString "nd"), .const off]) = some (.val (.word (hp + off))) := fun _ _ => by
      simp [ev, evalHOLExact, evalListHOLExact, L1, HolFiniteMapExact.lookup_update, FUPDATE,
        valueIsWord, valueWord, wordOpHOL, wordOp]
    refine Ret.ns_storeW (hp + 0#64) 0#64 (hnd_ev _ _) rfl fun _ => ?_
    refine Ret.ns_storeW (hp + 8#64) 0#64 (hnd_ev _ _) rfl fun _ => ?_
    refine Ret.ns_storeW (hp + 16#64) 0#64 (hnd_ev _ _) rfl fun _ => ?_
    refine Ret.ns_storeW (hp + 24#64) wh (hnd_ev _ _)
      (by simp [ev, evalHOLExact, L1, HolFiniteMapExact.lookup_update, FUPDATE, hwh_s,
            show ofString "nd" ≠ ofString "hash" by decide]) fun _ => ?_
    refine Ret.ns_ret fun val hval => ?_
    have hv : val = .val (.word hp) := by
      simp [ev, evalHOLExact, L1, HolFiniteMapExact.lookup_update, FUPDATE] at hval; exact hval.symm
    subst hv
    refine ⟨hp, rfl, ?_⟩
    set M4 := updW (updW (updW (updW s.memory (hp + 0#64) 0#64) (hp + 8#64) 0#64) (hp + 16#64) 0#64) (hp + 24#64) wh
    set post : PanSemStateFiniteExact 64 F :=
      { (NS s (emptyLocalsHOLFinite (NS s L1 G1 M4 (s.clock - 1))).locals G1 M4 (s.clock - 1)) with
        locals := HolFiniteMapExact.resVarEq
          (emptyLocalsHOLFinite (NS s L1 G1 M4 (s.clock - 1))).locals
          (ofString "nd", s.locals.lookup (ofString "nd")) }
    have hhp_hi : hp.toNat ≤ heapLimit := by rw [hhp_eq]; exact hA.2.1
    have hhp_al : hp.toNat % 8 = 0 := by rw [hhp_eq]; exact hA.2.2.2.2.2.1
    obtain ⟨hq_eq, hq_hi, hq_al, hp_le_q⟩ :=
      InitECandidate.Solver.Wave8GuestInv.R10Shards.P02.alloc_arith hp 32#64 hhp_hi hhp_al hcmp1 hcmp2
    change q.toNat = _ at hq_eq
    change q.toNat ≤ heapLimit at hq_hi
    change q.toNat % 8 = 0 at hq_al
    change hp.toNat ≤ q.toNat at hp_le_q
    have h32 : ((32#64).toNat + 7) / 8 * 8 = 32 := by decide
    rw [h32] at hq_eq
    change ArenaReady post ∧ AllocatorGrows s post ∧ FreshBlock s post hp.toNat 32
    have hpost_hp : globN post "heap_ptr" = q.toNat := by
      simp [post, NS, G1, globN, HolFiniteMapExact.lookup_update, FUPDATE]
    have hpost_fp : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := by
      simp [post, NS, G1, globN, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide]
    have hpost_sp : globN post "scratch_ptr" = globN s "scratch_ptr" := by
      simp [post, NS, G1, globN, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
    have hG_post : GuestInv post := ⟨hG.code, hG.memaddrs, hG.shMemaddrs, hG.baseAddr⟩
    have hsb_le : sourceBase ≤ hp.toNat := by rw [hhp_eq]; exact hA.1
    have hlim_le_he : heapLimit ≤ heapEnd := by decide
    have hA_post : ArenaOK post := by
      unfold ArenaOK; rw [hpost_hp, hpost_fp, hpost_sp]
      exact ⟨by omega, hq_hi, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2.1, hq_al, hA.2.2.2.2.2.2.1,
        hA.2.2.2.2.2.2.2.1,
        globalsWord_update (s := s) (t := post) (ofString "heap_ptr") q rfl hA.2.2.2.2.2.2.2.2⟩
    refine ⟨⟨hG_post, hA_post⟩, ⟨by rw [hpost_hp, ← hhp_eq]; exact hp_le_q, by rw [hpost_sp]⟩,
      hhp_al, ?_, ?_⟩
    · change Inside (hp.toNat, 32) (globN s "heap_ptr") (globN post "heap_ptr")
      rw [← hhp_eq, hpost_hp]; exact ⟨le_rfl, le_of_eq hq_eq.symm⟩
    · change WordsOK post (hp.toNat, 32)
      exact wordsOK_of_guestInv post hG_post hp.toNat 32 hhp_al (by decide) hsb_le (by omega)
  exact hrun v hret

theorem «ww__resolve_step» :
    WritesWithin (fun s => [])
    ["heap_ptr", "scratch_ptr"] (ofString "_resolve_step") := by
  refine ⟨_, _, _, lookup_of_guestAst_getElem 260 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__resolve_step) rfl, ?_⟩
  intro F s hc hAR _ hnt hres
  have hsub_sp : ∀ x ∈ (["scratch_ptr"] : List String), x ∈ ["heap_ptr", "scratch_ptr"] := by
    intro x hx; simp at hx; subst hx; simp
  have hsub_hp : ∀ x ∈ (["heap_ptr"] : List String), x ∈ ["heap_ptr", "scratch_ptr"] := by
    intro x hx; simp at hx; subst hx; simp
  have hf : StepFlowProg
      (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn__resolve_step).body) := by
    dsimp only [Guest.Software.guestFn__resolve_step, extractFn,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, Option.map]
    exact StepFlowProg.dec _ _ _
      (StepFlowProg.dec _ _ _
        (StepFlowProg.seq
          (StepFlowProg.handledCall_ww hsub_sp «ww_rlp_item» _ _ _ (by decide)
            (StepFlowProg.call0_ro «ro_mpt_fail» _) _)
          (StepFlowProg.seq
            (StepFlowProg.ite _
              (StepFlowProg.seq
                (StepFlowProg.ite _ (StepFlowProg.ret _) StepFlowProg.skip)
                (StepFlowProg.seq
                  (StepFlowProg.ite _ (StepFlowProg.call0_ro «ro_mpt_fail» _) StepFlowProg.skip)
                  (StepFlowProg.decCall_ro «ro_nodedb_lookup» _ _ _
                    (StepFlowProg.seq
                      (StepFlowProg.ite _
                        (StepFlowProg.decCall_ww hsub_hp ww_node_new_hashed_aux _ _ _
                          (StepFlowProg.ret _))
                        StepFlowProg.skip)
                      (StepFlowProg.ret _)))))
              StepFlowProg.skip)
            (StepFlowProg.ret _))))
  exact stepFrame_to_ww (hf s hc hAR hnt (Or.inr (Or.inr (Or.inr hres))))

theorem «sp__resolve_step» :
    ResolvesNode (ofString "_resolve_step") := by
  refine ⟨_, _, _, lookup_of_guestAst_getElem 260 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__resolve_step) rfl, ?_⟩
  intro F s hc hAR hlookup hnt v hret
  obtain ⟨vals, hvals⟩ := hlookup
  -- Extract that `p` and `n` are words in `s.locals`!
  have hlook_rs : originalRuntimeCode.lookup (ofString "_resolve_step") =
      some ([(ofString "db", .one), (ofString "p", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn__resolve_step, .comb [.one, .one, .one, .one]) :=
    lookup_of_guestAst_getElem 260 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn__resolve_step) rfl
  have hthree_words : ∃ wdb wp wn : BitVec 64,
      s.locals.lookup (ofString "db") = some (.val (.word wdb)) ∧
      s.locals.lookup (ofString "p") = some (.val (.word wp)) ∧
      s.locals.lookup (ofString "n") = some (.val (.word wn)) := by
    have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup _ vals _ s.locals _ hvals
    simp only [lookupCodeHOLExact, hlook_rs] at hx
    rcases vals with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩⟩ <;> try (simp at hx)
    rcases v0 with ⟨⟨w0⟩⟩ | _ | _ <;> rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;>
      rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hx
    obtain ⟨_, _, hL, _⟩ := hx
    refine ⟨w0, w1, w2, ?_, ?_, ?_⟩ <;>
      (rw [← hL]; simp [show ofString "db" ≠ ofString "p" by decide,
        show ofString "db" ≠ ofString "n" by decide,
        show ofString "p" ≠ ofString "n" by decide,
        show ofString "p" ≠ ofString "db" by decide,
        show ofString "n" ≠ ofString "db" by decide,
        show ofString "n" ≠ ofString "p" by decide])
  obtain ⟨_, wp, wn, _, hwp_s, hwn_s⟩ := hthree_words
  have hcall_noret : ∀ (t : PanSemStateFiniteExact 64 F) f args (u : ValueHOL 64),
      (evaluateHOLFiniteState t (.call (some (none, none)) f args)).1 ≠ some (.returned u) := by
    intro t f args u
    rw [evaluateHOLFiniteState_call]
    split
    · simp
    · split
      · simp
      · split
        · simp
        · rcases evaluateHOLFiniteState (callEntryStateHOLFinite t _) _ with ⟨r, _⟩
          rcases r with _ | (_ | _ | _ | _ | _ | _ | _) <;> dsimp only <;> (repeat' split) <;> simp
  have hhandled_noret : ∀ (t : PanSemStateFiniteExact 64 F) dv eid evar f args fargs (u : ValueHOL 64),
      (evaluateHOLFiniteState t (.call (some (some (.local, dv),
        some (eid, evar, .call (some (none, none)) f fargs))) (ofString "rlp_item") args)).1 ≠
        some (.returned u) := by
    intro t dv eid evar f args fargs u
    rw [evaluateHOLFiniteState_call]
    split
    · simp
    · split
      · simp
      · split
        · simp
        · rcases evaluateHOLFiniteState (callEntryStateHOLFinite t _) _ with ⟨r, post⟩
          cases r with
          | none => simp
          | some r' =>
            cases r' with
            | exception exId exVal =>
              dsimp only
              split
              · split
                · try dsimp only
                  split
                  · exact hcall_noret _ f fargs u
                  · simp
                · simp
              · simp
            | _ => dsimp only; (repeat' split) <;> simp
  dsimp only [Guest.Software.guestFn__resolve_step, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    List.map, Option.map] at hnt hret ⊢
  rw [evaluateHOLFiniteState_dec_total] at hnt hret ⊢; dsimp only at hnt hret ⊢
  have hit_init : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.rStruct [.const 0#64, .const 0#64, .const 0#64, .const 0#64]) =
      some (.rStruct [.val (.word 0#64), .val (.word 0#64), .val (.word 0#64), .val (.word 0#64)]) := rfl
  rw [hit_init] at hnt hret ⊢; dsimp only at hnt hret ⊢
  have hsh_it : shapeEqHOL (.comb [.one, .one, .one, .one])
      (shapeOfHOLExact (.rStruct [.val (.word 0#64), .val (.word 0#64), .val (.word 0#64), .val (.word 0#64)])) = true := by
    decide
  rw [if_pos hsh_it] at hnt hret ⊢; dsimp only at hnt hret ⊢
  set s1 := setVarHOLFinite (ofString "it")
    (.rStruct [.val (.word 0#64), .val (.word 0#64), .val (.word 0#64), .val (.word 0#64)]) s
  rw [evaluateHOLFiniteState_dec_total] at hnt hret ⊢; dsimp only at hnt hret ⊢
  have he_init : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
      (.const 0#64) = some (.val (.word 0#64)) := rfl
  rw [he_init] at hnt hret ⊢; dsimp only at hnt hret ⊢
  have hsh_e : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0#64))) = true := by decide
  rw [if_pos hsh_e] at hnt hret ⊢; dsimp only at hnt hret ⊢
  set s2 := setVarHOLFinite (ofString "e") (.val (.word 0#64)) s1
  have hs2_c : s2.code = originalRuntimeCode := hc
  have hs2_AR : ArenaReady s2 := localsFree_arenaReady s s2.locals s.clock hAR
  have hs2_hp : globN s2 "heap_ptr" = globN s "heap_ptr" := rfl
  have hs2_p : s2.locals.lookup (ofString "p") = some (.val (.word wp)) := by
    simp [s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hwp_s,
      show ofString "e" ≠ ofString "p" by decide, show ofString "it" ≠ ofString "p" by decide]
  have hs2_n : s2.locals.lookup (ofString "n") = some (.val (.word wn)) := by
    simp [s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hwn_s,
      show ofString "e" ≠ ofString "n" by decide, show ofString "it" ≠ ofString "n" by decide]
  rw [evaluateHOLFiniteState_seq_line780] at hnt hret ⊢
  set c_rlp := ProgHOL.call (some (some (.local, ofString "it"),
      some (ofString "RlpErr", ofString "e", .call (some (none, none)) (ofString "mpt_fail") [.const 3#64])))
    (ofString "rlp_item") [.var .local (ofString "p"), .var .local (ofString "n")]
  have hsf_rlp : StepFlowProg c_rlp :=
    StepFlowProg.handledCall_ww (by intro x hx; simp at hx; subst hx; simp) «ww_rlp_item»
      _ _ _ (by decide) (StepFlowProg.call0_ro «ro_mpt_fail» _) _
  rcases h1 : evaluateHOLFiniteState s2 c_rlp with ⟨r1, s3⟩
  rw [h1] at hnt hret ⊢
  cases r1 with
  | some _ => exact absurd hret (by rw [← h1]; exact hhandled_noret s2 _ _ _ _ _ _ v)
  | none =>
    dsimp only at hnt hret ⊢
    have hsf3 := hsf_rlp s2 hs2_c hs2_AR (by rw [h1]; simp) (by rw [h1]; exact Or.inl rfl)
    rw [h1] at hsf3; dsimp only at hsf3
    -- Note `c_rlp` returned `none`, so `rlp_item` returned normally and wrote `it` (with shape `.comb [.one, .one, .one, .one]`), preserving `p` and `n`!
    have hs3_pn_it : s3.locals.lookup (ofString "p") = some (.val (.word wp)) ∧
        s3.locals.lookup (ofString "n") = some (.val (.word wn)) ∧
        ∃ i0 i1 i2 i3 : BitVec 64,
          s3.locals.lookup (ofString "it") =
            some (.rStruct [.val (.word i0), .val (.word i1), .val (.word i2), .val (.word i3)]) := by
      have h1' := h1
      dsimp only [c_rlp] at h1'
      rw [evaluateHOLFiniteState_call] at h1'
      rcases hargs_r : evalListHOLFinite s2 (h := fun a => Classical.propDecidable (s2.memaddrs a))
          [.var .local (ofString "p"), .var .local (ofString "n")] with _ | vr
      · simp [hargs_r] at h1'
      · rw [hargs_r] at h1'; dsimp only at h1'
        rcases hl_r : lookupCodeHOLFinite s2.code.lookup (ofString "rlp_item") vr with _ | ⟨br, cr, rr⟩
        · simp [hl_r] at h1'
        · rw [hl_r] at h1'; dsimp only at h1'
          have hlook_ri : originalRuntimeCode.lookup (ofString "rlp_item") =
              some ([(ofString "p", .one), (ofString "len", .one)],
                sourceFnBody Guest.Software.guestFn_rlp_item, .comb [.one, .one, .one, .one]) :=
            lookup_of_guestAst_getElem 107 (by rw [guestAst_len]; decide)
              (extractFn Guest.Software.guestFn_rlp_item) rfl
          have hrr := lookupCodeHOLFinite_installed_return s2 _ _ br br _ rr vr cr
            (by rw [hs2_c]; exact hlook_ri) hl_r
          subst hrr
          split at h1'
          · simp at h1'
          · rcases hrun_r : evaluateHOLFiniteState (callEntryStateHOLFinite s2 cr) br with ⟨rr_res, pr⟩
            rw [hrun_r] at h1'
            cases rr_res with
            | none => simp at h1'
            | some rr_val =>
              cases rr_val with
              | returned rv =>
                dsimp only at h1'
                split at h1'
                · rename_i hsh_rv
                  dsimp only at h1'
                  split at h1'
                  · injection h1' with _ hs3_eq; subst hs3_eq
                    rcases rv with _ | fs | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hsh_rv
                    rcases fs with _ | ⟨f0, _ | ⟨f1, _ | ⟨f2, _ | ⟨f3, _ | _⟩⟩⟩⟩ <;>
                      simp [shapeOfHOLExact, shapeEqHOL] at hsh_rv
                    rcases f0 with ⟨⟨i0⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hsh_rv
                    rcases f1 with ⟨⟨i1⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hsh_rv
                    rcases f2 with ⟨⟨i2⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hsh_rv
                    rcases f3 with ⟨⟨i3⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hsh_rv
                    refine ⟨?_, ?_, i0, i1, i2, i3, ?_⟩
                    · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_p,
                        show ofString "it" ≠ ofString "p" by decide]
                    · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_n,
                        show ofString "it" ≠ ofString "n" by decide]
                    · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                  · simp at h1'
                · simp at h1'
              | exception exId exVal =>
                dsimp only at h1'
                split at h1'
                · split at h1'
                  · simp only at h1'
                    split at h1'
                    · have hnn : (evaluateHOLFiniteState _ (.call (some (none, none)) (ofString "mpt_fail") [.const 3#64])).1 ≠ none := by
                        rw [evaluateHOLFiniteState_call]
                        split
                        · simp
                        · split
                          · simp
                          · rename_i b_mf c_mf r_mf hl_mf
                            have hlook_mf : originalRuntimeCode.lookup (ofString "mpt_fail") =
                                some ([(ofString "code", .one)], sourceFnBody Guest.Software.guestFn_mpt_fail, .one) :=
                              lookup_of_guestAst_getElem 246 (by rw [guestAst_len]; decide)
                                (extractFn Guest.Software.guestFn_mpt_fail) rfl
                            have hc_pr : pr.code = originalRuntimeCode :=
                              (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s2 cr) br).1
                                |>.trans hs2_c |> fun h => by rw [hrun_r] at h; exact h
                            have hb_mf := lookupCodeHOLFinite_installed_body pr.code.lookup _ _ _ b_mf _ r_mf _ c_mf
                              (by rw [hc_pr]; exact hlook_mf) hl_mf
                            subst hb_mf
                            split
                            · simp
                            · have hbody_mf : sourceFnBody Guest.Software.guestFn_mpt_fail =
                                  .seq (.raise (ofString "MptErr") (.var .local (ofString "code"))) (.return (.const 0#64)) := rfl
                              have hmfn : (evaluateHOLFiniteState (callEntryStateHOLFinite _ c_mf)
                                  (sourceFnBody Guest.Software.guestFn_mpt_fail)).1 ≠ none := by
                                rw [hbody_mf, evaluateHOLFiniteState_seq_line780]
                                rcases evaluateHOLFiniteState _ (.raise _ _) with ⟨rm, tm⟩
                                cases rm with
                                | some _ => simp
                                | none => dsimp only; exact return_ne_none tm _
                              rcases hr_mf : evaluateHOLFiniteState (callEntryStateHOLFinite _ c_mf)
                                  (sourceFnBody Guest.Software.guestFn_mpt_fail) with ⟨rmf, _⟩
                              rw [hr_mf] at hmfn
                              cases rmf with
                              | none => exact absurd rfl hmfn
                              | some rmf' => cases rmf' <;> dsimp only <;> (repeat' split) <;> simp
                      exact absurd (congrArg Prod.fst h1') hnn
                    · simp at h1'
                  · simp at h1'
                · simp at h1'
              | _ => simp at h1'
    obtain ⟨hs3_p, hs3_n, i0, i1, i2, i3, hs3_it⟩ := hs3_pn_it
    -- Notice `hsf3.2.1 : globN s2 "heap_ptr" ≤ globN s3 "heap_ptr"` (actually `ww_rlp_item` keeps `heap_ptr` equal!)
    rw [evaluateHOLFiniteState_seq_line780] at hnt hret ⊢
    -- Evaluate outer `ite (it.0 == 0)` on `s3`:
    rw [evaluateHOLFiniteState_ite] at hnt hret ⊢
    have hev_it0 : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
        (.cmp .equal (.field 0 (.var .local (ofString "it"))) (.const 0#64)) =
        some (.val (.word (if i0 = 0#64 then 1#64 else 0#64))) := by
      simp only [evalHOLExact, evalListHOLExact, hs3_it, Compiler.Encoders.Asm.wordCmpHOL]
      by_cases h : i0 = 0#64 <;> simp [h]
    change (match evalHOLFinite s3 _ with | _ => _) ≠ _ at hnt
    rw [evalHOLFinite_eq_toExact, hev_it0] at hnt hret ⊢
    by_cases hi0 : i0 = 0#64
    · subst hi0
      simp only [↓reduceIte, show (1#64 : BitVec 64) ≠ 0 by decide, not_false_eq_true] at hnt hret ⊢
      -- Inside `it.0 == 0` branch:
      -- `.seq (.ite (it.2 == 0) (return [0,0,0,0]) skip) (.seq (.ite (it.2 != 32) (mpt_fail 10) skip) (decCall r := nodedb_lookup ...))`
      rw [evaluateHOLFiniteState_seq_line780] at hnt hret ⊢
      have hev_it2_0 : evalHOLFinite s3
          (.cmp .equal (.field 2 (.var .local (ofString "it"))) (.const 0#64)) =
          some (.val (.word (if i2 = 0#64 then 1#64 else 0#64))) := by
        rw [evalHOLFinite_eq_toExact]
        simp only [evalHOLExact, evalListHOLExact, hs3_it, Compiler.Encoders.Asm.wordCmpHOL]
        by_cases h : i2 = 0#64 <;> simp [h]
      by_cases hi2_0 : i2 = 0#64
      · subst hi2_0
        rw [evaluateHOLFiniteState_ite, hev_it2_0] at hret ⊢
        simp only [↓reduceIte, show (1#64 : BitVec 64) ≠ 0 by decide, not_false_eq_true] at hret ⊢
        rw [evaluateHOLFiniteState_return] at hret
        have hret0 : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
            (InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural
              (.rStruct [.const 0#64, .const 0#64, .const 0#64, .const 0#64])) =
            some (.rStruct [.val (.word 0#64), .val (.word 0#64), .val (.word 0#64), .val (.word 0#64)]) := rfl
        rw [hret0] at hret; dsimp only at hret
        split at hret <;> simp at hret
        subst hret
        exact ⟨0#64, 0#64, 0#64, 0#64, rfl, fun _ => Or.inl rfl⟩
      · rw [evaluateHOLFiniteState_ite, hev_it2_0, if_neg hi2_0] at hnt hret ⊢
        simp only [↓reduceIte, evaluateHOLFiniteState_skip] at hnt hret ⊢
        rw [evaluateHOLFiniteState_seq_line780] at hnt hret ⊢
        have hev_it2_32 : evalHOLFinite s3
            (.cmp .notEqual (.field 2 (.var .local (ofString "it"))) (.const 32#64)) =
            some (.val (.word (if i2 ≠ 32#64 then 1#64 else 0#64))) := by
          rw [evalHOLFinite_eq_toExact]
          simp only [evalHOLExact, evalListHOLExact, hs3_it, Compiler.Encoders.Asm.wordCmpHOL]
          by_cases h : i2 = 32#64 <;> simp [h]
        by_cases hi2_32 : i2 = 32#64
        · subst hi2_32
          rw [evaluateHOLFiniteState_ite, hev_it2_32] at hnt hret ⊢
          simp only [ne_eq, not_true_eq_false, ↓reduceIte, evaluateHOLFiniteState_skip] at hnt hret ⊢
          -- Now `decCall "r" (.comb [.one, .one, .one]) "nodedb_lookup" [db, it.1] cont` on `s3`!
          -- Note `nodedb_lookup` is `ro_nodedb_lookup`! If `decCall` returns `some (.returned v)` (or note the outer `.seq _ (return [1,p,n,0])` — wait: can `decCall "r"` fall through (`none`)? NO! Because its body ends in `.return [1, r.1, r.2, it.1]`!)
          rw [evaluateHOLFiniteState_decCall_total] at hnt hret ⊢
          rcases hargs_nd : evalListHOLFinite s3 (h := fun a => Classical.propDecidable (s3.memaddrs a))
              [.var .local (ofString "db"), .field 1 (.var .local (ofString "it"))] with _ | v_nd
          · simp [hargs_nd] at hret
          · simp only [hargs_nd] at hnt hret ⊢
            rcases hl_nd : lookupCodeHOLFinite s3.code.lookup (ofString "nodedb_lookup") v_nd with _ | ⟨b_nd, c_nd, r_nd⟩
            · simp [hl_nd] at hret
            · simp only [hl_nd] at hnt hret ⊢
              obtain ⟨p_nd, b_nd0, r_nd0, hlook_nd, hspec_nd⟩ := «ro_nodedb_lookup»
              have hb_eq := lookupCodeHOLFinite_installed_body s3.code.lookup _ p_nd b_nd0 b_nd r_nd0 r_nd v_nd c_nd
                (by rw [hsf3.1.1.code]; exact hlook_nd) hl_nd
              subst hb_eq
              have hr_eq := lookupCodeHOLFinite_installed_return s3 _ p_nd b_nd b_nd r_nd0 r_nd v_nd c_nd
                (by rw [hsf3.1.1.code]; exact hlook_nd) hl_nd
              subst hr_eq
              by_cases hz3 : s3.clock = 0
              · simp [hz3] at hnt
              · simp only [hz3, ↓reduceIte] at hnt hret ⊢
                try dsimp only at hnt hret ⊢
                rw [fixClockHOLFinite_evaluateState] at hnt hret ⊢
                rcases hrun_nd : evaluateHOLFiniteState (callEntryStateHOLFinite s3 c_nd) b_nd with ⟨res_nd, post_nd⟩
                simp only [hrun_nd] at hnt hret ⊢
                cases res_nd with
                | none => simp at hret
                | some rnd =>
                  cases rnd with
                  | returned v_r =>
                    dsimp only at hnt hret ⊢
                    by_cases hsh_r : (shapeEqHOL (shapeOfHOLExact v_r) (.comb [.one, .one, .one]) &&
                        shapeEqHOL (shapeOfHOLExact v_r) r_nd) = true
                    · simp only [hsh_r, ↓reduceIte] at hnt hret ⊢
                      have hsh_r1 : shapeEqHOL (shapeOfHOLExact v_r) (.comb [.one, .one, .one]) = true :=
                        (Bool.and_eq_true _ _).mp hsh_r |>.1
                      rcases v_r with _ | fs_r | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hsh_r1
                      rcases fs_r with _ | ⟨fr0, _ | ⟨fr1, _ | ⟨fr2, _ | _⟩⟩⟩ <;>
                        simp [shapeOfHOLExact, shapeEqHOL] at hsh_r1
                      rcases fr0 with ⟨⟨r0⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hsh_r1
                      rcases fr1 with ⟨⟨r1w⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hsh_r1
                      rcases fr2 with ⟨⟨r2w⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hsh_r1
                      have hro_nd := hspec_nd (callEntryStateHOLFinite s3 c_nd) hsf3.1.1.code
                        (guestInv_callEntry s3 c_nd hsf3.1.1)
                        ⟨v_nd, by simpa [hsf3.1.1.code, callEntryStateHOLFinite] using hl_nd⟩
                        (by rw [hrun_nd]; simp) (by rw [hrun_nd]; exact Or.inl ⟨_, rfl⟩)
                      rw [hrun_nd] at hro_nd; dsimp only at hro_nd
                      set s4 := setVarHOLFinite (ofString "r")
                        (.rStruct [.val (.word r0), .val (.word r1w), .val (.word r2w)])
                        { post_nd with locals := s3.locals }
                      have hs4_eq : s4 = { s3 with locals := s4.locals, clock := post_nd.clock } := by
                        dsimp only [s4, setVarHOLFinite]; rw [hro_nd]; cases s3; rfl
                      have hs4_AR : ArenaReady s4 := by
                        rw [hs4_eq]; exact localsFree_arenaReady s3 s4.locals post_nd.clock hsf3.1
                      have hs4_r : s4.locals.lookup (ofString "r") =
                          some (.rStruct [.val (.word r0), .val (.word r1w), .val (.word r2w)]) := by
                        simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                      have hs4_it : s4.locals.lookup (ofString "it") =
                          some (.rStruct [.val (.word 0#64), .val (.word i1), .val (.word 32#64), .val (.word i3)]) := by
                        simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_it,
                          show ofString "r" ≠ ofString "it" by decide]
                      -- Now on `s4`: `.seq (.ite (r.0 == 0) (decCall hn := node_new_hashed [it.1] (return [0, hn, 0, 0])) skip) (return [1, r.1, r.2, it.1])`
                      -- First note this continuation NEVER returns `none`!
                      set cont_r := ProgHOL.seq
                        (.ite (.cmp .equal (.field 0 (.var .local (ofString "r"))) (.const 0#64))
                          (.decCall (ofString "hn") .one (ofString "node_new_hashed")
                            [.field 1 (.var .local (ofString "it"))]
                            (.return (InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural
                              (.rStruct [.const 0#64, .var .local "hn", .const 0#64, .const 0#64]))))
                          .skip)
                        (.return (InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural
                          (.rStruct [.const 1#64, .rField 1 (.var .local "r"),
                            .rField 2 (.var .local "r"), .rField 1 (.var .local "it")])))
                      have hcont_nn : (evaluateHOLFiniteState s4 cont_r).1 ≠ none := by
                        dsimp only [cont_r]; rw [evaluateHOLFiniteState_seq_line780]
                        rcases evaluateHOLFiniteState s4 _ with ⟨rc1, tc1⟩
                        cases rc1 with
                        | some _ => simp
                        | none => dsimp only; exact return_ne_none tc1 _
                      rcases hcr : evaluateHOLFiniteState s4 cont_r with ⟨rc_out, pc_out⟩
                      cases rc_out with
                      | none => exact absurd (congrArg Prod.fst hcr) hcont_nn
                      | some rc_val =>
                        change (match (let co := evaluateHOLFiniteState s4 cont_r; (co.1, _)).1 with | _ => _) = _ at hret
                        simp only [hcr] at hnt hret ⊢
                        -- Now `hret : some rc_val = some (.returned v)` and post-state is `{ pc_out with locals := ... }`!
                        dsimp only [cont_r] at hcr
                        rw [evaluateHOLFiniteState_seq_line780] at hcr
                        have hev_r0 : evalHOLFinite s4
                            (.cmp .equal (.field 0 (.var .local (ofString "r"))) (.const 0#64)) =
                            some (.val (.word (if r0 = 0#64 then 1#64 else 0#64))) := by
                          rw [evalHOLFinite_eq_toExact]
                          simp only [evalHOLExact, evalListHOLExact, hs4_r, Compiler.Encoders.Asm.wordCmpHOL]
                          by_cases h : r0 = 0#64 <;> simp [h]
                        by_cases hr0_z : r0 = 0#64
                        · subst hr0_z
                          rw [evaluateHOLFiniteState_ite, hev_r0] at hcr
                          simp only [↓reduceIte, show (1#64 : BitVec 64) ≠ 0 by decide, not_false_eq_true] at hcr
                          -- Now `decCall "hn" .one "node_new_hashed" [it.1] (return [0, hn, 0, 0])` on `s4`!
                          set dc_hn := ProgHOL.decCall (ofString "hn") .one (ofString "node_new_hashed")
                            [.field 1 (.var .local (ofString "it"))]
                            (.return (InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural
                              (.rStruct [.const 0#64, .var .local "hn", .const 0#64, .const 0#64])))
                          have hdc_nn : (evaluateHOLFiniteState s4 dc_hn).1 ≠ none := by
                            dsimp only [dc_hn]; rw [evaluateHOLFiniteState_decCall_total]
                            rcases evalListHOLFinite s4 (h := fun a => Classical.propDecidable (s4.memaddrs a))
                              [.field 1 (.var .local (ofString "it"))] with _ | vs_h
                            · simp
                            · simp only
                              rcases lookupCodeHOLFinite s4.code.lookup (ofString "node_new_hashed") vs_h with _ | ⟨bh, ch, rh⟩
                              · simp
                              · simp only; split
                                · simp
                                · rcases hr_h : evaluateHOLFiniteState (callEntryStateHOLFinite s4 ch) bh with ⟨rh_r, _⟩
                                  simp only [hr_h]
                                  cases rh_r with
                                  | none => simp
                                  | some rhv =>
                                    cases rhv with
                                    | returned _ =>
                                      dsimp only [fixClockHOLFinite]; split
                                      · dsimp only; exact return_ne_none _ _
                                      · simp
                                    | _ => simp [fixClockHOLFinite]
                          rcases hdh : evaluateHOLFiniteState s4 dc_hn with ⟨rdh, pdh⟩
                          rw [hdh] at hcr
                          cases rdh with
                          | none => exact absurd (congrArg Prod.fst hdh) hdc_nn
                          | some rdh_v =>
                            dsimp only at hcr; injection hcr with hrc_eq hpc_eq; subst hrc_eq hpc_eq
                            injection hret with hret_eq; subst hret_eq
                            -- Unpack `dc_hn` returning `v` using `rt_node_new_hashed_aux`!
                            dsimp only [dc_hn] at hdh
                            rw [evaluateHOLFiniteState_decCall_total] at hdh
                            have hargs_hn : evalListHOLFinite s4 (h := fun a => Classical.propDecidable (s4.memaddrs a))
                                [.field 1 (.var .local (ofString "it"))] = some [.val (.word i1)] := by
                              rw [evalListHOLFinite_eq_toExact]
                              simp [evalListHOLExact, evalHOLExact, hs4_it]
                            rw [hargs_hn] at hdh; dsimp only at hdh
                            have hl_hn := pan_one_word_lookup s4.code.lookup (ofString "node_new_hashed")
                              (ofString "hash") (sourceFnBody Guest.Software.guestFn_node_new_hashed) i1
                              (by rw [hs4_AR.1.code]; exact lookup_node_new_hashed_r10)
                            rw [hl_hn] at hdh; dsimp only at hdh
                            split at hdh
                            · simp at hdh
                            · rw [fixClockHOLFinite_evaluateState] at hdh
                              let ent_hn := callEntryStateHOLFinite s4
                                (HolFiniteMapExact.empty.update (ofString "hash", .val (.word i1)))
                              rcases hrun_hn : evaluateHOLFiniteState ent_hn
                                  (sourceFnBody Guest.Software.guestFn_node_new_hashed) with ⟨r_hn, p_hn⟩
                              dsimp only [ent_hn] at hrun_hn
                              rw [hrun_hn] at hdh
                              cases r_hn with
                              | none => simp at hdh
                              | some r_hn' =>
                                cases r_hn' with
                                | returned v_hn =>
                                  dsimp only at hdh
                                  split at hdh
                                  · dsimp only at hdh
                                    obtain ⟨_, _, _, _, hspec_rt⟩ := rt_node_new_hashed_aux
                                    --Wait: `lookup_node_new_hashed_r10` gives exact body!
                                    have hrt := hspec_rt ent_hn hs4_AR.1.code
                                      (localsFree_arenaReady s4 _ _ hs4_AR)
                                      ⟨[.val (.word i1)], by
                                        simpa [hs4_AR.1.code, ent_hn, callEntryStateHOLFinite] using hl_hn⟩
                                      (by dsimp only [ent_hn]; rw [hrun_hn]; simp)
                                      v_hn (by dsimp only [ent_hn]; rw [hrun_hn])
                                    obtain ⟨ndw, rfl, hAR_phn, _, hFB_hn⟩ := hrt
                                    dsimp only [ent_hn] at hAR_phn hFB_hn
                                    rw [hrun_hn] at hAR_phn hFB_hn; dsimp only at hAR_phn hFB_hn
                                    -- Now evaluate `.return [0, hn, 0, 0]`!
                                    set s5 := setVarHOLFinite (ofString "hn") (.val (.word ndw))
                                      { p_hn with locals := s4.locals }
                                    rw [evaluateHOLFiniteState_return] at hdh
                                    have hev_ret_hn : @evalHOLExact 64 F _ s5.toExact
                                        (fun a => Classical.propDecidable (s5.memaddrs a))
                                        (InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural
                                          (.rStruct [.const 0#64, .var .local "hn", .const 0#64, .const 0#64])) =
                                        some (.rStruct [.val (.word 0#64), .val (.word ndw), .val (.word 0#64), .val (.word 0#64)]) := by
                                      simp [s5, setVarHOLFinite, evalHOLExact, evalListHOLExact,
                                        HolFiniteMapExact.lookup_update, FUPDATE,
                                        InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural]
                                    rw [hev_ret_hn] at hdh; dsimp only at hdh
                                    split at hdh <;> simp at hdh
                                    obtain ⟨rfl, hpdh_eq⟩ := hdh
                                    subst hpdh_eq
                                    refine ⟨0#64, ndw, 0#64, 0#64, rfl, fun _ => Or.inr ?_⟩
                                    -- Transfer `FreshBlock ent_hn p_hn ndw.toNat 32` to `FreshBlock s final_post ndw.toNat 32`!
                                    -- Notice `final_post` has the EXACT same `memory`, `globals`, `memaddrs`, `code` as `p_hn`,
                                    -- and `globN s "heap_ptr" ≤ globN s2 "heap_ptr" ≤ globN s3 "heap_ptr" = globN s4 "heap_ptr" = globN ent_hn "heap_ptr"`!
                                    obtain ⟨hnd_al, ⟨hnd_lo, hnd_hi⟩, hnd_wok⟩ := hFB_hn
                                    have hent_hp : globN ent_hn "heap_ptr" = globN s3 "heap_ptr" := by
                                      simp [ent_hn, callEntryStateHOLFinite, hs4_eq, globN]
                                    have hs_le_ent : globN s "heap_ptr" ≤ globN ent_hn "heap_ptr" := by
                                      rw [hent_hp, ← hs2_hp]; exact hsf3.2.1
                                    refine ⟨hnd_al, ⟨Nat.le_trans hs_le_ent hnd_lo, hnd_hi⟩, ?_⟩
                                    exact ⟨hnd_wok.1, hnd_wok.2.1, fun k hk => hnd_wok.2.2 k hk⟩
                                  · simp at hdh
                                | _ => simp at hdh
                        · rw [evaluateHOLFiniteState_ite, hev_r0, if_neg hr0_z] at hcr
                          simp only [↓reduceIte, evaluateHOLFiniteState_skip] at hcr
                          rw [evaluateHOLFiniteState_return] at hcr
                          have hev_ret1 : @evalHOLExact 64 F _ s4.toExact
                              (fun a => Classical.propDecidable (s4.memaddrs a))
                              (InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural
                                (.rStruct [.const 1#64, .rField 1 (.var .local "r"),
                                  .rField 2 (.var .local "r"), .rField 1 (.var .local "it")])) =
                              some (.rStruct [.val (.word 1#64), .val (.word r1w), .val (.word r2w), .val (.word i1)]) := by
                            simp [evalHOLExact, evalListHOLExact, hs4_r, hs4_it,
                              InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural]
                          rw [hev_ret1] at hcr; dsimp only at hcr
                          split at hcr <;> simp at hcr
                          obtain ⟨rfl, _⟩ := hcr
                          injection hret with hret_eq; subst hret_eq
                          exact ⟨1#64, r1w, r2w, i1, rfl, fun h => by simp at h⟩
                    · simp only [hsh_r, Bool.false_eq_true, ↓reduceIte] at hret; simp at hret
                  | _ => simp at hret
        · have hi2_ne : i2 ≠ 32#64 := hi2_32
          rw [evaluateHOLFiniteState_ite, hev_it2_32, if_pos hi2_ne] at hret
          simp only [show (1#64 : BitVec 64) ≠ 0 by decide, not_false_eq_true, ↓reduceIte] at hret
          -- `mpt_fail(10)` never returns `none` and never returns `some (.returned v)`!
          have hnn_mf : (evaluateHOLFiniteState s3 (.call (some (none, none)) (ofString "mpt_fail") [.const 10#64])).1 ≠ none := by
            rw [evaluateHOLFiniteState_call]
            split
            · simp
            · split
              · simp
              · rename_i b_mf c_mf r_mf hl_mf
                have hlook_mf : originalRuntimeCode.lookup (ofString "mpt_fail") =
                    some ([(ofString "code", .one)], sourceFnBody Guest.Software.guestFn_mpt_fail, .one) :=
                  lookup_of_guestAst_getElem 246 (by rw [guestAst_len]; decide)
                    (extractFn Guest.Software.guestFn_mpt_fail) rfl
                have hb_mf := lookupCodeHOLFinite_installed_body s3.code.lookup _ _ _ b_mf _ r_mf _ c_mf
                  (by rw [hsf3.1.1.code]; exact hlook_mf) hl_mf
                subst hb_mf
                split
                · simp
                · have hbody_mf : sourceFnBody Guest.Software.guestFn_mpt_fail =
                      .seq (.raise (ofString "MptErr") (.var .local (ofString "code"))) (.return (.const 0#64)) := rfl
                  have hmfn : (evaluateHOLFiniteState (callEntryStateHOLFinite s3 c_mf)
                      (sourceFnBody Guest.Software.guestFn_mpt_fail)).1 ≠ none := by
                    rw [hbody_mf, evaluateHOLFiniteState_seq_line780]
                    rcases evaluateHOLFiniteState _ (.raise _ _) with ⟨rm, tm⟩
                    cases rm with
                    | some _ => simp
                    | none => dsimp only; exact return_ne_none tm _
                  rcases hr_mf : evaluateHOLFiniteState (callEntryStateHOLFinite s3 c_mf)
                      (sourceFnBody Guest.Software.guestFn_mpt_fail) with ⟨rmf, _⟩
                  rw [hr_mf] at hmfn
                  cases rmf with
                  | none => exact absurd rfl hmfn
                  | some rmf' => cases rmf' <;> dsimp only <;> (repeat' split) <;> simp
          have hnr_mf := hcall_noret s3 (ofString "mpt_fail") [.const 10#64] v
          rcases hmf : evaluateHOLFiniteState s3 (.call (some (none, none)) (ofString "mpt_fail") [.const 10#64]) with ⟨rmf, _⟩
          rw [hmf] at hnn_mf hnr_mf hret
          cases rmf with
          | none => exact absurd rfl hnn_mf
          | some rmf' => dsimp only at hret; exact absurd hret hnr_mf
    · rw [if_neg hi0] at hnt hret ⊢
      simp only [↓reduceIte, evaluateHOLFiniteState_skip] at hnt hret ⊢
      rw [evaluateHOLFiniteState_return] at hret
      have hev_end : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
          (InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural
            (.rStruct [.const 1#64, .var .local "p", .var .local "n", .const 0#64])) =
          some (.rStruct [.val (.word 1#64), .val (.word wp), .val (.word wn), .val (.word 0#64)]) := by
        simp [evalHOLExact, evalListHOLExact, hs3_p, hs3_n,
          InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural]
      rw [hev_end] at hret; dsimp only at hret
      split at hret <;> simp at hret
      subst hret
      exact ⟨1#64, wp, wn, 0#64, rfl, fun h => by simp at h⟩

end ResolveAndDecodeStep

end InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_C08WrappersAndSmall
