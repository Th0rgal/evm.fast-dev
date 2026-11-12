import InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridgesR29
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase2BackingCut
import InitECandidate.Solver.Wave8GuestInv.R10Ports.ReadOnly
import InitECandidate.Solver.Wave8GuestInv.MergedLeaves
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P10
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P12_P15Callees
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M17.ro_tx_chain_id
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M17.ro_tx_has_access_list
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M17.ro_tx_is_blob
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M17.ro_tx_is_setcode
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.ro_u256_sub
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.ro_udiv_small5
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.ro_validate_transaction
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_max
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_min
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_htab_item
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_memeq
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_htab_get
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M17.ro_stor_lookup
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M17.ro_u256_eq
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M27.rv_validate_transaction
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M27.rv_min
import InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.FbCore
import InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.FbHtab
import InitECandidate.Solver.Wave8GuestInv.Shards.S03.Axioms
import InitECandidate.Solver.Wave8GuestInv.R11Adapters.FbClosure4
import InitECandidate.Solver.Wave8GuestInv.R11Adapters.ReadOnlyLeaves
import InitECandidate.Solver.Wave8GuestInv.R13Shards.WkShard01
import InitECandidate.Solver.Wave8GuestInv.R13Shards.WkShard06b
import InitECandidate.Solver.Wave8GuestInv.R13Shards.WkKeccak256
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.BlobGasPrice
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.EncodeReceipt
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.Batch1
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.WkGetAccount
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.AccountWk
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBalInitFresh
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBalStateInit.WkBalAddChanges
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBalStateInit.WkIdxStateInit
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkGetCode
import InitECandidate.Solver.Wave8GuestInv.R16Shards.ResolveDecodeStep
import InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12.DecodeStep
import InitECandidate.Solver.Wave8GuestInv.R16Shards.NfNodeNewExt
import InitECandidate.Solver.Wave8GuestInv.R16Shards.IncorporateTxIntoBlock
import InitECandidate.Solver.Wave8GuestInv.R16Shards.PrimC08Closure
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P02
import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_RemoteLeavesB1
import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_GbodyC17ToC21
import InitECandidate.Solver.Wave8GuestInv.R13Shards.HtabSetSpec

/-! # Wave 8 R31 Proved `process_transaction` Callee Bundle & Backing-Cut Closure

Fully proved Pillar 1 module (`ContractParts/PtxCalleesProvedR31`) closing:
1. All proved `process_transaction` callee bounds, read-only/domain/return specs,
   strong `encode_transaction` (`TxValidEncodeReady`), strong `recover_sender_with_chain_id`
   (`TxValidRecoverReady`), strong `lst_push` (`BoListArgStrong`), and closed
   `gb_incorporate_tx_into_block` (via witness-DB `wk_idx_start_storage_of_witnessDb`).
2. Both `PtxPhase1BackingCut` (`PtxPhase1BackingCut.ptxPhase1_backing_cut`) and
   `PtxPhase2BackingCut` (`PtxPhase2BackingCut.ptxPhase2_backing_cut`) — closing the
   `hp2` parameter that remained open in `StrongBridgesR29` — into
   `gbody_process_transaction_backing_strong_r31` without recompiling
   `PtxPhase45R11.lean` or 24,000-line `PtxPhase34R11.lean`.
-/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000
set_option linter.dupNamespace false

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.PtxCalleesProvedR31

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridges
open InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridgesR29

/-! ## 1. Closed `incorporate_tx_into_block` GuardedBody Bound under Witness-DB Bound -/

theorem wk_idx_start_storage_idxBufs_of_witnessDb
    (hdb : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      WorldOK s → globN s "ws" ≠ 0 →
        R16Shards.EvmEkFk.StorageCreateFinish.NodeDbSlicesBounded s (memW s (globN s "ws"))) :
    WorldKeeps WorldOK
      (fun s => [(globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64),
        (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
        (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "idx_start_storage") :=
  R16Shards.WkBalStateInit.wk_idx_start_storage_of_ws_storage_trie
    (R16Shards.WkBalStateInit.wkSc_ws_storage_trie_idxBufs_of_decode_witness
      decode_witness_to_mpt_spec_wkBal hdb)

theorem gbody_ws_storage_trie_closed :
    TerminatingFunBoundedOn WorldOK (ofString "ws_storage_trie") K.«ws_storage_trie» :=
  let g_dwnb := R16Shards.PrimC08Closure.«gbody__decode_witness_node_body»
    R11Adapters.«fb__decode_step»
    R11Adapters.«fb__resolve_step»
    Merged.fb_mpt_fail
    Merged.fb_node_new_ext
    PrimShardP10P30.fb_rlp_item
    R16Shards.MptC10C12.«ww__decode_step»
    R16Shards.MptC10C12.«sp__decode_step»
    R16Shards.ResolveDecodeStep.«ww__resolve_step»
    R16Shards.ResolveDecodeStep.«sp__resolve_step»
    R11Adapters.ReadOnlyLeaves.ro_mpt_fail
    R10Shards.P02.ww_node_new_ext
    R16Shards.«rt_node_new_ext»
    R10Shards.P02.ww_rlp_item
  let g_dwnm := «gbody__decode_witness_node_mpt» g_dwnb Merged.fb_scratch_release
  let g_dwn := «gbody__decode_witness_node»
    g_dwnm
    Merged.fb_scratch_mark
    Merged.fb_scratch_release
    R10Shards.P02.ro_scratch_mark
  let g_dw := «gbody_decode_witness_to_mpt»
    g_dwn
    Merged.fb_alloc
    Merged.fb_memcpy
    Merged.fb_memeq
    Merged.fb_mpt_fail
    Merged.fb_nodedb_lookup
    Wave8Contracts.M15.«ro_memeq»
    R11Adapters.ReadOnlyLeaves.ro_mpt_fail
    R11Adapters.ReadOnlyLeaves.ro_nodedb_lookup
  «gbody_ws_storage_trie»
    g_dw
    Merged.fb_htab_get
    Merged.fb_htab_set
    Wave8Contracts.M15.«ro_htab_get»

theorem gbody_get_pre_tx_storage_closed :
    TerminatingFunBoundedOn WorldOK (ofString "get_pre_tx_storage") K.«get_pre_tx_storage» :=
  let g_wgs := «gbody_ws_get_storage»
    Merged.fb_alloc
    PrimShardP10P30.fb_heap_mark
    PrimShardP10P30.fb_heap_release
    PrimShardP10P30.fb_keccak256
    Merged.fb_memeq
    PrimShardP10P30.fb_rlp_decode_fully
    Merged.fb_trie_lookup
    P12_P15.Callees.fb_u256_from_be
    R11Adapters.«fb_ws_storage_root_of»
    gbody_ws_storage_trie_closed
    Wave8Contracts.M15.«ro_memeq»
    R13Shards.WkShard01.«wk_ws_storage_root_of»
  «gbody_get_pre_tx_storage»
    Merged.fb_record_pre_state_read
    Merged.fb_stor_lookup
    g_wgs
    R16Shards.«wk_record_pre_state_read»
    M17.«ro_stor_lookup»

theorem gbody_idx_start_storage_closed :
    TerminatingFunBoundedOn WorldOK (ofString "idx_start_storage") K.«idx_start_storage» :=
  R16Shards.PrimC08Closure.«gbody_idx_start_storage»
    Merged.fb_alloc
    gbody_get_pre_tx_storage_closed
    Merged.fb_htab_get
    Merged.fb_htab_set
    Merged.fb_memcpy
    Merged.fb_st_le64
    Wave8Contracts.M15.«ro_htab_get»
    Merged.wk_memcpy
    Merged.wk_st_le64

theorem gbody_incorporate_tx_into_block_of_witnessDb
    (hdb : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      WorldOK s → globN s "ws" ≠ 0 →
        R16Shards.EvmEkFk.StorageCreateFinish.NodeDbSlicesBounded s (memW s (globN s "ws"))) :
    TerminatingFunBoundedOn WorldOK (ofString "incorporate_tx_into_block")
      K.«incorporate_tx_into_block» :=
  let g_ub := R16Shards.PrimC08Closure.«gbody_update_builder_from_tx»
    Merged.fb_add_balance_change
    Merged.fb_add_code_change
    Merged.fb_add_nonce_change
    Merged.fb_add_storage_write
    (Wave8Leaves.S03.fb_bal_remove_change
      (Wave8Leaves.S03.fb_bal_list_remove_idx Merged.fb_memcpy) Merged.fb_htab_get)
    R11Adapters.«fb_get_code»
    Merged.fb_htab_item
    R11Adapters.«fb_idx_start_account»
    gbody_idx_start_storage_closed
    Merged.fb_memeq
    (Wave8Leaves.S03.fb_remove_storage_write
      (Wave8Leaves.S03.fb_bal_list_remove_idx Merged.fb_memcpy)
      Merged.fb_htab_del Merged.fb_htab_get)
    R11Adapters.«fb_u256_eq»
    R16Shards.WkBal.«wk_add_balance_change»
    R16Shards.WkBal.«wk_add_code_change»
    R16Shards.WkBal.«wk_add_nonce_change»
    R16Shards.WkBal.«wk_add_storage_write»
    R16Shards.PrimC08Closure.«wk_bal_remove_change»
    R16Shards.«wk_get_code»
    Wave8Contracts.M15.«ro_htab_item»
    R16Shards.WkBalStateInit.«wk_idx_start_account»
    (wk_idx_start_storage_idxBufs_of_witnessDb hdb)
    Wave8Contracts.M15.«ro_memeq»
    R16Shards.PrimC08Closure.«wk_remove_storage_write»
    M17.«ro_u256_eq»
  R16Shards.«gbody_incorporate_tx_into_block»
    (Wave8Leaves.S03.fb_merge_tx_into_block
      Merged.fb_htab_get Merged.fb_htab_item Merged.fb_htab_new
      Merged.fb_htab_set Merged.fb_htab_union_into)
    g_ub

/-! ## 2. Fully Proved `PtxCalleesProvedR31` Structure and Concrete Witness -/

/-- Complete fully proved bundle of `process_transaction` callees, carrying the
strong `TxValidEncodeReady`, `TxValidRecoverReady`, and `BoListArgStrong` contracts
in place of legacy weak signatures. -/
structure PtxCalleesProvedR31 : Prop where
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
  fb_increment_nonce : TerminatingFunBoundedOn GuestInv (ofString "increment_nonce") K.«increment_nonce»
  fb_keccak256 : TerminatingFunBoundedOn GuestInv (ofString "keccak256") K.«keccak256»
  fb_lst_new : TerminatingFunBoundedOn GuestInv (ofString "lst_new") K.«lst_new»
  fb_lst_push : TerminatingFunBoundedOn GuestInv (ofString "lst_push") K.«lst_push»
  fb_max : TerminatingFunBoundedOn GuestInv (ofString "max") K.«max»
  fb_memcpy : TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy»
  fb_min : TerminatingFunBoundedOn GuestInv (ofString "min") K.«min»
  fb_msg_new : TerminatingFunBoundedOn GuestInv (ofString "msg_new") K.«msg_new»
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
  wk_alloc : type_of% @R13Shards.WkShard01.wk_alloc
  rt_alloc : type_of% @R13Shards.WkShard01.rt_alloc
  wk_calculate_blob_gas_price : type_of% @R16Shards.WkBlockTxEnc.wk_calculate_blob_gas_price
  ro_calculate_total_blob_gas : ReadOnlyFn (ofString "calculate_total_blob_gas")
  wk_check_transaction : type_of% @R16Shards.TopGbodyWk.wk_check_transaction
  wk_clear_account_preserving_balance : type_of% @R16Shards.EvmEkFk.wk_clear_account_preserving_balance
  wk_compute_contract_address : type_of% @R16Shards.WkBlockTxEnc.wk_compute_contract_address
  wk_create_ether : type_of% @R16Shards.EvmEkFk.wk_create_ether
  wk_encode_receipt : type_of% @R16Shards.WkBlockTxEnc.wk_encode_receipt
  wk_encode_transaction_strong : type_of% @R16Shards.WkBlockTxEnc.wk_encode_transaction_strong
  wk_encode_transaction_bounded : type_of% @R16Shards.TopGbodyWk.wk_encode_transaction_bounded
  ro_fee_mul : ReadOnlyFn (ofString "fee_mul")
  wk_get_account : type_of% @R16Shards.EvmEkFk.wk_get_account
  ro_htab_item : ReadOnlyFn (ofString "htab_item")
  htab_new_spec : type_of% @htab_new_spec
  htab_set_spec : type_of% @htab_set_spec
  wk_increment_nonce : type_of% @R16Shards.EvmEkFk.wk_increment_nonce
  wk_keccak256 : type_of% @R16Shards.PrimC08Closure.wk_keccak256
  wk_lst_new : type_of% @R13Wk06b.wk_lst_new
  rt_lst_new : type_of% @Merged.rt_lst_new
  wk_lst_push_strong : type_of% @ContractParts.StrongBridges.wk_lst_push_strong
  ro_max : ReadOnlyFn (ofString "max")
  wk_memcpy : type_of% @Merged.wk_memcpy
  dm_memcpy : type_of% @EvmFrameSpecs.dm_memcpy
  ro_min : ReadOnlyFn (ofString "min")
  rv_min : RetLe (fun s => locN s "a") (ofString "min")
  wk_msg_new : type_of% @R13Wk06b.wk_msg_new
  rt_msg_new : type_of% @Merged.rt_msg_new
  wk_recover_sender_with_chain_id_strong : type_of% @R16Shards.HeaderHashRecover.wk_recover_sender_with_chain_id_strong
  wk_recover_sender_with_chain_id_bo : type_of% @R16Shards.TopGbodyWk.wk_recover_sender_with_chain_id_bo
  wk_set_account_balance : type_of% @R16Shards.EvmEkFk.wk_set_account_balance
  wk_state_fresh_tx : type_of% @R16Shards.WkBal.wk_state_fresh_tx
  wk_te_new : type_of% @R13Wk06b.wk_te_new
  rt_te_new : type_of% @Merged.rt_te_new
  ro_tx_chain_id : ReadOnlyFn (ofString "tx_chain_id")
  ro_tx_has_access_list : ReadOnlyFn (ofString "tx_has_access_list")
  ro_tx_is_blob : ReadOnlyFn (ofString "tx_is_blob")
  ro_tx_is_setcode : ReadOnlyFn (ofString "tx_is_setcode")
  ro_u256_sub : ReadOnlyFn (ofString "u256_sub")
  ro_udiv_small5 : ReadOnlyFn (ofString "udiv_small5")
  ro_validate_transaction : ReadOnlyFn (ofString "validate_transaction")
  rv_validate_transaction : RetIntrinsic (ofString "validate_transaction")

/-- Unconditional fully proved witness for `PtxCalleesProvedR31`. -/
theorem ptxCalleesProvedR31 : PtxCalleesProvedR31 where
  fb_alloc := Merged.fb_alloc
  fb_calculate_blob_gas_price := R11Adapters.fb_calculate_blob_gas_price
  fb_calculate_total_blob_gas := Merged.fb_calculate_total_blob_gas
  fb_check_transaction := R11Adapters.fb_check_transaction
  fb_clear_account_preserving_balance := R11Adapters.fb_clear_account_preserving_balance
  fb_compute_contract_address := R11Adapters.fb_compute_contract_address
  fb_create_ether := R11Adapters.fb_create_ether
  fb_encode_receipt := R11Adapters.fb_encode_receipt
  fb_encode_transaction := R11Adapters.fb_encode_transaction
  fb_fee_mul := R11Adapters.fb_fee_mul
  fb_frame_mem_release := Wave8Leaves.S03.fb_frame_mem_release
  fb_get_account := R11Adapters.fb_get_account
  fb_htab_item := Merged.fb_htab_item
  fb_htab_new := Merged.fb_htab_new
  fb_htab_set := Merged.fb_htab_set
  fb_increment_nonce := R11Adapters.fb_increment_nonce
  fb_keccak256 := PrimShardP10P30.fb_keccak256
  fb_lst_new := Merged.fb_lst_new
  fb_lst_push := Merged.fb_lst_push
  fb_max := R10Shards.P10.fb_max
  fb_memcpy := Merged.fb_memcpy
  fb_min := R11Adapters.fb_min
  fb_msg_new := Wave8Leaves.S03.fb_msg_new Merged.fb_alloc Merged.fb_memzero
  fb_recover_sender_with_chain_id := Merged.fb_recover_sender_with_chain_id
  fb_scratch_release := Merged.fb_scratch_release
  fb_set_account_balance := R11Adapters.fb_set_account_balance
  fb_state_fresh_tx := Merged.fb_state_fresh_tx
  fb_te_new := Merged.fb_te_new
  fb_tx_chain_id := R11Adapters.fb_tx_chain_id
  fb_tx_has_access_list := Merged.fb_tx_has_access_list
  fb_tx_is_blob := Merged.fb_tx_is_blob
  fb_tx_is_setcode := Merged.fb_tx_is_setcode
  fb_u256_sub := R11Adapters.fb_u256_sub
  fb_udiv_small5 := R11Adapters.fb_udiv_small5
  fb_validate_transaction := R11Adapters.fb_validate_transaction
  wk_alloc := R13Shards.WkShard01.wk_alloc
  rt_alloc := R13Shards.WkShard01.rt_alloc
  wk_calculate_blob_gas_price := R16Shards.WkBlockTxEnc.wk_calculate_blob_gas_price
  ro_calculate_total_blob_gas := R10Ports.ro_calculate_total_blob_gas
  wk_check_transaction := R16Shards.TopGbodyWk.wk_check_transaction
  wk_clear_account_preserving_balance := R16Shards.EvmEkFk.wk_clear_account_preserving_balance
  wk_compute_contract_address := R16Shards.WkBlockTxEnc.wk_compute_contract_address
  wk_create_ether := R16Shards.EvmEkFk.wk_create_ether
  wk_encode_receipt := R16Shards.WkBlockTxEnc.wk_encode_receipt
  wk_encode_transaction_strong := R16Shards.WkBlockTxEnc.wk_encode_transaction_strong
  wk_encode_transaction_bounded := R16Shards.TopGbodyWk.wk_encode_transaction_bounded
  ro_fee_mul := R10Ports.ro_fee_mul
  wk_get_account := R16Shards.EvmEkFk.wk_get_account
  ro_htab_item := Wave8Contracts.M15.ro_htab_item
  htab_new_spec := R10Shards.Fast_RemoteLeavesB1.htab_new_spec
  htab_set_spec := R13SoloHtabSet.htab_set_spec_proof
  wk_increment_nonce := R16Shards.EvmEkFk.wk_increment_nonce
  wk_keccak256 := R16Shards.PrimC08Closure.wk_keccak256
  wk_lst_new := R13Wk06b.wk_lst_new
  rt_lst_new := Merged.rt_lst_new
  wk_lst_push_strong := ContractParts.StrongBridges.wk_lst_push_strong
  ro_max := Wave8Contracts.M15.ro_max
  wk_memcpy := Merged.wk_memcpy
  dm_memcpy := EvmFrameSpecs.dm_memcpy
  ro_min := Wave8Contracts.M15.ro_min
  rv_min := Merged.rv_min
  wk_msg_new := R13Wk06b.wk_msg_new
  rt_msg_new := Merged.rt_msg_new
  wk_recover_sender_with_chain_id_strong := R16Shards.HeaderHashRecover.wk_recover_sender_with_chain_id_strong
  wk_recover_sender_with_chain_id_bo := R16Shards.TopGbodyWk.wk_recover_sender_with_chain_id_bo
  wk_set_account_balance := R16Shards.EvmEkFk.wk_set_account_balance
  wk_state_fresh_tx := R16Shards.WkBal.wk_state_fresh_tx
  wk_te_new := R13Wk06b.wk_te_new
  rt_te_new := Merged.rt_te_new
  ro_tx_chain_id := M17.ro_tx_chain_id
  ro_tx_has_access_list := M17.ro_tx_has_access_list
  ro_tx_is_blob := M17.ro_tx_is_blob
  ro_tx_is_setcode := M17.ro_tx_is_setcode
  ro_u256_sub := Wave8Contracts.M18.ro_u256_sub
  ro_udiv_small5 := Wave8Contracts.M18.ro_udiv_small5
  ro_validate_transaction := Wave8Contracts.M18.ro_validate_transaction
  rv_validate_transaction := Merged.rv_validate_transaction

/-! ## 3. Bridge Adapters into `PtxCalleesCutover`, `PtxCallees`, and Backing Cuts -/

/-- The 2 legacy weak signature fields carried unused inside `R16Shards.PtxCalleesCutover`
(superseded dynamically in Phase 1 by `wk_encode_transaction_bounded` and
`wk_recover_sender_with_chain_id_bo`). -/
structure LegacyUnusedPtxCutoverFields : Prop where
  wk_encode_transaction : WorldKeeps (fun s => WorldOK s ∧ TxValid s) (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
     ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "encode_transaction")
  wk_recover_sender_with_chain_id : WorldKeeps (fun s => WorldOK s ∧ TxValid s)
    (fun s => [(locN s "out20", 20),
      (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
      (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
      (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
     ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "recover_sender_with_chain_id")

/-- The 4 legacy weak signature fields carried unused inside `R13Shards.PtxCallees`
for Phases 1 & 2 (never dynamically invoked in Phase 1 or Phase 2). -/
structure LegacyUnusedPtxPhase12Fields : Prop extends LegacyUnusedPtxCutoverFields where
  wk_lst_push : WorldKeeps BoListArg (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
     ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    RetListSlot (ofString "lst_push")
  wk_process_message_call : WorldKeepsIn MsgReady
    (fun s => [memW s (locN s "msg" + 152), memW s (locN s "msg" + 160)])
    (fun s => [(locN s "msg", 176),
      (globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128),
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
    ["bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]),
     ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    RetMessageOutput (ofString "process_message_call")

theorem ptxCalleesCutover_of_r31
    (hdb : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      WorldOK s → globN s "ws" ≠ 0 →
        R16Shards.EvmEkFk.StorageCreateFinish.NodeDbSlicesBounded s (memW s (globN s "ws")))
    (gb_pmc : TerminatingFunBoundedOn MsgReady (ofString "process_message_call")
      K.«process_message_call»)
    (hleg : LegacyUnusedPtxCutoverFields) :
    R16Shards.PtxCalleesCutover where
  fb_alloc := ptxCalleesProvedR31.fb_alloc
  fb_calculate_blob_gas_price := ptxCalleesProvedR31.fb_calculate_blob_gas_price
  fb_calculate_total_blob_gas := ptxCalleesProvedR31.fb_calculate_total_blob_gas
  fb_check_transaction := ptxCalleesProvedR31.fb_check_transaction
  fb_clear_account_preserving_balance := ptxCalleesProvedR31.fb_clear_account_preserving_balance
  fb_compute_contract_address := ptxCalleesProvedR31.fb_compute_contract_address
  fb_create_ether := ptxCalleesProvedR31.fb_create_ether
  fb_encode_receipt := ptxCalleesProvedR31.fb_encode_receipt
  fb_encode_transaction := ptxCalleesProvedR31.fb_encode_transaction
  fb_fee_mul := ptxCalleesProvedR31.fb_fee_mul
  fb_frame_mem_release := ptxCalleesProvedR31.fb_frame_mem_release
  fb_get_account := ptxCalleesProvedR31.fb_get_account
  fb_htab_item := ptxCalleesProvedR31.fb_htab_item
  fb_htab_new := ptxCalleesProvedR31.fb_htab_new
  fb_htab_set := ptxCalleesProvedR31.fb_htab_set
  gb_incorporate_tx_into_block := gbody_incorporate_tx_into_block_of_witnessDb hdb
  fb_increment_nonce := ptxCalleesProvedR31.fb_increment_nonce
  fb_keccak256 := ptxCalleesProvedR31.fb_keccak256
  fb_lst_new := ptxCalleesProvedR31.fb_lst_new
  fb_lst_push := ptxCalleesProvedR31.fb_lst_push
  fb_max := ptxCalleesProvedR31.fb_max
  fb_memcpy := ptxCalleesProvedR31.fb_memcpy
  fb_min := ptxCalleesProvedR31.fb_min
  fb_msg_new := ptxCalleesProvedR31.fb_msg_new
  gb_process_message_call := gb_pmc
  fb_recover_sender_with_chain_id := ptxCalleesProvedR31.fb_recover_sender_with_chain_id
  fb_scratch_release := ptxCalleesProvedR31.fb_scratch_release
  fb_set_account_balance := ptxCalleesProvedR31.fb_set_account_balance
  fb_state_fresh_tx := ptxCalleesProvedR31.fb_state_fresh_tx
  fb_te_new := ptxCalleesProvedR31.fb_te_new
  fb_tx_chain_id := ptxCalleesProvedR31.fb_tx_chain_id
  fb_tx_has_access_list := ptxCalleesProvedR31.fb_tx_has_access_list
  fb_tx_is_blob := ptxCalleesProvedR31.fb_tx_is_blob
  fb_tx_is_setcode := ptxCalleesProvedR31.fb_tx_is_setcode
  fb_u256_sub := ptxCalleesProvedR31.fb_u256_sub
  fb_udiv_small5 := ptxCalleesProvedR31.fb_udiv_small5
  fb_validate_transaction := ptxCalleesProvedR31.fb_validate_transaction
  wk_alloc := ptxCalleesProvedR31.wk_alloc
  rt_alloc := ptxCalleesProvedR31.rt_alloc
  wk_calculate_blob_gas_price := ptxCalleesProvedR31.wk_calculate_blob_gas_price
  ro_calculate_total_blob_gas := ptxCalleesProvedR31.ro_calculate_total_blob_gas
  wk_check_transaction := ptxCalleesProvedR31.wk_check_transaction
  wk_clear_account_preserving_balance := ptxCalleesProvedR31.wk_clear_account_preserving_balance
  wk_compute_contract_address := ptxCalleesProvedR31.wk_compute_contract_address
  wk_encode_receipt := ptxCalleesProvedR31.wk_encode_receipt
  wk_encode_transaction := hleg.wk_encode_transaction
  ro_fee_mul := ptxCalleesProvedR31.ro_fee_mul
  wk_get_account := ptxCalleesProvedR31.wk_get_account
  ro_htab_item := ptxCalleesProvedR31.ro_htab_item
  htab_new_spec := ptxCalleesProvedR31.htab_new_spec
  htab_set_spec := ptxCalleesProvedR31.htab_set_spec
  wk_increment_nonce := ptxCalleesProvedR31.wk_increment_nonce
  wk_keccak256 := ptxCalleesProvedR31.wk_keccak256
  wk_lst_new := ptxCalleesProvedR31.wk_lst_new
  rt_lst_new := ptxCalleesProvedR31.rt_lst_new
  ro_max := ptxCalleesProvedR31.ro_max
  wk_memcpy := ptxCalleesProvedR31.wk_memcpy
  dm_memcpy := ptxCalleesProvedR31.dm_memcpy
  ro_min := ptxCalleesProvedR31.ro_min
  rv_min := ptxCalleesProvedR31.rv_min
  wk_msg_new := ptxCalleesProvedR31.wk_msg_new
  rt_msg_new := ptxCalleesProvedR31.rt_msg_new
  wk_recover_sender_with_chain_id := hleg.wk_recover_sender_with_chain_id
  wk_set_account_balance := ptxCalleesProvedR31.wk_set_account_balance
  wk_state_fresh_tx := ptxCalleesProvedR31.wk_state_fresh_tx
  wk_te_new := ptxCalleesProvedR31.wk_te_new
  rt_te_new := ptxCalleesProvedR31.rt_te_new
  ro_tx_chain_id := ptxCalleesProvedR31.ro_tx_chain_id
  ro_tx_has_access_list := ptxCalleesProvedR31.ro_tx_has_access_list
  ro_tx_is_blob := ptxCalleesProvedR31.ro_tx_is_blob
  ro_tx_is_setcode := ptxCalleesProvedR31.ro_tx_is_setcode
  ro_u256_sub := ptxCalleesProvedR31.ro_u256_sub
  ro_udiv_small5 := ptxCalleesProvedR31.ro_udiv_small5
  ro_validate_transaction := ptxCalleesProvedR31.ro_validate_transaction
  rv_validate_transaction := ptxCalleesProvedR31.rv_validate_transaction

theorem ptxCallees_of_r31
    (hdb : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      WorldOK s → globN s "ws" ≠ 0 →
        R16Shards.EvmEkFk.StorageCreateFinish.NodeDbSlicesBounded s (memW s (globN s "ws")))
    (gb_pmc : TerminatingFunBoundedOn MsgReady (ofString "process_message_call")
      K.«process_message_call»)
    (hleg : LegacyUnusedPtxPhase12Fields) :
    R13Shards.PtxCallees where
  fb_alloc := ptxCalleesProvedR31.fb_alloc
  fb_calculate_blob_gas_price := ptxCalleesProvedR31.fb_calculate_blob_gas_price
  fb_calculate_total_blob_gas := ptxCalleesProvedR31.fb_calculate_total_blob_gas
  fb_check_transaction := ptxCalleesProvedR31.fb_check_transaction
  fb_clear_account_preserving_balance := ptxCalleesProvedR31.fb_clear_account_preserving_balance
  fb_compute_contract_address := ptxCalleesProvedR31.fb_compute_contract_address
  fb_create_ether := ptxCalleesProvedR31.fb_create_ether
  fb_encode_receipt := ptxCalleesProvedR31.fb_encode_receipt
  fb_encode_transaction := ptxCalleesProvedR31.fb_encode_transaction
  fb_fee_mul := ptxCalleesProvedR31.fb_fee_mul
  fb_frame_mem_release := ptxCalleesProvedR31.fb_frame_mem_release
  fb_get_account := ptxCalleesProvedR31.fb_get_account
  fb_htab_item := ptxCalleesProvedR31.fb_htab_item
  fb_htab_new := ptxCalleesProvedR31.fb_htab_new
  fb_htab_set := ptxCalleesProvedR31.fb_htab_set
  gb_incorporate_tx_into_block := gbody_incorporate_tx_into_block_of_witnessDb hdb
  fb_increment_nonce := ptxCalleesProvedR31.fb_increment_nonce
  fb_keccak256 := ptxCalleesProvedR31.fb_keccak256
  fb_lst_new := ptxCalleesProvedR31.fb_lst_new
  fb_lst_push := ptxCalleesProvedR31.fb_lst_push
  fb_max := ptxCalleesProvedR31.fb_max
  fb_memcpy := ptxCalleesProvedR31.fb_memcpy
  fb_min := ptxCalleesProvedR31.fb_min
  fb_msg_new := ptxCalleesProvedR31.fb_msg_new
  gb_process_message_call := gb_pmc
  fb_recover_sender_with_chain_id := ptxCalleesProvedR31.fb_recover_sender_with_chain_id
  fb_scratch_release := ptxCalleesProvedR31.fb_scratch_release
  fb_set_account_balance := ptxCalleesProvedR31.fb_set_account_balance
  fb_state_fresh_tx := ptxCalleesProvedR31.fb_state_fresh_tx
  fb_te_new := ptxCalleesProvedR31.fb_te_new
  fb_tx_chain_id := ptxCalleesProvedR31.fb_tx_chain_id
  fb_tx_has_access_list := ptxCalleesProvedR31.fb_tx_has_access_list
  fb_tx_is_blob := ptxCalleesProvedR31.fb_tx_is_blob
  fb_tx_is_setcode := ptxCalleesProvedR31.fb_tx_is_setcode
  fb_u256_sub := ptxCalleesProvedR31.fb_u256_sub
  fb_udiv_small5 := ptxCalleesProvedR31.fb_udiv_small5
  fb_validate_transaction := ptxCalleesProvedR31.fb_validate_transaction
  wk_alloc := ptxCalleesProvedR31.wk_alloc
  rt_alloc := ptxCalleesProvedR31.rt_alloc
  wk_calculate_blob_gas_price := ptxCalleesProvedR31.wk_calculate_blob_gas_price
  ro_calculate_total_blob_gas := ptxCalleesProvedR31.ro_calculate_total_blob_gas
  wk_check_transaction := ptxCalleesProvedR31.wk_check_transaction
  wk_clear_account_preserving_balance := ptxCalleesProvedR31.wk_clear_account_preserving_balance
  wk_compute_contract_address := ptxCalleesProvedR31.wk_compute_contract_address
  wk_create_ether := ptxCalleesProvedR31.wk_create_ether
  wk_encode_receipt := ptxCalleesProvedR31.wk_encode_receipt
  wk_encode_transaction := hleg.wk_encode_transaction
  ro_fee_mul := ptxCalleesProvedR31.ro_fee_mul
  wk_get_account := ptxCalleesProvedR31.wk_get_account
  ro_htab_item := ptxCalleesProvedR31.ro_htab_item
  htab_new_spec := ptxCalleesProvedR31.htab_new_spec
  htab_set_spec := ptxCalleesProvedR31.htab_set_spec
  wk_increment_nonce := ptxCalleesProvedR31.wk_increment_nonce
  wk_keccak256 := ptxCalleesProvedR31.wk_keccak256
  wk_lst_new := ptxCalleesProvedR31.wk_lst_new
  rt_lst_new := ptxCalleesProvedR31.rt_lst_new
  wk_lst_push := hleg.wk_lst_push
  ro_max := ptxCalleesProvedR31.ro_max
  wk_memcpy := ptxCalleesProvedR31.wk_memcpy
  dm_memcpy := ptxCalleesProvedR31.dm_memcpy
  ro_min := ptxCalleesProvedR31.ro_min
  rv_min := ptxCalleesProvedR31.rv_min
  wk_msg_new := ptxCalleesProvedR31.wk_msg_new
  rt_msg_new := ptxCalleesProvedR31.rt_msg_new
  wk_process_message_call := hleg.wk_process_message_call
  wk_recover_sender_with_chain_id := hleg.wk_recover_sender_with_chain_id
  wk_set_account_balance := ptxCalleesProvedR31.wk_set_account_balance
  wk_state_fresh_tx := ptxCalleesProvedR31.wk_state_fresh_tx
  wk_te_new := ptxCalleesProvedR31.wk_te_new
  rt_te_new := ptxCalleesProvedR31.rt_te_new
  ro_tx_chain_id := ptxCalleesProvedR31.ro_tx_chain_id
  ro_tx_has_access_list := ptxCalleesProvedR31.ro_tx_has_access_list
  ro_tx_is_blob := ptxCalleesProvedR31.ro_tx_is_blob
  ro_tx_is_setcode := ptxCalleesProvedR31.ro_tx_is_setcode
  ro_u256_sub := ptxCalleesProvedR31.ro_u256_sub
  ro_udiv_small5 := ptxCalleesProvedR31.ro_udiv_small5
  ro_validate_transaction := ptxCalleesProvedR31.ro_validate_transaction
  rv_validate_transaction := ptxCalleesProvedR31.rv_validate_transaction

/-- Both `PtxPhase1BackingCut` AND `PtxPhase2BackingCut` closed in R31! -/
theorem ptxPhase12BackingCuts_closed_r31
    (h1 : R13Shards.PtxCallees)
    (hent : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      R16Shards.TxReadyBackingStrong s → R16Shards.TopGbodyWk.TxReadyFullStrong s) :
    R13Shards.PtxPhase12BackingCuts where
  phase1 := R13Shards.ptxPhase1_backing_cut h1 hent
  phase2 := R13Shards.ptxPhase2_backing_cut h1

/-- Full `gbody_process_transaction` on `TxReadyBackingStrong` with BOTH Phase 1 and Phase 2
backing cuts discharged (eliminating `hp2 : PtxPhase2BackingCut` from R29). -/
theorem gbody_process_transaction_backing_strong_r31
    (hdb : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      WorldOK s → globN s "ws" ≠ 0 →
        R16Shards.EvmEkFk.StorageCreateFinish.NodeDbSlicesBounded s (memW s (globN s "ws")))
    (gb_pmc : TerminatingFunBoundedOn MsgReady (ofString "process_message_call")
      K.«process_message_call»)
    (hleg : LegacyUnusedPtxPhase12Fields)
    (hent : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      R16Shards.TxReadyBackingStrong s → R16Shards.TopGbodyWk.TxReadyFullStrong s)
    (hwk : R16Shards.PtxP34.PmcStrong)
    (hkeep : R16Shards.PmcBackingStrong) :
    TerminatingFunBoundedOn
      R16Shards.TxReadyBackingStrong (ofString "process_transaction")
      K.«process_transaction» :=
  let h1 := ptxCallees_of_r31 hdb gb_pmc hleg
  gbody_process_transaction_backing_strong_pmc_cutover_of_cuts
    (ptxCalleesCutover_of_r31 hdb gb_pmc hleg.toLegacyUnusedPtxCutoverFields)
    hwk hkeep
    (R13Shards.ptxPhase1_backing_cut h1 hent)
    (R13Shards.ptxPhase2_backing_cut h1)

/-- Full `gbody_process_transaction` directly on `TxReadyFullStrong` with zero `hent`
assumption (`ptxPhase1_backing_cut_full` + `ptxPhase2_backing_cut` + Phases 3–5). -/
theorem gbody_process_transaction_full_strong_r31
    (hdb : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      WorldOK s → globN s "ws" ≠ 0 →
        R16Shards.EvmEkFk.StorageCreateFinish.NodeDbSlicesBounded s (memW s (globN s "ws")))
    (gb_pmc : TerminatingFunBoundedOn MsgReady (ofString "process_message_call")
      K.«process_message_call»)
    (hleg : LegacyUnusedPtxPhase12Fields)
    (hwk : R16Shards.PtxP34.PmcStrong)
    (hkeep : R16Shards.PmcBackingStrong) :
    TerminatingFunBoundedOn
      R16Shards.TopGbodyWk.TxReadyFullStrong (ofString "process_transaction")
      K.«process_transaction» := by
  let h1 := ptxCallees_of_r31 hdb gb_pmc hleg
  let hc := ptxCalleesCutover_of_r31 hdb gb_pmc hleg.toLegacyUnusedPtxCutoverFields
  have hb : TerminatingProgBoundedOn R16Shards.TopGbodyWk.TxReadyFullStrong
      (R13Shards.ptxPhase1 (R13Shards.ptxPhase2
        (R13Shards.ptxPhase3 (R13Shards.ptxPhase4 R13Shards.ptxPhase5))))
      (R13Shards.ptxCost1 + (R13Shards.ptxCost2 +
        (R13Shards.ptxCost3 + (R13Shards.ptxCost4 + R13Shards.ptxCost5)))) :=
    R13Shards.ptxPhase1_backing_cut_full h1
      (R13Shards.ptxPhase2_backing_cut h1 _ _
        (R16Shards.ptxPhase345_cut_pmc_backing_strong_cutover hc hwk hkeep))
  refine ⟨_, _, _, R13Shards.ptx_lookup, ?_⟩
  rw [← R13Shards.ptx_phases_eq, R13Shards.ptx_cost_eq] at hb
  intro F s hc_clk hp
  simpa only [R13Shards.ptxCode,
    InitECandidate.Solver.GuestCodeLookup.sourceFunctionEntry,
    Guest.Software.guestFn_process_transaction,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural] using
    (hb (F := F) s hc_clk hp)

end InitECandidate.Solver.Wave8GuestInv.ContractParts.PtxCalleesProvedR31
