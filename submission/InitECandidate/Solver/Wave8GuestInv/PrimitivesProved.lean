import InitECandidate.Solver.Wave8GuestInv.LeafStatements
import InitECandidate.Solver.Wave8GuestInv.ContractParts.C08
import InitECandidate.Solver.Wave8GuestInv.R10Ports.ReadOnly
import InitECandidate.Solver.Wave8GuestInv.Primitives
import InitECandidate.Solver.Wave8GuestInv.MergedLeaves
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P02
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P10
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P11
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P12_P15
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P13
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P14
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28_InitProofs
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28_ForkEvm
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M17.ro_tx_chain_id
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M17.ro_tx_has_access_list
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M17.ro_tx_is_blob
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M17.ro_tx_is_setcode
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.ro_u256_mul
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.ro_u256_sub
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.ro_udiv_small5
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.ro_validate_block_access_list_gas_limit
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.ro_validate_transaction
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.ro_u256_is_zero
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_max
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_min
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_memeq
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_htab_get
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_htab_has
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_htab_item
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M17.ro_stor_lookup
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M17.ro_u256_eq
import InitECandidate.Solver.Wave8GuestInv.HtabC00Ports.TruncateSpec
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxRouter
import InitECandidate.Solver.Wave8GuestInv.R10Shards.EvmFrameSpecs
import InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.FbCore
import InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.FbSetStorage
import InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.FbHtab
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P12_P15Callees
import InitECandidate.Solver.Wave8GuestInv.Shards.S03.Axioms
import InitECandidate.Solver.Wave8GuestInv.R11Adapters.FbClosure4
import InitECandidate.Solver.Wave8GuestInv.R11Adapters.ReadOnlyLeaves
import InitECandidate.Solver.Wave8GuestInv.R11Adapters.Sha256
import InitECandidate.Solver.Wave8GuestInv.R11Adapters.BalRlp
import InitECandidate.Solver.Wave8GuestInv.R11Adapters.FbStaticCall
import InitECandidate.Solver.Wave8GuestInv.R11Shards.WkShard08
import InitECandidate.Solver.Wave8GuestInv.R11Shards.WkShard09a
import InitECandidate.Solver.Wave8GuestInv.R13Shards.WkShard01
import InitECandidate.Solver.Wave8GuestInv.R13Shards.WkShard06b
import InitECandidate.Solver.Wave8GuestInv.R13Shards.GbodyPayloadStateInitShard
import InitECandidate.Solver.Wave8GuestInv.R14Shards.P3C10C12.P3_NodeRlp
import InitECandidate.Solver.Wave8GuestInv.R14Shards.P3C10C12.P3_NodeHash
import InitECandidate.Solver.Wave8GuestInv.R14Shards.P3C10C12.P3_MptRoot
import InitECandidate.Solver.Wave8GuestInv.R14Shards.P3C10C12.P3_MptSet
import InitECandidate.Solver.Wave8GuestInv.R16Shards.NfCollapseBranch
import InitECandidate.Solver.Wave8GuestInv.R16Shards.NfDeleteExtFinish
import InitECandidate.Solver.Wave8GuestInv.R16Shards.NfNodeNewExt
import InitECandidate.Solver.Wave8GuestInv.R16Shards.NfNodeNewLeaf
import InitECandidate.Solver.Wave8GuestInv.R16Shards.NfInsertIntoLeaf
import InitECandidate.Solver.Wave8GuestInv.R16Shards.NfSplitExtension
import InitECandidate.Solver.Wave8GuestInv.R16Shards.MptNibbleKeyWW
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkMarkAccountCreated
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkGetCode
import InitECandidate.Solver.Wave8GuestInv.R16Shards.ProcessWithdrawals
import InitECandidate.Solver.Wave8GuestInv.R16Shards.ResolveDecodeStep
import InitECandidate.Solver.Wave8GuestInv.R16Shards.StateRestoreEpilogue
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBalInitFresh
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.Batch1
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkEncodeAccount
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.EkWarmStorageKey
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.WkGetAccount
import InitECandidate.Solver.Wave8GuestInv.R16Shards.HeaderHashRecover.ValidVersionedHashes
import InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12.DecodeStep
import InitECandidate.Solver.Wave8GuestInv.R16Shards.PrimC08Closure
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.BlobGasPrice
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.LogsBloom
import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_GbodyC17ToC21

/-! Primitive instance. merge_shard.py replaces placeholders with checked leaf applications.
Ported from campaign/specs-proposed/GuestInv.lean (working tree based on 664524baaf0aff6938ff399c2017a85b8ccc0c59).
Generated by campaign/notes/guestinv/r10_inputs/split_spec.py. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open R10Shards.P26_P28 in
open R10Shards.P02 in
open GuardedBody.R10 in
open M17 in

theorem primitives : Primitives where
  «fb__decode_step» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb__decode_step»
  «fb__resolve_step» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb__resolve_step»
  «fb_mpt_fail» := Merged.fb_mpt_fail
  «fb_node_new_ext» := Merged.fb_node_new_ext
  «fb_rlp_item» := PrimShardP10P30.fb_rlp_item
  «ww__decode_step» := R16Shards.MptC10C12.«ww__decode_step»
  «sp__decode_step» := R16Shards.MptC10C12.«sp__decode_step»
  «ww__resolve_step» := R16Shards.ResolveDecodeStep.«ww__resolve_step»
  «sp__resolve_step» := R16Shards.ResolveDecodeStep.«sp__resolve_step»
  «ro_mpt_fail» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.ReadOnlyLeaves.«ro_mpt_fail»
  «ww_node_new_ext» := R10Shards.P02.ww_node_new_ext
  «rt_node_new_ext» := R16Shards.«rt_node_new_ext»
  «ww_rlp_item» := R10Shards.P02.ww_rlp_item
  «gbody__decode_witness_node_body» := R16Shards.PrimC08Closure.«gbody__decode_witness_node_body»
  «fb_scratch_release» := Merged.fb_scratch_release
  «fb_scratch_mark» := Merged.fb_scratch_mark
  «ro_scratch_mark» := R10Shards.P02.ro_scratch_mark
  «fb__collapse_branch» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb__collapse_branch»
  «fb__delete_ext_finish» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb__delete_ext_finish»
  «fb_common_prefix_length» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_common_prefix_length»
  «fb_memeq» := Merged.fb_memeq
  «fb_node_invalidate» := Merged.fb_node_invalidate
  «fb_scratch_alloc» := Merged.fb_scratch_alloc
  «nf__collapse_branch» := R16Shards.«nf__collapse_branch»
  «nf__delete_ext_finish» := R16Shards.«nf__delete_ext_finish»
  «ro_common_prefix_length» := R10Ports.ro_common_prefix_length
  «rv_common_prefix_length» := Merged.rv_common_prefix_length
  «ro_memeq» := Wave8Contracts.M15.«ro_memeq»
  «nf_node_invalidate» := Merged.nf_node_invalidate
  «iz_node_invalidate» := EvmFrameSpecs.iz_node_invalidate
  «ww_scratch_alloc» := R10Shards.P02.ww_scratch_alloc
  «rt_scratch_alloc» := Merged.rt_scratch_alloc
  «gbody__mpt_delete_node_body» := R16Shards.PrimC08Closure.«gbody__mpt_delete_node_body»
  «fb__insert_into_leaf» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb__insert_into_leaf»
  «fb__split_extension» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb__split_extension»
  «fb_node_new_leaf» := R10Shards.P02.fb_node_new_leaf
  «nf__insert_into_leaf» := R16Shards.«nf__insert_into_leaf»
  «nf__split_extension» := R16Shards.«nf__split_extension»
  «nf_node_new_ext» := R16Shards.«nf_node_new_ext»
  «nf_node_new_leaf» := R16Shards.«nf_node_new_leaf»
  «gbody__mpt_insert_node» := R16Shards.PrimC08Closure.«gbody__mpt_insert_node»
  «fb__node_needs_rlp» := Merged.fb__node_needs_rlp
  «fb__node_rlp_begin» := Merged.fb__node_rlp_begin
  «fb__node_rlp_finish» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb__node_rlp_finish»
  «ro__node_needs_rlp» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.ReadOnlyLeaves.«ro__node_needs_rlp»
  «ak__node_rlp_begin» := R16Shards.PrimC08Closure.«ak__node_rlp_begin»
  «ak__node_rlp_finish» := R16Shards.PrimC08Closure.«ak__node_rlp_finish»
  «gbody__node_rlp_fill» := «gbody__node_rlp_fill»
  «gbody_node_rlp» := P3C10C12.«gbody_node_rlp»
  «fb_alloc» := Merged.fb_alloc
  «fb_keccak256» := PrimShardP10P30.fb_keccak256
  «gbody_node_hash» := P3C10C12.«gbody_node_hash»
  «fb_memcpy» := Merged.fb_memcpy
  «gbody_mpt_root» := P3C10C12.«gbody_mpt_root»
  «fb_mpt_nibble_key» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_mpt_nibble_key»
  «ww_mpt_nibble_key» := R16Shards.ww_mpt_nibble_key
  «nk_mpt_nibble_key» := R16Shards.PrimC08Closure.«nk_mpt_nibble_key»
  «gbody_mpt_set» := P3C10C12.«gbody_mpt_set»
  «fb_heap_mark» := PrimShardP10P30.fb_heap_mark
  «fb_heap_release» := PrimShardP10P30.fb_heap_release
  «fb_mpt_new» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_mpt_new»
  «fb_rlp_encode_word» := Merged.fb_rlp_encode_word
  «ro_heap_mark» := R10Ports.ro_heap_mark
  «wk_mpt_new» := R13Shards.WkShard01.«wk_mpt_new»
  «rt_mpt_new» := R13Shards.WkShard01.«rt_mpt_new»
  «mk_mpt_set» := «mk_mpt_set»
  «wk_rlp_encode_word» := Merged.wk_rlp_encode_word
  «gbody_build_mpt_indexed» := «gbody_build_mpt_indexed»
  «fb_nodedb_lookup» := Merged.fb_nodedb_lookup
  «ro_nodedb_lookup» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.ReadOnlyLeaves.«ro_nodedb_lookup»
  «fb_cache_get_root» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_cache_get_root»
  «fb_encode_account» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_encode_account»
  «fb_htab_copy» := Merged.fb_htab_copy
  «fb_htab_get» := Merged.fb_htab_get
  «fb_htab_has» := Merged.fb_htab_has
  «fb_htab_item» := Merged.fb_htab_item
  «fb_htab_new» := Merged.fb_htab_new
  «fb_htab_set» := Merged.fb_htab_set
  «fb_rlp_encode_bytes» := Merged.fb_rlp_encode_bytes
  «fb_u256_is_zero» := P12_P15.Callees.fb_u256_is_zero
  «fb_u256_to_be_min» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_to_be_min»
  «fb_ws_get_account_optional» := PrimShardP10P30.fb_ws_get_account_optional
  «fb_ws_storage_root_of» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_ws_storage_root_of»
  «wk_alloc» := R13Shards.WkShard01.«wk_alloc»
  «rt_alloc» := R13Shards.WkShard01.«rt_alloc»
  «wk_cache_get_root» := R13Shards.WkShard01.«wk_cache_get_root»
  «wk_encode_account» := R16Shards.«wk_encode_account»
  «wk_htab_copy» := R13Shards.WkShard01.«wk_htab_copy»
  «rt_htab_copy» := R13Shards.WkShard01.«rt_htab_copy»
  «ro_htab_get» := Wave8Contracts.M15.«ro_htab_get»
  «ro_htab_has» := Wave8Contracts.M15.«ro_htab_has»
  «ro_htab_item» := Wave8Contracts.M15.«ro_htab_item»
  «htab_new_spec» := R16Shards.PrimC08Closure.htab_new_spec
  «htab_set_spec» := R16Shards.PrimC08Closure.htab_set_spec
  «wk_memcpy» := Merged.wk_memcpy
  «wk_mpt_from_witness» := «wk_mpt_from_witness»
  «mk_mpt_root» := «mk_mpt_root»
  «wk_rlp_encode_bytes» := Merged.wk_rlp_encode_bytes
  «rv_rlp_encode_bytes» := Merged.rv_rlp_encode_bytes
  «ro_u256_is_zero» := Wave8Contracts.M18.«ro_u256_is_zero»
  «wk_u256_to_be_min» := Merged.wk_u256_to_be_min
  «rv_u256_to_be_min» := Merged.rv_u256_to_be_min
  «wk_ws_get_account_optional» := R13Shards.WkShard01.«wk_ws_get_account_optional»
  «wk_ws_storage_root_of» := R13Shards.WkShard01.«wk_ws_storage_root_of»
  «gbody_compute_state_root» := «gbody_compute_state_root»
  «fb_rlp_decode_fully» := PrimShardP10P30.fb_rlp_decode_fully
  «fb_trie_lookup» := Merged.fb_trie_lookup
  «fb_u256_from_be» := P12_P15.Callees.fb_u256_from_be
  «fb_record_pre_state_read» := Merged.fb_record_pre_state_read
  «fb_stor_lookup» := Wave8Leaves.S03.fb_stor_lookup Merged.fb_htab_get
  «wk_record_pre_state_read» := R16Shards.«wk_record_pre_state_read»
  «ro_stor_lookup» := M17.«ro_stor_lookup»
  «fb_st_le64» := Merged.fb_st_le64
  «wk_st_le64» := Merged.wk_st_le64
  «gbody_idx_start_storage» := R16Shards.PrimC08Closure.«gbody_idx_start_storage»
  «fb_add_balance_change» := Merged.fb_add_balance_change
  «fb_add_code_change» := Merged.fb_add_code_change
  «fb_add_nonce_change» := Merged.fb_add_nonce_change
  «fb_add_storage_write» := Merged.fb_add_storage_write
  «fb_bal_remove_change» := Wave8Leaves.S03.fb_bal_remove_change (Wave8Leaves.S03.fb_bal_list_remove_idx Merged.fb_memcpy) Merged.fb_htab_get
  «fb_get_code» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_get_code»
  «fb_idx_start_account» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_idx_start_account»
  «fb_remove_storage_write» := Wave8Leaves.S03.fb_remove_storage_write (Wave8Leaves.S03.fb_bal_list_remove_idx Merged.fb_memcpy) Merged.fb_htab_del Merged.fb_htab_get
  «fb_u256_eq» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_eq»
  «wk_add_balance_change» := «wk_add_balance_change»
  «wk_add_code_change» := «wk_add_code_change»
  «wk_add_nonce_change» := «wk_add_nonce_change»
  «wk_add_storage_write» := «wk_add_storage_write»
  «wk_bal_remove_change» := R16Shards.PrimC08Closure.«wk_bal_remove_change»
  «wk_get_code» := R16Shards.«wk_get_code»
  «wk_idx_start_account» := «wk_idx_start_account»
  «wk_idx_start_storage» := «wk_idx_start_storage»
  «wk_remove_storage_write» := R16Shards.PrimC08Closure.«wk_remove_storage_write»
  «ro_u256_eq» := M17.«ro_u256_eq»
  «gbody_update_builder_from_tx» := R16Shards.PrimC08Closure.«gbody_update_builder_from_tx»
  «fb_merge_tx_into_block» := Wave8Leaves.S03.fb_merge_tx_into_block Merged.fb_htab_get Merged.fb_htab_item Merged.fb_htab_new Merged.fb_htab_set Merged.fb_htab_union_into
  «fb_htab_del» := Merged.fb_htab_del
  «htab_del_spec» := Merged.htab_del_spec
  «htab_del_progress_spec» := Merged.htab_del_progress_spec
  «gbody_htab_truncate» := R16Shards.PrimC08Closure.«gbody_htab_truncate»
  «htab_truncate_spec» := HtabC00Ports.htab_truncate_spec
  «gbody_rollback_child_access» := R16Shards.PrimC08Closure.«gbody_rollback_child_access»
  «fb_address_to_u256» := P12_P15.Callees.fb_address_to_u256
  «fb_create_finish» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_create_finish»
  «fb_credit_state_gas_refund» := Merged.fb_credit_state_gas_refund
  «fb_frame_halt» := Wave8Leaves.S03.fb_frame_halt
  «fb_frame_mem_release» := Wave8Leaves.S03.fb_frame_mem_release
  «fb_incorporate_child_on_error» := Merged.fb_incorporate_child_on_error
  «fb_incorporate_child_on_success» := Merged.fb_incorporate_child_on_success
  «fb_min» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_min»
  «fb_pc_add» := Merged.fb_pc_add
  «fb_refill_frame_state_gas» := Merged.fb_refill_frame_state_gas
  «fb_set_retdata» := Merged.fb_set_retdata
  «fb_stack_push» := Merged.fb_stack_push
  «fb_state_restore» := Merged.fb_state_restore
  «ek_create_finish» := «ek_create_finish»
  «ek_frame_halt» := EvmFrameSpecs.ek_frame_halt
  «ek_refill_frame_state_gas» := EvmFrameSpecs.ek_refill_frame_state_gas
  «ek_state_restore» := R16Shards.StateRestoreEpilogue.ek_state_restore
  «gbody_finish_child» := R16Shards.PrimC08Closure.«gbody_finish_child»
  «fb_sk_make» := PrimShardP10P30.fb_sk_make
  «nz_htab_set» := EvmFrameSpecs.nz_htab_set
  «wk_sk_make» := EvmFrameSpecs.wk_sk_make
  «gbody_get_storage» := R16Shards.PrimC08Closure.«gbody_get_storage»
  «fb_charge_gas» := P12_P15.Callees.fb_charge_gas
  «fb_is_warm_storage_key» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_is_warm_storage_key»
  «fb_stack_pop» := Merged.fb_stack_pop
  «fb_u256_to_be32» := R10Shards.P10.fb_u256_to_be32
  «fb_warm_storage_key» := PrimShardP10P30.fb_warm_storage_key
  «ek_charge_gas» := EvmFrameSpecs.ek_charge_gas
  «ek_is_warm_storage_key» := EvmFrameSpecs.ek_is_warm_storage_key
  «ek_stack_pop» := EvmFrameSpecs.ek_stack_pop
  «ek_u256_to_be32» := EvmFrameSpecs.ek_u256_to_be32
  «ek_warm_storage_key» := R16Shards.EvmEkFk.«ek_warm_storage_key»
  «gbody_op_sload» := R16Shards.PrimC08Closure.«gbody_op_sload»
  «fb_charge_state_gas» := Wave8Leaves.S03.fb_charge_state_gas P12_P15.Callees.fb_add_sat
  «fb_check_gas» := Merged.fb_check_gas
  «fb_max» := R10Shards.P10.fb_max
  «fb_require_not_static» := Merged.fb_require_not_static
  «fb_set_storage» := PrimShardP10P30.fb_set_storage
  «ro_check_gas» := R10Ports.ro_check_gas
  «ek_get_storage_original» := «ek_get_storage_original»
  «ro_max» := Wave8Contracts.M15.«ro_max»
  «ro_require_not_static» := R10Shards.P10.ro_require_not_static
  «gbody_op_sstore» := R16Shards.PrimC08Closure.«gbody_op_sstore»
  «fb_op_add» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_op_add»
  «fb_op_addmod» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.Closure4.«fb_op_addmod»
  «fb_op_address» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_op_address»
  «fb_op_and» := Merged.fb_op_and
  «fb_op_balance» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_op_balance»
  «fb_op_basefee» := Merged.fb_op_basefee
  «fb_op_blobbasefee» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_op_blobbasefee»
  «fb_op_blobhash» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_op_blobhash»
  «fb_op_blockhash» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_op_blockhash»
  «fb_op_byte» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_op_byte»
  «fb_op_call» := R11Adapters.StaticCall.«fb_op_call»
  «fb_op_callcode» := R11Adapters.StaticCall.«fb_op_callcode»
  «fb_op_calldatacopy» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_op_calldatacopy»
  «fb_op_calldataload» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_op_calldataload»
  «fb_op_calldatasize» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_op_calldatasize»
  «fb_op_caller» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_op_caller»
  «fb_op_callvalue» := P12_P15.fb_op_callvalue
  «fb_op_chainid» := P12_P15.fb_op_chainid
  «fb_op_clz» := P12_P15.fb_op_clz
  «fb_op_codecopy» := P12_P15.fb_op_codecopy
  «fb_op_codesize» := P12_P15.fb_op_codesize
  «fb_op_coinbase» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_op_coinbase»
  «fb_op_create» := Merged.fb_op_create
  «fb_op_create2» := Merged.fb_op_create2
  «fb_op_delegatecall» := Merged.fb_op_delegatecall
  «fb_op_div» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_op_div»
  «fb_op_dup» := Merged.fb_op_dup
  «fb_op_dupn» := Merged.fb_op_dupn
  «fb_op_eq» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_op_eq»
  «fb_op_exchange» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_op_exchange»
  «fb_op_exp» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_op_exp»
  «fb_op_extcodecopy» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_op_extcodecopy»
  «fb_op_extcodehash» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_op_extcodehash»
  «fb_op_extcodesize» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_op_extcodesize»
  «fb_op_gas» := Merged.fb_op_gas
  «fb_op_gaslimit» := Merged.fb_op_gaslimit
  «fb_op_gasprice» := Merged.fb_op_gasprice
  «fb_op_gt» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_op_gt»
  «fb_op_iszero» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_op_iszero»
  «fb_op_jump» := Merged.fb_op_jump
  «fb_op_jumpdest» := P12_P15.fb_op_jumpdest
  «fb_op_jumpi» := P12_P15.fb_op_jumpi
  «fb_op_keccak» := P13.fb_op_keccak
  «fb_op_log» := P13.fb_op_log
  «fb_op_lt» := P13.fb_op_lt
  «fb_op_mcopy» := P13.fb_op_mcopy
  «fb_op_mload» := P13.fb_op_mload
  «fb_op_mod» := P13.fb_op_mod
  «fb_op_msize» := P13.fb_op_msize
  «fb_op_mstore» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_op_mstore»
  «fb_op_mstore8» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_op_mstore8»
  «fb_op_mul» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_op_mul»
  «fb_op_mulmod» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.Closure4.«fb_op_mulmod»
  «fb_op_not» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_op_not»
  «fb_op_number» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_op_number»
  «fb_op_or» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_op_or»
  «fb_op_origin» := P12_P15.fb_op_origin
  «fb_op_pc» := P12_P15.fb_op_pc
  «fb_op_pop» := P12_P15.fb_op_pop
  «fb_op_prevrandao» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_op_prevrandao»
  «fb_op_push» := P12_P15.fb_op_push
  «fb_op_return» := P12_P15.fb_op_return
  «fb_op_returndatacopy» := P12_P15.fb_op_returndatacopy
  «fb_op_returndatasize» := Merged.fb_op_returndatasize
  «fb_op_revert» := P12_P15.fb_op_revert
  «fb_op_sar» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_op_sar»
  «fb_op_sdiv» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_op_sdiv»
  «fb_op_selfbalance» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_op_selfbalance»
  «fb_op_selfdestruct» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_op_selfdestruct»
  «fb_op_sgt» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_op_sgt»
  «fb_op_shl» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_op_shl»
  «fb_op_shr» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_op_shr»
  «fb_op_signextend» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_op_signextend»
  «fb_op_slotnum» := Merged.fb_op_slotnum
  «fb_op_slt» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_op_slt»
  «fb_op_smod» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_op_smod»
  «fb_op_staticcall» := R11Adapters.StaticCall.«fb_op_staticcall»
  «fb_op_stop» := Merged.fb_op_stop
  «fb_op_sub» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_op_sub»
  «fb_op_swap» := Merged.fb_op_swap
  «fb_op_swapn» := Merged.fb_op_swapn
  «fb_op_timestamp» := Merged.fb_op_timestamp
  «fb_op_tload» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_op_tload»
  «fb_op_tstore» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_op_tstore»
  «fb_op_xor» := Merged.fb_op_xor
  «gbody_op_dispatch» := Merged.gbody_op_dispatch
  «fb_frame_epilogue» := Merged.fb_frame_epilogue
  «fb_frame_exception» := Merged.fb_frame_exception
  «finish_child_spec» := «finish_child_spec»
  «frame_epilogue_spec» := R16Shards.StateRestoreEpilogue.frame_epilogue_spec
  «frame_exception_spec» := R16Shards.PrimC08Closure.frame_exception_spec
  «op_dispatch_spec» := «op_dispatch_spec»
  «gbody_run_frames» := Merged.gbody_run_frames
  «fb_depth0_prepare» := Merged.fb_depth0_prepare
  «fb_frame_open» := Merged.fb_frame_open
  «fb_frame_start» := Merged.fb_frame_start
  «fb_state_snapshot» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_state_snapshot»
  «ek_depth0_prepare» := «ek_depth0_prepare»
  «fk_frame_open» := «fk_frame_open»
  «ek_frame_start» := «ek_frame_start»
  «ro_state_snapshot» := EvmFrameSpecs.«ro_state_snapshot»
  «gbody_process_message» := R16Shards.PrimC08Closure.«gbody_process_message»
  «fb_destroy_storage» := PrimShardP10P30.fb_destroy_storage
  «fb_increment_nonce» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_increment_nonce»
  «fb_mark_account_created» := Merged.fb_mark_account_created
  «wk_destroy_storage» := «wk_destroy_storage»
  «wk_increment_nonce» := «wk_increment_nonce»
  «wk_mark_account_created» := R16WkMarkAccountCreated.«wk_mark_account_created»
  «gbody_process_create_message» := R16Shards.PrimC08Closure.«gbody_process_create_message»
  «fb_account_deployable» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_account_deployable»
  «fb_frame_state_gas_used» := Wave8Leaves.S03.fb_frame_state_gas_used
  «fb_memzero» := Merged.fb_memzero
  «wk_account_deployable» := R16Shards.EvmEkFk.«wk_account_deployable»
  «wk_memzero» := Merged.wk_memzero
  «zv_memzero» := Merged.zv_memzero
  «gbody_process_message_call» := R10Shards.Fast_GbodyC17ToC21.«gbody_process_message_call»
  «fb_ext_code_of» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_ext_code_of»
  «fb_msg_new» := Wave8Leaves.S03.fb_msg_new Merged.fb_alloc Merged.fb_memzero
  «fb_state_fresh_tx» := Merged.fb_state_fresh_tx
  «fb_te_new» := Merged.fb_te_new
  «wk_ext_code_of» := R16Shards.EvmEkFk.«wk_ext_code_of»
  «wk_msg_new» := R13Wk06b.«wk_msg_new»
  «rt_msg_new» := Merged.rt_msg_new
  «wk_process_message_call» := «wk_process_message_call»
  «wk_state_fresh_tx» := R16Shards.WkBal.wk_state_fresh_tx
  «wk_te_new» := R13Wk06b.«wk_te_new»
  «rt_te_new» := Merged.rt_te_new
  «gbody_process_unchecked_system_transaction» := «gbody_process_unchecked_system_transaction»
  «fb_extract_deposit_data» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_extract_deposit_data»
  «fb_requests_append» := Merged.fb_requests_append
  «wk_extract_deposit_data» := Merged.wk_extract_deposit_data
  «wk_process_checked_system_transaction» := «wk_process_checked_system_transaction»
  «wk_requests_append» := R16Shards.PrimC08Closure.«wk_requests_append»
  «gbody_process_general_purpose_requests» := R10Shards.Fast_GbodyC17ToC21.«gbody_process_general_purpose_requests»
  «fb_calculate_blob_gas_price» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_calculate_blob_gas_price»
  «fb_calculate_total_blob_gas» := Merged.fb_calculate_total_blob_gas
  «fb_check_transaction» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_check_transaction»
  «fb_clear_account_preserving_balance» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_clear_account_preserving_balance»
  «fb_compute_contract_address» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_compute_contract_address»
  «fb_create_ether» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_create_ether»
  «fb_encode_receipt» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_encode_receipt»
  «fb_encode_transaction» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_encode_transaction»
  «fb_fee_mul» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_fee_mul»
  «fb_get_account» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_get_account»
  «fb_lst_new» := Merged.fb_lst_new
  «fb_lst_push» := Merged.fb_lst_push
  «fb_recover_sender_with_chain_id» := Merged.fb_recover_sender_with_chain_id
  «fb_set_account_balance» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_set_account_balance»
  «fb_tx_chain_id» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_tx_chain_id»
  «fb_tx_has_access_list» := Merged.fb_tx_has_access_list
  «fb_tx_is_blob» := Merged.fb_tx_is_blob
  «fb_tx_is_setcode» := Merged.fb_tx_is_setcode
  «fb_u256_sub» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_sub»
  «fb_udiv_small5» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_udiv_small5»
  «fb_validate_transaction» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_validate_transaction»
  «wk_calculate_blob_gas_price» := R16Shards.WkBlockTxEnc.«wk_calculate_blob_gas_price»
  «ro_calculate_total_blob_gas» := R10Ports.ro_calculate_total_blob_gas
  «wk_check_transaction» := «wk_check_transaction»
  «wk_clear_account_preserving_balance» := «wk_clear_account_preserving_balance»
  «wk_compute_contract_address» := R16Shards.WkBlockTxEnc.«wk_compute_contract_address»
  «wk_create_ether» := «wk_create_ether»
  «wk_encode_receipt» := «wk_encode_receipt»
  «wk_encode_transaction» := «wk_encode_transaction»
  «ro_fee_mul» := R10Ports.ro_fee_mul
  «wk_get_account» := R16Shards.EvmEkFk.«wk_get_account»
  «wk_keccak256» := R16Shards.PrimC08Closure.«wk_keccak256»
  «wk_lst_new» := R13Wk06b.«wk_lst_new»
  «rt_lst_new» := Merged.rt_lst_new
  «wk_lst_push» := «wk_lst_push»
  «dm_memcpy» := EvmFrameSpecs.dm_memcpy
  «ro_min» := Wave8Contracts.M15.«ro_min»
  «rv_min» := Merged.rv_min
  «wk_recover_sender_with_chain_id» := «wk_recover_sender_with_chain_id»
  «wk_set_account_balance» := «wk_set_account_balance»
  «ro_tx_chain_id» := M17.«ro_tx_chain_id»
  «ro_tx_has_access_list» := M17.«ro_tx_has_access_list»
  «ro_tx_is_blob» := M17.«ro_tx_is_blob»
  «ro_tx_is_setcode» := M17.«ro_tx_is_setcode»
  «ro_u256_sub» := Wave8Contracts.M18.«ro_u256_sub»
  «ro_udiv_small5» := Wave8Contracts.M18.«ro_udiv_small5»
  «ro_validate_transaction» := Wave8Contracts.M18.«ro_validate_transaction»
  «rv_validate_transaction» := Merged.rv_validate_transaction
  «gbody_process_transaction» := «gbody_process_transaction»
  «fb_u256_mul» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_mul»
  «ro_u256_mul» := Wave8Contracts.M18.«ro_u256_mul»
  «gbody_process_withdrawals» := R16Shards.«gbody_process_withdrawals»
  «fb_bal_init» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_bal_init»
  «fb_build_block_access_list_rlp» := R11Adapters.BalRlp.fb_build_block_access_list_rlp
  «fb_compute_requests_hash» := R11Adapters.Sha.fb_compute_requests_hash
  «fb_decode_transaction» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_decode_transaction»
  «fb_logs_bloom» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_logs_bloom»
  «fb_track_ancestor_access» := Merged.fb_track_ancestor_access
  «fb_validate_block_access_list_gas_limit» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_validate_block_access_list_gas_limit»
  «wk_bal_init» := R16Shards.WkBal.wk_bal_init
  «wk_build_block_access_list_rlp» := «wk_build_block_access_list_rlp»
  «wk_build_mpt_indexed» := «wk_build_mpt_indexed»
  «wk_compute_state_root» := «wk_compute_state_root»
  «wk_decode_transaction» := «wk_decode_transaction»
  «wk_logs_bloom» := R16Shards.WkBlockTxEnc.«wk_logs_bloom»
  «ww_memzero» := Merged.ww_memzero
  «wk_process_general_purpose_requests» := «wk_process_general_purpose_requests»
  «wk_process_transaction» := «wk_process_transaction»
  «wk_process_unchecked_system_transaction» := «wk_process_unchecked_system_transaction»
  «wk_process_withdrawals» := «wk_process_withdrawals»
  «wk_track_ancestor_access» := R11Shards.WkShard08.«wk_track_ancestor_access»
  «ro_validate_block_access_list_gas_limit» := Wave8Contracts.M18.«ro_validate_block_access_list_gas_limit»
  «gbody_execute_block» := «gbody_execute_block»
  «fb_block_rlp_length» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_block_rlp_length»
  «fb_encode_execution_requests» := Merged.fb_encode_execution_requests
  «fb_encode_withdrawal_rlp» := Merged.fb_encode_withdrawal_rlp
  «wk_block_rlp_length» := R11Shards.WkShard09a.«wk_block_rlp_length»
  «wk_encode_withdrawal_rlp» := R16Shards.WkBlockTxEnc.«wk_encode_withdrawal_rlp»
  «dm_encode_withdrawal_rlp» := EvmFrameSpecs.dm_encode_withdrawal_rlp
  «gbody_payload_header» := «gbody_payload_header»
  «gbody_state_init» := R13Shards.gbody_state_init
  «fb_check_gas_limit» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_check_gas_limit»
  «fb_header_hash» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_header_hash»
  «fb_is_valid_versioned_hashes» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_is_valid_versioned_hashes»
  «fb_nodedb_build» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_nodedb_build»
  «fb_validate_header» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_validate_header»
  «fb_validate_headers» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_validate_headers»
  «ro_check_gas_limit» := R10Ports.ro_check_gas_limit
  «wk_header_hash» := «wk_header_hash»
  «wk_is_valid_versioned_hashes» := R16Shards.HeaderHashRecover.«wk_is_valid_versioned_hashes»
  «wk_nodedb_build» := «wk_nodedb_build»
  «wk_payload_header» := «wk_payload_header»
  «wk_state_init» := «wk_state_init»
  «wk_validate_header» := «wk_validate_header»
  «wk_validate_headers» := «wk_validate_headers»
  «gbody_run_attempt» := «gbody_run_attempt»
  «fb_blake2_init» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_blake2_init»
  «fb_bls_precompiles_init» := R10Shards.P26_P28.fb_bls_precompiles_init
  «fb_bn254_init» := R10Shards.P26_P28.fb_bn254_init
  «fb_decode_host_input» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_decode_host_input»
  «fb_evm_init» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_evm_init»
  «fb_fork_init» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_fork_init»
  «fb_header_init» := Merged.fb_header_init
  «fb_htr_new_payload_request» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_htr_new_payload_request»
  «fb_keccak_init» := R10Shards.P26_P28.fb_keccak_init
  «fb_mem_init» := Merged.fb_mem_init
  «fb_mpt_init» := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_mpt_init»
  «fb_output_write» := Merged.fb_output_write
  «fb_ripemd160_init» := R10Shards.P26_P28.fb_ripemd160_init
  «fb_secp256k1_init» := R10Shards.P26_P28.fb_secp256k1_init
  «fb_serialize_result» := Merged.fb_serialize_result
  «fb_sha256_init» := R10Shards.P26_P28.fb_sha256_init
  «fb_ssz_init» := Merged.fb_ssz_init
  «fb_u256_ws_init» := R10Shards.P26_P28.fb_u256_ws_init
  «wk_blake2_init» := R10Shards.P26_P28.wk_blake2_init
  «wk_bls_precompiles_init» := R10Shards.P26_P28.wk_bls_precompiles_init
  «wk_bn254_init» := R10Shards.P26_P28.wk_bn254_init
  «wk_decode_host_input» := «wk_decode_host_input»
  «wk_evm_init» := R10Shards.P26_P28.wk_evm_init
  «wk_fork_init» := R10Shards.P26_P28.wk_fork_init
  «wk_header_init» := R10Shards.P26_P28.wk_header_init
  «wk_htr_new_payload_request» := «wk_htr_new_payload_request»
  «wk_keccak_init» := R10Shards.P26_P28.wk_keccak_init
  «mem_init_world» := R16Shards.PrimC08Closure.mem_init_world
  «wk_mpt_init» := R10Shards.P26_P28.wk_mpt_init
  «wk_ripemd160_init» := R10Shards.P26_P28.wk_ripemd160_init
  «ro_secp256k1_init» := R10Shards.P26_P28.ro_secp256k1_init
  «wk_sha256_init» := R10Shards.P26_P28.wk_sha256_init
  «wk_ssz_init» := R10Shards.P26_P28.wk_ssz_init
  «wk_u256_ws_init» := R10Shards.P26_P28.wk_u256_ws_init
  «gbody_main» := R10Shards.Fast_GbodyC17ToC21.«gbody_main»

end InitECandidate.Solver.Wave8GuestInv
