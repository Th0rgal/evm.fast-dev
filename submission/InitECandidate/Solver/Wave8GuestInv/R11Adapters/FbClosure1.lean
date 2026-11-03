import InitECandidate.Solver.Wave8GuestInv.Deliveries.GBODY_RUNFRAMES_SOL.Axioms
import InitECandidate.Solver.Wave8GuestInv.Deliveries.HTAB_LEAVES.Axioms
import InitECandidate.Solver.Wave8GuestInv.Deliveries.HTAB_LEAVES.Simple
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M05.IndividualAudit
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M08.IndividualAudit
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M11.IndividualAudit
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M12.IndividualAudit
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M13.IndividualAudit
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M14.Axioms
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.Axioms
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M17.Axioms
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.Axioms
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M21.IndividualAudit
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M23.IndividualAudit
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M25.IndividualAudit
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M26.IndividualAudit
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M27.IndividualAudit
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M28.IndividualAudit
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M29.IndividualAudit
import InitECandidate.Solver.Wave8GuestInv.Deliveries.RLP.Axioms
import InitECandidate.Solver.Wave8GuestInv.Deliveries.RLP.RlpCore
import InitECandidate.Solver.Wave8GuestInv.Deliveries.RLP.RlpEnc
import InitECandidate.Solver.Wave8GuestInv.Deliveries.RLP.RlpLeaves1
import InitECandidate.Solver.Wave8GuestInv.Deliveries.RLP.RlpWalk
import InitECandidate.Solver.Wave8GuestInv.HtabC00Ports.DelSpecs
import InitECandidate.Solver.Wave8GuestInv.HtabC00Ports.TruncateSpec
import InitECandidate.Solver.Wave8GuestInv.MergedLeaves
import InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.FbCore
import InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.FbHtab
import InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.FbSetStorage
import InitECandidate.Solver.Wave8GuestInv.R10Ports.ReadOnly
import InitECandidate.Solver.Wave8GuestInv.R10Shards.EvmFrameSpecs
import InitECandidate.Solver.Wave8GuestInv.R10Shards.EvmGBody
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P02
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P10
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P12_P15
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P12_P15Callees
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P13
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P13DivMod
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28
import InitECandidate.Solver.Wave8GuestInv.R11Adapters.FbAuto2
import InitECandidate.Solver.Wave8GuestInv.Shards.S00.Compatibility
import InitECandidate.Solver.Wave8GuestInv.Shards.S01.Axioms
import InitECandidate.Solver.Wave8GuestInv.Shards.S01.Leaves
import InitECandidate.Solver.Wave8GuestInv.Shards.S02.Axioms
import InitECandidate.Solver.Wave8GuestInv.Shards.S03.Axioms
import InitECandidate.Solver.Wave8GuestInv.Shards.S04.Axioms
import InitECandidate.Solver.Wave8GuestInv.Shards.S04.is_valid_delegation
import InitECandidate.Solver.Wave8GuestInv.Shards.S04.refill_frame_state_gas
import InitECandidate.Solver.Wave8GuestInv.Shards.S05.Axioms
import InitECandidate.Solver.Wave8GuestInv.Shards.S06.Axioms
import InitECandidate.Solver.Wave8GuestInv.Shards.S06.Base
import InitECandidate.Solver.Wave8GuestInv.Shards.S06.LoopFree
import InitECandidate.Solver.Wave8GuestInv.Shards.S08.Axioms
import InitECandidate.Solver.Wave8GuestInv.Shards.S08.code_imm
import InitECandidate.Solver.Wave8GuestInv.Shards.S08.require_not_static
import InitECandidate.Solver.Wave8GuestInv.Shards.S08.stack_swap_positions
import InitECandidate.Solver.Wave8GuestInv.Shards.S09.Axioms
import InitECandidate.Solver.Wave8GuestInv.Shards.S10.Axioms
import InitECandidate.Solver.Wave8GuestInv.Shards.S10.CheckGas
import InitECandidate.Solver.Wave8GuestInv.Shards.S11.Axioms
import InitECandidate.Solver.Wave8GuestInv.Shards.S12.Axioms
import InitECandidate.Solver.Wave8GuestInv.Shards.S12.S12LoopsMore
import InitECandidate.Solver.Wave8GuestInv.Shards.S12.S12Simple
import InitECandidate.Solver.Wave8GuestInv.Shards.S13.Axioms
import InitECandidate.Solver.Wave8GuestInv.Shards.S13.ceil_log2
import InitECandidate.Solver.Wave8GuestInv.Shards.S14.Axioms
import InitECandidate.Solver.Wave8GuestInv.Shards.S15.Axioms

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unusedSectionVars false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R11Adapters

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.P12_P15.Common

theorem «fb__collapse_branch» :
    TerminatingFunBoundedOn GuestInv (ofString "_collapse_branch") K.«_collapse_branch» := by
  exact InitECandidate.Solver.Wave8Leaves.S00Verified.fb__collapse_branch InitECandidate.Solver.Wave8GuestInv.Merged.fb_alloc InitECandidate.Solver.Wave8GuestInv.Merged.fb_mpt_fail InitECandidate.Solver.Wave8GuestInv.Merged.fb_nibbles_concat InitECandidate.Solver.Wave8GuestInv.Merged.fb_node_new_ext InitECandidate.Solver.Wave8GuestInv.R10Shards.P02.«fb_node_new_leaf»
theorem «fb__delete_ext_finish» :
    TerminatingFunBoundedOn GuestInv (ofString "_delete_ext_finish") K.«_delete_ext_finish» := by
  exact InitECandidate.Solver.Wave8Leaves.S00Verified.fb__delete_ext_finish InitECandidate.Solver.Wave8GuestInv.Merged.fb_mpt_fail InitECandidate.Solver.Wave8GuestInv.Merged.fb_nibbles_concat InitECandidate.Solver.Wave8GuestInv.Merged.fb_node_new_ext InitECandidate.Solver.Wave8GuestInv.R10Shards.P02.«fb_node_new_leaf»
theorem «fb__resolve_step» :
    TerminatingFunBoundedOn GuestInv (ofString "_resolve_step") K.«_resolve_step» := by
  exact InitECandidate.Solver.Wave8Leaves.S00Verified.fb__resolve_step InitECandidate.Solver.Wave8GuestInv.Merged.fb_mpt_fail InitECandidate.Solver.Wave8GuestInv.Merged.fb_node_new_hashed InitECandidate.Solver.Wave8GuestInv.Merged.fb_nodedb_lookup InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_rlp_item»
theorem «fb_add_to_bloom» :
    TerminatingFunBoundedOn GuestInv (ofString "add_to_bloom") K.«add_to_bloom» := by
  exact InitECandidate.Solver.Wave8GuestInv.S01.fb_add_to_bloom_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_keccak256»
theorem «fb_bal_init» :
    TerminatingFunBoundedOn GuestInv (ofString "bal_init") K.«bal_init» := by
  have h0 := InitECandidate.Solver.Wave8Leaves.Rlp.«fb_alloc»
  have h1 := InitECandidate.Solver.Wave8GuestInv.Htab.«fb_htab_new»
  fb_prove2 411 Guest.Software.guestFn_bal_init K.«bal_init»

theorem «fb_blake2_init» :
    TerminatingFunBoundedOn GuestInv (ofString "blake2_init") K.«blake2_init» := by
  have h0 := InitECandidate.Solver.Wave8Leaves.Rlp.«fb_alloc»
  fb_prove2 621 Guest.Software.guestFn_blake2_init K.«blake2_init»

theorem «fb_calculate_intrinsic_cost» :
    TerminatingFunBoundedOn GuestInv (ofString "calculate_intrinsic_cost") K.«calculate_intrinsic_cost» := by
  exact InitECandidate.Solver.Wave8Leaves.S13.certified_fb_calculate_intrinsic_cost InitECandidate.Solver.Wave8GuestInv.Merged.fb_count_tokens_in_data InitECandidate.Solver.Wave8GuestInv.Merged.fb_memeq (InitECandidate.Solver.Wave8GuestInv.S01.«on_u256_is_zero» (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv))
theorem «fb_calculate_message_call_gas» :
    TerminatingFunBoundedOn GuestInv (ofString "calculate_message_call_gas") K.«calculate_message_call_gas» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_add_sat
  have h1 := InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees.fb_u256_is_zero
  fb_prove2 602 Guest.Software.guestFn_calculate_message_call_gas K.«calculate_message_call_gas»

theorem «fb_compute_contract_address» :
    TerminatingFunBoundedOn GuestInv (ofString "compute_contract_address") K.«compute_contract_address» := by
  exact InitECandidate.Solver.Wave8Leaves.S08.fb_compute_contract_address_of InitECandidate.Solver.Wave8GuestInv.Merged.fb_rlp_encode_bytes InitECandidate.Solver.Wave8GuestInv.Merged.fb_rlp_encode_word InitECandidate.Solver.Wave8GuestInv.Merged.fb_rlp_list_header_len InitECandidate.Solver.Wave8GuestInv.Merged.fb_rlp_encode_list_header InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_keccak256» InitECandidate.Solver.Wave8GuestInv.Merged.fb_memcpy
theorem «fb_emit_transfer_log» :
    TerminatingFunBoundedOn GuestInv (ofString "emit_transfer_log") K.«emit_transfer_log» := by
  exact InitECandidate.Solver.Wave8Leaves.S04.Verified.fb_emit_transfer_log InitECandidate.Solver.Wave8GuestInv.Merged.fb_alloc InitECandidate.Solver.Wave8GuestInv.Merged.fb_log_append InitECandidate.Solver.Wave8GuestInv.Merged.fb_memcpy InitECandidate.Solver.Wave8GuestInv.Merged.fb_memzero (InitECandidate.Solver.Wave8GuestInv.S01.«on_u256_is_zero» (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv)) InitECandidate.Solver.Wave8GuestInv.R10Shards.P10.«fb_u256_to_be32»
theorem «fb_encode_account» :
    TerminatingFunBoundedOn GuestInv (ofString "encode_account") K.«encode_account» := by
  have h0 := InitECandidate.Solver.Wave8Leaves.Rlp.«fb_rlp_encode_bytes»
  have h1 := InitECandidate.Solver.Wave8Leaves.Rlp.«fb_rlp_encode_word»
  have h2 := InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees.fb_st_be64
  fb_prove2 294 Guest.Software.guestFn_encode_account K.«encode_account»

theorem «fb_evm_init» :
    TerminatingFunBoundedOn GuestInv (ofString "evm_init") K.«evm_init» := by
  exact InitECandidate.Solver.Wave8GuestInv.S14.fb_evm_init_of InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_mark» InitECandidate.Solver.Wave8GuestInv.Merged.fb_alloc InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_release» InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_keccak256» InitECandidate.Solver.Wave8GuestInv.Merged.fb_memzero
theorem «fb_fork_init» :
    TerminatingFunBoundedOn GuestInv (ofString "fork_init") K.«fork_init» := by
  exact InitECandidate.Solver.Wave8GuestInv.S14.fb_fork_init_of InitECandidate.Solver.Wave8GuestInv.Merged.fb_alloc InitECandidate.Solver.Wave8GuestInv.Merged.fb_memzero InitECandidate.Solver.Wave8GuestInv.Merged.fb_addr_from_words (InitECandidate.Solver.Wave8GuestInv.S06.«on_st_be64» (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv))
theorem «fb_get_account» :
    TerminatingFunBoundedOn GuestInv (ofString "get_account") K.«get_account» := by
  exact InitECandidate.Solver.Wave8GuestInv.S01.fb_get_account_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.fb_get_account_optional
theorem «fb_get_pre_tx_account» :
    TerminatingFunBoundedOn GuestInv (ofString "get_pre_tx_account") K.«get_pre_tx_account» := by
  exact InitECandidate.Solver.Wave8Leaves.S03.fb_get_pre_tx_account InitECandidate.Solver.Wave8GuestInv.Merged.fb_htab_get InitECandidate.Solver.Wave8GuestInv.Merged.fb_record_pre_state_read InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.fb_ws_get_account_optional
theorem «fb_get_transient_storage» :
    TerminatingFunBoundedOn GuestInv (ofString "get_transient_storage") K.«get_transient_storage» := by
  exact InitECandidate.Solver.Wave8GuestInv.S11.fb_get_transient_storage_of InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_sk_make» InitECandidate.Solver.Wave8GuestInv.Merged.fb_htab_get
theorem «fb_hdr_bytes_field» :
    TerminatingFunBoundedOn GuestInv (ofString "hdr_bytes_field") K.«hdr_bytes_field» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_rlp_item»
  fb_prove2 225 Guest.Software.guestFn_hdr_bytes_field K.«hdr_bytes_field»

theorem «fb_hdr_raw_field» :
    TerminatingFunBoundedOn GuestInv (ofString "hdr_raw_field") K.«hdr_raw_field» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_rlp_item»
  fb_prove2 226 Guest.Software.guestFn_hdr_raw_field K.«hdr_raw_field»

theorem «fb_hdr_uint_field» :
    TerminatingFunBoundedOn GuestInv (ofString "hdr_uint_field") K.«hdr_uint_field» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_rlp_item»
  fb_prove2 222 Guest.Software.guestFn_hdr_uint_field K.«hdr_uint_field»

theorem «fb_hdr_word_field» :
    TerminatingFunBoundedOn GuestInv (ofString "hdr_word_field") K.«hdr_word_field» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_hdr_uint_field»
  fb_prove2 223 Guest.Software.guestFn_hdr_word_field K.«hdr_word_field»

theorem «fb_host_input_byte» :
    TerminatingFunBoundedOn GuestInv (ofString "host_input_byte") K.«host_input_byte» := by
  fb_prove2 197 Guest.Software.guestFn_host_input_byte K.«host_input_byte»

theorem «fb_host_input_le32» :
    TerminatingFunBoundedOn GuestInv (ofString "host_input_le32") K.«host_input_le32» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_host_input_byte»
  fb_prove2 198 Guest.Software.guestFn_host_input_le32 K.«host_input_le32»

theorem «fb_idx_start_account» :
    TerminatingFunBoundedOn GuestInv (ofString "idx_start_account") K.«idx_start_account» := by
  exact InitECandidate.Solver.Wave8Leaves.S03.fb_idx_start_account InitECandidate.Solver.Wave8GuestInv.Merged.fb_alloc InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_get_pre_tx_account» InitECandidate.Solver.Wave8GuestInv.Merged.fb_htab_get InitECandidate.Solver.Wave8GuestInv.Merged.fb_htab_set InitECandidate.Solver.Wave8GuestInv.Merged.fb_memcpy InitECandidate.Solver.Wave8GuestInv.Merged.fb_memzero InitECandidate.Solver.Wave8GuestInv.Merged.fb_st_le64
theorem «fb_increment_nonce» :
    TerminatingFunBoundedOn GuestInv (ofString "increment_nonce") K.«increment_nonce» := by
  exact InitECandidate.Solver.Wave8Leaves.S03.fb_increment_nonce InitECandidate.Solver.Wave8GuestInv.Merged.fb_acct_copy InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_get_account» InitECandidate.Solver.Wave8GuestInv.Merged.fb_modify_state_commit
theorem «fb_is_account_alive» :
    TerminatingFunBoundedOn GuestInv (ofString "is_account_alive") K.«is_account_alive» := by
  exact InitECandidate.Solver.Wave8Leaves.S04.Verified.fb_is_account_alive InitECandidate.Solver.Wave8GuestInv.Merged.fb_acct_is_empty InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.fb_get_account_optional
theorem «fb_is_warm_storage_key» :
    TerminatingFunBoundedOn GuestInv (ofString "is_warm_storage_key") K.«is_warm_storage_key» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_htab_has»
  have h1 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_sk_make»
  fb_prove2 525 Guest.Software.guestFn_is_warm_storage_key K.«is_warm_storage_key»

theorem «fb_is_zero_bytes» :
    TerminatingFunBoundedOn GuestInv (ofString "is_zero_bytes") K.«is_zero_bytes» := by
  fb_prove2 19 Guest.Software.guestFn_is_zero_bytes K.«is_zero_bytes»

theorem «fb_logs_bloom» :
    TerminatingFunBoundedOn GuestInv (ofString "logs_bloom") K.«logs_bloom» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_add_to_bloom»
  have h1 := InitECandidate.Solver.Wave8Leaves.Rlp.«fb_memzero»
  fb_prove2 832 Guest.Software.guestFn_logs_bloom K.«logs_bloom»

theorem «fb_min» :
    TerminatingFunBoundedOn GuestInv (ofString "min") K.«min» := by
  fb_prove2 31 Guest.Software.guestFn_min K.«min»

theorem «fb_mpt_init» :
    TerminatingFunBoundedOn GuestInv (ofString "mpt_init") K.«mpt_init» := by
  exact InitECandidate.Solver.Wave8GuestInv.S14.fb_mpt_init_of InitECandidate.Solver.Wave8GuestInv.Merged.fb_alloc InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_keccak256»
theorem «fb_mpt_new» :
    TerminatingFunBoundedOn GuestInv (ofString "mpt_new") K.«mpt_new» := by
  have h0 := InitECandidate.Solver.Wave8Leaves.Rlp.«fb_alloc»
  fb_prove2 268 Guest.Software.guestFn_mpt_new K.«mpt_new»

theorem «fb_mpt_nibble_key» :
    TerminatingFunBoundedOn GuestInv (ofString "mpt_nibble_key") K.«mpt_nibble_key» := by
  have h0 := InitECandidate.Solver.Wave8Leaves.Rlp.«fb_alloc»
  have h1 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_keccak256»
  have h2 := InitECandidate.Solver.Wave8Leaves.Rlp.«fb_key_to_nibbles»
  fb_prove2 270 Guest.Software.guestFn_mpt_nibble_key K.«mpt_nibble_key»

theorem «fb_node_hash_cached» :
    TerminatingFunBoundedOn GuestInv (ofString "node_hash_cached") K.«node_hash_cached» := by
  exact InitECandidate.Solver.Wave8Leaves.S00Verified.fb_node_hash_cached InitECandidate.Solver.Wave8GuestInv.Merged.fb_alloc InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_keccak256» InitECandidate.Solver.Wave8GuestInv.Merged.fb_mpt_fail
theorem «fb_node_new_branch» :
    TerminatingFunBoundedOn GuestInv (ofString "node_new_branch") K.«node_new_branch» := by
  have h0 := InitECandidate.Solver.Wave8Leaves.Rlp.«fb_alloc»
  have h1 := InitECandidate.Solver.Wave8Leaves.Rlp.«fb_memzero»
  fb_prove2 258 Guest.Software.guestFn_node_new_branch K.«node_new_branch»

theorem «fb_node_write_ref» :
    TerminatingFunBoundedOn GuestInv (ofString "node_write_ref") K.«node_write_ref» := by
  exact InitECandidate.Solver.Wave8Leaves.S00Verified.fb_node_write_ref InitECandidate.Solver.Wave8GuestInv.Merged.fb_memcpy InitECandidate.Solver.Wave8GuestInv.Merged.fb_mpt_fail InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_node_hash_cached»
theorem «fb_op_address» :
    TerminatingFunBoundedOn GuestInv (ofString "op_address") K.«op_address» := by
  exact InitECandidate.Solver.Wave8GuestInv.S06.fb_op_address_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) InitECandidate.Solver.Wave8GuestInv.Merged.fb_charge_gas InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees.fb_address_to_u256 InitECandidate.Solver.Wave8GuestInv.Merged.fb_stack_push InitECandidate.Solver.Wave8GuestInv.Merged.fb_pc_add
theorem «fb_op_balance» :
    TerminatingFunBoundedOn GuestInv (ofString "op_balance") K.«op_balance» := by
  exact InitECandidate.Solver.Wave8GuestInv.S06.fb_op_balance_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) InitECandidate.Solver.Wave8GuestInv.Merged.fb_stack_pop InitECandidate.Solver.Wave8GuestInv.Merged.fb_to_address_masked InitECandidate.Solver.Wave8GuestInv.Merged.fb_access_gas_cost InitECandidate.Solver.Wave8GuestInv.Merged.fb_charge_gas InitECandidate.Solver.Wave8GuestInv.Merged.fb_warm_after_charge InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_get_account» InitECandidate.Solver.Wave8GuestInv.Merged.fb_stack_push InitECandidate.Solver.Wave8GuestInv.Merged.fb_pc_add
theorem «fb_op_blobhash» :
    TerminatingFunBoundedOn GuestInv (ofString "op_blobhash") K.«op_blobhash» := by
  exact InitECandidate.Solver.Wave8GuestInv.S06.fb_op_blobhash_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) InitECandidate.Solver.Wave8GuestInv.Merged.fb_charge_gas InitECandidate.Solver.Wave8GuestInv.Merged.fb_stack_pop InitECandidate.Solver.Wave8GuestInv.Merged.fb_sat_word InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees.«fb_u256_from_be» InitECandidate.Solver.Wave8GuestInv.Merged.fb_stack_push InitECandidate.Solver.Wave8GuestInv.Merged.fb_pc_add
theorem «fb_op_blockhash» :
    TerminatingFunBoundedOn GuestInv (ofString "op_blockhash") K.«op_blockhash» := by
  exact InitECandidate.Solver.Wave8GuestInv.S06.fb_op_blockhash_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) InitECandidate.Solver.Wave8GuestInv.Merged.fb_stack_pop InitECandidate.Solver.Wave8GuestInv.Merged.fb_charge_gas InitECandidate.Solver.Wave8GuestInv.Merged.fb_block_env InitECandidate.Solver.Wave8GuestInv.Merged.fb_sat_word InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees.«fb_u256_from_be» InitECandidate.Solver.Wave8GuestInv.Merged.fb_track_ancestor_access InitECandidate.Solver.Wave8GuestInv.Merged.fb_stack_push InitECandidate.Solver.Wave8GuestInv.Merged.fb_pc_add
theorem «fb_op_calldatacopy» :
    TerminatingFunBoundedOn GuestInv (ofString "op_calldatacopy") K.«op_calldatacopy» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.P12_P15.«fb_copy_from_buffer»
  fb_prove2 539 Guest.Software.guestFn_op_calldatacopy K.«op_calldatacopy»

theorem «fb_op_calldataload» :
    TerminatingFunBoundedOn GuestInv (ofString "op_calldataload") K.«op_calldataload» := by
  have h0 := InitECandidate.Solver.Wave8Leaves.Rlp.«fb_alloc»
  have h1 := InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees.«fb_buffer_read»
  have h2 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_charge_gas»
  have h3 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_mark»
  have h4 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_release»
  have h5 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_pc_add
  have h6 := InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees.«fb_sat_word»
  have h7 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_stack_pop
  have h8 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_stack_push»
  have h9 := InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees.«fb_u256_from_be»
  fb_prove2 536 Guest.Software.guestFn_op_calldataload K.«op_calldataload»

theorem «fb_op_calldatasize» :
    TerminatingFunBoundedOn GuestInv (ofString "op_calldatasize") K.«op_calldatasize» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_charge_gas»
  have h1 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_pc_add
  have h2 := InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees.«fb_stack_push_word»
  fb_prove2 537 Guest.Software.guestFn_op_calldatasize K.«op_calldatasize»

theorem «fb_op_caller» :
    TerminatingFunBoundedOn GuestInv (ofString "op_caller") K.«op_caller» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees.«fb_address_to_u256»
  have h1 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_charge_gas»
  have h2 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_pc_add
  have h3 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_stack_push»
  fb_prove2 534 Guest.Software.guestFn_op_caller K.«op_caller»

theorem «fb_op_coinbase» :
    TerminatingFunBoundedOn GuestInv (ofString "op_coinbase") K.«op_coinbase» := by
  exact InitECandidate.Solver.Wave8Leaves.S08.fb_op_coinbase InitECandidate.Solver.Wave8GuestInv.Merged.fb_charge_gas InitECandidate.Solver.Wave8GuestInv.Merged.fb_block_env InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees.fb_address_to_u256 InitECandidate.Solver.Wave8GuestInv.Merged.fb_stack_push InitECandidate.Solver.Wave8GuestInv.Merged.fb_pc_add
theorem «fb_op_exchange» :
    TerminatingFunBoundedOn GuestInv (ofString "op_exchange") K.«op_exchange» := by
  exact InitECandidate.Solver.Wave8Leaves.S08.fb_op_exchange_of InitECandidate.Solver.Wave8GuestInv.Merged.fb_charge_gas InitECandidate.Solver.Wave8GuestInv.R10Shards.P10.«fb_max» InitECandidate.Solver.Wave8GuestInv.Merged.fb_pc_add
theorem «fb_op_extcodehash» :
    TerminatingFunBoundedOn GuestInv (ofString "op_extcodehash") K.«op_extcodehash» := by
  exact InitECandidate.Solver.Wave8Leaves.S08.fb_op_extcodehash InitECandidate.Solver.Wave8GuestInv.Merged.fb_stack_pop InitECandidate.Solver.Wave8GuestInv.Merged.fb_to_address_masked InitECandidate.Solver.Wave8GuestInv.Merged.fb_access_gas_cost InitECandidate.Solver.Wave8GuestInv.Merged.fb_charge_gas InitECandidate.Solver.Wave8GuestInv.Merged.fb_warm_after_charge InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_get_account» InitECandidate.Solver.Wave8GuestInv.Merged.fb_acct_is_empty InitECandidate.Solver.Wave8GuestInv.Merged.fb_stack_push InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees.«fb_u256_from_be» InitECandidate.Solver.Wave8GuestInv.Merged.fb_pc_add
theorem «fb_op_iszero» :
    TerminatingFunBoundedOn GuestInv (ofString "op_iszero") K.«op_iszero» := by
  exact InitECandidate.Solver.Wave8Leaves.S09.fb_op_iszero (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) InitECandidate.Solver.Wave8GuestInv.Merged.fb_charge_gas InitECandidate.Solver.Wave8GuestInv.Merged.fb_pc_add InitECandidate.Solver.Wave8GuestInv.Merged.fb_stack_pop InitECandidate.Solver.Wave8GuestInv.Merged.fb_stack_push_bool (InitECandidate.Solver.Wave8GuestInv.S01.«on_u256_is_zero» (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv))
theorem «fb_op_mstore» :
    TerminatingFunBoundedOn GuestInv (ofString "op_mstore") K.«op_mstore» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees.«fb_charge_with_memory»
  have h1 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_pc_add
  have h2 := InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees.«fb_sat_word»
  have h3 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_stack_pop
  have h4 := InitECandidate.Solver.Wave8GuestInv.R10Shards.P10.«fb_u256_to_be32»
  fb_prove2 508 Guest.Software.guestFn_op_mstore K.«op_mstore»

theorem «fb_op_mstore8» :
    TerminatingFunBoundedOn GuestInv (ofString "op_mstore8") K.«op_mstore8» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees.«fb_charge_with_memory»
  have h1 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_pc_add
  have h2 := InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees.«fb_sat_word»
  have h3 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_stack_pop
  fb_prove2 509 Guest.Software.guestFn_op_mstore8 K.«op_mstore8»

theorem «fb_op_not» :
    TerminatingFunBoundedOn GuestInv (ofString "op_not") K.«op_not» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_charge_gas»
  have h1 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_pc_add
  have h2 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_stack_pop
  have h3 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_stack_push»
  fb_prove2 495 Guest.Software.guestFn_op_not K.«op_not»

theorem «fb_op_number» :
    TerminatingFunBoundedOn GuestInv (ofString "op_number") K.«op_number» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_block_env
  have h1 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_charge_gas»
  have h2 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_pc_add
  have h3 := InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees.«fb_stack_push_word»
  fb_prove2 557 Guest.Software.guestFn_op_number K.«op_number»

theorem «fb_op_or» :
    TerminatingFunBoundedOn GuestInv (ofString "op_or") K.«op_or» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_charge_gas»
  have h1 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_pc_add
  have h2 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_stack_pop
  have h3 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_stack_push»
  fb_prove2 493 Guest.Software.guestFn_op_or K.«op_or»

theorem «fb_op_prevrandao» :
    TerminatingFunBoundedOn GuestInv (ofString "op_prevrandao") K.«op_prevrandao» := by
  exact InitECandidate.Solver.Wave8Leaves.S10.fb_op_prevrandao InitECandidate.Solver.Wave8GuestInv.Merged.fb_charge_gas InitECandidate.Solver.Wave8GuestInv.Merged.fb_block_env InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees.«fb_u256_from_be» InitECandidate.Solver.Wave8GuestInv.Merged.fb_stack_push InitECandidate.Solver.Wave8GuestInv.Merged.fb_pc_add
theorem «fb_op_selfbalance» :
    TerminatingFunBoundedOn GuestInv (ofString "op_selfbalance") K.«op_selfbalance» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_charge_gas»
  have h1 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_get_account»
  have h2 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_pc_add
  have h3 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_stack_push»
  fb_prove2 549 Guest.Software.guestFn_op_selfbalance K.«op_selfbalance»

theorem «fb_op_tload» :
    TerminatingFunBoundedOn GuestInv (ofString "op_tload") K.«op_tload» := by
  exact InitECandidate.Solver.Wave8GuestInv.S11.fb_op_tload_of InitECandidate.Solver.Wave8GuestInv.Merged.fb_stack_pop InitECandidate.Solver.Wave8GuestInv.Merged.fb_charge_gas InitECandidate.Solver.Wave8GuestInv.R10Shards.P10.«fb_u256_to_be32» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_get_transient_storage» InitECandidate.Solver.Wave8GuestInv.Merged.fb_stack_push InitECandidate.Solver.Wave8GuestInv.Merged.fb_pc_add
theorem «fb_set_account_balance» :
    TerminatingFunBoundedOn GuestInv (ofString "set_account_balance") K.«set_account_balance» := by
  exact InitECandidate.Solver.Wave8Leaves.S12.fb_set_account_balance InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_get_account» InitECandidate.Solver.Wave8GuestInv.Merged.fb_acct_copy InitECandidate.Solver.Wave8GuestInv.Merged.fb_modify_state_commit
theorem «fb_set_code» :
    TerminatingFunBoundedOn GuestInv (ofString "set_code") K.«set_code» := by
  exact InitECandidate.Solver.Wave8Leaves.S03.fb_set_code InitECandidate.Solver.Wave8GuestInv.Merged.fb_acct_copy InitECandidate.Solver.Wave8GuestInv.Merged.fb_alloc InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_get_account» InitECandidate.Solver.Wave8GuestInv.Merged.fb_jset InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_keccak256» InitECandidate.Solver.Wave8GuestInv.Merged.fb_memeq InitECandidate.Solver.Wave8GuestInv.Merged.fb_modify_state_commit
theorem «fb_set_transient_storage» :
    TerminatingFunBoundedOn GuestInv (ofString "set_transient_storage") K.«set_transient_storage» := by
  exact InitECandidate.Solver.Wave8GuestInv.S11.fb_set_transient_storage_of InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_sk_make» (InitECandidate.Solver.Wave8GuestInv.S01.«on_u256_is_zero» (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv)) InitECandidate.Solver.Wave8GuestInv.Merged.fb_jdel InitECandidate.Solver.Wave8GuestInv.Merged.fb_alloc InitECandidate.Solver.Wave8GuestInv.Merged.fb_jset
theorem «fb_sha256_pair» :
    TerminatingFunBoundedOn GuestInv (ofString "sha256_pair") K.«sha256_pair» := by
  fb_prove2 96 Guest.Software.guestFn_sha256_pair K.«sha256_pair»

theorem «fb_ssz_fail» :
    TerminatingFunBoundedOn GuestInv (ofString "ssz_fail") K.«ssz_fail» := by
  fb_prove2 196 Guest.Software.guestFn_ssz_fail K.«ssz_fail»

theorem «fb_ssz_fixed_list_count» :
    TerminatingFunBoundedOn GuestInv (ofString "ssz_fixed_list_count") K.«ssz_fixed_list_count» := by
  exact InitECandidate.Solver.Wave8Leaves.S13.certified_fb_ssz_fixed_list_count InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_ssz_fail» InitECandidate.Solver.Wave8GuestInv.P13.DivMod.«fb_udivmod»
theorem «fb_ssz_split_var_list» :
    TerminatingFunBoundedOn GuestInv (ofString "ssz_split_var_list") K.«ssz_split_var_list» := by
  exact InitECandidate.Solver.Wave8Leaves.S13.certified_fb_ssz_split_var_list InitECandidate.Solver.Wave8GuestInv.Merged.fb_alloc InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_ssz_fail»
theorem «fb_state_snapshot» :
    TerminatingFunBoundedOn GuestInv (ofString "state_snapshot") K.«state_snapshot» := by
  fb_prove2 358 Guest.Software.guestFn_state_snapshot K.«state_snapshot»

theorem «fb_tx_bytes_item» :
    TerminatingFunBoundedOn GuestInv (ofString "tx_bytes_item") K.«tx_bytes_item» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_rlp_item»
  fb_prove2 299 Guest.Software.guestFn_tx_bytes_item K.«tx_bytes_item»

theorem «fb_tx_fixed_bytes» :
    TerminatingFunBoundedOn GuestInv (ofString "tx_fixed_bytes") K.«tx_fixed_bytes» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_rlp_item»
  fb_prove2 300 Guest.Software.guestFn_tx_fixed_bytes K.«tx_fixed_bytes»

theorem «fb_tx_list_item» :
    TerminatingFunBoundedOn GuestInv (ofString "tx_list_item") K.«tx_list_item» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_rlp_item»
  fb_prove2 302 Guest.Software.guestFn_tx_list_item K.«tx_list_item»

theorem «fb_tx_scalar_item» :
    TerminatingFunBoundedOn GuestInv (ofString "tx_scalar_item") K.«tx_scalar_item» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_rlp_item»
  fb_prove2 296 Guest.Software.guestFn_tx_scalar_item K.«tx_scalar_item»

theorem «fb_tx_scalar_u256» :
    TerminatingFunBoundedOn GuestInv (ofString "tx_scalar_u256") K.«tx_scalar_u256» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_tx_scalar_item»
  have h1 := InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees.«fb_u256_from_be»
  fb_prove2 297 Guest.Software.guestFn_tx_scalar_u256 K.«tx_scalar_u256»

theorem «fb_tx_scalar_word» :
    TerminatingFunBoundedOn GuestInv (ofString "tx_scalar_word") K.«tx_scalar_word» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_tx_scalar_item»
  fb_prove2 298 Guest.Software.guestFn_tx_scalar_word K.«tx_scalar_word»

theorem «fb_tx_to_item» :
    TerminatingFunBoundedOn GuestInv (ofString "tx_to_item") K.«tx_to_item» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_rlp_item»
  fb_prove2 301 Guest.Software.guestFn_tx_to_item K.«tx_to_item»

end InitECandidate.Solver.Wave8GuestInv.R11Adapters
