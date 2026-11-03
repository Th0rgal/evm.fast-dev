import InitECandidate.Solver.Wave8GuestInv.R11Adapters.FbClosure1

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

theorem «fb_u256_add» :
    TerminatingFunBoundedOn GuestInv (ofString "u256_add") K.«u256_add» := by
  fb_prove2 56 Guest.Software.guestFn_u256_add K.«u256_add»

theorem «fb_u256_add_carry» :
    TerminatingFunBoundedOn GuestInv (ofString "u256_add_carry") K.«u256_add_carry» := by
  fb_prove2 55 Guest.Software.guestFn_u256_add_carry K.«u256_add_carry»

theorem «fb_u256_and» :
    TerminatingFunBoundedOn GuestInv (ofString "u256_and") K.«u256_and» := by
  fb_prove2 52 Guest.Software.guestFn_u256_and K.«u256_and»

theorem «fb_u256_byte_length» :
    TerminatingFunBoundedOn GuestInv (ofString "u256_byte_length") K.«u256_byte_length» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees.«fb_u256_bit_length»
  fb_prove2 79 Guest.Software.guestFn_u256_byte_length K.«u256_byte_length»

theorem «fb_u256_div» :
    TerminatingFunBoundedOn GuestInv (ofString "u256_div") K.«u256_div» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.P13.DivMod.«fb_u256_divmod»
  fb_prove2 70 Guest.Software.guestFn_u256_div K.«u256_div»

theorem «fb_u256_eq» :
    TerminatingFunBoundedOn GuestInv (ofString "u256_eq") K.«u256_eq» := by
  fb_prove2 45 Guest.Software.guestFn_u256_eq K.«u256_eq»

theorem «fb_u256_fits_word» :
    TerminatingFunBoundedOn GuestInv (ofString "u256_fits_word") K.«u256_fits_word» := by
  fb_prove2 41 Guest.Software.guestFn_u256_fits_word K.«u256_fits_word»

theorem «fb_u256_from_word» :
    TerminatingFunBoundedOn GuestInv (ofString "u256_from_word") K.«u256_from_word» := by
  fb_prove2 39 Guest.Software.guestFn_u256_from_word K.«u256_from_word»

theorem «fb_u256_gt» :
    TerminatingFunBoundedOn GuestInv (ofString "u256_gt") K.«u256_gt» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees.«fb_u256_lt»
  fb_prove2 47 Guest.Software.guestFn_u256_gt K.«u256_gt»

theorem «fb_u256_limb» :
    TerminatingFunBoundedOn GuestInv (ofString "u256_limb") K.«u256_limb» := by
  fb_prove2 43 Guest.Software.guestFn_u256_limb K.«u256_limb»

theorem «fb_u256_mul» :
    TerminatingFunBoundedOn GuestInv (ofString "u256_mul") K.«u256_mul» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees.«fb_mul64x64»
  fb_prove2 60 Guest.Software.guestFn_u256_mul K.«u256_mul»

theorem «fb_u256_mul_full» :
    TerminatingFunBoundedOn GuestInv (ofString "u256_mul_full") K.«u256_mul_full» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees.«fb_mul64x64»
  fb_prove2 61 Guest.Software.guestFn_u256_mul_full K.«u256_mul_full»

theorem «fb_u256_neg» :
    TerminatingFunBoundedOn GuestInv (ofString "u256_neg") K.«u256_neg» := by
  fb_prove2 58 Guest.Software.guestFn_u256_neg K.«u256_neg»

theorem «fb_u256_not» :
    TerminatingFunBoundedOn GuestInv (ofString "u256_not") K.«u256_not» := by
  fb_prove2 51 Guest.Software.guestFn_u256_not K.«u256_not»

theorem «fb_u256_or» :
    TerminatingFunBoundedOn GuestInv (ofString "u256_or") K.«u256_or» := by
  fb_prove2 53 Guest.Software.guestFn_u256_or K.«u256_or»

theorem «fb_u256_shl» :
    TerminatingFunBoundedOn GuestInv (ofString "u256_shl") K.«u256_shl» := by
  fb_prove2 81 Guest.Software.guestFn_u256_shl K.«u256_shl»

theorem «fb_u256_shr» :
    TerminatingFunBoundedOn GuestInv (ofString "u256_shr") K.«u256_shr» := by
  fb_prove2 82 Guest.Software.guestFn_u256_shr K.«u256_shr»

theorem «fb_u256_slt» :
    TerminatingFunBoundedOn GuestInv (ofString "u256_slt") K.«u256_slt» := by
  fb_prove2 48 Guest.Software.guestFn_u256_slt K.«u256_slt»

theorem «fb_u256_sub» :
    TerminatingFunBoundedOn GuestInv (ofString "u256_sub") K.«u256_sub» := by
  fb_prove2 57 Guest.Software.guestFn_u256_sub K.«u256_sub»

theorem «fb_u256_to_be_min» :
    TerminatingFunBoundedOn GuestInv (ofString "u256_to_be_min") K.«u256_to_be_min» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_byte_length»
  have h1 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_limb»
  fb_prove2 88 Guest.Software.guestFn_u256_to_be_min K.«u256_to_be_min»

theorem «fb_udiv» :
    TerminatingFunBoundedOn GuestInv (ofString "udiv") K.«udiv» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.P13.DivMod.«fb_udivmod»
  fb_prove2 34 Guest.Software.guestFn_udiv K.«udiv»

theorem «fb_udiv_small5» :
    TerminatingFunBoundedOn GuestInv (ofString "udiv_small5") K.«udiv_small5» := by
  exact InitECandidate.Solver.Wave8Leaves.S12.fb_udiv_small5 InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_udiv»
theorem «fb_validate_block_access_list_gas_limit» :
    TerminatingFunBoundedOn GuestInv (ofString "validate_block_access_list_gas_limit") K.«validate_block_access_list_gas_limit» := by
  exact InitECandidate.Solver.Wave8Leaves.S13.certified_fb_validate_block_access_list_gas_limit InitECandidate.Solver.Wave8GuestInv.Merged.fb_htab_has InitECandidate.Solver.Wave8GuestInv.Merged.fb_htab_item InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_udiv»
theorem «fb_validate_transaction» :
    TerminatingFunBoundedOn GuestInv (ofString "validate_transaction") K.«validate_transaction» := by
  exact InitECandidate.Solver.Wave8Leaves.S13.certified_fb_validate_transaction InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_calculate_intrinsic_cost» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_fits_word»
theorem «fb_ws_get_code» :
    TerminatingFunBoundedOn GuestInv (ofString "ws_get_code") K.«ws_get_code» := by
  have h0 := InitECandidate.Solver.Wave8Leaves.Rlp.«fb_memeq»
  have h1 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_nodedb_lookup
  fb_prove2 370 Guest.Software.guestFn_ws_get_code K.«ws_get_code»

theorem «fb_ws_storage_root_of» :
    TerminatingFunBoundedOn GuestInv (ofString "ws_storage_root_of") K.«ws_storage_root_of» := by
  exact InitECandidate.Solver.Wave8GuestInv.S01.fb_ws_storage_root_of_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.fb_ws_get_account_optional
theorem «fb__create_branch_from_two_leaves» :
    TerminatingFunBoundedOn GuestInv (ofString "_create_branch_from_two_leaves") K.«_create_branch_from_two_leaves» := by
  exact InitECandidate.Solver.Wave8Leaves.S00Verified.fb__create_branch_from_two_leaves InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_node_new_branch» InitECandidate.Solver.Wave8GuestInv.R10Shards.P02.«fb_node_new_leaf»

theorem «fb__node_rlp_finish» :
    TerminatingFunBoundedOn GuestInv (ofString "_node_rlp_finish") K.«_node_rlp_finish» := by
  exact InitECandidate.Solver.Wave8Leaves.S00Verified.fb__node_rlp_finish InitECandidate.Solver.Wave8Leaves.Rlp.«fb_alloc» InitECandidate.Solver.Wave8GuestInv.Merged.fb_node_ref_len InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_node_write_ref» InitECandidate.Solver.Wave8Leaves.Rlp.«fb_rlp_encode_bytes» InitECandidate.Solver.Wave8Leaves.Rlp.«fb_rlp_encode_list_header» InitECandidate.Solver.Wave8Leaves.Rlp.«fb_rlp_list_header_len» InitECandidate.Solver.Wave8Leaves.Rlp.«fb_rlp_value_encoded_len»

theorem «fb__split_extension» :
    TerminatingFunBoundedOn GuestInv (ofString "_split_extension") K.«_split_extension» := by
  exact InitECandidate.Solver.Wave8Leaves.S00Verified.fb__split_extension InitECandidate.Solver.Wave8Leaves.Rlp.«fb_mpt_fail» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_node_new_branch» InitECandidate.Solver.Wave8GuestInv.Merged.fb_node_new_ext InitECandidate.Solver.Wave8GuestInv.R10Shards.P02.«fb_node_new_leaf»

theorem «fb_clear_account_preserving_balance» :
    TerminatingFunBoundedOn GuestInv (ofString "clear_account_preserving_balance") K.«clear_account_preserving_balance» := by
  exact InitECandidate.Solver.Wave8GuestInv.S11.fb_clear_account_preserving_balance_of InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_destroy_storage» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_get_account» InitECandidate.Solver.Wave8GuestInv.Merged.fb_acct_copy InitECandidate.Solver.Wave8GuestInv.Merged.fb_modify_state_commit

theorem «fb_common_prefix_length» :
    TerminatingFunBoundedOn GuestInv (ofString "common_prefix_length") K.«common_prefix_length» := by
  exact InitECandidate.Solver.Wave8Leaves.S00Verified.fb_common_prefix_length InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_min»

theorem «fb_create_ether» :
    TerminatingFunBoundedOn GuestInv (ofString "create_ether") K.«create_ether» := by
  exact InitECandidate.Solver.Wave8GuestInv.S11.fb_create_ether_of InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_get_account» InitECandidate.Solver.Wave8GuestInv.Merged.fb_acct_copy InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_add» InitECandidate.Solver.Wave8GuestInv.Merged.fb_modify_state_commit

theorem «fb_create_finish» :
    TerminatingFunBoundedOn GuestInv (ofString "create_finish") K.«create_finish» := by
  exact InitECandidate.Solver.Wave8Leaves.S03.fb_create_finish InitECandidate.Solver.Wave8Leaves.Rlp.«fb_alloc» InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_charge_gas» InitECandidate.Solver.Wave8GuestInv.Merged.fb_charge_state_gas InitECandidate.Solver.Wave8Leaves.Rlp.«fb_memcpy» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_set_code» InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees.«fb_words_of»

theorem «fb_decode_bytes_list» :
    TerminatingFunBoundedOn GuestInv (ofString "decode_bytes_list") K.«decode_bytes_list» := by
  exact InitECandidate.Solver.Wave8Leaves.S13.certified_fb_decode_bytes_list InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_ssz_fail» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_ssz_split_var_list»

theorem «fb_encode_receipt» :
    TerminatingFunBoundedOn GuestInv (ofString "encode_receipt") K.«encode_receipt» := by
  exact InitECandidate.Solver.Wave8GuestInv.S11.fb_encode_receipt_of InitECandidate.Solver.Wave8GuestInv.Merged.fb_logs_encoded_bound InitECandidate.Solver.Wave8Leaves.Rlp.«fb_alloc» InitECandidate.Solver.Wave8Leaves.Rlp.«fb_rlp_encode_word» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_logs_bloom» InitECandidate.Solver.Wave8Leaves.Rlp.«fb_rlp_encode_bytes» InitECandidate.Solver.Wave8GuestInv.Merged.fb_encode_logs InitECandidate.Solver.Wave8Leaves.Rlp.«fb_rlp_finish_list»

theorem «fb_fee_mul» :
    TerminatingFunBoundedOn GuestInv (ofString "fee_mul") K.«fee_mul» := by
  exact InitECandidate.Solver.Wave8GuestInv.S11.fb_fee_mul_of InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_mul_full»

theorem «fb_merkleize» :
    TerminatingFunBoundedOn GuestInv (ofString "merkleize") K.«merkleize» := by
  exact InitECandidate.Solver.Wave8GuestInv.S14.fb_merkleize_of InitECandidate.Solver.Wave8GuestInv.Merged.fb_ceil_log2 InitECandidate.Solver.Wave8GuestInv.R10Shards.P10.«fb_max» InitECandidate.Solver.Wave8Leaves.Rlp.«fb_memcpy» InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_mark» InitECandidate.Solver.Wave8Leaves.Rlp.«fb_alloc» InitECandidate.Solver.Wave8Leaves.Rlp.«fb_memzero» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_sha256_pair» InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_release»

theorem «fb_merkleize_progressive» :
    TerminatingFunBoundedOn GuestInv (ofString "merkleize_progressive") K.«merkleize_progressive» := by
  exact InitECandidate.Solver.Wave8GuestInv.S14.fb_merkleize_progressive_of InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_mark» InitECandidate.Solver.Wave8Leaves.Rlp.«fb_alloc» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_merkleize» InitECandidate.Solver.Wave8Leaves.Rlp.«fb_memzero» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_sha256_pair» InitECandidate.Solver.Wave8Leaves.Rlp.«fb_memcpy» InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_release»

theorem «fb_mix_in_length» :
    TerminatingFunBoundedOn GuestInv (ofString "mix_in_length") K.«mix_in_length» := by
  exact InitECandidate.Solver.Wave8GuestInv.S14.fb_mix_in_length_of InitECandidate.Solver.Wave8Leaves.Rlp.«fb_memzero» InitECandidate.Solver.Wave8Leaves.Rlp.«fb_st_le64» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_sha256_pair»

theorem «fb_move_ether» :
    TerminatingFunBoundedOn GuestInv (ofString "move_ether") K.«move_ether» := by
  exact InitECandidate.Solver.Wave8Leaves.S04.Verified.fb_move_ether InitECandidate.Solver.Wave8GuestInv.Merged.fb_acct_copy InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_get_account» InitECandidate.Solver.Wave8GuestInv.Merged.fb_modify_state_commit InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_add» InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees.«fb_u256_lt» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_sub»

theorem «fb_nodedb_build» :
    TerminatingFunBoundedOn GuestInv (ofString "nodedb_build") K.«nodedb_build» := by
  exact InitECandidate.Solver.Wave8Leaves.S13.certified_fb_nodedb_build InitECandidate.Solver.Wave8GuestInv.Htab.«fb_htab_new» InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_htab_set» InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_keccak256»

theorem «fb_op_add» :
    TerminatingFunBoundedOn GuestInv (ofString "op_add") K.«op_add» := by
  exact InitECandidate.Solver.Wave8GuestInv.S06.fb_op_add_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_charge_gas» InitECandidate.Solver.Wave8GuestInv.Merged.fb_stack_pop InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_add» InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_stack_push» InitECandidate.Solver.Wave8GuestInv.Merged.fb_pc_add

theorem «fb_op_div» :
    TerminatingFunBoundedOn GuestInv (ofString "op_div") K.«op_div» := by
  exact InitECandidate.Solver.Wave8Leaves.S08.fb_op_div InitECandidate.Solver.Wave8GuestInv.Merged.fb_stack_pop InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_charge_gas» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_div» InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_stack_push» InitECandidate.Solver.Wave8GuestInv.Merged.fb_pc_add

theorem «fb_op_eq» :
    TerminatingFunBoundedOn GuestInv (ofString "op_eq") K.«op_eq» := by
  exact InitECandidate.Solver.Wave8Leaves.S08.fb_op_eq_of InitECandidate.Solver.Wave8GuestInv.Merged.fb_stack_pop InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_charge_gas» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_eq» InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_stack_push» InitECandidate.Solver.Wave8GuestInv.Merged.fb_pc_add

theorem «fb_op_gt» :
    TerminatingFunBoundedOn GuestInv (ofString "op_gt") K.«op_gt» := by
  exact InitECandidate.Solver.Wave8Leaves.S09.fb_op_gt (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_charge_gas» InitECandidate.Solver.Wave8GuestInv.Merged.fb_pc_add InitECandidate.Solver.Wave8GuestInv.Merged.fb_stack_pop InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees.«fb_stack_push_bool» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_gt»

theorem «fb_op_shl» :
    TerminatingFunBoundedOn GuestInv (ofString "op_shl") K.«op_shl» := by
  exact InitECandidate.Solver.Wave8Leaves.S10.fb_op_shl InitECandidate.Solver.Wave8GuestInv.Merged.fb_stack_pop InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_charge_gas» InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees.«fb_sat_word» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_shl» InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_stack_push» InitECandidate.Solver.Wave8GuestInv.Merged.fb_pc_add

theorem «fb_op_sub» :
    TerminatingFunBoundedOn GuestInv (ofString "op_sub") K.«op_sub» := by
  exact InitECandidate.Solver.Wave8Leaves.S10.fb_op_sub InitECandidate.Solver.Wave8GuestInv.Merged.fb_stack_pop InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_charge_gas» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_sub» InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_stack_push» InitECandidate.Solver.Wave8GuestInv.Merged.fb_pc_add

theorem «fb_op_tstore» :
    TerminatingFunBoundedOn GuestInv (ofString "op_tstore") K.«op_tstore» := by
  exact InitECandidate.Solver.Wave8GuestInv.S11.fb_op_tstore_of InitECandidate.Solver.Wave8Leaves.S08.«fb_require_not_static» InitECandidate.Solver.Wave8GuestInv.Merged.fb_stack_pop InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_charge_gas» InitECandidate.Solver.Wave8GuestInv.R10Shards.P10.«fb_u256_to_be32» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_set_transient_storage» InitECandidate.Solver.Wave8GuestInv.Merged.fb_pc_add

theorem «fb_rlp_put_u256» :
    TerminatingFunBoundedOn GuestInv (ofString "rlp_put_u256") K.«rlp_put_u256» := by
  exact InitECandidate.Solver.Wave8GuestInv.S02.fb_rlp_put_u256 InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_mark» InitECandidate.Solver.Wave8Leaves.Rlp.«fb_alloc» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_to_be_min» InitECandidate.Solver.Wave8Leaves.Rlp.«fb_rlp_encode_bytes» InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_release»

theorem «fb_ssz_check_offsets» :
    TerminatingFunBoundedOn GuestInv (ofString "ssz_check_offsets") K.«ssz_check_offsets» := by
  exact InitECandidate.Solver.Wave8Leaves.S13.certified_fb_ssz_check_offsets InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_ssz_fail»

theorem «fb_taylor_exponential» :
    TerminatingFunBoundedOn GuestInv (ofString "taylor_exponential") K.«taylor_exponential» := by
  exact InitECandidate.Solver.Wave8GuestInv.S06.fb_taylor_exponential_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_from_word» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_mul» (InitECandidate.Solver.Wave8GuestInv.S01.«on_u256_is_zero» (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv)) InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_add» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_mul_full» InitECandidate.Solver.Wave8Leaves.Rlp.«fb_trap_with» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_div»

theorem «fb_tx_chain_id» :
    TerminatingFunBoundedOn GuestInv (ofString "tx_chain_id") K.«tx_chain_id» := by
  exact InitECandidate.Solver.Wave8Leaves.S12.fb_tx_chain_id InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_fits_word» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_sub» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_shr»

theorem «fb_tx_put_u256» :
    TerminatingFunBoundedOn GuestInv (ofString "tx_put_u256") K.«tx_put_u256» := by
  exact InitECandidate.Solver.Wave8Leaves.S12.fb_tx_put_u256 InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_mark» InitECandidate.Solver.Wave8Leaves.Rlp.«fb_alloc» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_to_be_min» InitECandidate.Solver.Wave8Leaves.Rlp.«fb_rlp_encode_bytes» InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_release»

theorem «fb_tx_u256_encoded_len» :
    TerminatingFunBoundedOn GuestInv (ofString "tx_u256_encoded_len") K.«tx_u256_encoded_len» := by
  exact InitECandidate.Solver.Wave8GuestInv.S11.fb_tx_u256_encoded_len_of InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_byte_length»

theorem «fb_ws_account_has_storage» :
    TerminatingFunBoundedOn GuestInv (ofString "ws_account_has_storage") K.«ws_account_has_storage» := by
  exact InitECandidate.Solver.Wave8GuestInv.S01.fb_ws_account_has_storage_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_ws_storage_root_of» InitECandidate.Solver.Wave8Leaves.Rlp.«fb_memeq»

theorem «fb__decode_step» :
    TerminatingFunBoundedOn GuestInv (ofString "_decode_step") K.«_decode_step» := by
  have h0 := InitECandidate.Solver.Wave8Leaves.Rlp.«fb_compact_to_nibbles»
  have h1 := InitECandidate.Solver.Wave8Leaves.Rlp.«fb_mpt_fail»
  have h2 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_node_new_branch»
  have h3 := InitECandidate.Solver.Wave8GuestInv.R10Shards.P02.«fb_node_new_leaf»
  have h4 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_rlp_decode_fully»
  have h5 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_rlp_item»
  have h6 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_rlp_list_to_slices»
  have h7 := InitECandidate.Solver.Wave8Leaves.Rlp.«fb_scratch_alloc»
  fb_prove2 261 Guest.Software.guestFn__decode_step K.«_decode_step»

theorem «fb__insert_into_leaf» :
    TerminatingFunBoundedOn GuestInv (ofString "_insert_into_leaf") K.«_insert_into_leaf» := by
  exact InitECandidate.Solver.Wave8Leaves.S00Verified.fb__insert_into_leaf InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb__create_branch_from_two_leaves» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_common_prefix_length» InitECandidate.Solver.Wave8GuestInv.Merged.fb_memeq InitECandidate.Solver.Wave8GuestInv.Merged.fb_node_new_ext
theorem «fb_account_has_storage» :
    TerminatingFunBoundedOn GuestInv (ofString "account_has_storage") K.«account_has_storage» := by
  exact InitECandidate.Solver.Wave8GuestInv.S01.fb_account_has_storage_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) InitECandidate.Solver.Wave8GuestInv.Merged.fb_htab_get InitECandidate.Solver.Wave8GuestInv.Merged.fb_record_pre_state_read InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_ws_account_has_storage»
theorem «fb_auth_payload_len» :
    TerminatingFunBoundedOn GuestInv (ofString "auth_payload_len") K.«auth_payload_len» := by
  exact InitECandidate.Solver.Wave8GuestInv.S11.fb_auth_payload_len_of InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_tx_u256_encoded_len» InitECandidate.Solver.Wave8GuestInv.Merged.fb_rlp_word_encoded_len
theorem «fb_cache_get_root» :
    TerminatingFunBoundedOn GuestInv (ofString "cache_get_root") K.«cache_get_root» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_htab_has»
  have h1 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_ws_storage_root_of»
  fb_prove2 842 Guest.Software.guestFn_cache_get_root K.«cache_get_root»

theorem «fb_calculate_blob_gas_price» :
    TerminatingFunBoundedOn GuestInv (ofString "calculate_blob_gas_price") K.«calculate_blob_gas_price» := by
  exact InitECandidate.Solver.Wave8GuestInv.S06.fb_calculate_blob_gas_price_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_taylor_exponential»
theorem «fb_calculate_excess_blob_gas» :
    TerminatingFunBoundedOn GuestInv (ofString "calculate_excess_blob_gas") K.«calculate_excess_blob_gas» := by
  exact InitECandidate.Solver.Wave8Leaves.S13.certified_fb_calculate_excess_blob_gas InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_calculate_blob_gas_price» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_from_word» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_gt» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_mul» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_udiv»
theorem «fb_check_gas_limit» :
    TerminatingFunBoundedOn GuestInv (ofString "check_gas_limit") K.«check_gas_limit» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_udiv»
  fb_prove2 235 Guest.Software.guestFn_check_gas_limit K.«check_gas_limit»

theorem «fb_decode_access_list» :
    TerminatingFunBoundedOn GuestInv (ofString "decode_access_list") K.«decode_access_list» := by
  have h0 := InitECandidate.Solver.Wave8Leaves.Rlp.«fb_alloc»
  have h1 := InitECandidate.Solver.Wave8Leaves.Rlp.«fb_memcpy»
  have h2 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_rlp_item»
  have h3 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_rlp_list_to_slices»
  have h4 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_tx_fixed_bytes»
  have h5 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_tx_list_item»
  fb_prove2 303 Guest.Software.guestFn_decode_access_list K.«decode_access_list»

theorem «fb_decode_authorizations» :
    TerminatingFunBoundedOn GuestInv (ofString "decode_authorizations") K.«decode_authorizations» := by
  have h0 := InitECandidate.Solver.Wave8Leaves.Rlp.«fb_alloc»
  have h1 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_rlp_item»
  have h2 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_rlp_list_to_slices»
  have h3 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_tx_fixed_bytes»
  have h4 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_tx_scalar_u256»
  have h5 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_tx_scalar_word»
  fb_prove2 305 Guest.Software.guestFn_decode_authorizations K.«decode_authorizations»

theorem «fb_decode_blob_hashes» :
    TerminatingFunBoundedOn GuestInv (ofString "decode_blob_hashes") K.«decode_blob_hashes» := by
  have h0 := InitECandidate.Solver.Wave8Leaves.Rlp.«fb_alloc»
  have h1 := InitECandidate.Solver.Wave8Leaves.Rlp.«fb_memcpy»
  have h2 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_rlp_list_to_slices»
  have h3 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_tx_fixed_bytes»
  fb_prove2 304 Guest.Software.guestFn_decode_blob_hashes K.«decode_blob_hashes»

theorem «fb_decode_payload» :
    TerminatingFunBoundedOn GuestInv (ofString "decode_payload") K.«decode_payload» := by
  exact InitECandidate.Solver.Wave8Leaves.S13.certified_fb_decode_payload InitECandidate.Solver.Wave8GuestInv.Merged.fb_alloc InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_ssz_check_offsets» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_ssz_fail» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_ssz_fixed_list_count» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_ssz_split_var_list»
theorem «fb_decode_requests» :
    TerminatingFunBoundedOn GuestInv (ofString "decode_requests") K.«decode_requests» := by
  exact InitECandidate.Solver.Wave8Leaves.S13.certified_fb_decode_requests InitECandidate.Solver.Wave8GuestInv.Merged.fb_alloc InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_ssz_check_offsets» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_ssz_fail» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_ssz_fixed_list_count»
theorem «fb_decode_stateless_input» :
    TerminatingFunBoundedOn GuestInv (ofString "decode_stateless_input") K.«decode_stateless_input» := by
  exact InitECandidate.Solver.Wave8Leaves.S13.certified_fb_decode_stateless_input InitECandidate.Solver.Wave8GuestInv.Merged.fb_alloc InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_decode_bytes_list» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_decode_payload» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_decode_requests» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_ssz_check_offsets» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_ssz_fail» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_ssz_fixed_list_count»
set_option maxHeartbeats 40000000 in
theorem «fb_decode_transaction_rlp» :
    TerminatingFunBoundedOn GuestInv (ofString "decode_transaction_rlp") K.«decode_transaction_rlp» := by
  have h0 := InitECandidate.Solver.Wave8Leaves.Rlp.«fb_alloc»
  have h1 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_decode_access_list»
  have h2 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_decode_authorizations»
  have h3 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_decode_blob_hashes»
  have h4 := InitECandidate.Solver.Wave8Leaves.Rlp.«fb_memzero»
  have h5 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_rlp_decode_fully»
  have h6 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_rlp_list_to_slices»
  have h7 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_tx_bytes_item»
  have h8 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_tx_fixed_bytes»
  have h9 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_tx_list_item»
  have h10 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_tx_scalar_u256»
  have h11 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_tx_scalar_word»
  have h12 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_tx_to_item»
  fb_prove2 306 Guest.Software.guestFn_decode_transaction_rlp K.«decode_transaction_rlp»

end InitECandidate.Solver.Wave8GuestInv.R11Adapters
