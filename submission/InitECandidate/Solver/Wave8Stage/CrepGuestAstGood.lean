import Guest.SoftwareAst

/-!
# Concrete `Guest.Software.guestAst` Syntactic Budget & Freedom Check

Splits `Guest.Software.guestAst.all declGoodS = true` into 9 chunks of ~100 declarations
checked by proof-producing kernel `cbv`, keeping elaboration fast and memory-bounded.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option cbv.maxSteps 100000000
set_option cbv.warning false

namespace InitECandidate.Solver.Wave8Stage.CrepGuestAstGood

open Flapjack

mutual
  def sizeOfShapeS : Shape → Nat
    | .one => 1
    | .comb shapes => sizeOfShapesS shapes
    | .named _ => 1
  termination_by structural shape => shape

  def sizeOfShapesS : List Shape → Nat
    | [] => 0
    | s :: ss => sizeOfShapeS s + sizeOfShapesS ss
  termination_by structural ss => ss
end

mutual
  def shapeFreeS : Shape → Bool
    | .one => true
    | .comb shapes => shapesFreeS shapes
    | .named _ => false
  termination_by structural shape => shape

  def shapesFreeS : List Shape → Bool
    | [] => true
    | s :: ss => shapeFreeS s && shapesFreeS ss
  termination_by structural ss => ss
end

mutual
  def panExpCostS {width : Nat} : (e : Exp (BitVec width)) → Nat
    | .const _ | .var _ _ | .baseAddr | .topAddr | .bytesInWord => 0
    | .rStruct es | .op _ es | .panOp _ es => panExpsCostS es
    | .rField _ e | .load _ e | .load32 e | .loadByte e | .nField _ e => panExpCostS e
    | .nStruct _ fs => panNamedExpsCostS fs
    | .cmp _ a b => panExpCostS a + panExpCostS b + 1
    | .shift _ a b => panExpCostS a + panExpCostS b
  termination_by structural e => e

  def panExpsCostS {width : Nat} : (es : List (Exp (BitVec width))) → Nat
    | [] => 0
    | e :: es => panExpCostS e + panExpsCostS es
  termination_by structural es => es

  def panNamedExpsCostS {width : Nat} : (fs : List (String × Exp (BitVec width))) → Nat
    | [] => 0
    | (_, e) :: fs => panExpCostS e + panNamedExpsCostS fs
  termination_by structural fs => fs
end

mutual
  def expFreeS {width : Nat} : (e : Exp (BitVec width)) → Bool
    | .nStruct _ _ | .nField _ _ => false
    | .rStruct fields => expsFreeS fields
    | .rField _ value => expFreeS value
    | .load shape address => shapeFreeS shape && expFreeS address
    | .loadByte address | .load32 address => expFreeS address
    | .op _ args | .panOp _ args => expsFreeS args
    | .cmp _ left right | .shift _ left right => expFreeS left && expFreeS right
    | .const _ | .var _ _ | .baseAddr | .topAddr | .bytesInWord => true
  termination_by structural e => e

  def expsFreeS {width : Nat} : (es : List (Exp (BitVec width))) → Bool
    | [] => true
    | e :: es => expFreeS e && expsFreeS es
  termination_by structural es => es
end

mutual
  def loadSafeExpS {width : Nat} : (e : Exp (BitVec width)) → Bool
    | .const _ | .var _ _ | .baseAddr | .topAddr | .bytesInWord => true
    | .rStruct es | .op _ es | .panOp _ es => loadSafeExpsS es
    | .rField _ e | .load32 e | .loadByte e | .nField _ e => loadSafeExpS e
    | .load shape e => (decide (sizeOfShapeS shape ≤ 1) || decide (panExpCostS e = 0)) && loadSafeExpS e
    | .nStruct _ fs => loadSafeNamedS fs
    | .cmp _ a b | .shift _ a b => loadSafeExpS a && loadSafeExpS b
  termination_by structural e => e

  def loadSafeExpsS {width : Nat} : (es : List (Exp (BitVec width))) → Bool
    | [] => true
    | e :: es => loadSafeExpS e && loadSafeExpsS es
  termination_by structural es => es

  def loadSafeNamedS {width : Nat} : (fs : List (String × Exp (BitVec width))) → Bool
    | [] => true
    | (_, e) :: fs => loadSafeExpS e && loadSafeNamedS fs
  termination_by structural fs => fs
end

def panProgCostS {width : Nat} : (p : Prog (BitVec width)) → Nat
  | .skip | .break | .continue | .tick | .annot _ _ => 0
  | .assign _ _ e | .return e | .raise _ e | .shMemLoad _ _ _ e => panExpCostS e
  | .primitive _ _ es => panExpsCostS es
  | .store a b | .store32 a b | .storeByte a b | .shMemStore _ a b => panExpCostS a + panExpCostS b
  | .dec _ _ e body => panExpCostS e + panProgCostS body
  | .decCall _ _ _ args body => panExpsCostS args + 3 + panProgCostS body
  | .seq a b => panProgCostS a + panProgCostS b
  | .ite c a b => panExpCostS c + 1 + panProgCostS a + panProgCostS b
  | .while c body => panExpCostS c + 2 + panProgCostS body
  | .extCall _ e1 e2 e3 e4 => panExpCostS e1 + panExpCostS e2 + panExpCostS e3 + panExpCostS e4
  | .call none _ args => panExpsCostS args + 3
  | .call (some (_, none)) _ args => panExpsCostS args + 3
  | .call (some (_, some (_, _, body))) _ args => panExpsCostS args + 3 + panProgCostS body
termination_by structural p => p

def progFreeS {width : Nat} : (p : Prog (BitVec width)) → Bool
  | .skip | .break | .continue | .tick | .annot _ _ => true
  | .assign _ _ e | .return e | .raise _ e | .shMemLoad _ _ _ e => expFreeS e
  | .primitive _ _ es => expsFreeS es
  | .store a b | .store32 a b | .storeByte a b | .shMemStore _ a b => expFreeS a && expFreeS b
  | .dec _ s e body => shapeFreeS s && expFreeS e && progFreeS body
  | .decCall _ s _ args body => shapeFreeS s && expsFreeS args && progFreeS body
  | .seq a b => progFreeS a && progFreeS b
  | .ite c a b => expFreeS c && progFreeS a && progFreeS b
  | .while c body => expFreeS c && progFreeS body
  | .extCall _ e1 e2 e3 e4 => expFreeS e1 && expFreeS e2 && expFreeS e3 && expFreeS e4
  | .call none _ args => expsFreeS args
  | .call (some (_, none)) _ args => expsFreeS args
  | .call (some (_, some (_, _, body))) _ args => expsFreeS args && progFreeS body
termination_by structural p => p

def loadSafeProgS {width : Nat} : (p : Prog (BitVec width)) → Bool
  | .skip | .break | .continue | .tick | .annot _ _ => true
  | .assign _ _ e | .return e | .raise _ e | .shMemLoad _ _ _ e => loadSafeExpS e
  | .primitive _ _ es => loadSafeExpsS es
  | .store a b | .store32 a b | .storeByte a b | .shMemStore _ a b => loadSafeExpS a && loadSafeExpS b
  | .dec _ _ e body => loadSafeExpS e && loadSafeProgS body
  | .decCall _ _ _ args body => loadSafeExpsS args && loadSafeProgS body
  | .seq a b => loadSafeProgS a && loadSafeProgS b
  | .ite c a b => loadSafeExpS c && loadSafeProgS a && loadSafeProgS b
  | .while c body => loadSafeExpS c && loadSafeProgS body
  | .extCall _ e1 e2 e3 e4 => loadSafeExpS e1 && loadSafeExpS e2 && loadSafeExpS e3 && loadSafeExpS e4
  | .call none _ args => loadSafeExpsS args
  | .call (some (_, none)) _ args => loadSafeExpsS args
  | .call (some (_, some (_, _, body))) _ args => loadSafeExpsS args && loadSafeProgS body
termination_by structural p => p

def progNoGlobCallS {width : Nat} : (p : Prog (BitVec width)) → Bool
  | .skip | .break | .continue | .tick | .annot _ _ => true
  | .assign _ _ _ | .return _ | .raise _ _ | .primitive _ _ _ => true
  | .store _ _ | .store32 _ _ | .storeByte _ _ | .shMemStore _ _ _ | .extCall _ _ _ _ _ => true
  | .shMemLoad _ .local _ _ => true
  | .shMemLoad _ .global _ _ => false
  | .dec _ _ _ body | .decCall _ _ _ _ body | .while _ body => progNoGlobCallS body
  | .seq a b | .ite _ a b => progNoGlobCallS a && progNoGlobCallS b
  | .call none _ _ => true
  | .call (some (_, none)) _ _ => true
  | .call (some (none, some (_, _, body))) _ _ => progNoGlobCallS body
  | .call (some (some (.local, _), some (_, _, body))) _ _ => progNoGlobCallS body
  | .call (some (some (.global, _), some _)) _ _ => false
termination_by structural p => p


def declGoodS {width : Nat} : Decl (BitVec width) → Bool
  | .function fn =>
      !fn.inline &&
      ((fn.params.all fun p => shapeFreeS p.2) && progFreeS fn.body && shapeFreeS fn.returnShape) &&
      loadSafeProgS fn.body &&
      progNoGlobCallS fn.body &&
      decide (panProgCostS fn.body ≤ 448)
  | .decl shape _ value =>
      shapeFreeS shape && expFreeS value && loadSafeExpS value && decide (panExpCostS value = 0)
  | .exnDecl _ shape => shapeFreeS shape
  | .name _ _ => false


private def chunk_8 : List (Decl (BitVec 64)) := [Guest.Software.guestFn_kzg_verify, Guest.Software.guestFn_bls_lib_init, Guest.Software.guestFn_bls_g1_add_exec, Guest.Software.guestFn_bls_g1_msm_exec, Guest.Software.guestFn_bls_g2_add_exec, Guest.Software.guestFn_bls_g2_msm_exec, Guest.Software.guestFn_bls_pairing_exec, Guest.Software.guestFn_bls_map_fp_to_g1_exec, Guest.Software.guestFn_bls_map_fp2_to_g2_exec, Guest.Software.guestFn_kzg_point_evaluation_exec, Guest.Software.guestGlobal_bls_discount, Guest.Software.guestFn_bls_precompiles_init, Guest.Software.guestFn_bls_g1_msm_discount, Guest.Software.guestFn_bls_g2_msm_discount, Guest.Software.guestFn_pre_bls_g1_add, Guest.Software.guestFn_pre_bls_g1_msm, Guest.Software.guestFn_pre_bls_g2_add, Guest.Software.guestFn_pre_bls_g2_msm, Guest.Software.guestFn_pre_bls_pairing, Guest.Software.guestFn_pre_bls_map_fp_to_g1, Guest.Software.guestFn_pre_bls_map_fp2_to_g2, Guest.Software.guestFn_pre_kzg_point_evaluation, Guest.Software.guestFn_precompile_index, Guest.Software.guestFn_pre_identity, Guest.Software.guestFn_pre_sha256, Guest.Software.guestFn_pre_ecrecover, Guest.Software.guestFn_pre_ripemd160, Guest.Software.guestFn_pre_blake2f, Guest.Software.guestFn_modexp_gas, Guest.Software.guestFn_pre_modexp, Guest.Software.guestFn_run_precompile, Guest.Software.guestFn_add_to_bloom, Guest.Software.guestFn_logs_bloom, Guest.Software.guestFn_rlp_finish_list, Guest.Software.guestFn_logs_encoded_bound, Guest.Software.guestFn_encode_logs, Guest.Software.guestFn_encode_receipt, Guest.Software.guestFn_withdrawal_rlp_len, Guest.Software.guestFn_encode_withdrawal_rlp, Guest.Software.guestFn_encode_execution_requests, Guest.Software.guestFn_compute_requests_hash, Guest.Software.guestFn_extract_deposit_data, Guest.Software.guestFn_cache_get_root, Guest.Software.guestFn_compute_state_root, Guest.Software.guestExn_Fail, Guest.Software.guestGlobal_be, Guest.Software.guestGlobal_bo, Guest.Software.guestGlobal_precompile_addrs, Guest.Software.guestGlobal_zero32, Guest.Software.guestGlobal_block_hashes, Guest.Software.guestGlobal_block_hashes_n, Guest.Software.guestGlobal_cur_si, Guest.Software.guestGlobal_beacon_roots_address, Guest.Software.guestGlobal_history_storage_address, Guest.Software.guestGlobal_withdrawal_request_address, Guest.Software.guestGlobal_consolidation_request_address, Guest.Software.guestGlobal_builder_deposit_address, Guest.Software.guestGlobal_builder_exit_address, Guest.Software.guestGlobal_deposit_contract_address, Guest.Software.guestGlobal_deposit_event_signature_hash, Guest.Software.guestFn_addr_from_words, Guest.Software.guestFn_fork_init, Guest.Software.guestFn_block_rlp_length, Guest.Software.guestGlobal_wd_rlp_slices, Guest.Software.guestFn_payload_header, Guest.Software.guestFn_tx_is_blob, Guest.Software.guestFn_tx_is_setcode, Guest.Software.guestFn_fee_mul, Guest.Software.guestFn_is_valid_versioned_hashes, Guest.Software.guestFn_te_new, Guest.Software.guestFn_process_unchecked_system_transaction, Guest.Software.guestFn_process_checked_system_transaction, Guest.Software.guestFn_check_transaction, Guest.Software.guestFn_process_transaction, Guest.Software.guestFn_udiv_small5, Guest.Software.guestFn_process_withdrawals, Guest.Software.guestFn_requests_append, Guest.Software.guestFn_process_general_purpose_requests, Guest.Software.guestFn_execute_block, Guest.Software.guestFn_run_attempt, Guest.Software.guestFn_attempt_l1, Guest.Software.guestFn_attempt_l2, Guest.Software.guestFn_attempt_l3, Guest.Software.guestFn_attempt_l4, Guest.Software.guestFn_attempt_l5, Guest.Software.guestFn_attempt_l6, Guest.Software.guestFn_attempt_l7, Guest.Software.guestFn_verify_stateless_new_payload, Guest.Software.guestGlobal_fail_code, Guest.Software.guestFn_main]
private theorem chunkGood_8 : chunk_8.all declGoodS = true := by conv => lhs; cbv
private def chunk_7 : List (Decl (BitVec 64)) := [Guest.Software.guestFn_bls_fp_add_raw, Guest.Software.guestFn_bls_fp_sub_raw, Guest.Software.guestFn_bls_fp_add, Guest.Software.guestFn_bls_fp_sub, Guest.Software.guestFn_bls_fp_neg, Guest.Software.guestFn_bls_fp_dbl, Guest.Software.guestFn_bls_fp_mul, Guest.Software.guestFn_bls_fp_sqr, Guest.Software.guestFn_bls_fp_to_mont, Guest.Software.guestFn_bls_fp_from_mont, Guest.Software.guestFn_bls_fp_shr1, Guest.Software.guestFn_bls_fp_half_can, Guest.Software.guestFn_bls_fp_inv_raw, Guest.Software.guestFn_bls_fp_inv, Guest.Software.guestFn_bls_fp_pow, Guest.Software.guestFn_bls_fp_sgn0, Guest.Software.guestFn_bls_fp_is_high, Guest.Software.guestFn_bls_fp_from_be48, Guest.Software.guestFn_bls_fp_to_be48, Guest.Software.guestFn_bls_fp_decode64, Guest.Software.guestFn_bls_fp_encode64, Guest.Software.guestFn_fp2_copy, Guest.Software.guestFn_fp2_set_zero, Guest.Software.guestFn_fp2_set_one, Guest.Software.guestFn_fp2_is_zero, Guest.Software.guestFn_fp2_eq, Guest.Software.guestFn_fp2_add, Guest.Software.guestFn_fp2_sub, Guest.Software.guestFn_fp2_neg, Guest.Software.guestFn_fp2_dbl, Guest.Software.guestFn_fp2_conj, Guest.Software.guestFn_fp2_mul, Guest.Software.guestFn_fp2_sqr, Guest.Software.guestFn_fp2_mul_xi, Guest.Software.guestFn_fp2_scale, Guest.Software.guestFn_fp2_inv, Guest.Software.guestFn_fp2_pow, Guest.Software.guestFn_fp2_sgn0, Guest.Software.guestFn_fp6_copy, Guest.Software.guestFn_fp6_set_zero, Guest.Software.guestFn_fp6_set_one, Guest.Software.guestFn_fp6_add, Guest.Software.guestFn_fp6_sub, Guest.Software.guestFn_fp6_neg, Guest.Software.guestFn_fp6_mul, Guest.Software.guestFn_fp6_mul_v, Guest.Software.guestFn_fp6_inv, Guest.Software.guestFn_fp12_copy, Guest.Software.guestFn_fp12_set_one, Guest.Software.guestFn_fp12_is_one, Guest.Software.guestFn_fp12_mul, Guest.Software.guestFn_fp12_sqr, Guest.Software.guestFn_fp12_conj, Guest.Software.guestFn_fp12_inv, Guest.Software.guestFn_fp12_frob, Guest.Software.guestFn_fp12_pow_absx, Guest.Software.guestFn_fp12_exp_x, Guest.Software.guestFn_fp12_final_exp, Guest.Software.guestFn_g1_set_inf, Guest.Software.guestFn_g1_is_inf, Guest.Software.guestFn_g1_copy, Guest.Software.guestFn_g1_neg, Guest.Software.guestFn_g1_double, Guest.Software.guestFn_g1_add, Guest.Software.guestFn_g1_mul, Guest.Software.guestFn_g1_normalize, Guest.Software.guestFn_g1_on_curve, Guest.Software.guestFn_g1_decode, Guest.Software.guestFn_g1_encode, Guest.Software.guestFn_g1_subgroup_check, Guest.Software.guestFn_g2_set_inf, Guest.Software.guestFn_g2_is_inf, Guest.Software.guestFn_g2_copy, Guest.Software.guestFn_g2_neg, Guest.Software.guestFn_g2_double, Guest.Software.guestFn_g2_add, Guest.Software.guestFn_g2_mul, Guest.Software.guestFn_g2_normalize, Guest.Software.guestFn_g2_on_curve, Guest.Software.guestFn_g2_decode, Guest.Software.guestFn_g2_encode, Guest.Software.guestFn_g2_subgroup_check, Guest.Software.guestFn_pair_doubling_step, Guest.Software.guestFn_pair_addition_step, Guest.Software.guestFn_pair_ell, Guest.Software.guestFn_pair_miller_loop, Guest.Software.guestFn_pair_accumulate, Guest.Software.guestFn_swu_sqrt_division_fp, Guest.Software.guestFn_swu_g1, Guest.Software.guestFn_iso_horner_fp, Guest.Software.guestFn_iso_map_g1, Guest.Software.guestFn_map_fp_to_g1, Guest.Software.guestFn_swu_sqrt_division_fp2, Guest.Software.guestFn_swu_g2, Guest.Software.guestFn_iso_horner_fp2, Guest.Software.guestFn_iso_map_g2, Guest.Software.guestFn_map_fp2_to_g2, Guest.Software.guestFn_kzg_decompress_g1, Guest.Software.guestFn_kzg_load_g1, Guest.Software.guestFn_kzg_neg_scalar]
private theorem chunkGood_7 : chunk_7.all declGoodS = true := by conv => lhs; cbv
private def chunk_6 : List (Decl (BitVec 64)) := [Guest.Software.guestFn_op_create2, Guest.Software.guestFn_generic_call, Guest.Software.guestFn_calculate_message_call_gas, Guest.Software.guestFn_op_call, Guest.Software.guestFn_op_callcode, Guest.Software.guestFn_op_delegatecall, Guest.Software.guestFn_op_staticcall, Guest.Software.guestFn_process_message_call, Guest.Software.guestGlobal_rmd_tab, Guest.Software.guestGlobal_rmd_x, Guest.Software.guestGlobal_rmd_h, Guest.Software.guestGlobal_rmd_pad, Guest.Software.guestFn_ripemd160_init, Guest.Software.guestFn_rmd_f, Guest.Software.guestFn_rmd_k, Guest.Software.guestFn_rmd_kp, Guest.Software.guestFn_ripemd160_block, Guest.Software.guestFn_ripemd160, Guest.Software.guestGlobal_b2_sigma, Guest.Software.guestGlobal_b2_iv, Guest.Software.guestGlobal_b2_v, Guest.Software.guestFn_blake2_init, Guest.Software.guestFn_blake2_g, Guest.Software.guestFn_blake2b_f, Guest.Software.guestFn_bn_from_be, Guest.Software.guestFn_bn_to_be, Guest.Software.guestFn_bn_mul, Guest.Software.guestFn_bn_divmnu, Guest.Software.guestFn_bn_mod, Guest.Software.guestFn_be_top_bit, Guest.Software.guestFn_modexp, Guest.Software.guestFn_p256_fp_add, Guest.Software.guestFn_p256_fp_sub, Guest.Software.guestFn_p256_fp_reduce, Guest.Software.guestFn_p256_fp_mul, Guest.Software.guestFn_p256_fp_sqr, Guest.Software.guestFn_p256_fp_inv, Guest.Software.guestFn_p256_set_infinity, Guest.Software.guestFn_p256_set_affine, Guest.Software.guestFn_p256_ec_double, Guest.Software.guestFn_p256_ec_add_affine, Guest.Software.guestFn_p256_ec_mul2, Guest.Software.guestFn_p256_ec_to_affine, Guest.Software.guestFn_p256_on_curve, Guest.Software.guestFn_p256_verify, Guest.Software.guestFn_pre_p256verify, Guest.Software.guestGlobal_bn_gamma, Guest.Software.guestGlobal_bn_expw, Guest.Software.guestFn_bn254_init, Guest.Software.guestFn_fq_add, Guest.Software.guestFn_fq_sub, Guest.Software.guestFn_fq_neg, Guest.Software.guestFn_fq_mul, Guest.Software.guestFn_fq_to_mont, Guest.Software.guestFn_fq_from_mont, Guest.Software.guestFn_fq_inv, Guest.Software.guestFn_fq_mul_small, Guest.Software.guestFn_fq2_mul, Guest.Software.guestFn_fq12_reduce, Guest.Software.guestFn_fq12_mul, Guest.Software.guestFn_fq12_sqr, Guest.Software.guestFn_fe_mul, Guest.Software.guestFn_fe_sqr, Guest.Software.guestFn_fe_add, Guest.Software.guestFn_fe_sub, Guest.Software.guestFn_fe_neg, Guest.Software.guestFn_fe_mul_small, Guest.Software.guestFn_fe_is_zero, Guest.Software.guestFn_fe_eq, Guest.Software.guestFn_fe_set_zero, Guest.Software.guestFn_fe_set_one, Guest.Software.guestFn_ecp_set_inf, Guest.Software.guestFn_ecp_is_inf, Guest.Software.guestFn_ecp_double, Guest.Software.guestFn_ecp_add, Guest.Software.guestFn_ecp_mul, Guest.Software.guestFn_ecp_linefunc, Guest.Software.guestFn_fq12_twist, Guest.Software.guestFn_fq12_cast, Guest.Software.guestFn_fq12_frob, Guest.Software.guestFn_fq_poly_deg, Guest.Software.guestFn_fq_poly_submul, Guest.Software.guestFn_fq12_inv, Guest.Software.guestFn_fq12_pow_words, Guest.Software.guestFn_bn254_miller_raw, Guest.Software.guestFn_bn254_pairing, Guest.Software.guestFn_bn254_parse_g1, Guest.Software.guestFn_bn254_parse_g2, Guest.Software.guestFn_bn254_g1_to_bytes, Guest.Software.guestFn_bn254_g1_add, Guest.Software.guestFn_bn254_g1_mul, Guest.Software.guestFn_bn254_pairing_check, Guest.Software.guestFn_pre_alt_bn128_add, Guest.Software.guestFn_pre_alt_bn128_mul, Guest.Software.guestFn_pre_alt_bn128_pairing_check, Guest.Software.guestGlobal_bls_c, Guest.Software.guestFn_bls_consts_init, Guest.Software.guestFn_bls_fp_is_zero, Guest.Software.guestFn_bls_fp_eq, Guest.Software.guestFn_bls_fp_lt_raw]
private theorem chunkGood_6 : chunk_6.all declGoodS = true := by conv => lhs; cbv
private def chunk_5 : List (Decl (BitVec 64)) := [Guest.Software.guestFn_op_clz, Guest.Software.guestFn_op_keccak, Guest.Software.guestFn_op_stop, Guest.Software.guestFn_op_jump, Guest.Software.guestFn_op_jumpi, Guest.Software.guestFn_op_pc, Guest.Software.guestFn_op_gas, Guest.Software.guestFn_op_jumpdest, Guest.Software.guestFn_op_mstore, Guest.Software.guestFn_op_mstore8, Guest.Software.guestFn_op_mload, Guest.Software.guestFn_op_msize, Guest.Software.guestFn_op_mcopy, Guest.Software.guestFn_op_pop, Guest.Software.guestFn_op_push, Guest.Software.guestFn_op_dup, Guest.Software.guestFn_stack_swap_positions, Guest.Software.guestFn_op_swap, Guest.Software.guestFn_code_imm, Guest.Software.guestFn_decode_single, Guest.Software.guestFn_op_dupn, Guest.Software.guestFn_op_swapn, Guest.Software.guestFn_op_exchange, Guest.Software.guestFn_log_append, Guest.Software.guestFn_op_log, Guest.Software.guestFn_is_warm_storage_key, Guest.Software.guestFn_warm_storage_key, Guest.Software.guestFn_op_sload, Guest.Software.guestFn_op_sstore, Guest.Software.guestFn_op_tload, Guest.Software.guestFn_op_tstore, Guest.Software.guestFn_op_address, Guest.Software.guestFn_op_balance, Guest.Software.guestFn_op_origin, Guest.Software.guestFn_op_caller, Guest.Software.guestFn_op_callvalue, Guest.Software.guestFn_op_calldataload, Guest.Software.guestFn_op_calldatasize, Guest.Software.guestFn_copy_from_buffer, Guest.Software.guestFn_op_calldatacopy, Guest.Software.guestFn_op_codesize, Guest.Software.guestFn_op_codecopy, Guest.Software.guestFn_op_gasprice, Guest.Software.guestFn_ext_code_of, Guest.Software.guestFn_op_extcodesize, Guest.Software.guestFn_op_extcodecopy, Guest.Software.guestFn_op_returndatasize, Guest.Software.guestFn_op_returndatacopy, Guest.Software.guestFn_op_extcodehash, Guest.Software.guestFn_op_selfbalance, Guest.Software.guestFn_block_env, Guest.Software.guestFn_op_basefee, Guest.Software.guestFn_op_blobhash, Guest.Software.guestFn_op_blobbasefee, Guest.Software.guestFn_op_blockhash, Guest.Software.guestFn_op_coinbase, Guest.Software.guestFn_op_timestamp, Guest.Software.guestFn_op_number, Guest.Software.guestFn_op_gaslimit, Guest.Software.guestFn_op_chainid, Guest.Software.guestFn_op_prevrandao, Guest.Software.guestFn_op_slotnum, Guest.Software.guestGlobal_cur_cont, Guest.Software.guestGlobal_transfer_topic, Guest.Software.guestGlobal_vm_system_address, Guest.Software.guestGlobal_null_address, Guest.Software.guestFn_evm_init, Guest.Software.guestFn_emit_transfer_log, Guest.Software.guestFn_op_return, Guest.Software.guestFn_op_revert, Guest.Software.guestFn_op_selfdestruct, Guest.Software.guestFn_get_delegated_code_address, Guest.Software.guestFn_recover_authority, Guest.Software.guestFn_calculate_delegation_cost, Guest.Software.guestFn_validate_authorization_checks, Guest.Software.guestFn_set_delegation, Guest.Software.guestFn_prepare_dispatch, Guest.Software.guestFn_op_dispatch, Guest.Software.guestFn_frame_open, Guest.Software.guestFn_frame_exception, Guest.Software.guestFn_frame_prologue, Guest.Software.guestFn_frame_start, Guest.Software.guestFn_frame_epilogue, Guest.Software.guestFn_finish_child, Guest.Software.guestFn_run_frames, Guest.Software.guestFn_start_child, Guest.Software.guestFn_frame_halt, Guest.Software.guestFn_depth0_prepare, Guest.Software.guestFn_process_message, Guest.Software.guestFn_create_finish, Guest.Software.guestFn_process_create_message, Guest.Software.guestFn_incorporate_child_on_error, Guest.Software.guestFn_incorporate_child_on_success, Guest.Software.guestFn_rollback_child_access, Guest.Software.guestFn_child_message, Guest.Software.guestFn_set_retdata, Guest.Software.guestFn_compute_contract_address, Guest.Software.guestFn_compute_create2_contract_address, Guest.Software.guestFn_generic_create, Guest.Software.guestFn_op_create]
private theorem chunkGood_5 : chunk_5.all declGoodS = true := by conv => lhs; cbv
private def chunk_4 : List (Decl (BitVec 64)) := [Guest.Software.guestFn_htab_union_into, Guest.Software.guestFn_merge_tx_into_block, Guest.Software.guestFn_track_ancestor_access, Guest.Software.guestGlobal_bal_accounts, Guest.Software.guestGlobal_bal_index, Guest.Software.guestGlobal_bal_idx_accts, Guest.Software.guestGlobal_bal_idx_stor, Guest.Software.guestGlobal_bal_key_buf, Guest.Software.guestFn_lst_new, Guest.Software.guestFn_lst_new_scratch, Guest.Software.guestFn_lst_push, Guest.Software.guestFn_bal_init, Guest.Software.guestFn_bal_ensure_account, Guest.Software.guestFn_lst_upsert_idx, Guest.Software.guestFn_add_storage_write, Guest.Software.guestFn_add_storage_read, Guest.Software.guestFn_add_balance_change, Guest.Software.guestFn_add_nonce_change, Guest.Software.guestFn_add_code_change, Guest.Software.guestFn_add_touched_account, Guest.Software.guestFn_get_pre_tx_account, Guest.Software.guestFn_get_pre_tx_storage, Guest.Software.guestFn_idx_start_account, Guest.Software.guestFn_idx_start_storage, Guest.Software.guestFn_bal_list_remove_idx, Guest.Software.guestFn_bal_remove_change, Guest.Software.guestFn_remove_storage_write, Guest.Software.guestFn_update_builder_from_tx, Guest.Software.guestFn_incorporate_tx_into_block, Guest.Software.guestFn_bal_sort_gt, Guest.Software.guestFn_sort_elems, Guest.Software.guestFn_sorted_keys32, Guest.Software.guestFn_bal_encode_account, Guest.Software.guestFn_build_block_access_list_rlp, Guest.Software.guestFn_validate_block_access_list_gas_limit, Guest.Software.guestExn_EvmErr, Guest.Software.guestGlobal_ev, Guest.Software.guestGlobal_evm_empty, Guest.Software.guestGlobal_pre_hdr_buf, Guest.Software.guestGlobal_evm_key_buf, Guest.Software.guestFn_sat_word, Guest.Software.guestFn_add_sat, Guest.Software.guestFn_ceil32, Guest.Software.guestFn_words_of, Guest.Software.guestFn_to_address_masked, Guest.Software.guestFn_address_to_u256, Guest.Software.guestFn_is_valid_delegation, Guest.Software.guestFn_check_gas, Guest.Software.guestFn_charge_gas, Guest.Software.guestFn_charge_state_gas, Guest.Software.guestFn_credit_state_gas_refund, Guest.Software.guestFn_frame_state_gas_used, Guest.Software.guestFn_refill_frame_state_gas, Guest.Software.guestFn_stack_pop, Guest.Software.guestFn_stack_push, Guest.Software.guestFn_stack_push_word, Guest.Software.guestFn_stack_push_bool, Guest.Software.guestFn_memory_gas_cost, Guest.Software.guestFn_extend_memory_cost1, Guest.Software.guestFn_extend_memory_cost2, Guest.Software.guestFn_extend_memory, Guest.Software.guestFn_charge_with_memory, Guest.Software.guestFn_buffer_read, Guest.Software.guestFn_compute_jumpdests, Guest.Software.guestFn_is_valid_jumpdest, Guest.Software.guestFn_msg_new, Guest.Software.guestFn_msg_new_scratch, Guest.Software.guestFn_frame_new, Guest.Software.guestFn_pc_add, Guest.Software.guestFn_cur_msg, Guest.Software.guestFn_require_not_static, Guest.Software.guestFn_is_warm_address, Guest.Software.guestFn_warm_address, Guest.Software.guestFn_access_gas_cost, Guest.Software.guestFn_warm_after_charge, Guest.Software.guestFn_op_add, Guest.Software.guestFn_op_mul, Guest.Software.guestFn_op_sub, Guest.Software.guestFn_op_div, Guest.Software.guestFn_op_sdiv, Guest.Software.guestFn_op_mod, Guest.Software.guestFn_op_smod, Guest.Software.guestFn_op_addmod, Guest.Software.guestFn_op_mulmod, Guest.Software.guestFn_op_exp, Guest.Software.guestFn_op_signextend, Guest.Software.guestFn_op_lt, Guest.Software.guestFn_op_gt, Guest.Software.guestFn_op_slt, Guest.Software.guestFn_op_sgt, Guest.Software.guestFn_op_eq, Guest.Software.guestFn_op_iszero, Guest.Software.guestFn_op_and, Guest.Software.guestFn_op_or, Guest.Software.guestFn_op_xor, Guest.Software.guestFn_op_not, Guest.Software.guestFn_op_byte, Guest.Software.guestFn_op_shl, Guest.Software.guestFn_op_shr, Guest.Software.guestFn_op_sar]
private theorem chunkGood_4 : chunk_4.all declGoodS = true := by conv => lhs; cbv
private def chunk_3 : List (Decl (BitVec 64)) := [Guest.Software.guestFn_tx_fixed_bytes, Guest.Software.guestFn_tx_to_item, Guest.Software.guestFn_tx_list_item, Guest.Software.guestFn_decode_access_list, Guest.Software.guestFn_decode_blob_hashes, Guest.Software.guestFn_decode_authorizations, Guest.Software.guestFn_decode_transaction_rlp, Guest.Software.guestFn_decode_transaction, Guest.Software.guestFn_tx_gas, Guest.Software.guestFn_tx_nonce, Guest.Software.guestFn_tx_to, Guest.Software.guestFn_tx_value, Guest.Software.guestFn_tx_data, Guest.Software.guestFn_tx_r, Guest.Software.guestFn_tx_s, Guest.Software.guestFn_tx_has_access_list, Guest.Software.guestFn_tx_blob_count, Guest.Software.guestFn_calculate_total_blob_gas, Guest.Software.guestFn_tx_put_u256, Guest.Software.guestFn_tx_u256_encoded_len, Guest.Software.guestFn_tx_put_to, Guest.Software.guestFn_access_list_payload_len, Guest.Software.guestFn_tx_put_access_list, Guest.Software.guestFn_tx_put_blob_hashes, Guest.Software.guestFn_auth_payload_len, Guest.Software.guestFn_auth_list_payload_len, Guest.Software.guestFn_tx_put_authorizations, Guest.Software.guestFn_tx_encode_bound, Guest.Software.guestFn_tx_encode_generic, Guest.Software.guestFn_encode_transaction, Guest.Software.guestFn_get_transaction_hash, Guest.Software.guestFn_tx_signing_hash_mode, Guest.Software.guestFn_signing_hash_pre155, Guest.Software.guestFn_signing_hash_155, Guest.Software.guestFn_signing_hash_2930, Guest.Software.guestFn_signing_hash_1559, Guest.Software.guestFn_signing_hash_4844, Guest.Software.guestFn_signing_hash_7702, Guest.Software.guestFn_tx_chain_id, Guest.Software.guestFn_signature_recovery_parameters, Guest.Software.guestFn_recover_transaction_public_key, Guest.Software.guestFn_sender_address_from_public_key, Guest.Software.guestFn_recover_sender, Guest.Software.guestFn_recover_sender_with_chain_id, Guest.Software.guestFn_count_tokens_in_data, Guest.Software.guestFn_calculate_intrinsic_cost, Guest.Software.guestFn_validate_transaction, Guest.Software.guestExn_StateErr, Guest.Software.guestGlobal_ws, Guest.Software.guestGlobal_bs, Guest.Software.guestGlobal_ts, Guest.Software.guestGlobal_sk_buf, Guest.Software.guestGlobal_journal, Guest.Software.guestGlobal_journal_cap, Guest.Software.guestFn_state_init, Guest.Software.guestFn_state_fresh_tx, Guest.Software.guestFn_jset, Guest.Software.guestFn_jdel, Guest.Software.guestFn_state_snapshot, Guest.Software.guestFn_state_restore, Guest.Software.guestFn_sk_make, Guest.Software.guestFn_acct_new, Guest.Software.guestFn_acct_empty, Guest.Software.guestFn_acct_copy, Guest.Software.guestFn_record_pre_state_read, Guest.Software.guestFn_ws_account_leaf, Guest.Software.guestFn_ws_get_account_optional, Guest.Software.guestFn_ws_storage_root_of, Guest.Software.guestFn_ws_storage_trie, Guest.Software.guestFn_ws_get_storage, Guest.Software.guestFn_ws_get_code, Guest.Software.guestFn_ws_account_has_storage, Guest.Software.guestFn_get_pre_state_account_optional, Guest.Software.guestFn_get_pre_state_account, Guest.Software.guestFn_get_account_optional, Guest.Software.guestFn_get_account, Guest.Software.guestFn_get_code, Guest.Software.guestFn_stor_lookup, Guest.Software.guestFn_get_storage, Guest.Software.guestFn_get_storage_original, Guest.Software.guestFn_get_transient_storage, Guest.Software.guestFn_account_exists, Guest.Software.guestFn_account_has_storage, Guest.Software.guestFn_account_deployable, Guest.Software.guestFn_acct_is_empty, Guest.Software.guestFn_account_exists_and_is_empty, Guest.Software.guestFn_is_account_alive, Guest.Software.guestFn_set_account, Guest.Software.guestFn_set_storage, Guest.Software.guestFn_destroy_storage, Guest.Software.guestFn_destroy_account, Guest.Software.guestFn_modify_state_commit, Guest.Software.guestFn_clear_account_preserving_balance, Guest.Software.guestFn_mark_account_created, Guest.Software.guestFn_set_transient_storage, Guest.Software.guestFn_move_ether, Guest.Software.guestFn_create_ether, Guest.Software.guestFn_set_account_balance, Guest.Software.guestFn_increment_nonce, Guest.Software.guestFn_set_code]
private theorem chunkGood_3 : chunk_3.all declGoodS = true := by conv => lhs; cbv
private def chunk_2 : List (Decl (BitVec 64)) := [Guest.Software.guestFn_decode_host_input, Guest.Software.guestFn_ssz_check_offsets, Guest.Software.guestFn_ssz_split_var_list, Guest.Software.guestFn_ssz_fixed_list_count, Guest.Software.guestFn_decode_payload, Guest.Software.guestFn_decode_requests, Guest.Software.guestFn_decode_bytes_list, Guest.Software.guestFn_decode_stateless_input, Guest.Software.guestFn_htr_withdrawal, Guest.Software.guestFn_htr_list_roots, Guest.Software.guestFn_htr_payload, Guest.Software.guestFn_htr_deposit, Guest.Software.guestFn_htr_wdreq, Guest.Software.guestFn_htr_cons, Guest.Software.guestFn_htr_bdep, Guest.Software.guestFn_htr_bexit, Guest.Software.guestFn_htr_request_list, Guest.Software.guestFn_htr_requests, Guest.Software.guestFn_htr_new_payload_request, Guest.Software.guestFn_serialize_result, Guest.Software.guestExn_HdrErr, Guest.Software.guestExn_BlockErr, Guest.Software.guestFn_hdr_uint_field, Guest.Software.guestFn_hdr_word_field, Guest.Software.guestFn_hdr_u256_field, Guest.Software.guestFn_hdr_bytes_field, Guest.Software.guestFn_hdr_raw_field, Guest.Software.guestFn_decode_header, Guest.Software.guestFn_rlp_put_u256, Guest.Software.guestFn_encode_header, Guest.Software.guestFn_header_hash, Guest.Software.guestFn_validate_headers, Guest.Software.guestFn_taylor_exponential, Guest.Software.guestFn_calculate_blob_gas_price, Guest.Software.guestFn_calculate_excess_blob_gas, Guest.Software.guestFn_check_gas_limit, Guest.Software.guestFn_calculate_base_fee_per_gas, Guest.Software.guestGlobal_hdr_zero8, Guest.Software.guestFn_header_init, Guest.Software.guestFn_validate_header, Guest.Software.guestExn_MptErr, Guest.Software.guestGlobal_empty_trie_root, Guest.Software.guestGlobal_empty_code_hash, Guest.Software.guestGlobal_mpt_nib_scratch, Guest.Software.guestGlobal_mpt_hash_scratch, Guest.Software.guestGlobal_mpt_key_scratch, Guest.Software.guestFn_mpt_fail, Guest.Software.guestFn_mpt_init, Guest.Software.guestFn_key_to_nibbles, Guest.Software.guestFn_compact_to_nibbles, Guest.Software.guestFn_nibble_list_to_compact, Guest.Software.guestFn_common_prefix_length, Guest.Software.guestFn_nibbles_concat, Guest.Software.guestFn_nodedb_build, Guest.Software.guestFn_nodedb_lookup, Guest.Software.guestFn_node_new_hashed, Guest.Software.guestFn_node_new_leaf, Guest.Software.guestFn_node_new_ext, Guest.Software.guestFn_node_new_branch, Guest.Software.guestFn_node_invalidate, Guest.Software.guestFn__resolve_step, Guest.Software.guestFn__decode_step, Guest.Software.guestFn__decode_witness_node_body, Guest.Software.guestFn__decode_witness_node_mpt, Guest.Software.guestFn__decode_witness_node, Guest.Software.guestFn_decode_witness_to_mpt, Guest.Software.guestFn_trie_walk, Guest.Software.guestFn_trie_lookup, Guest.Software.guestFn_mpt_new, Guest.Software.guestFn_mpt_from_witness, Guest.Software.guestFn_mpt_nibble_key, Guest.Software.guestFn_mpt_get, Guest.Software.guestFn__create_branch_from_two_leaves, Guest.Software.guestFn__insert_into_leaf, Guest.Software.guestFn__split_extension, Guest.Software.guestFn__mpt_insert_node, Guest.Software.guestFn__collapse_branch, Guest.Software.guestFn__delete_ext_finish, Guest.Software.guestFn__mpt_delete_node_body, Guest.Software.guestFn__mpt_delete_node, Guest.Software.guestFn_mpt_set, Guest.Software.guestFn__node_rlp_begin, Guest.Software.guestFn__node_rlp_finish, Guest.Software.guestFn__node_needs_rlp, Guest.Software.guestFn__node_rlp_fill, Guest.Software.guestFn_node_rlp, Guest.Software.guestFn_rlp_value_encoded_len, Guest.Software.guestFn_node_ref_len, Guest.Software.guestFn_node_hash_cached, Guest.Software.guestFn_node_write_ref, Guest.Software.guestFn_node_hash, Guest.Software.guestFn_mpt_root, Guest.Software.guestFn_build_mpt_indexed, Guest.Software.guestFn_decode_account_from_leaf, Guest.Software.guestFn_encode_account, Guest.Software.guestExn_TxErr, Guest.Software.guestFn_tx_scalar_item, Guest.Software.guestFn_tx_scalar_u256, Guest.Software.guestFn_tx_scalar_word, Guest.Software.guestFn_tx_bytes_item]
private theorem chunkGood_2 : chunk_2.all declGoodS = true := by conv => lhs; cbv
private def chunk_1 : List (Decl (BitVec 64)) := [Guest.Software.guestFn_keccak_init, Guest.Software.guestFn_keccak_f1600, Guest.Software.guestFn_keccak_absorb_block, Guest.Software.guestFn_keccak256, Guest.Software.guestExn_RlpErr, Guest.Software.guestFn_rlp_fail, Guest.Software.guestFn_rlp_read_length, Guest.Software.guestFn_rlp_item, Guest.Software.guestFn_rlp_decode_fully, Guest.Software.guestFn_rlp_item_header, Guest.Software.guestFn__rlp_validate_items_body, Guest.Software.guestFn_rlp_validate_items, Guest.Software.guestFn_rlp_item_total, Guest.Software.guestFn_rlp_list_count, Guest.Software.guestFn_rlp_item_total_unchecked, Guest.Software.guestFn_rlp_list_to_slices, Guest.Software.guestFn_rlp_bytes_to_word, Guest.Software.guestFn_rlp_check_uint_bytes, Guest.Software.guestFn_rlp_be_len, Guest.Software.guestFn_rlp_put_be, Guest.Software.guestFn_rlp_write_header, Guest.Software.guestFn_rlp_header_len, Guest.Software.guestFn_rlp_encode_bytes, Guest.Software.guestFn_rlp_encode_word, Guest.Software.guestFn_rlp_encode_list_header, Guest.Software.guestFn_rlp_bytes_encoded_len, Guest.Software.guestFn_rlp_list_header_len, Guest.Software.guestFn_rlp_word_encoded_len, Guest.Software.guestFn_htab_new, Guest.Software.guestFn_htab_new_scratch, Guest.Software.guestFn_htab_first_diff, Guest.Software.guestFn_htab_find_leaf, Guest.Software.guestFn_htab_get, Guest.Software.guestFn_htab_has, Guest.Software.guestFn_htab_new_node, Guest.Software.guestFn_htab_new_leaf, Guest.Software.guestFn_htab_new_internal, Guest.Software.guestFn_htab_grow, Guest.Software.guestFn_htab_set, Guest.Software.guestFn_htab_del, Guest.Software.guestFn_htab_truncate, Guest.Software.guestFn_htab_count, Guest.Software.guestFn_htab_cap, Guest.Software.guestFn_htab_item, Guest.Software.guestFn_htab_keys, Guest.Software.guestFn_htab_copy, Guest.Software.guestFn_htab_copy_scratch, Guest.Software.guestGlobal_secp_accel_scratch, Guest.Software.guestFn_secp256k1_init, Guest.Software.guestFn_fp_add, Guest.Software.guestFn_fp_sub, Guest.Software.guestFn_fp_neg, Guest.Software.guestFn_fp_reduce, Guest.Software.guestFn_fp_mul, Guest.Software.guestFn_fp_sqr, Guest.Software.guestFn_fp_pow, Guest.Software.guestFn_fp_inv_fermat, Guest.Software.guestFn_modinv_bin, Guest.Software.guestFn_mod_half, Guest.Software.guestFn_mod_sub, Guest.Software.guestFn_fp_inv, Guest.Software.guestFn_fp_sqrt, Guest.Software.guestFn_fn_mul, Guest.Software.guestFn_fn_add, Guest.Software.guestFn_fn_pow, Guest.Software.guestFn_fn_inv_fermat, Guest.Software.guestFn_fn_inv, Guest.Software.guestFn_ec_set_infinity, Guest.Software.guestFn_ec_set_affine, Guest.Software.guestFn_ec_is_infinity, Guest.Software.guestFn_ec_double, Guest.Software.guestFn_ec_add_affine, Guest.Software.guestFn_ec_add, Guest.Software.guestFn_ec_mul, Guest.Software.guestFn_ec_mul2, Guest.Software.guestFn_ec_to_affine, Guest.Software.guestFn_ec_on_curve, Guest.Software.guestFn_secp256k1_decompress_r, Guest.Software.guestFn_secp256k1_recover, Guest.Software.guestFn_secp256k1_address_of_point, Guest.Software.guestFn_secp256k1_ecrecover, Guest.Software.guestExn_SszErr, Guest.Software.guestGlobal_zero_hashes, Guest.Software.guestGlobal_ssz_len_chunk, Guest.Software.guestGlobal_ssz_offs, Guest.Software.guestFn_ssz_init, Guest.Software.guestFn_merkleize, Guest.Software.guestFn_mix_in_length, Guest.Software.guestFn_merkleize_progressive, Guest.Software.guestFn_htr_plist_chunks, Guest.Software.guestFn_htr_pbytes, Guest.Software.guestFn_htr_pcontainer, Guest.Software.guestFn_pack_bytes, Guest.Software.guestFn_htr_bytes_vector, Guest.Software.guestFn_htr_bytes_list, Guest.Software.guestFn_htr_u64_at, Guest.Software.guestFn_ssz_fail, Guest.Software.guestFn_host_input_byte, Guest.Software.guestFn_host_input_le32, Guest.Software.guestFn_precheck_host_ssz_header]
private theorem chunkGood_1 : chunk_1.all declGoodS = true := by conv => lhs; cbv
private def chunk_0 : List (Decl (BitVec 64)) := [Guest.Software.guestGlobal_heap_ptr, Guest.Software.guestGlobal_journal_n, Guest.Software.guestExn_TrapErr, Guest.Software.guestFn_trap_with, Guest.Software.guestGlobal_scratch_ptr, Guest.Software.guestGlobal_frame_mem_ptr, Guest.Software.guestFn_mem_init, Guest.Software.guestFn_alloc, Guest.Software.guestFn_heap_mark, Guest.Software.guestFn_heap_release, Guest.Software.guestFn_frame_mem_alloc, Guest.Software.guestFn_frame_mem_mark, Guest.Software.guestFn_frame_mem_release, Guest.Software.guestFn_scratch_alloc, Guest.Software.guestFn_scratch_mark, Guest.Software.guestFn_scratch_release, Guest.Software.guestFn_memcpy, Guest.Software.guestFn_memzero, Guest.Software.guestFn_memeq, Guest.Software.guestFn_is_zero_bytes, Guest.Software.guestFn_ld_le32, Guest.Software.guestFn_ld_le64, Guest.Software.guestFn_ld_be32, Guest.Software.guestFn_bswap64, Guest.Software.guestFn_ld_be64, Guest.Software.guestFn_st_le32, Guest.Software.guestFn_st_le64, Guest.Software.guestFn_st_be32, Guest.Software.guestFn_st_be64, Guest.Software.guestFn_input_blob, Guest.Software.guestFn_output_write, Guest.Software.guestFn_min, Guest.Software.guestFn_max, Guest.Software.guestFn_udivmod, Guest.Software.guestFn_udiv, Guest.Software.guestFn_umod, Guest.Software.guestFn_ceil_log2, Guest.Software.guestGlobal_u256_ws, Guest.Software.guestFn_u256_ws_init, Guest.Software.guestFn_u256_from_word, Guest.Software.guestFn_u256_low, Guest.Software.guestFn_u256_fits_word, Guest.Software.guestFn_u256_is_zero, Guest.Software.guestFn_u256_limb, Guest.Software.guestFn_u256_bit, Guest.Software.guestFn_u256_eq, Guest.Software.guestFn_u256_lt, Guest.Software.guestFn_u256_gt, Guest.Software.guestFn_u256_slt, Guest.Software.guestFn_u256_sgt, Guest.Software.guestFn_u256_cmp, Guest.Software.guestFn_u256_not, Guest.Software.guestFn_u256_and, Guest.Software.guestFn_u256_or, Guest.Software.guestFn_u256_xor, Guest.Software.guestFn_u256_add_carry, Guest.Software.guestFn_u256_add, Guest.Software.guestFn_u256_sub, Guest.Software.guestFn_u256_neg, Guest.Software.guestFn_mul64x64, Guest.Software.guestFn_u256_mul, Guest.Software.guestFn_u256_mul_full, Guest.Software.guestFn_nlz32, Guest.Software.guestFn_div64by32, Guest.Software.guestFn_u256_to_digits, Guest.Software.guestFn_digits_to_u256, Guest.Software.guestFn_digits_len, Guest.Software.guestFn_divmnu, Guest.Software.guestFn_digits_divmod, Guest.Software.guestFn_u256_divmod, Guest.Software.guestFn_u256_div, Guest.Software.guestFn_u256_mod, Guest.Software.guestFn_u256_abs, Guest.Software.guestFn_u256_sdiv, Guest.Software.guestFn_u256_smod, Guest.Software.guestFn_u256_addmod, Guest.Software.guestFn_u256_mulmod, Guest.Software.guestFn_bit_length64, Guest.Software.guestFn_u256_bit_length, Guest.Software.guestFn_u256_byte_length, Guest.Software.guestFn_u256_exp, Guest.Software.guestFn_u256_shl, Guest.Software.guestFn_u256_shr, Guest.Software.guestFn_u256_sar, Guest.Software.guestFn_u256_signextend, Guest.Software.guestFn_u256_byte, Guest.Software.guestFn_u256_from_be, Guest.Software.guestFn_u256_to_be32, Guest.Software.guestFn_u256_to_be_min, Guest.Software.guestGlobal_sha_st, Guest.Software.guestGlobal_sha_pad, Guest.Software.guestFn_sha256_init, Guest.Software.guestFn_sha256_state_init, Guest.Software.guestFn_sha256_block, Guest.Software.guestFn_sha256_finish, Guest.Software.guestFn_sha256, Guest.Software.guestFn_sha256_pair, Guest.Software.guestGlobal_keccak_rc, Guest.Software.guestGlobal_keccak_st, Guest.Software.guestGlobal_keccak_pad]
private theorem chunkGood_0 : chunk_0.all declGoodS = true := by conv => lhs; cbv
private def tail_8 : List (Decl (BitVec 64)) := chunk_8
private theorem tailGood_8 : tail_8.all declGoodS = true := chunkGood_8
private def tail_7 : List (Decl (BitVec 64)) := chunk_7 ++ tail_8
private theorem tailGood_7 : tail_7.all declGoodS = true := by rw [tail_7, List.all_append, chunkGood_7, tailGood_8]; rfl
private def tail_6 : List (Decl (BitVec 64)) := chunk_6 ++ tail_7
private theorem tailGood_6 : tail_6.all declGoodS = true := by rw [tail_6, List.all_append, chunkGood_6, tailGood_7]; rfl
private def tail_5 : List (Decl (BitVec 64)) := chunk_5 ++ tail_6
private theorem tailGood_5 : tail_5.all declGoodS = true := by rw [tail_5, List.all_append, chunkGood_5, tailGood_6]; rfl
private def tail_4 : List (Decl (BitVec 64)) := chunk_4 ++ tail_5
private theorem tailGood_4 : tail_4.all declGoodS = true := by rw [tail_4, List.all_append, chunkGood_4, tailGood_5]; rfl
private def tail_3 : List (Decl (BitVec 64)) := chunk_3 ++ tail_4
private theorem tailGood_3 : tail_3.all declGoodS = true := by rw [tail_3, List.all_append, chunkGood_3, tailGood_4]; rfl
private def tail_2 : List (Decl (BitVec 64)) := chunk_2 ++ tail_3
private theorem tailGood_2 : tail_2.all declGoodS = true := by rw [tail_2, List.all_append, chunkGood_2, tailGood_3]; rfl
private def tail_1 : List (Decl (BitVec 64)) := chunk_1 ++ tail_2
private theorem tailGood_1 : tail_1.all declGoodS = true := by rw [tail_1, List.all_append, chunkGood_1, tailGood_2]; rfl
private def tail_0 : List (Decl (BitVec 64)) := chunk_0 ++ tail_1
private theorem tailGood_0 : tail_0.all declGoodS = true := by rw [tail_0, List.all_append, chunkGood_0, tailGood_1]; rfl

theorem guestAst_all_declGoodS : Guest.Software.guestAst.all declGoodS = true := tailGood_0

end InitECandidate.Solver.Wave8Stage.CrepGuestAstGood
