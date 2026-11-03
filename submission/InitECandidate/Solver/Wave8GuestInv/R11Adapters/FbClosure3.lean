import InitECandidate.Solver.Wave8GuestInv.R11Adapters.FbClosure2

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

theorem «fb_encode_header» :
    TerminatingFunBoundedOn GuestInv (ofString "encode_header") K.«encode_header» := by
  exact InitECandidate.Solver.Wave8Leaves.S13.certified_fb_encode_header InitECandidate.Solver.Wave8GuestInv.Merged.fb_alloc InitECandidate.Solver.Wave8GuestInv.Merged.fb_rlp_encode_bytes InitECandidate.Solver.Wave8GuestInv.Merged.fb_rlp_encode_list_header InitECandidate.Solver.Wave8GuestInv.Merged.fb_rlp_encode_word InitECandidate.Solver.Wave8GuestInv.Merged.fb_rlp_list_header_len InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_rlp_put_u256»
theorem «fb_extract_deposit_data» :
    TerminatingFunBoundedOn GuestInv (ofString "extract_deposit_data") K.«extract_deposit_data» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_mark»
  have h1 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_release»
  have h2 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_is_zero_bytes»
  have h3 := InitECandidate.Solver.Wave8Leaves.Rlp.«fb_ld_be64»
  have h4 := InitECandidate.Solver.Wave8Leaves.Rlp.«fb_memcpy»
  fb_prove2 841 Guest.Software.guestFn_extract_deposit_data K.«extract_deposit_data»

theorem «fb_get_code» :
    TerminatingFunBoundedOn GuestInv (ofString "get_code") K.«get_code» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_htab_get»
  have h1 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_htab_set»
  have h2 := InitECandidate.Solver.Wave8Leaves.Rlp.«fb_memeq»
  have h3 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_sk_make»
  have h4 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_ws_get_code»
  fb_prove2 376 Guest.Software.guestFn_get_code K.«get_code»

theorem «fb_hdr_u256_field» :
    TerminatingFunBoundedOn GuestInv (ofString "hdr_u256_field") K.«hdr_u256_field» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_hdr_uint_field»
  have h1 := InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees.«fb_u256_from_be»
  fb_prove2 224 Guest.Software.guestFn_hdr_u256_field K.«hdr_u256_field»

theorem «fb_header_hash» :
    TerminatingFunBoundedOn GuestInv (ofString "header_hash") K.«header_hash» := by
  exact InitECandidate.Solver.Wave8Leaves.S13.certified_fb_header_hash InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_encode_header» InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_mark» InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_release» InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_keccak256»
theorem «fb_htr_bytes_list» :
    TerminatingFunBoundedOn GuestInv (ofString "htr_bytes_list") K.«htr_bytes_list» := by
  exact InitECandidate.Solver.Wave8GuestInv.S14.fb_htr_bytes_list_of InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_mark» InitECandidate.Solver.Wave8GuestInv.Merged.fb_pack_bytes InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_merkleize» InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_release» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_mix_in_length»
theorem «fb_htr_bytes_vector» :
    TerminatingFunBoundedOn GuestInv (ofString "htr_bytes_vector") K.«htr_bytes_vector» := by
  exact InitECandidate.Solver.Wave8GuestInv.S14.fb_htr_bytes_vector_of InitECandidate.Solver.Wave8GuestInv.Merged.fb_memzero InitECandidate.Solver.Wave8GuestInv.Merged.fb_memcpy InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_mark» InitECandidate.Solver.Wave8GuestInv.Merged.fb_pack_bytes InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_merkleize» InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_release»
theorem «fb_htr_cons» :
    TerminatingFunBoundedOn GuestInv (ofString "htr_cons") K.«htr_cons» := by
  exact InitECandidate.Solver.Wave8GuestInv.S14.fb_htr_cons_of InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_mark» InitECandidate.Solver.Wave8GuestInv.Merged.fb_alloc InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_htr_bytes_vector» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_merkleize» InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_release»
theorem «fb_htr_deposit» :
    TerminatingFunBoundedOn GuestInv (ofString "htr_deposit") K.«htr_deposit» := by
  exact InitECandidate.Solver.Wave8GuestInv.S14.fb_htr_deposit_of InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_mark» InitECandidate.Solver.Wave8GuestInv.Merged.fb_alloc InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_htr_bytes_vector» InitECandidate.Solver.Wave8GuestInv.Merged.fb_memcpy InitECandidate.Solver.Wave8GuestInv.Merged.fb_htr_u64_at InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_merkleize» InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_release»
theorem «fb_htr_pcontainer» :
    TerminatingFunBoundedOn GuestInv (ofString "htr_pcontainer") K.«htr_pcontainer» := by
  exact InitECandidate.Solver.Wave8GuestInv.S14.fb_htr_pcontainer_of InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_mark» InitECandidate.Solver.Wave8GuestInv.Merged.fb_alloc InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_merkleize_progressive» InitECandidate.Solver.Wave8GuestInv.Merged.fb_memzero InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_sha256_pair» InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_release»
theorem «fb_htr_plist_chunks» :
    TerminatingFunBoundedOn GuestInv (ofString "htr_plist_chunks") K.«htr_plist_chunks» := by
  exact InitECandidate.Solver.Wave8GuestInv.S14.fb_htr_plist_chunks_of InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_merkleize_progressive» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_mix_in_length»
theorem «fb_htr_wdreq» :
    TerminatingFunBoundedOn GuestInv (ofString "htr_wdreq") K.«htr_wdreq» := by
  exact InitECandidate.Solver.Wave8GuestInv.S14.fb_htr_wdreq_of InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_mark» InitECandidate.Solver.Wave8GuestInv.Merged.fb_alloc InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_htr_bytes_vector» InitECandidate.Solver.Wave8GuestInv.Merged.fb_htr_u64_at InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_merkleize» InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_release»
theorem «fb_htr_withdrawal» :
    TerminatingFunBoundedOn GuestInv (ofString "htr_withdrawal") K.«htr_withdrawal» := by
  exact InitECandidate.Solver.Wave8GuestInv.S14.fb_htr_withdrawal_of InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_mark» InitECandidate.Solver.Wave8GuestInv.Merged.fb_alloc InitECandidate.Solver.Wave8GuestInv.Merged.fb_htr_u64_at InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_htr_bytes_vector» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_merkleize» InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_release»
theorem «fb_op_blobbasefee» :
    TerminatingFunBoundedOn GuestInv (ofString "op_blobbasefee") K.«op_blobbasefee» := by
  exact InitECandidate.Solver.Wave8GuestInv.S06.fb_op_blobbasefee_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) InitECandidate.Solver.Wave8GuestInv.Merged.fb_charge_gas InitECandidate.Solver.Wave8GuestInv.Merged.fb_block_env InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_calculate_blob_gas_price» InitECandidate.Solver.Wave8GuestInv.Merged.fb_stack_push InitECandidate.Solver.Wave8GuestInv.Merged.fb_pc_add
theorem «fb_op_mul» :
    TerminatingFunBoundedOn GuestInv (ofString "op_mul") K.«op_mul» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_charge_gas»
  have h1 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_pc_add
  have h2 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_stack_pop
  have h3 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_stack_push»
  have h4 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_mul»
  fb_prove2 476 Guest.Software.guestFn_op_mul K.«op_mul»

theorem «fb_op_selfdestruct» :
    TerminatingFunBoundedOn GuestInv (ofString "op_selfdestruct") K.«op_selfdestruct» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_charge_gas»
  have h1 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_charge_state_gas
  have h2 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_emit_transfer_log»
  have h3 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_get_account»
  have h4 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_htab_has»
  have h5 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_htab_set»
  have h6 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_is_account_alive»
  have h7 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_is_warm_address
  have h8 := InitECandidate.Solver.Wave8Leaves.Rlp.«fb_memeq»
  have h9 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_move_ether»
  have h10 := InitECandidate.Solver.Wave8Leaves.S08.«fb_require_not_static»
  have h11 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_stack_pop
  have h12 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_to_address_masked
  have h13 := InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees.fb_u256_is_zero
  have h14 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_warm_address
  fb_prove2 570 Guest.Software.guestFn_op_selfdestruct K.«op_selfdestruct»

theorem «fb_op_shr» :
    TerminatingFunBoundedOn GuestInv (ofString "op_shr") K.«op_shr» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_charge_gas»
  have h1 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_pc_add
  have h2 := InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees.«fb_sat_word»
  have h3 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_stack_pop
  have h4 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_stack_push»
  have h5 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_shr»
  fb_prove2 498 Guest.Software.guestFn_op_shr K.«op_shr»

theorem «fb_op_slt» :
    TerminatingFunBoundedOn GuestInv (ofString "op_slt") K.«op_slt» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_charge_gas»
  have h1 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_pc_add
  have h2 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_stack_pop
  have h3 := InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees.«fb_stack_push_bool»
  have h4 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_slt»
  fb_prove2 488 Guest.Software.guestFn_op_slt K.«op_slt»

theorem «fb_precheck_host_ssz_header» :
    TerminatingFunBoundedOn GuestInv (ofString "precheck_host_ssz_header") K.«precheck_host_ssz_header» := by
  exact InitECandidate.Solver.Wave8Leaves.S13.certified_fb_precheck_host_ssz_header InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_host_input_byte» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_host_input_le32» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_ssz_check_offsets» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_ssz_fail»
theorem «fb_u256_abs» :
    TerminatingFunBoundedOn GuestInv (ofString "u256_abs") K.«u256_abs» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_neg»
  fb_prove2 72 Guest.Software.guestFn_u256_abs K.«u256_abs»

theorem «fb_u256_bit» :
    TerminatingFunBoundedOn GuestInv (ofString "u256_bit") K.«u256_bit» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_limb»
  fb_prove2 44 Guest.Software.guestFn_u256_bit K.«u256_bit»

theorem «fb_u256_byte» :
    TerminatingFunBoundedOn GuestInv (ofString "u256_byte") K.«u256_byte» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_limb»
  fb_prove2 85 Guest.Software.guestFn_u256_byte K.«u256_byte»

theorem while_counter_step_lower_guestInv (i X : MlS)
    {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn GuestInv body B) (hinc : CounterStep i 1 body)
    (hX : avoidsLocal X body = true) :
    TerminatingProgBoundedOn GuestInv (.while (.cmp .lower (.var .local i) (.var .local X)) body)
      ((2 ^ 64 + 1) * (B + 1)) := by
  refine @TerminatingProgBoundedOn.while_rank GuestInv
    (.cmp .lower (.var .local i) (.var .local X)) body B (2 ^ 64)
    (counterGap .lower i X)
    (fun s hs => guestInv_decClock s hs) hbody ?_ ?_
  · intro F s _ _ _
    simp only [counterGap]
    split
    · rename_i a b _ _
      have := cmpRank_le .lower b
      omega
    · omega
  · intro F s _ hs hact hflow
    refine ⟨guestInv_evaluate _ _ (guestInv_decClock s hs), ?_⟩
    obtain ⟨word, hw, hnz⟩ := hact
    change evalAt s _ = _ at hw
    obtain ⟨a, b, ha, hb, hword⟩ := evalAt_cmp s .lower _ _ word hw
    simp only [evalAt, evalHOLExact] at ha hb
    have hia : s.locals.lookup i = some (.val (.word a)) := by simpa using ha
    have hXb : s.locals.lookup X = some (.val (.word b)) := by simpa using hb
    have hcmp : wordCmpHOL .lower a b = true := by
      by_contra hc
      simp [hc] at hword
      exact hnz hword
    have hlt := cmpRank_lt .lower (Or.inr rfl) a b hcmp
    have hi' := hinc (decClockHOLFinite s) a hia hflow
    have hX' := evaluate_avoidsLocal_flowing X body hX (decClockHOLFinite s)
      (hflow.elim Or.inl (fun h => Or.inr (Or.inr h)))
    have hX'' : (evaluateHOLFiniteState (decClockHOLFinite s) body).2.locals.lookup X =
        some (.val (.word b)) := hX'.trans hXb
    have hsucc := cmpRank_succ .lower a b hlt
    simp only [counterGap, hi', hX'', hia, hXb]
    omega

theorem «fb_u256_exp» :
    TerminatingFunBoundedOn GuestInv (ofString "u256_exp") K.«u256_exp» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_bit»
  have h1 := InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees.«fb_u256_bit_length»
  have h2 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_mul»
  fb_unfold 80 Guest.Software.guestFn_u256_exp
  apply TerminatingProgBoundedOn.weaken'
  · apply dec_guestInv
    apply dec_guestInv
    apply decCall_guestInv' h1
    apply dec_guestInv
    apply TerminatingProgBoundedOn.seq_guestInv
    · apply while_counter_step_lower_guestInv
      · fb_auto2
      · apply CounterStep.decCall _ _ _ _ _ _ (by decide)
        apply CounterStep.seq _ _ _ rfl rfl
        exact CounterStep.suffix _ _ _ (CounterStep.assign _ _) rfl
      · rfl
    · exact straightOn _ rfl
  · have hD : domainBytes + 1 + 1 ≤ 2 ^ 64 + 1 := by rw [domainBytes_eq]; decide
    unfold K.«u256_exp»
    generalize_K
    generalize domainBytes = D at hD ⊢
    try simp only [nat_max_eq]
    omega

theorem «fb_u256_sar» :
    TerminatingFunBoundedOn GuestInv (ofString "u256_sar") K.«u256_sar» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_or»
  have h1 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_shl»
  have h2 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_shr»
  fb_prove2 83 Guest.Software.guestFn_u256_sar K.«u256_sar»

theorem «fb_u256_sdiv» :
    TerminatingFunBoundedOn GuestInv (ofString "u256_sdiv") K.«u256_sdiv» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_abs»
  have h1 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_div»
  have h2 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_neg»
  fb_prove2 73 Guest.Software.guestFn_u256_sdiv K.«u256_sdiv»

theorem «fb_u256_sgt» :
    TerminatingFunBoundedOn GuestInv (ofString "u256_sgt") K.«u256_sgt» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_slt»
  fb_prove2 49 Guest.Software.guestFn_u256_sgt K.«u256_sgt»

theorem «fb_u256_signextend» :
    TerminatingFunBoundedOn GuestInv (ofString "u256_signextend") K.«u256_signextend» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_and»
  have h1 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_bit»
  have h2 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_not»
  have h3 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_or»
  have h4 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_shl»
  fb_prove2 84 Guest.Software.guestFn_u256_signextend K.«u256_signextend»

theorem «fb_u256_smod» :
    TerminatingFunBoundedOn GuestInv (ofString "u256_smod") K.«u256_smod» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_abs»
  have h1 := InitECandidate.Solver.Wave8GuestInv.P13.DivMod.«fb_u256_mod»
  have h2 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_neg»
  fb_prove2 74 Guest.Software.guestFn_u256_smod K.«u256_smod»

theorem «fb_account_deployable» :
    TerminatingFunBoundedOn GuestInv (ofString "account_deployable") K.«account_deployable» := by
  exact InitECandidate.Solver.Wave8GuestInv.S01.fb_account_deployable_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_get_account» InitECandidate.Solver.Wave8Leaves.Rlp.«fb_memeq» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_account_has_storage»

theorem «fb_auth_list_payload_len» :
    TerminatingFunBoundedOn GuestInv (ofString "auth_list_payload_len") K.«auth_list_payload_len» := by
  exact InitECandidate.Solver.Wave8GuestInv.S11.fb_auth_list_payload_len_of InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_auth_payload_len» InitECandidate.Solver.Wave8Leaves.Rlp.«fb_rlp_list_header_len»

theorem «fb_block_rlp_length» :
    TerminatingFunBoundedOn GuestInv (ofString "block_rlp_length") K.«block_rlp_length» := by
  exact InitECandidate.Solver.Wave8Leaves.S13.certified_fb_block_rlp_length InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_encode_header» InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_mark» InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_release» InitECandidate.Solver.Wave8Leaves.Rlp.«fb_rlp_bytes_encoded_len» InitECandidate.Solver.Wave8Leaves.Rlp.«fb_rlp_list_header_len» InitECandidate.Solver.Wave8Leaves.Rlp.«fb_withdrawal_rlp_len»

theorem «fb_calculate_base_fee_per_gas» :
    TerminatingFunBoundedOn GuestInv (ofString "calculate_base_fee_per_gas") K.«calculate_base_fee_per_gas» := by
  exact InitECandidate.Solver.Wave8Leaves.S13.certified_fb_calculate_base_fee_per_gas InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_check_gas_limit» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_add» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_div» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_from_word» (InitECandidate.Solver.Wave8GuestInv.S01.«on_u256_is_zero» (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv)) InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_mul» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_sub»

theorem «fb_check_transaction» :
    TerminatingFunBoundedOn GuestInv (ofString "check_transaction") K.«check_transaction» := by
  exact InitECandidate.Solver.Wave8GuestInv.S11.fb_check_transaction_of InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_min» InitECandidate.Solver.Wave8GuestInv.Merged.fb_calculate_total_blob_gas InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_get_account» InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees.«fb_u256_lt» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_sub» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_add» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_fee_mul» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_calculate_blob_gas_price» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_add_carry» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_fits_word» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_get_code» InitECandidate.Solver.Wave8Leaves.Rlp.«fb_memeq» InitECandidate.Solver.Wave8Leaves.S04.Verified.fb_is_valid_delegation

theorem «fb_decode_host_input» :
    TerminatingFunBoundedOn GuestInv (ofString "decode_host_input") K.«decode_host_input» := by
  exact InitECandidate.Solver.Wave8Leaves.S13.certified_fb_decode_host_input InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_decode_stateless_input» InitECandidate.Solver.Wave8GuestInv.Merged.fb_input_blob InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_precheck_host_ssz_header»

theorem «fb_htr_bdep» :
    TerminatingFunBoundedOn GuestInv (ofString "htr_bdep") K.«htr_bdep» := by
  exact InitECandidate.Solver.Wave8GuestInv.S14.fb_htr_bdep_of InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_mark» InitECandidate.Solver.Wave8Leaves.Rlp.«fb_alloc» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_htr_bytes_vector» InitECandidate.Solver.Wave8Leaves.Rlp.«fb_memcpy» InitECandidate.Solver.Wave8GuestInv.Merged.fb_htr_u64_at InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_merkleize» InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_release»

theorem «fb_htr_bexit» :
    TerminatingFunBoundedOn GuestInv (ofString "htr_bexit") K.«htr_bexit» := by
  exact InitECandidate.Solver.Wave8GuestInv.S14.fb_htr_bexit_of InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_mark» InitECandidate.Solver.Wave8Leaves.Rlp.«fb_alloc» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_htr_bytes_vector» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_merkleize» InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_release»

theorem «fb_htr_pbytes» :
    TerminatingFunBoundedOn GuestInv (ofString "htr_pbytes") K.«htr_pbytes» := by
  exact InitECandidate.Solver.Wave8GuestInv.S14.fb_htr_pbytes_of InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_mark» InitECandidate.Solver.Wave8Leaves.Rlp.«fb_pack_bytes» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_htr_plist_chunks» InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_release»

theorem «fb_htr_request_list» :
    TerminatingFunBoundedOn GuestInv (ofString "htr_request_list") K.«htr_request_list» := by
  exact InitECandidate.Solver.Wave8GuestInv.S14.fb_htr_request_list_of InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_mark» InitECandidate.Solver.Wave8Leaves.Rlp.«fb_alloc» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_htr_deposit» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_htr_wdreq» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_htr_cons» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_htr_bdep» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_htr_bexit» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_htr_plist_chunks» InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_release»

theorem «fb_htr_requests» :
    TerminatingFunBoundedOn GuestInv (ofString "htr_requests") K.«htr_requests» := by
  exact InitECandidate.Solver.Wave8GuestInv.S14.fb_htr_requests_of InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_mark» InitECandidate.Solver.Wave8Leaves.Rlp.«fb_alloc» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_htr_request_list» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_htr_pcontainer» InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_release»

theorem «fb_op_exp» :
    TerminatingFunBoundedOn GuestInv (ofString "op_exp") K.«op_exp» := by
  exact InitECandidate.Solver.Wave8Leaves.S08.fb_op_exp InitECandidate.Solver.Wave8GuestInv.Merged.fb_stack_pop InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_byte_length» InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_charge_gas» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_exp» InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_stack_push» InitECandidate.Solver.Wave8GuestInv.Merged.fb_pc_add

theorem «fb_tx_encode_bound» :
    TerminatingFunBoundedOn GuestInv (ofString "tx_encode_bound") K.«tx_encode_bound» := by
  exact InitECandidate.Solver.Wave8GuestInv.S11.fb_tx_encode_bound_of InitECandidate.Solver.Wave8GuestInv.Merged.fb_access_list_payload_len InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_auth_list_payload_len»

theorem «fb_validate_header» :
    TerminatingFunBoundedOn GuestInv (ofString "validate_header") K.«validate_header» := by
  exact InitECandidate.Solver.Wave8Leaves.S13.certified_fb_validate_header InitECandidate.Solver.Wave8Leaves.Rlp.«fb_alloc» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_calculate_base_fee_per_gas» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_calculate_excess_blob_gas» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_header_hash» InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_mark» InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_release» InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_keccak256» InitECandidate.Solver.Wave8Leaves.Rlp.«fb_memeq» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_eq» (InitECandidate.Solver.Wave8GuestInv.S01.«on_u256_is_zero» (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv))

theorem «fb_decode_header» :
    TerminatingFunBoundedOn GuestInv (ofString "decode_header") K.«decode_header» := by
  have h0 := InitECandidate.Solver.Wave8Leaves.Rlp.«fb_alloc»
  have h1 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_hdr_bytes_field»
  have h2 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_hdr_raw_field»
  have h3 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_hdr_u256_field»
  have h4 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_hdr_uint_field»
  have h5 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_hdr_word_field»
  have h6 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_rlp_decode_fully»
  have h7 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_rlp_list_to_slices»
  fb_prove2 227 Guest.Software.guestFn_decode_header K.«decode_header»

theorem «fb_decode_transaction» :
    TerminatingFunBoundedOn GuestInv (ofString "decode_transaction") K.«decode_transaction» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_decode_transaction_rlp»
  fb_prove2 307 Guest.Software.guestFn_decode_transaction K.«decode_transaction»

theorem «fb_ext_code_of» :
    TerminatingFunBoundedOn GuestInv (ofString "ext_code_of") K.«ext_code_of» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_get_account»
  have h1 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_get_code»
  fb_prove2 543 Guest.Software.guestFn_ext_code_of K.«ext_code_of»

theorem «fb_htr_payload» :
    TerminatingFunBoundedOn GuestInv (ofString "htr_payload") K.«htr_payload» := by
  exact InitECandidate.Solver.Wave8GuestInv.S14.fb_htr_payload_of InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_mark» InitECandidate.Solver.Wave8GuestInv.Merged.fb_alloc InitECandidate.Solver.Wave8GuestInv.Merged.fb_memcpy InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_htr_bytes_vector» InitECandidate.Solver.Wave8GuestInv.Merged.fb_htr_u64_at InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_htr_bytes_list» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_htr_pbytes» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_htr_plist_chunks» InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_release» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_htr_withdrawal» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_htr_pcontainer»
theorem «fb_is_valid_versioned_hashes» :
    TerminatingFunBoundedOn GuestInv (ofString "is_valid_versioned_hashes") K.«is_valid_versioned_hashes» := by
  exact InitECandidate.Solver.Wave8Leaves.S13.certified_fb_is_valid_versioned_hashes InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_decode_transaction» InitECandidate.Solver.Wave8GuestInv.Merged.fb_memeq InitECandidate.Solver.Wave8GuestInv.Merged.fb_tx_is_blob
theorem «fb_op_byte» :
    TerminatingFunBoundedOn GuestInv (ofString "op_byte") K.«op_byte» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_charge_gas»
  have h1 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_pc_add
  have h2 := InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees.«fb_sat_word»
  have h3 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_stack_pop
  have h4 := InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees.«fb_stack_push_word»
  have h5 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_byte»
  fb_prove2 496 Guest.Software.guestFn_op_byte K.«op_byte»

theorem «fb_op_extcodecopy» :
    TerminatingFunBoundedOn GuestInv (ofString "op_extcodecopy") K.«op_extcodecopy» := by
  exact InitECandidate.Solver.Wave8Leaves.S08.fb_op_extcodecopy InitECandidate.Solver.Wave8GuestInv.Merged.fb_stack_pop InitECandidate.Solver.Wave8GuestInv.Merged.fb_to_address_masked InitECandidate.Solver.Wave8GuestInv.Merged.fb_sat_word InitECandidate.Solver.Wave8GuestInv.Merged.fb_words_of InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees.«fb_extend_memory_cost1» InitECandidate.Solver.Wave8GuestInv.Merged.fb_access_gas_cost InitECandidate.Solver.Wave8GuestInv.Merged.fb_add_sat InitECandidate.Solver.Wave8GuestInv.Merged.fb_charge_gas InitECandidate.Solver.Wave8GuestInv.Merged.fb_warm_after_charge InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees.«fb_extend_memory» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_ext_code_of» InitECandidate.Solver.Wave8GuestInv.Merged.fb_buffer_read InitECandidate.Solver.Wave8GuestInv.Merged.fb_pc_add
theorem «fb_op_extcodesize» :
    TerminatingFunBoundedOn GuestInv (ofString "op_extcodesize") K.«op_extcodesize» := by
  exact InitECandidate.Solver.Wave8Leaves.S08.fb_op_extcodesize InitECandidate.Solver.Wave8GuestInv.Merged.fb_stack_pop InitECandidate.Solver.Wave8GuestInv.Merged.fb_to_address_masked InitECandidate.Solver.Wave8GuestInv.Merged.fb_access_gas_cost InitECandidate.Solver.Wave8GuestInv.Merged.fb_charge_gas InitECandidate.Solver.Wave8GuestInv.Merged.fb_warm_after_charge InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_ext_code_of» InitECandidate.Solver.Wave8GuestInv.Merged.fb_stack_push_word InitECandidate.Solver.Wave8GuestInv.Merged.fb_pc_add
theorem «fb_op_sar» :
    TerminatingFunBoundedOn GuestInv (ofString "op_sar") K.«op_sar» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_charge_gas»
  have h1 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_pc_add
  have h2 := InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees.«fb_sat_word»
  have h3 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_stack_pop
  have h4 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_stack_push»
  have h5 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_sar»
  fb_prove2 499 Guest.Software.guestFn_op_sar K.«op_sar»

theorem «fb_op_sdiv» :
    TerminatingFunBoundedOn GuestInv (ofString "op_sdiv") K.«op_sdiv» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_charge_gas»
  have h1 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_pc_add
  have h2 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_stack_pop
  have h3 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_stack_push»
  have h4 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_sdiv»
  fb_prove2 479 Guest.Software.guestFn_op_sdiv K.«op_sdiv»

theorem «fb_op_sgt» :
    TerminatingFunBoundedOn GuestInv (ofString "op_sgt") K.«op_sgt» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_charge_gas»
  have h1 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_pc_add
  have h2 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_stack_pop
  have h3 := InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees.«fb_stack_push_bool»
  have h4 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_sgt»
  fb_prove2 489 Guest.Software.guestFn_op_sgt K.«op_sgt»

theorem «fb_op_signextend» :
    TerminatingFunBoundedOn GuestInv (ofString "op_signextend") K.«op_signextend» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_charge_gas»
  have h1 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_pc_add
  have h2 := InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees.«fb_sat_word»
  have h3 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_stack_pop
  have h4 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_stack_push»
  have h5 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_signextend»
  fb_prove2 485 Guest.Software.guestFn_op_signextend K.«op_signextend»

theorem «fb_op_smod» :
    TerminatingFunBoundedOn GuestInv (ofString "op_smod") K.«op_smod» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_charge_gas»
  have h1 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_pc_add
  have h2 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_stack_pop
  have h3 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_stack_push»
  have h4 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_smod»
  fb_prove2 481 Guest.Software.guestFn_op_smod K.«op_smod»

theorem «fb_tx_put_authorizations» :
    TerminatingFunBoundedOn GuestInv (ofString "tx_put_authorizations") K.«tx_put_authorizations» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_auth_list_payload_len»
  have h1 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_auth_payload_len»
  have h2 := InitECandidate.Solver.Wave8Leaves.Rlp.«fb_rlp_encode_bytes»
  have h3 := InitECandidate.Solver.Wave8Leaves.Rlp.«fb_rlp_encode_list_header»
  have h4 := InitECandidate.Solver.Wave8Leaves.Rlp.«fb_rlp_encode_word»
  have h5 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_tx_put_u256»
  fb_prove2 326 Guest.Software.guestFn_tx_put_authorizations K.«tx_put_authorizations»

theorem «fb_validate_headers» :
    TerminatingFunBoundedOn GuestInv (ofString "validate_headers") K.«validate_headers» := by
  exact InitECandidate.Solver.Wave8Leaves.S13.certified_fb_validate_headers InitECandidate.Solver.Wave8GuestInv.Merged.fb_alloc InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_decode_header» InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_keccak256» InitECandidate.Solver.Wave8GuestInv.Merged.fb_memeq
theorem «fb_htr_new_payload_request» :
    TerminatingFunBoundedOn GuestInv (ofString "htr_new_payload_request") K.«htr_new_payload_request» := by
  exact InitECandidate.Solver.Wave8GuestInv.S14.fb_htr_new_payload_request_of InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_mark» InitECandidate.Solver.Wave8Leaves.Rlp.«fb_alloc» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_htr_payload» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_htr_plist_chunks» InitECandidate.Solver.Wave8Leaves.Rlp.«fb_memcpy» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_htr_requests» InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_merkleize» InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_heap_release»

theorem «fb_calculate_delegation_cost» :
    TerminatingFunBoundedOn GuestInv (ofString "calculate_delegation_cost") K.«calculate_delegation_cost» := by
  have h0 := InitECandidate.Solver.Wave8Leaves.Rlp.«fb_alloc»
  have h1 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_ext_code_of»
  have h2 := InitECandidate.Solver.Wave8Leaves.S04.Verified.fb_is_valid_delegation
  have h3 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_is_warm_address
  have h4 := InitECandidate.Solver.Wave8Leaves.Rlp.«fb_memcpy»
  fb_prove2 573 Guest.Software.guestFn_calculate_delegation_cost K.«calculate_delegation_cost»

theorem «fb_tx_encode_generic» :
    TerminatingFunBoundedOn GuestInv (ofString "tx_encode_generic") K.«tx_encode_generic» := by
  have h0 := InitECandidate.Solver.Wave8Leaves.Rlp.«fb_alloc»
  have h1 := InitECandidate.Solver.Wave8Leaves.Rlp.«fb_rlp_encode_bytes»
  have h2 := InitECandidate.Solver.Wave8Leaves.Rlp.«fb_rlp_encode_list_header»
  have h3 := InitECandidate.Solver.Wave8Leaves.Rlp.«fb_rlp_encode_word»
  have h4 := InitECandidate.Solver.Wave8Leaves.Rlp.«fb_rlp_list_header_len»
  have h5 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_tx_encode_bound»
  have h6 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_tx_put_access_list
  have h7 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_tx_put_authorizations»
  have h8 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_tx_put_blob_hashes
  have h9 := InitECandidate.Solver.Wave8GuestInv.Merged.fb_tx_put_to
  have h10 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_tx_put_u256»
  fb_prove2 328 Guest.Software.guestFn_tx_encode_generic K.«tx_encode_generic»

theorem «fb_encode_transaction» :
    TerminatingFunBoundedOn GuestInv (ofString "encode_transaction") K.«encode_transaction» := by
  exact InitECandidate.Solver.Wave8Leaves.S12.fb_encode_transaction InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_tx_encode_generic»

end InitECandidate.Solver.Wave8GuestInv.R11Adapters
