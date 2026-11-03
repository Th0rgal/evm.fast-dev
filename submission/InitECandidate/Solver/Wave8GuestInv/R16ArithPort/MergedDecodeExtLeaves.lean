import InitECandidate.Solver.Wave8GuestInv.Deliveries.RLP.Axioms
import InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.FbCore
import InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.FbHtab
import InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.FbRlp
import InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.FbSetStorage
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P12_P15Callees
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_12
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_16
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_21
import InitECandidate.Solver.Wave8GuestInv.R11Adapters.FbAuto2
import InitECandidate.Solver.Wave8GuestInv.Shards.S04.Axioms

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unusedSectionVars false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R16ArithPort

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
open InitECandidate.Solver.Wave8GuestInv.R11Adapters

theorem fb_hdr_bytes_field :
    TerminatingFunBoundedOn GuestInv (ofString "hdr_bytes_field") K.«hdr_bytes_field» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_rlp_item»
  fb_prove2 225 Guest.Software.guestFn_hdr_bytes_field K.«hdr_bytes_field»

theorem fb_hdr_raw_field :
    TerminatingFunBoundedOn GuestInv (ofString "hdr_raw_field") K.«hdr_raw_field» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_rlp_item»
  fb_prove2 226 Guest.Software.guestFn_hdr_raw_field K.«hdr_raw_field»

theorem fb_hdr_uint_field :
    TerminatingFunBoundedOn GuestInv (ofString "hdr_uint_field") K.«hdr_uint_field» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_rlp_item»
  fb_prove2 222 Guest.Software.guestFn_hdr_uint_field K.«hdr_uint_field»

theorem fb_hdr_word_field :
    TerminatingFunBoundedOn GuestInv (ofString "hdr_word_field") K.«hdr_word_field» := by
  have h0 := fb_hdr_uint_field
  fb_prove2 223 Guest.Software.guestFn_hdr_word_field K.«hdr_word_field»

theorem fb_hdr_u256_field :
    TerminatingFunBoundedOn GuestInv (ofString "hdr_u256_field") K.«hdr_u256_field» := by
  have h0 := fb_hdr_uint_field
  have h1 := InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees.«fb_u256_from_be»
  fb_prove2 224 Guest.Software.guestFn_hdr_u256_field K.«hdr_u256_field»

theorem fb_decode_header :
    TerminatingFunBoundedOn GuestInv (ofString "decode_header") K.«decode_header» := by
  have h0 := InitECandidate.Solver.Wave8Leaves.Rlp.«fb_alloc»
  have h1 := fb_hdr_bytes_field
  have h2 := fb_hdr_raw_field
  have h3 := fb_hdr_u256_field
  have h4 := fb_hdr_uint_field
  have h5 := fb_hdr_word_field
  have h6 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_rlp_decode_fully»
  have h7 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_rlp_list_to_slices»
  fb_prove2 227 Guest.Software.guestFn_decode_header K.«decode_header»

theorem fb_tx_bytes_item :
    TerminatingFunBoundedOn GuestInv (ofString "tx_bytes_item") K.«tx_bytes_item» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_rlp_item»
  fb_prove2 299 Guest.Software.guestFn_tx_bytes_item K.«tx_bytes_item»

theorem fb_tx_fixed_bytes :
    TerminatingFunBoundedOn GuestInv (ofString "tx_fixed_bytes") K.«tx_fixed_bytes» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_rlp_item»
  fb_prove2 300 Guest.Software.guestFn_tx_fixed_bytes K.«tx_fixed_bytes»

theorem fb_tx_list_item :
    TerminatingFunBoundedOn GuestInv (ofString "tx_list_item") K.«tx_list_item» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_rlp_item»
  fb_prove2 302 Guest.Software.guestFn_tx_list_item K.«tx_list_item»

theorem fb_tx_scalar_item :
    TerminatingFunBoundedOn GuestInv (ofString "tx_scalar_item") K.«tx_scalar_item» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_rlp_item»
  fb_prove2 296 Guest.Software.guestFn_tx_scalar_item K.«tx_scalar_item»

theorem fb_tx_scalar_u256 :
    TerminatingFunBoundedOn GuestInv (ofString "tx_scalar_u256") K.«tx_scalar_u256» := by
  have h0 := fb_tx_scalar_item
  have h1 := InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees.«fb_u256_from_be»
  fb_prove2 297 Guest.Software.guestFn_tx_scalar_u256 K.«tx_scalar_u256»

theorem fb_tx_scalar_word :
    TerminatingFunBoundedOn GuestInv (ofString "tx_scalar_word") K.«tx_scalar_word» := by
  have h0 := fb_tx_scalar_item
  fb_prove2 298 Guest.Software.guestFn_tx_scalar_word K.«tx_scalar_word»

theorem fb_tx_to_item :
    TerminatingFunBoundedOn GuestInv (ofString "tx_to_item") K.«tx_to_item» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_rlp_item»
  fb_prove2 301 Guest.Software.guestFn_tx_to_item K.«tx_to_item»

theorem fb_decode_access_list :
    TerminatingFunBoundedOn GuestInv (ofString "decode_access_list") K.«decode_access_list» :=
  InitECandidate.Solver.Wave8GuestInv.FastGen.fb_decode_access_list_of
    InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_rlp_item»
    InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_rlp_list_to_slices»
    fb_tx_fixed_bytes
    fb_tx_list_item

theorem fb_decode_authorizations :
    TerminatingFunBoundedOn GuestInv (ofString "decode_authorizations") K.«decode_authorizations» :=
  InitECandidate.Solver.Wave8GuestInv.FastGen.fb_decode_authorizations_of
    InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_rlp_item»
    InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_rlp_list_to_slices»
    fb_tx_fixed_bytes
    fb_tx_scalar_u256
    fb_tx_scalar_word

theorem fb_decode_blob_hashes :
    TerminatingFunBoundedOn GuestInv (ofString "decode_blob_hashes") K.«decode_blob_hashes» :=
  InitECandidate.Solver.Wave8GuestInv.FastGen.fb_decode_blob_hashes_of
    InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_rlp_list_to_slices»
    fb_tx_fixed_bytes

theorem fb_decode_transaction_rlp :
    TerminatingFunBoundedOn GuestInv (ofString "decode_transaction_rlp") K.«decode_transaction_rlp» := by
  have h_alloc := InitECandidate.Solver.Wave8Leaves.Rlp.«fb_alloc»
  have h_dal := fb_decode_access_list
  have h_da := fb_decode_authorizations
  have h_dbh := fb_decode_blob_hashes
  have h_mz := InitECandidate.Solver.Wave8Leaves.Rlp.«fb_memzero»
  have h_rdf := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_rlp_decode_fully»
  have h_rlts := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_rlp_list_to_slices»
  have h_tbi := fb_tx_bytes_item
  have h_tfb := fb_tx_fixed_bytes
  have h_tli := fb_tx_list_item
  have h_tsu := fb_tx_scalar_u256
  have h_tsw := fb_tx_scalar_word
  have h_tti := fb_tx_to_item
  refine ⟨_, _, _, lookup_of_guestAst_getElem 306 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_decode_transaction_rlp) rfl, ?_⟩
  dsimp only [extractFn, Guest.Software.guestFn_decode_transaction_rlp,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  apply TerminatingProgBoundedOn.weaken'
  · apply TerminatingProgBoundedOn.seq_guestInv; · exact straightOn _ rfl
    apply dec_guestInv
    apply decCall_guestInv' h_alloc
    apply TerminatingProgBoundedOn.seq_guestInv; · exact call_guestInv' h_mz
    apply TerminatingProgBoundedOn.seq_guestInv; · exact straightOn _ rfl
    apply TerminatingProgBoundedOn.seq_guestInv; · exact straightOn _ rfl
    apply dec_guestInv
    apply dec_guestInv
    apply dec_guestInv
    apply TerminatingProgBoundedOn.seq_guestInv
    · apply TerminatingProgBoundedOn.ite_on
      · apply TerminatingProgBoundedOn.seq_guestInv
        · exact call_guestInv' h_rdf
        · exact straightOn _ rfl
      · apply TerminatingProgBoundedOn.ite_on
        · exact call_guestInv' h_rdf
        · exact straightOn _ rfl
    apply TerminatingProgBoundedOn.seq_guestInv; · exact straightOn _ rfl
    apply TerminatingProgBoundedOn.seq_guestInv; · exact straightOn _ rfl
    apply decCall_guestInv' h_rlts
    apply dec_guestInv
    apply TerminatingProgBoundedOn.seq_guestInv; · exact straightOn _ rfl
    apply dec_guestInv
    apply dec_guestInv
    apply TerminatingProgBoundedOn.seq_guestInv
    · apply TerminatingProgBoundedOn.ite_on
      · apply TerminatingProgBoundedOn.seq_guestInv
        · exact call_guestInv' h_tsw
        · exact straightOn _ rfl
      · exact straightOn _ rfl
    apply dec_guestInv
    apply TerminatingProgBoundedOn.seq_guestInv
    · apply TerminatingProgBoundedOn.ite_on
      · apply TerminatingProgBoundedOn.seq_guestInv
        · exact call_guestInv' h_tsw
        · exact straightOn _ rfl
      · exact call_guestInv' h_tsu
    apply TerminatingProgBoundedOn.seq_guestInv; · exact straightOn _ rfl
    apply TerminatingProgBoundedOn.seq_guestInv; · exact straightOn _ rfl
    apply TerminatingProgBoundedOn.seq_guestInv
    · apply TerminatingProgBoundedOn.ite_on
      · apply TerminatingProgBoundedOn.seq_guestInv
        · exact call_guestInv' h_tsu
        · exact straightOn _ rfl
      · apply TerminatingProgBoundedOn.seq_guestInv
        · exact call_guestInv' h_tsu
        · apply TerminatingProgBoundedOn.seq_guestInv
          · exact straightOn _ rfl
          · apply TerminatingProgBoundedOn.seq_guestInv
            · exact call_guestInv' h_tsu
            · exact straightOn _ rfl
    apply TerminatingProgBoundedOn.seq_guestInv; · exact call_guestInv' h_tsw
    apply TerminatingProgBoundedOn.seq_guestInv; · exact straightOn _ rfl
    apply TerminatingProgBoundedOn.seq_guestInv; · exact straightOn _ rfl
    apply TerminatingProgBoundedOn.seq_guestInv
    · apply TerminatingProgBoundedOn.ite_on
      · exact call_guestInv' h_tfb
      · exact call_guestInv' h_tti
    apply TerminatingProgBoundedOn.seq_guestInv; · exact straightOn _ rfl
    apply TerminatingProgBoundedOn.seq_guestInv; · exact straightOn _ rfl
    apply TerminatingProgBoundedOn.seq_guestInv; · exact call_guestInv' h_tsu
    apply TerminatingProgBoundedOn.seq_guestInv; · exact straightOn _ rfl
    apply TerminatingProgBoundedOn.seq_guestInv; · exact straightOn _ rfl
    apply decCall_guestInv' h_tbi
    apply TerminatingProgBoundedOn.seq_guestInv; · exact straightOn _ rfl
    apply TerminatingProgBoundedOn.seq_guestInv; · exact straightOn _ rfl
    apply TerminatingProgBoundedOn.seq_guestInv; · exact straightOn _ rfl
    apply TerminatingProgBoundedOn.seq_guestInv
    · apply TerminatingProgBoundedOn.ite_on
      · apply decCall_guestInv' h_tli
        apply decCall_guestInv' h_dal
        exact straightOn _ rfl
      · exact straightOn _ rfl
    apply TerminatingProgBoundedOn.seq_guestInv
    · apply TerminatingProgBoundedOn.ite_on
      · apply TerminatingProgBoundedOn.seq_guestInv
        · exact call_guestInv' h_tsu
        · apply TerminatingProgBoundedOn.seq_guestInv
          · exact straightOn _ rfl
          · apply decCall_guestInv' h_tli
            apply decCall_guestInv' h_dbh
            exact straightOn _ rfl
      · exact straightOn _ rfl
    apply TerminatingProgBoundedOn.seq_guestInv
    · apply TerminatingProgBoundedOn.ite_on
      · apply decCall_guestInv' h_tli
        apply decCall_guestInv' h_da
        exact straightOn _ rfl
      · exact straightOn _ rfl
    apply TerminatingProgBoundedOn.seq_guestInv; · exact call_guestInv' h_tsu
    apply TerminatingProgBoundedOn.seq_guestInv; · exact straightOn _ rfl
    apply TerminatingProgBoundedOn.seq_guestInv; · exact call_guestInv' h_tsu
    apply TerminatingProgBoundedOn.seq_guestInv; · exact straightOn _ rfl
    apply TerminatingProgBoundedOn.seq_guestInv; · exact call_guestInv' h_tsu
    exact straightOn _ rfl
  · unfold K.«decode_transaction_rlp»
    generalize_K
    simp only [nat_max_eq, Nat.add_zero, Nat.zero_add, Nat.max_zero]
    exact Nat.le_of_eq (by ac_rfl)

theorem fb_decode_transaction :
    TerminatingFunBoundedOn GuestInv (ofString "decode_transaction") K.«decode_transaction» := by
  have h0 := fb_decode_transaction_rlp
  fb_prove2 307 Guest.Software.guestFn_decode_transaction K.«decode_transaction»

theorem fb_get_code_of
    (h_nodedb_lookup : TerminatingFunBoundedOn GuestInv (ofString "nodedb_lookup") K.«nodedb_lookup») :
    TerminatingFunBoundedOn GuestInv (ofString "get_code") K.«get_code» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_htab_get»
  have h1 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_htab_set»
  have h2 := InitECandidate.Solver.Wave8Leaves.Rlp.«fb_memeq»
  have h3 := InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.«fb_sk_make»
  have h4 := InitECandidate.Solver.Wave8GuestInv.FastGen.fb_ws_get_code_of
    InitECandidate.Solver.Wave8Leaves.Rlp.«fb_memeq» h_nodedb_lookup
  fb_prove2 376 Guest.Software.guestFn_get_code K.«get_code»

theorem fb_ext_code_of_of
    (h_get_account : TerminatingFunBoundedOn GuestInv (ofString "get_account") K.«get_account»)
    (h_get_code : TerminatingFunBoundedOn GuestInv (ofString "get_code") K.«get_code») :
    TerminatingFunBoundedOn GuestInv (ofString "ext_code_of") K.«ext_code_of» := by
  have h0 := h_get_account
  have h1 := h_get_code
  fb_prove2 543 Guest.Software.guestFn_ext_code_of K.«ext_code_of»

theorem fb_calculate_delegation_cost_of
    (h_ext_code_of : TerminatingFunBoundedOn GuestInv (ofString "ext_code_of") K.«ext_code_of»)
    (h_is_warm_address : TerminatingFunBoundedOn GuestInv (ofString "is_warm_address") K.«is_warm_address») :
    TerminatingFunBoundedOn GuestInv (ofString "calculate_delegation_cost") K.«calculate_delegation_cost» := by
  have h0 := InitECandidate.Solver.Wave8Leaves.Rlp.«fb_alloc»
  have h1 := h_ext_code_of
  have h2 := InitECandidate.Solver.Wave8Leaves.S04.Verified.fb_is_valid_delegation
  have h3 := h_is_warm_address
  have h4 := InitECandidate.Solver.Wave8Leaves.Rlp.«fb_memcpy»
  fb_prove2 573 Guest.Software.guestFn_calculate_delegation_cost K.«calculate_delegation_cost»

theorem fb_generic_call_of
    (h_credit_state_gas_refund : TerminatingFunBoundedOn GuestInv (ofString "credit_state_gas_refund") K.«credit_state_gas_refund»)
    (h_frame_mem_mark : TerminatingFunBoundedOn GuestInv (ofString "frame_mem_mark") K.«frame_mem_mark»)
    (h_scratch_mark : TerminatingFunBoundedOn GuestInv (ofString "scratch_mark") K.«scratch_mark»)
    (h_set_retdata : TerminatingFunBoundedOn GuestInv (ofString "set_retdata") K.«set_retdata»)
    (h_stack_push : TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push»)
    (h_start_child : TerminatingFunBoundedOn GuestInv (ofString "start_child") K.«start_child») :
    TerminatingFunBoundedOn GuestInv (ofString "generic_call") K.«generic_call» := by
  have h0 := h_set_retdata
  have h1 := h_credit_state_gas_refund
  have h2 := h_scratch_mark
  have h3 := h_frame_mem_mark
  have h4 := InitECandidate.Solver.Wave8GuestInv.FastGen.fb_child_message
  have h5 := h_stack_push
  have h6 := h_start_child
  fb_prove2 601 Guest.Software.guestFn_generic_call K.«generic_call»

end InitECandidate.Solver.Wave8GuestInv.R16ArithPort
