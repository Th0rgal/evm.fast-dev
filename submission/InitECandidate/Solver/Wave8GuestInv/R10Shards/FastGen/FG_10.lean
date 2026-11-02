import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FGCommon


set_option autoImplicit false
set_option linter.unusedTactic false
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.FastGen

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.GuestBoundBlockTxBal
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.P13.Common
open InitECandidate.Solver.Wave8GuestInv.FastGen

local syntax "fg_auto" : tactic
local macro_rules
  | `(tactic| fg_auto) => `(tactic| first
      | exact straightOn _ rfl
      | (apply TerminatingProgBoundedOn.seq_guestInv
         · fg_auto
         · fg_auto)
      | (apply TerminatingProgBoundedOn.ite_on
         · fg_auto
         · fg_auto)
      | (apply dec_guestInv; fg_auto)
      | (apply call_guestInv'; exact_fb_hyp)
      | (apply decCall_guestInv'
         · exact_fb_hyp
         · fg_auto)
      | (apply callHandle_guestInv'
         · exact_fb_hyp
         · fg_auto)
      | (apply tailCall_guestInv'; exact_fb_hyp))

local syntax "fg_auto_loops" : tactic
local macro_rules
  | `(tactic| fg_auto_loops) => `(tactic| first
      | fg_auto
      | (apply TerminatingProgBoundedOn.seq_guestInv
         · fg_auto_loops
         · fg_auto_loops)
      | (apply TerminatingProgBoundedOn.ite_on
         · fg_auto_loops
         · fg_auto_loops)
      | (apply dec_guestInv; fg_auto_loops)
      | (apply decCall_guestInv'
         · exact_fb_hyp
         · fg_auto_loops)
      | (apply callHandle_guestInv'
         · exact_fb_hyp
         · fg_auto_loops)
      | skip)

local syntax "fg_prove " num ident ident : tactic
local macro_rules
  | `(tactic| fg_prove $idx $fn $k) => `(tactic|
      (fg_unfold $idx $fn
       apply TerminatingProgBoundedOn.weaken'
       · fg_auto
       · fg_arith $k))

theorem fb_rmd_f :
    TerminatingFunBoundedOn GuestInv (ofString "rmd_f") K.rmd_f := by
  fg_prove 613 Guest.Software.guestFn_rmd_f K.rmd_f

theorem fb_rmd_k :
    TerminatingFunBoundedOn GuestInv (ofString "rmd_k") K.rmd_k := by
  fg_prove 614 Guest.Software.guestFn_rmd_k K.rmd_k

theorem fb_rmd_kp :
    TerminatingFunBoundedOn GuestInv (ofString "rmd_kp") K.rmd_kp := by
  fg_prove 615 Guest.Software.guestFn_rmd_kp K.rmd_kp

theorem fb_secp256k1_address_of_point :
    TerminatingFunBoundedOn GuestInv (ofString "secp256k1_address_of_point") K.secp256k1_address_of_point := by
  fg_prove 179 Guest.Software.guestFn_secp256k1_address_of_point K.secp256k1_address_of_point

theorem fb_signature_recovery_parameters_of
    (h_signing_hash_155 : TerminatingFunBoundedOn GuestInv (ofString "signing_hash_155") K.signing_hash_155)
    (h_signing_hash_1559 : TerminatingFunBoundedOn GuestInv (ofString "signing_hash_1559") K.signing_hash_1559)
    (h_signing_hash_2930 : TerminatingFunBoundedOn GuestInv (ofString "signing_hash_2930") K.signing_hash_2930)
    (h_signing_hash_4844 : TerminatingFunBoundedOn GuestInv (ofString "signing_hash_4844") K.signing_hash_4844)
    (h_signing_hash_7702 : TerminatingFunBoundedOn GuestInv (ofString "signing_hash_7702") K.signing_hash_7702)
    (h_signing_hash_pre155 : TerminatingFunBoundedOn GuestInv (ofString "signing_hash_pre155") K.signing_hash_pre155) :
    TerminatingFunBoundedOn GuestInv (ofString "signature_recovery_parameters") K.signature_recovery_parameters := by
  have _ := h_signing_hash_pre155
  have _ := h_signing_hash_155
  have _ := h_signing_hash_2930
  have _ := h_signing_hash_1559
  have _ := h_signing_hash_4844
  have _ := h_signing_hash_7702
  fg_prove 339 Guest.Software.guestFn_signature_recovery_parameters K.signature_recovery_parameters

theorem fb_sorted_keys32_of
    (h_htab_keys : TerminatingFunBoundedOn GuestInv (ofString "htab_keys") K.htab_keys)
    (h_sort_elems : TerminatingFunBoundedOn GuestInv (ofString "sort_elems") K.sort_elems) :
    TerminatingFunBoundedOn GuestInv (ofString "sorted_keys32") K.sorted_keys32 := by
  have _ := h_htab_keys
  have _ := h_sort_elems
  fg_prove 431 Guest.Software.guestFn_sorted_keys32 K.sorted_keys32

theorem fb_start_child_of
    (h_destroy_storage : TerminatingFunBoundedOn GuestInv (ofString "destroy_storage") K.destroy_storage)
    (h_frame_open : TerminatingFunBoundedOn GuestInv (ofString "frame_open") K.frame_open)
    (h_frame_start : TerminatingFunBoundedOn GuestInv (ofString "frame_start") K.frame_start)
    (h_increment_nonce : TerminatingFunBoundedOn GuestInv (ofString "increment_nonce") K.increment_nonce)
    (h_mark_account_created : TerminatingFunBoundedOn GuestInv (ofString "mark_account_created") K.mark_account_created) :
    TerminatingFunBoundedOn GuestInv (ofString "start_child") K.start_child := by
  have _ := h_destroy_storage
  have _ := h_mark_account_created
  have _ := h_increment_nonce
  have _ := h_frame_open
  have _ := h_frame_start
  fg_prove 585 Guest.Software.guestFn_start_child K.start_child

theorem fb_tx_bytes_item_of
    (h_rlp_item : TerminatingFunBoundedOn GuestInv (ofString "rlp_item") K.rlp_item) :
    TerminatingFunBoundedOn GuestInv (ofString "tx_bytes_item") K.tx_bytes_item := by
  have _ := h_rlp_item
  fg_prove 299 Guest.Software.guestFn_tx_bytes_item K.tx_bytes_item

end InitECandidate.Solver.Wave8GuestInv.FastGen
