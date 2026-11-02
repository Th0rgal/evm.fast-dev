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

theorem fb_ec_set_infinity :
    TerminatingFunBoundedOn GuestInv (ofString "ec_set_infinity") K.ec_set_infinity := by
  fg_prove 167 Guest.Software.guestFn_ec_set_infinity K.ec_set_infinity

theorem fb_encode_account
    (h_rlp_encode_bytes : TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_bytes") K.rlp_encode_bytes)
    (h_rlp_encode_word : TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_word") K.rlp_encode_word) :
    TerminatingFunBoundedOn GuestInv (ofString "encode_account") K.encode_account := by
  have _ := h_rlp_encode_word
  have _ := h_rlp_encode_bytes
  fg_unfold 294 Guest.Software.guestFn_encode_account
  apply TerminatingProgBoundedOn.weaken'
  · fg_auto_loops
    · apply while_up_unsigned_const_guestInv (ofString "z") (BitVec.ofNat 64 32)
      · fg_auto
      · refine CounterStep.seq _ _ _ rfl rfl ?_; exact CounterStep.assign _ 1#64
  · fg_arith K.encode_account

theorem fb_fe_eq_of
    (h_memeq : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.memeq) :
    TerminatingFunBoundedOn GuestInv (ofString "fe_eq") K.fe_eq := by
  have _ := h_memeq
  fg_prove 668 Guest.Software.guestFn_fe_eq K.fe_eq

theorem fb_fe_set_one :
    TerminatingFunBoundedOn GuestInv (ofString "fe_set_one") K.fe_set_one := by
  fg_prove 670 Guest.Software.guestFn_fe_set_one K.fe_set_one

theorem fb_fe_set_zero :
    TerminatingFunBoundedOn GuestInv (ofString "fe_set_zero") K.fe_set_zero := by
  fg_prove 669 Guest.Software.guestFn_fe_set_zero K.fe_set_zero

theorem fb_fn_inv_of
    (h_modinv_bin : TerminatingFunBoundedOn GuestInv (ofString "modinv_bin") K.modinv_bin) :
    TerminatingFunBoundedOn GuestInv (ofString "fn_inv") K.fn_inv := by
  have _ := h_modinv_bin
  fg_prove 166 Guest.Software.guestFn_fn_inv K.fn_inv

theorem fb_fp12_copy :
    TerminatingFunBoundedOn GuestInv (ofString "fp12_copy") K.fp12_copy := by
  fg_prove 747 Guest.Software.guestFn_fp12_copy K.fp12_copy

theorem fb_fp2_copy :
    TerminatingFunBoundedOn GuestInv (ofString "fp2_copy") K.fp2_copy := by
  fg_prove 721 Guest.Software.guestFn_fp2_copy K.fp2_copy

end InitECandidate.Solver.Wave8GuestInv.FastGen
