import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FGCommon
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_02
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_03
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_15
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_19
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_24

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

theorem fb_ec_mul2_of
    (h_ec_to_affine : TerminatingFunBoundedOn GuestInv (ofString "ec_to_affine") K.ec_to_affine) :
    TerminatingFunBoundedOn GuestInv (ofString "ec_mul2") K.ec_mul2 := by
  have _ := fb_ec_set_infinity
  have _ := fb_ec_set_affine
  have _ := fb_ec_add_affine
  have _ := fb_ec_is_infinity
  have _ := h_ec_to_affine
  have _ := fb_ec_double
  fg_unfold 174 Guest.Software.guestFn_ec_mul2
  apply TerminatingProgBoundedOn.weaken'
  · fg_auto_loops
    · apply while_down_unsigned_guestInv (ofString "i")
      · fg_auto
      · refine CounterStep.suffix _ _ _ ?_ rfl; exact CounterStep.sub_one _
  · fg_arith K.ec_mul2

theorem fb_ecp_double_of
    (h_fe_mul : TerminatingFunBoundedOn GuestInv (ofString "fe_mul") K.fe_mul)
    (h_fe_mul_small : TerminatingFunBoundedOn GuestInv (ofString "fe_mul_small") K.fe_mul_small)
    (h_fe_sqr : TerminatingFunBoundedOn GuestInv (ofString "fe_sqr") K.fe_sqr)
    (h_fe_sub : TerminatingFunBoundedOn GuestInv (ofString "fe_sub") K.fe_sub) :
    TerminatingFunBoundedOn GuestInv (ofString "ecp_double") K.ecp_double := by
  have _ := h_fe_sqr
  have _ := h_fe_mul_small
  have _ := h_fe_mul
  have _ := h_fe_sub
  fg_prove 673 Guest.Software.guestFn_ecp_double K.ecp_double

theorem fb_ecp_linefunc_of
    (h_fe_mul : TerminatingFunBoundedOn GuestInv (ofString "fe_mul") K.fe_mul)
    (h_fe_mul_small : TerminatingFunBoundedOn GuestInv (ofString "fe_mul_small") K.fe_mul_small)
    (h_fe_sqr : TerminatingFunBoundedOn GuestInv (ofString "fe_sqr") K.fe_sqr)
    (h_fe_sub : TerminatingFunBoundedOn GuestInv (ofString "fe_sub") K.fe_sub) :
    TerminatingFunBoundedOn GuestInv (ofString "ecp_linefunc") K.ecp_linefunc := by
  have _ := fb_fe_set_zero
  have _ := h_fe_mul
  have _ := h_fe_sub
  have _ := fb_fe_is_zero
  have _ := h_fe_sqr
  have _ := h_fe_mul_small
  fg_prove 676 Guest.Software.guestFn_ecp_linefunc K.ecp_linefunc

theorem fb_p256_verify_of
    (h_modinv_bin : TerminatingFunBoundedOn GuestInv (ofString "modinv_bin") K.modinv_bin)
    (h_p256_ec_mul2 : TerminatingFunBoundedOn GuestInv (ofString "p256_ec_mul2") K.p256_ec_mul2)
    (h_p256_fp_mul : TerminatingFunBoundedOn GuestInv (ofString "p256_fp_mul") K.p256_fp_mul)
    (h_p256_fp_sqr : TerminatingFunBoundedOn GuestInv (ofString "p256_fp_sqr") K.p256_fp_sqr)
    (h_p256_on_curve : TerminatingFunBoundedOn GuestInv (ofString "p256_on_curve") K.p256_on_curve)
    (h_u256_mulmod : TerminatingFunBoundedOn GuestInv (ofString "u256_mulmod") K.u256_mulmod) :
    TerminatingFunBoundedOn GuestInv (ofString "p256_verify") K.p256_verify := by
  have _ := h_p256_on_curve
  have _ := h_modinv_bin
  have _ := h_u256_mulmod
  have _ := h_p256_ec_mul2
  have _ := h_p256_fp_sqr
  have _ := h_p256_fp_mul
  fg_prove 644 Guest.Software.guestFn_p256_verify K.p256_verify

theorem fb_decode_transaction_of
    (h_decode_transaction_rlp : TerminatingFunBoundedOn GuestInv (ofString "decode_transaction_rlp") K.decode_transaction_rlp) :
    TerminatingFunBoundedOn GuestInv (ofString "decode_transaction") K.decode_transaction := by
  have _ := h_decode_transaction_rlp
  fg_prove 307 Guest.Software.guestFn_decode_transaction K.decode_transaction

theorem fb_op_call_of
    (h_calculate_delegation_cost : TerminatingFunBoundedOn GuestInv (ofString "calculate_delegation_cost") K.calculate_delegation_cost)
    (h_charge_state_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_state_gas") K.charge_state_gas)
    (h_credit_state_gas_refund : TerminatingFunBoundedOn GuestInv (ofString "credit_state_gas_refund") K.credit_state_gas_refund)
    (h_ext_code_of : TerminatingFunBoundedOn GuestInv (ofString "ext_code_of") K.ext_code_of)
    (h_generic_call : TerminatingFunBoundedOn GuestInv (ofString "generic_call") K.generic_call)
    (h_get_account : TerminatingFunBoundedOn GuestInv (ofString "get_account") K.get_account)
    (h_is_account_alive : TerminatingFunBoundedOn GuestInv (ofString "is_account_alive") K.is_account_alive)
    (h_is_warm_address : TerminatingFunBoundedOn GuestInv (ofString "is_warm_address") K.is_warm_address)
    (h_set_retdata : TerminatingFunBoundedOn GuestInv (ofString "set_retdata") K.set_retdata)
    (h_to_address_masked : TerminatingFunBoundedOn GuestInv (ofString "to_address_masked") K.to_address_masked)
    (h_warm_address : TerminatingFunBoundedOn GuestInv (ofString "warm_address") K.warm_address) :
    TerminatingFunBoundedOn GuestInv (ofString "op_call") K.op_call := by
  have _ := h_to_address_masked
  have _ := h_is_warm_address
  have _ := h_warm_address
  have _ := h_calculate_delegation_cost
  have _ := h_ext_code_of
  have _ := h_is_account_alive
  have _ := h_charge_state_gas
  have _ := h_get_account
  have _ := h_set_retdata
  have _ := h_credit_state_gas_refund
  have _ := h_generic_call
  fg_prove 603 Guest.Software.guestFn_op_call K.op_call

theorem fb_op_callcode_of
    (h_calculate_delegation_cost : TerminatingFunBoundedOn GuestInv (ofString "calculate_delegation_cost") K.calculate_delegation_cost)
    (h_ext_code_of : TerminatingFunBoundedOn GuestInv (ofString "ext_code_of") K.ext_code_of)
    (h_generic_call : TerminatingFunBoundedOn GuestInv (ofString "generic_call") K.generic_call)
    (h_get_account : TerminatingFunBoundedOn GuestInv (ofString "get_account") K.get_account)
    (h_is_warm_address : TerminatingFunBoundedOn GuestInv (ofString "is_warm_address") K.is_warm_address)
    (h_set_retdata : TerminatingFunBoundedOn GuestInv (ofString "set_retdata") K.set_retdata)
    (h_to_address_masked : TerminatingFunBoundedOn GuestInv (ofString "to_address_masked") K.to_address_masked)
    (h_warm_address : TerminatingFunBoundedOn GuestInv (ofString "warm_address") K.warm_address) :
    TerminatingFunBoundedOn GuestInv (ofString "op_callcode") K.op_callcode := by
  have _ := h_to_address_masked
  have _ := h_is_warm_address
  have _ := h_warm_address
  have _ := h_calculate_delegation_cost
  have _ := h_ext_code_of
  have _ := h_get_account
  have _ := h_set_retdata
  have _ := h_generic_call
  fg_prove 604 Guest.Software.guestFn_op_callcode K.op_callcode

theorem fb_op_staticcall_of
    (h_calculate_delegation_cost : TerminatingFunBoundedOn GuestInv (ofString "calculate_delegation_cost") K.calculate_delegation_cost)
    (h_ext_code_of : TerminatingFunBoundedOn GuestInv (ofString "ext_code_of") K.ext_code_of)
    (h_generic_call : TerminatingFunBoundedOn GuestInv (ofString "generic_call") K.generic_call)
    (h_is_warm_address : TerminatingFunBoundedOn GuestInv (ofString "is_warm_address") K.is_warm_address)
    (h_to_address_masked : TerminatingFunBoundedOn GuestInv (ofString "to_address_masked") K.to_address_masked)
    (h_warm_address : TerminatingFunBoundedOn GuestInv (ofString "warm_address") K.warm_address) :
    TerminatingFunBoundedOn GuestInv (ofString "op_staticcall") K.op_staticcall := by
  have _ := h_to_address_masked
  have _ := h_is_warm_address
  have _ := h_warm_address
  have _ := h_calculate_delegation_cost
  have _ := h_ext_code_of
  have _ := h_generic_call
  fg_prove 606 Guest.Software.guestFn_op_staticcall K.op_staticcall

end InitECandidate.Solver.Wave8GuestInv.FastGen
