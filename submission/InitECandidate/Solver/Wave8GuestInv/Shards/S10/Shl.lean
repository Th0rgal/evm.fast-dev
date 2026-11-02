import InitECandidate.Solver.Wave8GuestInv.Shards.S10.Helpers

set_option maxRecDepth 1000000

namespace InitECandidate.Solver.Wave8Leaves.S10

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8GuestInv InitECandidate.Solver.PanTerminatingBounded

theorem fb_op_shl
    (h_stack_pop : TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop»)
    (h_charge_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (h_sat_word : TerminatingFunBoundedOn GuestInv (ofString "sat_word") K.«sat_word»)
    (h_u256_shl : TerminatingFunBoundedOn GuestInv (ofString "u256_shl") K.«u256_shl»)
    (h_stack_push : TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push»)
    (h_pc_add : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») :
    TerminatingFunBoundedOn GuestInv (ofString "op_shl") K.«op_shl» := by
  fb_unfold 497 Guest.Software.guestFn_op_shl
  apply TerminatingProgBoundedOn.weaken'
  · apply decCall_guestInv'
    · exact h_stack_pop
    · apply decCall_guestInv'
      · exact h_stack_pop
      · apply TerminatingProgBoundedOn.seq_guestInv
        · apply call_guestInv'
          exact h_charge_gas
        · apply decCall_guestInv'
          · exact h_sat_word
          · apply decCall_guestInv'
            · exact h_u256_shl
            · apply TerminatingProgBoundedOn.seq_guestInv
              · apply call_guestInv'
                exact h_stack_push
              · apply TerminatingProgBoundedOn.seq_guestInv
                · apply call_guestInv'
                  exact h_pc_add
                · exact straightOn _ rfl
  · fb_arith K.«op_shl»

example : type_of% fb_op_shl = (
    (TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop») →
    (TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas») →
    (TerminatingFunBoundedOn GuestInv (ofString "sat_word") K.«sat_word») →
    (TerminatingFunBoundedOn GuestInv (ofString "u256_shl") K.«u256_shl») →
    (TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push») →
    (TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») →
      TerminatingFunBoundedOn GuestInv (ofString "op_shl") K.«op_shl») := rfl

end InitECandidate.Solver.Wave8Leaves.S10
