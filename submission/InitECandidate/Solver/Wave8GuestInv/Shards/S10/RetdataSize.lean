import InitECandidate.Solver.Wave8GuestInv.Shards.S10.Helpers

set_option maxRecDepth 1000000

namespace InitECandidate.Solver.Wave8Leaves.S10

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8GuestInv InitECandidate.Solver.PanTerminatingBounded

theorem fb_op_returndatasize
    (h_charge_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (h_stack_push_word : TerminatingFunBoundedOn GuestInv (ofString "stack_push_word") K.«stack_push_word»)
    (h_pc_add : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») :
    TerminatingFunBoundedOn GuestInv (ofString "op_returndatasize") K.«op_returndatasize» := by
  fb_unfold 546 Guest.Software.guestFn_op_returndatasize
  apply TerminatingProgBoundedOn.weaken'
  · apply TerminatingProgBoundedOn.seq_guestInv
    · apply call_guestInv'
      exact h_charge_gas
    · apply TerminatingProgBoundedOn.seq_guestInv
      · apply call_guestInv'
        exact h_stack_push_word
      · apply TerminatingProgBoundedOn.seq_guestInv
        · apply call_guestInv'
          exact h_pc_add
        · exact straightOn _ rfl
  · fb_arith K.«op_returndatasize»

example : type_of% fb_op_returndatasize = (
    (TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas») →
    (TerminatingFunBoundedOn GuestInv (ofString "stack_push_word") K.«stack_push_word») →
    (TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») →
      TerminatingFunBoundedOn GuestInv (ofString "op_returndatasize") K.«op_returndatasize») := rfl

end InitECandidate.Solver.Wave8Leaves.S10
