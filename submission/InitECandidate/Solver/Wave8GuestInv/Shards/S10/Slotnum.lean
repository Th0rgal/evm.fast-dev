import InitECandidate.Solver.Wave8GuestInv.Shards.S10.Helpers

set_option maxRecDepth 1000000

namespace InitECandidate.Solver.Wave8Leaves.S10

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8GuestInv InitECandidate.Solver.PanTerminatingBounded

theorem fb_op_slotnum
    (h_charge_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (h_block_env : TerminatingFunBoundedOn GuestInv (ofString "block_env") K.«block_env»)
    (h_stack_push_word : TerminatingFunBoundedOn GuestInv (ofString "stack_push_word") K.«stack_push_word»)
    (h_pc_add : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») :
    TerminatingFunBoundedOn GuestInv (ofString "op_slotnum") K.«op_slotnum» := by
  fb_unfold 561 Guest.Software.guestFn_op_slotnum
  apply TerminatingProgBoundedOn.weaken'
  · apply TerminatingProgBoundedOn.seq_guestInv
    · apply call_guestInv'
      exact h_charge_gas
    · apply decCall_guestInv'
      · exact h_block_env
      · apply TerminatingProgBoundedOn.seq_guestInv
        · apply call_guestInv'
          exact h_stack_push_word
        · apply TerminatingProgBoundedOn.seq_guestInv
          · apply call_guestInv'
            exact h_pc_add
          · exact straightOn _ rfl
  · fb_arith K.«op_slotnum»

example : type_of% fb_op_slotnum = (
    (TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas») →
    (TerminatingFunBoundedOn GuestInv (ofString "block_env") K.«block_env») →
    (TerminatingFunBoundedOn GuestInv (ofString "stack_push_word") K.«stack_push_word») →
    (TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») →
      TerminatingFunBoundedOn GuestInv (ofString "op_slotnum") K.«op_slotnum») := rfl

end InitECandidate.Solver.Wave8Leaves.S10
