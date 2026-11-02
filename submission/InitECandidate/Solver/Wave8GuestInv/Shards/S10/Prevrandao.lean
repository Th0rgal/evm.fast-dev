import InitECandidate.Solver.Wave8GuestInv.Shards.S10.Helpers

set_option maxRecDepth 1000000

namespace InitECandidate.Solver.Wave8Leaves.S10

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8GuestInv InitECandidate.Solver.PanTerminatingBounded

theorem fb_op_prevrandao
    (h_charge_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (h_block_env : TerminatingFunBoundedOn GuestInv (ofString "block_env") K.«block_env»)
    (h_u256_from_be : TerminatingFunBoundedOn GuestInv (ofString "u256_from_be") K.«u256_from_be»)
    (h_stack_push : TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push»)
    (h_pc_add : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») :
    TerminatingFunBoundedOn GuestInv (ofString "op_prevrandao") K.«op_prevrandao» := by
  fb_unfold 560 Guest.Software.guestFn_op_prevrandao
  apply TerminatingProgBoundedOn.weaken'
  · apply TerminatingProgBoundedOn.seq_guestInv
    · apply call_guestInv'
      exact h_charge_gas
    · apply decCall_guestInv'
      · exact h_block_env
      · apply decCall_guestInv'
        · exact h_u256_from_be
        · apply TerminatingProgBoundedOn.seq_guestInv
          · apply call_guestInv'
            exact h_stack_push
          · apply TerminatingProgBoundedOn.seq_guestInv
            · apply call_guestInv'
              exact h_pc_add
            · exact straightOn _ rfl
  · fb_arith K.«op_prevrandao»

example : type_of% fb_op_prevrandao = (
    (TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas») →
    (TerminatingFunBoundedOn GuestInv (ofString "block_env") K.«block_env») →
    (TerminatingFunBoundedOn GuestInv (ofString "u256_from_be") K.«u256_from_be») →
    (TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push») →
    (TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») →
      TerminatingFunBoundedOn GuestInv (ofString "op_prevrandao") K.«op_prevrandao») := rfl

end InitECandidate.Solver.Wave8Leaves.S10
