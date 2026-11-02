import InitECandidate.Solver.Wave8GuestInv.Shards.S10.Helpers

set_option maxRecDepth 1000000

/-! First routine s10 leaves. -/

namespace InitECandidate.Solver.Wave8Leaves.S10

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8GuestInv InitECandidate.Solver.PanTerminatingBounded

/-- `op_sub` (AST line 15563): stack primitive composition. -/
theorem fb_op_sub
    (h_stack_pop : TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop»)
    (h_charge_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (h_u256_sub : TerminatingFunBoundedOn GuestInv (ofString "u256_sub") K.«u256_sub»)
    (h_stack_push : TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push»)
    (h_pc_add : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») :
    TerminatingFunBoundedOn GuestInv (ofString "op_sub") K.«op_sub» := by
  fb_unfold 477 Guest.Software.guestFn_op_sub
  apply TerminatingProgBoundedOn.weaken'
  · apply decCall_guestInv'
    · exact h_stack_pop
    · apply decCall_guestInv'
      · exact h_stack_pop
      · apply TerminatingProgBoundedOn.seq_guestInv
        · apply call_guestInv'
          exact h_charge_gas
        · apply decCall_guestInv'
          · exact h_u256_sub
          · apply TerminatingProgBoundedOn.seq_guestInv
            · apply call_guestInv'
              exact h_stack_push
            · apply TerminatingProgBoundedOn.seq_guestInv
              · apply call_guestInv'
                exact h_pc_add
              · exact straightOn _ rfl
  · fb_arith K.«op_sub»

example : type_of% fb_op_sub = (
    (TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop») →
    (TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas») →
    (TerminatingFunBoundedOn GuestInv (ofString "u256_sub") K.«u256_sub») →
    (TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push») →
    (TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») →
          TerminatingFunBoundedOn GuestInv (ofString "op_sub") K.«op_sub») := rfl

end InitECandidate.Solver.Wave8Leaves.S10
