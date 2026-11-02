import InitECandidate.Solver.Wave8GuestInv.Shards.S10.Helpers

set_option maxRecDepth 1000000

namespace InitECandidate.Solver.Wave8Leaves.S10

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8GuestInv InitECandidate.Solver.PanTerminatingBounded

/-- `op_stop` (AST line 16052): one direct call and straight-line state update. -/
theorem fb_op_stop
    (h_pc_add : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») :
    TerminatingFunBoundedOn GuestInv (ofString "op_stop") K.«op_stop» := by
  fb_unfold 502 Guest.Software.guestFn_op_stop
  apply TerminatingProgBoundedOn.weaken'
  · apply TerminatingProgBoundedOn.seq_guestInv
    · exact straightOn _ rfl
    · apply TerminatingProgBoundedOn.seq_guestInv
      · apply call_guestInv'
        exact h_pc_add
      · exact straightOn _ rfl
  · fb_arith K.«op_stop»

example : type_of% fb_op_stop = (
    (TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») →
      TerminatingFunBoundedOn GuestInv (ofString "op_stop") K.«op_stop») := rfl

end InitECandidate.Solver.Wave8Leaves.S10
