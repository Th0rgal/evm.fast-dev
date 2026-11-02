import InitECandidate.Solver.Wave8GuestInv.Shards.S13.CounterExpr

namespace InitECandidate.Solver.Wave8Leaves.S13
open InitECandidate.Solver.Wave8Leaves.S13.Spec

variable {GuestInv : ∀ {F : Type}, Flapjack.PanSemStateFiniteExact 64 F → Prop}
  [IsGuestInv GuestInv]


-- Adapted from htab/Loops.lean; callee bounds always come from explicit hypotheses.
macro "s13_incr" : tactic => `(tactic| repeat (first
  | exact IncrBody.incr
  | apply IncrBody.dec _ _ _ (by decide)
  | apply IncrBody.decCall _ _ _ _ (by decide)
  | apply IncrBody.seq _ rfl rfl))

syntax "s13_walk" : tactic
macro_rules
  | `(tactic| s13_walk) => `(tactic| first
    | exact straightOn _ rfl
    | (apply TerminatingProgBoundedOn.dec_on localsFree_guestInv; s13_walk)
    | (apply TerminatingProgBoundedOn.seq_guestInv <;> s13_walk)
    | (apply TerminatingProgBoundedOn.ite_on <;> s13_walk)
    | (apply TerminatingProgBoundedOn.decCall_guestInv
       · callee_hyp
       · s13_walk)
    | (apply TerminatingProgBoundedOn.call_guestInv; callee_hyp)
    | (apply TerminatingProgBoundedOn.tailCall_guestInv; callee_hyp)
    | (apply while_counter_expr_guestInv .less (Or.inl rfl)
       · s13_walk
       · s13_incr)
    | (apply while_counter_expr_guestInv .lower (Or.inr rfl)
       · s13_walk
       · s13_incr))

end InitECandidate.Solver.Wave8Leaves.S13
