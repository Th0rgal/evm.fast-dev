import InitECandidate.Solver.Wave8GuestInv.Shards.S04.Base
import InitECandidate.Solver.Wave8GuestInv.Shards.S04.CounterSignedUpOn

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Leaves.S04.Base

open InitECandidate.Solver.Wave8Leaves.S04.Light.Arith

-- Structural counterpart of the reused CounterAdd constructors.
syntax "s04_counter_add" : tactic
macro_rules
  | `(tactic| s04_counter_add) => `(tactic| first
      | exact CounterAdd.assign _ _
      | (apply CounterAdd.seq
         · rfl
         · rfl
         · s04_counter_add)
      | (apply CounterAdd.dec
         · decide
         · s04_counter_add)
      | (apply CounterAdd.decCall
         · decide
         · s04_counter_add))

macro_rules
  | `(tactic| s04_fb_auto) => `(tactic|
      (apply while_up_signed_one_on
       · s04_fb_auto
       · s04_counter_add))

end InitECandidate.Solver.Wave8Leaves.S04.Base
