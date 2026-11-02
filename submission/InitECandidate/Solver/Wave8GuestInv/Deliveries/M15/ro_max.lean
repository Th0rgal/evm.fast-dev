import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.Common

set_option autoImplicit false
set_option maxRecDepth 100000

namespace InitECandidate.Solver.Wave8Contracts.M15

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

/-- `max` (AST index 32, line 681): read-only. -/
theorem «ro_max» : ReadOnlyFn (ofString "max") :=
  readOnlyFn_of_guestAst 32 (by rw [guestAst_len]; decide) Guest.Software.guestFn_max rfl
    (fun _ => false) (fun _ h => by cases h) rfl

end InitECandidate.Solver.Wave8Contracts.M15
