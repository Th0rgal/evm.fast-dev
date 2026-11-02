import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.Common

set_option autoImplicit false
set_option maxRecDepth 100000

namespace InitECandidate.Solver.Wave8Contracts.M15

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

/-- `min` (AST index 31, line 667): read-only. -/
theorem «ro_min» : ReadOnlyFn (ofString "min") :=
  readOnlyFn_of_guestAst 31 (by rw [guestAst_len]; decide) Guest.Software.guestFn_min rfl
    (fun _ => false) (fun _ h => by cases h) rfl

end InitECandidate.Solver.Wave8Contracts.M15
