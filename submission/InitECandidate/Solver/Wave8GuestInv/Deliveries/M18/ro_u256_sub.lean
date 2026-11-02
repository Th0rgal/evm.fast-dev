import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.Common

set_option autoImplicit false
set_option maxRecDepth 100000

namespace InitECandidate.Solver.Wave8Contracts.M18

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

/-- `u256_sub` (AST index 57, line 1083): read-only. -/
theorem «ro_u256_sub» : ReadOnlyFn (ofString "u256_sub") :=
  readOnlyFn_of_guestAst 57 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_sub rfl
    (fun _ => false) (fun _ h => by cases h) rfl

end InitECandidate.Solver.Wave8Contracts.M18
