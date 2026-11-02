import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.Common

set_option autoImplicit false
set_option maxRecDepth 100000

namespace InitECandidate.Solver.Wave8Contracts.M18

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

/-- `u256_is_zero` (AST index 42, line 814): read-only. -/
theorem «ro_u256_is_zero» : ReadOnlyFn (ofString "u256_is_zero") :=
  readOnlyFn_of_guestAst 42 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_is_zero rfl
    (fun _ => false) (fun _ h => by cases h) rfl

end InitECandidate.Solver.Wave8Contracts.M18
