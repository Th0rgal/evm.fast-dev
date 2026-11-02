import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.Common

set_option autoImplicit false
set_option maxRecDepth 100000

namespace InitECandidate.Solver.Wave8Contracts.M18

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

/-- `u256_mul` (AST index 60, line 1150): read-only. -/
theorem «ro_u256_mul» : ReadOnlyFn (ofString "u256_mul") :=
  readOnlyFn_of_guestAst 60 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_mul rfl
    m18Callees m18Callees_good rfl

end InitECandidate.Solver.Wave8Contracts.M18
