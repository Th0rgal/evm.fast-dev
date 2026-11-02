import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.Common

set_option autoImplicit false
set_option maxRecDepth 100000

namespace InitECandidate.Solver.Wave8Contracts.M18

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

/-- `validate_transaction` (AST index 346, line 12639): read-only. -/
theorem «ro_validate_transaction» : ReadOnlyFn (ofString "validate_transaction") :=
  readOnlyFn_of_guestAst 346 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_validate_transaction rfl
    m18Callees m18Callees_good rfl

end InitECandidate.Solver.Wave8Contracts.M18
