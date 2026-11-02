import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.Common

set_option autoImplicit false
set_option maxRecDepth 100000

namespace InitECandidate.Solver.Wave8Contracts.M15

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

/-- `htab_has` (AST index 133, line 5022): read-only. -/
theorem «ro_htab_has» : ReadOnlyFn (ofString "htab_has") :=
  readOnlyFn_of_guestAst 133 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htab_has rfl
    htabGetCallees htabGetCallees_good rfl

end InitECandidate.Solver.Wave8Contracts.M15
