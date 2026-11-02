import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.Common

set_option autoImplicit false
set_option maxRecDepth 100000

namespace InitECandidate.Solver.Wave8Contracts.M15

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

/-- `htab_get` (AST index 132, line 4999): read-only. -/
theorem «ro_htab_get» : ReadOnlyFn (ofString "htab_get") :=
  readOnlyFn_of_guestAst 132 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htab_get rfl
    htabGetCallees htabGetCallees_good rfl

end InitECandidate.Solver.Wave8Contracts.M15
