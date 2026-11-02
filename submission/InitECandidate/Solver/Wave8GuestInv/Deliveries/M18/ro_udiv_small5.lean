import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.Common

set_option autoImplicit false
set_option maxRecDepth 100000

namespace InitECandidate.Solver.Wave8Contracts.M18

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

/-- `udiv_small5` (AST index 874, line 33447): read-only. -/
theorem «ro_udiv_small5» : ReadOnlyFn (ofString "udiv_small5") :=
  readOnlyFn_of_guestAst 874 (by rw [guestAst_len]; decide) Guest.Software.guestFn_udiv_small5 rfl
    m18Callees m18Callees_good rfl

end InitECandidate.Solver.Wave8Contracts.M18
