import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.Common

set_option autoImplicit false
set_option maxRecDepth 100000

namespace InitECandidate.Solver.Wave8Contracts.M15

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

/-- `memeq` (AST index 18, line 304): read-only. -/
theorem «ro_memeq» : ReadOnlyFn (ofString "memeq") :=
  readOnlyFn_of_guestAst 18 (by rw [guestAst_len]; decide) Guest.Software.guestFn_memeq rfl
    (fun _ => false) (fun _ h => by cases h) rfl

end InitECandidate.Solver.Wave8Contracts.M15
