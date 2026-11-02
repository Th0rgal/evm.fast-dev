import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.Common

set_option autoImplicit false
set_option maxRecDepth 100000

namespace InitECandidate.Solver.Wave8Contracts.M15

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

/-- `htab_item` (AST index 143, line 5314): read-only. -/
theorem «ro_htab_item» : ReadOnlyFn (ofString "htab_item") :=
  readOnlyFn_of_guestAst 143 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htab_item rfl
    (fun _ => false) (fun _ h => by cases h) rfl

end InitECandidate.Solver.Wave8Contracts.M15
