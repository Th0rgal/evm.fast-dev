import InitECandidate.Solver.Wave8GuestInv.Deliveries.M17.Core

/-! Proof of `ro_tx_is_setcode` (`tx_is_setcode`, `Guest/SoftwareAst.lean:32764`, `guestAst[866]`). -/

set_option autoImplicit false
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8GuestInv.M17

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

theorem ro_tx_is_setcode : ReadOnlyFn (ofString "tx_is_setcode") :=
  readOnlyFn_of_guestAst_pure 866 Guest.Software.guestFn_tx_is_setcode
    (by rw [guestAst_len]; decide) rfl (by decide)

end InitECandidate.Solver.Wave8GuestInv.M17
