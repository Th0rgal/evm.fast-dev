import InitECandidate.Solver.Wave8GuestInv.Deliveries.M17.Core

/-! Proof of `ro_tx_is_blob` (`tx_is_blob`, `Guest/SoftwareAst.lean:32750`, `guestAst[865]`). -/

set_option autoImplicit false
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8GuestInv.M17

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

theorem ro_tx_is_blob : ReadOnlyFn (ofString "tx_is_blob") :=
  readOnlyFn_of_guestAst_pure 865 Guest.Software.guestFn_tx_is_blob
    (by rw [guestAst_len]; decide) rfl (by decide)

end InitECandidate.Solver.Wave8GuestInv.M17
