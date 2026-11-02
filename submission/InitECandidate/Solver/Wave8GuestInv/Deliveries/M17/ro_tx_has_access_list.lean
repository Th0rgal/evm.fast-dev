import InitECandidate.Solver.Wave8GuestInv.Deliveries.M17.Core

/-! Proof of `ro_tx_has_access_list` (`tx_has_access_list`, `Guest/SoftwareAst.lean:11890`, `guestAst[315]`). -/

set_option autoImplicit false
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8GuestInv.M17

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

theorem ro_tx_has_access_list : ReadOnlyFn (ofString "tx_has_access_list") :=
  readOnlyFn_of_guestAst_pure 315 Guest.Software.guestFn_tx_has_access_list
    (by rw [guestAst_len]; decide) rfl (by decide)

end InitECandidate.Solver.Wave8GuestInv.M17
