import InitECandidate.Solver.Wave8GuestInv.Deliveries.M17.Core

/-! Proof of `ro_u256_eq` (`u256_eq`, `Guest/SoftwareAst.lean:869`, `guestAst[45]`). -/

set_option autoImplicit false
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8GuestInv.M17

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

theorem ro_u256_eq : ReadOnlyFn (ofString "u256_eq") :=
  readOnlyFn_of_guestAst_pure 45 Guest.Software.guestFn_u256_eq
    (by rw [guestAst_len]; decide) rfl (by decide)

end InitECandidate.Solver.Wave8GuestInv.M17
