import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.Common

set_option autoImplicit false
set_option maxRecDepth 100000

namespace InitECandidate.Solver.Wave8Contracts.M18

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

/-- `validate_block_access_list_gas_limit` (AST index 434, line 14776): read-only. -/
theorem «ro_validate_block_access_list_gas_limit» :
    ReadOnlyFn (ofString "validate_block_access_list_gas_limit") :=
  readOnlyFn_of_guestAst 434 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_validate_block_access_list_gas_limit rfl
    m18Callees m18Callees_good rfl

end InitECandidate.Solver.Wave8Contracts.M18
