import InitECandidate.Solver.Wave8GuestInv.Deliveries.RLP.RlpStack

/-! RLP / byte-decoding family, part 10: RLP item validation built on `_rlp_validate_items_body`. -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.Rlp

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8GuestInv InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.PanTerminatingCombinators

/-- `rlp_validate_items` (AST line 4548): loop-free (call with `RlpErr` handler). -/
theorem «fb_rlp_validate_items» :
    TerminatingFunBoundedOn GuestInv (ofString "rlp_validate_items") K.«rlp_validate_items» := by
  fb_prove 111 Guest.Software.guestFn_rlp_validate_items K.«rlp_validate_items»

/-- `rlp_item_total` (AST line 4567): loop-free. -/
theorem «fb_rlp_item_total» :
    TerminatingFunBoundedOn GuestInv (ofString "rlp_item_total") K.«rlp_item_total» := by
  fb_prove 112 Guest.Software.guestFn_rlp_item_total K.«rlp_item_total»


end InitECandidate.Solver.Wave8Leaves.Rlp
