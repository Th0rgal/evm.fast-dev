import InitECandidate.Solver.Wave8GuestInv.Deliveries.RLP.RlpStack

set_option autoImplicit false

namespace InitECandidate.Solver.Wave8Leaves.Rlp

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8GuestInv

theorem «fb_rlp_validate_items» :
    TerminatingFunBoundedOn GuestInv (ofString "rlp_validate_items") K.«rlp_validate_items» :=
  InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.fb_rlp_validate_items

theorem «fb_rlp_item_total» :
    TerminatingFunBoundedOn GuestInv (ofString "rlp_item_total") K.«rlp_item_total» :=
  InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.fb_rlp_item_total

end InitECandidate.Solver.Wave8Leaves.Rlp
