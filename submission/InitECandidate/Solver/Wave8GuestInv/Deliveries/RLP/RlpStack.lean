import InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.FbRlp

set_option autoImplicit false

namespace InitECandidate.Solver.Wave8Leaves.Rlp

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8GuestInv

theorem «fb__rlp_validate_items_body» : TerminatingFunBoundedOn GuestInv
    (ofString "_rlp_validate_items_body") K.«_rlp_validate_items_body» :=
  InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.fb__rlp_validate_items_body

end InitECandidate.Solver.Wave8Leaves.Rlp
