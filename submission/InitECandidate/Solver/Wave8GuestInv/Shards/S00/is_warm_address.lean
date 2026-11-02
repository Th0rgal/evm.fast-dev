import InitECandidate.Solver.Wave8GuestInv.Shards.S00.Core

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.S00
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8Leaves.S00Spec

theorem fb_is_warm_address
    (h_htab_has : TerminatingFunBoundedOn GuestInv (ofString "htab_has") K.«htab_has») :
    TerminatingFunBoundedOn GuestInv (ofString "is_warm_address") K.«is_warm_address» := by
  fb_prove 471 Guest.Software.guestFn_is_warm_address K.«is_warm_address»


end InitECandidate.Solver.Wave8Leaves.S00
