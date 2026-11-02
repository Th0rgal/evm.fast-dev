import InitECandidate.Solver.Wave8GuestInv.Shards.S00.Core

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.S00
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8Leaves.S00Spec

theorem fb_access_gas_cost
    (h_is_warm_address : TerminatingFunBoundedOn GuestInv (ofString "is_warm_address") K.«is_warm_address») :
    TerminatingFunBoundedOn GuestInv (ofString "access_gas_cost") K.«access_gas_cost» := by
  fb_prove 473 Guest.Software.guestFn_access_gas_cost K.«access_gas_cost»


end InitECandidate.Solver.Wave8Leaves.S00
