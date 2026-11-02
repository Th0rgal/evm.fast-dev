import InitECandidate.Solver.Wave8GuestInv.Shards.S00.Core

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.S00
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8Leaves.S00Spec

theorem fb_nodedb_lookup
    (h_htab_get : TerminatingFunBoundedOn GuestInv (ofString "htab_get") K.«htab_get») :
    TerminatingFunBoundedOn GuestInv (ofString "nodedb_lookup") K.«nodedb_lookup» := by
  fb_prove 254 Guest.Software.guestFn_nodedb_lookup K.«nodedb_lookup»


end InitECandidate.Solver.Wave8Leaves.S00
