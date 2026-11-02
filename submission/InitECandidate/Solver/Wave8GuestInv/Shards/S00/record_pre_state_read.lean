import InitECandidate.Solver.Wave8GuestInv.Shards.S00.Core

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.S00
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8Leaves.S00Spec

theorem fb_record_pre_state_read
    (h_htab_set : TerminatingFunBoundedOn GuestInv (ofString "htab_set") K.«htab_set») :
    TerminatingFunBoundedOn GuestInv (ofString "record_pre_state_read") K.«record_pre_state_read» := by
  fb_prove 364 Guest.Software.guestFn_record_pre_state_read K.«record_pre_state_read»


end InitECandidate.Solver.Wave8Leaves.S00
