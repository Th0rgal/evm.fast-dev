import InitECandidate.Solver.Wave8GuestInv.Shards.S00.CounterTactics

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.S00
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8Leaves.S00Spec

theorem fb_access_list_payload_len
    (h_rlp_list_header_len : TerminatingFunBoundedOn GuestInv (ofString "rlp_list_header_len") K.«rlp_list_header_len») :
    TerminatingFunBoundedOn GuestInv (ofString "access_list_payload_len") K.«access_list_payload_len» := by
  fb_unfold 321 Guest.Software.guestFn_access_list_payload_len
  apply TerminatingProgBoundedOn.weaken'
  · fb_counter_auto
  · fb_arith K.«access_list_payload_len»


end InitECandidate.Solver.Wave8Leaves.S00
