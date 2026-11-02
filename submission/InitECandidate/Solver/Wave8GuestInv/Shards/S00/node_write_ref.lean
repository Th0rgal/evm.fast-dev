import InitECandidate.Solver.Wave8GuestInv.Shards.S00.Core

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.S00
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8Leaves.S00Spec

theorem fb_node_write_ref
    (h_memcpy : TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy»)
    (h_mpt_fail : TerminatingFunBoundedOn GuestInv (ofString "mpt_fail") K.«mpt_fail»)
    (h_node_hash_cached : TerminatingFunBoundedOn GuestInv (ofString "node_hash_cached") K.«node_hash_cached») :
    TerminatingFunBoundedOn GuestInv (ofString "node_write_ref") K.«node_write_ref» := by
  fb_prove 289 Guest.Software.guestFn_node_write_ref K.«node_write_ref»


end InitECandidate.Solver.Wave8Leaves.S00
