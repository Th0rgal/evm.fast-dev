import InitECandidate.Solver.Wave8GuestInv.Shards.S00.Core

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.S00
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8Leaves.S00Spec

theorem fb_trie_lookup
    (h_key_to_nibbles : TerminatingFunBoundedOn GuestInv (ofString "key_to_nibbles") K.«key_to_nibbles»)
    (h_trie_walk : TerminatingFunBoundedOn GuestInv (ofString "trie_walk") K.«trie_walk») :
    TerminatingFunBoundedOn GuestInv (ofString "trie_lookup") K.«trie_lookup» := by
  fb_prove 267 Guest.Software.guestFn_trie_lookup K.«trie_lookup»


end InitECandidate.Solver.Wave8Leaves.S00
