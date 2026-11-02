import InitECandidate.Solver.Wave8GuestInv.Shards.S13.CounterAuto

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.S13

attribute [local irreducible] InitECandidate.Solver.PanTerminatingBounded.TerminatingProgBoundedOn
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8Leaves.S13.Spec

variable {GuestInv : ∀ {F : Type}, Flapjack.PanSemStateFiniteExact 64 F → Prop}
  [IsGuestInv GuestInv]

open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup

theorem fb_is_valid_versioned_hashes
    (h_decode_transaction : TerminatingFunBoundedOn GuestInv (ofString "decode_transaction") K.«decode_transaction»)
    (h_memeq : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq»)
    (h_tx_is_blob : TerminatingFunBoundedOn GuestInv (ofString "tx_is_blob") K.«tx_is_blob») :
    TerminatingFunBoundedOn GuestInv (ofString "is_valid_versioned_hashes") K.«is_valid_versioned_hashes» := by
  apply onFun_le 868 (by rw [guestAst_len]; decide) Guest.Software.guestFn_is_valid_versioned_hashes _ rfl
  · htab_unfold Guest.Software.guestFn_is_valid_versioned_hashes
    s13_walk
  · htab_bound K.«is_valid_versioned_hashes»

example : type_of% (fb_is_valid_versioned_hashes (GuestInv := GuestInv)) =
    ((TerminatingFunBoundedOn GuestInv (ofString "decode_transaction") K.«decode_transaction») →
    (TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq») →
    (TerminatingFunBoundedOn GuestInv (ofString "tx_is_blob") K.«tx_is_blob») →
    TerminatingFunBoundedOn GuestInv (ofString "is_valid_versioned_hashes") K.«is_valid_versioned_hashes») := rfl

#print axioms fb_is_valid_versioned_hashes

end InitECandidate.Solver.Wave8Leaves.S13
