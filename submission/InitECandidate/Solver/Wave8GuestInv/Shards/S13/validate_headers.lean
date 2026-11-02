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

theorem fb_validate_headers
    (h_alloc : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (h_decode_header : TerminatingFunBoundedOn GuestInv (ofString "decode_header") K.«decode_header»)
    (h_keccak256 : TerminatingFunBoundedOn GuestInv (ofString "keccak256") K.«keccak256»)
    (h_memeq : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq») :
    TerminatingFunBoundedOn GuestInv (ofString "validate_headers") K.«validate_headers» := by
  apply onFun_le 231 (by rw [guestAst_len]; decide) Guest.Software.guestFn_validate_headers _ rfl
  · htab_unfold Guest.Software.guestFn_validate_headers
    s13_walk
  · htab_bound K.«validate_headers»

example : type_of% (fb_validate_headers (GuestInv := GuestInv)) =
    ((TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc») →
    (TerminatingFunBoundedOn GuestInv (ofString "decode_header") K.«decode_header») →
    (TerminatingFunBoundedOn GuestInv (ofString "keccak256") K.«keccak256») →
    (TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq») →
    TerminatingFunBoundedOn GuestInv (ofString "validate_headers") K.«validate_headers») := rfl

#print axioms fb_validate_headers

end InitECandidate.Solver.Wave8Leaves.S13
