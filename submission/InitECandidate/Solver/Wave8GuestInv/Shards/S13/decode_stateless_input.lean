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

theorem fb_decode_stateless_input
    (h_alloc : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (h_decode_bytes_list : TerminatingFunBoundedOn GuestInv (ofString "decode_bytes_list") K.«decode_bytes_list»)
    (h_decode_payload : TerminatingFunBoundedOn GuestInv (ofString "decode_payload") K.«decode_payload»)
    (h_decode_requests : TerminatingFunBoundedOn GuestInv (ofString "decode_requests") K.«decode_requests»)
    (h_ssz_check_offsets : TerminatingFunBoundedOn GuestInv (ofString "ssz_check_offsets") K.«ssz_check_offsets»)
    (h_ssz_fail : TerminatingFunBoundedOn GuestInv (ofString "ssz_fail") K.«ssz_fail»)
    (h_ssz_fixed_list_count : TerminatingFunBoundedOn GuestInv (ofString "ssz_fixed_list_count") K.«ssz_fixed_list_count») :
    TerminatingFunBoundedOn GuestInv (ofString "decode_stateless_input") K.«decode_stateless_input» := by
  apply onFun_le 207 (by rw [guestAst_len]; decide) Guest.Software.guestFn_decode_stateless_input _ rfl
  · htab_unfold Guest.Software.guestFn_decode_stateless_input
    s13_walk
  · htab_bound K.«decode_stateless_input»

example : type_of% (fb_decode_stateless_input (GuestInv := GuestInv)) =
    ((TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc») →
    (TerminatingFunBoundedOn GuestInv (ofString "decode_bytes_list") K.«decode_bytes_list») →
    (TerminatingFunBoundedOn GuestInv (ofString "decode_payload") K.«decode_payload») →
    (TerminatingFunBoundedOn GuestInv (ofString "decode_requests") K.«decode_requests») →
    (TerminatingFunBoundedOn GuestInv (ofString "ssz_check_offsets") K.«ssz_check_offsets») →
    (TerminatingFunBoundedOn GuestInv (ofString "ssz_fail") K.«ssz_fail») →
    (TerminatingFunBoundedOn GuestInv (ofString "ssz_fixed_list_count") K.«ssz_fixed_list_count») →
    TerminatingFunBoundedOn GuestInv (ofString "decode_stateless_input") K.«decode_stateless_input») := rfl

#print axioms fb_decode_stateless_input

end InitECandidate.Solver.Wave8Leaves.S13
