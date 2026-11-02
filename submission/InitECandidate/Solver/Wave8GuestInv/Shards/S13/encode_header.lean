import InitECandidate.Solver.Wave8GuestInv.Shards.S13.Base

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

attribute [local irreducible] K.alloc K.rlp_encode_bytes K.rlp_encode_list_header K.rlp_encode_word K.rlp_list_header_len K.rlp_put_u256

theorem fb_encode_header
    (h_alloc : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (h_rlp_encode_bytes : TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_bytes") K.«rlp_encode_bytes»)
    (h_rlp_encode_list_header : TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_list_header") K.«rlp_encode_list_header»)
    (h_rlp_encode_word : TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_word") K.«rlp_encode_word»)
    (h_rlp_list_header_len : TerminatingFunBoundedOn GuestInv (ofString "rlp_list_header_len") K.«rlp_list_header_len»)
    (h_rlp_put_u256 : TerminatingFunBoundedOn GuestInv (ofString "rlp_put_u256") K.«rlp_put_u256») :
    TerminatingFunBoundedOn GuestInv (ofString "encode_header") K.«encode_header» := by
  apply onFun_le 229 (by rw [guestAst_len]; decide) Guest.Software.guestFn_encode_header _ rfl
  · htab_unfold Guest.Software.guestFn_encode_header
    htab_walk
  · simp only [K.encode_header, Nat.add_zero, Nat.zero_add, Nat.add_assoc,
      Nat.max_zero, Nat.zero_max, Nat.max_self]
    omega

example : type_of% (fb_encode_header (GuestInv := GuestInv)) =
    ((TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc») →
    (TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_bytes") K.«rlp_encode_bytes») →
    (TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_list_header") K.«rlp_encode_list_header») →
    (TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_word") K.«rlp_encode_word») →
    (TerminatingFunBoundedOn GuestInv (ofString "rlp_list_header_len") K.«rlp_list_header_len») →
    (TerminatingFunBoundedOn GuestInv (ofString "rlp_put_u256") K.«rlp_put_u256») →
    TerminatingFunBoundedOn GuestInv (ofString "encode_header") K.«encode_header») := rfl

#print axioms fb_encode_header

end InitECandidate.Solver.Wave8Leaves.S13
