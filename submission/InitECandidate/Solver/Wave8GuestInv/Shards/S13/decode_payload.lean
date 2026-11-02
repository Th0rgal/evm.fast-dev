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

theorem fb_decode_payload
    (h_alloc : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (h_ssz_check_offsets : TerminatingFunBoundedOn GuestInv (ofString "ssz_check_offsets") K.«ssz_check_offsets»)
    (h_ssz_fail : TerminatingFunBoundedOn GuestInv (ofString "ssz_fail") K.«ssz_fail»)
    (h_ssz_fixed_list_count : TerminatingFunBoundedOn GuestInv (ofString "ssz_fixed_list_count") K.«ssz_fixed_list_count»)
    (h_ssz_split_var_list : TerminatingFunBoundedOn GuestInv (ofString "ssz_split_var_list") K.«ssz_split_var_list») :
    TerminatingFunBoundedOn GuestInv (ofString "decode_payload") K.«decode_payload» := by
  apply onFun_le 204 (by rw [guestAst_len]; decide) Guest.Software.guestFn_decode_payload _ rfl
  · htab_unfold Guest.Software.guestFn_decode_payload
    htab_walk
  · htab_bound K.«decode_payload»

example : type_of% (fb_decode_payload (GuestInv := GuestInv)) =
    ((TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc») →
    (TerminatingFunBoundedOn GuestInv (ofString "ssz_check_offsets") K.«ssz_check_offsets») →
    (TerminatingFunBoundedOn GuestInv (ofString "ssz_fail") K.«ssz_fail») →
    (TerminatingFunBoundedOn GuestInv (ofString "ssz_fixed_list_count") K.«ssz_fixed_list_count») →
    (TerminatingFunBoundedOn GuestInv (ofString "ssz_split_var_list") K.«ssz_split_var_list») →
    TerminatingFunBoundedOn GuestInv (ofString "decode_payload") K.«decode_payload») := rfl


end InitECandidate.Solver.Wave8Leaves.S13
