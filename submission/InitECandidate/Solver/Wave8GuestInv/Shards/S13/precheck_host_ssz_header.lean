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

theorem fb_precheck_host_ssz_header
    (h_host_input_byte : TerminatingFunBoundedOn GuestInv (ofString "host_input_byte") K.«host_input_byte»)
    (h_host_input_le32 : TerminatingFunBoundedOn GuestInv (ofString "host_input_le32") K.«host_input_le32»)
    (h_ssz_check_offsets : TerminatingFunBoundedOn GuestInv (ofString "ssz_check_offsets") K.«ssz_check_offsets»)
    (h_ssz_fail : TerminatingFunBoundedOn GuestInv (ofString "ssz_fail") K.«ssz_fail») :
    TerminatingFunBoundedOn GuestInv (ofString "precheck_host_ssz_header") K.«precheck_host_ssz_header» := by
  apply onFun_le 199 (by rw [guestAst_len]; decide) Guest.Software.guestFn_precheck_host_ssz_header _ rfl
  · htab_unfold Guest.Software.guestFn_precheck_host_ssz_header
    htab_walk
  · htab_bound K.«precheck_host_ssz_header»

example : type_of% (fb_precheck_host_ssz_header (GuestInv := GuestInv)) =
    ((TerminatingFunBoundedOn GuestInv (ofString "host_input_byte") K.«host_input_byte») →
    (TerminatingFunBoundedOn GuestInv (ofString "host_input_le32") K.«host_input_le32») →
    (TerminatingFunBoundedOn GuestInv (ofString "ssz_check_offsets") K.«ssz_check_offsets») →
    (TerminatingFunBoundedOn GuestInv (ofString "ssz_fail") K.«ssz_fail») →
    TerminatingFunBoundedOn GuestInv (ofString "precheck_host_ssz_header") K.«precheck_host_ssz_header») := rfl

#print axioms fb_precheck_host_ssz_header

end InitECandidate.Solver.Wave8Leaves.S13
