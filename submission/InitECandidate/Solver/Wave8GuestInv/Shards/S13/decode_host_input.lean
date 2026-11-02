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

theorem fb_decode_host_input
    (h_decode_stateless_input : TerminatingFunBoundedOn GuestInv (ofString "decode_stateless_input") K.«decode_stateless_input»)
    (h_input_blob : TerminatingFunBoundedOn GuestInv (ofString "input_blob") K.«input_blob»)
    (h_precheck_host_ssz_header : TerminatingFunBoundedOn GuestInv (ofString "precheck_host_ssz_header") K.«precheck_host_ssz_header») :
    TerminatingFunBoundedOn GuestInv (ofString "decode_host_input") K.«decode_host_input» := by
  apply onFun_le 200 (by rw [guestAst_len]; decide) Guest.Software.guestFn_decode_host_input _ rfl
  · htab_unfold Guest.Software.guestFn_decode_host_input
    htab_walk
  · htab_bound K.«decode_host_input»

example : type_of% (fb_decode_host_input (GuestInv := GuestInv)) =
    ((TerminatingFunBoundedOn GuestInv (ofString "decode_stateless_input") K.«decode_stateless_input») →
    (TerminatingFunBoundedOn GuestInv (ofString "input_blob") K.«input_blob») →
    (TerminatingFunBoundedOn GuestInv (ofString "precheck_host_ssz_header") K.«precheck_host_ssz_header») →
    TerminatingFunBoundedOn GuestInv (ofString "decode_host_input") K.«decode_host_input») := rfl


end InitECandidate.Solver.Wave8Leaves.S13
