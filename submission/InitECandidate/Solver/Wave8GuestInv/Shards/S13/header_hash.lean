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

theorem fb_header_hash
    (h_encode_header : TerminatingFunBoundedOn GuestInv (ofString "encode_header") K.«encode_header»)
    (h_heap_mark : TerminatingFunBoundedOn GuestInv (ofString "heap_mark") K.«heap_mark»)
    (h_heap_release : TerminatingFunBoundedOn GuestInv (ofString "heap_release") K.«heap_release»)
    (h_keccak256 : TerminatingFunBoundedOn GuestInv (ofString "keccak256") K.«keccak256») :
    TerminatingFunBoundedOn GuestInv (ofString "header_hash") K.«header_hash» := by
  apply onFun_le 230 (by rw [guestAst_len]; decide) Guest.Software.guestFn_header_hash _ rfl
  · htab_unfold Guest.Software.guestFn_header_hash
    htab_walk
  · htab_bound K.«header_hash»

example : type_of% (fb_header_hash (GuestInv := GuestInv)) =
    ((TerminatingFunBoundedOn GuestInv (ofString "encode_header") K.«encode_header») →
    (TerminatingFunBoundedOn GuestInv (ofString "heap_mark") K.«heap_mark») →
    (TerminatingFunBoundedOn GuestInv (ofString "heap_release") K.«heap_release») →
    (TerminatingFunBoundedOn GuestInv (ofString "keccak256") K.«keccak256») →
    TerminatingFunBoundedOn GuestInv (ofString "header_hash") K.«header_hash») := rfl


end InitECandidate.Solver.Wave8Leaves.S13
