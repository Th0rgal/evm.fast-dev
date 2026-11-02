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

theorem fb_encode_execution_requests
    (h_alloc : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (h_memcpy : TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy») :
    TerminatingFunBoundedOn GuestInv (ofString "encode_execution_requests") K.«encode_execution_requests» := by
  apply onFun_le 839 (by rw [guestAst_len]; decide) Guest.Software.guestFn_encode_execution_requests _ rfl
  · htab_unfold Guest.Software.guestFn_encode_execution_requests
    s13_walk
  · htab_bound K.«encode_execution_requests»

example : type_of% (fb_encode_execution_requests (GuestInv := GuestInv)) =
    ((TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc») →
    (TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy») →
    TerminatingFunBoundedOn GuestInv (ofString "encode_execution_requests") K.«encode_execution_requests») := rfl


end InitECandidate.Solver.Wave8Leaves.S13
