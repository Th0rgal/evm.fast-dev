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

theorem fb_ssz_check_offsets
    (h_ssz_fail : TerminatingFunBoundedOn GuestInv (ofString "ssz_fail") K.«ssz_fail») :
    TerminatingFunBoundedOn GuestInv (ofString "ssz_check_offsets") K.«ssz_check_offsets» := by
  apply onFun_le 201 (by rw [guestAst_len]; decide) Guest.Software.guestFn_ssz_check_offsets _ rfl
  · htab_unfold Guest.Software.guestFn_ssz_check_offsets
    s13_walk
  · htab_bound K.«ssz_check_offsets»

example : type_of% (fb_ssz_check_offsets (GuestInv := GuestInv)) =
    ((TerminatingFunBoundedOn GuestInv (ofString "ssz_fail") K.«ssz_fail») →
    TerminatingFunBoundedOn GuestInv (ofString "ssz_check_offsets") K.«ssz_check_offsets») := rfl

#print axioms fb_ssz_check_offsets

end InitECandidate.Solver.Wave8Leaves.S13
