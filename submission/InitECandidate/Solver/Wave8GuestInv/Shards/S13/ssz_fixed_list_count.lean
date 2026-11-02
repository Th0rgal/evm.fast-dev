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

theorem fb_ssz_fixed_list_count
    (h_ssz_fail : TerminatingFunBoundedOn GuestInv (ofString "ssz_fail") K.«ssz_fail»)
    (h_udivmod : TerminatingFunBoundedOn GuestInv (ofString "udivmod") K.«udivmod») :
    TerminatingFunBoundedOn GuestInv (ofString "ssz_fixed_list_count") K.«ssz_fixed_list_count» := by
  apply onFun_le 203 (by rw [guestAst_len]; decide) Guest.Software.guestFn_ssz_fixed_list_count _ rfl
  · htab_unfold Guest.Software.guestFn_ssz_fixed_list_count
    htab_walk
  · htab_bound K.«ssz_fixed_list_count»

example : type_of% (fb_ssz_fixed_list_count (GuestInv := GuestInv)) =
    ((TerminatingFunBoundedOn GuestInv (ofString "ssz_fail") K.«ssz_fail») →
    (TerminatingFunBoundedOn GuestInv (ofString "udivmod") K.«udivmod») →
    TerminatingFunBoundedOn GuestInv (ofString "ssz_fixed_list_count") K.«ssz_fixed_list_count») := rfl

#print axioms fb_ssz_fixed_list_count

end InitECandidate.Solver.Wave8Leaves.S13
