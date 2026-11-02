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

theorem fb_ssz_split_var_list
    (h_alloc : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (h_ssz_fail : TerminatingFunBoundedOn GuestInv (ofString "ssz_fail") K.«ssz_fail») :
    TerminatingFunBoundedOn GuestInv (ofString "ssz_split_var_list") K.«ssz_split_var_list» := by
  apply onFun_le 202 (by rw [guestAst_len]; decide) Guest.Software.guestFn_ssz_split_var_list _ rfl
  · htab_unfold Guest.Software.guestFn_ssz_split_var_list
    s13_walk
  · htab_bound K.«ssz_split_var_list»

example : type_of% (fb_ssz_split_var_list (GuestInv := GuestInv)) =
    ((TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc») →
    (TerminatingFunBoundedOn GuestInv (ofString "ssz_fail") K.«ssz_fail») →
    TerminatingFunBoundedOn GuestInv (ofString "ssz_split_var_list") K.«ssz_split_var_list») := rfl


end InitECandidate.Solver.Wave8Leaves.S13
