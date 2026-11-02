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

theorem fb_decode_bytes_list
    (h_ssz_fail : TerminatingFunBoundedOn GuestInv (ofString "ssz_fail") K.«ssz_fail»)
    (h_ssz_split_var_list : TerminatingFunBoundedOn GuestInv (ofString "ssz_split_var_list") K.«ssz_split_var_list») :
    TerminatingFunBoundedOn GuestInv (ofString "decode_bytes_list") K.«decode_bytes_list» := by
  apply onFun_le 206 (by rw [guestAst_len]; decide) Guest.Software.guestFn_decode_bytes_list _ rfl
  · htab_unfold Guest.Software.guestFn_decode_bytes_list
    s13_walk
  · htab_bound K.«decode_bytes_list»

example : type_of% (fb_decode_bytes_list (GuestInv := GuestInv)) =
    ((TerminatingFunBoundedOn GuestInv (ofString "ssz_fail") K.«ssz_fail») →
    (TerminatingFunBoundedOn GuestInv (ofString "ssz_split_var_list") K.«ssz_split_var_list») →
    TerminatingFunBoundedOn GuestInv (ofString "decode_bytes_list") K.«decode_bytes_list») := rfl


end InitECandidate.Solver.Wave8Leaves.S13
