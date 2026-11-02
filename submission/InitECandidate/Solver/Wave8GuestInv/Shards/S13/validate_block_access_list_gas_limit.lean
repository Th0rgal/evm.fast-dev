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

theorem fb_validate_block_access_list_gas_limit
    (h_htab_has : TerminatingFunBoundedOn GuestInv (ofString "htab_has") K.«htab_has»)
    (h_htab_item : TerminatingFunBoundedOn GuestInv (ofString "htab_item") K.«htab_item»)
    (h_udiv : TerminatingFunBoundedOn GuestInv (ofString "udiv") K.«udiv») :
    TerminatingFunBoundedOn GuestInv (ofString "validate_block_access_list_gas_limit") K.«validate_block_access_list_gas_limit» := by
  apply onFun_le 434 (by rw [guestAst_len]; decide) Guest.Software.guestFn_validate_block_access_list_gas_limit _ rfl
  · htab_unfold Guest.Software.guestFn_validate_block_access_list_gas_limit
    s13_walk
  · htab_bound K.«validate_block_access_list_gas_limit»

example : type_of% (fb_validate_block_access_list_gas_limit (GuestInv := GuestInv)) =
    ((TerminatingFunBoundedOn GuestInv (ofString "htab_has") K.«htab_has») →
    (TerminatingFunBoundedOn GuestInv (ofString "htab_item") K.«htab_item») →
    (TerminatingFunBoundedOn GuestInv (ofString "udiv") K.«udiv») →
    TerminatingFunBoundedOn GuestInv (ofString "validate_block_access_list_gas_limit") K.«validate_block_access_list_gas_limit») := rfl

#print axioms fb_validate_block_access_list_gas_limit

end InitECandidate.Solver.Wave8Leaves.S13
