import InitECandidate.Solver.Wave8GuestInv.Shards.S02.Base

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace InitECandidate.Solver.Wave8GuestInv.S02

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.Wave8GuestInv

theorem fb_address_to_u256
    (fb_u256_from_be : TerminatingFunBoundedOn GuestInv (ofString "u256_from_be") K.«u256_from_be») :
    TerminatingFunBoundedOn GuestInv (ofString "address_to_u256") K.«address_to_u256» := by
  refine onFun_le 445 (by rw [guestAst_len]; decide) Guest.Software.guestFn_address_to_u256 K.«address_to_u256» rfl
    (K' := K.«u256_from_be» + 0 + 1) ?_ ?_
  s02_unfold Guest.Software.guestFn_address_to_u256
  apply TerminatingProgBoundedOn.decCall_guestInv (Bc := 0) fb_u256_from_be
  exact straightOn _ rfl
  rfl

example : type_of% fb_address_to_u256 =
    (TerminatingFunBoundedOn GuestInv (ofString "u256_from_be") K.«u256_from_be» →
      TerminatingFunBoundedOn GuestInv (ofString "address_to_u256") K.«address_to_u256») := rfl

theorem fb_check_gas_limit
    (fb_udiv : TerminatingFunBoundedOn GuestInv (ofString "udiv") K.«udiv») :
    TerminatingFunBoundedOn GuestInv (ofString "check_gas_limit") K.«check_gas_limit» := by
  refine onFun_le 235 (by rw [guestAst_len]; decide) Guest.Software.guestFn_check_gas_limit K.«check_gas_limit» rfl
    (K' := K.«udiv» + 0 + 1) ?_ ?_
  s02_unfold Guest.Software.guestFn_check_gas_limit
  apply TerminatingProgBoundedOn.decCall_guestInv (Bc := 0) fb_udiv
  exact straightOn _ rfl
  rfl

example : type_of% fb_check_gas_limit =
    (TerminatingFunBoundedOn GuestInv (ofString "udiv") K.«udiv» →
      TerminatingFunBoundedOn GuestInv (ofString "check_gas_limit") K.«check_gas_limit») := rfl

theorem fb_bal_init
    (fb_htab_new : TerminatingFunBoundedOn GuestInv (ofString "htab_new") K.«htab_new»)
    (fb_alloc : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc») :
    TerminatingFunBoundedOn GuestInv (ofString "bal_init") K.«bal_init» := by
  refine onFun_le 411 (by rw [guestAst_len]; decide) Guest.Software.guestFn_bal_init K.«bal_init» rfl
    (K' := (K.«htab_new» + 1) + ((K.«htab_new» + 1) + ((K.«htab_new» + 1) + (K.«alloc» + 1 + 0)))) ?_ ?_
  s02_unfold Guest.Software.guestFn_bal_init
  refine TerminatingProgBoundedOn.seq_guestInv (a := K.«htab_new» + 1)
    (b := (K.«htab_new» + 1) + ((K.«htab_new» + 1) + (K.«alloc» + 1 + 0))) ?_ ?_
  · exact TerminatingProgBoundedOn.call_guestInv fb_htab_new _ _
  refine TerminatingProgBoundedOn.seq_guestInv (a := K.«htab_new» + 1)
    (b := (K.«htab_new» + 1) + (K.«alloc» + 1 + 0)) ?_ ?_
  · exact TerminatingProgBoundedOn.call_guestInv fb_htab_new _ _
  refine TerminatingProgBoundedOn.seq_guestInv (a := K.«htab_new» + 1)
    (b := K.«alloc» + 1 + 0) ?_ ?_
  · exact TerminatingProgBoundedOn.call_guestInv fb_htab_new _ _
  refine TerminatingProgBoundedOn.seq_guestInv (a := K.«alloc» + 1) (b := 0) ?_ ?_
  · exact TerminatingProgBoundedOn.call_guestInv fb_alloc _ _
  · exact straightOn _ rfl
  simp only [K.«bal_init»]
  omega

example : type_of% fb_bal_init =
    (TerminatingFunBoundedOn GuestInv (ofString "htab_new") K.«htab_new» →
      TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc» →
      TerminatingFunBoundedOn GuestInv (ofString "bal_init") K.«bal_init») := rfl

end InitECandidate.Solver.Wave8GuestInv.S02
