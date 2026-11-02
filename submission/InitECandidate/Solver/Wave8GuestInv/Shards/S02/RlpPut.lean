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

theorem fb_rlp_put_u256
    (fb_heap_mark : TerminatingFunBoundedOn GuestInv (ofString "heap_mark") K.«heap_mark»)
    (fb_alloc : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (fb_u256_to_be_min : TerminatingFunBoundedOn GuestInv (ofString "u256_to_be_min") K.«u256_to_be_min»)
    (fb_rlp_encode_bytes : TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_bytes") K.«rlp_encode_bytes»)
    (fb_heap_release : TerminatingFunBoundedOn GuestInv (ofString "heap_release") K.«heap_release») :
    TerminatingFunBoundedOn GuestInv (ofString "rlp_put_u256") K.«rlp_put_u256» := by
  refine onFun_le 228 (by rw [guestAst_len]; decide) Guest.Software.guestFn_rlp_put_u256 K.«rlp_put_u256» rfl
    (K' := K.«heap_mark» + (K.«alloc» + (K.«u256_to_be_min» +
      (K.«rlp_encode_bytes» + (K.«heap_release» + 1 + 0) + 1) + 1) + 1) + 1) ?_ ?_
  s02_unfold Guest.Software.guestFn_rlp_put_u256
  apply TerminatingProgBoundedOn.decCall_guestInv
    (Bc := K.«alloc» + (K.«u256_to_be_min» +
      (K.«rlp_encode_bytes» + (K.«heap_release» + 1 + 0) + 1) + 1) + 1) fb_heap_mark
  apply TerminatingProgBoundedOn.decCall_guestInv
    (Bc := K.«u256_to_be_min» + (K.«rlp_encode_bytes» +
      (K.«heap_release» + 1 + 0) + 1) + 1) fb_alloc
  apply TerminatingProgBoundedOn.decCall_guestInv
    (Bc := K.«rlp_encode_bytes» + (K.«heap_release» + 1 + 0) + 1) fb_u256_to_be_min
  apply TerminatingProgBoundedOn.decCall_guestInv
    (Bc := K.«heap_release» + 1 + 0) fb_rlp_encode_bytes
  refine TerminatingProgBoundedOn.seq_guestInv (a := K.«heap_release» + 1) (b := 0) ?_ ?_
  · exact TerminatingProgBoundedOn.call_guestInv fb_heap_release _ _
  · exact straightOn _ rfl
  simp only [K.«rlp_put_u256»]
  omega

example : type_of% fb_rlp_put_u256 =
    (TerminatingFunBoundedOn GuestInv (ofString "heap_mark") K.«heap_mark» →
      TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc» →
      TerminatingFunBoundedOn GuestInv (ofString "u256_to_be_min") K.«u256_to_be_min» →
      TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_bytes") K.«rlp_encode_bytes» →
      TerminatingFunBoundedOn GuestInv (ofString "heap_release") K.«heap_release» →
      TerminatingFunBoundedOn GuestInv (ofString "rlp_put_u256") K.«rlp_put_u256») := rfl

theorem fb_sorted_keys32
    (fb_htab_keys : TerminatingFunBoundedOn GuestInv (ofString "htab_keys") K.«htab_keys»)
    (fb_sort_elems : TerminatingFunBoundedOn GuestInv (ofString "sort_elems") K.«sort_elems») :
    TerminatingFunBoundedOn GuestInv (ofString "sorted_keys32") K.«sorted_keys32» := by
  refine onFun_le 431 (by rw [guestAst_len]; decide) Guest.Software.guestFn_sorted_keys32 K.«sorted_keys32» rfl
    (K' := K.«htab_keys» + (K.«sort_elems» + 1 + 0) + 1) ?_ ?_
  s02_unfold Guest.Software.guestFn_sorted_keys32
  apply TerminatingProgBoundedOn.decCall_guestInv (Bc := K.«sort_elems» + 1 + 0) fb_htab_keys
  refine TerminatingProgBoundedOn.seq_guestInv (a := K.«sort_elems» + 1) (b := 0) ?_ ?_
  · exact TerminatingProgBoundedOn.call_guestInv fb_sort_elems _ _
  · exact straightOn _ rfl
  simp only [K.«sorted_keys32»]
  omega

example : type_of% fb_sorted_keys32 =
    (TerminatingFunBoundedOn GuestInv (ofString "htab_keys") K.«htab_keys» →
      TerminatingFunBoundedOn GuestInv (ofString "sort_elems") K.«sort_elems» →
      TerminatingFunBoundedOn GuestInv (ofString "sorted_keys32") K.«sorted_keys32») := rfl

end InitECandidate.Solver.Wave8GuestInv.S02
