import InitECandidate.Solver.Wave8GuestInv.Shards.S04.Base

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.S04

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.Wave8Leaves.S04.Light
open InitECandidate.Solver.Wave8Leaves.S04.Base

-- Conditional leaf: final spec compatibility and axioms are checked in Axioms.lean.
theorem fb_pre_alt_bn128_add
    (h_alloc : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (h_bn254_g1_add : TerminatingFunBoundedOn GuestInv (ofString "bn254_g1_add") K.«bn254_g1_add»)
    (h_buffer_read : TerminatingFunBoundedOn GuestInv (ofString "buffer_read") K.«buffer_read»)
    (h_charge_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (h_heap_mark : TerminatingFunBoundedOn GuestInv (ofString "heap_mark") K.«heap_mark»)
    (h_heap_release : TerminatingFunBoundedOn GuestInv (ofString "heap_release") K.«heap_release»)
    : TerminatingFunBoundedOn GuestInv (ofString "pre_alt_bn128_add") K.«pre_alt_bn128_add» := by
  s04_fb_prove 692 Guest.Software.guestFn_pre_alt_bn128_add K.«pre_alt_bn128_add»


end InitECandidate.Solver.Wave8Leaves.S04
