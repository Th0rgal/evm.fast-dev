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
theorem fb_emit_transfer_log
    (h_alloc : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (h_log_append : TerminatingFunBoundedOn GuestInv (ofString "log_append") K.«log_append»)
    (h_memcpy : TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy»)
    (h_memzero : TerminatingFunBoundedOn GuestInv (ofString "memzero") K.«memzero»)
    (h_u256_is_zero : TerminatingFunBoundedOn GuestInv (ofString "u256_is_zero") K.«u256_is_zero»)
    (h_u256_to_be32 : TerminatingFunBoundedOn GuestInv (ofString "u256_to_be32") K.«u256_to_be32»)
    : TerminatingFunBoundedOn GuestInv (ofString "emit_transfer_log") K.«emit_transfer_log» := by
  s04_fb_prove 567 Guest.Software.guestFn_emit_transfer_log K.«emit_transfer_log»


end InitECandidate.Solver.Wave8Leaves.S04
