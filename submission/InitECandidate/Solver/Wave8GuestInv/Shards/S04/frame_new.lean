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
theorem fb_frame_new
    (h_compute_jumpdests : TerminatingFunBoundedOn GuestInv (ofString "compute_jumpdests") K.«compute_jumpdests»)
    (h_frame_mem_alloc : TerminatingFunBoundedOn GuestInv (ofString "frame_mem_alloc") K.«frame_mem_alloc»)
    (h_frame_mem_mark : TerminatingFunBoundedOn GuestInv (ofString "frame_mem_mark") K.«frame_mem_mark»)
    (h_htab_count : TerminatingFunBoundedOn GuestInv (ofString "htab_count") K.«htab_count»)
    (h_htab_new_scratch : TerminatingFunBoundedOn GuestInv (ofString "htab_new_scratch") K.«htab_new_scratch»)
    (h_lst_new_scratch : TerminatingFunBoundedOn GuestInv (ofString "lst_new_scratch") K.«lst_new_scratch»)
    (h_memzero : TerminatingFunBoundedOn GuestInv (ofString "memzero") K.«memzero»)
    (h_scratch_alloc : TerminatingFunBoundedOn GuestInv (ofString "scratch_alloc") K.«scratch_alloc»)
    (h_scratch_mark : TerminatingFunBoundedOn GuestInv (ofString "scratch_mark") K.«scratch_mark»)
    : TerminatingFunBoundedOn GuestInv (ofString "frame_new") K.«frame_new» := by
  s04_fb_prove 467 Guest.Software.guestFn_frame_new K.«frame_new»


end InitECandidate.Solver.Wave8Leaves.S04
