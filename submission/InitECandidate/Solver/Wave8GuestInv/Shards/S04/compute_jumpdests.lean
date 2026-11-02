import InitECandidate.Solver.Wave8GuestInv.Shards.S04.JumpAdvance

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.S04

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.Wave8Leaves.S04.Light
open InitECandidate.Solver.Wave8Leaves.S04.Base

-- Variable-stride walk; the final audit uses the frozen rev9 statement.
theorem fb_compute_jumpdests
    (h_memzero : TerminatingFunBoundedOn GuestInv (ofString "memzero") K.«memzero»)
    (h_scratch_alloc : TerminatingFunBoundedOn GuestInv (ofString "scratch_alloc") K.«scratch_alloc»)
    : TerminatingFunBoundedOn GuestInv (ofString "compute_jumpdests") K.«compute_jumpdests» := by
  s04_fb_unfold 463 Guest.Software.guestFn_compute_jumpdests
  apply TerminatingProgBoundedOn.weaken'
  · apply decCall_guestInv' h_scratch_alloc
    apply TerminatingProgBoundedOn.seq_guestInv
    · exact call_guestInv' h_memzero
    · apply dec_guestInv
      apply TerminatingProgBoundedOn.seq_guestInv
      · exact jumpLoop_bound
      · exact straightOn _ rfl
  · unfold K.«compute_jumpdests»
    rw [domainBytes_eq]
    s04_generalize_K
    omega


end InitECandidate.Solver.Wave8Leaves.S04
