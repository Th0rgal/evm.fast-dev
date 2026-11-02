import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxCuts
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

/-- Phase 2: native HOL spine depths 34–98. -/
theorem ptxPhase2_cut (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn PtxMessageReady tail b) :
    TerminatingProgBoundedOn PtxValidated (ptxPhase2 tail) (ptxCost2 + b) := by
  sorry

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10
