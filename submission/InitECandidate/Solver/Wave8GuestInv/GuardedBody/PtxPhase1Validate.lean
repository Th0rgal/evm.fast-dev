import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase1Assemble
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

/-- Phase 1: native HOL spine depths 0–34. -/
theorem ptxPhase1_cut (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn PtxValidated tail b) :
    TerminatingProgBoundedOn TxReadyStrong (ptxPhase1 tail) (ptxCost1 + b) := by
  exact Phase1.phase1_bound h htail


end InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10
