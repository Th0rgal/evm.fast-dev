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

/-- Phase 3: native HOL spine depths 98–99. -/
theorem ptxPhase3_cut (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn PtxMessageDone tail b) :
    TerminatingProgBoundedOn PtxMessageReady (ptxPhase3 tail) (ptxCost3 + b) := by
  sorry

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10
