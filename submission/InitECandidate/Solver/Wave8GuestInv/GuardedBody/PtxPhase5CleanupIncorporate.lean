import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxCuts
import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_PtxPhase5
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

/-- Phase 5: native HOL spine depths 139–144. -/
theorem ptxPhase5_cut (h : PtxCallees) :
    TerminatingProgBoundedOn PtxReceiptsDone ptxPhase5 ptxCost5 :=
  FastPhase5.ptxPhase5_cut h

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10
