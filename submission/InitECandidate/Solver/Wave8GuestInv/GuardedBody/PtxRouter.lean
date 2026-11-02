import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase1Validate
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase2PreStateWarm
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase3MessageCall
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase4ReceiptLogs
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase5CleanupIncorporate
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

/-- Five native HOL continuation cuts (including `decCall` scopes) reconstruct
the original function at depths 0/34/98/99/139 and its exact cost. -/
theorem gbody_process_transaction : GBodyProcessTransaction := by
  intro h
  refine ⟨_, _, _, ptx_lookup, ?_⟩
  have hb : TerminatingProgBoundedOn TxReadyStrong (ptxPhase1 (ptxPhase2 (ptxPhase3 (ptxPhase4 ptxPhase5)))) (ptxCost1 + (ptxCost2 + (ptxCost3 + (ptxCost4 + ptxCost5)))) := ptxPhase1_cut h (ptxPhase2_cut h (ptxPhase3_cut h (ptxPhase4_cut h (ptxPhase5_cut h))))
  rw [← ptx_phases_eq, ptx_cost_eq] at hb
  intro F s hc hp
  simpa only [ptxCode, sourceFunctionEntry, Guest.Software.guestFn_process_transaction,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural] using (hb (F := F) s hc hp)

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10
