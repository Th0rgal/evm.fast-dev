import InitECandidate.Solver.Wave8GuestInv.GuardedBody.RunFramesCuts
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

open InitECandidate.Solver.Wave8GuestInv.RunFramesRace

/-- Normal opcode returns and child pushes share the potential-decrease bridge. -/
theorem runFramesStep03 (p0 R0 L0 F0 : Nat) : DispatchReturnCut p0 R0 L0 F0 := by
  intro F t callee post hP hi hlt
  refine ⟨fun _ => Or.inr ⟨evmInv_locals _ hi, ?_, hP.2.1⟩, fun h => absurd rfl h⟩
  rw [(evm_congr (s := post) (t := { post with locals := t.locals }) rfl rfl).1]
  rw [(evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl).1,
    hP.1.2.1] at hlt
  exact hlt

end InitECandidate.Solver.Wave8GuestInv.GuardedBody
