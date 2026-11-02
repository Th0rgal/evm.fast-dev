import InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptCuts
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

/-- One iteration with node tag 0; shard 0 includes the null-root case.
Prove the bound and the continuing-state effect. No other kind shard is imported. -/
theorem mptInsert_kind0 (h : MptInsertCallees) :
    MptStepAt MptInsertActive MptInsertHead MptInsertEffect mptInsertBody mptInsertCost 0 := by
  sorry

end InitECandidate.Solver.Wave8GuestInv.GuardedBody
