import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptInsert.MptInsertKind2Normal
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

/-- One iteration with node tag 2; shard 0 includes the null-root case.
Prove the bound and the continuing-state effect. No other kind shard is imported. -/
theorem mptInsert_kind2 (h : MptInsertCallees) :
    MptStepAt MptInsertActive MptInsertHead MptInsertEffect mptInsertBody mptInsertCost 2 := by
  intro F s hc ha hk
  refine ⟨mptInsert_body_bound h s hc ha.1.1.1, ?_⟩
  intro hflow
  have hnormal : (evaluateHOLFiniteState s mptInsertBody).1 = none :=
    hflow.resolve_right (MptInsertKind2.insert_noContinue s)
  exact MptInsertKind2.normal_run h ha hk (Prod.ext hnormal rfl)

end InitECandidate.Solver.Wave8GuestInv.GuardedBody
