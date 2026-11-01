import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete.MptDeleteKind3Prefix
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
namespace InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

/-- One iteration with node tag 3; shard 0 includes the null-root case.
Prove the bound and the continuing-state effect. No other kind shard is imported. -/
theorem mptDelete_kind3 (h : MptDeleteCallees) :
    MptStepAt MptDeleteActive MptDeleteHead MptDeleteEffect mptDeleteBody mptDeleteCost 3 := by
  intro F s hc hp hk
  refine ⟨mptDelete_body_bound h s hc hp.1.1.1, ?_⟩
  intro hflow
  have hnone : (evaluateHOLFiniteState s mptDeleteBody).1 = none :=
    hflow.resolve_right (evaluate_noTopContinue mptDeleteBody (by rfl) s)
  exact mptDelete_kind3_run h hc hp hk (Prod.ext hnone rfl)

end InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete
