import InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind0Support
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind0Flow
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
  intro F s hc hp hk
  refine ⟨InsertKind0.bounded h s hc hp.1.1.1, ?_⟩
  intro hflow
  obtain ⟨hle, Nd, hheap, _, hkey, _⟩ := hp.1.2 hp.2
  have hready : InsertKind0.Ready s := ⟨hp.1.1, hle, ⟨Nd, hheap, hkey⟩, hk⟩
  have hnt : (evaluateHOLFiniteState s mptInsertBody).1 ≠ some .timeOut := by
    rcases hflow with hr | hr <;> rw [hr] <;> simp
  have hout := (InsertKind0.body_done h).run s hc hready hnt
  have hnormal := hflow.resolve_right hout.1
  have hd := hout.2 hnormal
  exact ⟨⟨hd.1, fun hgo => (hgo hd.2).elim⟩, Or.inl hd.2⟩

end InitECandidate.Solver.Wave8GuestInv.GuardedBody

