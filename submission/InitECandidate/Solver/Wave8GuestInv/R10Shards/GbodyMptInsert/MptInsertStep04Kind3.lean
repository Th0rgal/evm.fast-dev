import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptInsert.MptInsertKind3Support
import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptInsert.MptInsertKind3Outer
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

/-- One iteration with node tag 3; shard 0 includes the null-root case.
Prove the bound and the continuing-state effect. No other kind shard is imported. -/
theorem mptInsert_kind3 (h : MptInsertCallees) :
    MptStepAt MptInsertActive MptInsertHead MptInsertEffect mptInsertBody mptInsertCost 3 := by
  intro F s hc hs hk
  refine ⟨mptInsert_body_bound h s hc hs.1.1.1, fun hflow => ?_⟩
  have hnone : (evaluateHOLFiniteState s mptInsertBody).1 = none :=
    hflow.resolve_right (evaluate_noTopContinue mptInsertBody (by decide) s)
  have heval : evaluateHOLFiniteState s mptInsertBody =
      (none, (evaluateHOLFiniteState s mptInsertBody).2) := Prod.ext hnone rfl
  obtain ⟨hhead, heffect⟩ := mpt_kind3_none s _ hs hk heval
  refine ⟨hhead, ?_⟩
  rcases heffect with hstop | hprogress
  · exact Or.inl hstop
  · refine Or.inr ⟨?_, ?_, ?_, ?_, Or.inl hprogress⟩
    · have he := mpt_avoids_none s _ mptInsertBody (ofString "key") (by decide) heval
      simp only [locN, he]
    · have he := mpt_avoids_none s _ mptInsertBody (ofString "klen") (by decide) heval
      simp only [locN, he]
    · have he := mpt_avoids_none s _ mptInsertBody (ofString "vptr") (by decide) heval
      simp only [locN, he]
    · have he := mpt_avoids_none s _ mptInsertBody (ofString "vlen") (by decide) heval
      simp only [locN, he]

end InitECandidate.Solver.Wave8GuestInv.GuardedBody
