import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptInsert.MptInsertStep01Kind0
import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptInsert.MptInsertStep02Kind1
import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptInsert.MptInsertStep03Kind2
import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptInsert.MptInsertStep04Kind3
import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptInsert.MptInsertStep05Count

/-! Assembly of the insertion leaves for the revision-10 guard and clock budget. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

/-- The seven supplied callee bounds and their exact R10 contracts suffice. -/
theorem mptInsert_bounded (h : MptInsertCallees) :
    TerminatingFunBoundedOn MptInsertReady (ofString "_mpt_insert_node") K.«_mpt_insert_node» := by
  have steps : MptSteps MptInsertActive MptInsertHead MptInsertEffect mptInsertBody mptInsertCost :=
    mpt_cases (fun _ hp => mptInsert_kind hp)
      (mptInsert_kind0 h) (mptInsert_kind1 h) (mptInsert_kind2 h) (mptInsert_kind3 h)
  have hb : TerminatingProgBoundedOn MptInsertReady
      (mptInit "result" "slot" (.seq (.while mptGo mptInsertBody) (mptReturn "result")))
      (mptInsertBudget + 0) :=
    mptInsert_initialize (RunFramesRace.TerminatingProgBoundedOn.seq_guestInv_after
      (mptInsert_count steps) (fun _ hp => hp.1.1)
      (RunFramesRace.TerminatingProgBoundedOn.of_clock
        (fun s => RunFramesRace.clock_return s (.var .local (ofString "result")))))
  simp only [Nat.add_zero, mptInsert_budget] at hb
  refine ⟨_, _, _, mptInsert_lookup, ?_⟩
  change TerminatingProgBoundedOn MptInsertReady mptInsertCode _
  rw [mptInsert_ast]
  exact hb

end InitECandidate.Solver.Wave8GuestInv.GuardedBody
