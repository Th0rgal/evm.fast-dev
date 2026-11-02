import InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertStep01Kind0
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertStep02Kind1
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertStep03Kind2
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertStep04Kind3
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertStep05Count
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

theorem gbody__mpt_insert_node : GBody.«_mpt_insert_node» := by
  intro fb__insert_into_leaf fb__split_extension fb_common_prefix_length fb_mpt_fail fb_node_invalidate fb_node_new_ext fb_node_new_leaf nf__insert_into_leaf nf__split_extension ro_common_prefix_length rv_common_prefix_length ro_mpt_fail nf_node_invalidate iz_node_invalidate nf_node_new_ext rt_node_new_ext nf_node_new_leaf
  let h : MptInsertCallees := ⟨fb__insert_into_leaf, fb__split_extension, fb_common_prefix_length, fb_mpt_fail, fb_node_invalidate, fb_node_new_ext, fb_node_new_leaf, nf__insert_into_leaf, nf__split_extension, ro_common_prefix_length, rv_common_prefix_length, ro_mpt_fail, nf_node_invalidate, iz_node_invalidate, nf_node_new_ext, rt_node_new_ext, nf_node_new_leaf⟩
  have steps : MptSteps MptInsertActive MptInsertHead MptInsertEffect mptInsertBody mptInsertCost := mpt_cases (fun _ hp => mptInsert_kind hp)
    (mptInsert_kind0 h) (mptInsert_kind1 h) (mptInsert_kind2 h) (mptInsert_kind3 h)
  have hb : TerminatingProgBoundedOn MptReady (mptInit "result" "slot" (.seq (.while mptGo mptInsertBody) (mptReturn "result"))) (mptInsertBudget + 0) := mptInsert_initialize (RunFramesRace.TerminatingProgBoundedOn.seq_guestInv_after
    (mptInsert_count steps) (fun _ hp => hp.1.1)
    (RunFramesRace.TerminatingProgBoundedOn.of_clock (fun s => RunFramesRace.clock_return s (.var .local (ofString "result")))))
  simp only [Nat.add_zero, mptInsert_budget] at hb
  refine ⟨_, _, _, mptInsert_lookup, ?_⟩
  change TerminatingProgBoundedOn MptReady mptInsertCode _
  rw [mptInsert_ast]
  exact hb

end InitECandidate.Solver.Wave8GuestInv.GuardedBody
