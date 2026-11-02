import InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptDeleteStep01Kind0
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptDeleteStep02Kind1
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptDeleteStep03Kind2
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptDeleteStep04Kind3
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptDeleteStep05Descent
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptDeleteStep06Unwind
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

theorem gbody__mpt_delete_node_body : GBody.«_mpt_delete_node_body» := by
  intro fb__collapse_branch fb__delete_ext_finish fb_common_prefix_length fb_memeq fb_mpt_fail fb_node_invalidate fb_scratch_alloc nf__collapse_branch nf__delete_ext_finish ro_common_prefix_length rv_common_prefix_length ro_memeq ro_mpt_fail nf_node_invalidate iz_node_invalidate ww_scratch_alloc rt_scratch_alloc
  let h : MptDeleteCallees := ⟨fb__collapse_branch, fb__delete_ext_finish, fb_common_prefix_length, fb_memeq, fb_mpt_fail, fb_node_invalidate, fb_scratch_alloc, nf__collapse_branch, nf__delete_ext_finish, ro_common_prefix_length, rv_common_prefix_length, ro_memeq, ro_mpt_fail, nf_node_invalidate, iz_node_invalidate, ww_scratch_alloc, rt_scratch_alloc⟩
  have steps : MptSteps MptDeleteActive MptDeleteHead MptDeleteEffect mptDeleteBody mptDeleteCost := mpt_cases (fun _ hp => mptDelete_kind hp)
    (mptDelete_kind0 h) (mptDelete_kind1 h) (mptDelete_kind2 h) (mptDelete_kind3 h)
  have hu : TerminatingProgBoundedOn MptUnwindHead (.seq (.while mptTop mptUnwindBody) (mptReturn "res")) (mptUnwindBudget + 0) := RunFramesRace.TerminatingProgBoundedOn.seq_guestInv_after
    (mptDelete_unwind h) (fun _ hp => hp.1.1)
    (RunFramesRace.TerminatingProgBoundedOn.of_clock (fun s => RunFramesRace.clock_return s (.var .local (ofString "res"))))
  have hb : TerminatingProgBoundedOn MptReady (mptInit "top" "res" (.seq (.while mptGo mptDeleteBody) (.seq (.while mptTop mptUnwindBody) (mptReturn "res")))) (mptDeleteBudget + (mptUnwindBudget + 0)) := mptDelete_initialize (mptDelete_descent steps hu)
  simp only [Nat.add_zero, mptDelete_budget] at hb
  refine ⟨_, _, _, lookup__mpt_delete_node_body, ?_⟩
  change TerminatingProgBoundedOn MptReady mptDeleteCode _
  rw [mptDelete_ast]
  exact hb

end InitECandidate.Solver.Wave8GuestInv.GuardedBody
