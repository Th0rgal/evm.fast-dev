import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete.MptDeleteStep01Kind0
import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete.MptDeleteStep02Kind1
import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete.MptDeleteStep03Kind2
import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete.MptDeleteStep04Kind3
import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete.MptDeleteStep05Descent
import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete.MptDeleteStep06Unwind
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

theorem mptDelete_lookup : originalRuntimeCode.lookup (ofString "_mpt_delete_node_body") =
    some ((sourceFunctionEntry Guest.Software.guestFn__mpt_delete_node_body).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 278 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__mpt_delete_node_body) rfl

theorem bounded (h : MptDeleteCallees) :
    TerminatingFunBoundedOn MptReady (ofString "_mpt_delete_node_body") K.«_mpt_delete_node_body» := by
  have steps : MptSteps MptDeleteActive MptDeleteHead MptDeleteEffect mptDeleteBody mptDeleteCost := mpt_cases (fun _ hp => mptDelete_kind hp)
    (mptDelete_kind0 h) (mptDelete_kind1 h) (mptDelete_kind2 h) (mptDelete_kind3 h)
  have hu : TerminatingProgBoundedOn MptUnwindHead (.seq (.while mptTop mptUnwindBody) (mptReturn "res")) (mptUnwindBudget + 0) := TerminatingProgBoundedOn.seq_guestInv_after
    (mptDelete_unwind h) (fun _ hp => hp.1.1)
    (TerminatingProgBoundedOn.of_clock (fun s => clock_return s (.var .local (ofString "res"))))
  have hb : TerminatingProgBoundedOn MptReady (mptInit "top" "res" (.seq (.while mptGo mptDeleteBody) (.seq (.while mptTop mptUnwindBody) (mptReturn "res")))) (mptDeleteBudget + (mptUnwindBudget + 0)) := mptDelete_initialize (mptDelete_descent steps hu)
  simp only [Nat.add_zero, mptDelete_budget] at hb
  refine ⟨_, _, _, mptDelete_lookup, ?_⟩
  change TerminatingProgBoundedOn MptReady mptDeleteCode _
  rw [mptDelete_ast]
  exact hb

end InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete
