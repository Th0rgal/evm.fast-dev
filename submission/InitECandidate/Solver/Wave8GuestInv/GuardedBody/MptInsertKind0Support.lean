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

namespace InsertKind0

private def cost : ProgHOL 64 → Nat
  | .seq a b => cost a + cost b
  | .ite _ a b => max (cost a) (cost b)
  | .dec _ _ _ b => cost b
  | .call _ f _ => mptCharge f + 1
  | .decCall _ _ f _ b => mptCharge f + cost b + 1
  | _ => 0

/-- The syntactic call budget also covers unsuccessful expression evaluations. -/
theorem bounded (h : MptInsertCallees) :
    TerminatingProgBoundedOn GuestInv mptInsertBody mptInsertCost := by
  have hb : TerminatingProgBoundedOn GuestInv mptInsertBody (cost mptInsertBody) := by
    repeat' first
      | apply TerminatingProgBoundedOn.dec_on localsFree_guestInv
      | apply TerminatingProgBoundedOn.seq_guestInv (a := cost _) (b := cost _)
      | apply TerminatingProgBoundedOn.ite_on (a := cost _) (b := cost _)
      | apply TerminatingProgBoundedOn.decCall_guestInv h.fb_common_prefix_length
      | apply TerminatingProgBoundedOn.decCall_guestInv h.fb__split_extension
      | exact TerminatingProgBoundedOn.call_guestInv h.fb_node_new_leaf _ _
      | exact TerminatingProgBoundedOn.call_guestInv h.fb_mpt_fail _ _
      | exact TerminatingProgBoundedOn.call_guestInv h.fb_node_invalidate _ _
      | exact TerminatingProgBoundedOn.call_guestInv h.fb__insert_into_leaf _ _
      | exact TerminatingProgBoundedOn.call_guestInv h.fb_common_prefix_length _ _
      | exact TerminatingProgBoundedOn.call_guestInv h.fb__split_extension _ _
      | exact TerminatingProgBoundedOn.call_guestInv h.fb_node_new_ext _ _
      | exact RunFramesRace.TerminatingProgBoundedOn.of_clock (fun s => RunFramesRace.clock_assign s _ _ _)
      | exact RunFramesRace.TerminatingProgBoundedOn.of_clock (fun s => clockPreserving_store _ _ s)
      | exact RunFramesRace.TerminatingProgBoundedOn.of_clock (fun s => RunFramesRace.clock_skip s)
  have heq : cost mptInsertBody = mptInsertCost := by
    simp only [mptInsertBody, mptInsertTail, mptInsertCode, sourceFunctionEntry,
      Guest.Software.guestFn__mpt_insert_node,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      mptDecBody, mptLeft, mptWhileBody, cost]
    simp +decide [mptCharge, mptInsertCost, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  intro F s hc hp
  rw [← heq]
  exact hb s hc hp

end InsertKind0
end InitECandidate.Solver.Wave8GuestInv.GuardedBody
