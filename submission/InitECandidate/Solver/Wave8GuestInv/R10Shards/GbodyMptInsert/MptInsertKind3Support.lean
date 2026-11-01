import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptInsert.MptCuts

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

def insertWalkCost : ProgHOL 64 → Nat
  | .seq a b => insertWalkCost a + insertWalkCost b
  | .ite _ a b => max (insertWalkCost a) (insertWalkCost b)
  | .dec _ _ _ b => insertWalkCost b
  | .decCall _ _ f _ b => mptCharge f + insertWalkCost b + 1
  | .call _ f _ => mptCharge f + 1
  | _ => 0

/-- The syntactic one-iteration budget applies to every insertion kind. -/
theorem mptInsert_body_bound (h : MptInsertCallees) :
    TerminatingProgBoundedOn GuestInv mptInsertBody mptInsertCost := by
  have hb : TerminatingProgBoundedOn GuestInv mptInsertBody (insertWalkCost mptInsertBody) := by
    simp only [mptInsertBody, mptInsertTail, mptInsertCode, mptDecBody,
      mptWhileBody, mptLeft, sourceFunctionEntry,
      Guest.Software.guestFn__mpt_insert_node,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
    simp only [insertWalkCost]
    repeat' first
      | apply TerminatingProgBoundedOn.seq_guestInv
      | apply TerminatingProgBoundedOn.ite_on
      | apply TerminatingProgBoundedOn.dec_on localsFree_guestInv
      | exact TerminatingProgBoundedOn.call_guestInv h.fb_node_new_leaf _ _
      | exact TerminatingProgBoundedOn.call_guestInv h.fb_mpt_fail _ _
      | exact TerminatingProgBoundedOn.call_guestInv h.fb_node_invalidate _ _
      | exact TerminatingProgBoundedOn.call_guestInv h.fb__insert_into_leaf _ _
      | exact TerminatingProgBoundedOn.call_guestInv h.fb_node_new_ext _ _
      | apply TerminatingProgBoundedOn.decCall_guestInv h.fb_common_prefix_length
      | apply TerminatingProgBoundedOn.decCall_guestInv h.fb__split_extension
      | exact fun s hc _ => TerminatingProgBounded.straight _ (by rfl) s hc
  have heq : insertWalkCost mptInsertBody = mptInsertCost := by
    change (0 + (max (K.node_new_leaf + 1)
      ((max (K.mpt_fail + 1) 0) + ((K.node_invalidate + 1) +
        max (K._insert_into_leaf + 1)
          (max (K.common_prefix_length +
            max (0 + (0 + (0 + (0 + 0))))
              (K._split_extension + max (K.node_new_ext + 1) 0 + 1) + 1)
            (max (0 + (0 + 0)) (0 + (0 + (0 + (0 + 0))))))))) +
        (max 0 0 + (0 + (0 + 0)))) = mptInsertCost
    simp only [mptInsertCost, Nat.max_self, Nat.add_zero, Nat.zero_add,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  rw [← heq]
  exact @hb

end InitECandidate.Solver.Wave8GuestInv.GuardedBody
