import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete.MptCuts

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
/-- The clock bound is independent of the node kind. Each call is charged once,
and each conditional uses the larger of its two branch charges. -/
theorem mptDelete_body_bound (h : MptDeleteCallees) :
    TerminatingProgBoundedOn GuestInv mptDeleteBody mptDeleteCost := by
  apply TerminatingProgBoundedOn.mono_bound
  · repeat' first
    | exact TerminatingProgBoundedOn.call_guestInv h.fb_mpt_fail _ _
    | exact TerminatingProgBoundedOn.call_guestInv h.fb_node_invalidate _ _
    | exact TerminatingProgBoundedOn.call_guestInv h.fb_memeq _ _
    | exact TerminatingProgBoundedOn.call_guestInv h.fb_common_prefix_length _ _
    | exact TerminatingProgBoundedOn.call_guestInv h.fb_scratch_alloc _ _
    | exact TerminatingProgBoundedOn.call_guestInv h.fb__collapse_branch _ _
    | apply TerminatingProgBoundedOn.decCall_guestInv h.fb_memeq
    | apply TerminatingProgBoundedOn.decCall_guestInv h.fb_common_prefix_length
    | apply TerminatingProgBoundedOn.decCall_guestInv h.fb_scratch_alloc
    | apply TerminatingProgBoundedOn.seq_guestInv
    | apply TerminatingProgBoundedOn.ite_on
    | apply TerminatingProgBoundedOn.dec_on localsFree_guestInv
    | exact fun s hc _ => TerminatingProgBounded.straight _ (by rfl) s hc
  · simp only [mptDeleteCost, Nat.zero_add, Nat.add_zero, Nat.max_zero,
      Nat.zero_max, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, le_refl]

end InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete
