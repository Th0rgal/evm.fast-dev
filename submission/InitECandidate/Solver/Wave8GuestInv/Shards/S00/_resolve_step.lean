import InitECandidate.Solver.Wave8GuestInv.Shards.S00.Core

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.S00
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8Leaves.S00Spec

/-- Keep all callee costs opaque while constructing the program proof. -/
private theorem resolve_step_bounds (a b c d : Nat)
    (h_mpt_fail : TerminatingFunBoundedOn GuestInv (ofString "mpt_fail") b)
    (h_node_new_hashed : TerminatingFunBoundedOn GuestInv (ofString "node_new_hashed") d)
    (h_nodedb_lookup : TerminatingFunBoundedOn GuestInv (ofString "nodedb_lookup") c)
    (h_rlp_item : TerminatingFunBoundedOn GuestInv (ofString "rlp_item") a) :
    TerminatingFunBoundedOn GuestInv (ofString "_resolve_step")
      ((a + 1) + (b + 1) + Nat.max
        (Nat.max (b + 1) 0 + (c + 1) + Nat.max (d + 1) 0) 0) := by
  fb_unfold 260 Guest.Software.guestFn__resolve_step
  refine TerminatingProgBoundedOn.weaken' (by fb_auto) ?_
  simp only [nat_max_eq]
  omega

theorem fb__resolve_step
    (h_mpt_fail : TerminatingFunBoundedOn GuestInv (ofString "mpt_fail") K.«mpt_fail»)
    (h_node_new_hashed : TerminatingFunBoundedOn GuestInv (ofString "node_new_hashed") K.«node_new_hashed»)
    (h_nodedb_lookup : TerminatingFunBoundedOn GuestInv (ofString "nodedb_lookup") K.«nodedb_lookup»)
    (h_rlp_item : TerminatingFunBoundedOn GuestInv (ofString "rlp_item") K.«rlp_item») :
    TerminatingFunBoundedOn GuestInv (ofString "_resolve_step") K.«_resolve_step» := by
  exact resolve_step_bounds _ _ _ _ h_mpt_fail h_node_new_hashed h_nodedb_lookup h_rlp_item


end InitECandidate.Solver.Wave8Leaves.S00
