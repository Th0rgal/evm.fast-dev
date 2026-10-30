import InitECandidate.Solver.PanTerminatingBounded
import InitECandidate.Solver.LeafMptInsertDelete
import InitECandidate.Solver.LeafStateJournalHtab
import InitECandidate.Solver.GuestBoundBlockTxBal

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-!
# `InitECandidate.Solver.LeafSortBalPostState` — Track B Leaf 12 (`< 350` LOC)

Frozen Spec Contract (`1 Cluster = 1 Leaf File < 350 LOC = 1 Worker`):
Bounds the bottom-up merge sort `sort_elems`, EIP-7928 Block Access List (BAL) encoder, and
post-execution state/tx/receipt/withdrawals/requests root commitment cluster:
- `sort_elems` (L7185: bottom-up merge sort `while width <+ n` doubling `width = width * 2` ≤ 64 passes,
  inner `while left <+ n` merging `i <+ mid`, `j <+ right` followed by `memcpy`),
- `compute_state_root` (sorts touched accounts/slots via `sort_elems`, mutates MPT via
  `_mpt_insert_node` / `_mpt_delete_node_body` / `_node_rlp_fill`),
- `build_block_access_list_rlp`, `build_mpt_indexed`, `compute_requests_hash`.

Imports `LeafMptInsertDelete`, `LeafStateJournalHtab`, and `GuestBoundBlockTxBal`.

Forbidden: NO `sorry`, `axiom`, `native_decide`, `bv_decide`, `Lean.ofReduceBool`,
`InitECandidate.Proofs.Bounded*`, `InitECandidate.Proofs.FullBaseline`, or `Guest.Ast`.
-/

namespace InitECandidate.Solver.LeafSortBalPostState

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.LeafMptInsertDelete
open InitECandidate.Solver.LeafStateJournalHtab
open InitECandidate.Solver.GuestBoundBlockTxBal

def K_sort_elems : Nat := 64 * 8 * (2 ^ 64 - 1) + 65536
def K_compute_state_root : Nat :=
  4 * (2 ^ 64 - 1) * (K_sort_elems + K_mpt_insert_node + K_mpt_delete_node_body + 65536) + 262144
def K_build_block_access_list_rlp : Nat := 8 * (2 ^ 64 - 1) * (K_sort_elems + 4096) + 262144
def K_compute_block_commitments : Nat :=
  K_compute_state_root + K_build_block_access_list_rlp + 4 * K_build_mpt_indexed + 524288

theorem terminatingFunBounded_sort_elems :
    TerminatingFunBounded (ofString "sort_elems") K_sort_elems := by
  sorry

theorem terminatingFunBounded_compute_state_root :
    TerminatingFunBounded (ofString "compute_state_root") K_compute_state_root := by
  sorry

theorem terminatingFunBounded_build_block_access_list_rlp :
    TerminatingFunBounded (ofString "build_block_access_list_rlp") K_build_block_access_list_rlp := by
  sorry

end InitECandidate.Solver.LeafSortBalPostState
