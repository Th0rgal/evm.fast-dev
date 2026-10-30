import InitECandidate.Solver.PanTerminatingBounded
import InitECandidate.Solver.GuestBoundRlpMpt
import InitECandidate.Solver.LeafMptWitnessWalk

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-!
# `InitECandidate.Solver.LeafMptInsertDelete` — Track B Leaf 04 (`< 350` LOC)

Frozen Spec Contract (`1 Cluster = 1 Leaf File < 350 LOC = 1 Worker`):
Bounds the MPT Patricia-trie mutation and indexed root builder cluster:
- `_collapse_branch` (`while i < 16`),
- `_mpt_insert_node` (L5013: `while go != 0` advancing `level` toward `klen ≤ 64`),
- `_mpt_delete_node_body` (L5135: `scratch_alloc(40)` downward stack `while go != 0` advancing `level`,
  followed by upward unwind `while top != 0` calling `_collapse_branch` + `memeq`),
- `build_mpt_indexed` (`while i <+ n`).

Imports `progBounded_mpt_insert_node_step`, `progBounded_mpt_delete_node_down_step`,
`funBounded_collapse_branch`, and `funBounded_build_mpt_indexed` from `GuestBoundRlpMpt`.

Forbidden: NO `sorry`, `axiom`, `native_decide`, `bv_decide`, `Lean.ofReduceBool`,
`InitECandidate.Proofs.Bounded*`, `InitECandidate.Proofs.FullBaseline`, or `Guest.Ast`.
-/

namespace InitECandidate.Solver.LeafMptInsertDelete

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.GuestBoundRlpMpt
open InitECandidate.Solver.LeafMptWitnessWalk

def K_collapse_branch : Nat := 2 * (2 ^ 64 - 1) + 1024
def K_mpt_insert_node : Nat := 4 * (2 ^ 64 - 1) + 8192
def K_mpt_delete_node_body : Nat := 8 * (2 ^ 64 - 1) * (K_collapse_branch + 128) + 16384
def K_build_mpt_indexed : Nat := 4 * (2 ^ 64 - 1) * (K_mpt_insert_node + K_node_rlp_fill + 256) + 8192

theorem terminatingFunBounded_collapse_branch :
    TerminatingFunBounded (ofString "_collapse_branch") K_collapse_branch := by
  sorry

theorem terminatingFunBounded_mpt_insert_node :
    TerminatingFunBounded (ofString "_mpt_insert_node") K_mpt_insert_node := by
  sorry

theorem terminatingFunBounded_mpt_delete_node_body :
    TerminatingFunBounded (ofString "_mpt_delete_node_body") K_mpt_delete_node_body := by
  sorry

theorem terminatingFunBounded_build_mpt_indexed :
    TerminatingFunBounded (ofString "build_mpt_indexed") K_build_mpt_indexed := by
  sorry

end InitECandidate.Solver.LeafMptInsertDelete
