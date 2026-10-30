import InitECandidate.Solver.PanTerminatingBounded
import InitECandidate.Solver.GuestBoundRlpMpt
import InitECandidate.Solver.GuestBoundLoopFree

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-!
# `InitECandidate.Solver.LeafMptWitnessWalk` — Track B Leaf 03 (`< 350` LOC)

Frozen Spec Contract (`1 Cluster = 1 Leaf File < 350 LOC = 1 Worker`):
Bounds the MPT witness node decoder, trie walk, and node RLP serializer cluster:
- `_decode_witness_node_body` (L4740: explicit heap/scratch stack `top`, `mode` 1/2/0, `slot` 0..16),
- `trie_walk` (L4876: `while node != 0` advancing nibble index `pos` toward `nlen ≤ 64`),
- `_node_rlp_finish` (`while i < 16`, `while j < 16`),
- `_node_rlp_fill` (L5320: `scratch_alloc(48)` stack `top` + child scan `while (i < 16) && (found == 0)`).

Imports existing step bounds `progBounded_decode_witness_node_body_step`,
`progBounded_trie_walk_step`, `funBounded_node_rlp_finish`, and `progBounded_node_rlp_fill_step`
from `GuestBoundRlpMpt`.

Forbidden: NO `sorry`, `axiom`, `native_decide`, `bv_decide`, `Lean.ofReduceBool`,
`InitECandidate.Proofs.Bounded*`, `InitECandidate.Proofs.FullBaseline`, or `Guest.Ast`.
-/

namespace InitECandidate.Solver.LeafMptWitnessWalk

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.GuestBoundRlpMpt

def K_decode_witness_node_body : Nat := 16 * (2 ^ 64 - 1) + 65536
def K_trie_walk : Nat := 4 * (2 ^ 64 - 1) + 4096
def K_node_rlp_finish : Nat := 2 * (2 ^ 64 - 1) + 4096
def K_node_rlp_fill : Nat := 18 * (2 ^ 64 - 1) * (K_node_rlp_finish + 64) + 8192

theorem terminatingFunBounded_decode_witness_node_body :
    TerminatingFunBounded (ofString "_decode_witness_node_body") K_decode_witness_node_body := by
  sorry

theorem terminatingFunBounded_trie_walk :
    TerminatingFunBounded (ofString "trie_walk") K_trie_walk := by
  sorry

theorem terminatingFunBounded_node_rlp_finish :
    TerminatingFunBounded (ofString "_node_rlp_finish") K_node_rlp_finish := by
  sorry

theorem terminatingFunBounded_node_rlp_fill :
    TerminatingFunBounded (ofString "_node_rlp_fill") K_node_rlp_fill := by
  sorry

end InitECandidate.Solver.LeafMptWitnessWalk
