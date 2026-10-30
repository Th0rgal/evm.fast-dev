import InitECandidate.Solver.PanTerminatingBounded
import InitECandidate.Solver.GuestBoundSszHtr
import InitECandidate.Solver.GuestBoundLoopFree

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-!
# `InitECandidate.Solver.LeafSszMerkleize` — Track B Leaf 05 (`< 350` LOC)

Frozen Spec Contract (`1 Cluster = 1 Leaf File < 350 LOC = 1 Worker`):
Bounds the SSZ packing and progressive/binary Merkleization cluster (`Guest/SoftwareAst.lean`):
- `pack_bytes` (`while i <+ n` chunking 32-byte words),
- `merkleize` (L3547: `ceil_log2` ≤ 64, `size = 1 << dn`, `while d < target` hashing `j < half` via `sha256`),
- `merkleize_progressive` (L3585: `size = 1`, `while off <+ n` doubling `size << 2` calling `merkleize`,
  followed by `while k != 0` calling `sha256`),
- `htr_bytes_list`, `htr_plist_chunks`, `htr_withdrawal`, `htr_payload`, `htr_new_payload_request`.

Imports `GuestBoundSszHtr` (`funBounded_main_reduced`, `DecStep`), `GuestBoundLoopFree`
(`funBounded_ceil_log2`), and `PanTerminatingBounded`.

Forbidden: NO `sorry`, `axiom`, `native_decide`, `bv_decide`, `Lean.ofReduceBool`,
`InitECandidate.Proofs.Bounded*`, `InitECandidate.Proofs.FullBaseline`, or `Guest.Ast`.
-/

namespace InitECandidate.Solver.LeafSszMerkleize

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.GuestBoundLoopFree
open InitECandidate.Solver.GuestBoundSszHtr

def K_pack_bytes : Nat := 4 * (2 ^ 64 - 1) + 4096
def K_merkleize : Nat := 128 * (2 ^ 64 - 1) + 65536
def K_merkleize_progressive : Nat := 64 * (K_merkleize + 4096) + 65536
def K_htr_bytes_list : Nat := K_pack_bytes + K_merkleize + 4096
def K_htr_plist_chunks : Nat := 2 * (2 ^ 64 - 1) + K_merkleize_progressive + 4096
def K_htr_payload : Nat := 8 * (K_htr_bytes_list + K_htr_plist_chunks + K_merkleize_progressive) + 65536
def K_htr_new_payload_request : Nat := 4 * K_htr_payload + 4 * K_htr_plist_chunks + 65536

theorem terminatingFunBounded_pack_bytes :
    TerminatingFunBounded (ofString "pack_bytes") K_pack_bytes := by
  sorry

theorem terminatingFunBounded_merkleize :
    TerminatingFunBounded (ofString "merkleize") K_merkleize := by
  sorry

theorem terminatingFunBounded_merkleize_progressive :
    TerminatingFunBounded (ofString "merkleize_progressive") K_merkleize_progressive := by
  sorry

theorem terminatingFunBounded_htr_bytes_list :
    TerminatingFunBounded (ofString "htr_bytes_list") K_htr_bytes_list := by
  sorry

theorem terminatingFunBounded_htr_plist_chunks :
    TerminatingFunBounded (ofString "htr_plist_chunks") K_htr_plist_chunks := by
  sorry

theorem terminatingFunBounded_htr_payload :
    TerminatingFunBounded (ofString "htr_payload") K_htr_payload := by
  sorry

theorem terminatingFunBounded_htr_new_payload_request :
    TerminatingFunBounded (ofString "htr_new_payload_request") K_htr_new_payload_request := by
  sorry

end InitECandidate.Solver.LeafSszMerkleize
