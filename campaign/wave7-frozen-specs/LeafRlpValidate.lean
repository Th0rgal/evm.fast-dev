import InitECandidate.Solver.PanTerminatingBounded
import InitECandidate.Solver.GuestBoundRlpMpt
import InitECandidate.Solver.GuestBoundLoopFree

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-!
# `InitECandidate.Solver.LeafRlpValidate` — Track B Leaf 02 (`< 350` LOC)

Frozen Spec Contract (`1 Cluster = 1 Leaf File < 350 LOC = 1 Worker`):
Bounds the RLP item validation and list/account/tx-field decoding cluster:
- `_rlp_validate_items_body` (L2165: `scratch_alloc(24)` stack `top` + `pos` advancing toward `end`),
- `rlp_list_count`, `rlp_list_to_slices`,
- `decode_account_from_leaf`, `tx_scalar_word`, `hdr_word_field`,
- `decode_access_list`, `decode_authorizations`, `decode_blob_hashes`.

Uses `ScratchStackBounded` (`maxScratchFrames24 = 521216`) + byte-offset progression in
`PanTerminatingBounded`, and existing step lemmas in `GuestBoundRlpMpt` / `GuestBoundLoopFree`.

Forbidden: NO `sorry`, `axiom`, `native_decide`, `bv_decide`, `Lean.ofReduceBool`,
`InitECandidate.Proofs.Bounded*`, `InitECandidate.Proofs.FullBaseline`, or `Guest.Ast`.
-/

namespace InitECandidate.Solver.LeafRlpValidate

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.GuestBoundRlpMpt
open InitECandidate.Solver.GuestBoundLoopFree

def K_rlp_validate_items_body : Nat := 8 * (2 ^ 64 - 1) + 4096
def K_rlp_list_count : Nat := K_rlp_validate_items_body + 2 * (2 ^ 64 - 1) + 128
def K_rlp_list_to_slices : Nat := K_rlp_list_count + 4 * (2 ^ 64 - 1) + 256
def K_decode_account_from_leaf : Nat := 4 * K_rlp_list_to_slices + 8 * (2 ^ 64 - 1) + 512
def K_tx_scalar_word : Nat := 2 * (2 ^ 64 - 1) + 128
def K_hdr_word_field : Nat := 2 * (2 ^ 64 - 1) + 128
def K_decode_access_list : Nat := 4 * (2 ^ 64 - 1) * K_rlp_list_to_slices + 1024
def K_decode_authorizations : Nat := 2 * (2 ^ 64 - 1) * (K_rlp_list_to_slices + K_tx_scalar_word) + 1024
def K_decode_blob_hashes : Nat := 2 * (2 ^ 64 - 1) * K_rlp_list_to_slices + 512

theorem terminatingFunBounded_rlp_validate_items_body :
    TerminatingFunBounded (ofString "_rlp_validate_items_body") K_rlp_validate_items_body := by
  sorry

theorem terminatingFunBounded_rlp_list_count :
    TerminatingFunBounded (ofString "rlp_list_count") K_rlp_list_count := by
  sorry

theorem terminatingFunBounded_rlp_list_to_slices :
    TerminatingFunBounded (ofString "rlp_list_to_slices") K_rlp_list_to_slices := by
  sorry

theorem terminatingFunBounded_decode_account_from_leaf :
    TerminatingFunBounded (ofString "decode_account_from_leaf") K_decode_account_from_leaf := by
  sorry

theorem terminatingFunBounded_tx_scalar_word :
    TerminatingFunBounded (ofString "tx_scalar_word") K_tx_scalar_word := by
  sorry

theorem terminatingFunBounded_hdr_word_field :
    TerminatingFunBounded (ofString "hdr_word_field") K_hdr_word_field := by
  sorry

theorem terminatingFunBounded_decode_access_list :
    TerminatingFunBounded (ofString "decode_access_list") K_decode_access_list := by
  sorry

theorem terminatingFunBounded_decode_authorizations :
    TerminatingFunBounded (ofString "decode_authorizations") K_decode_authorizations := by
  sorry

theorem terminatingFunBounded_decode_blob_hashes :
    TerminatingFunBounded (ofString "decode_blob_hashes") K_decode_blob_hashes := by
  sorry

end InitECandidate.Solver.LeafRlpValidate
