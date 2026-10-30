import InitECandidate.Solver.PanTerminatingBounded
import InitECandidate.Solver.LeafRlpValidate
import InitECandidate.Solver.LeafSecpP256
import InitECandidate.Solver.LeafStateJournalHtab
import InitECandidate.Solver.LeafSortBalPostState
import InitECandidate.Solver.LeafRunFrames
import InitECandidate.Solver.GuestBoundBlockTxBal

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-!
# `InitECandidate.Solver.LeafBlockTxLoop` — Track B Leaf 17 (`< 350` LOC)

Frozen Spec Contract (`1 Cluster = 1 Leaf File < 350 LOC = 1 Worker`):
Bounds single-transaction validation/execution (`process_transaction`), system contracts
(EIP-2935 blockhash history, EIP-4788 beacon root, EIP-7002 withdrawal requests, EIP-7251
consolidation requests, EIP-6110 deposit parsing), and full block execution (`execute_block` /
`run_attempt`):
- `process_unchecked_system_transaction`, `process_checked_system_transaction`, `extract_deposit_data`,
- `process_transaction` (decodes tx, recovers sender via `secp256k1_ecrecover`, applies EIP-7702
  authorizations, warms access list, runs `process_message`, refunds gas, emits receipt),
- `execute_block` / `run_attempt` (iterates `while tx_idx <+ num_txs` calling `process_transaction`,
  processes withdrawals & system calls, then verifies commitments via `LeafSortBalPostState`).

Imports `LeafRlpValidate`, `LeafSecpP256`, `LeafStateJournalHtab`, `LeafSortBalPostState`,
`LeafRunFrames`, and `GuestBoundBlockTxBal`.

Forbidden: NO `sorry`, `axiom`, `native_decide`, `bv_decide`, `Lean.ofReduceBool`,
`InitECandidate.Proofs.Bounded*`, `InitECandidate.Proofs.FullBaseline`, or `Guest.Ast`.
-/

namespace InitECandidate.Solver.LeafBlockTxLoop

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.LeafRlpValidate
open InitECandidate.Solver.LeafSecpP256
open InitECandidate.Solver.LeafStateJournalHtab
open InitECandidate.Solver.LeafSortBalPostState
open InitECandidate.Solver.LeafRunFrames
open InitECandidate.Solver.GuestBoundBlockTxBal

def K_process_transaction : Nat :=
  K_decode_access_list + K_decode_authorizations + K_decode_blob_hashes +
  4 * K_secp256k1_ecrecover + K_process_message + K_state_restore + 1048576

def K_run_attempt : Nat :=
  (2 ^ 64 - 1) * (K_process_transaction + 65536) +
  4 * K_process_message + K_compute_block_commitments + 4194304

theorem terminatingFunBounded_process_transaction :
    TerminatingFunBounded (ofString "process_transaction") K_process_transaction := by
  sorry

theorem terminatingFunBounded_run_attempt :
    TerminatingFunBounded (ofString "run_attempt") K_run_attempt := by
  sorry

end InitECandidate.Solver.LeafBlockTxLoop
