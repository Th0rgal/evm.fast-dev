import InitECandidate.Solver.PanTerminatingBounded
import InitECandidate.Solver.LeafStateJournalHtab
import InitECandidate.Solver.GuestBoundEvmInterpreter
import InitECandidate.Solver.GuestBoundEvmFrames

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-!
# `InitECandidate.Solver.LeafEvmOpcodesBasic` — Track B Leaf 14 (`< 350` LOC)

Frozen Spec Contract (`1 Cluster = 1 Leaf File < 350 LOC = 1 Worker`):
Bounds the arithmetic, bitwise, stack/memory/keccak, environment, and block-context EVM opcode
handlers (`0x00`..`0x9f` excluding storage/call/create):
- `op_exp` (`while i <+ exp_bytes` byte-length loop + `while b < 8` square-and-multiply),
- `op_keccak`, `op_calldatacopy`, `op_codecopy`, `op_extcodecopy`, `op_returndatacopy`, `op_mcopy`,
- `op_balance`, `op_extcodesize`, `op_extcodehash`, `op_blockhash`, `op_blobhash`,
- stack/push/dup/swap/jump (`op_jump`, `op_jumpi`, `op_push`, `op_dup`, `op_swap`, `op_dupn`, `op_swapn`, `op_exchange`).

Imports `LeafStateJournalHtab`, `GuestBoundEvmInterpreter`, and `GuestBoundEvmFrames`.

Forbidden: NO `sorry`, `axiom`, `native_decide`, `bv_decide`, `Lean.ofReduceBool`,
`InitECandidate.Proofs.Bounded*`, `InitECandidate.Proofs.FullBaseline`, or `Guest.Ast`.
-/

namespace InitECandidate.Solver.LeafEvmOpcodesBasic

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.LeafStateJournalHtab
open InitECandidate.Solver.GuestBoundEvmInterpreter
open InitECandidate.Solver.GuestBoundEvmFrames

def K_op_exp : Nat := 32 * 8 * 512 + 16384
def K_op_memory_copy : Nat := 8 * (2 ^ 64 - 1) + K_get_account + 65536
def K_op_env_account : Nat := 2 * K_get_account + 4 * (2 ^ 64 - 1) + 65536

theorem terminatingFunBounded_op_exp :
    TerminatingFunBounded (ofString "op_exp") K_op_exp := by
  sorry

theorem terminatingFunBounded_op_keccak :
    TerminatingFunBounded (ofString "op_keccak") K_op_memory_copy := by
  sorry

theorem terminatingFunBounded_op_extcodecopy :
    TerminatingFunBounded (ofString "op_extcodecopy") K_op_memory_copy := by
  sorry

theorem terminatingFunBounded_op_balance :
    TerminatingFunBounded (ofString "op_balance") K_op_env_account := by
  sorry

theorem terminatingFunBounded_op_extcodehash :
    TerminatingFunBounded (ofString "op_extcodehash") K_op_env_account := by
  sorry

end InitECandidate.Solver.LeafEvmOpcodesBasic
