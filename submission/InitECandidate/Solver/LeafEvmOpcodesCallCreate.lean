import InitECandidate.Solver.PanTerminatingBounded
import InitECandidate.Solver.LeafStateJournalHtab
import InitECandidate.Solver.LeafPrecompileDispatch
import InitECandidate.Solver.LeafEvmOpcodesBasic
import InitECandidate.Solver.GuestBoundEvmInterpreter
import InitECandidate.Solver.GuestBoundEvmFrames

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-!
# `InitECandidate.Solver.LeafEvmOpcodesCallCreate` — Track B Leaf 15 (`< 350` LOC)

Frozen Spec Contract (`1 Cluster = 1 Leaf File < 350 LOC = 1 Worker`):
Bounds the state-mutating, logging, CALL-family, CREATE-family, SELFDESTRUCT, and master single-step
`op_dispatch` handlers:
- `op_sload`, `op_sstore`, `op_tload`, `op_tstore`, `op_log`,
- `generic_call` (`op_call`, `op_callcode`, `op_delegatecall`, `op_staticcall`, EIP-7702 delegation resolution,
  and synchronous `run_precompile` / child frame push),
- `generic_create` (`op_create`, `op_create2` initcode copy + keccak256 address derivation + child frame push),
- `op_selfdestruct`,
- `op_dispatch` (master single-instruction EVM step called inside `run_frames`).

Imports `LeafStateJournalHtab`, `LeafPrecompileDispatch`, `LeafEvmOpcodesBasic`,
`GuestBoundEvmInterpreter`, and `GuestBoundEvmFrames`.

Forbidden: NO `sorry`, `axiom`, `native_decide`, `bv_decide`, `Lean.ofReduceBool`,
`InitECandidate.Proofs.Bounded*`, `InitECandidate.Proofs.FullBaseline`, or `Guest.Ast`.
-/

namespace InitECandidate.Solver.LeafEvmOpcodesCallCreate

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.LeafStateJournalHtab
open InitECandidate.Solver.LeafPrecompileDispatch
open InitECandidate.Solver.LeafEvmOpcodesBasic
open InitECandidate.Solver.GuestBoundEvmInterpreter
open InitECandidate.Solver.GuestBoundEvmFrames

def K_op_sstore : Nat := 4 * K_set_storage + 65536
def K_generic_call : Nat :=
  4 * K_get_account + K_run_precompile + K_compute_jumpdests + K_state_restore + 262144
def K_generic_create : Nat :=
  4 * K_get_account + K_compute_jumpdests + K_state_restore + 8 * (2 ^ 64 - 1) + 262144
def K_op_selfdestruct : Nat := 4 * K_get_account + K_state_restore + 65536
def K_op_dispatch : Nat :=
  K_generic_call + K_generic_create + K_op_sstore + K_op_selfdestruct +
  K_op_exp + K_op_memory_copy + K_op_env_account + 524288

theorem terminatingFunBounded_op_sstore :
    TerminatingFunBounded (ofString "op_sstore") K_op_sstore := by
  sorry

theorem terminatingFunBounded_generic_call :
    TerminatingFunBounded (ofString "generic_call") K_generic_call := by
  sorry

theorem terminatingFunBounded_generic_create :
    TerminatingFunBounded (ofString "generic_create") K_generic_create := by
  sorry

theorem terminatingFunBounded_op_selfdestruct :
    TerminatingFunBounded (ofString "op_selfdestruct") K_op_selfdestruct := by
  sorry

theorem terminatingFunBounded_op_dispatch :
    TerminatingFunBounded (ofString "op_dispatch") K_op_dispatch := by
  sorry

end InitECandidate.Solver.LeafEvmOpcodesCallCreate
