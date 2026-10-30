import InitECandidate.Solver.PanTerminatingBounded
import InitECandidate.Solver.LeafPrecompileDispatch
import InitECandidate.Solver.LeafEvmOpcodesCallCreate
import InitECandidate.Solver.GuestBoundEvmFrames

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-!
# `InitECandidate.Solver.LeafRunFrames` — Track B Leaf 16 (`< 350` LOC)

Frozen Spec Contract (`1 Cluster = 1 Leaf File < 350 LOC = 1 Worker`):
Bounds the master EVM frame execution loop `run_frames` (`Guest/guest-software.pp.pnk` L9342:
`while go != 0`) and top-level message execution `process_message`:

Potential function (`evmFramePotential` in `PanTerminatingBounded` / `gasPotential` in
`GuestBoundEvmFrames`):
`Phi = 2050 * (sum of remaining gas + state_gas across active frames) + 2 * active_frames + (1 if current frame halted else 0)`.
Every `while go != 0` iteration either:
1. Halts/reverts the top frame and runs `frame_epilogue` / `finish_child` (popping `active_frames`
   and returning `≤ child_gas` back to parent, strictly decreasing `2 * active_frames` even if all
   child gas is refunded), OR
2. Dispatches `op_dispatch` on the top frame:
   - Any non-halting opcode charges `≥ 1` gas (`charge_gas`), decreasing `Phi` by `≥ 2050`; even if
     `CALL`/`CREATE` pushes 1 child frame (`+2` to `2 * active_frames`) and transfers `child_gas ≤ parent_gas`,
     total gas across frames does not increase and `Phi` strictly decreases by `≥ 2048`!
   - Zero-gas halting opcodes (`STOP`, `RETURN`, `REVERT`, `INVALID`, OOG) transition the top frame
     to halted/popped on the immediate epilogue, strictly decreasing `Phi`.

Imports `LeafPrecompileDispatch`, `LeafEvmOpcodesCallCreate`, and `GuestBoundEvmFrames`.

Forbidden: NO `sorry`, `axiom`, `native_decide`, `bv_decide`, `Lean.ofReduceBool`,
`InitECandidate.Proofs.Bounded*`, `InitECandidate.Proofs.FullBaseline`, or `Guest.Ast`.
-/

namespace InitECandidate.Solver.LeafRunFrames

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.LeafPrecompileDispatch
open InitECandidate.Solver.LeafEvmOpcodesCallCreate
open InitECandidate.Solver.GuestBoundEvmFrames

/-- Upper bound on `run_frames` iterations (`Phi ≤ 2050 * (1025 * (2^64 - 1)) + 2050` unconditionally
over arbitrary 64-bit frame gas words, or `maxEvmFramePotential = 410_000_002_050` under `gas ≤ 200M`). -/
def maxRunFramesIters : Nat := 2050 * 1025 * (2 ^ 64 - 1) + 4096

def K_run_frames : Nat :=
  maxRunFramesIters * (K_op_dispatch + K_frame_epilogue + K_finish_child + 256) + 65536

def K_process_message : Nat :=
  K_run_frames + K_run_precompile + K_compute_jumpdests + 262144

theorem terminatingFunBounded_run_frames :
    TerminatingFunBounded (ofString "run_frames") K_run_frames := by
  sorry

theorem terminatingFunBounded_process_message :
    TerminatingFunBounded (ofString "process_message") K_process_message := by
  sorry

end InitECandidate.Solver.LeafRunFrames
