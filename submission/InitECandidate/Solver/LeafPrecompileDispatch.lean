import InitECandidate.Solver.PanTerminatingBounded
import InitECandidate.Solver.LeafSecpP256
import InitECandidate.Solver.LeafBn254
import InitECandidate.Solver.LeafBlsPrecompiles
import InitECandidate.Solver.GuestBoundCryptoPrecompiles
import InitECandidate.Solver.GuestBoundEvmFrames

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-!
# `InitECandidate.Solver.LeafPrecompileDispatch` — Track B Leaf 13 (`< 350` LOC)

Frozen Spec Contract (`1 Cluster = 1 Leaf File < 350 LOC = 1 Worker`):
Aggregates all Ethereum precompiles (`0x01` ECRECOVER through `0x11` BLS12_MAP_FP2_TO_G2 plus
`0x0100` P256VERIFY) into `run_precompile` and child-frame setup/epilogue helpers:
- `pre_sha256` (0x02), `pre_ripemd160` (0x03), `pre_identity` (0x04),
  `pre_blake2f` (0x09),
- `run_precompile` (dispatches 0x01..0x11 and 0x0100),
- `compute_jumpdests` (`while pc <+ code_len`),
- `frame_epilogue`, `finish_child`.

Imports `LeafSecpP256`, `LeafBn254`, `LeafBlsPrecompiles`, `GuestBoundCryptoPrecompiles`,
and `GuestBoundEvmFrames`.

Forbidden: NO `sorry`, `axiom`, `native_decide`, `bv_decide`, `Lean.ofReduceBool`,
`InitECandidate.Proofs.Bounded*`, `InitECandidate.Proofs.FullBaseline`, or `Guest.Ast`.
-/

namespace InitECandidate.Solver.LeafPrecompileDispatch

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.LeafModInvBin
open InitECandidate.Solver.LeafSecpP256
open InitECandidate.Solver.LeafBn254
open InitECandidate.Solver.LeafBlsPrecompiles
open InitECandidate.Solver.GuestBoundEvmFrames

def K_compute_jumpdests : Nat := 4 * (2 ^ 64 - 1) + 4096

def K_run_precompile : Nat :=
  K_pre_ecrecover + K_pre_modexp + K_pre_alt_bn128_pairing_check +
  K_pre_kzg_point_evaluation + K_pre_bls_g1_msm + K_pre_bls_g2_msm +
  K_pre_bls_pairing + K_pre_bls_map_fp2_to_g2 + K_pre_p256verify +
  8 * (2 ^ 64 - 1) + 4194304

def K_frame_epilogue : Nat := 4 * (2 ^ 64 - 1) + 65536
def K_finish_child : Nat := 8 * (2 ^ 64 - 1) + 131072

theorem terminatingFunBounded_compute_jumpdests :
    TerminatingFunBounded (ofString "compute_jumpdests") K_compute_jumpdests := by
  sorry

theorem terminatingFunBounded_run_precompile :
    TerminatingFunBounded (ofString "run_precompile") K_run_precompile := by
  sorry

theorem terminatingFunBounded_frame_epilogue :
    TerminatingFunBounded (ofString "frame_epilogue") K_frame_epilogue := by
  sorry

theorem terminatingFunBounded_finish_child :
    TerminatingFunBounded (ofString "finish_child") K_finish_child := by
  sorry

end InitECandidate.Solver.LeafPrecompileDispatch
