import InitECandidate.Solver.PanTerminatingBounded
import InitECandidate.Solver.LeafBlsFpInv
import InitECandidate.Solver.LeafModInvBin
import InitECandidate.Solver.GuestBoundCryptoPrecompiles

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-!
# `InitECandidate.Solver.LeafBlsPrecompiles` — Track B Leaf 10 (`< 350` LOC)

Frozen Spec Contract (`1 Cluster = 1 Leaf File < 350 LOC = 1 Worker`):
Bounds the EIP-2537 BLS12-381 precompiles (0x0b..0x11) and EIP-4844 KZG point evaluation (0x0a):
- `pre_kzg_point_evaluation` (0x0a),
- `pre_bls_g1_add` (0x0b), `pre_bls_g1_msm` (0x0c),
- `pre_bls_g2_add` (0x0d), `pre_bls_g2_msm` (0x0e),
- `pre_bls_pairing` (0x0f),
- `pre_bls_map_fp_to_g1` (0x10), `pre_bls_map_fp2_to_g2` (0x11).

Imports `LeafBlsFpInv`, `LeafModInvBin`, and `GuestBoundCryptoPrecompiles`.

Forbidden: NO `sorry`, `axiom`, `native_decide`, `bv_decide`, `Lean.ofReduceBool`,
`InitECandidate.Proofs.Bounded*`, `InitECandidate.Proofs.FullBaseline`, or `Guest.Ast`.
-/

namespace InitECandidate.Solver.LeafBlsPrecompiles

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.LeafBlsFpInv
open InitECandidate.Solver.LeafModInvBin
open InitECandidate.Solver.GuestBoundCryptoPrecompiles

def K_pre_kzg_point_evaluation : Nat := 8 * (K_fp12_inv + K_g1_mul + K_g2_mul) + 2097152
def K_pre_bls_g1_add : Nat := 4 * K_bls_fp_inv + 131072
def K_pre_bls_g1_msm : Nat := 8 * (2 ^ 64 - 1) * K_g1_mul + 262144
def K_pre_bls_g2_add : Nat := 4 * K_fp2_inv + 262144
def K_pre_bls_g2_msm : Nat := 8 * (2 ^ 64 - 1) * K_g2_mul + 524288
def K_pre_bls_pairing : Nat := 16 * (2 ^ 64 - 1) * (K_fp12_inv + 524288) + 2097152
def K_pre_bls_map_fp_to_g1 : Nat := 8 * K_bls_fp_inv + 524288
def K_pre_bls_map_fp2_to_g2 : Nat := 8 * K_fp2_inv + 1048576

theorem terminatingFunBounded_pre_kzg_point_evaluation :
    TerminatingFunBounded (ofString "pre_kzg_point_evaluation") K_pre_kzg_point_evaluation := by
  sorry

theorem terminatingFunBounded_pre_bls_g1_add :
    TerminatingFunBounded (ofString "pre_bls_g1_add") K_pre_bls_g1_add := by
  sorry

theorem terminatingFunBounded_pre_bls_g1_msm :
    TerminatingFunBounded (ofString "pre_bls_g1_msm") K_pre_bls_g1_msm := by
  sorry

theorem terminatingFunBounded_pre_bls_g2_add :
    TerminatingFunBounded (ofString "pre_bls_g2_add") K_pre_bls_g2_add := by
  sorry

theorem terminatingFunBounded_pre_bls_g2_msm :
    TerminatingFunBounded (ofString "pre_bls_g2_msm") K_pre_bls_g2_msm := by
  sorry

theorem terminatingFunBounded_pre_bls_pairing :
    TerminatingFunBounded (ofString "pre_bls_pairing") K_pre_bls_pairing := by
  sorry

theorem terminatingFunBounded_pre_bls_map_fp_to_g1 :
    TerminatingFunBounded (ofString "pre_bls_map_fp_to_g1") K_pre_bls_map_fp_to_g1 := by
  sorry

theorem terminatingFunBounded_pre_bls_map_fp2_to_g2 :
    TerminatingFunBounded (ofString "pre_bls_map_fp2_to_g2") K_pre_bls_map_fp2_to_g2 := by
  sorry

end InitECandidate.Solver.LeafBlsPrecompiles
