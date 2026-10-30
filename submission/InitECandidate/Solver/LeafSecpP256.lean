import InitECandidate.Solver.PanTerminatingBounded
import InitECandidate.Solver.LeafModInvBin
import InitECandidate.Solver.GuestBoundCryptoPrecompiles

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-!
# `InitECandidate.Solver.LeafSecpP256` — Track B Leaf 07 (`< 350` LOC)

Frozen Spec Contract (`1 Cluster = 1 Leaf File < 350 LOC = 1 Worker`):
Bounds the `secp256k1` (`ECRECOVER` / EIP-7702 authority recovery) and `secp256r1` (`P256VERIFY`,
EIP-7951) elliptic-curve arithmetic cluster:
- `p256_fp_mul` (L10495: unrolled limb product + carry reduction `while c < 0`, `while c > 0`),
- `p256_fp_sqr` (L10553: unrolled limb square + carry reduction `while c < 0`, `while c > 0`),
- `p256_fp_inv`, `p256_ec_double`, `p256_ec_add_affine`, `p256_ec_mul2`, `p256_verify`, `pre_p256verify`,
- `secp256k1_recover`, `secp256k1_address_of_point`, `secp256k1_ecrecover`, `pre_ecrecover`.

Imports `LeafModInvBin`, `GuestBoundCryptoPrecompiles`, and `PanTerminatingBounded`.

Forbidden: NO `sorry`, `axiom`, `native_decide`, `bv_decide`, `Lean.ofReduceBool`,
`InitECandidate.Proofs.Bounded*`, `InitECandidate.Proofs.FullBaseline`, or `Guest.Ast`.
-/

namespace InitECandidate.Solver.LeafSecpP256

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.LeafModInvBin
open InitECandidate.Solver.GuestBoundCryptoPrecompiles

def K_p256_fp_mul : Nat := 1024
def K_p256_fp_sqr : Nat := 1024
def K_p256_ec_mul2 : Nat := 256 * 32 * (K_p256_fp_mul + K_p256_fp_sqr + 256) + 65536
def K_pre_p256verify : Nat := 4 * K_p256_ec_mul2 + 4 * K_modinv_bin + 65536
def K_secp256k1_ecrecover : Nat := 4 * K_p256_ec_mul2 + 4 * K_modinv_bin + 131072
def K_pre_ecrecover : Nat := K_secp256k1_ecrecover + 8192

theorem terminatingFunBounded_p256_fp_mul :
    TerminatingFunBounded (ofString "p256_fp_mul") K_p256_fp_mul := by
  sorry

theorem terminatingFunBounded_p256_fp_sqr :
    TerminatingFunBounded (ofString "p256_fp_sqr") K_p256_fp_sqr := by
  sorry

theorem terminatingFunBounded_pre_p256verify :
    TerminatingFunBounded (ofString "pre_p256verify") K_pre_p256verify := by
  sorry

theorem terminatingFunBounded_secp256k1_ecrecover :
    TerminatingFunBounded (ofString "secp256k1_ecrecover") K_secp256k1_ecrecover := by
  sorry

theorem terminatingFunBounded_pre_ecrecover :
    TerminatingFunBounded (ofString "pre_ecrecover") K_pre_ecrecover := by
  sorry

end InitECandidate.Solver.LeafSecpP256
