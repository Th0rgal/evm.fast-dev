import InitECandidate.Solver.PanTerminatingBounded
import InitECandidate.Solver.LeafModInvBin
import InitECandidate.Solver.GuestBoundCryptoDiv
import InitECandidate.Solver.GuestBoundCryptoPrecompiles

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-!
# `InitECandidate.Solver.LeafBn254` — Track B Leaf 08 (`< 350` LOC)

Frozen Spec Contract (`1 Cluster = 1 Leaf File < 350 LOC = 1 Worker`):
Bounds Knuth multi-word division `bn_divmnu`, degree-12 polynomial extended GCD `fq12_inv`, and
the BN254 (`alt_bn128`) precompile cluster:
- `bn_divmnu` (L10303: Knuth Algorithm D `j >+ 0`, `i >+ 0`, `while again == 1` at most 2 qhat
  adjustments),
- `fq12_inv` (L11454: polynomial extended GCD over `Fp[u]/(u^12 - ...)` where `fq_poly_deg(r1, 13) ≤ 12`
  strictly decreases each outer iteration, inner division loop `while d0 >= d1` decreases `d0`),
- `pre_alt_bn128_add` (0x06), `pre_alt_bn128_mul` (0x07), `pre_alt_bn128_pairing_check` (0x08).

Forbidden: NO `sorry`, `axiom`, `native_decide`, `bv_decide`, `Lean.ofReduceBool`,
`InitECandidate.Proofs.Bounded*`, `InitECandidate.Proofs.FullBaseline`, or `Guest.Ast`.
-/

namespace InitECandidate.Solver.LeafBn254

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.LeafModInvBin
open InitECandidate.Solver.GuestBoundCryptoDiv
open InitECandidate.Solver.GuestBoundCryptoPrecompiles

def K_bn_divmnu : Nat := 16 * (2 ^ 64 - 1) + 65536
def K_fq12_inv : Nat := 16 * 16 * (K_modinv_bin + 16384) + 262144
def K_pre_alt_bn128_add : Nat := 4 * K_modinv_bin + 65536
def K_pre_alt_bn128_mul : Nat := 256 * K_pre_alt_bn128_add + 65536
def K_pre_alt_bn128_pairing_check : Nat := 16 * (2 ^ 64 - 1) * (K_fq12_inv + 262144) + 1048576

theorem terminatingFunBounded_bn_divmnu :
    TerminatingFunBounded (ofString "bn_divmnu") K_bn_divmnu := by
  sorry

theorem terminatingFunBounded_fq12_inv :
    TerminatingFunBounded (ofString "fq12_inv") K_fq12_inv := by
  sorry

theorem terminatingFunBounded_pre_alt_bn128_add :
    TerminatingFunBounded (ofString "pre_alt_bn128_add") K_pre_alt_bn128_add := by
  sorry

theorem terminatingFunBounded_pre_alt_bn128_mul :
    TerminatingFunBounded (ofString "pre_alt_bn128_mul") K_pre_alt_bn128_mul := by
  sorry

theorem terminatingFunBounded_pre_alt_bn128_pairing_check :
    TerminatingFunBounded (ofString "pre_alt_bn128_pairing_check") K_pre_alt_bn128_pairing_check := by
  sorry

end InitECandidate.Solver.LeafBn254
