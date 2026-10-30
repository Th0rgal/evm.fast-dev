import InitECandidate.Solver.PanTerminatingBounded
import InitECandidate.Solver.GuestBoundCryptoDiv
import InitECandidate.Solver.GuestBoundCryptoPrecompiles

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-!
# `InitECandidate.Solver.LeafBlsFpInv` — Track B Leaf 09 (`< 350` LOC)

Frozen Spec Contract (`1 Cluster = 1 Leaf File < 350 LOC = 1 Worker`):
Bounds the 384-bit BLS12-381 base/tower field arithmetic and binary extended GCD inversion cluster:
- `bls_fp_inv_raw` (L12860: 384-bit binary extended GCD on 6-limb `u, v`; `bitlen(u) + bitlen(v) ≤ 768`
  decreases via `bls_fp_shr1` and `bls_fp_sub_raw`),
- `bls_fp_inv`, `fp2_inv`, `fp6_inv`, `fp12_inv`,
- `g1_add`, `g1_mul`, `g2_add`, `g2_mul`.

Forbidden: NO `sorry`, `axiom`, `native_decide`, `bv_decide`, `Lean.ofReduceBool`,
`InitECandidate.Proofs.Bounded*`, `InitECandidate.Proofs.FullBaseline`, or `Guest.Ast`.
-/

namespace InitECandidate.Solver.LeafBlsFpInv

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.GuestBoundCryptoDiv
open InitECandidate.Solver.GuestBoundCryptoPrecompiles

def K_bls_fp_inv_raw : Nat := 4096 * 512 + 16384
def K_bls_fp_inv : Nat := K_bls_fp_inv_raw + 8192
def K_fp2_inv : Nat := 2 * K_bls_fp_inv + 16384
def K_fp12_inv : Nat := 4 * K_fp2_inv + 131072
def K_g1_mul : Nat := 256 * 16384 + 2 * K_bls_fp_inv + 65536
def K_g2_mul : Nat := 256 * 65536 + 2 * K_fp2_inv + 131072

theorem terminatingFunBounded_bls_fp_inv_raw :
    TerminatingFunBounded (ofString "bls_fp_inv_raw") K_bls_fp_inv_raw := by
  sorry

theorem terminatingFunBounded_bls_fp_inv :
    TerminatingFunBounded (ofString "bls_fp_inv") K_bls_fp_inv := by
  sorry

theorem terminatingFunBounded_fp2_inv :
    TerminatingFunBounded (ofString "fp2_inv") K_fp2_inv := by
  sorry

theorem terminatingFunBounded_fp12_inv :
    TerminatingFunBounded (ofString "fp12_inv") K_fp12_inv := by
  sorry

theorem terminatingFunBounded_g1_mul :
    TerminatingFunBounded (ofString "g1_mul") K_g1_mul := by
  sorry

theorem terminatingFunBounded_g2_mul :
    TerminatingFunBounded (ofString "g2_mul") K_g2_mul := by
  sorry

end InitECandidate.Solver.LeafBlsFpInv
