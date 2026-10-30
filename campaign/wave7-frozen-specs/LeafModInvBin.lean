import InitECandidate.Solver.PanTerminatingBounded
import InitECandidate.Solver.GuestBoundCryptoDiv
import InitECandidate.Solver.GuestBoundCryptoPrecompiles

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-!
# `InitECandidate.Solver.LeafModInvBin` — Track B Leaf 06 (`< 350` LOC)

Frozen Spec Contract (`1 Cluster = 1 Leaf File < 350 LOC = 1 Worker`):
Bounds the 256-bit binary extended GCD modular inverse and big-integer MODEXP precompile cluster:
- `modinv_bin` (L2868: 256-bit binary extended GCD on `u, v`; every iteration halves `u`, halves `v`,
  or replaces `max(u,v)` by `|u - v|` then halves on the next step ⇒ `bitlen(u) + bitlen(v) ≤ 512`
  strictly decreases),
- `fp_inv`, `fn_inv`, `u256_addmod`, `u256_mulmod`,
- `modexp`, `pre_modexp` (EIP-198 / EIP-7883 arbitrary-precision modular exponentiation).

Imports 0-`sorry` helpers from `GuestBoundCryptoDiv` and `GuestBoundCryptoPrecompiles`.

Forbidden: NO `sorry`, `axiom`, `native_decide`, `bv_decide`, `Lean.ofReduceBool`,
`InitECandidate.Proofs.Bounded*`, `InitECandidate.Proofs.FullBaseline`, or `Guest.Ast`.
-/

namespace InitECandidate.Solver.LeafModInvBin

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.GuestBoundCryptoDiv
open InitECandidate.Solver.GuestBoundCryptoPrecompiles

def K_modinv_bin : Nat := 2048 * 256 + 4096
def K_fp_inv : Nat := K_modinv_bin + 4096
def K_fn_inv : Nat := K_modinv_bin + 4096
def K_u256_addmod : Nat := 4096
def K_u256_mulmod : Nat := 16384
def K_pre_modexp : Nat := 64 * (2 ^ 64 - 1) + 1048576

theorem terminatingFunBounded_modinv_bin :
    TerminatingFunBounded (ofString "modinv_bin") K_modinv_bin := by
  sorry

theorem terminatingFunBounded_fp_inv :
    TerminatingFunBounded (ofString "fp_inv") K_fp_inv := by
  sorry

theorem terminatingFunBounded_fn_inv :
    TerminatingFunBounded (ofString "fn_inv") K_fn_inv := by
  sorry

theorem terminatingFunBounded_u256_addmod :
    TerminatingFunBounded (ofString "u256_addmod") K_u256_addmod := by
  sorry

theorem terminatingFunBounded_u256_mulmod :
    TerminatingFunBounded (ofString "u256_mulmod") K_u256_mulmod := by
  sorry

theorem terminatingFunBounded_pre_modexp :
    TerminatingFunBounded (ofString "pre_modexp") K_pre_modexp := by
  sorry

end InitECandidate.Solver.LeafModInvBin
