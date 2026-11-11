import InitECandidate.Solver.Wave8GuestInv.K_tightening.V23Prewarm
import Guest.GasLimit

/-!
# v3 covered-gas and scratch-arena tightening

The v3 cutover specialises two constants:

* the covered gas cap is `200_000_000`, the literal used by the challenge
  statement (`docs/CHALLENGE.md`); and
* the chain limit is `maxChainV3 = 8884`, while each live frame reserves
  `1408` bytes of the `12_509_184`-byte scratch arena.

The arithmetic below is closed: `8884 * 1408 = 12_508_672`, leaving `512`
bytes of slack in the arena.  The gas theorem is the policy shape used by the
source certificate: a declared limit within `200_000_000` is within the v3 cap.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv

open K

/-- v3 covered-gas cap. -/
def coveredGasMaxV3 : Nat := 200000000

/-- The v3 cap is the challenge literal. -/
theorem coveredGasMaxV3_eq : coveredGasMaxV3 = 200000000 := rfl

/-- v3 covered-gas tightening: a declared gas limit under the policy bound is
under the v3 cap. -/
theorem declaredGasLimit_le_coveredGasMaxV3 {input : Guest.InputBlob}
    (h : Guest.GasLimit.declaredGasLimit input ≤ 200000000) :
    Guest.GasLimit.declaredGasLimit input ≤ coveredGasMaxV3 := by
  simpa only [coveredGasMaxV3] using h

/-- Scratch bytes reserved by one live frame. -/
def frameBytesV3 : Nat := 1408

/-- Total scratch arena available to the frame stack. -/
def scratchArenaV3 : Nat := 12509184

/-- The v3 chain limit is the literal `8884`. -/
theorem maxChainV3_eq : maxChainV3 = 8884 := rfl

/-- The v3 chain limit is at most `8884`. -/
theorem maxChainV3_le_8884 : maxChainV3 ≤ 8884 := le_rfl

/-- The full v3 frame stack fits in the scratch arena. -/
theorem maxChainV3_scratch_fits : maxChainV3 * frameBytesV3 ≤ scratchArenaV3 := by
  decide

/-- General scratch-arena disjointness bound: any chain of at most `8884`
frames, `1408` bytes each, fits in the `12_509_184`-byte arena. -/
theorem scratch_fits_of_le_8884 {c : Nat} (hc : c ≤ 8884) :
    c * 1408 ≤ 12509184 := by
  have hmul : c * 1408 ≤ 8884 * 1408 := Nat.mul_le_mul_right 1408 hc
  have hnum : 8884 * 1408 ≤ 12509184 := by decide
  omega

/-- The v3 arena leaves `512` bytes of slack after the full frame stack. -/
theorem scratchArenaV3_slack : scratchArenaV3 - maxChainV3 * frameBytesV3 = 512 := by
  decide

end InitECandidate.Solver.Wave8GuestInv
