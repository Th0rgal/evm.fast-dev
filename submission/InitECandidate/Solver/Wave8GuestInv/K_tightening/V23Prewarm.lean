import InitECandidate.Solver.Wave8GuestInv.Bounds

/-!
v2 / v3 `K`-tightening pre-warm, checked against the *real* generated cost
definitions in `Bounds.lean` (not hand-copied numerals).

* v2 target: `evmPotMax = 2^160` instead of the v1 `evmPotMax`.
* v3 target: `maxChain = 8884` instead of `16384`.

The only proofs here are closed Nat arithmetic and monotonicity of the
`run_frames` bound; the genuine cutover still needs
`EvmInv s → evmPot s < evmPotMaxV2` and the covered-gas bound.
-/

set_option maxRecDepth 100000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv

open K

/-- The blanket chain limit is the literal `16384`. -/
theorem maxChain_eq : maxChain = 16384 := rfl

/-- The v1 potential bound, unfolded from the real definitions. -/
theorem evmPotMax_eq :
    evmPotMax = (2 * 16384 * 2 ^ 64 + 1) * (2 * 16384 + 2) * (16384 * 2 ^ 64) := by
  decide

/-- v2 target potential bound. -/
def evmPotMaxV2 : Nat := 2 ^ 160

/-- The v2 potential is strictly below the v1 potential. -/
theorem evmPotMaxV2_lt_evmPotMax : evmPotMaxV2 < evmPotMax := by
  rw [evmPotMax_eq]
  decide

/-- v3 specialized chain limit. -/
def maxChainV3 : Nat := 8884

/-- The v3 chain limit is strictly below the blanket limit. -/
theorem maxChainV3_lt_maxChain : maxChainV3 < maxChain := by
  rw [maxChain_eq]
  decide

/-- Potential bound parameterized by the chain limit (same formula as `evmPotMax`). -/
def evmPotMaxWith (c : Nat) : Nat := (2 * c * 2 ^ 64 + 1) * (2 * c + 2) * (c * 2 ^ 64)

/-- The parameterized formula agrees with `evmPotMax` at the blanket limit. -/
theorem evmPotMaxWith_maxChain : evmPotMaxWith maxChain = evmPotMax := by
  rw [evmPotMax_eq]; rfl

/-- Specializing the chain limit to 8884 strictly lowers the potential bound. -/
theorem evmPotMaxV3_lt_evmPotMax : evmPotMaxWith maxChainV3 < evmPotMax := by
  rw [evmPotMax_eq]
  decide

/-- The closed coefficient multiplying `(evmPotMax + 1)` in `run_frames`. -/
def runFramesCoeff : Nat :=
  Nat.max (0) (Nat.max (0) (Nat.max (0) ((«op_dispatch» + 1) + («frame_exception» + 1)))) +
    Nat.max ((«frame_epilogue» + 1) + Nat.max (0) ((«finish_child» + 1) + («frame_exception» + 1))) (0) + 1

/-- `run_frames` is exactly the potential bound times a closed positive coefficient. -/
theorem run_frames_eq : «run_frames» = (evmPotMax + 1) * runFramesCoeff := rfl

theorem runFramesCoeff_pos : 0 < runFramesCoeff := by
  unfold runFramesCoeff
  omega

/-- Replacing the v1 potential by the v2 potential strictly lowers `run_frames`. -/
theorem run_framesV2_lt : (evmPotMaxV2 + 1) * runFramesCoeff < «run_frames» := by
  rw [run_frames_eq]
  exact Nat.mul_lt_mul_of_pos_right (by rw [evmPotMaxV2]; decide) runFramesCoeff_pos

/-- Replacing the v1 potential by the v3 potential strictly lowers `run_frames`. -/
theorem run_framesV3_lt : (evmPotMaxWith maxChainV3 + 1) * runFramesCoeff < «run_frames» := by
  rw [run_frames_eq]
  exact Nat.mul_lt_mul_of_pos_right (by rw [evmPotMaxWith]; decide) runFramesCoeff_pos

end InitECandidate.Solver.Wave8GuestInv
