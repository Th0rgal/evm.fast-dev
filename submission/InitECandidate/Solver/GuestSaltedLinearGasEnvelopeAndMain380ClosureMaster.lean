import InitECandidate.Solver.GuestCompleteMainAllSubsystemsSynthesisMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestSaltedLinearGasEnvelopeAndMain380ClosureMaster`

Under a salted `htab_hash` with probe runs `≤ L = 8` on every table, the unsalted quadratic block
term `B²/40` (`10¹¹` at `B = 2·10⁶` units, `3.61·10¹¹` at `3.8·10⁶`) is replaced by a linear term.
Per 100-gas unit the Guest does a bounded number of table operations; at `2` ticks per probe step
and `≤ 8` steps per find, we charge **`1,000` ticks per unit** for all table work (conservative,
hand bound: `≥ 60` finds per unit at `L = 8`).

The remaining non-quadratic part of the envelope (`56,088,992,805` at 200M) is kept unchanged.
It still contains collision-derived terms (address tables, probes) computed unsalted, so the
totals below are upper bounds, not tight.

`L ≤ 8` is the expected run length of a salted table at load `≤ 1/2`, not a worst case: a salt
makes long runs improbable, it does not forbid them.
-/

namespace InitECandidate.Solver.GuestSaltedLinearGasEnvelopeAndMain380ClosureMaster

open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open InitECandidate.Solver.GuestCompleteMainAllSubsystemsSynthesisMaster (main200 main380 main_val main380_val)

def saltedTable (units : Nat) : Nat := 1000 * units

def salted200 : Nat := main200 - 100000000000 + saltedTable 2000000
def salted380 : Nat := main380 - 361000000000 + saltedTable 3800000

/-- 1. Per-unit table charge covers `60` finds of `8` steps at `2` ticks. -/
theorem per_unit : 60 * 8 * 2 ≤ 1000 := by decide

/-- 2. Unsalted quadratic terms vs. salted linear terms. -/
theorem quad_vs_lin : 2000000 * 2000000 / 40 = 100000000000 ∧ saltedTable 2000000 = 2000000000 ∧
    3800000 * 3800000 / 40 = 361000000000 ∧ saltedTable 3800000 = 3800000000 := by decide

/-- 3. Salted gas envelopes: `58,088,992,805` (200M) and `110,369,086,329` (380M). -/
theorem salted_env : 156088992805 - 100000000000 + 2000000000 = 58088992805 ∧
    467569086329 - 361000000000 + 3800000000 = 110369086329 := by decide

/-- 4. **`main200` salted**: `102,485,906,743`. -/
theorem salted200_val : salted200 = 102485906743 := by
  unfold salted200 saltedTable; rw [main_val]

/-- 5. **`main380` salted**: `154,766,000,267`. -/
theorem salted380_val : salted380 = 154766000267 := by
  unfold salted380 saltedTable; rw [main380_val]

/-- 6. `main200` salted: `8×` passes (margin `80,832,671,530`), `9×` fails. -/
theorem slope200 : 8 * 102485906743 < yukon ∧ yukon - 8 * 102485906743 = 80832671530 ∧
    yukon < 9 * 102485906743 := by decide

/-- 7. **`main380` salted (adversarial system code)**: `5×` passes (margin `126,889,924,139`),
`6×` fails. -/
theorem slope380 : 5 * 154766000267 < yukon ∧ yukon - 5 * 154766000267 = 126889924139 ∧
    yukon < 6 * 154766000267 := by decide

/-- 8. The salt alone removes `98,000,000,000` (200M) and `357,200,000,000` (380M). -/
theorem salt_gain : 100000000000 - 2000000000 = 98000000000 ∧
    361000000000 - 3800000000 = 357200000000 := by decide

/-- 9. Sensitivity: the `8×` / `5×` verdicts survive up to `6,052` / `7,678` ticks per unit. -/
theorem per_unit_slack :
    8 * (200485906743 - 100000000000 + 6052 * 2000000) < yukon ∧
      yukon < 8 * (200485906743 - 100000000000 + 6053 * 2000000) ∧
    5 * (511966000267 - 361000000000 + 7678 * 3800000) < yukon ∧
      yukon < 5 * (511966000267 - 361000000000 + 7679 * 3800000) := by decide

/-- 10. Unsalted for comparison: `main200` only `4×`, `main380` only `1×`. -/
theorem unsalted_cmp : 4 * main200 < yukon ∧ yukon < 5 * main200 ∧ yukon < 2 * main380 := by
  rw [main_val, main380_val]; decide

end InitECandidate.Solver.GuestSaltedLinearGasEnvelopeAndMain380ClosureMaster
