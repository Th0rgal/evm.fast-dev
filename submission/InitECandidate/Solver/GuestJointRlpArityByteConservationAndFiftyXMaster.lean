import InitECandidate.Solver.GuestByteCoupledWitnessResolveAndThirtyFiveXMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestJointRlpArityByteConservationAndFiftyXMaster`

`decodeMemo = 326 · 33,554,428` (`GuestWitnessDecodeExactTicksPerByteAudit`) charged every
node as a branch (`326` ticks) and allowed `I/4` nodes. Accepted nodes are 2-item (leaf/ext,
`≤ 48` ticks, `≥ 4` RLP bytes) or 17-item branches (`326` ticks, `≥ 18` bytes: list header +
17 items of `≥ 1` byte). Each 32-byte hash ref costs `32` extra bytes and `2 · 8 = 16` probe
ticks. Under DAG memoization node bodies are disjoint slices of `I = 134,217,712`:
`4 N₂ + 18 N₁₇ + 32 H ≤ I`.

Per byte: branch `326/18 ≈ 18.1`, 2-item `48/4 = 12`, ref `16/32 = 0.5`. The joint maximum of
`48 N₂ + 326 N₁₇ + 16 H` `≤ ⌊326 I / 18⌋ = 2,430,831,895` (scale by 18); the integer optimum `2,430,831,810` (all branch + two leaves) is within `85`.

`buildNodedb = 3,038,649,506` is kept: `nodedb_build` hashes every witness list entry before
any arity check, so its `I/4` entry count is not reduced by arity.
-/

namespace InitECandidate.Solver.GuestJointRlpArityByteConservationAndFiftyXMaster

open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

def inputBytes : Nat := 134217712
def jointCost (n2 n17 h : Nat) : Nat := 48 * n2 + 326 * n17 + 16 * h

def decodeProbesOld : Nat := 10938743528 + 65075248
def decodeProbesNew : Nat := 326 * inputBytes / 18

def main200 : Nat := 24381873932 - decodeProbesOld + decodeProbesNew
def main380 : Nat := 32488958762 - decodeProbesOld + decodeProbesNew

/-- 1. **Joint bound**: under byte conservation, decode + resolve probes `≤ 2,430,831,895`. -/
theorem joint_bound (n2 n17 h : Nat) (hb : 4 * n2 + 18 * n17 + 32 * h ≤ inputBytes) :
    jointCost n2 n17 h ≤ 2430831895 := by
  unfold jointCost inputBytes at *
  have : 18 * (48 * n2 + 326 * n17 + 16 * h) ≤ 326 * 134217712 := by omega
  omega

/-- 2. Attained: `7,456,539` branches, two 2-item nodes, no refs. -/
theorem joint_tight : 4 * 2 + 18 * 7456539 + 32 * 0 ≤ inputBytes ∧
    jointCost 2 7456539 0 = 2430831810 ∧ 2430831895 - 2430831810 = 85 ∧ inputBytes < 18 * 7456540 := by decide

/-- 3. Branch count bound: `⌊I/18⌋ = 7,456,539`, `4.5×` below `I/4`. -/
theorem branch_count : inputBytes / 18 = 7456539 ∧ 9 * 7456539 ≤ 2 * 33554428 := by decide

/-- 4. Gain over the old decode + probe rows: `8,572,986,881`. -/
theorem gain : decodeProbesOld - decodeProbesNew = 8572986881 := by decide

/-- 5. **`main200 = 15,808,887,051`: `56×` passes, `57×` fails; below `Y/50`.** -/
theorem main200_slope : main200 = 15808887051 ∧ 56 * main200 < yukon ∧
    yukon < 57 * main200 ∧ 50 * main200 < yukon := by decide

/-- 6. **`main380 = 23,915,971,881`: `37×` passes, `38×` fails.** -/
theorem main380_slope : main380 = 23915971881 ∧ 37 * main380 < yukon ∧ yukon < 38 * main380 := by
  decide

/-- 7. Margins at the passing factors. -/
theorem margins : yukon - 56 * main200 = 15422250618 ∧ yukon - 37 * main380 = 15828965877 := by
  decide

/-- 8. `buildNodedb` is now the largest witness row (`> 19 %` of `main200`). -/
theorem build_dominates : 100 * 3038649506 > 19 * main200 ∧ 3038649506 > decodeProbesNew := by
  decide

end InitECandidate.Solver.GuestJointRlpArityByteConservationAndFiftyXMaster
