import InitECandidate.Solver.GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestSszOffsetWitnessNodeMinBytesAndSixtyEightXMaster`

**Code check (`guest.pp.pnk` wt-2).**
* `decode_stateless_input` (l.2984): witness container = 3 offsets (`state`, `codes`,
  `headers`), each list decoded by `decode_bytes_list` → `ssz_split_var_list` (l.2859):
  `count = first / 4`, one `uint32` offset per entry, offsets nondecreasing and `≤ len`.
  So every `nodedb_build` entry (l.3691, `si+40/48` nodes, `si+56/64` codes) costs **4 offset
  bytes**; empty entries (`o_i = o_{i+1}`) are accepted and still hashed.
* `_decode_step` (l.3778) 2-item node: path item must be a string (`mpt_fail(5)`), non-empty
  (`compact_to_nibbles`, `n == 0 ⇒ mpt_fail(5)`); a leaf (`is_leaf`) needs only a string
  value. Minimal accepted node: `c2 20 01` = **3 bytes** (leaf, empty path, value `01`). Branch:
  list header + 17 items ⇒ **`≥ 18` bytes**.

**Joint constraint** `4 M + 7 N₂ + 22 N₁₇ + 32 H ≤ I`, cost `90 M + 138 N₂ + 416 N₁₇ + 16 H`
(+ Keccak blocks `19 ⌊I/136⌋`). Per byte `22.5 ≥ 19.7, 18.9, 0.5`: worst case is all empty
undecoded entries, `90 · ⌊I/4⌋`. Decode work then vanishes: the joint row equals the old
`buildNodedb` alone.
-/

namespace InitECandidate.Solver.GuestSszOffsetWitnessNodeMinBytesAndSixtyEightXMaster

open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

def inputBytes : Nat := 134217712
def keccakBlocks : Nat := 19 * (inputBytes / 136)
def jointCost (m n2 n17 h : Nat) : Nat := 90 * m + 138 * n2 + 416 * n17 + 16 * h

def jointPrev : Nat := 138 * (inputBytes / 4) + keccakBlocks
def jointSsz : Nat := 90 * (inputBytes / 4) + keccakBlocks

def main200 : Nat := 14988667700 - jointPrev + jointSsz
def main380 : Nat := 23095752530 - jointPrev + jointSsz

/-- 1. **Joint bound with SSZ offsets** (min sizes: empty entry 4, leaf 7, branch 22, ref 32). -/
theorem joint_bound (m n2 n17 h : Nat) (hb : 4 * m + 7 * n2 + 22 * n17 + 32 * h ≤ inputBytes) :
    jointCost m n2 n17 h ≤ 90 * (inputBytes / 4) := by
  unfold jointCost inputBytes at *; omega

/-- 2. Attained by `33,554,428` empty entries; a 3-byte leaf plus offset (7 bytes) is cheaper
per byte than an empty entry. -/
theorem joint_tight : 4 * 33554428 ≤ inputBytes ∧ jointCost 33554428 0 0 0 = 3019898520 ∧
    138 * 4 < 90 * 7 := by decide

/-- 3. Joint row `3,038,649,506` = old `buildNodedb`; gain `1,610,612,544`. -/
theorem joint_val : jointSsz = 3038649506 ∧ jointPrev - jointSsz = 1610612544 := by decide

/-- 4. **`main200 = 13,378,055,156`: `67×` passes, `68×` fails.** -/
theorem main200_slope : main200 = 13378055156 ∧ 67 * main200 < yukon ∧ yukon < 68 * main200 := by
  decide

/-- 5. **`main380 = 21,485,139,986`: `41×` passes, `42×` fails.** -/
theorem main380_slope : main380 = 21485139986 ∧ 41 * main380 < yukon ∧ yukon < 42 * main380 := by
  decide

/-- 6. Margins at the passing factors. -/
theorem margins : yukon - 67 * main200 = 4390230022 ∧ yukon - 41 * main380 = 19829186048 := by
  decide

/-- 7. `68×` needs `main200 ≤ 13,245,881,256`: `132,173,900` ticks short. -/
theorem sixty_eight_gap : yukon / 68 = 13245881256 ∧ main200 - yukon / 68 = 132173900 := by decide

end InitECandidate.Solver.GuestSszOffsetWitnessNodeMinBytesAndSixtyEightXMaster
