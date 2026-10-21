import InitECandidate.Solver.GuestJointRlpArityByteConservationAndFiftyXMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster`

**Code check (`guest.pp.pnk` wt-2).**
* `_decode_step` (l.3778): `rlp_decode_fully` (else `mpt_fail(3)`), must be a list (else
  `mpt_fail(4)`), `rlp_list_to_slices`; `sl.1 == 2` ⇒ leaf/extension; `sl.1 != 17` ⇒
  `mpt_fail(4)`; else branch. So accepted arity is exactly `2` or `17`.
* A rejected node (`k ∉ {2,17}`) calls `mpt_fail`, which aborts the block: it happens at most
  once per run, after one RLP pass over that node's bytes (`≤ I`), so it adds no per-node term.
* `nodedb_build` (l.3691): one `keccak256` + one `htab_set` per witness entry (nodes and codes),
  before any arity check: `16` probe + `74` Keccak ticks per entry, `19` per 136-byte block.

**Shared nodes.** Let `M` count entries never decoded (codes, unreferenced nodes, `≥ 4` bytes as
in the original `I/4` count). Each decoded node is also a build entry, so with disjoint slices
`4 M + 4 N₂ + 18 N₁₇ + 32 H ≤ I` and the per-entry cost is
`90 M + 138 N₂ + 416 N₁₇ + 16 H` (+ Keccak blocks `19 ⌊I/136⌋`). Per byte:
`22.5`, `34.5`, `23.1`, `0.5`; the max is all 2-item nodes: `138 · I/4`.
-/

namespace InitECandidate.Solver.GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster

open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

def inputBytes : Nat := 134217712
def keccakBlocks : Nat := 19 * (inputBytes / 136)
def jointCost (m n2 n17 h : Nat) : Nat := 90 * m + 138 * n2 + 416 * n17 + 16 * h

def separateOld : Nat := 3038649506 + 2430831895
def jointNew : Nat := 138 * (inputBytes / 4) + keccakBlocks

def main200 : Nat := 15808887051 - separateOld + jointNew
def main380 : Nat := 23915971881 - separateOld + jointNew

/-- 1. **Joint bound** over shared build/decode entries, including undecoded entries. -/
theorem joint_bound (m n2 n17 h : Nat) (hb : 4 * m + 4 * n2 + 18 * n17 + 32 * h ≤ inputBytes) :
    jointCost m n2 n17 h ≤ 138 * (inputBytes / 4) := by
  unfold jointCost inputBytes at *; omega

/-- 2. Attained by `33,554,428` two-item nodes. -/
theorem joint_tight : 4 * 33554428 ≤ inputBytes ∧ jointCost 0 33554428 0 0 = 4630511064 ∧
    inputBytes / 4 = 33554428 := by decide

/-- 3. The all-branch witness of the previous module is not the joint worst case. -/
theorem branch_not_worst : jointCost 0 7456539 0 0 < jointCost 0 33554428 0 0 := by decide

/-- 4. Joint row `4,649,262,050` vs separate `5,469,481,401`: gain `820,219,351`. -/
theorem joint_val : keccakBlocks = 18750986 ∧ jointNew = 4649262050 ∧
    separateOld - jointNew = 820219351 := by decide

/-- 5. **`main200 = 14,988,667,700`: `60×` passes, `61×` fails.** -/
theorem main200_slope : main200 = 14988667700 ∧ 60 * main200 < yukon ∧ yukon < 61 * main200 := by
  decide

/-- 6. **`main380 = 23,095,752,530`: `38×` passes, `39×` fails.** -/
theorem main380_slope : main380 = 23095752530 ∧ 38 * main380 < yukon ∧ yukon < 39 * main380 := by
  decide

/-- 7. Margins at the passing factors. -/
theorem margins : yukon - 60 * main200 = 1399863474 ∧ yukon - 38 * main380 = 23081329334 := by
  decide

end InitECandidate.Solver.GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster
