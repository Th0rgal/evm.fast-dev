import InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestExactMergeBalPrologueAndSeventyFiveXMaster`

**Code check (`Guest/guest.pp.pnk` wt-2; there is no `GuestProgram/` directory).**
* `merge_tx_into_block` (l.5911), called once per tx by `incorporate_tx_into_block`: six
  `htab_union_into` (l.5899) over the per-tx tables, plus a per-address loop on `ts+32`.
  `htab_union_into` walks `src` entries by ordinal (`htab_item`): cost per entry is one
  `htab_set` (`≤ 12 + 2L = 28` ticks salted) plus loop overhead; we charge `60` ticks/entry.
  Per tx `state_fresh_tx` (l.5419) allocates fresh tables, so entries are only those created
  in the tx. Each entry needs `≥ 1,900` gas (`minGasPerKey`) except the `≤ 4` fixed entries
  per tx (sender, target, coinbase, …): per tx `≤ 240 · 6 + 60` fixed ticks, per gas entry
  `≤ 6` tables × `(4 + 60)`. With `≤ 16,668` txs: merge `= 16,668 · 1,500 + 6 · ⌊G/1900⌋ · 64`.
* `build_block_access_list_rlp` (l.6494): keys `≤ G/2000` (cold access `≥ 2,000` gas),
  `2 · 18 · 40` ticks per key (two passes, sort, encode) as in GCM's control:
  `1,440 · ⌊G/2000⌋`.
* `op_sstore` (l.7499): `set_storage` is called on **every** `SSTORE`, even a no-op, so a
  `bs+32` entry costs only the access: `2,100` gas cold (`100` warm on an already-present key).
  Minimal gas per new key: **`21` units** (kept); the `+10,000` applies only to real changes.
* Prologue `268,435,424` (`ρ ≤ 2` ticks/input byte, `GuestSszHtrHeadersAndCompleteMainBound`) is
  already an exact linear bound in `I`; kept.
-/

namespace InitECandidate.Solver.GuestExactMergeBalPrologueAndSeventyFiveXMaster

open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

def txs : Nat := 16668
def mergeTicks (G : Nat) : Nat := txs * (240 * 6 + 60) + 6 * (G / 1900) * (4 + 60)
def balTicks (G : Nat) : Nat := 2 * 18 * 40 * (G / 2000)
def keccakBlocks : Nat := 19 * (134217712 / 136)
def lp200 : Nat := 58999236680 / 9
def lp380 : Nat := 1179391270576 / 135

def main200 : Nat := 6235124040 - 500000000 - 300000000 + mergeTicks 200000000 + balTicks 200000000
  + keccakBlocks + lp200
def main380 : Nat := 10648364040 - 500000000 - 300000000 + mergeTicks 380000000 + balTicks 380000000
  + keccakBlocks + lp380

/-- 1. Merge rows: `65,422,992` (200M), `101,802,000` (380M), vs placeholder `500,000,000`. -/
theorem merge_vals : mergeTicks 200000000 = 65422992 ∧ mergeTicks 380000000 = 101802000 ∧
    mergeTicks 380000000 < 500000000 := by decide

/-- 2. BAL rows: `144,000,000` (200M), `273,600,000` (380M), vs `300,000,000`. -/
theorem bal_vals : balTicks 200000000 = 144000000 ∧ balTicks 380000000 = 273600000 := by decide

/-- 3. Salted `htab_set` fits the per-entry merge charge. -/
theorem entry_charge : 12 + 2 * 8 ≤ 60 ∧ 2100 / 100 = 21 := by decide

/-- 4. **`main200 = 12,218,768,760`: `73×` passes, `74×` fails.** -/
theorem main200_slope : main200 = 12218768760 ∧ 73 * main200 < yukon ∧ yukon < 74 * main200 := by
  decide

/-- 5. **`main380 = 18,978,748,659`: `47×` passes, `48×` fails.** -/
theorem main380_slope : main380 = 18978748659 ∧ 47 * main380 < yukon ∧ yukon < 48 * main380 := by
  decide

/-- 6. `75×` at 200M would need `main200 ≤ 12,009,599,006`. -/
theorem no_75 : yukon / 75 = 12009599006 ∧ yukon < 75 * main200 := by decide

/-- 7. Margins. -/
theorem margins : yukon - 73 * main200 = 8749805994 ∧ yukon - 47 * main380 = 8718738501 := by
  decide

end InitECandidate.Solver.GuestExactMergeBalPrologueAndSeventyFiveXMaster
