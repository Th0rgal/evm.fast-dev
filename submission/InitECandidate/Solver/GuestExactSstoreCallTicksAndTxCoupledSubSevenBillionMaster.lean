import InitECandidate.Solver.GuestGlobalGasCoupledEvmAndSubNineBillionMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestExactSstoreCallTicksAndTxCoupledSubSevenBillionMaster`

**Static call-graph counts (`Guest/guest.pp.pnk` wt-2, 1 tick per call, `htab_*`/trie/witness/
Keccak/`jset` charged 1 here since counted in their own rows, `memcpy`/`memzero ≤ 32` B = 5).**
* `op_sstore` (l.7499): **110**. `op_sload`: 82. `op_balance`: 43. `op_extcodesize`: 66.
* `op_call`: **349**, `op_callcode` 329, `op_staticcall`/`op_delegatecall` 294
  (`generic_call` 115, `start_child` 82, `frame_new` 28), **excluding** `compute_jumpdests`,
  `run_precompile`, `destroy_storage` and the child's `frame_prologue`.
So the previous hand charges (`2,000`/key, `10,000`/account) cover the straight-line work.

**New issue: jumpdest re-scan per call.** `frame_new` (l.6884, every `CALL`-family frame) and
`prepare_dispatch` (l.8144) call `compute_jumpdests(code, n)` (l.6826): one `while` tick per
code byte (`adv ≥ 1`), **not cached**. Code is `≤ 65,536` bytes (`decode_bytes_list` limit,
`create_finish` l.8575). A warm `STATICCALL` to a `65,536`-byte contract costs `100` gas +
`≤ 26` gas of argument setup, and the callee may `STOP` at once: `≥ 65,536` ticks per
`≤ 126` gas, i.e. `> 520` ticks/gas `≫ 18`. The bound `18 · G` used since
`GuestEvmStepDispatchAndNinetyXMaster` does not hold for the current Guest.

**Tx coupling.** Guest intrinsic gas is **12,000** (`calculate_intrinsic_cost` l.5298,
`base_regular_gas = 12000 + …`), not 21,000: `T ≤ 16,666` at 200M, as already used. No gain.
-/

namespace InitECandidate.Solver.GuestExactSstoreCallTicksAndTxCoupledSubSevenBillionMaster

open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

def sstoreBaseTicks : Nat := 110
def sloadBaseTicks : Nat := 82
def accountAccessBaseTicks : Nat := 349
def maxCode : Nat := 65536
def callGas : Nat := 126

/-- Calls of `≤ 126` gas each that fit in `G`. -/
def calls (G : Nat) : Nat := G / callGas
def jumpdestTicks (G : Nat) : Nat := calls G * maxCode

/-- 1. Exact straight-line counts fit the previous charges. -/
theorem charges_ok : sstoreBaseTicks ≤ 2000 ∧ accountAccessBaseTicks ≤ 10000 ∧
    sloadBaseTicks + 7 * 28 ≤ 18 * 100 := by decide

/-- 2. Per call, the jumpdest scan exceeds `18` ticks/gas by `> 28×`. -/
theorem scan_ratio : 18 * callGas < maxCode ∧ 28 * (18 * callGas) < maxCode := by decide

/-- 3. **Lower bound at 200M**: `104,025,358,336` jumpdest ticks alone; Yukon admits only
`8×`. -/
theorem attack200 : jumpdestTicks 200000000 = 104025358336 ∧ 8 * jumpdestTicks 200000000 < yukon ∧
    yukon < 9 * jumpdestTicks 200000000 := by decide

/-- 4. **Lower bound at 380M**: `197,648,252,928` ticks; only `4×`. -/
theorem attack380 : jumpdestTicks 380000000 = 197648252928 ∧ 4 * jumpdestTicks 380000000 < yukon ∧
    yukon < 5 * jumpdestTicks 380000000 := by decide

/-- 5. The previous `108×` bound is broken by `> 12×`. -/
theorem previous_broken : 12 * 8298113205 < jumpdestTicks 200000000 := by decide

/-- 6. **With a jumpdest cache per code** (scan each distinct code once, codes `≤ I` bytes):
extra `≤ I` ticks; `main200 ≤ 8,432,330,917` (`106×`), `main380 ≤ 11,992,988,211` (`75×`). -/
theorem cached : 8298113205 + 134217712 = 8432330917 ∧ 106 * 8432330917 < yukon ∧
    yukon < 107 * 8432330917 ∧ 11858770499 + 134217712 = 11992988211 ∧
    75 * 11992988211 < yukon ∧ yukon < 76 * 11992988211 := by decide

/-- 7. Intrinsic gas `12,000` ⇒ `T ≤ 16,666` user txs at 200M (no `9,523`). -/
theorem tx_count : 200000000 / 12000 = 16666 ∧ 200000000 / 21000 = 9523 := by decide

end InitECandidate.Solver.GuestExactSstoreCallTicksAndTxCoupledSubSevenBillionMaster
