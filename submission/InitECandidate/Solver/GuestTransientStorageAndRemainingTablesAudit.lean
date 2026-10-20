import InitECandidate.Solver.GuestExhaustiveHtabInventoryAndSlopeAbsorption

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestTransientStorageAndRemainingTablesAudit`

Hand transcription of `guest.pp.pnk` (wt-2).

## `ts+64` (EIP-1153)
* `op_tstore` / `op_tload`: `charge_gas(100)`, no cold surcharge.
* `set_transient_storage` (l.5832): `jdel(ts+64, k)` if value = 0, else `jset(ts+64, k, v)`.
  `jset` (l.5441) = `htab_get` (one `htab_find_slot`) + journal + `htab_set` (second find, then
  `htab_insert_raw` probing the same run). No `ts+72`.
* `get_transient_storage` (l.5686): one `htab_get`.
* No `htab_clear` / `clear_transient_storage` exists: `state_fresh_tx` (l.5419) allocates a fresh
  `htab_new(52, 16)` for `ts+64` per tx.
* `state_restore` (l.5481) undoes each journaled insert by `htab_del` (find + backward shift).
* Keys `addr‖key` are attacker-chosen, `htab_hash` is unsalted: one collision run.

Tick model (same as upstream modules, hand-counted): inserting the `i`-th colliding key costs
`≤ 5i` ticks (2 + 2 + 1 per entry); undoing it on revert `≤ 5i`. A new key costs `≥ 106` gas
(`PUSH` ×2 + `TSTORE`). Intrinsic gas in this Guest is `12,000` (not 21,000; `21,000` only lowers
the counts below). EIP-7825: `16,777,216` gas per tx; block `200,000,000`.

## Remaining tables
* `bal_accounts` / per-account `bal` tables: filled only by `update_builder_from_tx` and
  `build_block_access_list_rlp`, once per tx entry already in `ts+8..ts+48` / `bs+72`: each entry
  pays a cold access (≥ 2,000 gas). Absorbed.
* `ev+136` (selfdestruct set, `op_selfdestruct` l.7985, ≥ 5,000 gas). Absorbed.
* `nodedb` (l.3696): built once from the witness, size bounded by `input.bytes.size`, not gas.
* `new_roots` (`compute_state_root` l.14662): one entry per changed account (≥ cold access). Absorbed.
* `written` / `set_for` (EIP-7702, l.8074): one entry per authorization (≥ 12,500 gas). Absorbed.
-/

namespace InitECandidate.Solver.GuestTransientStorageAndRemainingTablesAudit

open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

def txCap : Nat := 16777216
def blockGas : Nat := 200000000
def intrinsic : Nat := 12000
def keyGas : Nat := 106

/-- Ticks to insert `k` colliding keys: `Σ_{i<k} 5i`. -/
def buildTicks (k : Nat) : Nat := 5 * (k * (k - 1)) / 2

/-- 1. Per-tx key cap: `158,162` new transient keys, tight. -/
theorem keys_per_tx : intrinsic + keyGas * 158162 ≤ txCap ∧ txCap < intrinsic + keyGas * 158163 := by
  decide

/-- 2. Any per-tx key count is ≤ `158,162`. -/
theorem keys_le (k : Nat) (h : intrinsic + keyGas * k ≤ txCap) : k ≤ 158162 := by
  unfold intrinsic keyGas txCap at h; omega

/-- 3. Block packing: 11 full txs and one partial tx of `145,647` keys fit in 200M gas. -/
theorem block_packing :
    11 * txCap + intrinsic + keyGas * 145647 ≤ blockGas ∧
      blockGas < 11 * txCap + intrinsic + keyGas * 145648 := by decide

/-- 4. `buildTicks` is monotone (larger runs cost more). -/
theorem build_mono (a b : Nat) (h : a ≤ b) : buildTicks a ≤ buildTicks b := by
  unfold buildTicks
  have h1 : a - 1 ≤ b - 1 := by omega
  have : a * (a - 1) ≤ b * (b - 1) := Nat.mul_le_mul h h1
  omega

/-- 5. Per-tx `ts+64` build cost at the cap. -/
theorem tx_build : buildTicks 158162 = 62537650205 := by decide

/-- 6. Block `ts+64` cost without revert (lower witness and model upper bound coincide). -/
theorem block_build : 11 * buildTicks 158162 + buildTicks 145647 = 740946409660 := by decide

/-- 7. With revert (`state_restore` undoes every insert at ≤ the same cost): doubles. -/
theorem block_with_revert : 2 * (11 * buildTicks 158162 + buildTicks 145647) = 1481892819320 := by
  decide

/-- 8. Slope `1×`: `ts+64` without revert is under Yukon alone, and together with the storage
envelope `156,088,992,805` still under (margin `3,684,523,009`). -/
theorem one_slope_no_revert :
    740946409660 < yukon ∧ 156088992805 + 740946409660 < yukon ∧
      yukon - (156088992805 + 740946409660) = 3684523009 := by decide

/-- 9. With revert even `1×` fails; `2×` fails without revert. -/
theorem slopes_fail :
    yukon < 1481892819320 ∧ yukon < 2 * 740946409660 := by decide

/-- 10. Slope per unit (100 gas) of `ts+64` at the cap exceeds `50,000`: not absorbable by
`general_side_regime_absorption`. -/
theorem tstore_not_absorbable : 50000 * (txCap / 100) < buildTicks 158162 := by decide

/-- 11. Remaining tables: gas floors per entry are ≥ 20 units (`2,000` gas), so their slope with
cluster ≤ `95,238` stays below `50,000 · 20` per entry ⇒ absorbed. -/
theorem remaining_absorbed :
    5 * 95238 ≤ 50000 * 20 ∧ 2000 ≤ 2100 ∧ 2000 ≤ 5000 ∧ 2000 ≤ 12500 := by decide

end InitECandidate.Solver.GuestTransientStorageAndRemainingTablesAudit
