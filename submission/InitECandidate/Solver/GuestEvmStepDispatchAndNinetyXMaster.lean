import InitECandidate.Solver.GuestExactMergeBalPrologueAndSeventyFiveXMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestEvmStepDispatchAndNinetyXMaster`

**Dispatch ticks (`Guest/guest.pp.pnk` wt-2; 1 tick per `while` body and per `.call`, 0 for
FFI/builtins).** Loop `run_frames` (l.8437): 1 `while` + 1 `op_dispatch` call (l.8190; the
`if op == …` chain is free).
* `JUMPDEST` (l.7251): `op_jumpdest` + `charge_gas` + `pc_add` ⇒ `5` ticks / 1 gas.
* `POP` (l.7311): + `stack_pop` ⇒ `6` / 2 gas. `ADD` (l.6954): 2 `stack_pop`, `charge_gas`,
  `u256_add` (carry builtins 0), `stack_push`, `pc_add` ⇒ `9` / 3 gas.
* `PUSHn` (l.7317): `charge_gas`, `heap_mark`, `alloc`, `buffer_read` (+ `memcpy`/`memzero`),
  `u256_from_be` (byte loop `≤ 31` when not aligned 32), `heap_release`, `stack_push`,
  `pc_add`: worst `PUSH31` = **`54` ticks / 3 gas = 18 ticks/gas** — the `18 · G` term is this
  exact maximum, not a placeholder.

**Joint dispatch + tables.** `18 · G` bounds every opcode's own ticks by its gas. The salted
table row `336 · units` was **added** on top; it should be **inside** the per-opcode ratio:
warm `SLOAD` (100 gas) = dispatch `≤ 30` calls + `7` salted finds × `28` = `≤ 226 < 1,800`
ticks. Same for `TLOAD`/`TSTORE`/`BALANCE`. So the joint per-gas max stays `18`, and the
`336 · units` row is removed.

**`merge` at 380M.** `env380` held `950,000,000` (= `500M · 380/200`); the previous module
removed only `500,000,000`: `450,000,000` phantom ticks removed here.

**secp256k1.** `30,000` ticks per `recover_sender`, one per user tx (`≤ 16,666`) plus the
two system rows: `500,040,000`. The `ecrecover` precompile (3,000 gas) runs `≤ 10` ticks/gas,
inside `18 · G`. Kept.
-/

namespace InitECandidate.Solver.GuestEvmStepDispatchAndNinetyXMaster

open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

def jumpdestTicks : Nat := 1 + 1 + 1 + 1 + 1
def addTicks : Nat := 1 + 1 + 1 + 2 + 1 + 1 + 1 + 1
def push31Ticks : Nat := 54
def sloadWarmTicks : Nat := 30 + 7 * (12 + 2 * 8)

def main200 : Nat := 12218768760 - 336 * 2000000
def main380 : Nat := 18978748659 - 450000000 - 336 * 3800000

/-- 1. Per-gas dispatch ratios: `JUMPDEST 5`, `ADD 3`, `PUSH31 18`; max `18`. -/
theorem ratios : jumpdestTicks = 5 ∧ addTicks = 9 ∧ addTicks ≤ 18 * 3 ∧ jumpdestTicks ≤ 18 * 1 ∧
    push31Ticks = 18 * 3 := by decide

/-- 2. A warm `SLOAD` with all salted table work stays under `18` ticks/gas. -/
theorem sload_inside : sloadWarmTicks = 226 ∧ sloadWarmTicks ≤ 18 * 100 := by decide

/-- 3. Joint bound: for any mix of `a` table opcodes (100 gas) and `b` cheap gas, ticks
`≤ 18 · gas`; no extra `336` per unit. -/
theorem joint (a b : Nat) : sloadWarmTicks * a + 18 * b ≤ 18 * (100 * a + b) := by
  unfold sloadWarmTicks; omega

/-- 4. Removed rows: `672,000,000` (200M), `450,000,000 + 1,276,800,000` (380M). -/
theorem removed : 336 * 2000000 = 672000000 ∧ 450000000 + 336 * 3800000 = 1726800000 := by decide

/-- 5. **`main200 = 11,546,768,760`: `78×` passes, `79×` fails.** -/
theorem main200_slope : main200 = 11546768760 ∧ 78 * main200 < yukon ∧ yukon < 79 * main200 := by
  decide

/-- 6. **`main380 = 17,251,948,659`: `52×` passes, `53×` fails.** -/
theorem main380_slope : main380 = 17251948659 ∧ 52 * main380 < yukon ∧ yukon < 53 * main380 := by
  decide

/-- 7. `90×` would need `main200 ≤ 10,007,999,171`. -/
theorem no_90 : yukon / 90 = 10007999171 ∧ yukon < 90 * main200 := by decide

/-- 8. Margins. -/
theorem margins : yukon - 78 * main200 = 71962194 ∧ yukon - 52 * main380 = 3618595206 := by decide

end InitECandidate.Solver.GuestEvmStepDispatchAndNinetyXMaster
