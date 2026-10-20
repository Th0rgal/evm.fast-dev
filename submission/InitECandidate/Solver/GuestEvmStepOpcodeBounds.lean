import InitECandidate.Solver.SelfContainedMasterK

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-!
# `InitECandidate.Solver.GuestEvmStepOpcodeBounds`

Hand-transcribed `PanSem` tick counts for the EVM step of `Guest/guest.pp.pnk`
(`run_frames` l.~8437, `op_dispatch` l.8190, `op_*` l.6954–7600). Clock rules
(`Flapjack/.../PanSem/StateExactFiniteMap.lean`): 1 tick per executed `while` body,
1 tick per function `.call`, 0 for FFI / builtins (`__add_with_carry__`) and plain statements.
Worst alignment is taken for `memcpy`/`memzero`. Counts are upper bounds read off the source,
not derived from `PanSem` on the AST. Imports only `SelfContainedMasterK` (no `Proofs/Bounded*`).

Findings:
* Per opcode: `run_frames` loop iteration + `op_dispatch` call = 2 ticks.
* Stack/arith (`ADD`): 9 ticks / 3 gas. `JUMPDEST`: 5 ticks / 1 gas. `PUSH31`: 54 ticks / 3 gas
  (18 ticks/gas) — the max over all non-table families examined. `SelfContainedMasterK`'s
  arithmetic family (3 gas, 2 ticks) under-counts by 4.5×.
* Hash-table opcodes are NOT linearly bounded: `htab_hash` is an XOR fold of attacker-chosen
  words, so storage keys can be made to collide; a warm `SLOAD` (100 gas) then probes a whole
  cluster (≥ 2 ticks per probe). A cluster of 47,619 keys plus 1,000,001 warm lookups fits in
  200M gas and costs ≥ 95,238,095,238 ticks > `maxGuestSourceClock` (43,934,217,712).
-/

namespace InitECandidate.Solver.GuestEvmStepOpcodeBounds

/-- Amortised slope of `guestSourceClockBudget _ 18 200 _`. -/
def slope : Nat := 219
/-- Block gas limit. -/
def gasCap : Nat := 200000000
/-- `maxGuestSourceClock` (restated, to avoid the `Proofs/Bounded*` closure). -/
def maxGuestSourceClock : Nat := 43934217712

/-- `memcpy`/`memzero` worst (unaligned) path on `n` bytes. -/
def memTicks (n : Nat) : Nat := 1 + n / 8 + n % 8

/-- `run_frames` iteration + `op_dispatch` call. -/
def stepOverhead : Nat := 2

/-- `op_add`: call, 2 `stack_pop`, `charge_gas`, `u256_add`, `stack_push`, `pc_add`. -/
def addTicks : Nat := stepOverhead + 1 + 2 + 1 + 1 + 1 + 1
/-- `op_jumpdest`: call, `charge_gas`, `pc_add`. -/
def jumpdestTicks : Nat := stepOverhead + 1 + 1 + 1
/-- `op_pop`: call, `stack_pop`, `charge_gas`, `pc_add`. -/
def popTicks : Nat := stepOverhead + 1 + 1 + 1 + 1

/-- `u256_from_be(tmp, n)`: aligned fast path (`n = 32`, 4 `bswap64`) or byte loop. -/
def fromBeTicks (n : Nat) : Nat := if n = 32 then 1 + 4 else 1 + n
/-- `op_push(n)`: call, `charge_gas`, `heap_mark`, `alloc`, `buffer_read` (+`memcpy`+`memzero 0`),
`u256_from_be`, `heap_release`, `stack_push`, `pc_add`. -/
def pushTicks (n : Nat) : Nat :=
  stepOverhead + 1 + 1 + 1 + 1 + (1 + memTicks n + 1) + fromBeTicks n + 1 + 1 + 1

/-- 1. `ADD` costs 9 ticks for 3 gas (3 ticks/gas). -/
theorem add_ticks : addTicks = 9 ∧ addTicks = 3 * 3 := by decide

/-- 2. `JUMPDEST` costs 5 ticks for 1 gas; `POP` 6 ticks for 2 gas. -/
theorem jumpdest_pop_ticks : jumpdestTicks = 5 ∧ popTicks = 6 := by decide

/-- 3. `PUSHn` is maximal at `n = 31` with 54 ticks; `PUSH0` 13, `PUSH32` 21. -/
theorem push_ticks_max : (∀ n : Fin 33, pushTicks n.val ≤ 54) ∧ pushTicks 31 = 54 ∧
    pushTicks 0 = 13 ∧ pushTicks 32 = 21 := by decide

/-- 4. Exact maximum ratio over these families: 18 ticks/gas (`PUSH31`), attained. -/
theorem max_ratio_simple :
    addTicks ≤ 18 * 3 ∧ jumpdestTicks ≤ 18 * 1 ∧ popTicks ≤ 18 * 2 ∧
      (∀ n : Fin 33, pushTicks n.val ≤ 18 * 3) ∧ pushTicks 31 = 18 * 3 := by decide

/-- 5. Hence these families respect the 219 ticks/gas slope with factor > 12 of margin. -/
theorem simple_families_within_slope :
    18 ≤ slope ∧ 18 * 12 < slope ∧ ∀ n : Fin 33, pushTicks n.val ≤ slope * 3 := by decide

/-- 6. `SelfContainedMasterK`'s arithmetic family (2 ticks / 3 gas) under-counts `ADD`. -/
theorem masterK_arith_undercounts :
    SelfContainedMasterK.arithTicks < addTicks ∧ SelfContainedMasterK.arithMinGas = 3 := by decide

/-- 7. Tightened linear source clock if every opcode were ≤ 18 ticks/gas (no collisions):
`prologue + 18 · 200M`, versus the `keccak` family (60 ticks / 30 gas = 2 ticks/gas). -/
def tightLinearClock : Nat := SelfContainedMasterK.prologueTicks + 18 * gasCap
theorem tightLinearClock_val : tightLinearClock = 3659564234 ∧
    SelfContainedMasterK.refinedSourceClock < tightLinearClock ∧
    tightLinearClock ≤ maxGuestSourceClock := by
  refine ⟨by decide, ?_, by decide⟩
  rw [(SelfContainedMasterK.refinedSourceClock_eq).1]; decide

/-! ## Hash-collision schedule -/

/-- Lower bound on ticks of a warm `SLOAD` probing `p` occupied slots in `is_warm_storage_key`
(one loop iteration + one `memeq` call per probe). -/
def sloadProbeTicks (p : Nat) : Nat := 2 * p

/-- Attack: `c` colliding cold `SLOAD`s (2100 gas each), then `L` warm `SLOAD`s (100 gas each),
each probing the full cluster. -/
def attackGas (c L : Nat) : Nat := 2100 * c + 100 * L
def attackTicks (c L : Nat) : Nat := L * sloadProbeTicks c

/-- 8. The schedule `c = 47,619`, `L = 1,000,001` fits exactly in the 200M block budget. -/
theorem attack_fits : attackGas 47619 1000001 ≤ gasCap ∧ gasCap - attackGas 47619 1000001 = 0 := by
  decide

/-- 9. Its source ticks exceed `maxGuestSourceClock`: no linear `≤ 219 · gas` bound holds. -/
theorem attack_exceeds_max :
    attackTicks 47619 1000001 = 95238095238 ∧
      maxGuestSourceClock < attackTicks 47619 1000001 ∧
      slope * gasCap < attackTicks 47619 1000001 := by decide

/-- 10. A single warm `SLOAD` on a 47,619-key cluster violates the per-iteration
`AmortizedOk` inequality `ticks ≤ 219 · gas` (95,238 > 21,900); the break-even cluster is 10,950. -/
theorem warm_sload_breaks_slope :
    slope * 100 < sloadProbeTicks 47619 ∧
      (∀ p, sloadProbeTicks p ≤ slope * 100 ↔ p ≤ 10950) := by
  refine ⟨by decide, fun p => ?_⟩
  unfold sloadProbeTicks slope; omega

/-- 11. Gas-feasible clusters can exceed the break-even size: 10,951 colliding cold keys
cost 22,997,100 gas ≤ 200M. -/
theorem breakeven_cluster_affordable : 2100 * 10951 ≤ gasCap ∧ 10950 < 10951 := by decide

end InitECandidate.Solver.GuestEvmStepOpcodeBounds
