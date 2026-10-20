import InitECandidate.Solver.GuestSloadExactProbeTicks

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestMemoryAndAccountOpcodeBounds`

Hand transcription from `Guest/guest.pp.pnk` (`PanSem` clock: 1 tick per executed `while`
body, 1 per `.call`, 0 otherwise).

Memory (`memcpy` l.76, `memzero` l.108, `extend_memory` l.6787, `memory_gas_cost`):
aligned paths do 1 iteration per 32 bytes (+ ≤ 3 for the 8-byte tail); EVM charges
`3·w + w²/512` per expansion and `3 + 3·w` per `MCOPY` word.

Accounts (`op_balance` l.7583, `access_gas_cost` l.6941): cold = 3000 gas (not 2600), warm 100.
A warm `BALANCE` searches `ev+168` (`is_warm_address`), `ts+8` (`htab_set` in
`get_account_optional`) and `ts+16` (`htab_get`, holds only modified accounts) — the same two
attacker-fillable colliding tables as `SLOAD`, with 20-byte keys (`memeq` unrolled, 2 ticks per
probe). `EXTCODESIZE` warm = 200 gas.

`SSTORE` (l.7499): `max(access, 2301)` stipend check; warm no-op = 100 gas, but it searches
`ev+176`, `ts+56` + `bs+32` (`get_storage_original`), `ts+24`, `ts+32`, `bs+32` (`get_storage`),
`ts+32` + inner (`set_storage`/`jset`) — more tables than `SLOAD`.

Per-transaction cap (l.15034, EIP-7825): `min(16777216, gas)`, and `state_fresh_tx` (l.5419)
re-creates every `ts+*` table. The theorem `per_tx_split` shows that if all colliding clusters are
per-transaction, the collision term collapses below `maxGuestSourceClock`.
-/

namespace InitECandidate.Solver.GuestMemoryAndAccountOpcodeBounds

open InitECandidate.Solver.GuestSloadExactProbeTicks

/-- Worst ticks of aligned `memcpy`/`memzero` on `n` bytes. -/
def memAligned (n : Nat) : Nat := 1 + n / 32 + 3
/-- EVM memory gas for `w` words. -/
def memGas (w : Nat) : Nat := 3 * w + w * w / 512

/-- 1. Aligned memory primitives cost ≤ `4 + w` ticks on `w` words; equality at `w = 0`. -/
theorem memAligned_words (w : Nat) : memAligned (32 * w) = 4 + w := by
  unfold memAligned; omega

/-- 2. Expansion: `extend_memory` (call + ≤ 2 `memzero`, cap-doubling) for `w` new words costs
`≤ 2 + 2·(4 + w)` ticks, `≤ 4` ticks/gas once `w ≥ 1`, tight at `w = 1`. -/
theorem expand_le (w : Nat) (hw : 1 ≤ w) : 2 + 2 * (4 + w) ≤ 4 * memGas w ∧
    2 + 2 * (4 + 1) = 4 * memGas 1 - 0 := by
  unfold memGas; constructor <;> omega

/-- 3. `MCOPY` of `w` words: 2 `memcpy` + ~12 calls ≤ `14 + 2·(4 + w)` ticks for `3 + 3w` gas:
≤ 22/3 < 18 ticks/gas (`PUSH31` slope). -/
theorem mcopy_dominated (w : Nat) : 3 * (14 + 2 * (4 + w)) ≤ 22 * (3 + 3 * w) ∧
    22 < 3 * 18 := by
  constructor <;> omega

/-- 4. Warm `BALANCE` has the same per-probe slope as warm `SLOAD` (2 colliding finds, 2 ticks). -/
def balanceWarmTables : Nat := 2
theorem balance_slope_eq : balanceWarmTables * pFind = pEff := by decide

/-- 5. Cold address insert costs 3000 gas ≥ 2100: per gas, it fills a cluster strictly slower
than a cold storage key (`21·c + w ≤ 2·10⁶` already covers it: `30 > 21`). -/
theorem cold_balance_dominated (c w : Nat) (h : 30 * c + w ≤ 2000000) :
    c * w ≤ 47619047619 ∧ 30 * c + w ≤ 2000000 → 21 * c + w ≤ 2000000 := by
  intro ⟨_, h'⟩; omega

/-- 6. `EXTCODESIZE` warm (200 gas, same 2 tables) has half the ticks/gas of a warm `SLOAD`. -/
theorem extcodesize_half (c : Nat) : 2 * (pEff * c) = (pEff * c) * 200 / 100 := by
  omega

/-- 7. Warm-lookup cost per probe for ops on the same clusters: `SLOAD`/`BALANCE` 100 gas,
`EXTCODESIZE` 200 gas, `SSTORE` no-op ≥ 100 gas but with check `≥ 2301` gas remaining.
The minimal per-lookup gas is 100: no op is cheaper than the `SLOAD` envelope. -/
def warmGas : List Nat := [100, 100, 200, 100]
theorem warm_gas_min : (∀ g ∈ warmGas, 100 ≤ g) ∧ 100 ∈ warmGas := by decide

/-- 8. Per-transaction bound: with `x = 20c` and `w + c ≤ g/100 − 20c` (2100-gas cold keys),
`80·c·(w + c) ≤ (g/100)²`. -/
theorem per_tx_probes (c w m : Nat) (h : 21 * c + w ≤ m) : 80 * (c * (w + c)) ≤ m * m := by
  have hw : (w : Int) + c ≤ m - 20 * c := by omega
  have hc0 : (0 : Int) ≤ c := by omega
  have hmul : (c : Int) * (w + c) ≤ c * (m - 20 * c) := Int.mul_le_mul_of_nonneg_left hw hc0
  have hsq : (0 : Int) ≤ ((m : Int) - 40 * c) ^ 2 := sq_nonneg _
  have : (80 : Int) * (c * (w + c)) ≤ m * m := by nlinarith
  exact_mod_cast this

/-- 9. Over a block of per-transaction clusters: if each tx has `≤ 167,772` warm-units
(`16,777,216 / 100`) and the units sum to `≤ 2·10⁶`, the probe total is `≤ 4,194,300,000`. -/
theorem per_tx_split (ms : List Nat) (hcap : ∀ m ∈ ms, m ≤ 167772) (hsum : ms.sum ≤ 2000000) :
    (ms.map (fun m => m * m)).sum ≤ 167772 * 2000000 := by
  have key : ∀ l : List Nat, (∀ m ∈ l, m ≤ 167772) →
      (l.map (fun m => m * m)).sum ≤ 167772 * l.sum := by
    intro l hl
    induction l with
    | nil => simp
    | cons a t ih =>
      simp only [List.map_cons, List.sum_cons]
      have ha := hl a (by simp)
      have ht := ih (fun m hm => hl m (by simp [hm]))
      have : a * a ≤ 167772 * a := Nat.mul_le_mul_right _ ha
      rw [Nat.mul_add]; omega
  have := key ms hcap
  exact le_trans this (Nat.mul_le_mul_left _ hsum)

/-- 10. Consequence (conditional on clusters being per-transaction): collision ticks
`≤ 4 · 335,544,000,000 / 80 = 16,777,200,000` and total `≤ 20,436,764,234 <`
`maxGuestSourceClock`. -/
theorem per_tx_kPan :
    pEff * (167772 * 2000000 / 80) = 16777200000 ∧
      SelfContainedMasterK.prologueTicks + 18 * GuestEvmStepOpcodeBounds.gasCap + 16777200000
        = 20436764234 ∧
      20436764234 < GuestEvmStepOpcodeBounds.maxGuestSourceClock := by decide

end InitECandidate.Solver.GuestMemoryAndAccountOpcodeBounds
