import InitECandidate.Solver.GuestMemoryAndAccountOpcodeBounds

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestBlockVsTxHtabBounds`

Separation of per-transaction vs block-level hash tables in `Guest/guest.pp.pnk`, and the
combined worst-case `k_pan` for an `SLOAD`/`SSTORE`/`BALANCE`/`PUSH31` adversary over 200M gas.

## Per-transaction tables (reset by `state_fresh_tx` l.5419, EIP-7825 cap `16,777,216` gas/tx)
`ts+8` accounts, `ts+16` account values, `ts+24` warm-created, `ts+32` storage (outer→inner),
`ts+40..64`, and the warm sets `ev+168` (addresses) / `ev+176` (storage keys) which are
rebuilt per EVM frame (`make_child_frame` copies `ev+168/176`). Any collision cluster in these
lives inside one transaction, so its quadratic cost is governed by `m = gas_tx / 100 ≤ 167,772`.

## Block-level tables (persist across txs)
`bs+8/16/24/40/48` (account/code caches), `bs+32` (storage outer→inner), `bs+72` (pre-state
read set). Two accumulation paths only:
* `record_pre_state_read` (l.5517) = `htab_set(bs+72, addr, 1)` — fires on every *cold* account
  read (`get_pre_state_account_optional`, l.5599) and cold storage read; 20-byte attacker key.
* `merge_tx_into_block` (l.5911) unions each committed `ts+*` into `bs+*` at tx commit.

So the only *unbounded-across-block* attacker-driven insert is `bs+72`: one `htab_set` per cold
access (`≥ 2100` gas ⇒ `c ≤ 95,238` inserts/block). Each insert does one failing `htab_find_slot`
(scans the whole `j`-sized cluster, `pFind = 2`) + one `htab_insert_raw` scan (`pIns = 1`):
`3·j` ticks on the `j`-th insert, total `blkRead c = Σ_{j<c} 3j = 3·c·(c−1)/2`.

## `op_sstore` probe cost (l.7499)
A warm no-op `SSTORE` (≥ 100 gas, stipend check `≥ 2301` gas available) still calls, in order:
`is_warm_storage_key`(ev+176), `get_storage_original`(ts+56 + bs+32), `get_storage`(ts+24 +
ts+32 + bs+32), `set_storage`→`get_account_optional`(ts+8) + `htab_get`(ts+32) + `jset`(inner).
That is `sstoreFinds = 7` colliding `htab_find_slot` calls, `pSstore = 14` ticks per probed slot —
all on **per-transaction** tables except the two `bs+32` `stor_lookup`s, whose cluster is itself
only grown by committed writes (also per-tx capped before merge).
-/

namespace InitECandidate.Solver.GuestBlockVsTxHtabBounds

open InitECandidate.Solver.GuestSloadExactProbeTicks
open InitECandidate.Solver.GuestEvmStepOpcodeBounds (gasCap maxGuestSourceClock)

/-! ## Constants -/

/-- EIP-7825 per-transaction execution gas cap (`min(16777216, gas)`, l.15034). -/
def txGasCap : Nat := 16777216
/-- Warm-lookup units available per transaction (`txGasCap / 100`). -/
def txUnits : Nat := 167772
/-- `op_sstore` colliding `htab_find_slot` calls. -/
def sstoreFinds : Nat := 7
/-- Ticks per probed slot in one `SSTORE`. -/
def pSstore : Nat := sstoreFinds * pFind
/-- Cold accesses per block at `≥ 2100` gas. -/
def maxColdPerBlock : Nat := 95238

/-- 1. Extracted constants. -/
theorem constants : txGasCap = 16777216 ∧ txUnits = 167772 ∧ pSstore = 14 ∧
    maxColdPerBlock = 95238 ∧ 2100 * maxColdPerBlock ≤ gasCap := by decide

/-! ## Block-level `bs+72` insert cost -/

/-- `Σ_{j<c} 3j`, the quadratic probe cost of filling a colliding `bs+72` cluster of `c` keys. -/
def blkRead : Nat → Nat
  | 0 => 0
  | c + 1 => blkRead c + 3 * c

/-- 2. Closed form without division: `2 · blkRead c = 3 · c · (c − 1)`. -/
theorem blkRead_closed (c : Nat) : 2 * blkRead c = 3 * (c * (c - 1)) := by
  induction c with
  | zero => rfl
  | succ n ih =>
    rw [blkRead]
    cases n with
    | zero => rfl
    | succ m =>
      rw [Nat.mul_add, ih]
      simp only [Nat.add_sub_cancel]
      ring

/-- 3. The block-level `bs+72` cluster costs exactly `13,605,272,109` ticks at the cap, and no
more for any gas-feasible `c`. -/
theorem blkRead_le (c : Nat) (h : 2100 * c ≤ gasCap) :
    blkRead c ≤ 13605272109 ∧ blkRead maxColdPerBlock = 13605272109 := by
  constructor
  · have hc : c ≤ 95238 := by unfold gasCap at h; omega
    have hcc : c * (c - 1) ≤ 95238 * 95237 := by
      apply Nat.mul_le_mul hc
      omega
    have h2 := blkRead_closed c
    omega
  · have := blkRead_closed maxColdPerBlock
    unfold maxColdPerBlock at this ⊢; omega

/-! ## Per-transaction quadratic term (EIP-7825) -/

/-- 4. Within one transaction, any colliding cluster `c` with `w` warm lookups obeys
`21c + w ≤ txUnits`, so `c·(w+c) ≤ txUnits²/80` (reuse of `per_tx_probes`). -/
theorem per_tx_cluster (c w : Nat) (h : 21 * c + w ≤ txUnits) :
    80 * (c * (w + c)) ≤ txUnits * txUnits :=
  InitECandidate.Solver.GuestMemoryAndAccountOpcodeBounds.per_tx_probes c w txUnits h

/-- 5. With the heaviest per-tx opcode slope `pSstore = 14`, one transaction's collision ticks are
`≤ 14 · txUnits²/80 = 4,925,802,697`. -/
theorem per_tx_sstore_ticks (c w : Nat) (h : 21 * c + w ≤ txUnits) :
    pSstore * (c * (w + c)) ≤ 4925802697 := by
  have hp := per_tx_cluster c w h
  unfold pSstore sstoreFinds pFind
  unfold txUnits at hp
  omega

/-! ## Combined master bound -/

/-- Number of full `16,777,216`-gas transactions that fit in a 200M-gas block (`⌊200M/16777216⌋`). -/
def txPerBlock : Nat := 11

/-- 6. `11` transactions exhaust ≤ 200M gas; the 12th would overflow. -/
theorem txPerBlock_fits : txPerBlock * txGasCap ≤ gasCap ∧ gasCap < (txPerBlock + 1) * txGasCap := by
  decide

/-- Combined source-clock model: prologue + linear `18·gas` envelope + per-tx collision term over
all `txPerBlock` transactions (`pSstore` slope) + the single block-level `bs+72` term. -/
def kPanBlock (c : Nat) : Nat :=
  SelfContainedMasterK.prologueTicks + 18 * gasCap + txPerBlock * 4925802697 + blkRead c

/-- 7. Master bound: for every gas-feasible cold-read count, the combined `SLOAD`+`SSTORE`+
`BALANCE`+`PUSH31` model is `≤ 71,448,666,010` ticks (above `maxGuestSourceClock`). -/
theorem kPanBlock_le_max (c : Nat) (h : 2100 * c ≤ gasCap) :
    kPanBlock c ≤ 71448666010 ∧ kPanBlock c < 115000000000 := by
  have hb := (blkRead_le c h).1
  unfold kPanBlock SelfContainedMasterK.prologueTicks txPerBlock
  unfold gasCap
  omega

/-- 8. The combined worst case is far below the Yukon ceiling `900,719,925,474` (factor > 12),
and the block-level `bs+72` term is the only cross-transaction contribution. -/
theorem kPanBlock_within_yukon (c : Nat) (h : 2100 * c ≤ gasCap) :
    12 * kPanBlock c < 900719925474 ∧
      kPanBlock c = (SelfContainedMasterK.prologueTicks + 18 * gasCap +
        txPerBlock * 4925802697) + blkRead c := by
  have hb := (blkRead_le c h).1
  refine ⟨?_, by unfold kPanBlock; ring⟩
  unfold kPanBlock SelfContainedMasterK.prologueTicks txPerBlock gasCap
  omega

/-- 9. Tightness: at the cold-read cap the block term is maximal and the master value is exact. -/
theorem kPanBlock_tight :
    kPanBlock maxColdPerBlock = 71448666010 ∧
      maxGuestSourceClock < kPanBlock maxColdPerBlock := by
  have := (blkRead_le maxColdPerBlock (by decide)).2
  unfold kPanBlock SelfContainedMasterK.prologueTicks txPerBlock maxGuestSourceClock gasCap
  rw [this]; decide

/-- 10. Separation: the block-level `bs+72` term alone fits under `maxGuestSourceClock`, but the
summed per-tx `SSTORE` term (`11 × 4,925,802,697`) already exceeds it; it is the dominant term. -/
theorem separation :
    blkRead maxColdPerBlock < maxGuestSourceClock ∧
      maxGuestSourceClock < txPerBlock * 4925802697 ∧
      blkRead maxColdPerBlock < txPerBlock * 4925802697 := by
  have := (blkRead_le maxColdPerBlock (by decide)).2
  unfold txPerBlock maxGuestSourceClock
  rw [this]; decide

/-- 11. Per-opcode-slope threshold: with the per-tx slope `p` in place of `pSstore`, the model fits
under `maxGuestSourceClock` iff `p ≤ 6` (`p = 4` for `SLOAD`/`BALANCE`, `14` for `SSTORE`). -/
def kPanP (p : Nat) : Nat :=
  SelfContainedMasterK.prologueTicks + 18 * gasCap + txPerBlock * (p * (txUnits * txUnits / 80)) +
    13605272109
theorem kPanP_threshold (p : Nat) : kPanP p ≤ maxGuestSourceClock ↔ p ≤ 6 := by
  unfold kPanP SelfContainedMasterK.prologueTicks txPerBlock txUnits gasCap maxGuestSourceClock
  omega

end InitECandidate.Solver.GuestBlockVsTxHtabBounds
