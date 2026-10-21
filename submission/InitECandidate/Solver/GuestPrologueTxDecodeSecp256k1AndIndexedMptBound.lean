import InitECandidate.Solver.GuestEndToEndStartToHaltAndCoupledMptMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestPrologueTxDecodeSecp256k1AndIndexedMptBound`

Hand reading of `guest.pp.pnk` (wt-2), convention 1 tick per `while` body / call, 0 for FFI.

**Transactions.** Guest intrinsic gas is `12,000` (`calculate_intrinsic_cost`, l.5298), not `21,000`:
`≤ 16,666` user txs (`9,523` only under the `21,000` premise) + 2 system txs.

**Sender recovery** (`recover_sender` l.5268 → `secp256k1_recover` l.2375): fixed-size, no
input-dependent loop. `ec_mul2` (l.2220): 15-entry table, then `128` windows, each `2 ec_double`
(FFI `@secpdbl`) + `≤ 1 ec_add` (43 calls) + `4 u256_bit` ⇒ `≤ ~72` ticks/window, `~9,300`.
`fn_inv` / `fp_inv` / `fp_sqrt` = `secp_accel_*_pow4`: `14 + 64·(1+4+1)` field ops via FFI
`@arith256mod` ⇒ `~1,400` each. Total `≤ ~14,000`; we use **`30,000` ticks/tx** (conservative).

**Indexed tries** (`build_mpt_indexed` l.4552): per entry one `mpt_set` + share of `mpt_root`,
the same `2 · 65` node visits as the state root at `1,000` ticks/visit ⇒ **`130,000`/entry**,
entries = txs (txs), txs (receipts), withdrawals (bounded by input, counted in the prologue rate).

**`logs_bloom`** (l.14449): per log `1 + 1` call per address/topic (`add_to_bloom` = Keccak of 20/32
bytes). Logs cost `≥ 375` gas each ⇒ `≤ 533,333` logs; each topic costs `375` gas too, so
`≤ 50` ticks per 375-gas unit is conservative.

**Prologue** (`decode_stateless_input` 1 loop, `htr_payload` 2 loops, `merkleize` + `@sha256f`,
`validate_headers` 2 loops, `validate_header` / `header_hash` straight-line + Keccak): every loop
runs over input bytes or input items. Not tick-counted here: stated as a per-input-byte rate `ρ`,
with the exact budget left.

All per-unit constants above are **conservative hand estimates**, not `PanSem`-derived.
-/

namespace InitECandidate.Solver.GuestPrologueTxDecodeSecp256k1AndIndexedMptBound

open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

/-- 1. Tx count: Guest intrinsic `12,000` ⇒ `16,666`; the `21,000` premise gives `9,523`. -/
theorem tx_count (t : Nat) (h : 12000 * t ≤ 200000000) : t ≤ 16666 ∧ 200000000 / 21000 = 9523 := by
  constructor
  · omega
  · decide

/-- 2. Sender recovery for all txs (incl. 2 system): `≤ 30,000 · 16,668`. -/
theorem secp_total (t : Nat) (h : t ≤ 16668) : 30000 * t ≤ 500040000 := by omega

/-- 3. Two tx-indexed tries (txs, receipts): `≤ 2 · 130,000 · 16,666 = 4,333,160,000`. -/
theorem tries_total (t : Nat) (h : t ≤ 16666) : 2 * 130000 * t ≤ 4333160000 := by omega

/-- 4. Logs bloom: `≤ 533,333` log units of 375 gas, `≤ 50` ticks each. -/
theorem bloom_total (g : Nat) (h : 375 * g ≤ 200000000) : 50 * g ≤ 26666650 := by omega

/-- Per-tx / per-gas post-EVM terms. -/
def postTerms : Nat := 500040000 + 4333160000 + 26666650

/-- 5. Their sum: `4,859,866,650`. -/
theorem post_val : postTerms = 4859866650 := by decide

/-- 6. **`1×`**: after these terms, `671,493,809,131` remain for the prologue, i.e. `≤ 5,003`
ticks per input byte. -/
theorem prologue_1x : 676353675781 - postTerms = 671493809131 ∧
    5003 * 134217712 ≤ 671493809131 ∧ 671493809131 < 5004 * 134217712 := by decide

/-- 7. **`4×` without memoization fails**: post terms alone exceed the `813,731,675` residual. -/
theorem fourx_heap_fails : 813731675 < postTerms := by decide

/-- 8. **`4×` with memoization**: `25,284,633,969` remain, `≤ 188` ticks per input byte. -/
theorem prologue_4x_memo : 30144500619 - postTerms = 25284633969 ∧
    188 * 134217712 ≤ 25284633969 ∧ 25284633969 < 189 * 134217712 := by decide

/-- 9. Even counting secp at `30,000` the dominant post-EVM term is the tries (`89 %`). -/
theorem tries_dominate : 10 * 4333160000 ≥ 8 * postTerms := by decide

/-- 10. With the `21,000` premise (`9,523` txs) the post terms would be `2,788,396,650`: still
over the `4×` heap residual. -/
theorem premise_21000 : 30000 * 9525 + 2 * 130000 * 9523 + 26666650 = 2788396650 ∧
    813731675 < 2788396650 := by decide

/-- 11. Secp per tx is input-independent: `128` windows × `≤ 72` ticks plus 3 pow4 of `≤ 1,400`
and setup fit `30,000`. -/
theorem secp_per_tx : 128 * 72 + 3 * 1400 + 1500 ≤ 30000 := by decide

end InitECandidate.Solver.GuestPrologueTxDecodeSecp256k1AndIndexedMptBound
