import InitECandidate.Solver.GuestPrologueTxDecodeSecp256k1AndIndexedMptBound

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestSszHtrHeadersAndCompleteMainBound`

Hand reading of `guest.pp.pnk` (wt-2), 1 tick per `while` body / call, 0 for loads and FFI.

**Input-proportional prologue** (`ρ ≤ 2` ticks/input byte, conservative):
* `decode_stateless_input` (l.2984): fixed header, `ssz_check_offsets` on 2–5 offsets,
  `ssz_split_var_list` one iteration per 4-byte offset, `decode_bytes_list` one per item.
* `htr_new_payload_request` → `htr_payload` (l.3064): `pack_bytes` (`memcpy`), `merkleize`
  (`sha256_pair` per pair of 32-byte chunks: `≤ 12` ticks per 64 bytes, FFI `@sha256f`).
* `validate_headers` (l.3417): `≤ 256` headers of `≤ 1,024` bytes, `decode_header` + Keccak.
* `compute_requests_hash`: one `sha256` per request + one over `32 n` bytes.

**New finding: withdrawals.** `payload_header` (l.14853) only caps the block RLP at `8,388,608`
bytes; one withdrawal is `≥ 25` RLP bytes ⇒ `nwd ≤ 335,544`. Withdrawals consume **no gas**.
`process_withdrawals` (l.15387) calls `create_ether(addr)` per withdrawal: `get_account` →
`htab_set(ts+8, addr)`, `htab_get(ts+16, addr)`, `htab_get(bs+16, addr)`, then `jset(ts+16, addr)`.
All tables are keyed by the attacker-chosen 20-byte address with the **unsalted** `htab_hash`.
Linear part (account trie walk + Keccak + withdrawal trie entry) `≤ 200,000` ticks each.
Colliding part: `f` finds per withdrawal over a run of `i` previous keys, `≥ 1` tick per step ⇒
`f · n(n−1)` with `f` the number of colliding-table finds (not counted exactly; `4` finds, `2`
ticks/step gives `f = 4`).
-/

namespace InitECandidate.Solver.GuestSszHtrHeadersAndCompleteMainBound

open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

def maxInput : Nat := 134217712
def nwdMax : Nat := 335544
def r1 : Nat := 671493809131
def r4 : Nat := 25284633969

/-- 1. Prologue at `ρ = 2` ticks/byte: `268,435,424`. -/
theorem prologue_val : 2 * maxInput = 268435424 := by decide

/-- 2. Withdrawal count from the `8 MiB` block RLP cap, `25` bytes each: `335,544`, tight. -/
theorem nwd_le (n : Nat) (h : 25 * n ≤ 8388608) : n ≤ nwdMax := by unfold nwdMax; omega

theorem nwd_tight : 25 * 335544 ≤ 8388608 ∧ 8388608 < 25 * 335545 := by decide

/-- 3. Withdrawals are gas-free: their count is independent of the `200M` budget. -/
theorem nwd_vs_gas : 200000000 / 12000 < nwdMax := by decide

/-- 4. Linear withdrawal term: `200,000 · 335,544 = 67,108,800,000`. -/
theorem wd_linear (n : Nat) (h : n ≤ nwdMax) : 200000 * n ≤ 67108800000 := by
  unfold nwdMax at h; omega

/-- 5. Collision term per find: `n(n−1) = 112,589,440,392` at `n = 335,544`. -/
theorem wd_quad : 335544 * (335544 - 1) = 112589440392 := by decide

/-- 6. **`1×` closes without collisions**: prologue + withdrawals linear leave
`604,116,573,707`. -/
theorem close_1x_linear : r1 - 2 * maxInput - 200000 * nwdMax = 604116573707 := by decide

/-- 7. **`1×` with unsalted collisions**: passes for `f ≤ 5` colliding finds, fails at `6`. -/
theorem close_1x_quad : 5 * 112589440392 ≤ 604116573707 ∧ 604116573707 < 6 * 112589440392 := by
  decide

/-- 8. **`4×` (memo) fails on withdrawals alone**, even without collisions: linear term exceeds the
`25,284,633,969` residual. -/
theorem fourx_fails : r4 < 2 * maxInput + 200000 * nwdMax := by decide

/-- 9. `4×` withdrawal threshold: `≤ 125,080` withdrawals fit, `125,081` do not. -/
theorem fourx_wd_threshold : 2 * maxInput + 200000 * 125080 ≤ r4 ∧
    r4 < 2 * maxInput + 200000 * 125081 := by decide

/-- 10. Per-input-byte rates: `1×` remaining rate is `≤ 5,003`/byte, so `ρ = 2` is far inside;
`4×` memo is `≤ 188`/byte. -/
theorem rho_inside : 2 ≤ 188 ∧ 188 * maxInput ≤ r4 ∧ 5003 * maxInput ≤ r1 := by decide

/-- 11. The withdrawal term dominates the prologue by `≥ 249×`. -/
theorem wd_dominates : 249 * (2 * maxInput) ≤ 200000 * nwdMax := by decide

end InitECandidate.Solver.GuestSszHtrHeadersAndCompleteMainBound
