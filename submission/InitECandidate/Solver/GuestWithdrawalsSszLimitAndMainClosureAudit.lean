import InitECandidate.Solver.GuestSszHtrHeadersAndCompleteMainBound

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestWithdrawalsSszLimitAndMainClosureAudit`

Hand reading of `guest.pp.pnk` (wt-2).

**No `MAX_WITHDRAWALS_PER_PAYLOAD = 16` check.**
* `decode_payload` (l.2902): `nwd = ssz_fixed_list_count(o_bal − o_wd, 44, 9223372036854775807)`;
  `ssz_fixed_list_count` (l.2892) only fails if `qr.0 > lim` with `lim = 2^63 − 1`.
  Transactions: `ssz_split_var_list(…, 9223372036854775807)`, same.
* `htr_payload` (l.3064): withdrawals root = `htr_plist_chunks(roots, nwd, nwd, …)` →
  `merkleize_progressive` (no fixed depth, grows by `×4` per level) + `mix_in_length`. The limit
  passed is `nwd` itself; no depth-4 cap, no exception.
* The only cap is `payload_header`'s block RLP `≤ 8,388,608` ⇒ `nwd ≤ 335,544`. (If the root were
  wrong the block is rejected later, but after `execute_block` has run.)

**Per-withdrawal cost** (`process_withdrawals` l.15387 → `create_ether` l.5861):
address-keyed (20-byte, unsalted hash) finds: `get_account_optional` `htab_set(ts+8)` +
`htab_get(ts+16)`; `get_pre_state_account_optional` `htab_set(ts+8)` + `htab_get(bs+16)`;
`record_pre_state_read` `htab_set(bs+72)`; `jset(ts+16)` `htab_get` + `htab_set` ⇒ **`f ≥ 6`**
colliding finds (`≤ 8` with insert-raw re-probes). Linear: `keccak256` of the address, `trie_walk
≤ 65`, `decode_account_from_leaf`, `acct_copy`, `u256_*` ⇒ `≤ 2,000` ticks; plus the withdrawals
trie entry in `build_mpt_indexed` at the chain's `130,000` (`2 · 65` visits × `1,000`):
**`132,000` ticks/withdrawal** (conservative, hand count).
-/

namespace InitECandidate.Solver.GuestWithdrawalsSszLimitAndMainClosureAudit

open InitECandidate.Solver.GuestSszHtrHeadersAndCompleteMainBound (maxInput nwdMax r1 r4)

/-- The limit passed to `ssz_fixed_list_count` for withdrawals. -/
def sszLim : Nat := 9223372036854775807

/-- 1. The SSZ limit is not `16`: `335,544` withdrawals pass `ssz_fixed_list_count`. -/
theorem ssz_no_cap : nwdMax ≤ sszLim ∧ 16 < nwdMax := by decide

/-- 2. Spec depth `4` (`2⁴ = 16` leaves) vs. the Guest bound. -/
theorem spec_vs_guest : 2 ^ 4 = 16 ∧ 335544 / 16 = 20971 := by decide

/-- Withdrawal-phase ticks: prologue `2 ρ` + linear `132,000 n` + `f · n(n−1)` collisions. -/
def wdTicks (f n : Nat) : Nat := 2 * maxInput + 132000 * n + f * (n * (n - 1))

/-- 3. Linear part at the cap: `44,291,808,000`. -/
theorem linear_val : 132000 * nwdMax = 44291808000 := by decide

/-- 4. **`1×` without collisions (salted)**: closes, margin `626,933,565,707`. -/
theorem close_1x_salted : wdTicks 0 nwdMax ≤ r1 ∧ r1 - wdTicks 0 nwdMax = 626933565707 := by
  decide

/-- 5. **`1×` unsalted with `f = 6` finds fails** at the cap. -/
theorem fail_1x_unsalted : r1 < wdTicks 6 nwdMax := by decide

/-- 6. `1×` unsalted threshold at `f = 6`: `n ≤ 323,652`, `323,653` fails. -/
theorem nmax_f6 : wdTicks 6 323652 ≤ r1 ∧ r1 < wdTicks 6 323653 := by decide

/-- 7. At `f = 8`: `n ≤ 281,528`. -/
theorem nmax_f8 : wdTicks 8 281528 ≤ r1 ∧ r1 < wdTicks 8 281529 := by decide

/-- 8. **`4×` (memo) fails at the cap even salted**. -/
theorem fail_4x : r4 < wdTicks 0 nwdMax := by decide

/-- 9. `4×` salted linear threshold: `n ≤ 189,516`. -/
theorem nmax_4x : wdTicks 0 189516 ≤ r4 ∧ r4 < wdTicks 0 189517 := by decide

/-- 10. **With the spec cap `nwd ≤ 16`**, even unsalted (`f = 8`) the withdrawal phase is
negligible and `4×` closes with margin `25,014,084,625`. -/
theorem spec_cap_closes (n : Nat) (h : n ≤ 16) : wdTicks 8 n ≤ wdTicks 8 16 ∧
    wdTicks 8 16 ≤ r4 ∧ r4 - wdTicks 8 16 = 25014084625 := by
  refine ⟨?_, by decide, by decide⟩
  unfold wdTicks
  have h1 : 132000 * n ≤ 132000 * 16 := Nat.mul_le_mul_left _ h
  have h2 : n * (n - 1) ≤ 16 * (16 - 1) := Nat.mul_le_mul h (by omega)
  have h3 : 8 * (n * (n - 1)) ≤ 8 * (16 * (16 - 1)) := Nat.mul_le_mul_left _ h2
  omega

/-- 11. The fix is one comparison in `decode_payload`: `ssz_fixed_list_count(…, 44, 16)`. -/
theorem fix_shape : (16 * 44 : Nat) = 704 ∧ 704 < 8388608 := by decide

end InitECandidate.Solver.GuestWithdrawalsSszLimitAndMainClosureAudit
