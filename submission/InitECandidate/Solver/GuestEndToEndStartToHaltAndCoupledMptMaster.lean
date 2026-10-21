import InitECandidate.Solver.GuestCoupledGasFullBlockWithProbesAndTransientMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestEndToEndStartToHaltAndCoupledMptMaster`

Hand transcription of the top level of `guest.pp.pnk` (wt-2).

`main` (l.15681): 14 `*_init`, `input_blob`, `decode_stateless_input` (SSZ, l.2984),
`htr_new_payload_request` (SSZ hash-tree-root, `merkleize` + `@sha256f`), then
`verify_stateless_new_payload` → `attempt_l7 … attempt_l1` (exception wrappers) → `run_attempt`:
`validate_headers`, two `nodedb_build`, `state_init` (decodes the state root via
`decode_witness_to_mpt`), a `ntx` loop, `payload_header` + `header_hash`, `is_valid_versioned_hashes`,
`validate_header`, `execute_block` (l.15469). Then `serialize_result`, `output_write`, `@halt`.

`execute_block`: 2 system txs, per tx `decode_transaction` + `process_transaction` (EVM loop),
`process_withdrawals`, `process_general_purpose_requests`, `build_block_access_list_rlp`,
`compute_state_root`, three `build_mpt_indexed` (txs, receipts, withdrawals), `logs_bloom`,
`compute_requests_hash`, `keccak256` of the BAL, 7 `memeq` header checks.

There is no `_mpt_put` / `_mpt_delete` / `_state_root`: writes are `mpt_set` (value or empty).

**Not yet bounded by any module of the chain** (outside EVM / witness / MPT state):
SSZ decode + hash-tree-root, header RLP/validation, `decode_transaction` + sender recovery
(`secp256k1_recover`), the three `build_mpt_indexed` tries, `logs_bloom`, BAL build, requests hash.
This module states the remaining Yukon budget they must fit in, not a bound on them.

Coupled MPT writes: `compute_state_root` does `mpt_set` only for keys in `bs+32` (written slots).
Each such key consumed `≥ 21` units of the shared budget, so `≤ 95,238` keys instead of the
`100,000` used in `mptPlusBuild` (`130,000` ticks per key: `2 · 65` visits at `1,000`).
-/

namespace InitECandidate.Solver.GuestEndToEndStartToHaltAndCoupledMptMaster

open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

/-- 1. Written keys per block on the shared budget: `≤ 95,238` (`21` units each), tight. -/
theorem dirty_keys (k : Nat) (h : 21 * k ≤ 2000000) : k ≤ 95238 := by omega

theorem dirty_keys_tight : 21 * 95238 ≤ 2000000 ∧ 2000000 < 21 * 95239 := by decide

/-- 2. State-root writes coupled: `≤ 130,000 · 95,238 = 12,380,940,000` ticks (was `13·10⁹`). -/
theorem root_coupled (k : Nat) (h : 21 * k ≤ 2000000) : 130000 * k ≤ 12380940000 := by omega

/-- 3. Gain of the coupling: `619,060,000` ticks. -/
theorem coupling_gain : 13000000000 - 130000 * 95238 = 619060000 := by decide

/-- 4. The MPT slope per written key (`130,000 / 21 ≈ 6,190` per unit) is under the absorption
slope `50,000`, but the keys are the **same** units as the storage quadratic term, so
`general_side_regime_absorption` (which needs disjoint units) does not apply: at `B = 2·10⁶`
storage alone already reaches `10¹¹`. -/
theorem no_absorption : 130000 ≤ 21 * 50000 ∧ 40 * 100000000000 = 2000000 * 2000000 := by decide

/-- 5. Coupled block totals (heap / memo). -/
theorem coupled_totals : 224985309693 - 619060000 = 224366249693 ∧
    195654540749 - 619060000 = 195035480749 := by decide

/-- 6. `1×` remaining budget for the unbounded pre/post-EVM work: `676,353,675,781`. -/
theorem residual_1x : yukon - 224366249693 = 676353675781 := by decide

/-- 7. `4×` remaining budget (per quarter): heap `813,731,675`, memo `30,144,500,619`. -/
theorem residual_4x : yukon / 4 - 224366249693 = 813731675 ∧
    yukon / 4 - 195035480749 = 30144500619 := by decide

/-- 8. As a rate per input byte (`134,217,712`): `1×` needs `≤ 5,039` ticks/byte; `4×` heap
`≤ 6`; `4×` memo `≤ 224`. -/
theorem per_byte : 5039 * 134217712 ≤ 676353675781 ∧ 676353675781 < 5040 * 134217712 ∧
    6 * 134217712 ≤ 813731675 ∧ 813731675 < 7 * 134217712 ∧
    224 * 134217712 ≤ 30144500619 ∧ 30144500619 < 225 * 134217712 := by decide

/-- 9. As a rate per transaction (`≤ 16,666` tx at `12,000` gas): `4×` heap `≤ 48,825`
ticks/tx (sender recovery included); `4×` memo `≤ 1,808,742`. -/
theorem per_tx : 200000000 / 12000 = 16666 ∧
    48825 * 16666 ≤ 813731675 ∧ 813731675 < 48826 * 16666 ∧
    1808742 * 16666 ≤ 30144500619 ∧ 30144500619 < 1808743 * 16666 := by decide

/-- 10. Constant reconciliation: the request's `20,037,125,024` is not the chain's
`mptPlusBuild = 20,036,870,848` (difference `254,176`). -/
theorem mpt_const : 19500000000 + 536870848 = 20036870848 ∧
    20037125024 - 20036870848 = 254176 := by decide

end InitECandidate.Solver.GuestEndToEndStartToHaltAndCoupledMptMaster
