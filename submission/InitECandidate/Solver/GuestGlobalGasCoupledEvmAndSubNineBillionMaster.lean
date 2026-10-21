import InitECandidate.Solver.GuestEvmStepDispatchAndNinetyXMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestGlobalGasCoupledEvmAndSubNineBillionMaster`

**Double count removed.** `18 · G` charged all gas as `PUSH31`, while the trie/witness LP spent
`24 A + 21 K` units of the same gas on accounts and storage keys. Here one gas budget feeds
both: `P` units of cheap opcodes at `1,800` ticks/unit, plus `A` accounts and `K` keys,
`24 A + 21 K + P ≤ units`.

**Per-op dispatch charges (`Guest/guest.pp.pnk` wt-2, static call graph).**
`op_sstore` (l.7499) reaches 83 functions; its loops are `htab_*` (salted, counted in the
`28`-tick finds), `keccak256`/`trie_walk`/witness decode (counted in the walk, witness and
Keccak rows), `memcpy`/`memzero` (`≤ 32` bytes). Straight-line calls: `22` direct, `≤ 2,000`
ticks with the salted finds (`7 × 28`) and one `≤ 65`-step walk. We charge **`2,000` ticks per
key** on top of the `1,950` traversal ticks already in the LP.
`op_call`/`op_staticcall` (account access, l.~8300): `35` direct calls, `generic_call` →
`start_child` (frame setup, `scratch_mark`, calldata copy paid by memory gas); charge
**`10,000` ticks per account**. These two constants are hand bounds, not line-by-line sums.

Fixed rows (everything except `18 G` and the LP): `1,391,298,018` (200M), `1,675,717,026`
(380M).
-/

namespace InitECandidate.Solver.GuestGlobalGasCoupledEvmAndSubNineBillionMaster

open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

def inputBytes : Nat := 134217712
def cost (A K B E n2 n17 m P : Nat) : Nat :=
  10000 * A + 3950 * K + 633 * B + 439 * E + 138 * n2 + 416 * n17 + 90 * m + 1800 * P

def fixed200 : Nat := 11546768760 - 18 * 200000000 - 6555470742
def fixed380 : Nat := 17251948659 - 18 * 380000000 - 8736231633
def main200 : Nat := fixed200 + (20720445560 + 2) / 3
def main380 : Nat := fixed380 + (661898475728 + 64) / 65

/-- 1. Fixed rows. -/
theorem fixed_vals : fixed200 = 1391298018 ∧ fixed380 = 1675717026 := by decide

/-- 2. **Global joint bound at 200M** (one gas budget for cheap ops, accounts, keys). -/
theorem joint200 (A K B E n2 n17 m P : Nat) (hg : 24 * A + 21 * K + P ≤ 2000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A)) (hw : 7 * n2 + 22 * n17 + 4 * m ≤ inputBytes) :
    3 * cost A K B E n2 n17 m P ≤ 20720445560 := by
  unfold cost inputBytes at *; omega

/-- 3. **Global joint bound at 380M.** -/
theorem joint380 (A K B E n2 n17 m P : Nat) (hg : 24 * A + 21 * K + P ≤ 3800000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A)) (hw : 7 * n2 + 22 * n17 + 4 * m ≤ inputBytes) :
    65 * cost A K B E n2 n17 m P ≤ 661898475728 := by
  unfold cost inputBytes at *; omega

/-- 4. Extremes: all-`PUSH31` gives `3.6·10⁹ + 90·I/4`, below the joint bound. -/
theorem all_push : 3 * cost 0 0 0 0 0 0 (inputBytes / 4) 2000000 ≤ 20720445560 := by decide

/-- 5. **`main200 = 8,298,113,205`: `108×` passes, `109×` fails; below `9·10⁹`.** -/
theorem main200_slope : main200 = 8298113205 ∧ 108 * main200 < yukon ∧ yukon < 109 * main200 ∧
    main200 < 9000000000 := by decide

/-- 6. **`main380 = 11,858,770,499`: `75×` passes, `76×` fails.** -/
theorem main380_slope : main380 = 11858770499 ∧ 75 * main380 < yukon ∧ yukon < 76 * main380 := by
  decide

/-- 7. Margins. -/
theorem margins : yukon - 108 * main200 = 4523699334 ∧ yukon - 75 * main380 = 11312138049 := by
  decide

/-- 8. Sensitivity: with `5,000` per key and `20,000` per account the 200M total is
`9,131,446,538` (`98×`): the sub-9·10⁹ claim needs the per-op charges. -/
theorem sensitivity : 98 * 9131446538 < yukon ∧ yukon < 99 * 9131446538 := by decide

end InitECandidate.Solver.GuestGlobalGasCoupledEvmAndSubNineBillionMaster
