import InitECandidate.Solver.GuestMptTraversalAndStateRootBound
import InitECandidate.Solver.GuestNodedbAndWitnessTableBound
import InitECandidate.Solver.GuestTransientStorageSubcallRevertAndAbsorption

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge`

Arithmetic bridge between three certified envelopes:

* MPT traversal (`GuestMptTraversalAndStateRootBound`): `steps_le` ≤ 64, `walk_iters` ≤ 65,
  `access_totals` ≤ 6,500,000 visits, `state_root_totals` ≤ 13,000,000 visits and 6,500,000
  hashes, `linear_budget` = 19,500,000,000 ticks.
* Bounded-run `nodedb` build (`GuestNodedbAndWitnessTableBound`): `bounded_build_val` =
  536,870,848 ticks at `r = 8`, and `two_builds` keeps both builds inside that budget.
* Transient-storage absorption (`GuestTransientStorageSubcallRevertAndAbsorption`): the 11-table
  shared envelope `156,088,992,805` absorbs a `ts+64` run under `absorbed_with_cap` when
  `L ≤ 5,000` (with `REVERT`) or `L ≤ 10,000` (without), and `buildTicks` is superadditive
  (`split_le`, `split_strict`, `tx_worst_revert`).
-/

namespace InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge

open InitECandidate.Solver.GuestMptTraversalAndStateRootBound
open InitECandidate.Solver.GuestNodedbAndWitnessTableBound
open InitECandidate.Solver.GuestTransientStorageSubcallRevertAndAbsorption
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

/-- Combined MPT linear budget and bounded-run nodedb build. -/
def mptPlusBuild : Nat := 19500000000 + 536870848

/-- Storage envelope plus the combined MPT/nodedb budget. -/
def joint : Nat := 156088992805 + mptPlusBuild

/-- 1. The two budgets add to `20,036,870,848`. -/
theorem sum_val : mptPlusBuild = 20036870848 := by decide

/-- 2. That sum is more than `44×` under Yukon: `44 · sum < yukon ≤ 45 · sum`. -/
theorem sum_margin : 44 * mptPlusBuild < yukon ∧ yukon ≤ 45 * mptPlusBuild := by decide

/-- 3. The joint total is `176,125,863,653`. -/
theorem joint_val : joint = 176125863653 := by decide

/-- 4. At `1×` the margin under Yukon is `724,594,061,821`. -/
theorem joint_once : yukon - joint = 724594061821 := by decide

/-- 5. At `5×` it still fits, with margin `20,090,607,209`. -/
theorem joint_five : 5 * joint = 880629318265 ∧ yukon - 5 * joint = 20090607209 := by decide

/-- 6. `two_builds` instantiated at `r = 8`: both builds stay inside the certified budget. -/
theorem two_builds_at_8 (ns nc : Nat) (h : 4 * (ns + nc) ≤ maxInput) :
    boundedBuild 8 ns + boundedBuild 8 nc ≤ 536870848 := by
  have := two_builds 8 ns nc h
  have hb := bounded_build_val
  omega

/-- 7. MPT budget plus both builds stays under `mptPlusBuild`. -/
theorem mpt_plus_two_builds (ns nc : Nat) (h : 4 * (ns + nc) ≤ maxInput) :
    19500000000 + boundedBuild 8 ns + boundedBuild 8 nc ≤ mptPlusBuild := by
  have := two_builds_at_8 ns nc h
  unfold mptPlusBuild
  omega

/-- 8. The joint budget dominates the MPT budget, both builds and the storage envelope. -/
theorem joint_covers (ns nc : Nat) (h : 4 * (ns + nc) ≤ maxInput) :
    156088992805 + 19500000000 + boundedBuild 8 ns + boundedBuild 8 nc ≤ joint := by
  have := mpt_plus_two_builds ns nc h
  unfold joint
  omega

/-- 9. Splitting two chunks of 2 costs 10 against 30 for one chunk of 4, and one end-of-tx
revert doubles the build of 158,162 keys to `125,075,300,410`. -/
theorem build_split : 5 * (2 * 1) / 2 + 5 * (2 * 1) / 2 = 10 ∧ 5 * (4 * 3) / 2 = 30 ∧
    2 * (5 * (158162 * 158161) / 2) = 125075300410 := by
  decide

/-- 10. Both absorption thresholds are sharp: `10 · 5,000 = 50,000 < 10 · 5,001` and
`5 · 10,000 = 50,000 < 5 · 10,001`. -/
theorem anchors : 10 * 5000 = 50000 ∧ 50000 < 10 * 5001 ∧ 5 * 10000 = 50000 ∧ 50000 < 5 * 10001 := by
  decide

end InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge
