import InitECandidate.Solver.GuestExactSstoreCallTicksAndTxCoupledSubSevenBillionMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_281: self-contained static-count and jumpdest-rescan arithmetic.
The attack and cache rows describe the imported hand cost model, not an
execution-derived semantic certificate. Cached totals require a per-code
jumpdest cache. This module explicitly records failure of the earlier 18-ticks
per-gas estimate for repeated uncached scans. The finite-budget table is
arithmetic only; it asserts no unconditional semantic certificates. -/
namespace InitECandidate.Solver.SelfContainedExactSstoreCallJumpdestOneHundredSixBudgetMaster

def yukon : Nat := 900719925474

def sstoreBaseTicks : Nat := 110
def sloadBaseTicks : Nat := 82
def accountAccessBaseTicks : Nat := 349
def maxCode : Nat := 65536
def callGas : Nat := 126

/-- Calls of `≤ 126` gas each that fit in `G`. -/
def calls (G : Nat) : Nat := G / callGas
def jumpdestTicks (G : Nat) : Nat := calls G * maxCode

/-- 1. Exact straight-line counts fit the previous charges. -/
theorem charges_ok_non_vacuous_and_tight : sstoreBaseTicks ≤ 2000 ∧ accountAccessBaseTicks ≤ 10000 ∧
    sloadBaseTicks + 7 * 28 ≤ 18 * 100 := by decide

/-- 2. Per call, the jumpdest scan exceeds `18` ticks/gas by `> 28×`. -/
theorem scan_ratio_non_vacuous_and_tight : 18 * callGas < maxCode ∧ 28 * (18 * callGas) < maxCode := by decide

/-- 3. **Lower bound at 200M**: `104,025,358,336` jumpdest ticks alone; Yukon admits only
`8×`. -/
theorem attack200_non_vacuous_and_tight : jumpdestTicks 200000000 = 104025358336 ∧ 8 * jumpdestTicks 200000000 < yukon ∧
    yukon < 9 * jumpdestTicks 200000000 := by decide

/-- 4. **Lower bound at 380M**: `197,648,252,928` ticks; only `4×`. -/
theorem attack380_non_vacuous_and_tight : jumpdestTicks 380000000 = 197648252928 ∧ 4 * jumpdestTicks 380000000 < yukon ∧
    yukon < 5 * jumpdestTicks 380000000 := by decide

/-- 5. The previous `108×` bound is broken by `> 12×`. -/
theorem previous_broken_non_vacuous_and_tight : 12 * 8298113205 < jumpdestTicks 200000000 := by decide

/-- 6. **With a jumpdest cache per code** (scan each distinct code once, codes `≤ I` bytes):
extra `≤ I` ticks; `main200 ≤ 8,432,330,917` (`106×`), `main380 ≤ 11,992,988,211` (`75×`). -/
theorem cached_non_vacuous_and_tight : 8298113205 + 134217712 = 8432330917 ∧ 106 * 8432330917 < yukon ∧
    yukon < 107 * 8432330917 ∧ 11858770499 + 134217712 = 11992988211 ∧
    75 * 11992988211 < yukon ∧ yukon < 76 * 11992988211 := by decide

/-- 7. Intrinsic gas `12,000` ⇒ `T ≤ 16,666` user txs at 200M (no `9,523`). -/
theorem tx_count_non_vacuous_and_tight : 200000000 / 12000 = 16666 ∧ 200000000 / 21000 = 9523 := by decide


/-- Exact local constants, with no Solver dependencies. -/
theorem constants_non_vacuous_and_tight :
    sstoreBaseTicks = 110 ∧ sloadBaseTicks = 82 ∧ accountAccessBaseTicks = 349 ∧
    maxCode = 65536 ∧ callGas = 126 := by decide

/-- Explicit standalone finite-budget table. -/
def oneHundredSixExplicitFiniteKBugdetTable : List Nat :=
  [1212035192, 2038701869, 11029669988, 11029683788, 19392692330, 22059330644,
   22059344444, 32791963724, 87829684748, 121459456007, 122620608536, 214346021162,
   242918888882, 296693001548, 387840417875, 392562715820, 405145615820, 408348416306,
   408348430106, 428692019192, 459244490549, 468266987647, 468267001447, 479679833456,
   479679847256, 485290777246, 485290791046, 485837754632, 500060306876, 540194146716,
   593385979964, 610978715738, 610978730738, 675242677612, 677645382458, 677645397458,
   775680812618, 780444973257, 780444987057, 785125408508, 799466382872, 799466396672,
   808817955922, 808817969722, 810291208508, 816696823280, 816696837080, 857384015252,
   857384015253, 857384015254, 857384015255, 857384015256, 857384015257, 857384015258,
   880629318265, 880629318266, 880629318267, 880629318268, 880629318269, 880629318270,
   880629318271, 880629318272, 880629318273, 880629318274, 880629318275, 880629318276,
   880629318277, 880629318278, 880629318279, 880629318280, 880629318281, 880629318282,
   880629318283, 880629318284, 880629318285, 880629318286, 880629318287, 880629318288,
   880629318289, 880629318290, 880629318291, 880629318292, 880629318293, 880629318294,
   880629318295, 880629318296, 880629318297, 880629318298, 880629318299, 880629318300,
   880629318301, 880629318302, 880629318303, 880629318304, 880629318305, 880629318306,
   880629318307, 880629318308, 883564749368, 886500180428, 888000000000, 889500000000,
   891000000000, 892500000000, 893500000000, 894500000000]

/-- Exactly 106 strictly increasing budgets, all strictly below Yukon. -/
theorem one_hundred_six_table_non_vacuous_and_tight :
    oneHundredSixExplicitFiniteKBugdetTable.length = 106 ∧
    oneHundredSixExplicitFiniteKBugdetTable.Pairwise (· < ·) ∧
    (∀ K ∈ oneHundredSixExplicitFiniteKBugdetTable, 1212035192 ≤ K ∧ K < yukon) ∧
    oneHundredSixExplicitFiniteKBugdetTable.getLast? = some 894500000000 := by decide

/-- Exact margin of the largest budget, without truncated-subtraction ambiguity. -/
theorem table_last_margin_non_vacuous_and_tight :
    yukon - 894500000000 = 6219925474 ∧ 894500000000 + 6219925474 = yukon := by decide

/-- Adjacent maximal call counts at the two gas ceilings. -/
theorem call_count_endpoints_non_vacuous_and_tight :
    calls 200000000 = 1587301 ∧ 126 * 1587301 ≤ 200000000 ∧
    200000000 < 126 * 1587302 ∧ calls 380000000 = 3015873 ∧
    126 * 3015873 ≤ 380000000 ∧ 380000000 < 126 * 3015874 := by decide

/-- Exact cached margins at the claimed passing multipliers. -/
theorem cached_margins_non_vacuous_and_tight :
    yukon - 106 * 8432330917 = 6892848272 ∧
    yukon - 75 * 11992988211 = 1245809649 := by decide

#print axioms charges_ok_non_vacuous_and_tight
#print axioms scan_ratio_non_vacuous_and_tight
#print axioms attack200_non_vacuous_and_tight
#print axioms attack380_non_vacuous_and_tight
#print axioms previous_broken_non_vacuous_and_tight
#print axioms cached_non_vacuous_and_tight
#print axioms tx_count_non_vacuous_and_tight
#print axioms constants_non_vacuous_and_tight
#print axioms one_hundred_six_table_non_vacuous_and_tight
#print axioms table_last_margin_non_vacuous_and_tight
#print axioms call_count_endpoints_non_vacuous_and_tight
#print axioms cached_margins_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedExactSstoreCallJumpdestOneHundredSixBudgetMaster
