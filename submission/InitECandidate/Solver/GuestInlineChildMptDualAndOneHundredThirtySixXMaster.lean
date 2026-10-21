import InitECandidate.Solver.GuestSstoreDirtyKeyGasAndSubSevenBillionMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestInlineChildMptDualAndOneHundredThirtySixXMaster`

`_resolve_step` (l.3755, `Guest/guest.pp.pnk` wt-2): an empty child stops the descent; a
32-byte string is a hash reference (`nodedb_lookup`); **any other item is returned inline**
(`return <1, p, n, 0>`) with no `< 32`-byte check. So a traversed branch need not cost a
33-byte reference, and a rehashed branch need not be a witness item.

**Regime 1 (current Guest, unconditional).** Drop `hb : B ≤ N₁₇ + K + A`; `N₂, N₁₇` are bounded
only by witness bytes. Cached jumpdests assumed as in the previous modules.

**Regime 2 (Yellow-Paper rule: inline children must be `< 32` bytes, so each traversed
non-root branch is a witness item reached by a 33-byte reference).** Split witness branches
into dead-ends `d` (`22` bytes) and traversed `r` (`22 + 32` bytes); `B ≤ r + K + A`; each path
root (`A + K` of them) is referenced from outside the witness (`+32` byte credit). The optimum
moves back to all-`PUSH31` plus dead-end branches.
-/

namespace InitECandidate.Solver.GuestInlineChildMptDualAndOneHundredThirtySixXMaster

open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

def inputBytes : Nat := 134217712
def blockFixed : Nat := 370538614

def cost1 (A K L B E n2 n17 md ms P T : Nat) : Nat :=
  3473 * A + 5274 * K + 3124 * L + 633 * B + 439 * E + 127 * n2 + 405 * n17 + 43 * md +
    79 * ms + 18 * P + 42382 * T
def cost2 (A K L B E n2 d r md ms P T : Nat) : Nat :=
  3473 * A + 5274 * K + 3124 * L + 633 * B + 439 * E + 127 * n2 + 405 * d + 405 * r +
    43 * md + 79 * ms + 18 * P + 42382 * T

def inline200 : Nat := blockFixed + inputBytes + (3058910053880 + 450) / 451
def inline380 : Nat := blockFixed + inputBytes + (4809020803880 + 450) / 451
def yp200 : Nat := blockFixed + inputBytes + (66779086680 + 10) / 11
def yp380 : Nat := blockFixed + inputBytes + (102419086680 + 10) / 11

/-- 1. **Regime 1, 200M** (no `hb`). -/
theorem inline_200 (A K L B E n2 n17 md ms P T : Nat)
    (hg : 12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    451 * cost1 A K L B E n2 n17 md ms P T ≤ 3058910053880 := by
  unfold cost1 inputBytes at *; omega

/-- 2. **Regime 1, 380M.** -/
theorem inline_380 (A K L B E n2 n17 md ms P T : Nat)
    (hg : 12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 380000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    451 * cost1 A K L B E n2 n17 md ms P T ≤ 4809020803880 := by
  unfold cost1 inputBytes at *; omega

/-- 3. **Regime 2, 200M** (hashed children only). -/
theorem yp_200 (A K L B E n2 d r md ms P T : Nat)
    (hg : 12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ r + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * d + 54 * r + 4 * md + 5 * ms ≤ inputBytes + 32 * (A + K)) :
    11 * cost2 A K L B E n2 d r md ms P T ≤ 66779086680 := by
  unfold cost2 inputBytes at *; omega

/-- 4. **Regime 2, 380M.** -/
theorem yp_380 (A K L B E n2 d r md ms P T : Nat)
    (hg : 12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 380000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ r + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * d + 54 * r + 4 * md + 5 * ms ≤ inputBytes + 32 * (A + K)) :
    11 * cost2 A K L B E n2 d r md ms P T ≤ 102419086680 := by
  unfold cost2 inputBytes at *; omega

/-- 5. **Regime 2 is attained** (all `PUSH31`, `6,100,805` dead-end branches). -/
theorem yp_tight : 11 * cost2 0 0 0 0 0 0 6100805 0 0 0 200000000 0 ≤ 66779086680 ∧
    66779086680 - 11 * cost2 0 0 0 0 0 0 6100805 0 0 0 200000000 0 < 11 * 405 ∧
    7 * 0 + 22 * 6100805 ≤ inputBytes := by decide

/-- 6. **Regime 1: `123×` at 200M, `80×` at 380M.** -/
theorem inline_slopes : inline200 = 7287261989 ∧ 123 * inline200 < yukon ∧
    yukon < 124 * inline200 ∧ inline380 = 11167773630 ∧ 80 * inline380 < yukon ∧
    yukon < 81 * inline380 := by decide

/-- 7. **Regime 2: `136×` at 200M, `91×` at 380M.** -/
theorem yp_slopes : yp200 = 6575582388 ∧ 136 * yp200 < yukon ∧ yukon < 137 * yp200 ∧
    yp380 = 9815582388 ∧ 91 * yp380 < yukon ∧ yukon < 92 * yp380 := by decide

/-- 8. Dropping `hb` costs `622,215,414` ticks at 380M (`85× → 80×`); at 200M nothing. -/
theorem hb_gap : inline380 - 10545558216 = 622215414 ∧ inline200 = 7287261989 := by decide

end InitECandidate.Solver.GuestInlineChildMptDualAndOneHundredThirtySixXMaster
