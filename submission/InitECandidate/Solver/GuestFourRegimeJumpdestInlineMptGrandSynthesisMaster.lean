import InitECandidate.Solver.GuestInlineChildMptDualAndOneHundredThirtySixXMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestFourRegimeJumpdestInlineMptGrandSynthesisMaster`

Four-regime matrix for `main` (`blockFixed = 370,538,614`, `I = 134,217,712`), one gas budget
`12000 T + 2400 A + 2105 K + 1900 L + P (+ 126 C) ≤ G`.

* **A** current Guest: `compute_jumpdests` uncached (`67,884` ticks per `≥ 126`-gas call,
  `66,562` per tx), inline children free, no `hb`.
* **B** + jumpdest cache, no `hb` (current `_resolve_step`).
* **C** + jumpdest cache + `hb : B ≤ N₁₇ + K + A` (valid only if every rehashed branch is a
  witness item, i.e. under the inline-child rule; kept for comparison with the pushed chain).
* **D** + jumpdest cache + Yellow-Paper rule (inline child `< 32` bytes in `_resolve_step`).

Only A is unconditional for the unmodified Guest. B needs the jumpdest cache; D needs both fixes.
-/

namespace InitECandidate.Solver.GuestFourRegimeJumpdestInlineMptGrandSynthesisMaster

open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

def inputBytes : Nat := 134217712
def blockFixed : Nat := 370538614

def costC (A K L B E n2 n17 md ms P T : Nat) : Nat :=
  3473 * A + 5274 * K + 3124 * L + 633 * B + 439 * E + 127 * n2 + 405 * n17 + 43 * md +
    79 * ms + 18 * P + 42382 * T
def costU (A K L B E n2 n17 md ms P C T : Nat) : Nat :=
  costC A K L B E n2 n17 md ms P T + 67884 * C + 66562 * T
def costD (A K L B E n2 d r md ms P T : Nat) : Nat :=
  costC A K L B E n2 (d + r) md ms P T

def mainA200 : Nat := blockFixed + (25461560820280 + 230) / 231
def mainA380 : Nat := blockFixed + (47863280820280 + 230) / 231
def mainB200 : Nat := blockFixed + inputBytes + (3058910053880 + 450) / 451
def mainB380 : Nat := blockFixed + inputBytes + (4809020803880 + 450) / 451
def mainC200 : Nat := blockFixed + inputBytes + (3058910053880 + 450) / 451
def mainC380 : Nat := blockFixed + inputBytes + (118511584702912 + 11802) / 11803
def mainD200 : Nat := blockFixed + inputBytes + (66779086680 + 10) / 11
def mainD380 : Nat := blockFixed + inputBytes + (102419086680 + 10) / 11

/-- 1. **Regime A** (unmodified Guest, no `hb`). -/
theorem regimeA (A K L B E n2 n17 md ms P C T G : Nat) (hG : G = 200000000 ∨ G = 380000000)
    (hg : 12000 * T + 2400 * A + 2105 * K + 1900 * L + P + 126 * C ≤ G)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    (G = 200000000 → 231 * costU A K L B E n2 n17 md ms P C T ≤ 25461560820280) ∧
    (G = 380000000 → 231 * costU A K L B E n2 n17 md ms P C T ≤ 47863280820280) := by
  unfold costU costC inputBytes at *; constructor <;> intro h <;> subst h <;> omega

/-- 2. **Regime B** (cache, no `hb`). -/
theorem regimeB (A K L B E n2 n17 md ms P T : Nat)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    (12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 200000000 →
      451 * costC A K L B E n2 n17 md ms P T ≤ 3058910053880) ∧
    (12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 380000000 →
      451 * costC A K L B E n2 n17 md ms P T ≤ 4809020803880) := by
  unfold costC inputBytes at *; constructor <;> intro hg <;> omega

/-- 3. **Regime C** (cache + `hb`). -/
theorem regimeC (A K L B E n2 n17 md ms P T : Nat)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    (12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 200000000 →
      451 * costC A K L B E n2 n17 md ms P T ≤ 3058910053880) ∧
    (12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 380000000 →
      11803 * costC A K L B E n2 n17 md ms P T ≤ 118511584702912) := by
  unfold costC inputBytes at *; constructor <;> intro hg <;> omega

/-- 4. **Regime D** (cache + Yellow-Paper inline rule). -/
theorem regimeD (A K L B E n2 d r md ms P T : Nat)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ r + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * d + 54 * r + 4 * md + 5 * ms ≤ inputBytes + 32 * (A + K)) :
    (12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 200000000 →
      11 * costD A K L B E n2 d r md ms P T ≤ 66779086680) ∧
    (12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 380000000 →
      11 * costD A K L B E n2 d r md ms P T ≤ 102419086680) := by
  unfold costD costC inputBytes at *; constructor <;> intro hg <;> omega

/-- 5. **Witnesses**: A and D attained within one unit of their rational optimum. -/
theorem witnesses :
    25461560820280 - 231 * costU 0 0 0 0 0 0 6100805 0 0 0 1587302 0 < 231 * 67884 ∧
    66779086680 - 11 * costD 0 0 0 0 0 0 6100805 0 0 0 200000000 0 < 11 * 405 := by decide

/-- 6. **Matrix values.** -/
theorem matrix : mainA200 = 110593745629 ∧ mainA380 = 207570888486 ∧
    mainB200 = 7287261989 ∧ mainB380 = 11167773630 ∧ mainC200 = 7287261989 ∧
    mainC380 = 10545558216 ∧ mainD200 = 6575582388 ∧ mainD380 = 9815582388 := by decide

/-- 7. **Yukon multiples** (`k` passes, `k+1` fails): A 8/4, B 123/80, C 123/85, D 136/91. -/
theorem multiples :
    8 * mainA200 < yukon ∧ yukon < 9 * mainA200 ∧ 4 * mainA380 < yukon ∧ yukon < 5 * mainA380 ∧
    123 * mainB200 < yukon ∧ yukon < 124 * mainB200 ∧ 80 * mainB380 < yukon ∧
    yukon < 81 * mainB380 ∧ 123 * mainC200 < yukon ∧ yukon < 124 * mainC200 ∧
    85 * mainC380 < yukon ∧ yukon < 86 * mainC380 ∧ 136 * mainD200 < yukon ∧
    yukon < 137 * mainD200 ∧ 91 * mainD380 < yukon ∧ yukon < 92 * mainD380 := by decide

/-- 8. **Gaps**: `hb` gap at 380M, D under 7·10⁹ / 10¹⁰, B and C not. -/
theorem gaps : mainB380 - mainC380 = 622215414 ∧ mainD200 < 7000000000 ∧
    mainD380 < 10000000000 ∧ 7000000000 < mainB200 ∧ 7000000000 < mainC200 := by decide

end InitECandidate.Solver.GuestFourRegimeJumpdestInlineMptGrandSynthesisMaster
