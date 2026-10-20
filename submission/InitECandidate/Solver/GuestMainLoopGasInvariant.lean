import InitECandidate.Solver.SourceWitnessClockBound

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-!
# `InitECandidate.Solver.GuestMainLoopGasInvariant`

Abstract model of the clock of `"main"` in `Guest/guest.pp.pnk` (line ~15681):
`k_main = k_prologue + k_tx_loop + k_epilogue`.

* Prologue (`*_init`, `decode_stateless_input`): `k_prologue ≤ Guest.maxInputBytes`
  (`134,217,712`, not 4,194,304: see `Guest/Model.lean`).
* Opcode loop: a list of iterations; iteration `i` charges `gas_i ≥ 1`, runs `ticks_i`
  PanSem ticks and creates `keys_i` fresh table keys. Exits (`OutOfGas`/`Halt`/`Revert`)
  are charged to the epilogue.
* Epilogue (state root / trie hash): `≤ epiPerKey` ticks per created key plus a constant
  `epiBase`, both charged against `initTicks` slack or amortized into the gas term.

Interpreter invariant (`AmortizedOk`): `ticks_i + epiPerKey * keys_i ≤ 219 * gas_i`
(`219 = guestCallGraphMaxDepth + 200 + 1`, the per-gas-unit slope of `guestSourceClockBudget`).
Under it the whole run fits `guestSourceClockBudget totalGas 18 200 (k_pro + epiBase)`,
which discharges `hbudget` of `kMin_le_maxGuestSourceClock_of_budget`.

The invariant itself is NOT derived from `PanSem` on the 825 Guest functions: it is
the remaining semantic obligation, now localised to a per-iteration inequality.
-/

namespace InitECandidate.Solver.GuestMainLoopGasInvariant

open InitECandidate.Solver
open InitECandidate.Solver.HtabLoadFactorBound
open InitECandidate.Solver.GuestGasAndHtabBound
open InitECandidate.Solver.SourceWitnessClockBound

/-- Per-gas-unit tick slope of `guestSourceClockBudget _ 18 200 _`. -/
def slope : Nat := 219

/-- One opcode-loop iteration. -/
structure Iter where
  gas : Nat
  ticks : Nat
  keys : Nat

def totalGas (l : List Iter) : Nat := (l.map Iter.gas).sum
def totalTicks (l : List Iter) : Nat := (l.map Iter.ticks).sum
def totalKeys (l : List Iter) : Nat := (l.map Iter.keys).sum

/-- Every iteration charges at least one gas unit. -/
def GasPositive (l : List Iter) : Prop := ∀ it ∈ l, 1 ≤ it.gas

/-- Amortized interpreter invariant. -/
def AmortizedOk (epiPerKey : Nat) (l : List Iter) : Prop :=
  ∀ it ∈ l, it.ticks + epiPerKey * it.keys ≤ slope * it.gas

/-- Clock decomposition of `"main"`. -/
def mainClock (kPro epiBase epiPerKey : Nat) (l : List Iter) : Nat :=
  kPro + totalTicks l + (epiBase + epiPerKey * totalKeys l)

/-- 1. Iteration count is bounded by consumed gas. -/
theorem length_le_totalGas (l : List Iter) (h : GasPositive l) : l.length ≤ totalGas l := by
  induction l with
  | nil => simp [totalGas]
  | cons a l ih =>
    have ha := h a (by simp)
    have hl := ih (fun it hit => h it (by simp [hit]))
    simp [totalGas] at hl ⊢; omega

/-- 2. Amortized loop + per-key epilogue ticks are bounded by `219 · gas`. -/
theorem loop_and_epi_le (epiPerKey : Nat) (l : List Iter) (h : AmortizedOk epiPerKey l) :
    totalTicks l + epiPerKey * totalKeys l ≤ slope * totalGas l := by
  induction l with
  | nil => simp [totalTicks, totalKeys, totalGas]
  | cons a l ih =>
    have ha := h a (by simp)
    have hl := ih (fun it hit => h it (by simp [hit]))
    simp only [totalTicks, totalKeys, totalGas, List.map_cons, List.sum_cons] at hl ⊢
    rw [Nat.mul_add, Nat.mul_add]; omega

/-- 3. Fresh keys are bounded by `105,263` when each costs `1900` gas within 200M. -/
theorem totalKeys_le (l : List Iter) (hk : minGasPerKey * totalKeys l ≤ totalGas l)
    (hg : totalGas l ≤ maxBlockGasLimit) : totalKeys l ≤ maxFreshHtabKeys := by
  have : minGasPerKey * totalKeys l ≤ blockGasLimit := by
    unfold blockGasLimit; rw [maxBlockGasLimit_eq] at hg; omega
  exact keys_le_200M _ this

/-- 4. `guestSourceClockBudget g 18 200 i = i + 219 g`. -/
theorem budget_eq (g i : Nat) :
    guestSourceClockBudget g guestCallGraphMaxDepth 200 i = i + slope * g := by
  unfold guestSourceClockBudget loopClockBudget guestCallGraphMaxDepth slope; ring_nf

/-- 5. Decomposition: the `"main"` clock fits the gas budget. -/
theorem mainClock_le_budget (kPro epiBase epiPerKey : Nat) (l : List Iter)
    (h : AmortizedOk epiPerKey l) :
    mainClock kPro epiBase epiPerKey l ≤
      guestSourceClockBudget (totalGas l) guestCallGraphMaxDepth 200 (kPro + epiBase) := by
  rw [budget_eq]; unfold mainClock
  have := loop_and_epi_le epiPerKey l h; omega

/-- 6. The budget is ≤ `43,934,217,712` under gas ≤ 200M and `kPro + epiBase ≤ maxInputBytes`. -/
theorem budget_le_max (kPro epiBase : Nat) (l : List Iter)
    (hg : totalGas l ≤ maxBlockGasLimit) (hi : kPro + epiBase ≤ Guest.maxInputBytes) :
    guestSourceClockBudget (totalGas l) guestCallGraphMaxDepth 200 (kPro + epiBase) ≤
      maxGuestSourceClock :=
  (guestSourceClockBudget_le_max _ _ _ _ hg (Nat.le_refl _) (Nat.le_refl _) hi).1

/-- 7. Main result: a non-timeout run at `mainClock` discharges `hbudget`, hence `kMin ≤ 43,934,217,712`. -/
theorem hbudget_of_interpreter_invariant
    (s : Flapjack.PanSemStateFiniteExact 64 Guest.HostMemory) (hex : ∃ k, NotTO s k)
    (kPro epiBase epiPerKey : Nat) (l : List Iter)
    (hamort : AmortizedOk epiPerKey l)
    (hg : totalGas l ≤ maxBlockGasLimit) (hi : kPro + epiBase ≤ Guest.maxInputBytes)
    (hrun : NotTO s (mainClock kPro epiBase epiPerKey l)) :
    NotTO s (guestSourceClockBudget (totalGas l) guestCallGraphMaxDepth 200 (kPro + epiBase)) ∧
      kMin s hex ≤ maxGuestSourceClock := by
  have hb := notTO_mono s hrun (mainClock_le_budget kPro epiBase epiPerKey l hamort)
  exact ⟨hb, (kMin_le_maxGuestSourceClock_of_budget s hex _ _ _ _ hg (Nat.le_refl _)
    (by decide) hi hb).2⟩

/-- 8. Worst-case probe cost fits per-key amortization: one full probe of a
`262,144`-slot table per fresh key costs ≤ `219 · 1900 = 416,100` ticks of slack. -/
theorem probe_fits_key_slack : 262144 ≤ slope * minGasPerKey ∧ slope * minGasPerKey = 416100 := by
  decide

/-- 9. A fully saturated loop (each iteration exactly `219 · gas` ticks, gas sum 200M,
`kPro + epiBase = maxInputBytes`) reaches `maxGuestSourceClock` exactly: the bound is tight. -/
theorem tight_at_max :
    mainClock Guest.maxInputBytes 0 0 [⟨200000000, 219 * 200000000, 0⟩] = maxGuestSourceClock ∧
      AmortizedOk 0 [⟨200000000, 219 * 200000000, 0⟩] ∧
      totalGas [⟨200000000, 219 * 200000000, 0⟩] ≤ maxBlockGasLimit := by
  refine ⟨by decide, ?_, by decide⟩
  intro it hit; simp at hit; subst hit; decide

/-- 10. Exceeding the slope by one tick in one iteration breaks the budget at saturation. -/
theorem slope_tight :
    ¬ mainClock Guest.maxInputBytes 0 0 [⟨200000000, 219 * 200000000 + 1, 0⟩] ≤
      maxGuestSourceClock := by decide

end InitECandidate.Solver.GuestMainLoopGasInvariant
