import InitECandidate.Solver.Wave8Stage.WordCostLabelSupport

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.WordCostCheck
open Flapjack WordCostEffects WordCostCertificates WordCostLabelSupport WordCostAnalysis

def leBudget : Budget → Budget → Bool
  | none,_ => true
  | some _,none => false
  | some first,some second => decide (first ≤ second)

theorem leBudget_sound (a b : Budget) (checked : leBudget a b = true) :
    ∀ cost, Covers a cost → Covers b cost := by
  intro cost covered
  cases a with
  | none => exact (covers_none cost covered).elim
  | some first =>
    cases b with
    | none => cases checked
    | some second =>
      have h : first ≤ second := by simpa only [leBudget,decide_eq_true_eq] using checked
      have hcost := (covers_some first cost).mp covered
      exact (covers_some second cost).mpr (by omega)

def checkWithin (bound : Nat) (effects expected : Effects) : Bool :=
  ([Exit.fall,.returned,.raised,.final,.invalid].all
    (fun exit => leBudget (effects exit) (expected exit))) &&
  ((List.range (bound+1)).all (fun label =>
    leBudget (effects (.breakTo label)) (expected (.breakTo label)) &&
    leBudget (effects (.continueTo label)) (expected (.continueTo label))))

/-- Finite checking covers all exit classes, including arbitrarily large
labels excluded by the proved support bound. -/
theorem checkWithin_sound (bound : Nat) (effects expected : Effects)
    (support : HighNone bound effects) (checked : checkWithin bound effects expected = true) :
    Subeffects effects expected := by
  have parts := checked
  simp only [checkWithin, Bool.and_eq_true] at parts
  have ordinary : ∀ exit ∈ [Exit.fall,.returned,.raised,.final,.invalid],
      leBudget (effects exit) (expected exit) = true := by
    exact List.all_eq_true.mp parts.1
  have labels : ∀ label ∈ List.range (bound+1),
      leBudget (effects (.breakTo label)) (expected (.breakTo label)) = true ∧
      leBudget (effects (.continueTo label)) (expected (.continueTo label)) = true := by
    intro label member
    simpa only [Bool.and_eq_true] using (List.all_eq_true.mp parts.2 label member)
  intro exit cost covered
  cases exit with
  | fall | returned | raised | final | invalid =>
    exact leBudget_sound _ _ (ordinary _ (by simp)) cost covered
  | breakTo label =>
    by_cases high : bound < label
    · rw [(support label high).1] at covered
      exact (covers_none cost covered).elim
    · exact leBudget_sound _ _ (labels label (by simp; omega)).1 cost covered
  | continueTo label =>
    by_cases high : bound < label
    · rw [(support label high).2] at covered
      exact (covers_none cost covered).elim
    · exact leBudget_sound _ _ (labels label (by simp; omega)).2 cost covered

def checkProgram {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (fuel : Nat) (p : WordLangProgHOL (BitVec width)) (expected : Effects) : Bool :=
  match analyze defs terminal fuel p with
  | none => false
  | some effects => checkWithin (labelBound p) effects expected

/-- A successful finite Boolean program check provides the exact syntactic
certificate and summary inclusion required by global cost soundness. -/
theorem checkProgram_sound {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (noLabels : ∀ dest label, defs dest (.breakTo label) = none ∧ defs dest (.continueTo label) = none)
    (fuel : Nat) (p : WordLangProgHOL (BitVec width)) (expected : Effects)
    (checked : checkProgram defs terminal fuel p expected = true) :
    ∃ effects, Derives defs terminal p effects ∧ Subeffects effects expected := by
  unfold checkProgram at checked
  cases run : analyze defs terminal fuel p with
  | none => simp [run] at checked
  | some effects =>
    have derived := analyze_derives defs terminal fuel p effects run
    exact ⟨effects,derived,checkWithin_sound (labelBound p) effects expected
      (derives_high defs terminal noLabels p effects derived) (by simpa only [run] using checked)⟩

end InitECandidate.Solver.Wave8Stage.WordCostCheck
