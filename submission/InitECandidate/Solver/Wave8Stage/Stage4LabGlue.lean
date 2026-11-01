import InitECandidate.Solver.SelfContainedStageBounds

set_option autoImplicit false

namespace InitECandidate.Solver.Wave8Stage.Stage4

open Flapjack Flapjack.Misc Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabToTarget.FilterSkip

/-- Removing alignment wrappers preserves the result at the same clock. -/
theorem lab_align_result {width : Nat} [NeZero width] {C F : Type}
    (hw : goodDimindex width) (t : LabSem.State width C F) (k : Nat) :
    (LabSem.evaluate { alignDm (alignSdm t) with clock := k }).1 =
      (LabSem.evaluate { t with clock := k }).1 := by
  have hdm := evaluateAlignDM hw { alignSdm t with clock := k }
  have hsdm := evaluateAlignSDM hw { t with clock := k }
  cases ht : LabSem.evaluate { t with clock := k } with
  | mk r post =>
    simp only [ht] at hsdm
    change LabSem.evaluate { alignSdm t with clock := k } = (r, alignSdm post) at hsdm
    simp only [hsdm] at hdm
    have hresult := congrArg Prod.fst hdm
    exact hresult

/-- The filtered state needs no more clock than an aligned unfiltered run. -/
theorem lab_filter_align_not_timeOut {width : Nat} [NeZero width] {C F : Type}
    (hw : goodDimindex width) (s t : LabSem.State width C F)
    (hr : LabFilter.Proofs.stateRel s t) (k : Nat)
    (hnt : (LabSem.evaluate { alignDm (alignSdm t) with clock := k }).1 ≠ .timeOut) :
    (LabSem.evaluate { s with clock := k }).1 ≠ .timeOut := by
  rw [lab_align_result hw t k] at hnt
  have hrc : LabFilter.Proofs.stateRel { s with clock := k } { t with clock := k } := by
    rcases hr with ⟨⟨compile, hs, hcomp⟩, hf⟩
    subst s
    exact ⟨⟨compile, rfl, hcomp⟩, hf⟩
  obtain ⟨extra, post, he, _⟩ := LabFilter.Proofs.filterCorrect
    { s with clock := k } { t with clock := k }
    (LabSem.evaluate { s with clock := k }).1
    (LabSem.evaluate { s with clock := k }).2 ⟨rfl, hrc, hrc.2⟩
  have hadd := evaluateAddClock { t with clock := k }
    (LabSem.evaluate { t with clock := k }).1
    (LabSem.evaluate { t with clock := k }).2 extra ⟨rfl, hnt⟩
  rw [hadd] at he
  exact (congrArg Prod.fst he) ▸ hnt

#print axioms lab_align_result
#print axioms lab_filter_align_not_timeOut

end InitECandidate.Solver.Wave8Stage.Stage4
