import InitECandidate.Solver.Wave8Stage.Stage4RuntimeEval

set_option autoImplicit false
namespace InitECandidate.Solver.Wave8Stage.RuntimeLabels
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
variable {width : Nat} [NeZero width]

/-- Lookup agreement and preservation of the global label-membership check.
The latter matters because locCheckExact can find a label in any section. -/
structure CodeAgreement (bad : Nat) (source target : Spt (HolProg width)) : Prop where
  lookup : ∀ n, n ≠ bad → sptLookup n target = sptLookup n source
  labels : ∀ n k, n ≠ bad →
    (StackSem.locCheckExact target (n, k) ↔ StackSem.locCheckExact source (n, k))

/-- Sufficient local condition for deleting/replacing the excluded section:
its internal labels, if any, all belong to the excluded section. -/
theorem codeAgreement_of_local_labels {bad : Nat} (source target : Spt (HolProg width))
    (hc : ∀ n, n ≠ bad → sptLookup n target = sptLookup n source)
    (hsource : ∀ p, sptLookup bad source = some p →
      ∀ n k, StackSem.getLabelsExact p (n, k) → n = bad)
    (htarget : ∀ p, sptLookup bad target = some p →
      ∀ n k, StackSem.getLabelsExact p (n, k) → n = bad) :
    CodeAgreement bad source target := by
  refine ⟨hc, ?_⟩
  intro n k hn
  have hm : sptMem n target ↔ sptMem n source := by
    simp only [sptMem, sptDomain, hc n hn]
  constructor
  · rintro (⟨hk, hd⟩ | ⟨label, p, hp, hl⟩)
    · exact Or.inl ⟨hk, hm.mp hd⟩
    · by_cases he : label = bad
      · subst label
        exact False.elim (hn (htarget p hp n k hl))
      · exact Or.inr ⟨label, p, (hc label he).symm.trans hp, hl⟩
  · rintro (⟨hk, hd⟩ | ⟨label, p, hp, hl⟩)
    · exact Or.inl ⟨hk, hm.mpr hd⟩
    · by_cases he : label = bad
      · subst label
        exact False.elim (hn (hsource p hp n k hl))
      · exact Or.inr ⟨label, p, (hc label he).trans hp, hl⟩

/-- Remove exactly one section, preserving the order of the remaining entries. -/
def withoutSection (bad : Nat) (entries : List (Nat × HolProg width)) :=
  entries.filter (fun e => e.1 != bad)

theorem withoutSection_lookup (bad n : Nat) (entries : List (Nat × HolProg width))
    (hn : n ≠ bad) :
    sptLookup n (sptFromAList (withoutSection bad entries)) = sptLookup n (sptFromAList entries) := by
  rw [sptLookup_sptFromAList, sptLookup_sptFromAList]
  induction entries with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨k, p⟩ := e
    by_cases hk : k = bad
    · subst k
      simp only [withoutSection, List.filter, bne_self_eq_false] at ih ⊢
      rw [ih]
      simp [sptAListLookup, hn]
    · have hk' : (k != bad) = true := by simp [hk]
      simp only [withoutSection, List.filter, hk'] at ih ⊢
      simp only [sptAListLookup]
      rw [ih]

theorem withoutSection_absent (bad : Nat) (entries : List (Nat × HolProg width)) :
    sptLookup bad (sptFromAList (withoutSection bad entries)) = none := by
  rw [sptLookup_sptFromAList]
  induction entries with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨k, p⟩ := e
    by_cases hk : k = bad
    · subst k
      simpa only [withoutSection, List.filter, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] using ih
    · have hk' : (k != bad) = true := by simp [hk]
      simp only [withoutSection, List.filter, hk'] at ih ⊢
      simp only [sptAListLookup, Ne.symm hk, ↓reduceIte]
      exact ih

theorem withoutSection_agreement (bad : Nat) (entries : List (Nat × HolProg width))
    (hlabels : ∀ p, sptLookup bad (sptFromAList entries) = some p →
      ∀ n k, StackSem.getLabelsExact p (n, k) → n = bad) :
    CodeAgreement bad (sptFromAList entries) (sptFromAList (withoutSection bad entries)) := by
  apply codeAgreement_of_local_labels _ _ (fun n hn => withoutSection_lookup bad n entries hn) hlabels
  intro p hp
  rw [withoutSection_absent] at hp
  cases hp

end InitECandidate.Solver.Wave8Stage.RuntimeLabels
