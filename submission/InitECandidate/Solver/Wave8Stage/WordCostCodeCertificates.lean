import InitECandidate.Solver.Wave8Stage.WordCostEntryCertificate
import InitECandidate.Solver.Wave8Stage.WordCostColourCertificates
import InitECandidate.Solver.Wave8Stage.WordCostCheck

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.WordCostCodeCertificates
open Flapjack WordCostEffects WordCostCertificates WordCostEntryCertificate
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm

/-- Every actual direct or indirect lookup receives a certificate for its
resolved function. The indirect summary must cover all named summaries. -/
theorem codeCertified_of_members {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (certificates : ∀ entry ∈ programs, ∃ effects,
      Derives defs terminal entry.2.2 effects ∧ Subeffects effects (defs (some entry.1)))
    (indirect : ∀ name, Subeffects (defs (some name)) (defs none)) :
    CodeCertified defs terminal (sptFromAList programs) := by
  intro dest args sizes values body frame found
  cases dest with
  | some name =>
    simp only [wordSemFindCode] at found
    cases lookup : sptLookup name (sptFromAList programs) with
    | none => simp [lookup] at found
    | some entry =>
      rcases entry with ⟨arity,program⟩
      simp only [lookup] at found
      split at found
      · cases found
        rw [sptLookup_sptFromAList] at lookup
        exact certificates _ (sptAListLookup_mem name programs (arity,body) lookup)
      · cases found
  | none =>
    simp only [wordSemFindCode] at found
    split at found
    · cases found
    · split at found
      · rename_i name last
        cases lookup : sptLookup name (sptFromAList programs) with
        | none => simp [lookup] at found
        | some entry =>
          rcases entry with ⟨arity,program⟩
          simp only [lookup] at found
          split at found
          · cases found
            rw [sptLookup_sptFromAList] at lookup
            obtain ⟨effects,derived,le⟩ := certificates _
              (sptAListLookup_mem name programs (arity,body) lookup)
            exact ⟨effects,derived,fun exit cost h => indirect name exit cost (le exit cost h)⟩
          · cases found
      · cases found

private theorem mem_zip_left {α β : Type} (a : α) (b : β)
    (as : List α) (bs : List β) (member : (a,b) ∈ as.zip bs) : a ∈ as := by
  induction as generalizing bs with
  | nil => simp at member
  | cons first rest ih =>
    cases bs with
    | nil => simp at member
    | cons next bs =>
      simp only [List.zip_cons_cons,List.mem_cons,Prod.mk.injEq] at member
      rcases member with ⟨rfl,rfl⟩ | member
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih bs member)

/-- Prefix certificates supply certificates for every full compiler output,
including arbitrary successful or fallback register allocation. -/
theorem compile_members {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (wc : WordToWord.Config) (ac : AsmConfigExact width)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (noMt : ∀ entry ∈ programs, noMtSubprogsHOL entry.2.2 = true)
    (prefixes : ∀ entry ∈ programs, ∃ effects,
      Derives defs terminal
        (WordCostCompilerControl.preAllocation ac ac.twoRegArith entry.2.1 entry.2.2) effects ∧
      Subeffects effects (defs (some entry.1))) :
    ∀ entry ∈ (WordToWord.compile wc ac programs).2, ∃ effects,
      Derives defs terminal entry.2.2 effects ∧ Subeffects effects (defs (some entry.1)) := by
  intro entry member
  change entry ∈ (programs.zip (WordToWord.nextNOracle programs.length wc.colOracle).1).map
    (WordToWord.fullCompileSingle ac.twoRegArith
      (ac.regCount - (5+ac.avoidRegs.length)) wc.regAlg ac) at member
  obtain ⟨⟨original,colour⟩,zipped,rfl⟩ := List.mem_map.mp member
  have sourceMember := mem_zip_left original colour _ _ zipped
  obtain ⟨effects,derived,le⟩ := prefixes original sourceMember
  refine ⟨effects,?_,le⟩
  exact WordCostColourCertificates.fullCompileSingle_derives defs terminal ac ac.twoRegArith
    _ wc.regAlg original.1 original.2.1 original.2.2 colour effects
    (noMt original sourceMember) derived

/-- A finite successful prefix check for each input function is sufficient
for the semantic code-certificate interface of the actual complete compiler. -/
theorem compile_codeCertified {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (wc : WordToWord.Config) (ac : AsmConfigExact width)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (fuel : Nat)
    (noLabels : ∀ dest label, defs dest (.breakTo label) = none ∧ defs dest (.continueTo label) = none)
    (indirect : ∀ name, Subeffects (defs (some name)) (defs none))
    (noMt : ∀ entry ∈ programs, noMtSubprogsHOL entry.2.2 = true)
    (checked : ∀ entry ∈ programs, WordCostCheck.checkProgram defs terminal fuel
      (WordCostCompilerControl.preAllocation ac ac.twoRegArith entry.2.1 entry.2.2)
      (defs (some entry.1)) = true) :
    CodeCertified defs terminal (sptFromAList (WordToWord.compile wc ac programs).2) := by
  apply codeCertified_of_members defs terminal _
    (compile_members defs terminal wc ac programs noMt ?_) indirect
  intro entry member
  exact WordCostCheck.checkProgram_sound defs terminal noLabels fuel _ _ (checked entry member)

end InitECandidate.Solver.Wave8Stage.WordCostCodeCertificates
