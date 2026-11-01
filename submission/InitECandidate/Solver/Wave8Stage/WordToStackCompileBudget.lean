import InitECandidate.Solver.SelfContainedStageBounds
import InitECandidate.Solver.Wave8Stage.WordToStackStaticBudget

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.WordToStackCompileBudget
open Classical Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackLang Flapjack.Pancake.Proofs.PanToTarget

private theorem sptAListLookup_eq_local {α : Type} (key : Nat) :
    ∀ entries : List (Nat × α), sptAListLookup key entries = panPropsALookupEq key entries
  | [] => rfl
  | (other, value) :: entries => by
      simp only [sptAListLookup, panPropsALookupEq, sptAListLookup_eq_local key entries]
      by_cases h : key = other
      · subst h; simp
      · simp [h, Ne.symm h]

private theorem mem_of_lookup_local {α : Type} {key : Nat} {value : α} :
    ∀ {entries : List (Nat × α)}, panPropsALookupEq key entries = some value →
      (key, value) ∈ entries
  | [], h => by simp [panPropsALookupEq] at h
  | (other, v) :: entries, h => by
      simp only [panPropsALookupEq] at h
      by_cases ho : other = key
      · subst ho
        simp only [decide_true, if_true, Option.some.injEq] at h
        subst h
        exact List.mem_cons_self
      · simp only [ho, decide_false, Bool.false_eq_true, if_false] at h
        exact List.mem_cons_of_mem _ (mem_of_lookup_local h)

/-- All code, frame and bitmap relations follow from the compiler output
and the complete original initialization contract. -/
theorem compile_stateRel {width : Nat} [NeZero width] {C F : Type}
    (asmConf : AsmConfigExact width) (code : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (t : StackSemStateFiniteExact width C F) (k : Nat)
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (codeEq : t.code = sptFromAList (WordToStack.Native.compileNative asmConf false code).2.2.2)
    (kEq : k = asmConf.regCount - (5 + asmConf.avoidRegs.length))
    (ok : WordToStackProofs.InitializationStateRel.initStateOk asmConf k t coracle)
    (noRaise : panPropsALookupEq raiseStubLocation code = none)
    (noStore : panPropsALookupEq storeConstsStubLocation code = none)
    (bitmapsPrefix : (WordToStack.Native.compileNative asmConf false code).1 <+: t.bitmaps)
    (conventions : ∀ entry ∈ code, flatExpConventions entry.2.2 = true ∧
      postAllocConventionsHOL (asmConf.regCount - (5 + asmConf.avoidRegs.length))
        entry.2.2 = true) :
    WordToStackProofs.stateRel asmConf k 0 0
      (WordToStack.Native.Initialization.makeInit asmConf k t (sptFromAList code) coracle)
      t [] 0 := by
  subst kEq
  rcases compiled : WordToStack.Native.compileWordToStackNative asmConf false
      (asmConf.regCount - (5 + asmConf.avoidRegs.length)) code (.list [4], 1) with
    ⟨bodies, frames, output, nextIndex⟩
  simp only [WordToStack.Native.compileNative, Bool.false_eq_true, if_false, compiled]
    at codeEq bitmapsPrefix
  have keys := Flapjack.WordToStackProofs.mapFstCompileWordToStack asmConf false _ code (.list [4], 1)
    bodies (frames, (output, nextIndex)) compiled
  have stubsDistinct : raiseStubLocation ≠ storeConstsStubLocation := by
    simp [raiseStubLocation, storeConstsStubLocation, wordNumStubs]
  apply WordToStackProofs.InitializationStateRel.initStateOkImpliesStateRel
  refine ⟨?_, ?_, ?_, ?_, ok⟩
  · rw [codeEq, sptLookup_sptFromAList, sptAListLookup_eq_local]
    simp [panPropsALookupEq]
  · rw [codeEq, sptLookup_sptFromAList, sptAListLookup_eq_local]
    simp [panPropsALookupEq, stubsDistinct]
  · intro n wordProg argumentCount lookup
    rw [sptLookup_sptFromAList, sptAListLookup_eq_local] at lookup
    have member := mem_of_lookup_local lookup
    obtain ⟨flat, allocated⟩ := conventions _ member
    obtain ⟨bs, i, bs2, i2, frame, body, compileRun, b1, b2, b3, bodyLookup⟩ :=
      WordToStack.Native.compileWordToStackImpALookup asmConf false _ code (.list [4]) 1
        bodies frames output nextIndex n argumentCount wordProg t.bitmaps compiled lookup
        (by simp [appListAppend, appendAux]) (by simp [appListAppend, appendAux])
        (by simpa [appListAppend, appendAux] using bitmapsPrefix)
    refine ⟨allocated, flat, bs, i, bs2, i2, frame, body, compileRun, b1, b2, b3, ?_⟩
    have notRaise : n ≠ raiseStubLocation := by
      rintro rfl
      rw [noRaise] at lookup
      cases lookup
    have notStore : n ≠ storeConstsStubLocation := by
      rintro rfl
      rw [noStore] at lookup
      cases lookup
    rw [codeEq, sptLookup_sptFromAList, sptAListLookup_eq_local]
    simp [panPropsALookupEq, Ne.symm notRaise, Ne.symm notStore, bodyLookup]
  · rw [codeEq, sptDomainFromAList, sptDomainFromAList]
    funext x
    simp only [List.map_cons, List.mem_cons, keys]

#print axioms compile_stateRel

/-- Compiler-level static affine native entry budget. -/
theorem compile_notTimeOutOfStaticBudget {width : Nat} [NeZero width] {C F : Type}
    (asmConf : AsmConfigExact width) (code : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (t : StackSemStateFiniteExact width C F) (k : Nat)
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (start clk : Nat)
    (res : Option (WordSemResult width))
    (s1 : WordSemStateFiniteExact width (Nat × C) F)
    (codeEq : t.code = sptFromAList (WordToStack.Native.compileNative asmConf false code).2.2.2)
    (kEq : k = asmConf.regCount - (5 + asmConf.avoidRegs.length))
    (ok : WordToStackProofs.InitializationStateRel.initStateOk asmConf k t coracle)
    (noRaise : panPropsALookupEq raiseStubLocation code = none)
    (noStore : panPropsALookupEq storeConstsStubLocation code = none)
    (bitmapsPrefix : (WordToStack.Native.compileNative asmConf false code).1 <+: t.bitmaps)
    (conventions : ∀ entry ∈ code, flatExpConventions entry.2.2 = true ∧
      postAllocConventionsHOL (asmConf.regCount - (5 + asmConf.avoidRegs.length))
        entry.2.2 = true)
    (hrun : WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
      { WordToStack.Native.Initialization.makeInit asmConf k t (sptFromAList code) coracle with
        clock := clk } = (res, s1))
    (hne : res ≠ some .error) (hnt : res ≠ some .timeOut)
    (noInstall : WordProps.noInstallCode (sptFromAList code)) :
    (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
      {t with clock := (WordToStackStaticBudget.codeBudget (sptFromAList code) + 1) * clk})).1 ≠
      some .timeOut := by
  have related := compile_stateRel asmConf code t k coracle codeEq kEq ok noRaise noStore
    bitmapsPrefix conventions
  apply WordToStackStaticBudget.notTimeOutOfStaticBudget asmConf start k clk _ t related noInstall
  · rw [hrun]; exact hne
  · rw [hrun]; exact hnt

#print axioms compile_notTimeOutOfStaticBudget

/-- Compiler-level precise execution-cost budget. -/
theorem compile_notTimeOutOfCostBound {width : Nat} [NeZero width] {C F : Type}
    (asmConf : AsmConfigExact width) (code : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (t : StackSemStateFiniteExact width C F) (k : Nat)
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (start clk budget : Nat)
    (codeEq : t.code = sptFromAList (WordToStack.Native.compileNative asmConf false code).2.2.2)
    (kEq : k = asmConf.regCount - (5 + asmConf.avoidRegs.length))
    (ok : WordToStackProofs.InitializationStateRel.initStateOk asmConf k t coracle)
    (noRaise : panPropsALookupEq raiseStubLocation code = none)
    (noStore : panPropsALookupEq storeConstsStubLocation code = none)
    (bitmapsPrefix : (WordToStack.Native.compileNative asmConf false code).1 <+: t.bitmaps)
    (conventions : ∀ entry ∈ code, flatExpConventions entry.2.2 = true ∧
      postAllocConventionsHOL (asmConf.regCount - (5 + asmConf.avoidRegs.length))
        entry.2.2 = true)
    (hne : (WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
      { WordToStack.Native.Initialization.makeInit asmConf k t (sptFromAList code) coracle with
        clock := clk }).1 ≠ some .error)
    (hnt : (WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
      { WordToStack.Native.Initialization.makeInit asmConf k t (sptFromAList code) coracle with
        clock := clk }).1 ≠ some .timeOut)
    (costBound : clk + WordToStackSourceCost.sourceCost (.call none (some start) [0] none)
      { WordToStack.Native.Initialization.makeInit asmConf k t (sptFromAList code) coracle with
        clock := clk } ≤ budget) :
    (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
      {t with clock := budget})).1 ≠ some .timeOut := by
  exact WordToStackCostEntry.notTimeOutOfCostBound asmConf start k clk budget _ t
    (compile_stateRel asmConf code t k coracle codeEq kEq ok noRaise noStore
      bitmapsPrefix conventions) hne hnt costBound

#print axioms compile_notTimeOutOfCostBound

/-- No-install is preserved by the actual Word-to-Word compiler, including
removal of MustTerminate blocks under its original no-MustTerminate input. -/
theorem compile_noInstall {width : Nat} [NeZero width]
    (wconf : WordToWord.Config) (ac : AsmConfigExact width)
    (source : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (col : List (Option (Spt Nat)))
    (target : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (compiled : WordToWord.compile wconf ac source = (col,target))
    (noInstall : WordProps.noInstallCode (sptFromAList source))
    (noMt : WordProps.noMtCode (sptFromAList source)) :
    WordProps.noInstallCode (sptFromAList target) := by
  have related := WordToWord.no_mt_code_rel_ext _ _
    ⟨noMt, WordToWord.code_rel_ext_word_to_word ac source wconf col target compiled⟩
  apply WordToWord.noInstallCode_of_codeRel _ _ related _ noInstall
  simp only [WordToWord.compile, Prod.mk.injEq] at compiled
  obtain ⟨_, rfl⟩ := compiled
  funext name
  simp only [sptDomain,sptLookup_sptFromAList]
  rw [WordToWord.sptAListLookup_isSome_map_fullCompileSingle _ _ _ _ source _
    (WordToWord.compile_zip_length wconf source)]

#print axioms compile_noInstall

end InitECandidate.Solver.Wave8Stage.WordToStackCompileBudget
