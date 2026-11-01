import InitECandidate.Solver.SelfContainedStageBounds

set_option autoImplicit false

namespace InitECandidate.Solver.Wave8Stage.Stage4

open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang

/-- The inverse register map in makeInit cancels the actual StackNames renaming.
The code and compilation oracle are the same concrete tables used by fullMakeInit. -/
theorem stack_names_rename_makeInit {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (f : Spt Nat)
    (code : List (Nat × HolProg width))
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (hf : Function.Bijective (StackNames.findNameSpt f))
    (hcode : s.code = sptFromAList (StackNames.compileHOL f code))
    (hor : s.compileOracle = Prod.map id (Prod.map (StackNames.compileHOL f) id) ∘ oracle) :
    StackNames.renameState s.compile f (StackNames.makeInit f (sptFromAList code) oracle s) = s := by
  have hinv : ∀ y, StackNames.findNameSpt f (holLinv (StackNames.findNameSpt f) (fun _ => True) y) = y :=
    apply_holLinv_of_surjective hf.2
  have hc : sptFromAList (StackNames.compileHOL f (sptToAList (sptFromAList code))) = s.code := by
    rw [hcode]
    refine (sptEqThm _ _ ⟨sptWfFromAList _, sptWfFromAList _⟩).mpr fun n => ?_
    rw [sptLookup_sptFromAList, StackNames.sptAListLookup_compileHOL, ← sptLookup_sptFromAList,
      sptLookup_sptFromAList_sptToAList, sptLookup_sptFromAList, sptLookup_sptFromAList,
      StackNames.sptAListLookup_compileHOL]
  classical
  have hsave : (fun y => decide (∃ x, decide (∃ z, s.ffiSaveRegs z = true ∧
      x = holLinv (StackNames.findNameSpt f) (fun _ => True) z) = true ∧
      y = StackNames.findNameSpt f x)) = s.ffiSaveRegs := by
    funext y
    by_cases hy : s.ffiSaveRegs y = true
    · rw [hy, decide_eq_true_iff]
      exact ⟨holLinv (StackNames.findNameSpt f) (fun _ => True) y,
        decide_eq_true_iff.mpr ⟨y, hy, rfl⟩, (hinv y).symm⟩
    · rw [Bool.not_eq_true] at hy
      rw [hy, decide_eq_false_iff_not]
      rintro ⟨x, hx, rfl⟩
      obtain ⟨z, hz, rfl⟩ := decide_eq_true_iff.mp hx
      rw [hinv z, hz] at hy
      exact Bool.noConfusion hy
  simp only [StackNames.renameState, StackNames.makeInit,
    StackNames.MakeInit.mapKeys_mapKeys_linv hf, hc, ← hor]
  refine Eq.trans ?_ (show { s with ffiSaveRegs := s.ffiSaveRegs } = s from rfl)
  congr 1

/-- Exact clocked entry result across the makeInit/renameState boundary. -/
theorem stack_names_makeInit_entry_result {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (f : Spt Nat)
    (code : List (Nat × HolProg width))
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (hf : Function.Bijective (StackNames.findNameSpt f))
    (ha : ¬s.useAlloc) (hs : ¬s.useStore) (hk : ¬s.useStack)
    (hcode : s.code = sptFromAList (StackNames.compileHOL f code))
    (hor : s.compileOracle = Prod.map id (Prod.map (StackNames.compileHOL f) id) ∘ oracle)
    (start k : Nat) :
    (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
      { s with clock := k })).1 =
      (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { StackNames.makeInit f (sptFromAList code) oracle s with clock := k })).1 := by
  have h := StackNames.CompileSemantics.evaluate_entry_renameState
    (c := s.compile) (f := f) (s := StackNames.makeInit f (sptFromAList code) oracle s)
    hf ha hs hk rfl start k
  rw [stack_names_rename_makeInit s f code oracle hf hcode hor] at h
  have hr := congrArg Prod.fst h
  exact hr

/-- The actual s2/s3 boundary of fullMakeInit has zero extra entry clock. -/
theorem fullMakeInit_s2_s3_entry_result {width : Nat} [NeZero width] {C F : Type}
    (sc : StackToLab.Config) (dc : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (code : List (Nat × HolProg width))
    (t : LabSem.State width C F) (saveRegs : Nat → Bool)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (hf : Function.Bijective (StackNames.findNameSpt sc.regNames)) (start k : Nat) :
    (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
      { StackToLab.Proofs.FullMakeInitSemantics.s3 sc dc maxHeap sp offset code t saveRegs oracle
          with clock := k })).1 =
      (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { StackToLab.Proofs.FullMakeInitSemantics.s2 sc dc maxHeap sp offset code t saveRegs oracle
            with clock := k })).1 := by
  apply stack_names_makeInit_entry_result
    (StackToLab.Proofs.FullMakeInitSemantics.s3 sc dc maxHeap sp offset code t saveRegs oracle)
    sc.regNames (StackToLab.Proofs.FullMakeInitSemantics.code2 sc dc maxHeap sp offset code)
    (StackToLab.Proofs.FullMakeInitSemantics.coracle2 sc sp offset oracle) hf
  · exact Bool.false_ne_true
  · exact Bool.false_ne_true
  · exact Bool.false_ne_true
  · rfl
  · rfl

#print axioms stack_names_rename_makeInit
#print axioms stack_names_makeInit_entry_result
#print axioms fullMakeInit_s2_s3_entry_result

end InitECandidate.Solver.Wave8Stage.Stage4
