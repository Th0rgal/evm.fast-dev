import InitECandidate.Solver.Wave8Stage.Stage4SafeRemoveClock

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8Stage.Stage4
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.Wave8Stage.RuntimeLabels
open InitECandidate.Solver.Wave8Stage.SafeRemoveClock
variable {width : Nat} [NeZero width]

/-- All runtime and code invariants for the real unfiltered StackRemove source
are discharged by initialization and compiler syntax. -/
theorem fullMakeInit_remove_ready {C F : Type}
    (sc : StackToLab.Config) (dc : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (bitmaps : List (BitVec width))
    (code : List (Nat × HolProg width)) (t : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (hA : StackToLab.Proofs.FullMakeInitSemantics.Assumptions
      sc dc maxHeap sp offset bitmaps code t saveRegs dataSp oracle)
    (conf : AsmConfigExact width) (perf : Bool) (wc : WordToWord.Config)
    (arch : AsmArchitecture) (source : List (Pancake.PanLang.DeclHOL width))
    (hcode : code = (WordToStack.Native.compileNative conf perf
      (WordToWord.compile wc conf (panToWordCompileProgHOL arch source)).2).2.2.2)
    (hm : MemorySafe storeConstsStubLocation t.memDomain t.memory)
    (ho : ∀ i, (oracle i).2.1 = []) :
    Ready storeConstsStubLocation
      (StackRemove.Proofs.InitMake.makeInitAny (StackToLab.isGenGc dc.gcKind) maxHeap
        bitmaps dataSp (StackToLab.Proofs.FullMakeInitSemantics.coracle1 oracle) sc.jump offset sp
        (sptFromAList (StackToLab.Proofs.FullMakeInitSemantics.code1 dc code))
        (StackToLab.Proofs.FullMakeInitSemantics.s2 sc dc maxHeap sp offset code t saveRegs oracle)) := by
  constructor
  · exact fullMakeInit_reduced_stateSafe sc dc maxHeap sp offset bitmaps code t saveRegs
      dataSp oracle hA (by decide) hm
  · apply pancake_compiled_codeSafe dc conf perf wc arch source
    rw [StackRemove.Proofs.InitAny.makeInitAnyCode]
    simp only [StackToLab.Proofs.FullMakeInitSemantics.code1, hcode]
  · intro i
    rw [StackRemove.Proofs.InitAny.makeInitAnyCompileOracle]
    simp [StackToLab.Proofs.FullMakeInitSemantics.coracle1, ho]

/-- Compose the unfiltered quantitative StackRemove simulation with the
actual initializer and StackToLab transfer. The sole source-run premise is
now on the real reduced state, before StackRemove; no code-cost or simulation
callback remains. Its finite program-dependent budget is not the frozen 8/32 bound. -/
theorem fullMakeInit_lab_affine_of_reduced_run {C F : Type}
    (sc : StackToLab.Config) (dc : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (bitmaps : List (BitVec width))
    (code : List (Nat × HolProg width)) (t : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (hA : StackToLab.Proofs.FullMakeInitSemantics.Assumptions
      sc dc maxHeap sp offset bitmaps code t saveRegs dataSp oracle)
    (conf : AsmConfigExact width) (perf : Bool) (wc : WordToWord.Config)
    (arch : AsmArchitecture) (source : List (Pancake.PanLang.DeclHOL width))
    (hcode : code = (WordToStack.Native.compileNative conf perf
      (WordToWord.compile wc conf (panToWordCompileProgHOL arch source)).2).2.2.2)
    (hm : MemorySafe storeConstsStubLocation t.memDomain t.memory)
    (ho : ∀ i, (oracle i).2.1 = []) (k : Nat)
    (hne : StackToLab.Proofs.FlattenSemantics.stackEntryClass
      (StackSemEvaluate.evaluate (.call none (.inl BvlToBvi.initGlobalsLocation) none,
        { StackRemove.Proofs.InitMake.makeInitAny (StackToLab.isGenGc dc.gcKind) maxHeap
            bitmaps dataSp (StackToLab.Proofs.FullMakeInitSemantics.coracle1 oracle) sc.jump offset sp
            (sptFromAList (StackToLab.Proofs.FullMakeInitSemantics.code1 dc code))
            (StackToLab.Proofs.FullMakeInitSemantics.s2 sc dc maxHeap sp offset code t saveRegs oracle)
          with clock := k })).1 ≠ .RunError)
    (hnt : (StackSemEvaluate.evaluate (.call none (.inl BvlToBvi.initGlobalsLocation) none,
        { StackRemove.Proofs.InitMake.makeInitAny (StackToLab.isGenGc dc.gcKind) maxHeap
            bitmaps dataSp (StackToLab.Proofs.FullMakeInitSemantics.coracle1 oracle) sc.jump offset sp
            (sptFromAList (StackToLab.Proofs.FullMakeInitSemantics.code1 dc code))
            (StackToLab.Proofs.FullMakeInitSemantics.s2 sc dc maxHeap sp offset code t saveRegs oracle)
          with clock := k })).1 ≠ some .timeOut) :
    let M := codeStepBudget (StackToLab.Proofs.FullMakeInitSemantics.code2 sc dc maxHeap sp offset code)
    (LabSem.evaluate { t with clock := (M + 1) * k + (3 * M + 2) }).1 ≠ .timeOut := by
  have hs := fullMakeInit_remove_ready sc dc maxHeap sp offset bitmaps code t saveRegs dataSp
    oracle hA conf perf wc arch source hcode hm ho
  obtain ⟨post, run, rel⟩ := fullMakeInit_postInit_stateRel
    sc dc maxHeap sp offset bitmaps code t saveRegs dataSp oracle hA
  have herr : (StackSemEvaluate.evaluate (.call none (.inl BvlToBvi.initGlobalsLocation) none,
      { StackRemove.Proofs.InitMake.makeInitAny (StackToLab.isGenGc dc.gcKind) maxHeap
          bitmaps dataSp (StackToLab.Proofs.FullMakeInitSemantics.coracle1 oracle) sc.jump offset sp
          (sptFromAList (StackToLab.Proofs.FullMakeInitSemantics.code1 dc code))
          (StackToLab.Proofs.FullMakeInitSemantics.s2 sc dc maxHeap sp offset code t saveRegs oracle)
        with clock := k })).1 ≠ some .error := by
    intro he
    rw [he] at hne
    exact hne rfl
  have heq := entry_result_add_one sc.jump offset sp BvlToBvi.initGlobalsLocation k
    _ post hs (by decide) rel herr hnt
  have hn' := hne
  have ht' := hnt
  rw [← heq] at hn' ht'
  have h := fullMakeInit_lab_affine_of_postInit_run sc dc maxHeap sp offset bitmaps code t
    saveRegs dataSp oracle hA ho post run (k + 1) hn' ht'
  let M := codeStepBudget (StackToLab.Proofs.FullMakeInitSemantics.code2 sc dc maxHeap sp offset code)
  have hbudget : (M + 1) * (k + 1) + (2 * M + 1) = (M + 1) * k + (3 * M + 2) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  change (LabSem.evaluate { t with clock := (M + 1) * (k + 1) + (2 * M + 1) }).1 ≠ .timeOut at h
  rwa [hbudget] at h

#print axioms fullMakeInit_remove_ready
#print axioms fullMakeInit_lab_affine_of_reduced_run
end InitECandidate.Solver.Wave8Stage.Stage4
