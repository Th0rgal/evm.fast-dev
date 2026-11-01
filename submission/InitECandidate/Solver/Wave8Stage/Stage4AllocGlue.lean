import InitECandidate.Solver.Wave8Stage.Stage4AllocClock
import InitECandidate.Solver.Wave8Stage.Stage4RemoveGlue
import InitECandidate.Solver.Wave8Stage.Stage4RawCallGlue

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8Stage.Stage4
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.Wave8Stage.RuntimeLabels
open InitECandidate.Solver.Wave8Stage.Static
open PanToStackRawCallNoAllocAndStackAllocStructural
open PanToStackRawCallNoAllocAndStackAllocStructural.PanToStackNoAlloc
open StackToLabAndLabToTargetNoLocValue6
variable {width : Nat} [NeZero width]

/-- The actual initialized state immediately before StackRemove. -/
noncomputable abbrev reducedInit {C F : Type}
    (sc : StackToLab.Config) (dc : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (bitmaps : List (BitVec width))
    (code : List (Nat × HolProg width)) (t : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)) :=
  StackRemove.Proofs.InitMake.makeInitAny (StackToLab.isGenGc dc.gcKind) maxHeap
    bitmaps dataSp (StackToLab.Proofs.FullMakeInitSemantics.coracle1 oracle) sc.jump offset sp
    (sptFromAList (StackToLab.Proofs.FullMakeInitSemantics.code1 dc code))
    (StackToLab.Proofs.FullMakeInitSemantics.s2 sc dc maxHeap sp offset code t saveRegs oracle)

/-- The real RawCall/StackAlloc boundary preserves the entry result at clock
2*k. Initialization discharges the runtime invariant; syntax discharges
StackAlloc's identity and the fresh GC-section condition. -/
theorem fullMakeInit_reduced_entry_result {C F : Type}
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
    (ho : ∀ i, (oracle i).2.1 = []) (k : Nat) :
    let initial := (StackToLab.Proofs.FullMakeInit.fullMakeInit
      sc dc maxHeap sp offset bitmaps code t saveRegs dataSp oracle).1
    let res := (StackSemEvaluate.evaluate
      ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
        { initial with clock := k })).1
    StackToLab.Proofs.FlattenSemantics.stackEntryClass res ≠ .RunError →
    res ≠ some .timeOut →
    (StackSemEvaluate.evaluate (.call none (.inl BvlToBvi.initGlobalsLocation) none,
      { reducedInit sc dc maxHeap sp offset bitmaps code t saveRegs dataSp oracle
        with clock := 2 * k })).1 = res := by
  intro initial res hne hnt
  have hAcopy := hA
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hgood, _⟩ := hAcopy
  have raw := fullMakeInit_rawCall_entry_result sc dc maxHeap sp offset bitmaps code t
    saveRegs dataSp oracle hgood.1 k hne hnt
  have ready := fullMakeInit_remove_ready sc dc maxHeap sp offset bitmaps code t saveRegs
    dataSp oracle hA conf perf wc arch source hcode hm ho
  have hid : ∀ e ∈ StackRawCall.compile code, StackAlloc.progComp e = e := by
    rw [hcode]
    exact AllocIdentity.rawCall_alloc_progComp_id conf perf _
      (fun e he => ⟨PanToStackNoStoreConsts.panToWordToWord_NoSt arch source wc conf e he,
        panToWordToWord_NSL arch source wc conf e he⟩)
      (panToStackRawCall_noAlloc_unconditional arch source wc conf perf)
  have hgc : ∀ e ∈ StackRawCall.compile code, e.1 ≠ gcStubLocation := by
    intro e he
    simp only [StackRawCall.compile] at he
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
    have hge := (hgood.2.1 x hx).1
    change x.1 ≠ gcStubLocation
    simp only [gcStubLocation, stackNumStubs, wordNumStubs] at hge ⊢
    omega
  let reduced := reducedInit sc dc maxHeap sp offset bitmaps code t saveRegs dataSp oracle
  have hstate :
      { StackAlloc.makeInit dc (sptFromAList (StackRawCall.compile code)) oracle reduced
          with clock := 2 * k } =
      { initial with code := sptFromAList (StackRawCall.compile code), clock := 2 * k } := rfl
  have herr : res ≠ some .error := by
    intro he
    rw [he] at hne
    exact hne rfl
  have hnr : (StackSemEvaluate.evaluate (.call none (.inl BvlToBvi.initGlobalsLocation) none,
      { StackAlloc.makeInit dc (sptFromAList (StackRawCall.compile code)) oracle reduced
          with clock := 2 * k })).1 ≠ some .error := by
    rw [hstate, raw]
    exact herr
  have alloc := AllocClock.makeInit_entry_result dc (StackRawCall.compile code) oracle
    reduced BvlToBvi.initGlobalsLocation (2 * k) hid hgc ready.state ready.code
    (by rw [StackRemove.Proofs.InitAny.makeInitAnyCode]; rfl)
    (StackRemove.Proofs.InitAny.makeInitAnyUseStack ..) ready.oracle ho (by decide) hnr
  rw [hstate, raw] at alloc
  exact alloc

/-- End-to-end Stage 4 affine bound from the original initialized StackSem
entry, with every pass bridge discharged. The maximum whole-procedure cost
M is explicit and program-dependent; this theorem does not assert 8/32. -/
theorem fullMakeInit_lab_affine_of_source_run {C F : Type}
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
    (ho : ∀ i, (oracle i).2.1 = []) (k : Nat) :
    let initial := (StackToLab.Proofs.FullMakeInit.fullMakeInit
      sc dc maxHeap sp offset bitmaps code t saveRegs dataSp oracle).1
    let res := (StackSemEvaluate.evaluate
      ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
        { initial with clock := k })).1
    StackToLab.Proofs.FlattenSemantics.stackEntryClass res ≠ .RunError →
    res ≠ some .timeOut →
    let M := codeStepBudget (StackToLab.Proofs.FullMakeInitSemantics.code2 sc dc maxHeap sp offset code)
    (LabSem.evaluate { t with clock := 2 * (M + 1) * k + (3 * M + 2) }).1 ≠ .timeOut := by
  intro initial res hne hnt M
  have hr := fullMakeInit_reduced_entry_result sc dc maxHeap sp offset bitmaps code t
    saveRegs dataSp oracle hA conf perf wc arch source hcode hm ho k hne hnt
  have h := fullMakeInit_lab_affine_of_reduced_run sc dc maxHeap sp offset bitmaps code t
    saveRegs dataSp oracle hA conf perf wc arch source hcode hm ho (2 * k)
    (by rw [hr]; exact hne) (by rw [hr]; exact hnt)
  have hbudget : (M + 1) * (2 * k) = 2 * (M + 1) * k := by
    rw [Nat.mul_left_comm, ← Nat.mul_assoc]
  change (LabSem.evaluate { t with clock := (M + 1) * (2 * k) + (3 * M + 2) }).1 ≠ .timeOut at h
  rwa [hbudget] at h

#print axioms fullMakeInit_reduced_entry_result
#print axioms fullMakeInit_lab_affine_of_source_run
end InitECandidate.Solver.Wave8Stage.Stage4
