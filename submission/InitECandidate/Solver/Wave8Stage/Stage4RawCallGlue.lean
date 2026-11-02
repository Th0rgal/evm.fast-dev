import InitECandidate.Solver.SelfContainedStageBounds
import InitECandidate.Solver.Wave8Stage.StackRawCallClock

set_option autoImplicit false

namespace InitECandidate.Solver.Wave8Stage.Stage4

open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang

variable {width : Nat} [NeZero width]

/-- The actual Pancake compilation equations discharge the distinct-code
premise of the RawCall entry simulation. -/
theorem pancake_stack_code_distinct {S Q : Type}
    (c : Backend.Config) (mc : MachineConfig width S Q)
    (panCode : List (Pancake.PanLang.DeclHOL width))
    (col : List (Option (Spt Nat)))
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bitmaps : List (BitVec width)) (wconf : WordToStack.Native.Config) (fs : List Nat)
    (code : List (Nat × HolProg width))
    (hwtw : WordToWord.compile c.wordToWordConf mc.target.config
      (panToWordCompileProgHOL mc.target.config.isa panCode) = (col, wprog))
    (hwts : WordToStack.Native.compileNative mc.target.config false wprog =
      (bitmaps, wconf, fs, code))
    (hisa : mc.target.config.isa ≠ .ag32)
    (hd : ((Pancake.PanLang.functionsHOL panCode).map Prod.fst).Nodup) :
    (code.map Prod.fst).Nodup :=
  (Pancake.Proofs.PanToTarget.pan_to_stack_compile_lab_pres
    mc panCode _ c col wprog bitmaps wconf fs code ⟨rfl, hwtw, hisa, hwts, hd⟩).1

/-- A non-error, non-timeout entry run has exactly the same result after
StackRawCall at twice the source clock. -/
theorem rawCall_entry_result_double {C F : Type}
    (code : List (Nat × HolProg width)) (s : StackSemStateFiniteExact width C F)
    (start k : Nat) (hd : (code.map Prod.fst).Nodup) (hc : s.code = sptFromAList code)
    (hne : (StackSemEvaluate.evaluate
      ((.call none (.inl start) none : HolProg width), { s with clock := k })).1 ≠ some .error)
    (hnt : (StackSemEvaluate.evaluate
      ((.call none (.inl start) none : HolProg width), { s with clock := k })).1 ≠ some .timeOut) :
    (StackSemEvaluate.evaluate
      ((.call none (.inl start) none : HolProg width),
        { s with code := sptFromAList (StackRawCall.compile code), clock := 2 * k })).1 =
    (StackSemEvaluate.evaluate
      ((.call none (.inl start) none : HolProg width), { s with clock := k })).1 := by
  obtain ⟨extra, post, hb, run, _⟩ :=
    StackRawCallClock.entrySimulationB code s start k _ _ hd hc rfl hne
  have hle : k + extra ≤ 2 * k := by omega
  have lifted := StackProps.evaluateAddClock (2 * k - (k + extra)) _ _ _ _ ⟨run, hnt⟩
  have hclock : k + extra + (2 * k - (k + extra)) = 2 * k := Nat.add_sub_of_le hle
  simpa only [hclock, StackSemEvaluate.evaluate] using congrArg Prod.fst lifted

/-- Specialize the doubled-clock RawCall result to the actual source state
returned by fullMakeInit; its installed-code equation is definitional. -/
theorem fullMakeInit_rawCall_entry_result {C F : Type}
    (sc : StackToLab.Config) (dc : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (bitmaps : List (BitVec width))
    (code : List (Nat × HolProg width)) (t : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (hd : (code.map Prod.fst).Nodup) (k : Nat) :
    let initial := (StackToLab.Proofs.FullMakeInit.fullMakeInit
      sc dc maxHeap sp offset bitmaps code t saveRegs dataSp oracle).1
    let res := (StackSemEvaluate.evaluate
      ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
        { initial with clock := k })).1
    StackToLab.Proofs.FlattenSemantics.stackEntryClass res ≠ .RunError →
    res ≠ some .timeOut →
    (StackSemEvaluate.evaluate
      ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
        { initial with code := sptFromAList (StackRawCall.compile code), clock := 2 * k })).1 = res := by
  intro initial res hne hnt
  have hn : res ≠ some .error := by
    rintro he
    simp [he, StackToLab.Proofs.FlattenSemantics.stackEntryClass] at hne
  exact rawCall_entry_result_double code initial BvlToBvi.initGlobalsLocation k hd rfl hn hnt


end InitECandidate.Solver.Wave8Stage.Stage4
