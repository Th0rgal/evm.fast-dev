import InitECandidate.Solver.Wave8GuestInv.InitializedPipelineTransfer
import InitECandidate.Solver.Wave8Stage.WordCostPipelineCertificate
import InitECandidate.Solver.Wave8Stage.ConcreteBaseline.InitializedTransfer
import InitECandidate.Solver.Wave8Stage.CompletedNonfailure
import InitECandidate.Solver.Wave8Stage.Stage5Transfer

/-! Preserve completed entry results at the certified factor-two budget.
The actual compiler pipeline and Boolean cost certificates remain explicit. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8GuestInv.CertifiedPipelineTransfer
open Classical InitE Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack.Pancake.Proofs.PanToTarget Flapjack.LoopToWord.CompileCorrect
open Flapjack.LoopToWordStateRelImpSemanticsSupport
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenSemantics
open Flapjack.WordToStackProofs.CompCorrect
open InitECandidate.Solver.Wave8Stage
open InitECandidate.Solver.SelfContainedStageBounds
open EntryClassTransfer InitializedPipelineTransfer

theorem word_to_stack_certified_complete {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (start registers clock : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F)
    (related : WordToStackProofs.stateRel ac registers 0 0 source target [] 0)
    (noInstall : WordProps.noInstallCode source.code)
    (defs : Option Nat → WordCostEffects.Effects)
    (terminal : Basis.Pure.MlString.MlString → Bool) (oracle : HolOracle F)
    (certificates : WordCostEntryCertificate.CodeCertified defs terminal source.code)
    (terminalCalls : WordCostEntryCertificate.TerminalOracle terminal oracle)
    (oracleEq : source.ffi.oracle = oracle)
    (entryBound : ∀ exit, WordCostEffects.AtMost (defs (some start) exit) 1)
    (complete : ∃ outcome, wordEntryClass (WordSemStateFiniteExact.evaluate
      (.call none (some start) [0] none) {source with clock := clock}).1 =
        .CompleteResult outcome) :
    ∃ outcome, stackEntryClass (StackSemEvaluate.evaluate
      ((.call none (.inl start) none : HolProg width),
        {target with clock := 2 * clock})).1 =
      .CompleteResult outcome := by
  have notError : (WordSemStateFiniteExact.evaluate
      (.call none (some start) [0] none) {source with clock := clock}).1 ≠ some .error := by
    intro bad
    obtain ⟨outcome,complete⟩ := complete
    rw [bad] at complete
    cases complete
  have notTimeout : (WordSemStateFiniteExact.evaluate
      (.call none (some start) [0] none) {source with clock := clock}).1 ≠ some .timeOut := by
    intro bad
    obtain ⟨outcome, complete⟩ := complete
    rw [bad] at complete
    cases complete
  rcases run : WordSemStateFiniteExact.evaluate
      (.call none (some start) [0] none) {source with clock := clock} with ⟨result,post⟩
  rw [run] at complete notError
  obtain ⟨extra,extraBound,targetPost,targetResult,targetRun,_,_,contract⟩ :=
    WordToStackCostEntry.compCall ac start {source with clock := clock} registers result post
      {target with clock := clock} []
      ⟨run,notError,WordToStackProofs.SemanticsHelpers.stateRelWithClock
        ac registers clock source target [] 0 related⟩
  have targetComplete : ∃ outcome, stackEntryClass targetResult = .CompleteResult outcome := by
    by_cases same : result.map compileResult = targetResult
    · rw [← same]
      exact compiled_word_complete result complete
    · rw [if_neg same] at contract
      rw [contract.1]
      exact ⟨_,rfl⟩
  have targetNotTimeout := (stack_complete_ready targetResult targetComplete).2
  have cost := WordCostEntryCertificate.entryCost_bound defs terminal source.code oracle
    noInstall certificates terminalCalls start {source with clock := clock}
    ⟨rfl, oracleEq⟩ entryBound (by rw [run]; exact notError) notTimeout
  let budget := 2 * clock
  have enough : clock + extra ≤ budget := by
    dsimp only [budget]
    change WordToStackSourceCost.sourceCost _ _ ≤ clock at cost
    omega
  have lifted := Flapjack.Compiler.Backend.StackProps.evaluateAddClock
    (budget-(clock+extra)) (.call none (.inl start) none)
    {target with clock := clock+extra} targetResult targetPost ⟨targetRun,targetNotTimeout⟩
  have clockEq : clock+extra+(budget-(clock+extra)) = budget := by omega
  simp only [clockEq] at lifted
  change ∃ outcome, stackEntryClass
    (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
      {target with clock := budget})).1 = .CompleteResult outcome
  rw [lifted]
  exact targetComplete

#print axioms word_to_stack_certified_complete
theorem initialized_certified_word_to_stack_complete {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (wc : WordToWord.Config) (panCode : List (DeclHOL width))
    (col : List (Option (Spt Nat)))
    (wordCode : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bitmaps : List (BitVec width)) (wconf : WordToStack.Native.Config) (fs : List Nat)
    (stackCode : List (Nat × HolProg width))
    (scc : StackToLab.Config) (dc : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (lab : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat) (cfg : C)
    (stack aux : StackSemStateFiniteExact width C F) (start clock : Nat)
    (dimension : goodDimindex width) (registers : ac.avoidRegs.length + 13 ≤ ac.regCount)
    (isa : ac.isa ≠ .ag32)
    (wtw : WordToWord.compile wc ac (panToWordCompileProgHOL ac.isa panCode) = (col,wordCode))
    (wts : WordToStack.Native.compileNative ac false wordCode = (bitmaps,wconf,fs,stackCode))
    (initialized : FullMakeInit.fullMakeInit scc dc maxHeap sp offset bitmaps stackCode lab
      saveRegs dataSp (fun _ => (cfg, [], [])) = (stack, some aux))
    (defs : Option Nat → WordCostEffects.Effects)
    (terminal : Basis.Pure.MlString.MlString → Bool) (oracle : HolOracle F) (fuel : Nat)
    (noLabels : ∀ dest label, defs dest (.breakTo label) = none ∧ defs dest (.continueTo label) = none)
    (indirect : ∀ name, WordCostCertificates.Subeffects (defs (some name)) (defs none))
    (checked : ∀ entry ∈ panToWordCompileProgHOL ac.isa panCode,
      WordCostCheck.checkProgram defs terminal fuel
        (WordCostCompilerControl.preAllocation ac ac.twoRegArith entry.2.1 entry.2.2)
        (defs (some entry.1)) = true)
    (entryBound : ∀ exit, WordCostEffects.AtMost (defs (some start) exit) 1)
    (oracleEq : lab.ffi.oracle = oracle)
    (terminalCalls : WordCostEntryCertificate.TerminalOracle terminal oracle)
    (complete : ∃ outcome, wordEntryClass (WordSemStateFiniteExact.evaluate
      (.call none (some start) [0] none)
      {WordToStack.Native.Initialization.makeInit ac
        (ac.regCount - (5 + ac.avoidRegs.length)) stack (sptFromAList wordCode)
        (fun _ => ((bitmaps.length,cfg), [])) with clock := clock}).1 = .CompleteResult outcome) :
    ∃ outcome, stackEntryClass (StackSemEvaluate.evaluate
      ((.call none (.inl start) none : HolProg width),
        {stack with clock := 2 * clock})).1 = .CompleteResult outcome := by
  have related := WordToStackPipelineBudget.initialized_stateRel ac wc panCode col wordCode
    bitmaps wconf fs stackCode scc dc maxHeap sp offset lab saveRegs dataSp cfg stack aux
    dimension registers isa wtw wts initialized
  have certificates := WordCostCodeCertificates.compile_codeCertified defs terminal wc ac
    (panToWordCompileProgHOL ac.isa panCode) fuel noLabels indirect
    (WordCostPipelineCertificate.panToWord_noMt_members ac.isa panCode) checked
  rw [wtw] at certificates
  have ffiEq := FullMakeInit.fullMakeInitFfi scc dc maxHeap sp offset bitmaps stackCode lab
    saveRegs dataSp (fun _ => (cfg, [], []))
  rw [initialized] at ffiEq
  apply word_to_stack_certified_complete ac start _ clock _ stack related
    (WordToStackCompileBudget.compile_noInstall wc ac _ col wordCode wtw
      (PanToWord.pan_to_word_compile_prog_no_install_code _ panCode _ rfl)
      (PanToWord.pan_to_word_compile_prog_no_mt_code _ panCode _ rfl))
    defs terminal oracle certificates terminalCalls
    (by change stack.ffi.oracle = oracle; rw [ffiEq]; exact oracleEq) entryBound complete

noncomputable def certifiedStackClock {width : Nat} [NeZero width]
    (panCode : List (DeclHOL width)) (start : MlS) (clock : Nat) : Nat :=
  2 * wordClock panCode start clock

theorem pan_to_certified_stack_complete {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (wc : WordToWord.Config) (panCode : List (DeclHOL width))
    (col : List (Option (Spt Nat)))
    (wordCode : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bitmaps : List (BitVec width)) (wconf : WordToStack.Native.Config) (fs : List Nat)
    (stackCode : List (Nat × HolProg width))
    (scc : StackToLab.Config) (dc : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (lab : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat) (cfg : C)
    (stack aux : StackSemStateFiniteExact width C F)
    (dimension : goodDimindex width) (registers : ac.avoidRegs.length + 13 ≤ ac.regCount)
    (isa : ac.isa ≠ .ag32)
    (wtw : WordToWord.compile wc ac (panToWordCompileProgHOL ac.isa panCode) = (col,wordCode))
    (wts : WordToStack.Native.compileNative ac false wordCode = (bitmaps,wconf,fs,stackCode))
    (initialized : FullMakeInit.fullMakeInit scc dc maxHeap sp offset bitmaps stackCode lab
      saveRegs dataSp (fun _ => (cfg, [], [])) = (stack, some aux))
    (defs : Option Nat → WordCostEffects.Effects)
    (terminal : Basis.Pure.MlString.MlString → Bool) (oracle : HolOracle F) (fuel : Nat)
    (noLabels : ∀ dest label, defs dest (.breakTo label) = none ∧ defs dest (.continueTo label) = none)
    (indirect : ∀ name, WordCostCertificates.Subeffects (defs (some name)) (defs none))
    (checked : ∀ entry ∈ panToWordCompileProgHOL ac.isa panCode,
      WordCostCheck.checkProgram defs terminal fuel
        (WordCostCompilerControl.preAllocation ac ac.twoRegArith entry.2.1 entry.2.2)
        (defs (some entry.1)) = true)
    (entryBound : ∀ exit, WordCostEffects.AtMost (defs (some BvlToBvi.initGlobalsLocation) exit) 1)
    (oracleEq : lab.ffi.oracle = oracle)
    (terminalCalls : WordCostEntryCertificate.TerminalOracle terminal oracle)
    (source : PanSemStateFiniteExact width F) (start : MlS)
    (globalsSize : Nat) (heapLen : BitVec width)
    (front : FrontendRelation source (frontendWordState ac panCode wordCode bitmaps stack cfg)
      ac.isa panCode start globalsSize heapLen)
    (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact width F)
    (hst : decsStcnamesHOLExact [] panCode = some stCtxt)
    (decls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width F _
      {source with structs := stCtxt} (fun a => Classical.propDecidable (source.memaddrs a))
      panCode = some s_decls)
    (k : Nat) (result : Option (PanSemResultExact width))
    (post : PanSemStateFiniteExact width F)
    (run : PanSemStateFiniteExact.evaluateHOLFiniteState {s_decls with clock := k}
      (.call none start [] : ProgHOL width) = (result,post))
    (notError : panEntryClass result ≠ .RunError)
    (notTimeout : result ≠ some .timeOut) :
    ∃ outcome, stackEntryClass (StackSemEvaluate.evaluate
      ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
        {stack with clock := certifiedStackClock panCode start k})).1 = .CompleteResult outcome := by
  let pre := frontendWordState ac panCode wordCode bitmaps stack cfg
  let oldClock := (FrontendCostTransfer.frontBudget panCode start + 1) * k +
    (FrontendCostTransfer.frontBudget panCode start + 4)
  have oldClass := FrontendStackTransfer.pan_to_word_static_class source pre ac.isa panCode
    start globalsSize heapLen front stCtxt s_decls hst decls k result post run notError notTimeout
  have sourceComplete : ∃ outcome, panEntryClass result = .CompleteResult outcome := by
    cases result with
    | none => exact False.elim (notError rfl)
    | some r => cases r <;> simp_all [panEntryClass]
  have oldComplete : ∃ outcome, wordEntryClass (WordSemStateFiniteExact.evaluate
      (.call none (some firstLoopName) [0] none) {pre with clock := oldClock}).1 =
        .CompleteResult outcome := by
    rw [oldClass]
    exact sourceComplete
  have oldNotTimeout : (WordSemStateFiniteExact.evaluate
      (.call none (some firstLoopName) [0] none) {pre with clock := oldClock}).1 ≠ some .timeOut := by
    obtain ⟨outcome,complete⟩ := oldComplete
    intro bad
    rw [bad] at complete
    cases complete
  have frontBound := FrontendStaticBudget.frontBudget_le_staticFrontBudget panCode start
  have enough : oldClock ≤ wordClock panCode start k :=
    Nat.add_le_add (Nat.mul_le_mul_right k (Nat.add_le_add_right frontBound 1))
      (Nat.add_le_add_right frontBound 4)
  rcases oldRun : WordSemStateFiniteExact.evaluate
      (.call none (some firstLoopName) [0] none) {pre with clock := oldClock} with ⟨r,t⟩
  have lift := WordSemStateFiniteExact.evaluate_add_clock (wordClock panCode start k-oldClock)
    (.call none (some firstLoopName) [0] none) {pre with clock := oldClock} r t
    ⟨oldRun,by rw [oldRun] at oldNotTimeout; exact oldNotTimeout⟩
  have clockEq : oldClock+(wordClock panCode start k-oldClock) = wordClock panCode start k :=
    Nat.add_sub_of_le enough
  simp only [clockEq] at lift
  have preComplete : ∃ outcome, wordEntryClass (WordSemStateFiniteExact.evaluate
      (.call none (some firstLoopName) [0] none) {pre with clock := wordClock panCode start k}).1 =
        .CompleteResult outcome := by
    rw [lift]
    rw [oldRun] at oldComplete
    exact oldComplete
  have preNotError : (WordSemStateFiniteExact.evaluate
      (.call none (some firstLoopName) [0] none) {pre with clock := wordClock panCode start k}).1 ≠
        some .error := by
    obtain ⟨outcome,complete⟩ := preComplete
    intro bad
    rw [bad] at complete
    cases complete
  have facts := panToTargetWordStateFacts ac (ac.regCount - (5 + ac.avoidRegs.length))
    (sptFromAList wordCode) (fun _ => ((bitmaps.length,cfg), [])) scc dc maxHeap sp
    offset bitmaps stackCode lab saveRegs dataSp (fun _ => (cfg, [], [])) stack aux initialized
  have agree := word_to_word_clocked_agree wc ac (panToWordCompileProgHOL ac.isa panCode)
    col wordCode pre firstLoopName (wordClock panCode start k) wtw facts.1
    (PanToWord.pan_to_word_compile_prog_no_install_code _ panCode _ rfl)
    (PanToWord.pan_to_word_compile_prog_no_alloc_code _ panCode _ rfl)
    (PanToWord.pan_to_word_compile_prog_no_mt_code _ panCode _ rfl) rfl rfl preNotError
  have allocatedComplete : ∃ outcome, wordEntryClass (WordSemStateFiniteExact.evaluate
      (.call none (some firstLoopName) [0] none)
      {nativeWordState ac wordCode bitmaps stack cfg with clock := wordClock panCode start k}).1 =
        .CompleteResult outcome := by
    change ∃ outcome, wordEntryClass (WordSemStateFiniteExact.evaluate
      (.call none (some firstLoopName) [0] none)
      {pre with clock := wordClock panCode start k, code := sptFromAList wordCode}).1 = _
    rw [agree.1]
    exact preComplete
  exact initialized_certified_word_to_stack_complete ac wc panCode col wordCode bitmaps wconf fs stackCode
    scc dc maxHeap sp offset lab saveRegs dataSp cfg stack aux firstLoopName
    (wordClock panCode start k) dimension registers isa wtw wts initialized defs terminal oracle fuel noLabels indirect checked entryBound oracleEq terminalCalls allocatedComplete


set_option pp.fullNames true
#print axioms initialized_certified_word_to_stack_complete
#print axioms pan_to_certified_stack_complete
open InitECandidate.Solver.Wave8Stage.RuntimeLabels
open InitECandidate.Solver.Wave8Stage.InitializedTransfer
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.RiscV.L3

theorem pan_to_certified_lab_not_timeOut {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (wc : WordToWord.Config) (panCode : List (DeclHOL width))
    (col : List (Option (Spt Nat)))
    (wordCode : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bitmaps : List (BitVec width)) (wconf : WordToStack.Native.Config) (fs : List Nat)
    (stackCode : List (Nat × HolProg width))
    (scc : StackToLab.Config) (dc : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (lab : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat) (cfg : C)
    (stack aux : StackSemStateFiniteExact width C F)
    (dimension : goodDimindex width) (registers : ac.avoidRegs.length + 13 ≤ ac.regCount)
    (isa : ac.isa ≠ .ag32)
    (wtw : WordToWord.compile wc ac (panToWordCompileProgHOL ac.isa panCode) = (col,wordCode))
    (wts : WordToStack.Native.compileNative ac false wordCode = (bitmaps,wconf,fs,stackCode))
    (initialized : FullMakeInit.fullMakeInit scc dc maxHeap sp offset bitmaps stackCode lab
      saveRegs dataSp (fun _ => (cfg, [], [])) = (stack, some aux))
    (defs : Option Nat → WordCostEffects.Effects)
    (terminal : Basis.Pure.MlString.MlString → Bool) (oracle : HolOracle F) (fuel : Nat)
    (noLabels : ∀ dest label, defs dest (.breakTo label) = none ∧ defs dest (.continueTo label) = none)
    (indirect : ∀ name, WordCostCertificates.Subeffects (defs (some name)) (defs none))
    (checked : ∀ entry ∈ panToWordCompileProgHOL ac.isa panCode,
      WordCostCheck.checkProgram defs terminal fuel
        (WordCostCompilerControl.preAllocation ac ac.twoRegArith entry.2.1 entry.2.2)
        (defs (some entry.1)) = true)
    (entryBound : ∀ exit, WordCostEffects.AtMost (defs (some BvlToBvi.initGlobalsLocation) exit) 1)
    (oracleEq : lab.ffi.oracle = oracle)
    (terminalCalls : WordCostEntryCertificate.TerminalOracle terminal oracle)
    (source : PanSemStateFiniteExact width F) (start : MlS)
    (globalsSize : Nat) (heapLen : BitVec width)
    (front : FrontendRelation source (frontendWordState ac panCode wordCode bitmaps stack cfg)
      ac.isa panCode start globalsSize heapLen)
    (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact width F)
    (hst : decsStcnamesHOLExact [] panCode = some stCtxt)
    (decls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width F _
      {source with structs := stCtxt} (fun a => Classical.propDecidable (source.memaddrs a))
      panCode = some s_decls)
    (k : Nat) (result : Option (PanSemResultExact width))
    (post : PanSemStateFiniteExact width F)
    (run : PanSemStateFiniteExact.evaluateHOLFiniteState {s_decls with clock := k}
      (.call none start [] : ProgHOL width) = (result,post))
    (notError : panEntryClass result ≠ .RunError)
    (notTimeout : result ≠ some .timeOut)
    (assumptions : FullMakeInitSemantics.Assumptions scc dc maxHeap sp offset bitmaps
      stackCode lab saveRegs dataSp (fun _ => (cfg, [], [])))
    (memorySafe : MemorySafe storeConstsStubLocation lab.memDomain lab.memory) :
    let M := Stage4.codeStepBudget (FullMakeInitSemantics.code2 scc dc maxHeap sp offset stackCode)
    (LabSem.evaluate {lab with
      clock := 2 * (M + 1) * certifiedStackClock panCode start k + (3 * M + 2)}).1 ≠ .timeOut := by
  have complete := pan_to_certified_stack_complete ac wc panCode col wordCode bitmaps wconf
    fs stackCode scc dc maxHeap sp offset lab saveRegs dataSp cfg stack aux dimension
    registers isa wtw wts initialized defs terminal oracle fuel noLabels indirect checked entryBound oracleEq terminalCalls source start globalsSize heapLen front stCtxt s_decls
    hst decls k result post run notError notTimeout
  have ready := stack_complete_ready _ complete
  have compiled : stackCode = (WordToStack.Native.compileNative ac false
      (WordToWord.compile wc ac (panToWordCompileProgHOL ac.isa panCode)).2).2.2.2 := by
    rw [wtw, wts]
  have bridge := Stage4.fullMakeInit_lab_affine_of_source_run scc dc maxHeap sp offset
    bitmaps stackCode lab saveRegs dataSp (fun _ => (cfg, [], [])) assumptions
    ac false wc ac.isa panCode compiled memorySafe (fun _ => rfl)
    (certifiedStackClock panCode start k)
  simp only [initialized] at bridge
  exact bridge ready.1 ready.2

/-- Preserve the completed result at the affine Lab clock. This supplies the
Stage 5 halt premise from the original source run, with no intermediate run premise. -/
theorem pan_to_certified_lab_complete {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (wc : WordToWord.Config) (panCode : List (DeclHOL width))
    (col : List (Option (Spt Nat)))
    (wordCode : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bitmaps : List (BitVec width)) (wconf : WordToStack.Native.Config) (fs : List Nat)
    (stackCode : List (Nat × HolProg width))
    (scc : StackToLab.Config) (dc : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (lab : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat) (cfg : C)
    (stack aux : StackSemStateFiniteExact width C F)
    (dimension : goodDimindex width) (registers : ac.avoidRegs.length + 13 ≤ ac.regCount)
    (isa : ac.isa ≠ .ag32)
    (wtw : WordToWord.compile wc ac (panToWordCompileProgHOL ac.isa panCode) = (col,wordCode))
    (wts : WordToStack.Native.compileNative ac false wordCode = (bitmaps,wconf,fs,stackCode))
    (initialized : FullMakeInit.fullMakeInit scc dc maxHeap sp offset bitmaps stackCode lab
      saveRegs dataSp (fun _ => (cfg, [], [])) = (stack, some aux))
    (defs : Option Nat → WordCostEffects.Effects)
    (terminal : Basis.Pure.MlString.MlString → Bool) (oracle : HolOracle F) (fuel : Nat)
    (noLabels : ∀ dest label, defs dest (.breakTo label) = none ∧ defs dest (.continueTo label) = none)
    (indirect : ∀ name, WordCostCertificates.Subeffects (defs (some name)) (defs none))
    (checked : ∀ entry ∈ panToWordCompileProgHOL ac.isa panCode,
      WordCostCheck.checkProgram defs terminal fuel
        (WordCostCompilerControl.preAllocation ac ac.twoRegArith entry.2.1 entry.2.2)
        (defs (some entry.1)) = true)
    (entryBound : ∀ exit, WordCostEffects.AtMost (defs (some BvlToBvi.initGlobalsLocation) exit) 1)
    (oracleEq : lab.ffi.oracle = oracle)
    (terminalCalls : WordCostEntryCertificate.TerminalOracle terminal oracle)
    (source : PanSemStateFiniteExact width F) (start : MlS)
    (globalsSize : Nat) (heapLen : BitVec width)
    (front : FrontendRelation source (frontendWordState ac panCode wordCode bitmaps stack cfg)
      ac.isa panCode start globalsSize heapLen)
    (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact width F)
    (hst : decsStcnamesHOLExact [] panCode = some stCtxt)
    (decls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width F _
      {source with structs := stCtxt} (fun a => Classical.propDecidable (source.memaddrs a))
      panCode = some s_decls)
    (k : Nat) (result : Option (PanSemResultExact width))
    (post : PanSemStateFiniteExact width F)
    (run : PanSemStateFiniteExact.evaluateHOLFiniteState {s_decls with clock := k}
      (.call none start [] : ProgHOL width) = (result,post))
    (notError : panEntryClass result ≠ .RunError)
    (notTimeout : result ≠ some .timeOut)
    (assumptions : FullMakeInitSemantics.Assumptions scc dc maxHeap sp offset bitmaps
      stackCode lab saveRegs dataSp (fun _ => (cfg, [], [])))
    (memorySafe : MemorySafe storeConstsStubLocation lab.memDomain lab.memory) :
    let M := Stage4.codeStepBudget (FullMakeInitSemantics.code2 scc dc maxHeap sp offset stackCode)
    ∃ outcome, (LabSem.evaluate {lab with
      clock := 2 * (M + 1) * certifiedStackClock panCode start k + (3 * M + 2)}).1 = .halt outcome := by
  obtain ⟨outcome, complete⟩ := pan_to_certified_stack_complete ac wc panCode col wordCode bitmaps wconf
    fs stackCode scc dc maxHeap sp offset lab saveRegs dataSp cfg stack aux dimension
    registers isa wtw wts initialized defs terminal oracle fuel noLabels indirect checked entryBound oracleEq terminalCalls source start globalsSize heapLen front stCtxt s_decls
    hst decls k result post run notError notTimeout
  have bounded := pan_to_certified_lab_not_timeOut ac wc panCode col wordCode bitmaps wconf
    fs stackCode scc dc maxHeap sp offset lab saveRegs dataSp cfg stack aux dimension
    registers isa wtw wts initialized defs terminal oracle fuel noLabels indirect checked entryBound oracleEq terminalCalls source start globalsSize heapLen front stCtxt s_decls
    hst decls k result post run notError notTimeout assumptions memorySafe
  exact ⟨outcome, (full_make_init_halt_of_lab_not_timeOut initialized assumptions
    (certifiedStackClock panCode start k) _ _ outcome rfl complete _ bounded).1⟩


theorem pan_to_target_certified_affine_not_timeOut {F : Type}
    (ac : AsmConfigExact 64) (wc : WordToWord.Config) (panCode : List (DeclHOL 64))
    (col : List (Option (Spt Nat)))
    (wordCode : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (bitmaps : List (BitVec 64)) (wconf : WordToStack.Native.Config) (fs : List Nat)
    (stackCode : List (Nat × HolProg 64))
    (scc : StackToLab.Config) (dc : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec 64 × BitVec 64) (lab : LabSem.State 64 LabToTarget.Config F)
    (saveRegs : Nat → Bool) (dataSp : Nat) (cfg : LabToTarget.Config)
    (stack aux : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (dimension : goodDimindex 64) (registers : ac.avoidRegs.length + 13 ≤ ac.regCount)
    (isa : ac.isa ≠ .ag32)
    (wtw : WordToWord.compile wc ac (panToWordCompileProgHOL ac.isa panCode) = (col,wordCode))
    (wts : WordToStack.Native.compileNative ac false wordCode = (bitmaps,wconf,fs,stackCode))
    (initialized : FullMakeInit.fullMakeInit scc dc maxHeap sp offset bitmaps stackCode lab
      saveRegs dataSp (fun _ => (cfg, [], [])) = (stack, some aux))
    (defs : Option Nat → WordCostEffects.Effects)
    (terminal : Basis.Pure.MlString.MlString → Bool) (oracle : HolOracle F) (fuel : Nat)
    (noLabels : ∀ dest label, defs dest (.breakTo label) = none ∧ defs dest (.continueTo label) = none)
    (indirect : ∀ name, WordCostCertificates.Subeffects (defs (some name)) (defs none))
    (checked : ∀ entry ∈ panToWordCompileProgHOL ac.isa panCode,
      WordCostCheck.checkProgram defs terminal fuel
        (WordCostCompilerControl.preAllocation ac ac.twoRegArith entry.2.1 entry.2.2)
        (defs (some entry.1)) = true)
    (entryBound : ∀ exit, WordCostEffects.AtMost (defs (some BvlToBvi.initGlobalsLocation) exit) 1)
    (oracleEq : lab.ffi.oracle = oracle)
    (terminalCalls : WordCostEntryCertificate.TerminalOracle terminal oracle)
    (source : PanSemStateFiniteExact 64 F) (start : MlS)
    (globalsSize : Nat) (heapLen : BitVec 64)
    (front : FrontendRelation source (frontendWordState ac panCode wordCode bitmaps stack cfg)
      ac.isa panCode start globalsSize heapLen)
    (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact 64 F)
    (hst : decsStcnamesHOLExact [] panCode = some stCtxt)
    (decls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite 64 F _
      {source with structs := stCtxt} (fun a => Classical.propDecidable (source.memaddrs a))
      panCode = some s_decls)
    (k : Nat) (result : Option (PanSemResultExact 64))
    (post : PanSemStateFiniteExact 64 F)
    (run : PanSemStateFiniteExact.evaluateHOLFiniteState {s_decls with clock := k}
      (.call none start [] : ProgHOL 64) = (result,post))
    (notError : panEntryClass result ≠ .RunError)
    (notTimeout : result ≠ some .timeOut)
    (assumptions : FullMakeInitSemantics.Assumptions scc dc maxHeap sp offset bitmaps
      stackCode lab saveRegs dataSp (fun _ => (cfg, [], [])))
    (memorySafe : MemorySafe storeConstsStubLocation lab.memDomain lab.memory)
    (input : Guest.InputBlob) (ffi : HolFfiState F)
    (code code2 : LabProgHOL 64) (labs : Spt (Spt Nat)) (clock i cbspace : Nat)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool)
    (coracle : Nat → LabToTarget.Config × LabProgHOL 64)
    (names : List HolFfiName) (info shiftedInfo : List ShmemInfoNum)
    (labInit : lab = ConcreteBaseline.Initialized.initialLab input ffi code (progToBytes code2) cbspace t m dm sdm coracle)
    (init : Initialization ConcreteBaseline.baselineMachineConfig ConcreteBaseline.baselineInstalledState
      code code2 labs clock i cbspace t m dm sdm coracle
      names info shiftedInfo)
    (safe : LabProps.noInstall code) :
    let M := Stage4.codeStepBudget (FullMakeInitSemantics.code2 scc dc maxHeap sp offset stackCode)
    (evaluateTargetHOL ConcreteBaseline.baselineMachineConfig ffi
      (InitE.bootstrapSteps + 9 * (2 * (M + 1) * certifiedStackClock panCode start k + (3 * M + 2) + 1))
      (ConcreteBaseline.baselineInitialState input)).1 ≠ .timeOut := by
  have labComplete := pan_to_certified_lab_not_timeOut ac wc panCode col wordCode bitmaps wconf
    fs stackCode scc dc maxHeap sp offset lab saveRegs dataSp cfg stack aux dimension
    registers isa wtw wts initialized defs terminal oracle fuel noLabels indirect checked entryBound oracleEq terminalCalls source start globalsSize heapLen front stCtxt s_decls
    hst decls k result post run notError notTimeout assumptions memorySafe
  let M := Stage4.codeStepBudget (FullMakeInitSemantics.code2 scc dc maxHeap sp offset stackCode)
  let k_lab := 2 * (M + 1) * certifiedStackClock panCode start k + (3 * M + 2)
  have stackComplete := pan_to_certified_stack_complete ac wc panCode col wordCode bitmaps wconf
    fs stackCode scc dc maxHeap sp offset lab saveRegs dataSp cfg stack aux dimension
    registers isa wtw wts initialized defs terminal oracle fuel noLabels indirect checked entryBound oracleEq terminalCalls source start globalsSize heapLen front stCtxt s_decls
    hst decls k result post run notError notTimeout
  have ready := stack_complete_ready _ stackComplete
  have nonfail := CompletedNonfailure.lab_nonfail_of_ready scc dc maxHeap sp offset bitmaps
    stackCode lab saveRegs dataSp (fun _ => (cfg, [], [])) stack (some aux) initialized
    assumptions (certifiedStackClock panCode start k) ready.1 ready.2
  have labNotError := lab_run_not_error_of_nonfail lab nonfail k_lab
  rw [labInit] at labComplete labNotError
  exact ConcreteBaseline.Initialized.stage5_lab_to_target_affine_not_timeOut input ffi code code2 labs
    clock i cbspace t m dm sdm coracle names info shiftedInfo init safe k_lab labNotError
    labComplete


set_option pp.fullNames true
#print axioms word_to_stack_certified_complete
#print axioms pan_to_certified_lab_not_timeOut
#print axioms pan_to_certified_lab_complete
#print axioms pan_to_target_certified_affine_not_timeOut
end InitECandidate.Solver.Wave8GuestInv.CertifiedPipelineTransfer
