import InitECandidate.Solver.Wave8GuestInv.Target
import InitECandidate.Solver.Wave8GuestInv.FiniteRebudget
import InitECandidate.Solver.Wave8Stage.PipelineIntegration
import InitECandidate.Solver.Wave8Stage.WordCostPipelineCertificate
import InitECandidate.Solver.Wave8Stage.ConcreteWordCostData
import InitECandidate.Solver.Wave8Stage.WordSourceOracle

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.R12_Stage5AndBridgeArgon

open Classical InitE Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.LoopToWord.CompileCorrect Flapjack.LoopToWordStateRelImpSemanticsSupport
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenSemantics Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.RiscV.L3
open InitECandidate.Solver InitECandidate.Solver.Wave8Stage InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.SelfContainedStageBounds
open EntryClassTransfer InitializedPipelineTransfer InitializedLabTransfer
open RuntimeLabels InitializedTransfer PipelineInitialization WordCostEffects WordCostCertificates

/-! ## 1. Stage 5 Lab-to-Target Affine Transfer & Halt Agreement -/

theorem stage5_lab_to_target_affine_not_timeOut {F : Type} (c : Backend.Config)
    (mc : MachineConfig 64 riscv_state RiscVProjection) (target : mc.target = riscvTarget)
    (initial installed : riscv_state) (ffi : HolFfiState F)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64) (bitmapsDm sdm : BitVec 64 → Bool)
    (bytes : List (BitVec 8)) (cbspace : Nat) (ltconf output : LabToTarget.Config) (p : List (Nat × StackLang.HolProg 64))
    (compiled : LabToTarget.compile riscvConfig ltconf
      (pipelineLabInitState c mc ffi t m bitmapsDm sdm installed bytes cbspace ltconf p).code = some (bytes, output))
    (position : ltconf.pos = 0)
    (safe : LabProps.noInstall (pipelineLabInitState c mc ffi t m bitmapsDm sdm installed bytes cbspace ltconf p).code)
    (related : LabToTarget.stateRel
      (mc, CompileTransfer.compiledCode riscvConfig ltconf output
        (pipelineLabInitState c mc ffi t m bitmapsDm sdm installed bytes cbspace ltconf p).code
        bytes compiled, output.labels, mc.target.getPc installed)
      (UnfilteredTransfer.filtered mc
        (pipelineLabInitState c mc ffi t m bitmapsDm sdm installed bytes cbspace ltconf p)) t installed)
    (tied : oracleTie mc installed (pipelineLabInitState c mc ffi t m bitmapsDm sdm installed bytes cbspace ltconf p))
    (bootstrap k_lab : Nat)
    (bootstrapRun : ∀ fuel, evaluateTargetHOL mc ffi (bootstrap + fuel) initial = evaluateTargetHOL mc ffi fuel installed)
    (notError : (LabSem.evaluate
      {pipelineLabInitState c mc ffi t m bitmapsDm sdm installed bytes cbspace ltconf p with clock := k_lab}).1 ≠ .error)
    (notTimeout : (LabSem.evaluate
      {pipelineLabInitState c mc ffi t m bitmapsDm sdm installed bytes cbspace ltconf p with clock := k_lab}).1 ≠ .timeOut) :
    (evaluateTargetHOL mc ffi (bootstrap + 9 * (k_lab + 1)) initial).1 ≠ .timeOut :=
  PipelineTransfer.stage5_lab_to_target_affine_not_timeOut c mc target initial installed ffi
    t m bitmapsDm sdm bytes cbspace ltconf output p compiled position safe related tied
    bootstrap k_lab bootstrapRun notError notTimeout

theorem stage5_lab_to_target_affine_not_timeOut_of_halt {F : Type} (c : Backend.Config)
    (mc : MachineConfig 64 riscv_state RiscVProjection) (target : mc.target = riscvTarget)
    (initial installed : riscv_state) (ffi : HolFfiState F)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64) (bitmapsDm sdm : BitVec 64 → Bool)
    (bytes : List (BitVec 8)) (cbspace : Nat) (ltconf output : LabToTarget.Config) (p : List (Nat × StackLang.HolProg 64))
    (compiled : LabToTarget.compile riscvConfig ltconf
      (pipelineLabInitState c mc ffi t m bitmapsDm sdm installed bytes cbspace ltconf p).code = some (bytes, output))
    (position : ltconf.pos = 0)
    (safe : LabProps.noInstall (pipelineLabInitState c mc ffi t m bitmapsDm sdm installed bytes cbspace ltconf p).code)
    (related : LabToTarget.stateRel
      (mc, CompileTransfer.compiledCode riscvConfig ltconf output
        (pipelineLabInitState c mc ffi t m bitmapsDm sdm installed bytes cbspace ltconf p).code
        bytes compiled, output.labels, mc.target.getPc installed)
      (UnfilteredTransfer.filtered mc
        (pipelineLabInitState c mc ffi t m bitmapsDm sdm installed bytes cbspace ltconf p)) t installed)
    (tied : oracleTie mc installed (pipelineLabInitState c mc ffi t m bitmapsDm sdm installed bytes cbspace ltconf p))
    (bootstrap k_lab : Nat)
    (bootstrapRun : ∀ fuel, evaluateTargetHOL mc ffi (bootstrap + fuel) initial = evaluateTargetHOL mc ffi fuel installed)
    (outcome : HolOutcome)
    (halt : (LabSem.evaluate
      {pipelineLabInitState c mc ffi t m bitmapsDm sdm installed bytes cbspace ltconf p with clock := k_lab}).1 = .halt outcome) :
    (evaluateTargetHOL mc ffi (bootstrap + 9 * (k_lab + 1)) initial).1 ≠ .timeOut :=
  stage5_lab_to_target_affine_not_timeOut c mc target initial installed ffi t m bitmapsDm sdm
    bytes cbspace ltconf output p compiled position safe related tied bootstrap k_lab bootstrapRun
    (by rw [halt]; intro h; cases h) (by rw [halt]; intro h; cases h)

theorem stage5_target_halt_agree_of_not_timeOut {width : Nat} [NeZero width] {S Q σ : Type}
    (mc : MachineConfig width S Q) (ffi : HolFfiState σ) (ms : S) (outcome : HolOutcome) (events : List HolIoEvent)
    (hclocked : ∃ k_target ms2 ffi2,
      evaluateTargetHOL mc ffi k_target ms = (.halt outcome, ms2, ffi2) ∧ ffi2.ioEvents = events)
    (K : Nat) (hnt : (evaluateTargetHOL mc ffi K ms).1 ≠ .timeOut) :
    (evaluateTargetHOL mc ffi K ms).1 = .halt outcome ∧ (evaluateTargetHOL mc ffi K ms).2.2.ioEvents = events := by
  obtain ⟨k0, ms0, ffi0, run0, io0⟩ := hclocked
  rcases runK : evaluateTargetHOL mc ffi K ms with ⟨resK, msK, ffiK⟩
  rw [runK] at hnt
  have heq := evaluateTargetIgnoreClocks mc ffi K k0 ms resK (.halt outcome) msK ms0 ffiK ffi0
    ⟨runK, hnt, run0, by simp⟩
  exact ⟨congrArg Prod.fst heq, (congrArg (fun r => r.2.2.ioEvents) heq).trans io0⟩

/-! ## 2. Concrete WordCost Annotations & Certified Factor-2 Word-to-Stack-to-Lab Transfer -/

theorem summaries_noLabels : ∀ dest label,
    ConcreteWordCostAnnotations.summaries dest (.breakTo label) = none ∧
      ConcreteWordCostAnnotations.summaries dest (.continueTo label) = none := fun _ _ => ⟨rfl, rfl⟩

theorem summaries_indirect : ∀ name, Subeffects (ConcreteWordCostAnnotations.summaries (some name))
    (ConcreteWordCostAnnotations.summaries none) := by
  intro name exit cost covered
  cases exit <;> simp [ConcreteWordCostAnnotations.summaries, Covers] at covered ⊢
  all_goals repeat' first | split at covered | omega

theorem summaries_entryBound : ∀ exit,
    AtMost (ConcreteWordCostAnnotations.summaries (some BvlToBvi.initGlobalsLocation) exit) 1 := by
  have start : BvlToBvi.initGlobalsLocation = 64 := by decide
  rw [start]; intro exit cost covered
  cases exit <;> simp [ConcreteWordCostAnnotations.summaries, Covers] at covered <;> omega

noncomputable def certifiedStackClock {width : Nat} [NeZero width]
    (panCode : List (DeclHOL width)) (start : MlS) (clock : Nat) : Nat := 2 * wordClock panCode start clock

theorem word_to_stack_certified_complete {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (start registers clock : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F) (target : StackSemStateFiniteExact width C F)
    (related : WordToStackProofs.stateRel ac registers 0 0 source target [] 0)
    (noInstall : WordProps.noInstallCode source.code) (defs : Option Nat → WordCostEffects.Effects)
    (terminal : Basis.Pure.MlString.MlString → Bool) (oracle : HolOracle F)
    (certificates : WordCostEntryCertificate.CodeCertified defs terminal source.code)
    (terminalCalls : WordCostEntryCertificate.TerminalOracle terminal oracle) (oracleEq : source.ffi.oracle = oracle)
    (entryBound : ∀ exit, WordCostEffects.AtMost (defs (some start) exit) 1)
    (complete : ∃ outcome, wordEntryClass (WordSemStateFiniteExact.evaluate
      (.call none (some start) [0] none) {source with clock := clock}).1 = .CompleteResult outcome) :
    ∃ outcome, stackEntryClass (StackSemEvaluate.evaluate
      ((.call none (.inl start) none : HolProg width), {target with clock := 2 * clock})).1 =
        .CompleteResult outcome := by
  have notError : (WordSemStateFiniteExact.evaluate
      (.call none (some start) [0] none) {source with clock := clock}).1 ≠ some .error := by
    intro bad; obtain ⟨outcome, complete⟩ := complete; rw [bad] at complete; cases complete
  have notTimeout : (WordSemStateFiniteExact.evaluate
      (.call none (some start) [0] none) {source with clock := clock}).1 ≠ some .timeOut := by
    intro bad; obtain ⟨outcome, complete⟩ := complete; rw [bad] at complete; cases complete
  rcases run : WordSemStateFiniteExact.evaluate
      (.call none (some start) [0] none) {source with clock := clock} with ⟨result, post⟩
  rw [run] at complete notError
  obtain ⟨extra, extraBound, targetPost, targetResult, targetRun, _, _, contract⟩ :=
    WordToStackCostEntry.compCall ac start {source with clock := clock} registers result post
      {target with clock := clock} [] ⟨run, notError,
        WordToStackProofs.SemanticsHelpers.stateRelWithClock ac registers clock source target [] 0 related⟩
  have targetComplete : ∃ outcome, stackEntryClass targetResult = .CompleteResult outcome := by
    by_cases same : result.map compileResult = targetResult
    · rw [← same]; exact compiled_word_complete result complete
    · rw [if_neg same] at contract; rw [contract.1]; exact ⟨_, rfl⟩
  have targetNotTimeout := (stack_complete_ready targetResult targetComplete).2
  have cost := WordCostEntryCertificate.entryCost_bound defs terminal source.code oracle
    noInstall certificates terminalCalls start {source with clock := clock}
    ⟨rfl, oracleEq⟩ entryBound (by rw [run]; exact notError) notTimeout
  let budget := 2 * clock
  have enough : clock + extra ≤ budget := by
    dsimp only [budget]; change WordToStackSourceCost.sourceCost _ _ ≤ clock at cost; omega
  have lifted := Flapjack.Compiler.Backend.StackProps.evaluateAddClock (budget - (clock + extra))
    (.call none (.inl start) none) {target with clock := clock + extra} targetResult targetPost ⟨targetRun, targetNotTimeout⟩
  have clockEq : clock + extra + (budget - (clock + extra)) = budget := by omega
  simp only [clockEq] at lifted
  change ∃ outcome, stackEntryClass (StackSemEvaluate.evaluate
    ((.call none (.inl start) none : HolProg width), {target with clock := budget})).1 = .CompleteResult outcome
  rw [lifted]; exact targetComplete

theorem pan_to_certified_stack_complete {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (wc : WordToWord.Config) (panCode : List (DeclHOL width))
    (col : List (Option (Spt Nat))) (wordCode : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bitmaps : List (BitVec width)) (wconf : WordToStack.Native.Config) (fs : List Nat)
    (stackCode : List (Nat × HolProg width)) (scc : StackToLab.Config) (dc : DataToWord.Config)
    (maxHeap sp : Nat) (offset : BitVec width × BitVec width) (lab : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat) (cfg : C) (stack aux : StackSemStateFiniteExact width C F)
    (dimension : goodDimindex width) (registers : ac.avoidRegs.length + 13 ≤ ac.regCount) (isa : ac.isa ≠ .ag32)
    (wtw : WordToWord.compile wc ac (panToWordCompileProgHOL ac.isa panCode) = (col, wordCode))
    (wts : WordToStack.Native.compileNative ac false wordCode = (bitmaps, wconf, fs, stackCode))
    (initialized : FullMakeInit.fullMakeInit scc dc maxHeap sp offset bitmaps stackCode lab
      saveRegs dataSp (fun _ => (cfg, [], [])) = (stack, some aux))
    (defs : Option Nat → WordCostEffects.Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (oracle : HolOracle F) (fuel : Nat)
    (noLabels : ∀ dest label, defs dest (.breakTo label) = none ∧ defs dest (.continueTo label) = none)
    (indirect : ∀ name, WordCostCertificates.Subeffects (defs (some name)) (defs none))
    (checked : ∀ entry ∈ panToWordCompileProgHOL ac.isa panCode,
      WordCostCheck.checkProgram defs terminal fuel
        (WordCostCompilerControl.preAllocation ac ac.twoRegArith entry.2.1 entry.2.2) (defs (some entry.1)) = true)
    (entryBound : ∀ exit, WordCostEffects.AtMost (defs (some BvlToBvi.initGlobalsLocation) exit) 1)
    (oracleEq : lab.ffi.oracle = oracle) (terminalCalls : WordCostEntryCertificate.TerminalOracle terminal oracle)
    (source : PanSemStateFiniteExact width F) (start : MlS) (globalsSize : Nat) (heapLen : BitVec width)
    (front : FrontendRelation source (frontendWordState ac panCode wordCode bitmaps stack cfg)
      ac.isa panCode start globalsSize heapLen)
    (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact width F)
    (hst : decsStcnamesHOLExact [] panCode = some stCtxt)
    (decls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width F _
      {source with structs := stCtxt} (fun a => Classical.propDecidable (source.memaddrs a)) panCode = some s_decls)
    (k : Nat) (result : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width F)
    (run : PanSemStateFiniteExact.evaluateHOLFiniteState {s_decls with clock := k}
      (.call none start [] : ProgHOL width) = (result, post))
    (notError : panEntryClass result ≠ .RunError) (notTimeout : result ≠ some .timeOut) :
    ∃ outcome, stackEntryClass (StackSemEvaluate.evaluate
      ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
        {stack with clock := certifiedStackClock panCode start k})).1 = .CompleteResult outcome := by
  let pre := frontendWordState ac panCode wordCode bitmaps stack cfg
  let oldClock := (FrontendCostTransfer.frontBudget panCode start + 1) * k +
    (FrontendCostTransfer.frontBudget panCode start + 4)
  have oldClass := FrontendStackTransfer.pan_to_word_static_class source pre ac.isa panCode
    start globalsSize heapLen front stCtxt s_decls hst decls k result post run notError notTimeout
  have sourceComplete : ∃ outcome, panEntryClass result = .CompleteResult outcome := by
    cases result with | none => exact False.elim (notError rfl) | some r => cases r <;> simp_all [panEntryClass]
  have oldComplete : ∃ outcome, wordEntryClass (WordSemStateFiniteExact.evaluate
      (.call none (some firstLoopName) [0] none) {pre with clock := oldClock}).1 =
        .CompleteResult outcome := by rw [oldClass]; exact sourceComplete
  have oldNotTimeout : (WordSemStateFiniteExact.evaluate
      (.call none (some firstLoopName) [0] none) {pre with clock := oldClock}).1 ≠ some .timeOut := by
    obtain ⟨outcome, complete⟩ := oldComplete; intro bad; rw [bad] at complete; cases complete
  have frontBound := FrontendStaticBudget.frontBudget_le_staticFrontBudget panCode start
  have enough : oldClock ≤ wordClock panCode start k :=
    Nat.add_le_add (Nat.mul_le_mul_right k (Nat.add_le_add_right frontBound 1)) (Nat.add_le_add_right frontBound 4)
  rcases oldRun : WordSemStateFiniteExact.evaluate
      (.call none (some firstLoopName) [0] none) {pre with clock := oldClock} with ⟨r, t⟩
  have lift := WordSemStateFiniteExact.evaluate_add_clock (wordClock panCode start k - oldClock)
    (.call none (some firstLoopName) [0] none) {pre with clock := oldClock} r t
    ⟨oldRun, by rw [oldRun] at oldNotTimeout; exact oldNotTimeout⟩
  have clockEq : oldClock + (wordClock panCode start k - oldClock) = wordClock panCode start k :=
    Nat.add_sub_of_le enough
  simp only [clockEq] at lift
  have preComplete : ∃ outcome, wordEntryClass (WordSemStateFiniteExact.evaluate
      (.call none (some firstLoopName) [0] none) {pre with clock := wordClock panCode start k}).1 =
        .CompleteResult outcome := by rw [lift]; rw [oldRun] at oldComplete; exact oldComplete
  have preNotError : (WordSemStateFiniteExact.evaluate
      (.call none (some firstLoopName) [0] none) {pre with clock := wordClock panCode start k}).1 ≠ some .error := by
    obtain ⟨outcome, complete⟩ := preComplete; intro bad; rw [bad] at complete; cases complete
  have facts := panToTargetWordStateFacts ac (ac.regCount - (5 + ac.avoidRegs.length))
    (sptFromAList wordCode) (fun _ => ((bitmaps.length, cfg), [])) scc dc maxHeap sp
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
    change ∃ outcome, wordEntryClass (WordSemStateFiniteExact.evaluate (.call none (some firstLoopName) [0] none)
      {pre with clock := wordClock panCode start k, code := sptFromAList wordCode}).1 = _
    rw [agree.1]; exact preComplete
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
  exact word_to_stack_certified_complete ac firstLoopName _ (wordClock panCode start k) _ stack related
    (WordToStackCompileBudget.compile_noInstall wc ac _ col wordCode wtw
      (PanToWord.pan_to_word_compile_prog_no_install_code _ panCode _ rfl)
      (PanToWord.pan_to_word_compile_prog_no_mt_code _ panCode _ rfl))
    defs terminal oracle certificates terminalCalls ((congrArg (·.oracle) ffiEq).trans oracleEq) entryBound allocatedComplete

theorem pan_to_certified_lab_not_timeOut {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (wc : WordToWord.Config) (panCode : List (DeclHOL width))
    (col : List (Option (Spt Nat))) (wordCode : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bitmaps : List (BitVec width)) (wconf : WordToStack.Native.Config) (fs : List Nat)
    (stackCode : List (Nat × HolProg width)) (scc : StackToLab.Config) (dc : DataToWord.Config)
    (maxHeap sp : Nat) (offset : BitVec width × BitVec width) (lab : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat) (cfg : C) (stack aux : StackSemStateFiniteExact width C F)
    (dimension : goodDimindex width) (registers : ac.avoidRegs.length + 13 ≤ ac.regCount) (isa : ac.isa ≠ .ag32)
    (wtw : WordToWord.compile wc ac (panToWordCompileProgHOL ac.isa panCode) = (col, wordCode))
    (wts : WordToStack.Native.compileNative ac false wordCode = (bitmaps, wconf, fs, stackCode))
    (initialized : FullMakeInit.fullMakeInit scc dc maxHeap sp offset bitmaps stackCode lab
      saveRegs dataSp (fun _ => (cfg, [], [])) = (stack, some aux))
    (defs : Option Nat → WordCostEffects.Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (oracle : HolOracle F) (fuel : Nat)
    (noLabels : ∀ dest label, defs dest (.breakTo label) = none ∧ defs dest (.continueTo label) = none)
    (indirect : ∀ name, WordCostCertificates.Subeffects (defs (some name)) (defs none))
    (checked : ∀ entry ∈ panToWordCompileProgHOL ac.isa panCode,
      WordCostCheck.checkProgram defs terminal fuel
        (WordCostCompilerControl.preAllocation ac ac.twoRegArith entry.2.1 entry.2.2) (defs (some entry.1)) = true)
    (entryBound : ∀ exit, WordCostEffects.AtMost (defs (some BvlToBvi.initGlobalsLocation) exit) 1)
    (oracleEq : lab.ffi.oracle = oracle) (terminalCalls : WordCostEntryCertificate.TerminalOracle terminal oracle)
    (source : PanSemStateFiniteExact width F) (start : MlS) (globalsSize : Nat) (heapLen : BitVec width)
    (front : FrontendRelation source (frontendWordState ac panCode wordCode bitmaps stack cfg)
      ac.isa panCode start globalsSize heapLen)
    (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact width F)
    (hst : decsStcnamesHOLExact [] panCode = some stCtxt)
    (decls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width F _
      {source with structs := stCtxt} (fun a => Classical.propDecidable (source.memaddrs a)) panCode = some s_decls)
    (k : Nat) (result : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width F)
    (run : PanSemStateFiniteExact.evaluateHOLFiniteState {s_decls with clock := k}
      (.call none start [] : ProgHOL width) = (result, post))
    (notError : panEntryClass result ≠ .RunError) (notTimeout : result ≠ some .timeOut)
    (assumptions : FullMakeInitSemantics.Assumptions scc dc maxHeap sp offset bitmaps
      stackCode lab saveRegs dataSp (fun _ => (cfg, [], [])))
    (memorySafe : MemorySafe storeConstsStubLocation lab.memDomain lab.memory) :
    let M := Stage4.codeStepBudget (FullMakeInitSemantics.code2 scc dc maxHeap sp offset stackCode)
    (LabSem.evaluate {lab with
      clock := 2 * (M + 1) * certifiedStackClock panCode start k + (3 * M + 2)}).1 ≠ .timeOut := by
  have complete := pan_to_certified_stack_complete ac wc panCode col wordCode bitmaps wconf
    fs stackCode scc dc maxHeap sp offset lab saveRegs dataSp cfg stack aux dimension
    registers isa wtw wts initialized defs terminal oracle fuel noLabels indirect checked
    entryBound oracleEq terminalCalls source start globalsSize heapLen front stCtxt s_decls
    hst decls k result post run notError notTimeout
  have ready := stack_complete_ready _ complete
  have compiled : stackCode = (WordToStack.Native.compileNative ac false
      (WordToWord.compile wc ac (panToWordCompileProgHOL ac.isa panCode)).2).2.2.2 := by rw [wtw, wts]
  have bridge := Stage4.fullMakeInit_lab_affine_of_source_run scc dc maxHeap sp offset
    bitmaps stackCode lab saveRegs dataSp (fun _ => (cfg, [], [])) assumptions
    ac false wc ac.isa panCode compiled memorySafe (fun _ => rfl) (certifiedStackClock panCode start k)
  simp only [initialized] at bridge; exact bridge ready.1 ready.2

/-! ## 3. End-to-End `K_pan` to `K_target` Bridge & `StageTransfer` -/

theorem lab_not_timeOut_mono {width : Nat} [NeZero width] {C F : Type}
    (lab : LabSem.State width C F) {k₁ k₂ : Nat} (hle : k₁ ≤ k₂)
    (hnt : (LabSem.evaluate {lab with clock := k₁}).1 ≠ .timeOut) :
    (LabSem.evaluate {lab with clock := k₂}).1 ≠ .timeOut := by
  have hadd := LabProps.evaluateAddClock {lab with clock := k₁} _ _ (k₂ - k₁) ⟨rfl, hnt⟩
  have hclk : k₁ + (k₂ - k₁) = k₂ := Nat.add_sub_of_le hle
  simp only [hclk] at hadd; rw [hadd]; exact hnt

theorem K_target_budget_identity :
    23077 + 9 * (2 * (7313 + 1) * (2 * ((448 + 1) * K_pan + (448 + 4))) + (3 * 7313 + 2) + 1) = K_target := by
  unfold K_target; omega

theorem source_not_timeOut_K_pan : UniformSourceClock.CoveredSourceUniformNotTimeOut K_pan :=
  UniformSourceClock.covered_source_uniform_not_timeOut_of_has_clock_within
    (UniformSourceClock.covered_source_has_clock_within_of_ticks_bounded coveredSourceTicksConsumedBounded_K_pan)

theorem stageTransfer_of_uniform_target_bound (sub : Submission)
    (h : ∀ (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent),
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      sourceBehaviour input = .terminate outcome events → coveredOutcome outcome →
      ∀ (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory)
        (result : Option (PanSemResultExact 64)) (post : PanSemStateFiniteExact 64 Guest.HostMemory),
        decsStcnamesHOLExact [] sourceDeclarations = some stCtxt →
        @PanSemStateFiniteExact.evaluateDeclsHOLFinite 64 Guest.HostMemory _
          {sourceInitialState input with structs := stCtxt}
          (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a)) sourceDeclarations = some s_decls →
        PanSemStateFiniteExact.evaluateHOLFiniteState {s_decls with clock := K_pan}
          (.call none (ofString "main") [] : ProgHOL 64) = (result, post) →
        panEntryClass result = .CompleteResult outcome → result ≠ some .timeOut →
        (evaluateTargetHOL sub.machineConfig (sourceFfi input) K_target (sub.initialState input)).1 ≠ .timeOut) :
    UniformSourceClock.CoveredSourceUniformNotTimeOut K_pan → FiniteRebudget.UniformNotTimeOut sub K_target := by
  intro hpan input hgas outcome events hsource hcov
  obtain ⟨stCtxt, s_decls, res, s_post, hst, hdecls, hrun, hclass, _⟩ :=
    UniformSourceClock.covered_source_uniform_terminates_of_uniform_not_timeOut hpan input outcome events hgas hsource hcov
  have hnt : res ≠ some .timeOut := by intro ht; subst ht; cases hclass
  exact h input outcome events hgas hsource hcov stCtxt s_decls res s_post hst hdecls hrun hclass hnt

end InitECandidate.Solver.Wave8Stage.R12_Stage5AndBridgeArgon
