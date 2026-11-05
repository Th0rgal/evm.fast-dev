import InitECandidate.Solver.Wave8Stage.R12_Stage1To2BoundArgon
import InitECandidate.Solver.Wave8GuestInv.CertifiedPipelineTransfer
import InitECandidate.Solver.Wave8Stage.ConcreteWordCheckInput
import InitECandidate.Solver.Wave8Stage.WordSourceOracle

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 200000

namespace InitECandidate.Solver.Wave8Stage.Stage5BridgeArgon
open Classical InitE InitECandidate.Proofs
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Pancake.Proofs.PanToTarget
open InitECandidate.Solver InitECandidate.Solver.Wave8GuestInv InitECandidate.Solver.Wave8Stage

theorem stages_noLabels (dest : Option Nat) (label : Nat) :
    ConcreteWordCostAnnotations.summaries dest (.breakTo label) = none ∧
      ConcreteWordCostAnnotations.summaries dest (.continueTo label) = none := by
  cases dest <;> exact ⟨rfl, rfl⟩

theorem stages_indirect (name : Nat) :
    WordCostCertificates.Subeffects (ConcreteWordCostAnnotations.summaries (some name))
      (ConcreteWordCostAnnotations.summaries none) := by
  intro exit
  cases exit <;> simp [ConcreteWordCostAnnotations.summaries]
  intro cost hcost
  by_cases h66 : name = 66 <;> by_cases h90 : name = 90 <;>
    simp [h66, h90] at hcost <;> omega

theorem stages_entryBound (exit : WordCostEffects.Exit) :
    WordCostEffects.AtMost
      (ConcreteWordCostAnnotations.summaries (some BvlToBvi.initGlobalsLocation) exit) 1 := by
  have h66 : BvlToBvi.initGlobalsLocation ≠ 66 := by decide
  have h90 : BvlToBvi.initGlobalsLocation ≠ 90 := by decide
  cases exit <;> simp [ConcreteWordCostAnnotations.summaries, WordCostEffects.AtMost, h66, h90]

theorem lab_clock_le_of_bounds (M k_word k_pan : Nat)
    (hM : M ≤ 7313) (hword : k_word ≤ 449 * k_pan + 452) :
    2 * (M + 1) * (2 * k_word) + (3 * M + 2) ≤
      2 * (7313 + 1) * (2 * (449 * k_pan + 452)) + (3 * 7313 + 2) := by
  have h1 : 2 * (M + 1) ≤ 2 * (7313 + 1) := by omega
  have h2 : 2 * k_word ≤ 2 * (449 * k_pan + 452) := by omega
  have h3 := Nat.mul_le_mul h1 h2
  omega

theorem lab_not_timeOut_and_not_error_of_halt {width : Nat} [NeZero width] {C F : Type}
    (lab : LabSem.State width C F) {k₁ k₂ : Nat} (hle : k₁ ≤ k₂)
    {outcome : HolOutcome}
    (hhalt : (LabSem.evaluate {lab with clock := k₁}).1 = .halt outcome) :
    (LabSem.evaluate {lab with clock := k₂}).1 ≠ .timeOut ∧
      (LabSem.evaluate {lab with clock := k₂}).1 ≠ .error := by
  have hnt₁ : (LabSem.evaluate {lab with clock := k₁}).1 ≠ .timeOut := by
    rw [hhalt]; intro h; cases h
  have hadd := LabProps.evaluateAddClock {lab with clock := k₁} _ _ (k₂ - k₁) ⟨rfl, hnt₁⟩
  have hclk : k₁ + (k₂ - k₁) = k₂ := Nat.add_sub_of_le hle
  simp only [hclk] at hadd
  have hhalt₂ : (LabSem.evaluate {lab with clock := k₂}).1 = .halt outcome :=
    (congrArg Prod.fst hadd).trans hhalt
  exact ⟨(by rw [hhalt₂]; intro h; cases h), (by rw [hhalt₂]; intro h; cases h)⟩

theorem lab_bounds_from_frontend
    (input : Guest.InputBlob) (k_pan : Nat) (c : Backend.Config)
    (col : List (Option (Spt Nat)))
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (wconf : WordToStack.Native.Config) (fs : List Nat) (p : List (Nat × HolProg 64))
    (ltconf : LabToTarget.Config) (lab_post : LabSem.State 64 LabToTarget.Config Guest.HostMemory)
    (stack_post aux_post : StackSemStateFiniteExact 64 LabToTarget.Config Guest.HostMemory)
    (hwtw : WordToWord.compile c.wordToWordConf riscvConfig
      (panToWordCompileProgHOL riscvConfig.isa sourceDeclarations) = (col, wprog))
    (hwts : WordToStack.Native.compileNative riscvConfig false wprog =
      (InitECandidate.bitmaps, wconf, fs, p))
    (hinit_post : FullMakeInit.fullMakeInit c.stackConf c.dataConf
      (2 * DataToWord.maxHeapLimit 64 c.dataConf - 1)
      (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset
      InitECandidate.bitmaps p lab_post
      (fun k => decide (k ∈ FastEnv.baselineMachineConfig.calleeSavedRegs)) 0
      (fun _ => (ltconf, [], [])) = (stack_post, some aux_post))
    (hA_post : FullMakeInitSemantics.Assumptions c.stackConf c.dataConf
      (2 * DataToWord.maxHeapLimit 64 c.dataConf - 1)
      (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset
      InitECandidate.bitmaps p lab_post
      (fun k => decide (k ∈ FastEnv.baselineMachineConfig.calleeSavedRegs)) 0
      (fun _ => (ltconf, [], [])))
    (hsafe_mem_post : RuntimeLabels.MemorySafe storeConstsStubLocation lab_post.memDomain lab_post.memory)
    (horacle : lab_post.ffi.oracle = InitE.sourceOracle)
    (heapLen_bv : BitVec 64)
    (hfront_post : InitializedPipelineTransfer.FrontendRelation
      (sourceInitialState input)
      (InitializedPipelineTransfer.frontendWordState riscvConfig sourceDeclarations
        wprog InitECandidate.bitmaps stack_post ltconf)
      riscvConfig.isa sourceDeclarations (ofString "main") globalsWords heapLen_bv)
    (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory)
    (hst : decsStcnamesHOLExact [] sourceDeclarations = some stCtxt)
    (hdecls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite 64 Guest.HostMemory _
      {sourceInitialState input with structs := stCtxt}
      (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
      sourceDeclarations = some s_decls)
    (res : Option (PanSemResultExact 64)) (s_post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (hrun : PanSemStateFiniteExact.evaluateHOLFiniteState {s_decls with clock := k_pan}
      (.call none (ofString "main") [] : ProgHOL 64) = (res, s_post))
    (hne_pan : panEntryClass res ≠ .RunError) (hnt_pan : res ≠ some .timeOut)
    (h_front : FrontendStaticBudget.listBudget ConcreteCompilerCrep.source ≤ 448)
    (h_word_all : ConcreteCompilerWord.source.all ConcreteWordCheckInput.check = true)
    (hM_bound : Stage4.codeStepBudget (FullMakeInitSemantics.code2 c.stackConf c.dataConf
      (2 * DataToWord.maxHeapLimit 64 c.dataConf - 1)
      (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset p) ≤ 7313) :
    let k_lab_max := 2 * (7313 + 1) * (2 * (449 * k_pan + 452)) + (3 * 7313 + 2)
    (LabSem.evaluate {lab_post with clock := k_lab_max}).1 ≠ .timeOut ∧
      (LabSem.evaluate {lab_post with clock := k_lab_max}).1 ≠ .error := by
  intro k_lab_max
  have hregs : riscvConfig.avoidRegs.length + 13 ≤ riscvConfig.regCount := by decide
  have hisa : riscvConfig.isa ≠ .ag32 := by rintro h; cases h
  obtain ⟨outcome, hhalt⟩ := CertifiedPipelineTransfer.pan_to_certified_lab_complete
    riscvConfig c.wordToWordConf sourceDeclarations col wprog InitECandidate.bitmaps
    wconf fs p c.stackConf c.dataConf (2 * DataToWord.maxHeapLimit 64 c.dataConf - 1)
    (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset
    lab_post (fun k => decide (k ∈ FastEnv.baselineMachineConfig.calleeSavedRegs)) 0 ltconf
    stack_post aux_post (Or.inr rfl) hregs hisa hwtw hwts hinit_post
    ConcreteWordCostAnnotations.summaries WordSourceOracle.terminal
    InitE.sourceOracle 20000 stages_noLabels stages_indirect
    (ConcreteWordCheckInput.original_of_all h_word_all) stages_entryBound horacle
    WordSourceOracle.terminalOracle (sourceInitialState input) (ofString "main")
    globalsWords heapLen_bv hfront_post stCtxt s_decls hst hdecls k_pan res s_post hrun
    hne_pan hnt_pan hA_post hsafe_mem_post
  have h_static : FrontendStaticBudget.staticFrontBudget sourceDeclarations (ofString "main") ≤ 448 := by
    rw [R12_Stage1To2BoundArgon.staticFrontBudget_sourceDeclarations_eq]
    exact h_front
  have h_word_bound := (R12_Stage1To2BoundArgon.wordClock_and_certifiedStackClock_bound h_static k_pan).1
  exact lab_not_timeOut_and_not_error_of_halt lab_post
    (lab_clock_le_of_bounds _ _ k_pan hM_bound h_word_bound) hhalt

end InitECandidate.Solver.Wave8Stage.Stage5BridgeArgon
