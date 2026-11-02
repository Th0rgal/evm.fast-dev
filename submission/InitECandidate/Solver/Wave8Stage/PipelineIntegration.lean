/- Pinned Stages 1–4 interface: bc8ae0cd62497bcb269a76b63007730c579c324f.
Check with the unchanged integration sources and the Stage 5 sources. -/
import InitECandidate.Solver.Wave8GuestInv.InitializedLabTransfer
import InitECandidate.Solver.Wave8Stage.Stage5Transfer
import InitECandidate.Solver.Wave8Stage.CompletedNonfailure
import InitECandidate.Solver.Wave8Stage.PipelineTransfer

/-! Compose the initialized frontend/Word/Stack result with Stage4.
Original frontend, initialization and memory premises remain explicit. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8Stage.PipelineIntegration
open Classical InitE Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack.Pancake.Proofs.PanToTarget Flapjack.LoopToWord.CompileCorrect
open Flapjack.LoopToWordStateRelImpSemanticsSupport
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenSemantics
open InitECandidate.Solver.Wave8Stage
open InitECandidate.Solver.SelfContainedStageBounds
open InitECandidate.Solver.Wave8GuestInv.EntryClassTransfer

open InitECandidate.Solver.Wave8GuestInv.InitializedPipelineTransfer
open InitECandidate.Solver.Wave8Stage.RuntimeLabels


open InitECandidate.Solver.Wave8GuestInv.InitializedLabTransfer
open InitECandidate.Solver.Wave8Stage.InitializedTransfer
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.RiscV.L3

theorem pan_to_target_affine_not_timeOut {F : Type}
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
    (mc : MachineConfig 64 riscv_state RiscVProjection) (target : mc.target = riscvTarget)
    (initial installed : riscv_state) (ffi : HolFfiState F)
    (c : Backend.Config) (bytes : List (BitVec 8)) (cbspace : Nat) (output : LabToTarget.Config)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool)
    (pipeline : lab = PipelineInitialization.pipelineLabInitState c mc ffi t m dm sdm
      installed bytes cbspace cfg stackCode)
    (compiled : LabToTarget.compile riscvConfig cfg lab.code = some (bytes, output))
    (position : cfg.pos = 0) (safe : LabProps.noInstall lab.code)
    (related : LabToTarget.stateRel
      (mc, CompileTransfer.compiledCode riscvConfig cfg output lab.code bytes compiled,
        output.labels, mc.target.getPc installed)
      (UnfilteredTransfer.filtered mc lab) t installed)
    (tied : oracleTie mc installed lab)
    (bootstrap : Nat)
    (bootstrapRun : ∀ fuel, evaluateTargetHOL mc ffi (bootstrap + fuel) initial =
      evaluateTargetHOL mc ffi fuel installed) :
    let M := Stage4.codeStepBudget (FullMakeInitSemantics.code2 scc dc maxHeap sp offset stackCode)
    (evaluateTargetHOL mc ffi
      (bootstrap + 9 * (2 * (M + 1) * stackClock panCode start wordCode k + (3 * M + 2) + 1))
      initial).1 ≠ .timeOut := by
  have labComplete := pan_to_initialized_lab_not_timeOut ac wc panCode col wordCode bitmaps wconf
    fs stackCode scc dc maxHeap sp offset lab saveRegs dataSp cfg stack aux dimension
    registers isa wtw wts initialized source start globalsSize heapLen front stCtxt s_decls
    hst decls k result post run notError notTimeout assumptions memorySafe
  let M := Stage4.codeStepBudget (FullMakeInitSemantics.code2 scc dc maxHeap sp offset stackCode)
  let k_lab := 2 * (M + 1) * stackClock panCode start wordCode k + (3 * M + 2)
  have stackComplete := pan_to_initialized_stack_complete ac wc panCode col wordCode bitmaps wconf
    fs stackCode scc dc maxHeap sp offset lab saveRegs dataSp cfg stack aux dimension
    registers isa wtw wts initialized source start globalsSize heapLen front stCtxt s_decls
    hst decls k result post run notError notTimeout
  have ready := stack_complete_ready _ stackComplete
  have nonfail := CompletedNonfailure.lab_nonfail_of_ready scc dc maxHeap sp offset bitmaps
    stackCode lab saveRegs dataSp (fun _ => (cfg, [], [])) stack (some aux) initialized
    assumptions (stackClock panCode start wordCode k) ready.1 ready.2
  have labNotError := lab_run_not_error_of_nonfail lab nonfail k_lab
  have ffiEq : lab.ffi = ffi := by rw [pipeline]; rfl
  have compiler : lab.compile = LabToTarget.compile mc.target.config := by rw [pipeline]; rfl
  have failed : lab.failed = false := by rw [pipeline]; rfl
  have boot : ∀ fuel, evaluateTargetHOL mc lab.ffi (bootstrap + fuel) initial =
      evaluateTargetHOL mc lab.ffi fuel installed := by simpa only [ffiEq] using bootstrapRun
  have transferred := CompileTransfer.stage5_lab_to_target_affine_not_timeOut mc target
    initial installed lab t cfg output bytes compiled position safe compiler failed related tied
    bootstrap k_lab boot labNotError labComplete
  simpa only [ffiEq] using transferred

set_option pp.fullNames true
end InitECandidate.Solver.Wave8Stage.PipelineIntegration
