/- Pinned Stages 1–4 interface: bc8ae0cd62497bcb269a76b63007730c579c324f.
Check with the unchanged integration sources and the Stage 5 sources. -/
import InitECandidate.Solver.Wave8GuestInv.InitializedLabTransfer
import InitECandidate.Solver.Wave8Stage.Stage5Transfer
import InitECandidate.Solver.Wave8Stage.ConcreteBaseline.InitializedTransfer
import InitECandidate.Solver.Wave8Stage.CompletedNonfailure

/-! Compose the initialized frontend/Word/Stack result with Stage4.
Original frontend, initialization and memory premises remain explicit. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteIntegration
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
      (InitE.bootstrapSteps + 9 * (2 * (M + 1) * stackClock panCode start wordCode k + (3 * M + 2) + 1))
      (ConcreteBaseline.baselineInitialState input)).1 ≠ .timeOut := by
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
  rw [labInit] at labComplete labNotError
  exact ConcreteBaseline.Initialized.stage5_lab_to_target_affine_not_timeOut input ffi code code2 labs
    clock i cbspace t m dm sdm coracle names info shiftedInfo init safe k_lab labNotError
    labComplete

set_option pp.fullNames true
end InitECandidate.Solver.Wave8Stage.ConcreteIntegration
