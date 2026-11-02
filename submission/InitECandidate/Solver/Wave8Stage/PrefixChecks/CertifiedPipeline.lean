import InitECandidate.Solver.Wave8Stage.PrefixChecks.AllChecked
import InitECandidate.Solver.Wave8GuestInv.CertifiedPipelineTransfer

/-! Specialize integration's certified transfers to the concrete guest, target,
summary annotations, terminal oracle and kernel-checked prefix certificates.
The compiler equations and initialized-state assumptions retain their original
meaning. No Boolean certificate premise remains in these bridge theorems. -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace InitECandidate.Solver.Wave8Stage.PrefixChecks.CertifiedPipeline
open InitE Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.StackToLab.Proofs
open InitECandidate.Solver.Wave8Stage
open InitECandidate.Solver.Wave8GuestInv

section
variable {C : Type}
    (wc : WordToWord.Config) (col : List (Option (Spt Nat)))
    (wordCode : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (wconf : WordToStack.Native.Config) (fs : List Nat)
    (stackCode : List (Nat × StackLang.HolProg 64))
    (scc : StackToLab.Config) (dc : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec 64 × BitVec 64) (lab : LabSem.State 64 C Guest.HostMemory)
    (saveRegs : Nat → Bool) (dataSp : Nat) (cfg : C)
    (stack aux : StackSemStateFiniteExact 64 C Guest.HostMemory)
    (wtw : WordToWord.compile wc riscvConfig
      (panToWordCompileProgHOL riscvConfig.isa sourceDeclarations) = (col,wordCode))
    (wts : WordToStack.Native.compileNative riscvConfig false wordCode =
      (InitECandidate.bitmaps,wconf,fs,stackCode))
    (initialized : FullMakeInit.fullMakeInit scc dc maxHeap sp offset InitECandidate.bitmaps
      stackCode lab saveRegs dataSp (fun _ => (cfg, [], [])) = (stack,some aux))
    (oracleEq : lab.ffi.oracle = sourceOracle)
include wc col wordCode wconf fs stackCode scc dc maxHeap sp offset lab saveRegs dataSp
  cfg stack aux wtw wts initialized oracleEq

theorem initialized_certified_word_to_stack_complete_concrete (clock : Nat) :
    type_of% (CertifiedPipelineTransfer.initialized_certified_word_to_stack_complete (C := C) (F := Guest.HostMemory)
      riscvConfig wc sourceDeclarations col wordCode InitECandidate.bitmaps wconf fs stackCode
      scc dc maxHeap sp offset lab saveRegs dataSp cfg stack aux BvlToBvi.initGlobalsLocation clock
      (Or.inr rfl) (by decide) (by decide) wtw wts initialized
      ConcreteWordCostAnnotations.summaries WordSourceOracle.terminal sourceOracle 20000
      ConcreteWordCostAnnotations.noLabels ConcreteWordCostAnnotations.indirect
      InitECandidate.Solver.Wave8Stage.PrefixChecks.checked
      ConcreteWordCostAnnotations.entryBound oracleEq WordSourceOracle.terminalOracle) :=
  CertifiedPipelineTransfer.initialized_certified_word_to_stack_complete (C := C) (F := Guest.HostMemory)
      riscvConfig wc sourceDeclarations col wordCode InitECandidate.bitmaps wconf fs stackCode
      scc dc maxHeap sp offset lab saveRegs dataSp cfg stack aux BvlToBvi.initGlobalsLocation clock
      (Or.inr rfl) (by decide) (by decide) wtw wts initialized
      ConcreteWordCostAnnotations.summaries WordSourceOracle.terminal sourceOracle 20000
      ConcreteWordCostAnnotations.noLabels ConcreteWordCostAnnotations.indirect
      InitECandidate.Solver.Wave8Stage.PrefixChecks.checked
      ConcreteWordCostAnnotations.entryBound oracleEq WordSourceOracle.terminalOracle

theorem pan_to_certified_stack_complete_concrete :
    type_of% (CertifiedPipelineTransfer.pan_to_certified_stack_complete (C := C) (F := Guest.HostMemory)
      riscvConfig wc sourceDeclarations col wordCode InitECandidate.bitmaps wconf fs stackCode
      scc dc maxHeap sp offset lab saveRegs dataSp cfg stack aux
      (Or.inr rfl) (by decide) (by decide) wtw wts initialized
      ConcreteWordCostAnnotations.summaries WordSourceOracle.terminal sourceOracle 20000
      ConcreteWordCostAnnotations.noLabels ConcreteWordCostAnnotations.indirect
      InitECandidate.Solver.Wave8Stage.PrefixChecks.checked
      ConcreteWordCostAnnotations.entryBound oracleEq WordSourceOracle.terminalOracle) :=
  CertifiedPipelineTransfer.pan_to_certified_stack_complete (C := C) (F := Guest.HostMemory)
      riscvConfig wc sourceDeclarations col wordCode InitECandidate.bitmaps wconf fs stackCode
      scc dc maxHeap sp offset lab saveRegs dataSp cfg stack aux
      (Or.inr rfl) (by decide) (by decide) wtw wts initialized
      ConcreteWordCostAnnotations.summaries WordSourceOracle.terminal sourceOracle 20000
      ConcreteWordCostAnnotations.noLabels ConcreteWordCostAnnotations.indirect
      InitECandidate.Solver.Wave8Stage.PrefixChecks.checked
      ConcreteWordCostAnnotations.entryBound oracleEq WordSourceOracle.terminalOracle

theorem pan_to_certified_lab_not_timeOut_concrete :
    type_of% (CertifiedPipelineTransfer.pan_to_certified_lab_not_timeOut (C := C) (F := Guest.HostMemory)
      riscvConfig wc sourceDeclarations col wordCode InitECandidate.bitmaps wconf fs stackCode
      scc dc maxHeap sp offset lab saveRegs dataSp cfg stack aux
      (Or.inr rfl) (by decide) (by decide) wtw wts initialized
      ConcreteWordCostAnnotations.summaries WordSourceOracle.terminal sourceOracle 20000
      ConcreteWordCostAnnotations.noLabels ConcreteWordCostAnnotations.indirect
      InitECandidate.Solver.Wave8Stage.PrefixChecks.checked
      ConcreteWordCostAnnotations.entryBound oracleEq WordSourceOracle.terminalOracle) :=
  CertifiedPipelineTransfer.pan_to_certified_lab_not_timeOut (C := C) (F := Guest.HostMemory)
      riscvConfig wc sourceDeclarations col wordCode InitECandidate.bitmaps wconf fs stackCode
      scc dc maxHeap sp offset lab saveRegs dataSp cfg stack aux
      (Or.inr rfl) (by decide) (by decide) wtw wts initialized
      ConcreteWordCostAnnotations.summaries WordSourceOracle.terminal sourceOracle 20000
      ConcreteWordCostAnnotations.noLabels ConcreteWordCostAnnotations.indirect
      InitECandidate.Solver.Wave8Stage.PrefixChecks.checked
      ConcreteWordCostAnnotations.entryBound oracleEq WordSourceOracle.terminalOracle

theorem pan_to_certified_lab_complete_concrete :
    type_of% (CertifiedPipelineTransfer.pan_to_certified_lab_complete (C := C) (F := Guest.HostMemory)
      riscvConfig wc sourceDeclarations col wordCode InitECandidate.bitmaps wconf fs stackCode
      scc dc maxHeap sp offset lab saveRegs dataSp cfg stack aux
      (Or.inr rfl) (by decide) (by decide) wtw wts initialized
      ConcreteWordCostAnnotations.summaries WordSourceOracle.terminal sourceOracle 20000
      ConcreteWordCostAnnotations.noLabels ConcreteWordCostAnnotations.indirect
      InitECandidate.Solver.Wave8Stage.PrefixChecks.checked
      ConcreteWordCostAnnotations.entryBound oracleEq WordSourceOracle.terminalOracle) :=
  CertifiedPipelineTransfer.pan_to_certified_lab_complete (C := C) (F := Guest.HostMemory)
      riscvConfig wc sourceDeclarations col wordCode InitECandidate.bitmaps wconf fs stackCode
      scc dc maxHeap sp offset lab saveRegs dataSp cfg stack aux
      (Or.inr rfl) (by decide) (by decide) wtw wts initialized
      ConcreteWordCostAnnotations.summaries WordSourceOracle.terminal sourceOracle 20000
      ConcreteWordCostAnnotations.noLabels ConcreteWordCostAnnotations.indirect
      InitECandidate.Solver.Wave8Stage.PrefixChecks.checked
      ConcreteWordCostAnnotations.entryBound oracleEq WordSourceOracle.terminalOracle

end

section
variable
    (wc : WordToWord.Config) (col : List (Option (Spt Nat)))
    (wordCode : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (wconf : WordToStack.Native.Config) (fs : List Nat)
    (stackCode : List (Nat × StackLang.HolProg 64))
    (scc : StackToLab.Config) (dc : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec 64 × BitVec 64)
    (lab : LabSem.State 64 LabToTarget.Config Guest.HostMemory)
    (saveRegs : Nat → Bool) (dataSp : Nat) (cfg : LabToTarget.Config)
    (stack aux : StackSemStateFiniteExact 64 LabToTarget.Config Guest.HostMemory)
    (wtw : WordToWord.compile wc riscvConfig
      (panToWordCompileProgHOL riscvConfig.isa sourceDeclarations) = (col,wordCode))
    (wts : WordToStack.Native.compileNative riscvConfig false wordCode =
      (InitECandidate.bitmaps,wconf,fs,stackCode))
    (initialized : FullMakeInit.fullMakeInit scc dc maxHeap sp offset InitECandidate.bitmaps
      stackCode lab saveRegs dataSp (fun _ => (cfg, [], [])) = (stack,some aux))
    (oracleEq : lab.ffi.oracle = sourceOracle)
include wc col wordCode wconf fs stackCode scc dc maxHeap sp offset lab saveRegs dataSp
  cfg stack aux wtw wts initialized oracleEq

theorem pan_to_target_certified_affine_not_timeOut_concrete :
    type_of% (CertifiedPipelineTransfer.pan_to_target_certified_affine_not_timeOut
      riscvConfig wc sourceDeclarations col wordCode InitECandidate.bitmaps wconf fs stackCode
      scc dc maxHeap sp offset lab saveRegs dataSp cfg stack aux
      (Or.inr rfl) (by decide) (by decide) wtw wts initialized
      ConcreteWordCostAnnotations.summaries WordSourceOracle.terminal sourceOracle 20000
      ConcreteWordCostAnnotations.noLabels ConcreteWordCostAnnotations.indirect
      InitECandidate.Solver.Wave8Stage.PrefixChecks.checked
      ConcreteWordCostAnnotations.entryBound oracleEq WordSourceOracle.terminalOracle) :=
  CertifiedPipelineTransfer.pan_to_target_certified_affine_not_timeOut
      riscvConfig wc sourceDeclarations col wordCode InitECandidate.bitmaps wconf fs stackCode
      scc dc maxHeap sp offset lab saveRegs dataSp cfg stack aux
      (Or.inr rfl) (by decide) (by decide) wtw wts initialized
      ConcreteWordCostAnnotations.summaries WordSourceOracle.terminal sourceOracle 20000
      ConcreteWordCostAnnotations.noLabels ConcreteWordCostAnnotations.indirect
      InitECandidate.Solver.Wave8Stage.PrefixChecks.checked
      ConcreteWordCostAnnotations.entryBound oracleEq WordSourceOracle.terminalOracle
end

end InitECandidate.Solver.Wave8Stage.PrefixChecks.CertifiedPipeline
