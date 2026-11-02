import InitECandidate.Solver.Wave8Stage.Stage4ConcreteInitialization
import InitECandidate.Solver.Wave8Stage.Stage4AllocGlue

/-! Concrete installation discharges the initialization and memory premises of
the integration branch's program-dependent Stage 4 transfer. The separate
frozen 8*k+32 claim is not asserted here. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteInitialization
open Classical InitE Flapjack
open Compiler.Backend Compiler.Backend.RiscVConfig Compiler.Encoders.Asm
open Compiler.Encoders.RiscV.Target Pancake.Proofs.PanToTarget StackToLab.Proofs
open InitECandidate.Solver.FastEnv

theorem lab_transfer_exists
    (oracles col : List (Option (Spt Nat))) (input : Guest.InputBlob)
    (wordCode : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (wconf : WordToStack.Native.Config) (fs : List Nat)
    (code : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config)
    (hwtw : WordToWord.compile (oracleCompilerConfig oracles).wordToWordConf riscvConfig
      (panToWordCompileProgHOL riscvConfig.isa sourceDeclarations) = (col, wordCode))
    (hwts : WordToStack.Native.compileNative riscvConfig false wordCode =
      (InitECandidate.bitmaps, wconf, fs, code)) :
    ∃ (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
      (bitmapDm sharedDm : BitVec 64 → Bool)
      (aux : StackSemStateFiniteExact 64 LabToTarget.Config Guest.HostMemory),
      initialized oracles input t m bitmapDm sharedDm ltconf code =
        ((initialized oracles input t m bitmapDm sharedDm ltconf code).1, some aux) ∧
      ∀ k : Nat,
        let c := oracleCompilerConfig oracles
        let lab := labState oracles input t m bitmapDm sharedDm ltconf code
        let stack := (initialized oracles input t m bitmapDm sharedDm ltconf code).1
        let result := (StackSemEvaluate.evaluate
          ((.call none (.inl BvlToBvi.initGlobalsLocation) none : StackLang.HolProg 64),
            {stack with clock := k})).1
        let M := Stage4.codeStepBudget (FullMakeInitSemantics.code2 c.stackConf c.dataConf
          (2 * DataToWord.maxHeapLimit 64 c.dataConf - 1)
          (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset code)
        FlattenSemantics.stackEntryClass result ≠ .RunError →
        result ≠ some .timeOut →
        (LabSem.evaluate {lab with clock := 2 * (M + 1) * k + (3 * M + 2)}).1 ≠ .timeOut := by
  obtain ⟨t, m, bitmapDm, sharedDm, aux, _, _, _, hA, hs, hmem⟩ :=
    initialization_exists oracles col input wordCode wconf fs code ltconf hwtw hwts
  have compiled : code = (WordToStack.Native.compileNative riscvConfig false
      (WordToWord.compile (oracleCompilerConfig oracles).wordToWordConf riscvConfig
        (panToWordCompileProgHOL riscvConfig.isa sourceDeclarations)).2).2.2.2 := by
    rw [hwtw, hwts]
  refine ⟨t, m, bitmapDm, sharedDm, aux, hs, ?_⟩
  intro k
  exact Stage4.fullMakeInit_lab_affine_of_source_run
    (oracleCompilerConfig oracles).stackConf (oracleCompilerConfig oracles).dataConf
    (2 * DataToWord.maxHeapLimit 64 (oracleCompilerConfig oracles).dataConf - 1)
    (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset
    InitECandidate.bitmaps code (labState oracles input t m bitmapDm sharedDm ltconf code)
    (fun r => decide (r ∈ baselineMachineConfig.calleeSavedRegs)) 0
    (fun _ => (ltconf, [], [])) hA riscvConfig false
    (oracleCompilerConfig oracles).wordToWordConf riscvConfig.isa sourceDeclarations
    compiled hmem (fun _ => rfl) k

#print axioms lab_transfer_exists
end InitECandidate.Solver.Wave8Stage.ConcreteInitialization
