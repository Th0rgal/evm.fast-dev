import InitECandidate.Proofs.CheckedCompilerConfig
import InitECandidate.Proofs.ArtifactFacts
import InitECandidate.Proofs.SourceStackCertificate
import Flapjack.Pancake.Proofs.PanToTarget.ExecutableCompileProgMaxAsmWith
import InitECandidate.Solver.ConcreteCompilationWitness

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.ConcreteOracleWitness

open Classical
open InitE
open InitECandidate.Proofs
open InitECandidate.Solver.SelfContainedConcretePipelineMaster
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Encoders.RiscV.Target

theorem baselineConfigLiteralWithOracles_labConf :
    baselineConfigLiteralWithOracles.labConf = baselineLabConfig := rfl

theorem baseline_compileProgMaxAsmExecutable_exists :
    ∃ depth : Nat,
      compileProgMaxAsmExecutable (oracleCompilerConfig WordBackend.oracles) riscvConfig
        sourceDeclarations =
          (some (InitECandidate.nativeCode, InitECandidate.bitmaps,
            baselineConfigLiteralWithOracles), some depth) ∧
      depth ≤ 7480 := by
  obtain ⟨depth, hdepth, hbound⟩ := sourceLogicalStackBound_bounded
  refine ⟨depth, ?_, hbound⟩
  apply Prod.ext
  · rw [← compileProgAsmFast_eq_fst]
    exact baseline_compiler_artifact_eq
  · exact hdepth

noncomputable def concreteOracleWitness : ConcreteOracleCompilationWitness :=
  { oracles := WordBackend.oracles
    c := baselineConfigLiteralWithOracles
    depth := Classical.choose baseline_compileProgMaxAsmExecutable_exists
    hlab := baselineConfigLiteralWithOracles_labConf
    compiled := (Classical.choose_spec baseline_compileProgMaxAsmExecutable_exists).1
    depthBound := (Classical.choose_spec baseline_compileProgMaxAsmExecutable_exists).2 }

theorem concreteOracleCompilationWitness_nonempty :
    Nonempty ConcreteOracleCompilationWitness :=
  ⟨concreteOracleWitness⟩

end InitECandidate.Solver.ConcreteOracleWitness

