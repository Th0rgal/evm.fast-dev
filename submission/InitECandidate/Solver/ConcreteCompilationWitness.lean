import InitECandidate.Solver.FastBaselineState
import InitECandidate.Proofs.CompilerOracles
import InitE.SourceDeclarationsCore

set_option autoImplicit false

namespace InitECandidate.Solver.SelfContainedConcretePipelineMaster
open InitE Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Pancake.Proofs.PanToTarget

/-- Concrete oracle compilation and stack-depth witness isolating the only
artifact facts absent when `InitECandidate.Proofs.FullBaseline` is unbuilt. -/
structure ConcreteOracleCompilationWitness : Type where
  oracles : List (Option (Spt Nat))
  c : Backend.Config
  depth : Nat
  hlab : c.labConf = baselineLabConfig
  compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
    sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth)
  depthBound : depth ≤ 7480


end InitECandidate.Solver.SelfContainedConcretePipelineMaster
