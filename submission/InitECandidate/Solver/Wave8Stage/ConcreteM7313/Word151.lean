import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word151Allocation
import InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard87
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Oracle151
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BackendDecomposition

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 16000000
set_option cbv.maxSteps 20000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word151
open InitE Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target
open BackendDecomposition PrefixChecks.Shard87

noncomputable def allocated := Word151Bounds.coloured
theorem allocated_eq : WordToWord.wordAllocWith RegAlloc.regAllocExecutable
    name riscvConfig (oracleCompilerConfig []).wordToWordConf.regAlg registers
    prefixProgram oracle151 = allocated := Word151Allocation.allocated_eq
noncomputable def program := WordRemove.removeMustTerminate allocated
theorem program_eq : WordRemove.removeMustTerminate allocated = program := rfl

theorem wordFunction_eq : wordFunction oracle151 entry = (name, arity, program) := by
  unfold wordFunction
  rw [word_eq.trans wordCompileEq, arity_eq, name_eq, prefixCompileEq,
    allocated_eq, program_eq]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word151
