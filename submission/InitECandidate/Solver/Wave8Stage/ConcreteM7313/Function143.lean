import InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard79
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Oracle143
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Function142
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses
import InitECandidate.Solver.Wave8Stage.CertifiedOracleAlloc

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Function143
open InitE Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition PrefixChecks.Shard79

private def col143 : Spt Nat := oracle143.getD .ln
private theorem oracle143_eq_some : oracle143 = some col143 := rfl
private abbrev tcol143 : Nat → Nat := WordAlloc.totalColour col143

wave8_kernel_reduce clashTree := getClashTreeS prefixProgram []
wave8_kernel_reduce forced := getForcedS riscvConfig prefixProgram []
wave8_kernel_reduce evenOk := everyEvenColourFast col143
wave8_certify_clash clashOk := tcol143 on clashTree
wave8_kernel_reduce allocated := applyColourFast tcol143 prefixProgram
wave8_kernel_reduce stackOk := everyStackVarFast (fun x => decide (2 * registers ≤ x)) allocated
wave8_kernel_reduce forcedOk := forced.all (fun (x, y) => tcol143 x != tcol143 y)
wave8_kernel_reduce program := WordRemove.removeMustTerminate allocated

theorem allocated_eq_full :
    WordToWord.wordAllocWith RegAlloc.regAllocExecutable name riscvConfig
      (oracleCompilerConfig []).wordToWordConf.regAlg registers prefixProgram oracle143 = allocated :=
  wordAllocWith_oracle_fast _ _ _ _ _ _ _ _ col143 clashTree forced
    oracle143_eq_some clashTree_eq forced_eq evenOk_eq clashOk_eq allocated_eq stackOk_eq forcedOk_eq

theorem wordFunction_eq : wordFunction oracle143 entry = (name, arity, program) := by
  unfold wordFunction
  rw [word_eq.trans wordCompileEq, arity_eq, name_eq, prefixCompileEq,
    allocated_eq_full, program_eq]

wave8_kernel_reduce stackResult := WordToStack.Native.compileProgNative
  riscvConfig false program arity registers Function142.stackResult.2.2

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Function143
