import InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard82
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Oracle146
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Function145
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses
import InitECandidate.Solver.Wave8Stage.CertifiedOracleAlloc

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Function146
open InitE Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition PrefixChecks.Shard82

private def col146 : Spt Nat := oracle146.getD .ln
private theorem oracle146_eq_some : oracle146 = some col146 := rfl
private abbrev tcol146 : Nat → Nat := WordAlloc.totalColour col146

wave8_kernel_reduce clashTree := getClashTreeS prefixProgram []
wave8_kernel_reduce forced := getForcedS riscvConfig prefixProgram []
wave8_kernel_reduce evenOk := everyEvenColourFast col146
wave8_certify_clash clashOk := tcol146 on clashTree
wave8_kernel_reduce allocated := applyColourFast tcol146 prefixProgram
wave8_kernel_reduce stackOk := everyStackVarFast (fun x => decide (2 * registers ≤ x)) allocated
wave8_kernel_reduce forcedOk := forced.all (fun (x, y) => tcol146 x != tcol146 y)
wave8_kernel_reduce program := WordRemove.removeMustTerminate allocated

theorem allocated_eq_full :
    WordToWord.wordAllocWith RegAlloc.regAllocExecutable name riscvConfig
      (oracleCompilerConfig []).wordToWordConf.regAlg registers prefixProgram oracle146 = allocated :=
  wordAllocWith_oracle_fast _ _ _ _ _ _ _ _ col146 clashTree forced
    oracle146_eq_some clashTree_eq forced_eq evenOk_eq clashOk_eq allocated_eq stackOk_eq forcedOk_eq

theorem wordFunction_eq : wordFunction oracle146 entry = (name, arity, program) := by
  unfold wordFunction
  rw [word_eq.trans wordCompileEq, arity_eq, name_eq, prefixCompileEq,
    allocated_eq_full, program_eq]

wave8_kernel_reduce stackResult := WordToStack.Native.compileProgNative
  riscvConfig false program arity registers Function145.stackResult.2.2

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Function146
