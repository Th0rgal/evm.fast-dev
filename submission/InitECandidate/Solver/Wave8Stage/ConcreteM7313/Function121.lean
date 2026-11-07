import InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard57
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Oracle121
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Function120
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses
import InitECandidate.Solver.Wave8Stage.CertifiedOracleAlloc

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Function121
open InitE Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition PrefixChecks.Shard57

private def col121 : Spt Nat := oracle121.getD .ln
private theorem oracle121_eq_some : oracle121 = some col121 := rfl
private abbrev tcol121 : Nat → Nat := WordAlloc.totalColour col121

wave8_kernel_reduce clashTree := getClashTreeS prefixProgram []
wave8_kernel_reduce forced := getForcedS riscvConfig prefixProgram []
wave8_kernel_reduce evenOk := everyEvenColourFast col121
wave8_certify_clash clashOk := tcol121 on clashTree
wave8_kernel_reduce allocated := applyColourFast tcol121 prefixProgram
wave8_kernel_reduce stackOk := everyStackVarFast (fun x => decide (2 * registers ≤ x)) allocated
wave8_kernel_reduce forcedOk := forced.all (fun (x, y) => tcol121 x != tcol121 y)
wave8_kernel_reduce program := WordRemove.removeMustTerminate allocated

theorem allocated_eq_full :
    WordToWord.wordAllocWith RegAlloc.regAllocExecutable name riscvConfig
      (oracleCompilerConfig []).wordToWordConf.regAlg registers prefixProgram oracle121 = allocated :=
  wordAllocWith_oracle_fast _ _ _ _ _ _ _ _ col121 clashTree forced
    oracle121_eq_some clashTree_eq forced_eq evenOk_eq clashOk_eq allocated_eq stackOk_eq forcedOk_eq

theorem wordFunction_eq : wordFunction oracle121 entry = (name, arity, program) := by
  unfold wordFunction
  rw [word_eq.trans wordCompileEq, arity_eq, name_eq, prefixCompileEq,
    allocated_eq_full, program_eq]

wave8_kernel_reduce stackResult := WordToStack.Native.compileProgNative
  riscvConfig false program arity registers Function120.stackResult.2.2

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Function121
