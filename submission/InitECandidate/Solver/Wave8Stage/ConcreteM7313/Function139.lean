import InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard75
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Oracle139
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Function138
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses
import InitECandidate.Solver.Wave8Stage.CertifiedOracleAlloc

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Function139
open InitE Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition PrefixChecks.Shard75

private def col139 : Spt Nat := oracle139.getD .ln
private theorem oracle139_eq_some : oracle139 = some col139 := rfl
private abbrev tcol139 : Nat → Nat := WordAlloc.totalColour col139

wave8_kernel_reduce clashTree := getClashTreeS prefixProgram []
wave8_kernel_reduce forced := getForcedS riscvConfig prefixProgram []
wave8_kernel_reduce evenOk := everyEvenColourFast col139
wave8_certify_clash clashOk := tcol139 on clashTree
wave8_kernel_reduce allocated := applyColourFast tcol139 prefixProgram
wave8_kernel_reduce stackOk := everyStackVarFast (fun x => decide (2 * registers ≤ x)) allocated
wave8_kernel_reduce forcedOk := forced.all (fun (x, y) => tcol139 x != tcol139 y)
wave8_kernel_reduce program := WordRemove.removeMustTerminate allocated

theorem allocated_eq_full :
    WordToWord.wordAllocWith RegAlloc.regAllocExecutable name riscvConfig
      (oracleCompilerConfig []).wordToWordConf.regAlg registers prefixProgram oracle139 = allocated :=
  wordAllocWith_oracle_fast _ _ _ _ _ _ _ _ col139 clashTree forced
    oracle139_eq_some clashTree_eq forced_eq evenOk_eq clashOk_eq allocated_eq stackOk_eq forcedOk_eq

theorem wordFunction_eq : wordFunction oracle139 entry = (name, arity, program) := by
  unfold wordFunction
  rw [word_eq.trans wordCompileEq, arity_eq, name_eq, prefixCompileEq,
    allocated_eq_full, program_eq]

wave8_kernel_reduce stackResult := WordToStack.Native.compileProgNative
  riscvConfig false program arity registers Function138.stackResult.2.2

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Function139
