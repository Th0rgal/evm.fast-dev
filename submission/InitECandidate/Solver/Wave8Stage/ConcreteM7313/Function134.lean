import InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard70
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Oracle134
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Function133
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses
import InitECandidate.Solver.Wave8Stage.CertifiedOracleAlloc

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Function134
open InitE Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition PrefixChecks.Shard70

private def col134 : Spt Nat := oracle134.getD .ln
private theorem oracle134_eq_some : oracle134 = some col134 := rfl
private abbrev tcol134 : Nat → Nat := WordAlloc.totalColour col134

wave8_kernel_reduce clashTree := getClashTreeS prefixProgram []
wave8_kernel_reduce forced := getForcedS riscvConfig prefixProgram []
wave8_kernel_reduce evenOk := everyEvenColourFast col134
wave8_certify_clash clashOk := tcol134 on clashTree
wave8_kernel_reduce allocated := applyColourFast tcol134 prefixProgram
wave8_kernel_reduce stackOk := everyStackVarFast (fun x => decide (2 * registers ≤ x)) allocated
wave8_kernel_reduce forcedOk := forced.all (fun (x, y) => tcol134 x != tcol134 y)
wave8_kernel_reduce program := WordRemove.removeMustTerminate allocated

theorem allocated_eq_full :
    WordToWord.wordAllocWith RegAlloc.regAllocExecutable name riscvConfig
      (oracleCompilerConfig []).wordToWordConf.regAlg registers prefixProgram oracle134 = allocated :=
  wordAllocWith_oracle_fast _ _ _ _ _ _ _ _ col134 clashTree forced
    oracle134_eq_some clashTree_eq forced_eq evenOk_eq clashOk_eq allocated_eq stackOk_eq forcedOk_eq

theorem wordFunction_eq : wordFunction oracle134 entry = (name, arity, program) := by
  unfold wordFunction
  rw [word_eq.trans wordCompileEq, arity_eq, name_eq, prefixCompileEq,
    allocated_eq_full, program_eq]

wave8_kernel_reduce stackResult := WordToStack.Native.compileProgNative
  riscvConfig false program arity registers Function133.stackResult.2.2

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Function134
