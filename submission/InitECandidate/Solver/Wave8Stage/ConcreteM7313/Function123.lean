import InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard59
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Oracle123
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Function122
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses
import InitECandidate.Solver.Wave8Stage.CertifiedOracleAlloc

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Function123
open InitE Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition PrefixChecks.Shard59

private def col123 : Spt Nat := oracle123.getD .ln
private theorem oracle123_eq_some : oracle123 = some col123 := rfl
private abbrev tcol123 : Nat → Nat := WordAlloc.totalColour col123

wave8_kernel_reduce clashTree := getClashTreeS prefixProgram []
wave8_kernel_reduce forced := getForcedS riscvConfig prefixProgram []
wave8_kernel_reduce evenOk := everyEvenColourFast col123
wave8_certify_clash clashOk := tcol123 on clashTree
wave8_kernel_reduce allocated := applyColourFast tcol123 prefixProgram
wave8_kernel_reduce stackOk := everyStackVarFast (fun x => decide (2 * registers ≤ x)) allocated
wave8_kernel_reduce forcedOk := forced.all (fun (x, y) => tcol123 x != tcol123 y)
wave8_kernel_reduce program := WordRemove.removeMustTerminate allocated

theorem allocated_eq_full :
    WordToWord.wordAllocWith RegAlloc.regAllocExecutable name riscvConfig
      (oracleCompilerConfig []).wordToWordConf.regAlg registers prefixProgram oracle123 = allocated :=
  wordAllocWith_oracle_fast _ _ _ _ _ _ _ _ col123 clashTree forced
    oracle123_eq_some clashTree_eq forced_eq evenOk_eq clashOk_eq allocated_eq stackOk_eq forcedOk_eq

theorem wordFunction_eq : wordFunction oracle123 entry = (name, arity, program) := by
  unfold wordFunction
  rw [word_eq.trans wordCompileEq, arity_eq, name_eq, prefixCompileEq,
    allocated_eq_full, program_eq]

wave8_kernel_reduce stackResult := WordToStack.Native.compileProgNative
  riscvConfig false program arity registers Function122.stackResult.2.2

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Function123
