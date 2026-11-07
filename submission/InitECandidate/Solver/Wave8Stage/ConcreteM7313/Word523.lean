import InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard459
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Oracle523
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BackendDecomposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses
import InitECandidate.Solver.Wave8Stage.CertifiedOracleAlloc

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word523
open InitE Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition PrefixChecks.Shard459

private def col523 : Spt Nat := oracle523.getD .ln
private theorem oracle523_eq_some : oracle523 = some col523 := rfl
private abbrev tcol523 : Nat → Nat := WordAlloc.totalColour col523

wave8_kernel_reduce clashTree := getClashTreeS prefixProgram []
wave8_kernel_reduce forced := getForcedS riscvConfig prefixProgram []
wave8_kernel_reduce evenOk := everyEvenColourFast col523
wave8_certify_clash clashOk := tcol523 on clashTree
wave8_kernel_reduce allocated := applyColourFast tcol523 prefixProgram
wave8_kernel_reduce stackOk := everyStackVarFast (fun x => decide (2 * registers ≤ x)) allocated
wave8_kernel_reduce forcedOk := forced.all (fun (x, y) => tcol523 x != tcol523 y)
wave8_kernel_reduce program := WordRemove.removeMustTerminate allocated

theorem allocated_eq_full :
    WordToWord.wordAllocWith RegAlloc.regAllocExecutable name riscvConfig
      (oracleCompilerConfig []).wordToWordConf.regAlg registers prefixProgram oracle523 = allocated :=
  wordAllocWith_oracle_fast _ _ _ _ _ _ _ _ col523 clashTree forced
    oracle523_eq_some clashTree_eq forced_eq evenOk_eq clashOk_eq allocated_eq stackOk_eq forcedOk_eq

theorem wordFunction_eq : wordFunction oracle523 entry = (name, arity, program) := by
  unfold wordFunction
  rw [word_eq.trans wordCompileEq, arity_eq, name_eq, prefixCompileEq,
    allocated_eq_full, program_eq]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word523
