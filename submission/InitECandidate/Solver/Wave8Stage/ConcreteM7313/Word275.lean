import InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard211
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Oracle275
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BackendDecomposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses
import InitECandidate.Solver.Wave8Stage.CertifiedOracleAlloc

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word275
open InitE Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition PrefixChecks.Shard211

private def col275 : Spt Nat := oracle275.getD .ln
private theorem oracle275_eq_some : oracle275 = some col275 := rfl
private abbrev tcol275 : Nat → Nat := WordAlloc.totalColour col275

wave8_kernel_reduce clashTree := getClashTreeS prefixProgram []
wave8_kernel_reduce forced := getForcedS riscvConfig prefixProgram []
wave8_kernel_reduce evenOk := everyEvenColourFast col275
wave8_certify_clash clashOk := tcol275 on clashTree
wave8_kernel_reduce allocated := applyColourFast tcol275 prefixProgram
wave8_kernel_reduce stackOk := everyStackVarFast (fun x => decide (2 * registers ≤ x)) allocated
wave8_kernel_reduce forcedOk := forced.all (fun (x, y) => tcol275 x != tcol275 y)
wave8_kernel_reduce program := WordRemove.removeMustTerminate allocated

theorem allocated_eq_full :
    WordToWord.wordAllocWith RegAlloc.regAllocExecutable name riscvConfig
      (oracleCompilerConfig []).wordToWordConf.regAlg registers prefixProgram oracle275 = allocated :=
  wordAllocWith_oracle_fast _ _ _ _ _ _ _ _ col275 clashTree forced
    oracle275_eq_some clashTree_eq forced_eq evenOk_eq clashOk_eq allocated_eq stackOk_eq forcedOk_eq

theorem wordFunction_eq : wordFunction oracle275 entry = (name, arity, program) := by
  unfold wordFunction
  rw [word_eq.trans wordCompileEq, arity_eq, name_eq, prefixCompileEq,
    allocated_eq_full, program_eq]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word275
