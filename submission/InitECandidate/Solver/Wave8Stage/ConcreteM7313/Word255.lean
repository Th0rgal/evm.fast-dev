import InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard191
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Oracle255
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BackendDecomposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses
import InitECandidate.Solver.Wave8Stage.CertifiedOracleAlloc

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word255
open InitE Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition PrefixChecks.Shard191

private def col255 : Spt Nat := oracle255.getD .ln
private theorem oracle255_eq_some : oracle255 = some col255 := rfl
private abbrev tcol255 : Nat → Nat := WordAlloc.totalColour col255

wave8_kernel_reduce clashTree := getClashTreeS prefixProgram []
wave8_kernel_reduce forced := getForcedS riscvConfig prefixProgram []
wave8_kernel_reduce evenOk := everyEvenColourFast col255
wave8_certify_clash clashOk := tcol255 on clashTree
wave8_kernel_reduce allocated := applyColourFast tcol255 prefixProgram
wave8_kernel_reduce stackOk := everyStackVarFast (fun x => decide (2 * registers ≤ x)) allocated
wave8_kernel_reduce forcedOk := forced.all (fun (x, y) => tcol255 x != tcol255 y)
wave8_kernel_reduce program := WordRemove.removeMustTerminate allocated

theorem allocated_eq_full :
    WordToWord.wordAllocWith RegAlloc.regAllocExecutable name riscvConfig
      (oracleCompilerConfig []).wordToWordConf.regAlg registers prefixProgram oracle255 = allocated :=
  wordAllocWith_oracle_fast _ _ _ _ _ _ _ _ col255 clashTree forced
    oracle255_eq_some clashTree_eq forced_eq evenOk_eq clashOk_eq allocated_eq stackOk_eq forcedOk_eq

theorem wordFunction_eq : wordFunction oracle255 entry = (name, arity, program) := by
  unfold wordFunction
  rw [word_eq.trans wordCompileEq, arity_eq, name_eq, prefixCompileEq,
    allocated_eq_full, program_eq]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word255
