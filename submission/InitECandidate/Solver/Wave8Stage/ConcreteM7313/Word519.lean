import InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard455
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Oracle519
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BackendDecomposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses
import InitECandidate.Solver.Wave8Stage.CertifiedOracleAlloc

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word519
open InitE Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition PrefixChecks.Shard455

private def col519 : Spt Nat := oracle519.getD .ln
private theorem oracle519_eq_some : oracle519 = some col519 := rfl
private abbrev tcol519 : Nat → Nat := WordAlloc.totalColour col519

wave8_kernel_reduce clashTree := getClashTreeS prefixProgram []
wave8_kernel_reduce forced := getForcedS riscvConfig prefixProgram []
wave8_kernel_reduce evenOk := everyEvenColourFast col519
wave8_certify_clash clashOk := tcol519 on clashTree
wave8_kernel_reduce allocated := applyColourFast tcol519 prefixProgram
wave8_kernel_reduce stackOk := everyStackVarFast (fun x => decide (2 * registers ≤ x)) allocated
wave8_kernel_reduce forcedOk := forced.all (fun (x, y) => tcol519 x != tcol519 y)
wave8_kernel_reduce program := WordRemove.removeMustTerminate allocated

theorem allocated_eq_full :
    WordToWord.wordAllocWith RegAlloc.regAllocExecutable name riscvConfig
      (oracleCompilerConfig []).wordToWordConf.regAlg registers prefixProgram oracle519 = allocated :=
  wordAllocWith_oracle_fast _ _ _ _ _ _ _ _ col519 clashTree forced
    oracle519_eq_some clashTree_eq forced_eq evenOk_eq clashOk_eq allocated_eq stackOk_eq forcedOk_eq

theorem wordFunction_eq : wordFunction oracle519 entry = (name, arity, program) := by
  unfold wordFunction
  rw [word_eq.trans wordCompileEq, arity_eq, name_eq, prefixCompileEq,
    allocated_eq_full, program_eq]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word519
