import InitECandidate.Solver.Wave8Stage.ConcreteCompilerWord
import InitECandidate.Solver.Wave8Stage.ConcreteWordCostData
import InitECandidate.Solver.Wave8Stage.WordCostCheck
import InitECandidate.Solver.Wave8Stage.WordCostCompilerControl
import InitECandidate.Solver.Wave8Stage.CertifiedListEntry
import InitECandidate.Solver.Wave8Stage.CertifiedListAll
import Flapjack.Compiler.Encoders.RiscV.Target.Configuration

set_option autoImplicit false

namespace InitECandidate.Solver.Wave8Stage.ConcreteWordCheckInput
open InitE Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target

def check (entry : Nat × Nat × WordLangProgHOL (BitVec 64)) : Bool :=
  WordCostCheck.checkProgram ConcreteWordCostAnnotations.summaries WordSourceOracle.terminal 20000
    (WordCostCompilerControl.preAllocation riscvConfig riscvConfig.twoRegArith entry.2.1 entry.2.2)
    (ConcreteWordCostAnnotations.summaries (some entry.1))

theorem original_of_all (checked : ConcreteCompilerWord.source.all check = true) :
    ∀ entry ∈ panToWordCompileProgHOL riscvConfig.isa sourceDeclarations,
      WordCostCheck.checkProgram ConcreteWordCostAnnotations.summaries WordSourceOracle.terminal 20000
        (WordCostCompilerControl.preAllocation riscvConfig riscvConfig.twoRegArith entry.2.1 entry.2.2)
        (ConcreteWordCostAnnotations.summaries (some entry.1)) = true := by
  change ∀ entry ∈ panToWordCompileProgHOL .riscv sourceDeclarations, check entry = true
  rw [ConcreteCompilerWord.compile_eq]
  exact List.all_eq_true.mp checked

end InitECandidate.Solver.Wave8Stage.ConcreteWordCheckInput
