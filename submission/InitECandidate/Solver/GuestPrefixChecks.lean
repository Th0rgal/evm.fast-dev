import InitECandidate.Solver.Wave8Stage.PrefixChecks.AllChecked
import InitECandidate.Solver.Wave8Stage.PrefixChecks.CertifiedPipeline

/-!
# Concrete Guest Prefix Cost Certificates

Re-exports the concrete Stage 2–3 `WordCostCheck` prefix check certificate
`checked : ConcreteCompilerWord.source.all ConcreteWordCheckInput.check = true`
and its certified pipeline specializations for the `InitECandidate` guest.
-/

set_option autoImplicit false

namespace InitECandidate.Solver.GuestPrefixChecks

open InitECandidate.Solver.Wave8Stage

/-- All 814 concrete `Word` procedures pass `ConcreteWordCheckInput.check`. -/
theorem word_all_checked :
    ConcreteCompilerWord.source.all ConcreteWordCheckInput.check = true := by
  rw [List.all_eq_true]
  change ∀ entry ∈ ConcreteCompilerWord.source, ConcreteWordCheckInput.check entry = true
  rw [← ConcreteCompilerWord.compile_eq]
  exact PrefixChecks.checked

/-- Original `panToWordCompileProgHOL` procedures satisfy `WordCostCheck.checkProgram`. -/
theorem word_original_checked :
    ∀ entry ∈ Flapjack.panToWordCompileProgHOL
      Flapjack.Compiler.Encoders.RiscV.Target.riscvConfig.isa InitE.sourceDeclarations,
      WordCostCheck.checkProgram ConcreteWordCostAnnotations.summaries WordSourceOracle.terminal
        20000
        (WordCostCompilerControl.preAllocation
          Flapjack.Compiler.Encoders.RiscV.Target.riscvConfig
          Flapjack.Compiler.Encoders.RiscV.Target.riscvConfig.twoRegArith
          entry.2.1 entry.2.2)
        (ConcreteWordCostAnnotations.summaries (some entry.1)) = true :=
  PrefixChecks.checked

/-- Concrete Stage 2–3 transfer with the finite-check premise discharged. -/
theorem stage2_to_3_concrete :
    type_of% PrefixChecks.stage2_to_3_concrete :=
  PrefixChecks.stage2_to_3_concrete

end InitECandidate.Solver.GuestPrefixChecks
