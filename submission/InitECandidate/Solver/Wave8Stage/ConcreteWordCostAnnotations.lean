import InitECandidate.Solver.Wave8Stage.WordCostFullPipelineCertificate
import InitECandidate.Solver.Wave8Stage.ConcreteWordCostData
import InitECandidate.Solver.Wave8Stage.WordSourceOracle
import InitECandidate.Bitmaps

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

namespace InitECandidate.Solver.Wave8Stage.ConcreteWordCostAnnotations
open Flapjack Flapjack.Compiler.Backend WordCostEffects WordCostCertificates

/-- Exit-sensitive summaries validated by the executable guest probe.
The concrete kernel check of each guest prefix is a separate obligation. -/
theorem noLabels : ∀ dest label,
    summaries dest (.breakTo label) = none ∧ summaries dest (.continueTo label) = none :=
  fun _ _ => ⟨rfl,rfl⟩

theorem indirect : ∀ name, Subeffects (summaries (some name)) (summaries none) := by
  intro name exit cost covered
  cases exit <;> simp [summaries,Covers] at covered ⊢
  all_goals repeat' first | split at covered | omega

theorem entryBound : ∀ exit,
    AtMost (summaries (some BvlToBvi.initGlobalsLocation) exit) 1 := by
  have start : BvlToBvi.initGlobalsLocation = 64 := by decide +kernel
  rw [start]
  intro exit cost covered
  cases exit <;> simp [summaries,Covers] at covered <;> omega

theorem bitmapBound : InitECandidate.bitmaps.length + 1 < 2 ^ 64 := by decide +kernel

theorem bitmapPrefix : [(4 : BitVec 64)] <+: InitECandidate.bitmaps := by
  exact ⟨InitECandidate.bitmaps.tail,rfl⟩

#print axioms indirect
#print axioms entryBound
#print axioms bitmapBound
#print axioms bitmapPrefix
end InitECandidate.Solver.Wave8Stage.ConcreteWordCostAnnotations
