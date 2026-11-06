import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word151ClashCompose23
import InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard87
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 16000000
set_option cbv.maxSteps 20000000
namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word151ClashTree
open Flapjack
noncomputable section
theorem prefix_eq : PrefixChecks.Shard87.prefixProgram = part0Suffix := by rfl
theorem tree_eq : WordAlloc.getClashTree PrefixChecks.Shard87.prefixProgram [] =
    part0TreeSuffix := by
  rw [prefix_eq]
  exact part0Suffix_eq

end
end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word151ClashTree
