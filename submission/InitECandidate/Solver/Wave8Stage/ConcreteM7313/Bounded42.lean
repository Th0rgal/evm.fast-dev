import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk42
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded42
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open StackToLabClock LoweredBudget

wave8_kernel_reduce cost736 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard672.name, Chunk42.stackResult736.1)).2
wave8_kernel_reduce cost737 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard673.name, Chunk42.stackResult737.1)).2
wave8_kernel_reduce cost738 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard674.name, Chunk42.stackResult738.1)).2
wave8_kernel_reduce cost739 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard675.name, Chunk42.stackResult739.1)).2
wave8_kernel_reduce cost740 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard676.name, Chunk42.stackResult740.1)).2
wave8_kernel_reduce cost741 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard677.name, Chunk42.stackResult741.1)).2
wave8_kernel_reduce cost742 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard678.name, Chunk42.stackResult742.1)).2
wave8_kernel_reduce cost743 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard679.name, Chunk42.stackResult743.1)).2
wave8_kernel_reduce cost744 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard680.name, Chunk42.stackResult744.1)).2
wave8_kernel_reduce cost745 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard681.name, Chunk42.stackResult745.1)).2
wave8_kernel_reduce cost746 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard682.name, Chunk42.stackResult746.1)).2
wave8_kernel_reduce cost747 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard683.name, Chunk42.stackResult747.1)).2
wave8_kernel_reduce cost748 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard684.name, Chunk42.stackResult748.1)).2
wave8_kernel_reduce cost749 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard685.name, Chunk42.stackResult749.1)).2
wave8_kernel_reduce cost750 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard686.name, Chunk42.stackResult750.1)).2
wave8_kernel_reduce cost751 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard687.name, Chunk42.stackResult751.1)).2

theorem head736 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard672.name, Chunk42.stackResult736.1)).2 ≤ 7313 := by
  rw [cost736_eq]
  decide

theorem head737 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard673.name, Chunk42.stackResult737.1)).2 ≤ 7313 := by
  rw [cost737_eq]
  decide

theorem head738 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard674.name, Chunk42.stackResult738.1)).2 ≤ 7313 := by
  rw [cost738_eq]
  decide

theorem head739 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard675.name, Chunk42.stackResult739.1)).2 ≤ 7313 := by
  rw [cost739_eq]
  decide

theorem head740 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard676.name, Chunk42.stackResult740.1)).2 ≤ 7313 := by
  rw [cost740_eq]
  decide

theorem head741 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard677.name, Chunk42.stackResult741.1)).2 ≤ 7313 := by
  rw [cost741_eq]
  decide

theorem head742 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard678.name, Chunk42.stackResult742.1)).2 ≤ 7313 := by
  rw [cost742_eq]
  decide

theorem head743 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard679.name, Chunk42.stackResult743.1)).2 ≤ 7313 := by
  rw [cost743_eq]
  decide

theorem head744 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard680.name, Chunk42.stackResult744.1)).2 ≤ 7313 := by
  rw [cost744_eq]
  decide

theorem head745 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard681.name, Chunk42.stackResult745.1)).2 ≤ 7313 := by
  rw [cost745_eq]
  decide

theorem head746 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard682.name, Chunk42.stackResult746.1)).2 ≤ 7313 := by
  rw [cost746_eq]
  decide

theorem head747 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard683.name, Chunk42.stackResult747.1)).2 ≤ 7313 := by
  rw [cost747_eq]
  decide

theorem head748 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard684.name, Chunk42.stackResult748.1)).2 ≤ 7313 := by
  rw [cost748_eq]
  decide

theorem head749 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard685.name, Chunk42.stackResult749.1)).2 ≤ 7313 := by
  rw [cost749_eq]
  decide

theorem head750 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard686.name, Chunk42.stackResult750.1)).2 ≤ 7313 := by
  rw [cost750_eq]
  decide

theorem head751 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard687.name, Chunk42.stackResult751.1)).2 ≤ 7313 := by
  rw [cost751_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk42.bodies := by
  unfold Chunk42.bodies
  apply bounded_cons _ _ _ head736
  apply bounded_cons _ _ _ head737
  apply bounded_cons _ _ _ head738
  apply bounded_cons _ _ _ head739
  apply bounded_cons _ _ _ head740
  apply bounded_cons _ _ _ head741
  apply bounded_cons _ _ _ head742
  apply bounded_cons _ _ _ head743
  apply bounded_cons _ _ _ head744
  apply bounded_cons _ _ _ head745
  apply bounded_cons _ _ _ head746
  apply bounded_cons _ _ _ head747
  apply bounded_cons _ _ _ head748
  apply bounded_cons _ _ _ head749
  apply bounded_cons _ _ _ head750
  apply bounded_cons _ _ _ head751
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded42
