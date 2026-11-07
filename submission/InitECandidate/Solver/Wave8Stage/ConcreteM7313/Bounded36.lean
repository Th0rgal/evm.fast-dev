import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk36
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded36
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open StackToLabClock LoweredBudget

wave8_kernel_reduce cost640 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard576.name, Chunk36.stackResult640.1)).2
wave8_kernel_reduce cost641 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard577.name, Chunk36.stackResult641.1)).2
wave8_kernel_reduce cost642 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard578.name, Chunk36.stackResult642.1)).2
wave8_kernel_reduce cost643 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard579.name, Chunk36.stackResult643.1)).2
wave8_kernel_reduce cost644 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard580.name, Chunk36.stackResult644.1)).2
wave8_kernel_reduce cost645 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard581.name, Chunk36.stackResult645.1)).2
wave8_kernel_reduce cost646 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard582.name, Chunk36.stackResult646.1)).2
wave8_kernel_reduce cost647 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard583.name, Chunk36.stackResult647.1)).2
wave8_kernel_reduce cost648 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard584.name, Chunk36.stackResult648.1)).2
wave8_kernel_reduce cost649 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard585.name, Chunk36.stackResult649.1)).2
wave8_kernel_reduce cost650 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard586.name, Chunk36.stackResult650.1)).2
wave8_kernel_reduce cost651 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard587.name, Chunk36.stackResult651.1)).2
wave8_kernel_reduce cost652 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard588.name, Chunk36.stackResult652.1)).2
wave8_kernel_reduce cost653 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard589.name, Chunk36.stackResult653.1)).2
wave8_kernel_reduce cost654 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard590.name, Chunk36.stackResult654.1)).2
wave8_kernel_reduce cost655 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard591.name, Chunk36.stackResult655.1)).2

theorem head640 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard576.name, Chunk36.stackResult640.1)).2 ≤ 7313 := by
  rw [cost640_eq]
  decide

theorem head641 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard577.name, Chunk36.stackResult641.1)).2 ≤ 7313 := by
  rw [cost641_eq]
  decide

theorem head642 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard578.name, Chunk36.stackResult642.1)).2 ≤ 7313 := by
  rw [cost642_eq]
  decide

theorem head643 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard579.name, Chunk36.stackResult643.1)).2 ≤ 7313 := by
  rw [cost643_eq]
  decide

theorem head644 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard580.name, Chunk36.stackResult644.1)).2 ≤ 7313 := by
  rw [cost644_eq]
  decide

theorem head645 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard581.name, Chunk36.stackResult645.1)).2 ≤ 7313 := by
  rw [cost645_eq]
  decide

theorem head646 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard582.name, Chunk36.stackResult646.1)).2 ≤ 7313 := by
  rw [cost646_eq]
  decide

theorem head647 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard583.name, Chunk36.stackResult647.1)).2 ≤ 7313 := by
  rw [cost647_eq]
  decide

theorem head648 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard584.name, Chunk36.stackResult648.1)).2 ≤ 7313 := by
  rw [cost648_eq]
  decide

theorem head649 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard585.name, Chunk36.stackResult649.1)).2 ≤ 7313 := by
  rw [cost649_eq]
  decide

theorem head650 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard586.name, Chunk36.stackResult650.1)).2 ≤ 7313 := by
  rw [cost650_eq]
  decide

theorem head651 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard587.name, Chunk36.stackResult651.1)).2 ≤ 7313 := by
  rw [cost651_eq]
  decide

theorem head652 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard588.name, Chunk36.stackResult652.1)).2 ≤ 7313 := by
  rw [cost652_eq]
  decide

theorem head653 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard589.name, Chunk36.stackResult653.1)).2 ≤ 7313 := by
  rw [cost653_eq]
  decide

theorem head654 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard590.name, Chunk36.stackResult654.1)).2 ≤ 7313 := by
  rw [cost654_eq]
  decide

theorem head655 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard591.name, Chunk36.stackResult655.1)).2 ≤ 7313 := by
  rw [cost655_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk36.bodies := by
  unfold Chunk36.bodies
  apply bounded_cons _ _ _ head640
  apply bounded_cons _ _ _ head641
  apply bounded_cons _ _ _ head642
  apply bounded_cons _ _ _ head643
  apply bounded_cons _ _ _ head644
  apply bounded_cons _ _ _ head645
  apply bounded_cons _ _ _ head646
  apply bounded_cons _ _ _ head647
  apply bounded_cons _ _ _ head648
  apply bounded_cons _ _ _ head649
  apply bounded_cons _ _ _ head650
  apply bounded_cons _ _ _ head651
  apply bounded_cons _ _ _ head652
  apply bounded_cons _ _ _ head653
  apply bounded_cons _ _ _ head654
  apply bounded_cons _ _ _ head655
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded36
