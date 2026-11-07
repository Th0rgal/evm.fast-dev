import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk40
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded40
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open StackToLabClock LoweredBudget

wave8_kernel_reduce cost704 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard640.name, Chunk40.stackResult704.1)).2
wave8_kernel_reduce cost705 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard641.name, Chunk40.stackResult705.1)).2
wave8_kernel_reduce cost706 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard642.name, Chunk40.stackResult706.1)).2
wave8_kernel_reduce cost707 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard643.name, Chunk40.stackResult707.1)).2
wave8_kernel_reduce cost708 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard644.name, Chunk40.stackResult708.1)).2
wave8_kernel_reduce cost709 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard645.name, Chunk40.stackResult709.1)).2
wave8_kernel_reduce cost710 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard646.name, Chunk40.stackResult710.1)).2
wave8_kernel_reduce cost711 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard647.name, Chunk40.stackResult711.1)).2
wave8_kernel_reduce cost712 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard648.name, Chunk40.stackResult712.1)).2
wave8_kernel_reduce cost713 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard649.name, Chunk40.stackResult713.1)).2
wave8_kernel_reduce cost714 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard650.name, Chunk40.stackResult714.1)).2
wave8_kernel_reduce cost715 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard651.name, Chunk40.stackResult715.1)).2
wave8_kernel_reduce cost716 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard652.name, Chunk40.stackResult716.1)).2
wave8_kernel_reduce cost717 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard653.name, Chunk40.stackResult717.1)).2
wave8_kernel_reduce cost718 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard654.name, Chunk40.stackResult718.1)).2
wave8_kernel_reduce cost719 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard655.name, Chunk40.stackResult719.1)).2

theorem head704 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard640.name, Chunk40.stackResult704.1)).2 ≤ 7313 := by
  rw [cost704_eq]
  decide

theorem head705 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard641.name, Chunk40.stackResult705.1)).2 ≤ 7313 := by
  rw [cost705_eq]
  decide

theorem head706 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard642.name, Chunk40.stackResult706.1)).2 ≤ 7313 := by
  rw [cost706_eq]
  decide

theorem head707 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard643.name, Chunk40.stackResult707.1)).2 ≤ 7313 := by
  rw [cost707_eq]
  decide

theorem head708 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard644.name, Chunk40.stackResult708.1)).2 ≤ 7313 := by
  rw [cost708_eq]
  decide

theorem head709 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard645.name, Chunk40.stackResult709.1)).2 ≤ 7313 := by
  rw [cost709_eq]
  decide

theorem head710 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard646.name, Chunk40.stackResult710.1)).2 ≤ 7313 := by
  rw [cost710_eq]
  decide

theorem head711 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard647.name, Chunk40.stackResult711.1)).2 ≤ 7313 := by
  rw [cost711_eq]
  decide

theorem head712 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard648.name, Chunk40.stackResult712.1)).2 ≤ 7313 := by
  rw [cost712_eq]
  decide

theorem head713 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard649.name, Chunk40.stackResult713.1)).2 ≤ 7313 := by
  rw [cost713_eq]
  decide

theorem head714 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard650.name, Chunk40.stackResult714.1)).2 ≤ 7313 := by
  rw [cost714_eq]
  decide

theorem head715 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard651.name, Chunk40.stackResult715.1)).2 ≤ 7313 := by
  rw [cost715_eq]
  decide

theorem head716 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard652.name, Chunk40.stackResult716.1)).2 ≤ 7313 := by
  rw [cost716_eq]
  decide

theorem head717 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard653.name, Chunk40.stackResult717.1)).2 ≤ 7313 := by
  rw [cost717_eq]
  decide

theorem head718 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard654.name, Chunk40.stackResult718.1)).2 ≤ 7313 := by
  rw [cost718_eq]
  decide

theorem head719 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard655.name, Chunk40.stackResult719.1)).2 ≤ 7313 := by
  rw [cost719_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk40.bodies := by
  unfold Chunk40.bodies
  apply bounded_cons _ _ _ head704
  apply bounded_cons _ _ _ head705
  apply bounded_cons _ _ _ head706
  apply bounded_cons _ _ _ head707
  apply bounded_cons _ _ _ head708
  apply bounded_cons _ _ _ head709
  apply bounded_cons _ _ _ head710
  apply bounded_cons _ _ _ head711
  apply bounded_cons _ _ _ head712
  apply bounded_cons _ _ _ head713
  apply bounded_cons _ _ _ head714
  apply bounded_cons _ _ _ head715
  apply bounded_cons _ _ _ head716
  apply bounded_cons _ _ _ head717
  apply bounded_cons _ _ _ head718
  apply bounded_cons _ _ _ head719
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded40
