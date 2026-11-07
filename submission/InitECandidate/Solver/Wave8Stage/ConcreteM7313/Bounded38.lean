import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk38
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded38
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open StackToLabClock LoweredBudget

wave8_kernel_reduce cost672 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard608.name, Chunk38.stackResult672.1)).2
wave8_kernel_reduce cost673 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard609.name, Chunk38.stackResult673.1)).2
wave8_kernel_reduce cost674 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard610.name, Chunk38.stackResult674.1)).2
wave8_kernel_reduce cost675 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard611.name, Chunk38.stackResult675.1)).2
wave8_kernel_reduce cost676 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard612.name, Chunk38.stackResult676.1)).2
wave8_kernel_reduce cost677 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard613.name, Chunk38.stackResult677.1)).2
wave8_kernel_reduce cost678 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard614.name, Chunk38.stackResult678.1)).2
wave8_kernel_reduce cost679 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard615.name, Chunk38.stackResult679.1)).2
wave8_kernel_reduce cost680 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard616.name, Chunk38.stackResult680.1)).2
wave8_kernel_reduce cost681 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard617.name, Chunk38.stackResult681.1)).2
wave8_kernel_reduce cost682 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard618.name, Chunk38.stackResult682.1)).2
wave8_kernel_reduce cost683 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard619.name, Chunk38.stackResult683.1)).2
wave8_kernel_reduce cost684 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard620.name, Chunk38.stackResult684.1)).2
wave8_kernel_reduce cost685 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard621.name, Chunk38.stackResult685.1)).2
wave8_kernel_reduce cost686 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard622.name, Chunk38.stackResult686.1)).2
wave8_kernel_reduce cost687 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard623.name, Chunk38.stackResult687.1)).2

theorem head672 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard608.name, Chunk38.stackResult672.1)).2 ≤ 7313 := by
  rw [cost672_eq]
  decide

theorem head673 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard609.name, Chunk38.stackResult673.1)).2 ≤ 7313 := by
  rw [cost673_eq]
  decide

theorem head674 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard610.name, Chunk38.stackResult674.1)).2 ≤ 7313 := by
  rw [cost674_eq]
  decide

theorem head675 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard611.name, Chunk38.stackResult675.1)).2 ≤ 7313 := by
  rw [cost675_eq]
  decide

theorem head676 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard612.name, Chunk38.stackResult676.1)).2 ≤ 7313 := by
  rw [cost676_eq]
  decide

theorem head677 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard613.name, Chunk38.stackResult677.1)).2 ≤ 7313 := by
  rw [cost677_eq]
  decide

theorem head678 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard614.name, Chunk38.stackResult678.1)).2 ≤ 7313 := by
  rw [cost678_eq]
  decide

theorem head679 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard615.name, Chunk38.stackResult679.1)).2 ≤ 7313 := by
  rw [cost679_eq]
  decide

theorem head680 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard616.name, Chunk38.stackResult680.1)).2 ≤ 7313 := by
  rw [cost680_eq]
  decide

theorem head681 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard617.name, Chunk38.stackResult681.1)).2 ≤ 7313 := by
  rw [cost681_eq]
  decide

theorem head682 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard618.name, Chunk38.stackResult682.1)).2 ≤ 7313 := by
  rw [cost682_eq]
  decide

theorem head683 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard619.name, Chunk38.stackResult683.1)).2 ≤ 7313 := by
  rw [cost683_eq]
  decide

theorem head684 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard620.name, Chunk38.stackResult684.1)).2 ≤ 7313 := by
  rw [cost684_eq]
  decide

theorem head685 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard621.name, Chunk38.stackResult685.1)).2 ≤ 7313 := by
  rw [cost685_eq]
  decide

theorem head686 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard622.name, Chunk38.stackResult686.1)).2 ≤ 7313 := by
  rw [cost686_eq]
  decide

theorem head687 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard623.name, Chunk38.stackResult687.1)).2 ≤ 7313 := by
  rw [cost687_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk38.bodies := by
  unfold Chunk38.bodies
  apply bounded_cons _ _ _ head672
  apply bounded_cons _ _ _ head673
  apply bounded_cons _ _ _ head674
  apply bounded_cons _ _ _ head675
  apply bounded_cons _ _ _ head676
  apply bounded_cons _ _ _ head677
  apply bounded_cons _ _ _ head678
  apply bounded_cons _ _ _ head679
  apply bounded_cons _ _ _ head680
  apply bounded_cons _ _ _ head681
  apply bounded_cons _ _ _ head682
  apply bounded_cons _ _ _ head683
  apply bounded_cons _ _ _ head684
  apply bounded_cons _ _ _ head685
  apply bounded_cons _ _ _ head686
  apply bounded_cons _ _ _ head687
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded38
