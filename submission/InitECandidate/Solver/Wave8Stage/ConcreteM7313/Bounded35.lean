import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk35
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded35
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open StackToLabClock LoweredBudget

wave8_kernel_reduce cost624 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard560.name, Chunk35.stackResult624.1)).2
wave8_kernel_reduce cost625 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard561.name, Chunk35.stackResult625.1)).2
wave8_kernel_reduce cost626 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard562.name, Chunk35.stackResult626.1)).2
wave8_kernel_reduce cost627 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard563.name, Chunk35.stackResult627.1)).2
wave8_kernel_reduce cost628 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard564.name, Chunk35.stackResult628.1)).2
wave8_kernel_reduce cost629 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard565.name, Chunk35.stackResult629.1)).2
wave8_kernel_reduce cost630 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard566.name, Chunk35.stackResult630.1)).2
wave8_kernel_reduce cost631 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard567.name, Chunk35.stackResult631.1)).2
wave8_kernel_reduce cost632 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard568.name, Chunk35.stackResult632.1)).2
wave8_kernel_reduce cost633 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard569.name, Chunk35.stackResult633.1)).2
wave8_kernel_reduce cost634 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard570.name, Chunk35.stackResult634.1)).2
wave8_kernel_reduce cost635 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard571.name, Chunk35.stackResult635.1)).2
wave8_kernel_reduce cost636 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard572.name, Chunk35.stackResult636.1)).2
wave8_kernel_reduce cost637 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard573.name, Chunk35.stackResult637.1)).2
wave8_kernel_reduce cost638 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard574.name, Chunk35.stackResult638.1)).2
wave8_kernel_reduce cost639 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard575.name, Chunk35.stackResult639.1)).2

theorem head624 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard560.name, Chunk35.stackResult624.1)).2 ≤ 7313 := by
  rw [cost624_eq]
  decide

theorem head625 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard561.name, Chunk35.stackResult625.1)).2 ≤ 7313 := by
  rw [cost625_eq]
  decide

theorem head626 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard562.name, Chunk35.stackResult626.1)).2 ≤ 7313 := by
  rw [cost626_eq]
  decide

theorem head627 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard563.name, Chunk35.stackResult627.1)).2 ≤ 7313 := by
  rw [cost627_eq]
  decide

theorem head628 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard564.name, Chunk35.stackResult628.1)).2 ≤ 7313 := by
  rw [cost628_eq]
  decide

theorem head629 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard565.name, Chunk35.stackResult629.1)).2 ≤ 7313 := by
  rw [cost629_eq]
  decide

theorem head630 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard566.name, Chunk35.stackResult630.1)).2 ≤ 7313 := by
  rw [cost630_eq]
  decide

theorem head631 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard567.name, Chunk35.stackResult631.1)).2 ≤ 7313 := by
  rw [cost631_eq]
  decide

theorem head632 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard568.name, Chunk35.stackResult632.1)).2 ≤ 7313 := by
  rw [cost632_eq]
  decide

theorem head633 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard569.name, Chunk35.stackResult633.1)).2 ≤ 7313 := by
  rw [cost633_eq]
  decide

theorem head634 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard570.name, Chunk35.stackResult634.1)).2 ≤ 7313 := by
  rw [cost634_eq]
  decide

theorem head635 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard571.name, Chunk35.stackResult635.1)).2 ≤ 7313 := by
  rw [cost635_eq]
  decide

theorem head636 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard572.name, Chunk35.stackResult636.1)).2 ≤ 7313 := by
  rw [cost636_eq]
  decide

theorem head637 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard573.name, Chunk35.stackResult637.1)).2 ≤ 7313 := by
  rw [cost637_eq]
  decide

theorem head638 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard574.name, Chunk35.stackResult638.1)).2 ≤ 7313 := by
  rw [cost638_eq]
  decide

theorem head639 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard575.name, Chunk35.stackResult639.1)).2 ≤ 7313 := by
  rw [cost639_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk35.bodies := by
  unfold Chunk35.bodies
  apply bounded_cons _ _ _ head624
  apply bounded_cons _ _ _ head625
  apply bounded_cons _ _ _ head626
  apply bounded_cons _ _ _ head627
  apply bounded_cons _ _ _ head628
  apply bounded_cons _ _ _ head629
  apply bounded_cons _ _ _ head630
  apply bounded_cons _ _ _ head631
  apply bounded_cons _ _ _ head632
  apply bounded_cons _ _ _ head633
  apply bounded_cons _ _ _ head634
  apply bounded_cons _ _ _ head635
  apply bounded_cons _ _ _ head636
  apply bounded_cons _ _ _ head637
  apply bounded_cons _ _ _ head638
  apply bounded_cons _ _ _ head639
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded35
