import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk25
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded25
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open StackToLabClock LoweredBudget

wave8_kernel_reduce cost464 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard400.name, Chunk25.stackResult464.1)).2
wave8_kernel_reduce cost465 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard401.name, Chunk25.stackResult465.1)).2
wave8_kernel_reduce cost466 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard402.name, Chunk25.stackResult466.1)).2
wave8_kernel_reduce cost467 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard403.name, Chunk25.stackResult467.1)).2
wave8_kernel_reduce cost468 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard404.name, Chunk25.stackResult468.1)).2
wave8_kernel_reduce cost469 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard405.name, Chunk25.stackResult469.1)).2
wave8_kernel_reduce cost470 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard406.name, Chunk25.stackResult470.1)).2
wave8_kernel_reduce cost471 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard407.name, Chunk25.stackResult471.1)).2
wave8_kernel_reduce cost472 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard408.name, Chunk25.stackResult472.1)).2
wave8_kernel_reduce cost473 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard409.name, Chunk25.stackResult473.1)).2
wave8_kernel_reduce cost474 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard410.name, Chunk25.stackResult474.1)).2
wave8_kernel_reduce cost475 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard411.name, Chunk25.stackResult475.1)).2
wave8_kernel_reduce cost476 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard412.name, Chunk25.stackResult476.1)).2
wave8_kernel_reduce cost477 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard413.name, Chunk25.stackResult477.1)).2
wave8_kernel_reduce cost478 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard414.name, Chunk25.stackResult478.1)).2
wave8_kernel_reduce cost479 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard415.name, Chunk25.stackResult479.1)).2

theorem head464 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard400.name, Chunk25.stackResult464.1)).2 ≤ 7313 := by
  rw [cost464_eq]
  decide

theorem head465 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard401.name, Chunk25.stackResult465.1)).2 ≤ 7313 := by
  rw [cost465_eq]
  decide

theorem head466 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard402.name, Chunk25.stackResult466.1)).2 ≤ 7313 := by
  rw [cost466_eq]
  decide

theorem head467 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard403.name, Chunk25.stackResult467.1)).2 ≤ 7313 := by
  rw [cost467_eq]
  decide

theorem head468 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard404.name, Chunk25.stackResult468.1)).2 ≤ 7313 := by
  rw [cost468_eq]
  decide

theorem head469 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard405.name, Chunk25.stackResult469.1)).2 ≤ 7313 := by
  rw [cost469_eq]
  decide

theorem head470 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard406.name, Chunk25.stackResult470.1)).2 ≤ 7313 := by
  rw [cost470_eq]
  decide

theorem head471 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard407.name, Chunk25.stackResult471.1)).2 ≤ 7313 := by
  rw [cost471_eq]
  decide

theorem head472 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard408.name, Chunk25.stackResult472.1)).2 ≤ 7313 := by
  rw [cost472_eq]
  decide

theorem head473 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard409.name, Chunk25.stackResult473.1)).2 ≤ 7313 := by
  rw [cost473_eq]
  decide

theorem head474 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard410.name, Chunk25.stackResult474.1)).2 ≤ 7313 := by
  rw [cost474_eq]
  decide

theorem head475 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard411.name, Chunk25.stackResult475.1)).2 ≤ 7313 := by
  rw [cost475_eq]
  decide

theorem head476 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard412.name, Chunk25.stackResult476.1)).2 ≤ 7313 := by
  rw [cost476_eq]
  decide

theorem head477 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard413.name, Chunk25.stackResult477.1)).2 ≤ 7313 := by
  rw [cost477_eq]
  decide

theorem head478 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard414.name, Chunk25.stackResult478.1)).2 ≤ 7313 := by
  rw [cost478_eq]
  decide

theorem head479 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard415.name, Chunk25.stackResult479.1)).2 ≤ 7313 := by
  rw [cost479_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk25.bodies := by
  unfold Chunk25.bodies
  apply bounded_cons _ _ _ head464
  apply bounded_cons _ _ _ head465
  apply bounded_cons _ _ _ head466
  apply bounded_cons _ _ _ head467
  apply bounded_cons _ _ _ head468
  apply bounded_cons _ _ _ head469
  apply bounded_cons _ _ _ head470
  apply bounded_cons _ _ _ head471
  apply bounded_cons _ _ _ head472
  apply bounded_cons _ _ _ head473
  apply bounded_cons _ _ _ head474
  apply bounded_cons _ _ _ head475
  apply bounded_cons _ _ _ head476
  apply bounded_cons _ _ _ head477
  apply bounded_cons _ _ _ head478
  apply bounded_cons _ _ _ head479
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded25
