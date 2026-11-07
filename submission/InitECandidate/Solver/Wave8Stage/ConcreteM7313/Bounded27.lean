import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk27
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded27
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open StackToLabClock LoweredBudget

wave8_kernel_reduce cost496 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard432.name, Chunk27.stackResult496.1)).2
wave8_kernel_reduce cost497 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard433.name, Chunk27.stackResult497.1)).2
wave8_kernel_reduce cost498 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard434.name, Chunk27.stackResult498.1)).2
wave8_kernel_reduce cost499 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard435.name, Chunk27.stackResult499.1)).2
wave8_kernel_reduce cost500 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard436.name, Chunk27.stackResult500.1)).2
wave8_kernel_reduce cost501 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard437.name, Chunk27.stackResult501.1)).2
wave8_kernel_reduce cost502 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard438.name, Chunk27.stackResult502.1)).2
wave8_kernel_reduce cost503 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard439.name, Chunk27.stackResult503.1)).2
wave8_kernel_reduce cost504 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard440.name, Chunk27.stackResult504.1)).2
wave8_kernel_reduce cost505 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard441.name, Chunk27.stackResult505.1)).2
wave8_kernel_reduce cost506 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard442.name, Chunk27.stackResult506.1)).2
wave8_kernel_reduce cost507 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard443.name, Chunk27.stackResult507.1)).2
wave8_kernel_reduce cost508 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard444.name, Chunk27.stackResult508.1)).2
wave8_kernel_reduce cost509 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard445.name, Chunk27.stackResult509.1)).2
wave8_kernel_reduce cost510 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard446.name, Chunk27.stackResult510.1)).2
wave8_kernel_reduce cost511 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard447.name, Chunk27.stackResult511.1)).2

theorem head496 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard432.name, Chunk27.stackResult496.1)).2 ≤ 7313 := by
  rw [cost496_eq]
  decide

theorem head497 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard433.name, Chunk27.stackResult497.1)).2 ≤ 7313 := by
  rw [cost497_eq]
  decide

theorem head498 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard434.name, Chunk27.stackResult498.1)).2 ≤ 7313 := by
  rw [cost498_eq]
  decide

theorem head499 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard435.name, Chunk27.stackResult499.1)).2 ≤ 7313 := by
  rw [cost499_eq]
  decide

theorem head500 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard436.name, Chunk27.stackResult500.1)).2 ≤ 7313 := by
  rw [cost500_eq]
  decide

theorem head501 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard437.name, Chunk27.stackResult501.1)).2 ≤ 7313 := by
  rw [cost501_eq]
  decide

theorem head502 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard438.name, Chunk27.stackResult502.1)).2 ≤ 7313 := by
  rw [cost502_eq]
  decide

theorem head503 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard439.name, Chunk27.stackResult503.1)).2 ≤ 7313 := by
  rw [cost503_eq]
  decide

theorem head504 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard440.name, Chunk27.stackResult504.1)).2 ≤ 7313 := by
  rw [cost504_eq]
  decide

theorem head505 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard441.name, Chunk27.stackResult505.1)).2 ≤ 7313 := by
  rw [cost505_eq]
  decide

theorem head506 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard442.name, Chunk27.stackResult506.1)).2 ≤ 7313 := by
  rw [cost506_eq]
  decide

theorem head507 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard443.name, Chunk27.stackResult507.1)).2 ≤ 7313 := by
  rw [cost507_eq]
  decide

theorem head508 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard444.name, Chunk27.stackResult508.1)).2 ≤ 7313 := by
  rw [cost508_eq]
  decide

theorem head509 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard445.name, Chunk27.stackResult509.1)).2 ≤ 7313 := by
  rw [cost509_eq]
  decide

theorem head510 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard446.name, Chunk27.stackResult510.1)).2 ≤ 7313 := by
  rw [cost510_eq]
  decide

theorem head511 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard447.name, Chunk27.stackResult511.1)).2 ≤ 7313 := by
  rw [cost511_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk27.bodies := by
  unfold Chunk27.bodies
  apply bounded_cons _ _ _ head496
  apply bounded_cons _ _ _ head497
  apply bounded_cons _ _ _ head498
  apply bounded_cons _ _ _ head499
  apply bounded_cons _ _ _ head500
  apply bounded_cons _ _ _ head501
  apply bounded_cons _ _ _ head502
  apply bounded_cons _ _ _ head503
  apply bounded_cons _ _ _ head504
  apply bounded_cons _ _ _ head505
  apply bounded_cons _ _ _ head506
  apply bounded_cons _ _ _ head507
  apply bounded_cons _ _ _ head508
  apply bounded_cons _ _ _ head509
  apply bounded_cons _ _ _ head510
  apply bounded_cons _ _ _ head511
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded27
