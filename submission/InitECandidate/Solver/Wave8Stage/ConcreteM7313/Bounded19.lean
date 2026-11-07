import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk19
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded19
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open StackToLabClock LoweredBudget

wave8_kernel_reduce cost368 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard304.name, Chunk19.stackResult368.1)).2
wave8_kernel_reduce cost369 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard305.name, Chunk19.stackResult369.1)).2
wave8_kernel_reduce cost370 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard306.name, Chunk19.stackResult370.1)).2
wave8_kernel_reduce cost371 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard307.name, Chunk19.stackResult371.1)).2
wave8_kernel_reduce cost372 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard308.name, Chunk19.stackResult372.1)).2
wave8_kernel_reduce cost373 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard309.name, Chunk19.stackResult373.1)).2
wave8_kernel_reduce cost374 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard310.name, Chunk19.stackResult374.1)).2
wave8_kernel_reduce cost375 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard311.name, Chunk19.stackResult375.1)).2
wave8_kernel_reduce cost376 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard312.name, Chunk19.stackResult376.1)).2
wave8_kernel_reduce cost377 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard313.name, Chunk19.stackResult377.1)).2
wave8_kernel_reduce cost378 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard314.name, Chunk19.stackResult378.1)).2
wave8_kernel_reduce cost379 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard315.name, Chunk19.stackResult379.1)).2
wave8_kernel_reduce cost380 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard316.name, Chunk19.stackResult380.1)).2
wave8_kernel_reduce cost381 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard317.name, Chunk19.stackResult381.1)).2
wave8_kernel_reduce cost382 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard318.name, Chunk19.stackResult382.1)).2
wave8_kernel_reduce cost383 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard319.name, Chunk19.stackResult383.1)).2

theorem head368 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard304.name, Chunk19.stackResult368.1)).2 ≤ 7313 := by
  rw [cost368_eq]
  decide

theorem head369 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard305.name, Chunk19.stackResult369.1)).2 ≤ 7313 := by
  rw [cost369_eq]
  decide

theorem head370 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard306.name, Chunk19.stackResult370.1)).2 ≤ 7313 := by
  rw [cost370_eq]
  decide

theorem head371 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard307.name, Chunk19.stackResult371.1)).2 ≤ 7313 := by
  rw [cost371_eq]
  decide

theorem head372 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard308.name, Chunk19.stackResult372.1)).2 ≤ 7313 := by
  rw [cost372_eq]
  decide

theorem head373 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard309.name, Chunk19.stackResult373.1)).2 ≤ 7313 := by
  rw [cost373_eq]
  decide

theorem head374 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard310.name, Chunk19.stackResult374.1)).2 ≤ 7313 := by
  rw [cost374_eq]
  decide

theorem head375 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard311.name, Chunk19.stackResult375.1)).2 ≤ 7313 := by
  rw [cost375_eq]
  decide

theorem head376 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard312.name, Chunk19.stackResult376.1)).2 ≤ 7313 := by
  rw [cost376_eq]
  decide

theorem head377 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard313.name, Chunk19.stackResult377.1)).2 ≤ 7313 := by
  rw [cost377_eq]
  decide

theorem head378 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard314.name, Chunk19.stackResult378.1)).2 ≤ 7313 := by
  rw [cost378_eq]
  decide

theorem head379 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard315.name, Chunk19.stackResult379.1)).2 ≤ 7313 := by
  rw [cost379_eq]
  decide

theorem head380 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard316.name, Chunk19.stackResult380.1)).2 ≤ 7313 := by
  rw [cost380_eq]
  decide

theorem head381 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard317.name, Chunk19.stackResult381.1)).2 ≤ 7313 := by
  rw [cost381_eq]
  decide

theorem head382 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard318.name, Chunk19.stackResult382.1)).2 ≤ 7313 := by
  rw [cost382_eq]
  decide

theorem head383 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard319.name, Chunk19.stackResult383.1)).2 ≤ 7313 := by
  rw [cost383_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk19.bodies := by
  unfold Chunk19.bodies
  apply bounded_cons _ _ _ head368
  apply bounded_cons _ _ _ head369
  apply bounded_cons _ _ _ head370
  apply bounded_cons _ _ _ head371
  apply bounded_cons _ _ _ head372
  apply bounded_cons _ _ _ head373
  apply bounded_cons _ _ _ head374
  apply bounded_cons _ _ _ head375
  apply bounded_cons _ _ _ head376
  apply bounded_cons _ _ _ head377
  apply bounded_cons _ _ _ head378
  apply bounded_cons _ _ _ head379
  apply bounded_cons _ _ _ head380
  apply bounded_cons _ _ _ head381
  apply bounded_cons _ _ _ head382
  apply bounded_cons _ _ _ head383
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded19
