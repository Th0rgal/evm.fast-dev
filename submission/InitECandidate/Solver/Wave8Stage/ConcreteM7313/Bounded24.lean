import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk24
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded24
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open StackToLabClock LoweredBudget

wave8_kernel_reduce cost448 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard384.name, Chunk24.stackResult448.1)).2
wave8_kernel_reduce cost449 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard385.name, Chunk24.stackResult449.1)).2
wave8_kernel_reduce cost450 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard386.name, Chunk24.stackResult450.1)).2
wave8_kernel_reduce cost451 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard387.name, Chunk24.stackResult451.1)).2
wave8_kernel_reduce cost452 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard388.name, Chunk24.stackResult452.1)).2
wave8_kernel_reduce cost453 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard389.name, Chunk24.stackResult453.1)).2
wave8_kernel_reduce cost454 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard390.name, Chunk24.stackResult454.1)).2
wave8_kernel_reduce cost455 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard391.name, Chunk24.stackResult455.1)).2
wave8_kernel_reduce cost456 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard392.name, Chunk24.stackResult456.1)).2
wave8_kernel_reduce cost457 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard393.name, Chunk24.stackResult457.1)).2
wave8_kernel_reduce cost458 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard394.name, Chunk24.stackResult458.1)).2
wave8_kernel_reduce cost459 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard395.name, Chunk24.stackResult459.1)).2
wave8_kernel_reduce cost460 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard396.name, Chunk24.stackResult460.1)).2
wave8_kernel_reduce cost461 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard397.name, Chunk24.stackResult461.1)).2
wave8_kernel_reduce cost462 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard398.name, Chunk24.stackResult462.1)).2
wave8_kernel_reduce cost463 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard399.name, Chunk24.stackResult463.1)).2

theorem head448 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard384.name, Chunk24.stackResult448.1)).2 ≤ 7313 := by
  rw [cost448_eq]
  decide

theorem head449 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard385.name, Chunk24.stackResult449.1)).2 ≤ 7313 := by
  rw [cost449_eq]
  decide

theorem head450 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard386.name, Chunk24.stackResult450.1)).2 ≤ 7313 := by
  rw [cost450_eq]
  decide

theorem head451 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard387.name, Chunk24.stackResult451.1)).2 ≤ 7313 := by
  rw [cost451_eq]
  decide

theorem head452 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard388.name, Chunk24.stackResult452.1)).2 ≤ 7313 := by
  rw [cost452_eq]
  decide

theorem head453 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard389.name, Chunk24.stackResult453.1)).2 ≤ 7313 := by
  rw [cost453_eq]
  decide

theorem head454 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard390.name, Chunk24.stackResult454.1)).2 ≤ 7313 := by
  rw [cost454_eq]
  decide

theorem head455 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard391.name, Chunk24.stackResult455.1)).2 ≤ 7313 := by
  rw [cost455_eq]
  decide

theorem head456 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard392.name, Chunk24.stackResult456.1)).2 ≤ 7313 := by
  rw [cost456_eq]
  decide

theorem head457 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard393.name, Chunk24.stackResult457.1)).2 ≤ 7313 := by
  rw [cost457_eq]
  decide

theorem head458 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard394.name, Chunk24.stackResult458.1)).2 ≤ 7313 := by
  rw [cost458_eq]
  decide

theorem head459 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard395.name, Chunk24.stackResult459.1)).2 ≤ 7313 := by
  rw [cost459_eq]
  decide

theorem head460 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard396.name, Chunk24.stackResult460.1)).2 ≤ 7313 := by
  rw [cost460_eq]
  decide

theorem head461 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard397.name, Chunk24.stackResult461.1)).2 ≤ 7313 := by
  rw [cost461_eq]
  decide

theorem head462 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard398.name, Chunk24.stackResult462.1)).2 ≤ 7313 := by
  rw [cost462_eq]
  decide

theorem head463 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard399.name, Chunk24.stackResult463.1)).2 ≤ 7313 := by
  rw [cost463_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk24.bodies := by
  unfold Chunk24.bodies
  apply bounded_cons _ _ _ head448
  apply bounded_cons _ _ _ head449
  apply bounded_cons _ _ _ head450
  apply bounded_cons _ _ _ head451
  apply bounded_cons _ _ _ head452
  apply bounded_cons _ _ _ head453
  apply bounded_cons _ _ _ head454
  apply bounded_cons _ _ _ head455
  apply bounded_cons _ _ _ head456
  apply bounded_cons _ _ _ head457
  apply bounded_cons _ _ _ head458
  apply bounded_cons _ _ _ head459
  apply bounded_cons _ _ _ head460
  apply bounded_cons _ _ _ head461
  apply bounded_cons _ _ _ head462
  apply bounded_cons _ _ _ head463
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded24
