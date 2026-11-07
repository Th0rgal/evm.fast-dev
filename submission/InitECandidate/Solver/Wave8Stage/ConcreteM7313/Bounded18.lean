import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk18
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded18
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open StackToLabClock LoweredBudget

wave8_kernel_reduce cost352 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard288.name, Chunk18.stackResult352.1)).2
wave8_kernel_reduce cost353 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard289.name, Chunk18.stackResult353.1)).2
wave8_kernel_reduce cost354 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard290.name, Chunk18.stackResult354.1)).2
wave8_kernel_reduce cost355 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard291.name, Chunk18.stackResult355.1)).2
wave8_kernel_reduce cost356 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard292.name, Chunk18.stackResult356.1)).2
wave8_kernel_reduce cost357 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard293.name, Chunk18.stackResult357.1)).2
wave8_kernel_reduce cost358 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard294.name, Chunk18.stackResult358.1)).2
wave8_kernel_reduce cost359 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard295.name, Chunk18.stackResult359.1)).2
wave8_kernel_reduce cost360 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard296.name, Chunk18.stackResult360.1)).2
wave8_kernel_reduce cost361 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard297.name, Chunk18.stackResult361.1)).2
wave8_kernel_reduce cost362 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard298.name, Chunk18.stackResult362.1)).2
wave8_kernel_reduce cost363 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard299.name, Chunk18.stackResult363.1)).2
wave8_kernel_reduce cost364 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard300.name, Chunk18.stackResult364.1)).2
wave8_kernel_reduce cost365 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard301.name, Chunk18.stackResult365.1)).2
wave8_kernel_reduce cost366 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard302.name, Chunk18.stackResult366.1)).2
wave8_kernel_reduce cost367 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard303.name, Chunk18.stackResult367.1)).2

theorem head352 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard288.name, Chunk18.stackResult352.1)).2 ≤ 7313 := by
  rw [cost352_eq]
  decide

theorem head353 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard289.name, Chunk18.stackResult353.1)).2 ≤ 7313 := by
  rw [cost353_eq]
  decide

theorem head354 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard290.name, Chunk18.stackResult354.1)).2 ≤ 7313 := by
  rw [cost354_eq]
  decide

theorem head355 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard291.name, Chunk18.stackResult355.1)).2 ≤ 7313 := by
  rw [cost355_eq]
  decide

theorem head356 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard292.name, Chunk18.stackResult356.1)).2 ≤ 7313 := by
  rw [cost356_eq]
  decide

theorem head357 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard293.name, Chunk18.stackResult357.1)).2 ≤ 7313 := by
  rw [cost357_eq]
  decide

theorem head358 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard294.name, Chunk18.stackResult358.1)).2 ≤ 7313 := by
  rw [cost358_eq]
  decide

theorem head359 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard295.name, Chunk18.stackResult359.1)).2 ≤ 7313 := by
  rw [cost359_eq]
  decide

theorem head360 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard296.name, Chunk18.stackResult360.1)).2 ≤ 7313 := by
  rw [cost360_eq]
  decide

theorem head361 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard297.name, Chunk18.stackResult361.1)).2 ≤ 7313 := by
  rw [cost361_eq]
  decide

theorem head362 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard298.name, Chunk18.stackResult362.1)).2 ≤ 7313 := by
  rw [cost362_eq]
  decide

theorem head363 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard299.name, Chunk18.stackResult363.1)).2 ≤ 7313 := by
  rw [cost363_eq]
  decide

theorem head364 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard300.name, Chunk18.stackResult364.1)).2 ≤ 7313 := by
  rw [cost364_eq]
  decide

theorem head365 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard301.name, Chunk18.stackResult365.1)).2 ≤ 7313 := by
  rw [cost365_eq]
  decide

theorem head366 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard302.name, Chunk18.stackResult366.1)).2 ≤ 7313 := by
  rw [cost366_eq]
  decide

theorem head367 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard303.name, Chunk18.stackResult367.1)).2 ≤ 7313 := by
  rw [cost367_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk18.bodies := by
  unfold Chunk18.bodies
  apply bounded_cons _ _ _ head352
  apply bounded_cons _ _ _ head353
  apply bounded_cons _ _ _ head354
  apply bounded_cons _ _ _ head355
  apply bounded_cons _ _ _ head356
  apply bounded_cons _ _ _ head357
  apply bounded_cons _ _ _ head358
  apply bounded_cons _ _ _ head359
  apply bounded_cons _ _ _ head360
  apply bounded_cons _ _ _ head361
  apply bounded_cons _ _ _ head362
  apply bounded_cons _ _ _ head363
  apply bounded_cons _ _ _ head364
  apply bounded_cons _ _ _ head365
  apply bounded_cons _ _ _ head366
  apply bounded_cons _ _ _ head367
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded18
