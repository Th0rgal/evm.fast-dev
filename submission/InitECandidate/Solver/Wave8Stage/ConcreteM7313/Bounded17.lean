import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk17
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded17
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open StackToLabClock LoweredBudget

wave8_kernel_reduce cost336 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard272.name, Chunk17.stackResult336.1)).2
wave8_kernel_reduce cost337 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard273.name, Chunk17.stackResult337.1)).2
wave8_kernel_reduce cost338 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard274.name, Chunk17.stackResult338.1)).2
wave8_kernel_reduce cost339 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard275.name, Chunk17.stackResult339.1)).2
wave8_kernel_reduce cost340 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard276.name, Chunk17.stackResult340.1)).2
wave8_kernel_reduce cost341 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard277.name, Chunk17.stackResult341.1)).2
wave8_kernel_reduce cost342 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard278.name, Chunk17.stackResult342.1)).2
wave8_kernel_reduce cost343 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard279.name, Chunk17.stackResult343.1)).2
wave8_kernel_reduce cost344 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard280.name, Chunk17.stackResult344.1)).2
wave8_kernel_reduce cost345 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard281.name, Chunk17.stackResult345.1)).2
wave8_kernel_reduce cost346 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard282.name, Chunk17.stackResult346.1)).2
wave8_kernel_reduce cost347 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard283.name, Chunk17.stackResult347.1)).2
wave8_kernel_reduce cost348 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard284.name, Chunk17.stackResult348.1)).2
wave8_kernel_reduce cost349 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard285.name, Chunk17.stackResult349.1)).2
wave8_kernel_reduce cost350 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard286.name, Chunk17.stackResult350.1)).2
wave8_kernel_reduce cost351 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard287.name, Chunk17.stackResult351.1)).2

theorem head336 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard272.name, Chunk17.stackResult336.1)).2 ≤ 7313 := by
  rw [cost336_eq]
  decide

theorem head337 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard273.name, Chunk17.stackResult337.1)).2 ≤ 7313 := by
  rw [cost337_eq]
  decide

theorem head338 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard274.name, Chunk17.stackResult338.1)).2 ≤ 7313 := by
  rw [cost338_eq]
  decide

theorem head339 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard275.name, Chunk17.stackResult339.1)).2 ≤ 7313 := by
  rw [cost339_eq]
  decide

theorem head340 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard276.name, Chunk17.stackResult340.1)).2 ≤ 7313 := by
  rw [cost340_eq]
  decide

theorem head341 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard277.name, Chunk17.stackResult341.1)).2 ≤ 7313 := by
  rw [cost341_eq]
  decide

theorem head342 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard278.name, Chunk17.stackResult342.1)).2 ≤ 7313 := by
  rw [cost342_eq]
  decide

theorem head343 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard279.name, Chunk17.stackResult343.1)).2 ≤ 7313 := by
  rw [cost343_eq]
  decide

theorem head344 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard280.name, Chunk17.stackResult344.1)).2 ≤ 7313 := by
  rw [cost344_eq]
  decide

theorem head345 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard281.name, Chunk17.stackResult345.1)).2 ≤ 7313 := by
  rw [cost345_eq]
  decide

theorem head346 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard282.name, Chunk17.stackResult346.1)).2 ≤ 7313 := by
  rw [cost346_eq]
  decide

theorem head347 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard283.name, Chunk17.stackResult347.1)).2 ≤ 7313 := by
  rw [cost347_eq]
  decide

theorem head348 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard284.name, Chunk17.stackResult348.1)).2 ≤ 7313 := by
  rw [cost348_eq]
  decide

theorem head349 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard285.name, Chunk17.stackResult349.1)).2 ≤ 7313 := by
  rw [cost349_eq]
  decide

theorem head350 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard286.name, Chunk17.stackResult350.1)).2 ≤ 7313 := by
  rw [cost350_eq]
  decide

theorem head351 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard287.name, Chunk17.stackResult351.1)).2 ≤ 7313 := by
  rw [cost351_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk17.bodies := by
  unfold Chunk17.bodies
  apply bounded_cons _ _ _ head336
  apply bounded_cons _ _ _ head337
  apply bounded_cons _ _ _ head338
  apply bounded_cons _ _ _ head339
  apply bounded_cons _ _ _ head340
  apply bounded_cons _ _ _ head341
  apply bounded_cons _ _ _ head342
  apply bounded_cons _ _ _ head343
  apply bounded_cons _ _ _ head344
  apply bounded_cons _ _ _ head345
  apply bounded_cons _ _ _ head346
  apply bounded_cons _ _ _ head347
  apply bounded_cons _ _ _ head348
  apply bounded_cons _ _ _ head349
  apply bounded_cons _ _ _ head350
  apply bounded_cons _ _ _ head351
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded17
