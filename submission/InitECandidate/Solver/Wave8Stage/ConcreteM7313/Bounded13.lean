import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk13
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded13
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open StackToLabClock LoweredBudget

wave8_kernel_reduce cost272 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard208.name, Chunk13.stackResult272.1)).2
wave8_kernel_reduce cost273 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard209.name, Chunk13.stackResult273.1)).2
wave8_kernel_reduce cost274 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard210.name, Chunk13.stackResult274.1)).2
wave8_kernel_reduce cost275 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard211.name, Chunk13.stackResult275.1)).2
wave8_kernel_reduce cost276 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard212.name, Chunk13.stackResult276.1)).2
wave8_kernel_reduce cost277 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard213.name, Chunk13.stackResult277.1)).2
wave8_kernel_reduce cost278 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard214.name, Chunk13.stackResult278.1)).2
wave8_kernel_reduce cost279 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard215.name, Chunk13.stackResult279.1)).2
wave8_kernel_reduce cost280 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard216.name, Chunk13.stackResult280.1)).2
wave8_kernel_reduce cost281 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard217.name, Chunk13.stackResult281.1)).2
wave8_kernel_reduce cost282 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard218.name, Chunk13.stackResult282.1)).2
wave8_kernel_reduce cost283 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard219.name, Chunk13.stackResult283.1)).2
wave8_kernel_reduce cost284 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard220.name, Chunk13.stackResult284.1)).2
wave8_kernel_reduce cost285 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard221.name, Chunk13.stackResult285.1)).2
wave8_kernel_reduce cost286 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard222.name, Chunk13.stackResult286.1)).2
wave8_kernel_reduce cost287 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard223.name, Chunk13.stackResult287.1)).2

theorem head272 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard208.name, Chunk13.stackResult272.1)).2 ≤ 7313 := by
  rw [cost272_eq]
  decide

theorem head273 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard209.name, Chunk13.stackResult273.1)).2 ≤ 7313 := by
  rw [cost273_eq]
  decide

theorem head274 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard210.name, Chunk13.stackResult274.1)).2 ≤ 7313 := by
  rw [cost274_eq]
  decide

theorem head275 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard211.name, Chunk13.stackResult275.1)).2 ≤ 7313 := by
  rw [cost275_eq]
  decide

theorem head276 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard212.name, Chunk13.stackResult276.1)).2 ≤ 7313 := by
  rw [cost276_eq]
  decide

theorem head277 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard213.name, Chunk13.stackResult277.1)).2 ≤ 7313 := by
  rw [cost277_eq]
  decide

theorem head278 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard214.name, Chunk13.stackResult278.1)).2 ≤ 7313 := by
  rw [cost278_eq]
  decide

theorem head279 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard215.name, Chunk13.stackResult279.1)).2 ≤ 7313 := by
  rw [cost279_eq]
  decide

theorem head280 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard216.name, Chunk13.stackResult280.1)).2 ≤ 7313 := by
  rw [cost280_eq]
  decide

theorem head281 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard217.name, Chunk13.stackResult281.1)).2 ≤ 7313 := by
  rw [cost281_eq]
  decide

theorem head282 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard218.name, Chunk13.stackResult282.1)).2 ≤ 7313 := by
  rw [cost282_eq]
  decide

theorem head283 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard219.name, Chunk13.stackResult283.1)).2 ≤ 7313 := by
  rw [cost283_eq]
  decide

theorem head284 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard220.name, Chunk13.stackResult284.1)).2 ≤ 7313 := by
  rw [cost284_eq]
  decide

theorem head285 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard221.name, Chunk13.stackResult285.1)).2 ≤ 7313 := by
  rw [cost285_eq]
  decide

theorem head286 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard222.name, Chunk13.stackResult286.1)).2 ≤ 7313 := by
  rw [cost286_eq]
  decide

theorem head287 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard223.name, Chunk13.stackResult287.1)).2 ≤ 7313 := by
  rw [cost287_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk13.bodies := by
  unfold Chunk13.bodies
  apply bounded_cons _ _ _ head272
  apply bounded_cons _ _ _ head273
  apply bounded_cons _ _ _ head274
  apply bounded_cons _ _ _ head275
  apply bounded_cons _ _ _ head276
  apply bounded_cons _ _ _ head277
  apply bounded_cons _ _ _ head278
  apply bounded_cons _ _ _ head279
  apply bounded_cons _ _ _ head280
  apply bounded_cons _ _ _ head281
  apply bounded_cons _ _ _ head282
  apply bounded_cons _ _ _ head283
  apply bounded_cons _ _ _ head284
  apply bounded_cons _ _ _ head285
  apply bounded_cons _ _ _ head286
  apply bounded_cons _ _ _ head287
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded13
