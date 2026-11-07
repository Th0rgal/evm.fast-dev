import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk21
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded21
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open StackToLabClock LoweredBudget

wave8_kernel_reduce cost400 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard336.name, Chunk21.stackResult400.1)).2
wave8_kernel_reduce cost401 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard337.name, Chunk21.stackResult401.1)).2
wave8_kernel_reduce cost402 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard338.name, Chunk21.stackResult402.1)).2
wave8_kernel_reduce cost403 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard339.name, Chunk21.stackResult403.1)).2
wave8_kernel_reduce cost404 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard340.name, Chunk21.stackResult404.1)).2
wave8_kernel_reduce cost405 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard341.name, Chunk21.stackResult405.1)).2
wave8_kernel_reduce cost406 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard342.name, Chunk21.stackResult406.1)).2
wave8_kernel_reduce cost407 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard343.name, Chunk21.stackResult407.1)).2
wave8_kernel_reduce cost408 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard344.name, Chunk21.stackResult408.1)).2
wave8_kernel_reduce cost409 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard345.name, Chunk21.stackResult409.1)).2
wave8_kernel_reduce cost410 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard346.name, Chunk21.stackResult410.1)).2
wave8_kernel_reduce cost411 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard347.name, Chunk21.stackResult411.1)).2
wave8_kernel_reduce cost412 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard348.name, Chunk21.stackResult412.1)).2
wave8_kernel_reduce cost413 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard349.name, Chunk21.stackResult413.1)).2
wave8_kernel_reduce cost414 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard350.name, Chunk21.stackResult414.1)).2
wave8_kernel_reduce cost415 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard351.name, Chunk21.stackResult415.1)).2

theorem head400 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard336.name, Chunk21.stackResult400.1)).2 ≤ 7313 := by
  rw [cost400_eq]
  decide

theorem head401 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard337.name, Chunk21.stackResult401.1)).2 ≤ 7313 := by
  rw [cost401_eq]
  decide

theorem head402 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard338.name, Chunk21.stackResult402.1)).2 ≤ 7313 := by
  rw [cost402_eq]
  decide

theorem head403 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard339.name, Chunk21.stackResult403.1)).2 ≤ 7313 := by
  rw [cost403_eq]
  decide

theorem head404 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard340.name, Chunk21.stackResult404.1)).2 ≤ 7313 := by
  rw [cost404_eq]
  decide

theorem head405 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard341.name, Chunk21.stackResult405.1)).2 ≤ 7313 := by
  rw [cost405_eq]
  decide

theorem head406 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard342.name, Chunk21.stackResult406.1)).2 ≤ 7313 := by
  rw [cost406_eq]
  decide

theorem head407 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard343.name, Chunk21.stackResult407.1)).2 ≤ 7313 := by
  rw [cost407_eq]
  decide

theorem head408 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard344.name, Chunk21.stackResult408.1)).2 ≤ 7313 := by
  rw [cost408_eq]
  decide

theorem head409 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard345.name, Chunk21.stackResult409.1)).2 ≤ 7313 := by
  rw [cost409_eq]
  decide

theorem head410 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard346.name, Chunk21.stackResult410.1)).2 ≤ 7313 := by
  rw [cost410_eq]
  decide

theorem head411 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard347.name, Chunk21.stackResult411.1)).2 ≤ 7313 := by
  rw [cost411_eq]
  decide

theorem head412 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard348.name, Chunk21.stackResult412.1)).2 ≤ 7313 := by
  rw [cost412_eq]
  decide

theorem head413 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard349.name, Chunk21.stackResult413.1)).2 ≤ 7313 := by
  rw [cost413_eq]
  decide

theorem head414 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard350.name, Chunk21.stackResult414.1)).2 ≤ 7313 := by
  rw [cost414_eq]
  decide

theorem head415 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard351.name, Chunk21.stackResult415.1)).2 ≤ 7313 := by
  rw [cost415_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk21.bodies := by
  unfold Chunk21.bodies
  apply bounded_cons _ _ _ head400
  apply bounded_cons _ _ _ head401
  apply bounded_cons _ _ _ head402
  apply bounded_cons _ _ _ head403
  apply bounded_cons _ _ _ head404
  apply bounded_cons _ _ _ head405
  apply bounded_cons _ _ _ head406
  apply bounded_cons _ _ _ head407
  apply bounded_cons _ _ _ head408
  apply bounded_cons _ _ _ head409
  apply bounded_cons _ _ _ head410
  apply bounded_cons _ _ _ head411
  apply bounded_cons _ _ _ head412
  apply bounded_cons _ _ _ head413
  apply bounded_cons _ _ _ head414
  apply bounded_cons _ _ _ head415
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded21
