import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk26
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded26
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open StackToLabClock LoweredBudget

wave8_kernel_reduce cost480 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard416.name, Chunk26.stackResult480.1)).2
wave8_kernel_reduce cost481 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard417.name, Chunk26.stackResult481.1)).2
wave8_kernel_reduce cost482 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard418.name, Chunk26.stackResult482.1)).2
wave8_kernel_reduce cost483 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard419.name, Chunk26.stackResult483.1)).2
wave8_kernel_reduce cost484 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard420.name, Chunk26.stackResult484.1)).2
wave8_kernel_reduce cost485 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard421.name, Chunk26.stackResult485.1)).2
wave8_kernel_reduce cost486 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard422.name, Chunk26.stackResult486.1)).2
wave8_kernel_reduce cost487 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard423.name, Chunk26.stackResult487.1)).2
wave8_kernel_reduce cost488 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard424.name, Chunk26.stackResult488.1)).2
wave8_kernel_reduce cost489 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard425.name, Chunk26.stackResult489.1)).2
wave8_kernel_reduce cost490 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard426.name, Chunk26.stackResult490.1)).2
wave8_kernel_reduce cost491 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard427.name, Chunk26.stackResult491.1)).2
wave8_kernel_reduce cost492 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard428.name, Chunk26.stackResult492.1)).2
wave8_kernel_reduce cost493 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard429.name, Chunk26.stackResult493.1)).2
wave8_kernel_reduce cost494 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard430.name, Chunk26.stackResult494.1)).2
wave8_kernel_reduce cost495 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard431.name, Chunk26.stackResult495.1)).2

theorem head480 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard416.name, Chunk26.stackResult480.1)).2 ≤ 7313 := by
  rw [cost480_eq]
  decide

theorem head481 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard417.name, Chunk26.stackResult481.1)).2 ≤ 7313 := by
  rw [cost481_eq]
  decide

theorem head482 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard418.name, Chunk26.stackResult482.1)).2 ≤ 7313 := by
  rw [cost482_eq]
  decide

theorem head483 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard419.name, Chunk26.stackResult483.1)).2 ≤ 7313 := by
  rw [cost483_eq]
  decide

theorem head484 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard420.name, Chunk26.stackResult484.1)).2 ≤ 7313 := by
  rw [cost484_eq]
  decide

theorem head485 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard421.name, Chunk26.stackResult485.1)).2 ≤ 7313 := by
  rw [cost485_eq]
  decide

theorem head486 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard422.name, Chunk26.stackResult486.1)).2 ≤ 7313 := by
  rw [cost486_eq]
  decide

theorem head487 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard423.name, Chunk26.stackResult487.1)).2 ≤ 7313 := by
  rw [cost487_eq]
  decide

theorem head488 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard424.name, Chunk26.stackResult488.1)).2 ≤ 7313 := by
  rw [cost488_eq]
  decide

theorem head489 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard425.name, Chunk26.stackResult489.1)).2 ≤ 7313 := by
  rw [cost489_eq]
  decide

theorem head490 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard426.name, Chunk26.stackResult490.1)).2 ≤ 7313 := by
  rw [cost490_eq]
  decide

theorem head491 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard427.name, Chunk26.stackResult491.1)).2 ≤ 7313 := by
  rw [cost491_eq]
  decide

theorem head492 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard428.name, Chunk26.stackResult492.1)).2 ≤ 7313 := by
  rw [cost492_eq]
  decide

theorem head493 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard429.name, Chunk26.stackResult493.1)).2 ≤ 7313 := by
  rw [cost493_eq]
  decide

theorem head494 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard430.name, Chunk26.stackResult494.1)).2 ≤ 7313 := by
  rw [cost494_eq]
  decide

theorem head495 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard431.name, Chunk26.stackResult495.1)).2 ≤ 7313 := by
  rw [cost495_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk26.bodies := by
  unfold Chunk26.bodies
  apply bounded_cons _ _ _ head480
  apply bounded_cons _ _ _ head481
  apply bounded_cons _ _ _ head482
  apply bounded_cons _ _ _ head483
  apply bounded_cons _ _ _ head484
  apply bounded_cons _ _ _ head485
  apply bounded_cons _ _ _ head486
  apply bounded_cons _ _ _ head487
  apply bounded_cons _ _ _ head488
  apply bounded_cons _ _ _ head489
  apply bounded_cons _ _ _ head490
  apply bounded_cons _ _ _ head491
  apply bounded_cons _ _ _ head492
  apply bounded_cons _ _ _ head493
  apply bounded_cons _ _ _ head494
  apply bounded_cons _ _ _ head495
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded26
