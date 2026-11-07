import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk37
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded37
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open StackToLabClock LoweredBudget

wave8_kernel_reduce cost656 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard592.name, Chunk37.stackResult656.1)).2
wave8_kernel_reduce cost657 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard593.name, Chunk37.stackResult657.1)).2
wave8_kernel_reduce cost658 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard594.name, Chunk37.stackResult658.1)).2
wave8_kernel_reduce cost659 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard595.name, Chunk37.stackResult659.1)).2
wave8_kernel_reduce cost660 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard596.name, Chunk37.stackResult660.1)).2
wave8_kernel_reduce cost661 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard597.name, Chunk37.stackResult661.1)).2
wave8_kernel_reduce cost662 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard598.name, Chunk37.stackResult662.1)).2
wave8_kernel_reduce cost663 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard599.name, Chunk37.stackResult663.1)).2
wave8_kernel_reduce cost664 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard600.name, Chunk37.stackResult664.1)).2
wave8_kernel_reduce cost665 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard601.name, Chunk37.stackResult665.1)).2
wave8_kernel_reduce cost666 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard602.name, Chunk37.stackResult666.1)).2
wave8_kernel_reduce cost667 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard603.name, Chunk37.stackResult667.1)).2
wave8_kernel_reduce cost668 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard604.name, Chunk37.stackResult668.1)).2
wave8_kernel_reduce cost669 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard605.name, Chunk37.stackResult669.1)).2
wave8_kernel_reduce cost670 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard606.name, Chunk37.stackResult670.1)).2
wave8_kernel_reduce cost671 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard607.name, Chunk37.stackResult671.1)).2

theorem head656 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard592.name, Chunk37.stackResult656.1)).2 ≤ 7313 := by
  rw [cost656_eq]
  decide

theorem head657 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard593.name, Chunk37.stackResult657.1)).2 ≤ 7313 := by
  rw [cost657_eq]
  decide

theorem head658 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard594.name, Chunk37.stackResult658.1)).2 ≤ 7313 := by
  rw [cost658_eq]
  decide

theorem head659 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard595.name, Chunk37.stackResult659.1)).2 ≤ 7313 := by
  rw [cost659_eq]
  decide

theorem head660 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard596.name, Chunk37.stackResult660.1)).2 ≤ 7313 := by
  rw [cost660_eq]
  decide

theorem head661 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard597.name, Chunk37.stackResult661.1)).2 ≤ 7313 := by
  rw [cost661_eq]
  decide

theorem head662 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard598.name, Chunk37.stackResult662.1)).2 ≤ 7313 := by
  rw [cost662_eq]
  decide

theorem head663 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard599.name, Chunk37.stackResult663.1)).2 ≤ 7313 := by
  rw [cost663_eq]
  decide

theorem head664 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard600.name, Chunk37.stackResult664.1)).2 ≤ 7313 := by
  rw [cost664_eq]
  decide

theorem head665 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard601.name, Chunk37.stackResult665.1)).2 ≤ 7313 := by
  rw [cost665_eq]
  decide

theorem head666 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard602.name, Chunk37.stackResult666.1)).2 ≤ 7313 := by
  rw [cost666_eq]
  decide

theorem head667 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard603.name, Chunk37.stackResult667.1)).2 ≤ 7313 := by
  rw [cost667_eq]
  decide

theorem head668 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard604.name, Chunk37.stackResult668.1)).2 ≤ 7313 := by
  rw [cost668_eq]
  decide

theorem head669 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard605.name, Chunk37.stackResult669.1)).2 ≤ 7313 := by
  rw [cost669_eq]
  decide

theorem head670 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard606.name, Chunk37.stackResult670.1)).2 ≤ 7313 := by
  rw [cost670_eq]
  decide

theorem head671 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard607.name, Chunk37.stackResult671.1)).2 ≤ 7313 := by
  rw [cost671_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk37.bodies := by
  unfold Chunk37.bodies
  apply bounded_cons _ _ _ head656
  apply bounded_cons _ _ _ head657
  apply bounded_cons _ _ _ head658
  apply bounded_cons _ _ _ head659
  apply bounded_cons _ _ _ head660
  apply bounded_cons _ _ _ head661
  apply bounded_cons _ _ _ head662
  apply bounded_cons _ _ _ head663
  apply bounded_cons _ _ _ head664
  apply bounded_cons _ _ _ head665
  apply bounded_cons _ _ _ head666
  apply bounded_cons _ _ _ head667
  apply bounded_cons _ _ _ head668
  apply bounded_cons _ _ _ head669
  apply bounded_cons _ _ _ head670
  apply bounded_cons _ _ _ head671
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded37
