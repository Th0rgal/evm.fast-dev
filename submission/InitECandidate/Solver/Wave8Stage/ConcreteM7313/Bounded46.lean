import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk46
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded46
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open StackToLabClock LoweredBudget

wave8_kernel_reduce cost800 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard736.name, Chunk46.stackResult800.1)).2
wave8_kernel_reduce cost801 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard737.name, Chunk46.stackResult801.1)).2
wave8_kernel_reduce cost802 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard738.name, Chunk46.stackResult802.1)).2
wave8_kernel_reduce cost803 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard739.name, Chunk46.stackResult803.1)).2
wave8_kernel_reduce cost804 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard740.name, Chunk46.stackResult804.1)).2
wave8_kernel_reduce cost805 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard741.name, Chunk46.stackResult805.1)).2
wave8_kernel_reduce cost806 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard742.name, Chunk46.stackResult806.1)).2
wave8_kernel_reduce cost807 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard743.name, Chunk46.stackResult807.1)).2
wave8_kernel_reduce cost808 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard744.name, Chunk46.stackResult808.1)).2
wave8_kernel_reduce cost809 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard745.name, Chunk46.stackResult809.1)).2
wave8_kernel_reduce cost810 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard746.name, Chunk46.stackResult810.1)).2
wave8_kernel_reduce cost811 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard747.name, Chunk46.stackResult811.1)).2
wave8_kernel_reduce cost812 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard748.name, Chunk46.stackResult812.1)).2
wave8_kernel_reduce cost813 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard749.name, Chunk46.stackResult813.1)).2
wave8_kernel_reduce cost814 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard750.name, Chunk46.stackResult814.1)).2
wave8_kernel_reduce cost815 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard751.name, Chunk46.stackResult815.1)).2

theorem head800 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard736.name, Chunk46.stackResult800.1)).2 ≤ 7313 := by
  rw [cost800_eq]
  decide

theorem head801 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard737.name, Chunk46.stackResult801.1)).2 ≤ 7313 := by
  rw [cost801_eq]
  decide

theorem head802 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard738.name, Chunk46.stackResult802.1)).2 ≤ 7313 := by
  rw [cost802_eq]
  decide

theorem head803 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard739.name, Chunk46.stackResult803.1)).2 ≤ 7313 := by
  rw [cost803_eq]
  decide

theorem head804 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard740.name, Chunk46.stackResult804.1)).2 ≤ 7313 := by
  rw [cost804_eq]
  decide

theorem head805 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard741.name, Chunk46.stackResult805.1)).2 ≤ 7313 := by
  rw [cost805_eq]
  decide

theorem head806 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard742.name, Chunk46.stackResult806.1)).2 ≤ 7313 := by
  rw [cost806_eq]
  decide

theorem head807 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard743.name, Chunk46.stackResult807.1)).2 ≤ 7313 := by
  rw [cost807_eq]
  decide

theorem head808 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard744.name, Chunk46.stackResult808.1)).2 ≤ 7313 := by
  rw [cost808_eq]
  decide

theorem head809 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard745.name, Chunk46.stackResult809.1)).2 ≤ 7313 := by
  rw [cost809_eq]
  decide

theorem head810 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard746.name, Chunk46.stackResult810.1)).2 ≤ 7313 := by
  rw [cost810_eq]
  decide

theorem head811 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard747.name, Chunk46.stackResult811.1)).2 ≤ 7313 := by
  rw [cost811_eq]
  decide

theorem head812 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard748.name, Chunk46.stackResult812.1)).2 ≤ 7313 := by
  rw [cost812_eq]
  decide

theorem head813 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard749.name, Chunk46.stackResult813.1)).2 ≤ 7313 := by
  rw [cost813_eq]
  decide

theorem head814 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard750.name, Chunk46.stackResult814.1)).2 ≤ 7313 := by
  rw [cost814_eq]
  decide

theorem head815 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard751.name, Chunk46.stackResult815.1)).2 ≤ 7313 := by
  rw [cost815_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk46.bodies := by
  unfold Chunk46.bodies
  apply bounded_cons _ _ _ head800
  apply bounded_cons _ _ _ head801
  apply bounded_cons _ _ _ head802
  apply bounded_cons _ _ _ head803
  apply bounded_cons _ _ _ head804
  apply bounded_cons _ _ _ head805
  apply bounded_cons _ _ _ head806
  apply bounded_cons _ _ _ head807
  apply bounded_cons _ _ _ head808
  apply bounded_cons _ _ _ head809
  apply bounded_cons _ _ _ head810
  apply bounded_cons _ _ _ head811
  apply bounded_cons _ _ _ head812
  apply bounded_cons _ _ _ head813
  apply bounded_cons _ _ _ head814
  apply bounded_cons _ _ _ head815
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded46
