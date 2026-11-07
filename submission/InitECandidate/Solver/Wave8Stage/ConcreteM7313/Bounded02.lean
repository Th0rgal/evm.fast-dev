import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk02
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded02
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open StackToLabClock LoweredBudget

wave8_kernel_reduce cost96 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard32.name, Function96.stackResult.1)).2
wave8_kernel_reduce cost97 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard33.name, Function97.stackResult.1)).2
wave8_kernel_reduce cost98 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard34.name, Function98.stackResult.1)).2
wave8_kernel_reduce cost99 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard35.name, Function99.stackResult.1)).2
wave8_kernel_reduce cost100 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard36.name, Function100.stackResult.1)).2
wave8_kernel_reduce cost101 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard37.name, Function101.stackResult.1)).2
wave8_kernel_reduce cost102 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard38.name, Function102.stackResult.1)).2
wave8_kernel_reduce cost103 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard39.name, Function103.stackResult.1)).2
wave8_kernel_reduce cost104 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard40.name, Function104.stackResult.1)).2
wave8_kernel_reduce cost105 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard41.name, Function105.stackResult.1)).2
wave8_kernel_reduce cost106 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard42.name, Function106.stackResult.1)).2
wave8_kernel_reduce cost107 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard43.name, Function107.stackResult.1)).2
wave8_kernel_reduce cost108 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard44.name, Function108.stackResult.1)).2
wave8_kernel_reduce cost109 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard45.name, Function109.stackResult.1)).2
wave8_kernel_reduce cost110 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard46.name, Function110.stackResult.1)).2
wave8_kernel_reduce cost111 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard47.name, Function111.stackResult.1)).2

theorem head96 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard32.name, Function96.stackResult.1)).2 ≤ 7313 := by
  rw [cost96_eq]
  decide

theorem head97 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard33.name, Function97.stackResult.1)).2 ≤ 7313 := by
  rw [cost97_eq]
  decide

theorem head98 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard34.name, Function98.stackResult.1)).2 ≤ 7313 := by
  rw [cost98_eq]
  decide

theorem head99 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard35.name, Function99.stackResult.1)).2 ≤ 7313 := by
  rw [cost99_eq]
  decide

theorem head100 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard36.name, Function100.stackResult.1)).2 ≤ 7313 := by
  rw [cost100_eq]
  decide

theorem head101 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard37.name, Function101.stackResult.1)).2 ≤ 7313 := by
  rw [cost101_eq]
  decide

theorem head102 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard38.name, Function102.stackResult.1)).2 ≤ 7313 := by
  rw [cost102_eq]
  decide

theorem head103 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard39.name, Function103.stackResult.1)).2 ≤ 7313 := by
  rw [cost103_eq]
  decide

theorem head104 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard40.name, Function104.stackResult.1)).2 ≤ 7313 := by
  rw [cost104_eq]
  decide

theorem head105 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard41.name, Function105.stackResult.1)).2 ≤ 7313 := by
  rw [cost105_eq]
  decide

theorem head106 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard42.name, Function106.stackResult.1)).2 ≤ 7313 := by
  rw [cost106_eq]
  decide

theorem head107 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard43.name, Function107.stackResult.1)).2 ≤ 7313 := by
  rw [cost107_eq]
  decide

theorem head108 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard44.name, Function108.stackResult.1)).2 ≤ 7313 := by
  rw [cost108_eq]
  decide

theorem head109 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard45.name, Function109.stackResult.1)).2 ≤ 7313 := by
  rw [cost109_eq]
  decide

theorem head110 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard46.name, Function110.stackResult.1)).2 ≤ 7313 := by
  rw [cost110_eq]
  decide

theorem head111 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard47.name, Function111.stackResult.1)).2 ≤ 7313 := by
  rw [cost111_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk02.bodies := by
  unfold Chunk02.bodies
  apply bounded_cons _ _ _ head96
  apply bounded_cons _ _ _ head97
  apply bounded_cons _ _ _ head98
  apply bounded_cons _ _ _ head99
  apply bounded_cons _ _ _ head100
  apply bounded_cons _ _ _ head101
  apply bounded_cons _ _ _ head102
  apply bounded_cons _ _ _ head103
  apply bounded_cons _ _ _ head104
  apply bounded_cons _ _ _ head105
  apply bounded_cons _ _ _ head106
  apply bounded_cons _ _ _ head107
  apply bounded_cons _ _ _ head108
  apply bounded_cons _ _ _ head109
  apply bounded_cons _ _ _ head110
  apply bounded_cons _ _ _ head111
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded02
