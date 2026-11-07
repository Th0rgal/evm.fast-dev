import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk03
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded03
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open StackToLabClock LoweredBudget

wave8_kernel_reduce cost112 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard48.name, Function112.stackResult.1)).2
wave8_kernel_reduce cost113 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard49.name, Function113.stackResult.1)).2
wave8_kernel_reduce cost114 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard50.name, Function114.stackResult.1)).2
wave8_kernel_reduce cost115 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard51.name, Function115.stackResult.1)).2
wave8_kernel_reduce cost116 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard52.name, Function116.stackResult.1)).2
wave8_kernel_reduce cost117 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard53.name, Function117.stackResult.1)).2
wave8_kernel_reduce cost118 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard54.name, Function118.stackResult.1)).2
wave8_kernel_reduce cost119 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard55.name, Function119.stackResult.1)).2
wave8_kernel_reduce cost120 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard56.name, Function120.stackResult.1)).2
wave8_kernel_reduce cost121 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard57.name, Function121.stackResult.1)).2
wave8_kernel_reduce cost122 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard58.name, Function122.stackResult.1)).2
wave8_kernel_reduce cost123 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard59.name, Function123.stackResult.1)).2
wave8_kernel_reduce cost124 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard60.name, Function124.stackResult.1)).2
wave8_kernel_reduce cost125 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard61.name, Function125.stackResult.1)).2
wave8_kernel_reduce cost126 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard62.name, Function126.stackResult.1)).2
wave8_kernel_reduce cost127 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard63.name, Function127.stackResult.1)).2

theorem head112 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard48.name, Function112.stackResult.1)).2 ≤ 7313 := by
  rw [cost112_eq]
  decide

theorem head113 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard49.name, Function113.stackResult.1)).2 ≤ 7313 := by
  rw [cost113_eq]
  decide

theorem head114 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard50.name, Function114.stackResult.1)).2 ≤ 7313 := by
  rw [cost114_eq]
  decide

theorem head115 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard51.name, Function115.stackResult.1)).2 ≤ 7313 := by
  rw [cost115_eq]
  decide

theorem head116 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard52.name, Function116.stackResult.1)).2 ≤ 7313 := by
  rw [cost116_eq]
  decide

theorem head117 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard53.name, Function117.stackResult.1)).2 ≤ 7313 := by
  rw [cost117_eq]
  decide

theorem head118 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard54.name, Function118.stackResult.1)).2 ≤ 7313 := by
  rw [cost118_eq]
  decide

theorem head119 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard55.name, Function119.stackResult.1)).2 ≤ 7313 := by
  rw [cost119_eq]
  decide

theorem head120 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard56.name, Function120.stackResult.1)).2 ≤ 7313 := by
  rw [cost120_eq]
  decide

theorem head121 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard57.name, Function121.stackResult.1)).2 ≤ 7313 := by
  rw [cost121_eq]
  decide

theorem head122 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard58.name, Function122.stackResult.1)).2 ≤ 7313 := by
  rw [cost122_eq]
  decide

theorem head123 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard59.name, Function123.stackResult.1)).2 ≤ 7313 := by
  rw [cost123_eq]
  decide

theorem head124 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard60.name, Function124.stackResult.1)).2 ≤ 7313 := by
  rw [cost124_eq]
  decide

theorem head125 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard61.name, Function125.stackResult.1)).2 ≤ 7313 := by
  rw [cost125_eq]
  decide

theorem head126 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard62.name, Function126.stackResult.1)).2 ≤ 7313 := by
  rw [cost126_eq]
  decide

theorem head127 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard63.name, Function127.stackResult.1)).2 ≤ 7313 := by
  rw [cost127_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk03.bodies := by
  unfold Chunk03.bodies
  apply bounded_cons _ _ _ head112
  apply bounded_cons _ _ _ head113
  apply bounded_cons _ _ _ head114
  apply bounded_cons _ _ _ head115
  apply bounded_cons _ _ _ head116
  apply bounded_cons _ _ _ head117
  apply bounded_cons _ _ _ head118
  apply bounded_cons _ _ _ head119
  apply bounded_cons _ _ _ head120
  apply bounded_cons _ _ _ head121
  apply bounded_cons _ _ _ head122
  apply bounded_cons _ _ _ head123
  apply bounded_cons _ _ _ head124
  apply bounded_cons _ _ _ head125
  apply bounded_cons _ _ _ head126
  apply bounded_cons _ _ _ head127
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded03
