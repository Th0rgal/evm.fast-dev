import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk04
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded04
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open StackToLabClock LoweredBudget

wave8_kernel_reduce cost128 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard64.name, Function128.stackResult.1)).2
wave8_kernel_reduce cost129 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard65.name, Function129.stackResult.1)).2
wave8_kernel_reduce cost130 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard66.name, Function130.stackResult.1)).2
wave8_kernel_reduce cost131 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard67.name, Function131.stackResult.1)).2
wave8_kernel_reduce cost132 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard68.name, Function132.stackResult.1)).2
wave8_kernel_reduce cost133 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard69.name, Function133.stackResult.1)).2
wave8_kernel_reduce cost134 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard70.name, Function134.stackResult.1)).2
wave8_kernel_reduce cost135 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard71.name, Function135.stackResult.1)).2
wave8_kernel_reduce cost136 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard72.name, Function136.stackResult.1)).2
wave8_kernel_reduce cost137 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard73.name, Function137.stackResult.1)).2
wave8_kernel_reduce cost138 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard74.name, Function138.stackResult.1)).2
wave8_kernel_reduce cost139 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard75.name, Function139.stackResult.1)).2
wave8_kernel_reduce cost140 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard76.name, Function140.stackResult.1)).2
wave8_kernel_reduce cost141 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard77.name, Function141.stackResult.1)).2
wave8_kernel_reduce cost142 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard78.name, Function142.stackResult.1)).2
wave8_kernel_reduce cost143 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard79.name, Function143.stackResult.1)).2

theorem head128 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard64.name, Function128.stackResult.1)).2 ≤ 7313 := by
  rw [cost128_eq]
  decide

theorem head129 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard65.name, Function129.stackResult.1)).2 ≤ 7313 := by
  rw [cost129_eq]
  decide

theorem head130 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard66.name, Function130.stackResult.1)).2 ≤ 7313 := by
  rw [cost130_eq]
  decide

theorem head131 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard67.name, Function131.stackResult.1)).2 ≤ 7313 := by
  rw [cost131_eq]
  decide

theorem head132 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard68.name, Function132.stackResult.1)).2 ≤ 7313 := by
  rw [cost132_eq]
  decide

theorem head133 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard69.name, Function133.stackResult.1)).2 ≤ 7313 := by
  rw [cost133_eq]
  decide

theorem head134 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard70.name, Function134.stackResult.1)).2 ≤ 7313 := by
  rw [cost134_eq]
  decide

theorem head135 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard71.name, Function135.stackResult.1)).2 ≤ 7313 := by
  rw [cost135_eq]
  decide

theorem head136 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard72.name, Function136.stackResult.1)).2 ≤ 7313 := by
  rw [cost136_eq]
  decide

theorem head137 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard73.name, Function137.stackResult.1)).2 ≤ 7313 := by
  rw [cost137_eq]
  decide

theorem head138 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard74.name, Function138.stackResult.1)).2 ≤ 7313 := by
  rw [cost138_eq]
  decide

theorem head139 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard75.name, Function139.stackResult.1)).2 ≤ 7313 := by
  rw [cost139_eq]
  decide

theorem head140 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard76.name, Function140.stackResult.1)).2 ≤ 7313 := by
  rw [cost140_eq]
  decide

theorem head141 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard77.name, Function141.stackResult.1)).2 ≤ 7313 := by
  rw [cost141_eq]
  decide

theorem head142 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard78.name, Function142.stackResult.1)).2 ≤ 7313 := by
  rw [cost142_eq]
  decide

theorem head143 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard79.name, Function143.stackResult.1)).2 ≤ 7313 := by
  rw [cost143_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk04.bodies := by
  unfold Chunk04.bodies
  apply bounded_cons _ _ _ head128
  apply bounded_cons _ _ _ head129
  apply bounded_cons _ _ _ head130
  apply bounded_cons _ _ _ head131
  apply bounded_cons _ _ _ head132
  apply bounded_cons _ _ _ head133
  apply bounded_cons _ _ _ head134
  apply bounded_cons _ _ _ head135
  apply bounded_cons _ _ _ head136
  apply bounded_cons _ _ _ head137
  apply bounded_cons _ _ _ head138
  apply bounded_cons _ _ _ head139
  apply bounded_cons _ _ _ head140
  apply bounded_cons _ _ _ head141
  apply bounded_cons _ _ _ head142
  apply bounded_cons _ _ _ head143
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded04
