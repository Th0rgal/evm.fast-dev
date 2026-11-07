import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded05
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open StackToLabClock LoweredBudget

wave8_kernel_reduce cost144 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard80.name, Chunk05.stackResult144.1)).2
wave8_kernel_reduce cost145 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard81.name, Chunk05.stackResult145.1)).2
wave8_kernel_reduce cost146 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard82.name, Chunk05.stackResult146.1)).2
wave8_kernel_reduce cost147 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard83.name, Chunk05.stackResult147.1)).2
wave8_kernel_reduce cost148 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard84.name, Chunk05.stackResult148.1)).2
wave8_kernel_reduce cost149 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard85.name, Chunk05.stackResult149.1)).2
wave8_kernel_reduce cost150 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard86.name, Chunk05.stackResult150.1)).2
wave8_kernel_reduce cost151 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard87.name, Chunk05.stackResult151.1)).2
wave8_kernel_reduce cost152 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard88.name, Chunk05.stackResult152.1)).2
wave8_kernel_reduce cost153 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard89.name, Chunk05.stackResult153.1)).2
wave8_kernel_reduce cost154 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard90.name, Chunk05.stackResult154.1)).2
wave8_kernel_reduce cost155 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard91.name, Chunk05.stackResult155.1)).2
wave8_kernel_reduce cost156 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard92.name, Chunk05.stackResult156.1)).2
wave8_kernel_reduce cost157 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard93.name, Chunk05.stackResult157.1)).2
wave8_kernel_reduce cost158 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard94.name, Chunk05.stackResult158.1)).2
wave8_kernel_reduce cost159 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard95.name, Chunk05.stackResult159.1)).2

theorem head144 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard80.name, Chunk05.stackResult144.1)).2 ≤ 7313 := by
  rw [cost144_eq]
  decide

theorem head145 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard81.name, Chunk05.stackResult145.1)).2 ≤ 7313 := by
  rw [cost145_eq]
  decide

theorem head146 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard82.name, Chunk05.stackResult146.1)).2 ≤ 7313 := by
  rw [cost146_eq]
  decide

theorem head147 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard83.name, Chunk05.stackResult147.1)).2 ≤ 7313 := by
  rw [cost147_eq]
  decide

theorem head148 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard84.name, Chunk05.stackResult148.1)).2 ≤ 7313 := by
  rw [cost148_eq]
  decide

theorem head149 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard85.name, Chunk05.stackResult149.1)).2 ≤ 7313 := by
  rw [cost149_eq]
  decide

theorem head150 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard86.name, Chunk05.stackResult150.1)).2 ≤ 7313 := by
  rw [cost150_eq]
  decide

theorem head151 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard87.name, Chunk05.stackResult151.1)).2 ≤ 7313 := by
  rw [cost151_eq]
  decide

theorem head152 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard88.name, Chunk05.stackResult152.1)).2 ≤ 7313 := by
  rw [cost152_eq]
  decide

theorem head153 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard89.name, Chunk05.stackResult153.1)).2 ≤ 7313 := by
  rw [cost153_eq]
  decide

theorem head154 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard90.name, Chunk05.stackResult154.1)).2 ≤ 7313 := by
  rw [cost154_eq]
  decide

theorem head155 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard91.name, Chunk05.stackResult155.1)).2 ≤ 7313 := by
  rw [cost155_eq]
  decide

theorem head156 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard92.name, Chunk05.stackResult156.1)).2 ≤ 7313 := by
  rw [cost156_eq]
  decide

theorem head157 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard93.name, Chunk05.stackResult157.1)).2 ≤ 7313 := by
  rw [cost157_eq]
  decide

theorem head158 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard94.name, Chunk05.stackResult158.1)).2 ≤ 7313 := by
  rw [cost158_eq]
  decide

theorem head159 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard95.name, Chunk05.stackResult159.1)).2 ≤ 7313 := by
  rw [cost159_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk05.bodies := by
  unfold Chunk05.bodies
  apply bounded_cons _ _ _ head144
  apply bounded_cons _ _ _ head145
  apply bounded_cons _ _ _ head146
  apply bounded_cons _ _ _ head147
  apply bounded_cons _ _ _ head148
  apply bounded_cons _ _ _ head149
  apply bounded_cons _ _ _ head150
  apply bounded_cons _ _ _ head151
  apply bounded_cons _ _ _ head152
  apply bounded_cons _ _ _ head153
  apply bounded_cons _ _ _ head154
  apply bounded_cons _ _ _ head155
  apply bounded_cons _ _ _ head156
  apply bounded_cons _ _ _ head157
  apply bounded_cons _ _ _ head158
  apply bounded_cons _ _ _ head159
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded05
