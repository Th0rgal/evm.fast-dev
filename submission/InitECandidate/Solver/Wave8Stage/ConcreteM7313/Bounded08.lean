import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk08
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded08
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open StackToLabClock LoweredBudget

wave8_kernel_reduce cost192 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard128.name, Chunk08.stackResult192.1)).2
wave8_kernel_reduce cost193 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard129.name, Chunk08.stackResult193.1)).2
wave8_kernel_reduce cost194 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard130.name, Chunk08.stackResult194.1)).2
wave8_kernel_reduce cost195 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard131.name, Chunk08.stackResult195.1)).2
wave8_kernel_reduce cost196 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard132.name, Chunk08.stackResult196.1)).2
wave8_kernel_reduce cost197 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard133.name, Chunk08.stackResult197.1)).2
wave8_kernel_reduce cost198 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard134.name, Chunk08.stackResult198.1)).2
wave8_kernel_reduce cost199 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard135.name, Chunk08.stackResult199.1)).2
wave8_kernel_reduce cost200 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard136.name, Chunk08.stackResult200.1)).2
wave8_kernel_reduce cost201 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard137.name, Chunk08.stackResult201.1)).2
wave8_kernel_reduce cost202 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard138.name, Chunk08.stackResult202.1)).2
wave8_kernel_reduce cost203 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard139.name, Chunk08.stackResult203.1)).2
wave8_kernel_reduce cost204 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard140.name, Chunk08.stackResult204.1)).2
wave8_kernel_reduce cost205 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard141.name, Chunk08.stackResult205.1)).2
wave8_kernel_reduce cost206 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard142.name, Chunk08.stackResult206.1)).2
wave8_kernel_reduce cost207 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard143.name, Chunk08.stackResult207.1)).2

theorem head192 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard128.name, Chunk08.stackResult192.1)).2 ≤ 7313 := by
  rw [cost192_eq]
  decide

theorem head193 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard129.name, Chunk08.stackResult193.1)).2 ≤ 7313 := by
  rw [cost193_eq]
  decide

theorem head194 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard130.name, Chunk08.stackResult194.1)).2 ≤ 7313 := by
  rw [cost194_eq]
  decide

theorem head195 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard131.name, Chunk08.stackResult195.1)).2 ≤ 7313 := by
  rw [cost195_eq]
  decide

theorem head196 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard132.name, Chunk08.stackResult196.1)).2 ≤ 7313 := by
  rw [cost196_eq]
  decide

theorem head197 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard133.name, Chunk08.stackResult197.1)).2 ≤ 7313 := by
  rw [cost197_eq]
  decide

theorem head198 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard134.name, Chunk08.stackResult198.1)).2 ≤ 7313 := by
  rw [cost198_eq]
  decide

theorem head199 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard135.name, Chunk08.stackResult199.1)).2 ≤ 7313 := by
  rw [cost199_eq]
  decide

theorem head200 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard136.name, Chunk08.stackResult200.1)).2 ≤ 7313 := by
  rw [cost200_eq]
  decide

theorem head201 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard137.name, Chunk08.stackResult201.1)).2 ≤ 7313 := by
  rw [cost201_eq]
  decide

theorem head202 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard138.name, Chunk08.stackResult202.1)).2 ≤ 7313 := by
  rw [cost202_eq]
  decide

theorem head203 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard139.name, Chunk08.stackResult203.1)).2 ≤ 7313 := by
  rw [cost203_eq]
  decide

theorem head204 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard140.name, Chunk08.stackResult204.1)).2 ≤ 7313 := by
  rw [cost204_eq]
  decide

theorem head205 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard141.name, Chunk08.stackResult205.1)).2 ≤ 7313 := by
  rw [cost205_eq]
  decide

theorem head206 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard142.name, Chunk08.stackResult206.1)).2 ≤ 7313 := by
  rw [cost206_eq]
  decide

theorem head207 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard143.name, Chunk08.stackResult207.1)).2 ≤ 7313 := by
  rw [cost207_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk08.bodies := by
  unfold Chunk08.bodies
  apply bounded_cons _ _ _ head192
  apply bounded_cons _ _ _ head193
  apply bounded_cons _ _ _ head194
  apply bounded_cons _ _ _ head195
  apply bounded_cons _ _ _ head196
  apply bounded_cons _ _ _ head197
  apply bounded_cons _ _ _ head198
  apply bounded_cons _ _ _ head199
  apply bounded_cons _ _ _ head200
  apply bounded_cons _ _ _ head201
  apply bounded_cons _ _ _ head202
  apply bounded_cons _ _ _ head203
  apply bounded_cons _ _ _ head204
  apply bounded_cons _ _ _ head205
  apply bounded_cons _ _ _ head206
  apply bounded_cons _ _ _ head207
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded08
