import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk09
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded09
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open StackToLabClock LoweredBudget

wave8_kernel_reduce cost208 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard144.name, Chunk09.stackResult208.1)).2
wave8_kernel_reduce cost209 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard145.name, Chunk09.stackResult209.1)).2
wave8_kernel_reduce cost210 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard146.name, Chunk09.stackResult210.1)).2
wave8_kernel_reduce cost211 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard147.name, Chunk09.stackResult211.1)).2
wave8_kernel_reduce cost212 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard148.name, Chunk09.stackResult212.1)).2
wave8_kernel_reduce cost213 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard149.name, Chunk09.stackResult213.1)).2
wave8_kernel_reduce cost214 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard150.name, Chunk09.stackResult214.1)).2
wave8_kernel_reduce cost215 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard151.name, Chunk09.stackResult215.1)).2
wave8_kernel_reduce cost216 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard152.name, Chunk09.stackResult216.1)).2
wave8_kernel_reduce cost217 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard153.name, Chunk09.stackResult217.1)).2
wave8_kernel_reduce cost218 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard154.name, Chunk09.stackResult218.1)).2
wave8_kernel_reduce cost219 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard155.name, Chunk09.stackResult219.1)).2
wave8_kernel_reduce cost220 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard156.name, Chunk09.stackResult220.1)).2
wave8_kernel_reduce cost221 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard157.name, Chunk09.stackResult221.1)).2
wave8_kernel_reduce cost222 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard158.name, Chunk09.stackResult222.1)).2
wave8_kernel_reduce cost223 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard159.name, Chunk09.stackResult223.1)).2

theorem head208 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard144.name, Chunk09.stackResult208.1)).2 ≤ 7313 := by
  rw [cost208_eq]
  decide

theorem head209 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard145.name, Chunk09.stackResult209.1)).2 ≤ 7313 := by
  rw [cost209_eq]
  decide

theorem head210 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard146.name, Chunk09.stackResult210.1)).2 ≤ 7313 := by
  rw [cost210_eq]
  decide

theorem head211 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard147.name, Chunk09.stackResult211.1)).2 ≤ 7313 := by
  rw [cost211_eq]
  decide

theorem head212 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard148.name, Chunk09.stackResult212.1)).2 ≤ 7313 := by
  rw [cost212_eq]
  decide

theorem head213 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard149.name, Chunk09.stackResult213.1)).2 ≤ 7313 := by
  rw [cost213_eq]
  decide

theorem head214 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard150.name, Chunk09.stackResult214.1)).2 ≤ 7313 := by
  rw [cost214_eq]
  decide

theorem head215 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard151.name, Chunk09.stackResult215.1)).2 ≤ 7313 := by
  rw [cost215_eq]
  decide

theorem head216 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard152.name, Chunk09.stackResult216.1)).2 ≤ 7313 := by
  rw [cost216_eq]
  decide

theorem head217 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard153.name, Chunk09.stackResult217.1)).2 ≤ 7313 := by
  rw [cost217_eq]
  decide

theorem head218 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard154.name, Chunk09.stackResult218.1)).2 ≤ 7313 := by
  rw [cost218_eq]
  decide

theorem head219 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard155.name, Chunk09.stackResult219.1)).2 ≤ 7313 := by
  rw [cost219_eq]
  decide

theorem head220 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard156.name, Chunk09.stackResult220.1)).2 ≤ 7313 := by
  rw [cost220_eq]
  decide

theorem head221 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard157.name, Chunk09.stackResult221.1)).2 ≤ 7313 := by
  rw [cost221_eq]
  decide

theorem head222 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard158.name, Chunk09.stackResult222.1)).2 ≤ 7313 := by
  rw [cost222_eq]
  decide

theorem head223 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard159.name, Chunk09.stackResult223.1)).2 ≤ 7313 := by
  rw [cost223_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk09.bodies := by
  unfold Chunk09.bodies
  apply bounded_cons _ _ _ head208
  apply bounded_cons _ _ _ head209
  apply bounded_cons _ _ _ head210
  apply bounded_cons _ _ _ head211
  apply bounded_cons _ _ _ head212
  apply bounded_cons _ _ _ head213
  apply bounded_cons _ _ _ head214
  apply bounded_cons _ _ _ head215
  apply bounded_cons _ _ _ head216
  apply bounded_cons _ _ _ head217
  apply bounded_cons _ _ _ head218
  apply bounded_cons _ _ _ head219
  apply bounded_cons _ _ _ head220
  apply bounded_cons _ _ _ head221
  apply bounded_cons _ _ _ head222
  apply bounded_cons _ _ _ head223
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded09
