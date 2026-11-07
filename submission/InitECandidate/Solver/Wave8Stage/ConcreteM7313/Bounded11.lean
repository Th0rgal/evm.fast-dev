import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk11
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded11
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open StackToLabClock LoweredBudget

wave8_kernel_reduce cost240 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard176.name, Chunk11.stackResult240.1)).2
wave8_kernel_reduce cost241 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard177.name, Chunk11.stackResult241.1)).2
wave8_kernel_reduce cost242 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard178.name, Chunk11.stackResult242.1)).2
wave8_kernel_reduce cost243 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard179.name, Chunk11.stackResult243.1)).2
wave8_kernel_reduce cost244 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard180.name, Chunk11.stackResult244.1)).2
wave8_kernel_reduce cost245 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard181.name, Chunk11.stackResult245.1)).2
wave8_kernel_reduce cost246 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard182.name, Chunk11.stackResult246.1)).2
wave8_kernel_reduce cost247 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard183.name, Chunk11.stackResult247.1)).2
wave8_kernel_reduce cost248 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard184.name, Chunk11.stackResult248.1)).2
wave8_kernel_reduce cost249 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard185.name, Chunk11.stackResult249.1)).2
wave8_kernel_reduce cost250 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard186.name, Chunk11.stackResult250.1)).2
wave8_kernel_reduce cost251 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard187.name, Chunk11.stackResult251.1)).2
wave8_kernel_reduce cost252 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard188.name, Chunk11.stackResult252.1)).2
wave8_kernel_reduce cost253 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard189.name, Chunk11.stackResult253.1)).2
wave8_kernel_reduce cost254 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard190.name, Chunk11.stackResult254.1)).2
wave8_kernel_reduce cost255 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard191.name, Chunk11.stackResult255.1)).2

theorem head240 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard176.name, Chunk11.stackResult240.1)).2 ≤ 7313 := by
  rw [cost240_eq]
  decide

theorem head241 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard177.name, Chunk11.stackResult241.1)).2 ≤ 7313 := by
  rw [cost241_eq]
  decide

theorem head242 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard178.name, Chunk11.stackResult242.1)).2 ≤ 7313 := by
  rw [cost242_eq]
  decide

theorem head243 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard179.name, Chunk11.stackResult243.1)).2 ≤ 7313 := by
  rw [cost243_eq]
  decide

theorem head244 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard180.name, Chunk11.stackResult244.1)).2 ≤ 7313 := by
  rw [cost244_eq]
  decide

theorem head245 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard181.name, Chunk11.stackResult245.1)).2 ≤ 7313 := by
  rw [cost245_eq]
  decide

theorem head246 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard182.name, Chunk11.stackResult246.1)).2 ≤ 7313 := by
  rw [cost246_eq]
  decide

theorem head247 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard183.name, Chunk11.stackResult247.1)).2 ≤ 7313 := by
  rw [cost247_eq]
  decide

theorem head248 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard184.name, Chunk11.stackResult248.1)).2 ≤ 7313 := by
  rw [cost248_eq]
  decide

theorem head249 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard185.name, Chunk11.stackResult249.1)).2 ≤ 7313 := by
  rw [cost249_eq]
  decide

theorem head250 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard186.name, Chunk11.stackResult250.1)).2 ≤ 7313 := by
  rw [cost250_eq]
  decide

theorem head251 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard187.name, Chunk11.stackResult251.1)).2 ≤ 7313 := by
  rw [cost251_eq]
  decide

theorem head252 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard188.name, Chunk11.stackResult252.1)).2 ≤ 7313 := by
  rw [cost252_eq]
  decide

theorem head253 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard189.name, Chunk11.stackResult253.1)).2 ≤ 7313 := by
  rw [cost253_eq]
  decide

theorem head254 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard190.name, Chunk11.stackResult254.1)).2 ≤ 7313 := by
  rw [cost254_eq]
  decide

theorem head255 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard191.name, Chunk11.stackResult255.1)).2 ≤ 7313 := by
  rw [cost255_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk11.bodies := by
  unfold Chunk11.bodies
  apply bounded_cons _ _ _ head240
  apply bounded_cons _ _ _ head241
  apply bounded_cons _ _ _ head242
  apply bounded_cons _ _ _ head243
  apply bounded_cons _ _ _ head244
  apply bounded_cons _ _ _ head245
  apply bounded_cons _ _ _ head246
  apply bounded_cons _ _ _ head247
  apply bounded_cons _ _ _ head248
  apply bounded_cons _ _ _ head249
  apply bounded_cons _ _ _ head250
  apply bounded_cons _ _ _ head251
  apply bounded_cons _ _ _ head252
  apply bounded_cons _ _ _ head253
  apply bounded_cons _ _ _ head254
  apply bounded_cons _ _ _ head255
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded11
