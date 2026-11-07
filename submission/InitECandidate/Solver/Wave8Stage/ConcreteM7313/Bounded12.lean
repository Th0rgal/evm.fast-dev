import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk12
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded12
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open StackToLabClock LoweredBudget

wave8_kernel_reduce cost256 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard192.name, Chunk12.stackResult256.1)).2
wave8_kernel_reduce cost257 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard193.name, Chunk12.stackResult257.1)).2
wave8_kernel_reduce cost258 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard194.name, Chunk12.stackResult258.1)).2
wave8_kernel_reduce cost259 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard195.name, Chunk12.stackResult259.1)).2
wave8_kernel_reduce cost260 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard196.name, Chunk12.stackResult260.1)).2
wave8_kernel_reduce cost261 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard197.name, Chunk12.stackResult261.1)).2
wave8_kernel_reduce cost262 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard198.name, Chunk12.stackResult262.1)).2
wave8_kernel_reduce cost263 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard199.name, Chunk12.stackResult263.1)).2
wave8_kernel_reduce cost264 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard200.name, Chunk12.stackResult264.1)).2
wave8_kernel_reduce cost265 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard201.name, Chunk12.stackResult265.1)).2
wave8_kernel_reduce cost266 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard202.name, Chunk12.stackResult266.1)).2
wave8_kernel_reduce cost267 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard203.name, Chunk12.stackResult267.1)).2
wave8_kernel_reduce cost268 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard204.name, Chunk12.stackResult268.1)).2
wave8_kernel_reduce cost269 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard205.name, Chunk12.stackResult269.1)).2
wave8_kernel_reduce cost270 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard206.name, Chunk12.stackResult270.1)).2
wave8_kernel_reduce cost271 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard207.name, Chunk12.stackResult271.1)).2

theorem head256 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard192.name, Chunk12.stackResult256.1)).2 ≤ 7313 := by
  rw [cost256_eq]
  decide

theorem head257 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard193.name, Chunk12.stackResult257.1)).2 ≤ 7313 := by
  rw [cost257_eq]
  decide

theorem head258 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard194.name, Chunk12.stackResult258.1)).2 ≤ 7313 := by
  rw [cost258_eq]
  decide

theorem head259 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard195.name, Chunk12.stackResult259.1)).2 ≤ 7313 := by
  rw [cost259_eq]
  decide

theorem head260 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard196.name, Chunk12.stackResult260.1)).2 ≤ 7313 := by
  rw [cost260_eq]
  decide

theorem head261 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard197.name, Chunk12.stackResult261.1)).2 ≤ 7313 := by
  rw [cost261_eq]
  decide

theorem head262 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard198.name, Chunk12.stackResult262.1)).2 ≤ 7313 := by
  rw [cost262_eq]
  decide

theorem head263 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard199.name, Chunk12.stackResult263.1)).2 ≤ 7313 := by
  rw [cost263_eq]
  decide

theorem head264 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard200.name, Chunk12.stackResult264.1)).2 ≤ 7313 := by
  rw [cost264_eq]
  decide

theorem head265 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard201.name, Chunk12.stackResult265.1)).2 ≤ 7313 := by
  rw [cost265_eq]
  decide

theorem head266 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard202.name, Chunk12.stackResult266.1)).2 ≤ 7313 := by
  rw [cost266_eq]
  decide

theorem head267 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard203.name, Chunk12.stackResult267.1)).2 ≤ 7313 := by
  rw [cost267_eq]
  decide

theorem head268 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard204.name, Chunk12.stackResult268.1)).2 ≤ 7313 := by
  rw [cost268_eq]
  decide

theorem head269 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard205.name, Chunk12.stackResult269.1)).2 ≤ 7313 := by
  rw [cost269_eq]
  decide

theorem head270 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard206.name, Chunk12.stackResult270.1)).2 ≤ 7313 := by
  rw [cost270_eq]
  decide

theorem head271 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard207.name, Chunk12.stackResult271.1)).2 ≤ 7313 := by
  rw [cost271_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk12.bodies := by
  unfold Chunk12.bodies
  apply bounded_cons _ _ _ head256
  apply bounded_cons _ _ _ head257
  apply bounded_cons _ _ _ head258
  apply bounded_cons _ _ _ head259
  apply bounded_cons _ _ _ head260
  apply bounded_cons _ _ _ head261
  apply bounded_cons _ _ _ head262
  apply bounded_cons _ _ _ head263
  apply bounded_cons _ _ _ head264
  apply bounded_cons _ _ _ head265
  apply bounded_cons _ _ _ head266
  apply bounded_cons _ _ _ head267
  apply bounded_cons _ _ _ head268
  apply bounded_cons _ _ _ head269
  apply bounded_cons _ _ _ head270
  apply bounded_cons _ _ _ head271
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded12
