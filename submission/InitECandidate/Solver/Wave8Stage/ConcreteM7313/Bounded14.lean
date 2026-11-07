import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk14
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded14
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open StackToLabClock LoweredBudget

wave8_kernel_reduce cost288 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard224.name, Chunk14.stackResult288.1)).2
wave8_kernel_reduce cost289 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard225.name, Chunk14.stackResult289.1)).2
wave8_kernel_reduce cost290 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard226.name, Chunk14.stackResult290.1)).2
wave8_kernel_reduce cost291 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard227.name, Chunk14.stackResult291.1)).2
wave8_kernel_reduce cost292 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard228.name, Chunk14.stackResult292.1)).2
wave8_kernel_reduce cost293 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard229.name, Chunk14.stackResult293.1)).2
wave8_kernel_reduce cost294 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard230.name, Chunk14.stackResult294.1)).2
wave8_kernel_reduce cost295 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard231.name, Chunk14.stackResult295.1)).2
wave8_kernel_reduce cost296 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard232.name, Chunk14.stackResult296.1)).2
wave8_kernel_reduce cost297 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard233.name, Chunk14.stackResult297.1)).2
wave8_kernel_reduce cost298 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard234.name, Chunk14.stackResult298.1)).2
wave8_kernel_reduce cost299 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard235.name, Chunk14.stackResult299.1)).2
wave8_kernel_reduce cost300 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard236.name, Chunk14.stackResult300.1)).2
wave8_kernel_reduce cost301 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard237.name, Chunk14.stackResult301.1)).2
wave8_kernel_reduce cost302 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard238.name, Chunk14.stackResult302.1)).2
wave8_kernel_reduce cost303 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard239.name, Chunk14.stackResult303.1)).2

theorem head288 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard224.name, Chunk14.stackResult288.1)).2 ≤ 7313 := by
  rw [cost288_eq]
  decide

theorem head289 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard225.name, Chunk14.stackResult289.1)).2 ≤ 7313 := by
  rw [cost289_eq]
  decide

theorem head290 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard226.name, Chunk14.stackResult290.1)).2 ≤ 7313 := by
  rw [cost290_eq]
  decide

theorem head291 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard227.name, Chunk14.stackResult291.1)).2 ≤ 7313 := by
  rw [cost291_eq]
  decide

theorem head292 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard228.name, Chunk14.stackResult292.1)).2 ≤ 7313 := by
  rw [cost292_eq]
  decide

theorem head293 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard229.name, Chunk14.stackResult293.1)).2 ≤ 7313 := by
  rw [cost293_eq]
  decide

theorem head294 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard230.name, Chunk14.stackResult294.1)).2 ≤ 7313 := by
  rw [cost294_eq]
  decide

theorem head295 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard231.name, Chunk14.stackResult295.1)).2 ≤ 7313 := by
  rw [cost295_eq]
  decide

theorem head296 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard232.name, Chunk14.stackResult296.1)).2 ≤ 7313 := by
  rw [cost296_eq]
  decide

theorem head297 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard233.name, Chunk14.stackResult297.1)).2 ≤ 7313 := by
  rw [cost297_eq]
  decide

theorem head298 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard234.name, Chunk14.stackResult298.1)).2 ≤ 7313 := by
  rw [cost298_eq]
  decide

theorem head299 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard235.name, Chunk14.stackResult299.1)).2 ≤ 7313 := by
  rw [cost299_eq]
  decide

theorem head300 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard236.name, Chunk14.stackResult300.1)).2 ≤ 7313 := by
  rw [cost300_eq]
  decide

theorem head301 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard237.name, Chunk14.stackResult301.1)).2 ≤ 7313 := by
  rw [cost301_eq]
  decide

theorem head302 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard238.name, Chunk14.stackResult302.1)).2 ≤ 7313 := by
  rw [cost302_eq]
  decide

theorem head303 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard239.name, Chunk14.stackResult303.1)).2 ≤ 7313 := by
  rw [cost303_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk14.bodies := by
  unfold Chunk14.bodies
  apply bounded_cons _ _ _ head288
  apply bounded_cons _ _ _ head289
  apply bounded_cons _ _ _ head290
  apply bounded_cons _ _ _ head291
  apply bounded_cons _ _ _ head292
  apply bounded_cons _ _ _ head293
  apply bounded_cons _ _ _ head294
  apply bounded_cons _ _ _ head295
  apply bounded_cons _ _ _ head296
  apply bounded_cons _ _ _ head297
  apply bounded_cons _ _ _ head298
  apply bounded_cons _ _ _ head299
  apply bounded_cons _ _ _ head300
  apply bounded_cons _ _ _ head301
  apply bounded_cons _ _ _ head302
  apply bounded_cons _ _ _ head303
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded14
