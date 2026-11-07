import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk15
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded15
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open StackToLabClock LoweredBudget

wave8_kernel_reduce cost304 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard240.name, Chunk15.stackResult304.1)).2
wave8_kernel_reduce cost305 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard241.name, Chunk15.stackResult305.1)).2
wave8_kernel_reduce cost306 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard242.name, Chunk15.stackResult306.1)).2
wave8_kernel_reduce cost307 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard243.name, Chunk15.stackResult307.1)).2
wave8_kernel_reduce cost308 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard244.name, Chunk15.stackResult308.1)).2
wave8_kernel_reduce cost309 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard245.name, Chunk15.stackResult309.1)).2
wave8_kernel_reduce cost310 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard246.name, Chunk15.stackResult310.1)).2
wave8_kernel_reduce cost311 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard247.name, Chunk15.stackResult311.1)).2
wave8_kernel_reduce cost312 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard248.name, Chunk15.stackResult312.1)).2
wave8_kernel_reduce cost313 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard249.name, Chunk15.stackResult313.1)).2
wave8_kernel_reduce cost314 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard250.name, Chunk15.stackResult314.1)).2
wave8_kernel_reduce cost315 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard251.name, Chunk15.stackResult315.1)).2
wave8_kernel_reduce cost316 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard252.name, Chunk15.stackResult316.1)).2
wave8_kernel_reduce cost317 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard253.name, Chunk15.stackResult317.1)).2
wave8_kernel_reduce cost318 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard254.name, Chunk15.stackResult318.1)).2
wave8_kernel_reduce cost319 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard255.name, Chunk15.stackResult319.1)).2

theorem head304 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard240.name, Chunk15.stackResult304.1)).2 ≤ 7313 := by
  rw [cost304_eq]
  decide

theorem head305 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard241.name, Chunk15.stackResult305.1)).2 ≤ 7313 := by
  rw [cost305_eq]
  decide

theorem head306 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard242.name, Chunk15.stackResult306.1)).2 ≤ 7313 := by
  rw [cost306_eq]
  decide

theorem head307 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard243.name, Chunk15.stackResult307.1)).2 ≤ 7313 := by
  rw [cost307_eq]
  decide

theorem head308 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard244.name, Chunk15.stackResult308.1)).2 ≤ 7313 := by
  rw [cost308_eq]
  decide

theorem head309 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard245.name, Chunk15.stackResult309.1)).2 ≤ 7313 := by
  rw [cost309_eq]
  decide

theorem head310 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard246.name, Chunk15.stackResult310.1)).2 ≤ 7313 := by
  rw [cost310_eq]
  decide

theorem head311 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard247.name, Chunk15.stackResult311.1)).2 ≤ 7313 := by
  rw [cost311_eq]
  decide

theorem head312 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard248.name, Chunk15.stackResult312.1)).2 ≤ 7313 := by
  rw [cost312_eq]
  decide

theorem head313 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard249.name, Chunk15.stackResult313.1)).2 ≤ 7313 := by
  rw [cost313_eq]
  decide

theorem head314 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard250.name, Chunk15.stackResult314.1)).2 ≤ 7313 := by
  rw [cost314_eq]
  decide

theorem head315 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard251.name, Chunk15.stackResult315.1)).2 ≤ 7313 := by
  rw [cost315_eq]
  decide

theorem head316 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard252.name, Chunk15.stackResult316.1)).2 ≤ 7313 := by
  rw [cost316_eq]
  decide

theorem head317 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard253.name, Chunk15.stackResult317.1)).2 ≤ 7313 := by
  rw [cost317_eq]
  decide

theorem head318 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard254.name, Chunk15.stackResult318.1)).2 ≤ 7313 := by
  rw [cost318_eq]
  decide

theorem head319 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard255.name, Chunk15.stackResult319.1)).2 ≤ 7313 := by
  rw [cost319_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk15.bodies := by
  unfold Chunk15.bodies
  apply bounded_cons _ _ _ head304
  apply bounded_cons _ _ _ head305
  apply bounded_cons _ _ _ head306
  apply bounded_cons _ _ _ head307
  apply bounded_cons _ _ _ head308
  apply bounded_cons _ _ _ head309
  apply bounded_cons _ _ _ head310
  apply bounded_cons _ _ _ head311
  apply bounded_cons _ _ _ head312
  apply bounded_cons _ _ _ head313
  apply bounded_cons _ _ _ head314
  apply bounded_cons _ _ _ head315
  apply bounded_cons _ _ _ head316
  apply bounded_cons _ _ _ head317
  apply bounded_cons _ _ _ head318
  apply bounded_cons _ _ _ head319
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded15
