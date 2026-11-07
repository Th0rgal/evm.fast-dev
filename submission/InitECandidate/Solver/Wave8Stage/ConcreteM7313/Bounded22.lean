import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk22
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded22
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open StackToLabClock LoweredBudget

wave8_kernel_reduce cost416 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard352.name, Chunk22.stackResult416.1)).2
wave8_kernel_reduce cost417 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard353.name, Chunk22.stackResult417.1)).2
wave8_kernel_reduce cost418 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard354.name, Chunk22.stackResult418.1)).2
wave8_kernel_reduce cost419 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard355.name, Chunk22.stackResult419.1)).2
wave8_kernel_reduce cost420 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard356.name, Chunk22.stackResult420.1)).2
wave8_kernel_reduce cost421 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard357.name, Chunk22.stackResult421.1)).2
wave8_kernel_reduce cost422 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard358.name, Chunk22.stackResult422.1)).2
wave8_kernel_reduce cost423 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard359.name, Chunk22.stackResult423.1)).2
wave8_kernel_reduce cost424 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard360.name, Chunk22.stackResult424.1)).2
wave8_kernel_reduce cost425 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard361.name, Chunk22.stackResult425.1)).2
wave8_kernel_reduce cost426 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard362.name, Chunk22.stackResult426.1)).2
wave8_kernel_reduce cost427 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard363.name, Chunk22.stackResult427.1)).2
wave8_kernel_reduce cost428 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard364.name, Chunk22.stackResult428.1)).2
wave8_kernel_reduce cost429 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard365.name, Chunk22.stackResult429.1)).2
wave8_kernel_reduce cost430 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard366.name, Chunk22.stackResult430.1)).2
wave8_kernel_reduce cost431 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard367.name, Chunk22.stackResult431.1)).2

theorem head416 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard352.name, Chunk22.stackResult416.1)).2 ≤ 7313 := by
  rw [cost416_eq]
  decide

theorem head417 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard353.name, Chunk22.stackResult417.1)).2 ≤ 7313 := by
  rw [cost417_eq]
  decide

theorem head418 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard354.name, Chunk22.stackResult418.1)).2 ≤ 7313 := by
  rw [cost418_eq]
  decide

theorem head419 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard355.name, Chunk22.stackResult419.1)).2 ≤ 7313 := by
  rw [cost419_eq]
  decide

theorem head420 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard356.name, Chunk22.stackResult420.1)).2 ≤ 7313 := by
  rw [cost420_eq]
  decide

theorem head421 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard357.name, Chunk22.stackResult421.1)).2 ≤ 7313 := by
  rw [cost421_eq]
  decide

theorem head422 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard358.name, Chunk22.stackResult422.1)).2 ≤ 7313 := by
  rw [cost422_eq]
  decide

theorem head423 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard359.name, Chunk22.stackResult423.1)).2 ≤ 7313 := by
  rw [cost423_eq]
  decide

theorem head424 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard360.name, Chunk22.stackResult424.1)).2 ≤ 7313 := by
  rw [cost424_eq]
  decide

theorem head425 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard361.name, Chunk22.stackResult425.1)).2 ≤ 7313 := by
  rw [cost425_eq]
  decide

theorem head426 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard362.name, Chunk22.stackResult426.1)).2 ≤ 7313 := by
  rw [cost426_eq]
  decide

theorem head427 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard363.name, Chunk22.stackResult427.1)).2 ≤ 7313 := by
  rw [cost427_eq]
  decide

theorem head428 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard364.name, Chunk22.stackResult428.1)).2 ≤ 7313 := by
  rw [cost428_eq]
  decide

theorem head429 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard365.name, Chunk22.stackResult429.1)).2 ≤ 7313 := by
  rw [cost429_eq]
  decide

theorem head430 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard366.name, Chunk22.stackResult430.1)).2 ≤ 7313 := by
  rw [cost430_eq]
  decide

theorem head431 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard367.name, Chunk22.stackResult431.1)).2 ≤ 7313 := by
  rw [cost431_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk22.bodies := by
  unfold Chunk22.bodies
  apply bounded_cons _ _ _ head416
  apply bounded_cons _ _ _ head417
  apply bounded_cons _ _ _ head418
  apply bounded_cons _ _ _ head419
  apply bounded_cons _ _ _ head420
  apply bounded_cons _ _ _ head421
  apply bounded_cons _ _ _ head422
  apply bounded_cons _ _ _ head423
  apply bounded_cons _ _ _ head424
  apply bounded_cons _ _ _ head425
  apply bounded_cons _ _ _ head426
  apply bounded_cons _ _ _ head427
  apply bounded_cons _ _ _ head428
  apply bounded_cons _ _ _ head429
  apply bounded_cons _ _ _ head430
  apply bounded_cons _ _ _ head431
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded22
