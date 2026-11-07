import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk23
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded23
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open StackToLabClock LoweredBudget

wave8_kernel_reduce cost432 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard368.name, Chunk23.stackResult432.1)).2
wave8_kernel_reduce cost433 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard369.name, Chunk23.stackResult433.1)).2
wave8_kernel_reduce cost434 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard370.name, Chunk23.stackResult434.1)).2
wave8_kernel_reduce cost435 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard371.name, Chunk23.stackResult435.1)).2
wave8_kernel_reduce cost436 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard372.name, Chunk23.stackResult436.1)).2
wave8_kernel_reduce cost437 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard373.name, Chunk23.stackResult437.1)).2
wave8_kernel_reduce cost438 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard374.name, Chunk23.stackResult438.1)).2
wave8_kernel_reduce cost439 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard375.name, Chunk23.stackResult439.1)).2
wave8_kernel_reduce cost440 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard376.name, Chunk23.stackResult440.1)).2
wave8_kernel_reduce cost441 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard377.name, Chunk23.stackResult441.1)).2
wave8_kernel_reduce cost442 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard378.name, Chunk23.stackResult442.1)).2
wave8_kernel_reduce cost443 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard379.name, Chunk23.stackResult443.1)).2
wave8_kernel_reduce cost444 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard380.name, Chunk23.stackResult444.1)).2
wave8_kernel_reduce cost445 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard381.name, Chunk23.stackResult445.1)).2
wave8_kernel_reduce cost446 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard382.name, Chunk23.stackResult446.1)).2
wave8_kernel_reduce cost447 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard383.name, Chunk23.stackResult447.1)).2

theorem head432 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard368.name, Chunk23.stackResult432.1)).2 ≤ 7313 := by
  rw [cost432_eq]
  decide

theorem head433 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard369.name, Chunk23.stackResult433.1)).2 ≤ 7313 := by
  rw [cost433_eq]
  decide

theorem head434 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard370.name, Chunk23.stackResult434.1)).2 ≤ 7313 := by
  rw [cost434_eq]
  decide

theorem head435 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard371.name, Chunk23.stackResult435.1)).2 ≤ 7313 := by
  rw [cost435_eq]
  decide

theorem head436 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard372.name, Chunk23.stackResult436.1)).2 ≤ 7313 := by
  rw [cost436_eq]
  decide

theorem head437 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard373.name, Chunk23.stackResult437.1)).2 ≤ 7313 := by
  rw [cost437_eq]
  decide

theorem head438 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard374.name, Chunk23.stackResult438.1)).2 ≤ 7313 := by
  rw [cost438_eq]
  decide

theorem head439 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard375.name, Chunk23.stackResult439.1)).2 ≤ 7313 := by
  rw [cost439_eq]
  decide

theorem head440 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard376.name, Chunk23.stackResult440.1)).2 ≤ 7313 := by
  rw [cost440_eq]
  decide

theorem head441 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard377.name, Chunk23.stackResult441.1)).2 ≤ 7313 := by
  rw [cost441_eq]
  decide

theorem head442 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard378.name, Chunk23.stackResult442.1)).2 ≤ 7313 := by
  rw [cost442_eq]
  decide

theorem head443 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard379.name, Chunk23.stackResult443.1)).2 ≤ 7313 := by
  rw [cost443_eq]
  decide

theorem head444 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard380.name, Chunk23.stackResult444.1)).2 ≤ 7313 := by
  rw [cost444_eq]
  decide

theorem head445 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard381.name, Chunk23.stackResult445.1)).2 ≤ 7313 := by
  rw [cost445_eq]
  decide

theorem head446 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard382.name, Chunk23.stackResult446.1)).2 ≤ 7313 := by
  rw [cost446_eq]
  decide

theorem head447 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard383.name, Chunk23.stackResult447.1)).2 ≤ 7313 := by
  rw [cost447_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk23.bodies := by
  unfold Chunk23.bodies
  apply bounded_cons _ _ _ head432
  apply bounded_cons _ _ _ head433
  apply bounded_cons _ _ _ head434
  apply bounded_cons _ _ _ head435
  apply bounded_cons _ _ _ head436
  apply bounded_cons _ _ _ head437
  apply bounded_cons _ _ _ head438
  apply bounded_cons _ _ _ head439
  apply bounded_cons _ _ _ head440
  apply bounded_cons _ _ _ head441
  apply bounded_cons _ _ _ head442
  apply bounded_cons _ _ _ head443
  apply bounded_cons _ _ _ head444
  apply bounded_cons _ _ _ head445
  apply bounded_cons _ _ _ head446
  apply bounded_cons _ _ _ head447
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded23
