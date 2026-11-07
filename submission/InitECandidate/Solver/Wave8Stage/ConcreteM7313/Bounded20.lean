import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk20
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded20
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open StackToLabClock LoweredBudget

wave8_kernel_reduce cost384 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard320.name, Chunk20.stackResult384.1)).2
wave8_kernel_reduce cost385 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard321.name, Chunk20.stackResult385.1)).2
wave8_kernel_reduce cost386 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard322.name, Chunk20.stackResult386.1)).2
wave8_kernel_reduce cost387 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard323.name, Chunk20.stackResult387.1)).2
wave8_kernel_reduce cost388 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard324.name, Chunk20.stackResult388.1)).2
wave8_kernel_reduce cost389 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard325.name, Chunk20.stackResult389.1)).2
wave8_kernel_reduce cost390 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard326.name, Chunk20.stackResult390.1)).2
wave8_kernel_reduce cost391 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard327.name, Chunk20.stackResult391.1)).2
wave8_kernel_reduce cost392 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard328.name, Chunk20.stackResult392.1)).2
wave8_kernel_reduce cost393 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard329.name, Chunk20.stackResult393.1)).2
wave8_kernel_reduce cost394 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard330.name, Chunk20.stackResult394.1)).2
wave8_kernel_reduce cost395 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard331.name, Chunk20.stackResult395.1)).2
wave8_kernel_reduce cost396 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard332.name, Chunk20.stackResult396.1)).2
wave8_kernel_reduce cost397 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard333.name, Chunk20.stackResult397.1)).2
wave8_kernel_reduce cost398 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard334.name, Chunk20.stackResult398.1)).2
wave8_kernel_reduce cost399 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard335.name, Chunk20.stackResult399.1)).2

theorem head384 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard320.name, Chunk20.stackResult384.1)).2 ≤ 7313 := by
  rw [cost384_eq]
  decide

theorem head385 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard321.name, Chunk20.stackResult385.1)).2 ≤ 7313 := by
  rw [cost385_eq]
  decide

theorem head386 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard322.name, Chunk20.stackResult386.1)).2 ≤ 7313 := by
  rw [cost386_eq]
  decide

theorem head387 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard323.name, Chunk20.stackResult387.1)).2 ≤ 7313 := by
  rw [cost387_eq]
  decide

theorem head388 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard324.name, Chunk20.stackResult388.1)).2 ≤ 7313 := by
  rw [cost388_eq]
  decide

theorem head389 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard325.name, Chunk20.stackResult389.1)).2 ≤ 7313 := by
  rw [cost389_eq]
  decide

theorem head390 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard326.name, Chunk20.stackResult390.1)).2 ≤ 7313 := by
  rw [cost390_eq]
  decide

theorem head391 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard327.name, Chunk20.stackResult391.1)).2 ≤ 7313 := by
  rw [cost391_eq]
  decide

theorem head392 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard328.name, Chunk20.stackResult392.1)).2 ≤ 7313 := by
  rw [cost392_eq]
  decide

theorem head393 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard329.name, Chunk20.stackResult393.1)).2 ≤ 7313 := by
  rw [cost393_eq]
  decide

theorem head394 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard330.name, Chunk20.stackResult394.1)).2 ≤ 7313 := by
  rw [cost394_eq]
  decide

theorem head395 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard331.name, Chunk20.stackResult395.1)).2 ≤ 7313 := by
  rw [cost395_eq]
  decide

theorem head396 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard332.name, Chunk20.stackResult396.1)).2 ≤ 7313 := by
  rw [cost396_eq]
  decide

theorem head397 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard333.name, Chunk20.stackResult397.1)).2 ≤ 7313 := by
  rw [cost397_eq]
  decide

theorem head398 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard334.name, Chunk20.stackResult398.1)).2 ≤ 7313 := by
  rw [cost398_eq]
  decide

theorem head399 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard335.name, Chunk20.stackResult399.1)).2 ≤ 7313 := by
  rw [cost399_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk20.bodies := by
  unfold Chunk20.bodies
  apply bounded_cons _ _ _ head384
  apply bounded_cons _ _ _ head385
  apply bounded_cons _ _ _ head386
  apply bounded_cons _ _ _ head387
  apply bounded_cons _ _ _ head388
  apply bounded_cons _ _ _ head389
  apply bounded_cons _ _ _ head390
  apply bounded_cons _ _ _ head391
  apply bounded_cons _ _ _ head392
  apply bounded_cons _ _ _ head393
  apply bounded_cons _ _ _ head394
  apply bounded_cons _ _ _ head395
  apply bounded_cons _ _ _ head396
  apply bounded_cons _ _ _ head397
  apply bounded_cons _ _ _ head398
  apply bounded_cons _ _ _ head399
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded20
