import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk41
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded41
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open StackToLabClock LoweredBudget

wave8_kernel_reduce cost720 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard656.name, Chunk41.stackResult720.1)).2
wave8_kernel_reduce cost721 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard657.name, Chunk41.stackResult721.1)).2
wave8_kernel_reduce cost722 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard658.name, Chunk41.stackResult722.1)).2
wave8_kernel_reduce cost723 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard659.name, Chunk41.stackResult723.1)).2
wave8_kernel_reduce cost724 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard660.name, Chunk41.stackResult724.1)).2
wave8_kernel_reduce cost725 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard661.name, Chunk41.stackResult725.1)).2
wave8_kernel_reduce cost726 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard662.name, Chunk41.stackResult726.1)).2
wave8_kernel_reduce cost727 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard663.name, Chunk41.stackResult727.1)).2
wave8_kernel_reduce cost728 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard664.name, Chunk41.stackResult728.1)).2
wave8_kernel_reduce cost729 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard665.name, Chunk41.stackResult729.1)).2
wave8_kernel_reduce cost730 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard666.name, Chunk41.stackResult730.1)).2
wave8_kernel_reduce cost731 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard667.name, Chunk41.stackResult731.1)).2
wave8_kernel_reduce cost732 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard668.name, Chunk41.stackResult732.1)).2
wave8_kernel_reduce cost733 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard669.name, Chunk41.stackResult733.1)).2
wave8_kernel_reduce cost734 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard670.name, Chunk41.stackResult734.1)).2
wave8_kernel_reduce cost735 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard671.name, Chunk41.stackResult735.1)).2

theorem head720 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard656.name, Chunk41.stackResult720.1)).2 ≤ 7313 := by
  rw [cost720_eq]
  decide

theorem head721 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard657.name, Chunk41.stackResult721.1)).2 ≤ 7313 := by
  rw [cost721_eq]
  decide

theorem head722 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard658.name, Chunk41.stackResult722.1)).2 ≤ 7313 := by
  rw [cost722_eq]
  decide

theorem head723 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard659.name, Chunk41.stackResult723.1)).2 ≤ 7313 := by
  rw [cost723_eq]
  decide

theorem head724 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard660.name, Chunk41.stackResult724.1)).2 ≤ 7313 := by
  rw [cost724_eq]
  decide

theorem head725 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard661.name, Chunk41.stackResult725.1)).2 ≤ 7313 := by
  rw [cost725_eq]
  decide

theorem head726 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard662.name, Chunk41.stackResult726.1)).2 ≤ 7313 := by
  rw [cost726_eq]
  decide

theorem head727 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard663.name, Chunk41.stackResult727.1)).2 ≤ 7313 := by
  rw [cost727_eq]
  decide

theorem head728 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard664.name, Chunk41.stackResult728.1)).2 ≤ 7313 := by
  rw [cost728_eq]
  decide

theorem head729 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard665.name, Chunk41.stackResult729.1)).2 ≤ 7313 := by
  rw [cost729_eq]
  decide

theorem head730 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard666.name, Chunk41.stackResult730.1)).2 ≤ 7313 := by
  rw [cost730_eq]
  decide

theorem head731 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard667.name, Chunk41.stackResult731.1)).2 ≤ 7313 := by
  rw [cost731_eq]
  decide

theorem head732 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard668.name, Chunk41.stackResult732.1)).2 ≤ 7313 := by
  rw [cost732_eq]
  decide

theorem head733 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard669.name, Chunk41.stackResult733.1)).2 ≤ 7313 := by
  rw [cost733_eq]
  decide

theorem head734 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard670.name, Chunk41.stackResult734.1)).2 ≤ 7313 := by
  rw [cost734_eq]
  decide

theorem head735 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard671.name, Chunk41.stackResult735.1)).2 ≤ 7313 := by
  rw [cost735_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk41.bodies := by
  unfold Chunk41.bodies
  apply bounded_cons _ _ _ head720
  apply bounded_cons _ _ _ head721
  apply bounded_cons _ _ _ head722
  apply bounded_cons _ _ _ head723
  apply bounded_cons _ _ _ head724
  apply bounded_cons _ _ _ head725
  apply bounded_cons _ _ _ head726
  apply bounded_cons _ _ _ head727
  apply bounded_cons _ _ _ head728
  apply bounded_cons _ _ _ head729
  apply bounded_cons _ _ _ head730
  apply bounded_cons _ _ _ head731
  apply bounded_cons _ _ _ head732
  apply bounded_cons _ _ _ head733
  apply bounded_cons _ _ _ head734
  apply bounded_cons _ _ _ head735
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded41
