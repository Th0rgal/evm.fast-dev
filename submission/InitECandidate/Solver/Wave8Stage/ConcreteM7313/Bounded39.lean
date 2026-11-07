import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk39
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded39
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open StackToLabClock LoweredBudget

wave8_kernel_reduce cost688 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard624.name, Chunk39.stackResult688.1)).2
wave8_kernel_reduce cost689 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard625.name, Chunk39.stackResult689.1)).2
wave8_kernel_reduce cost690 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard626.name, Chunk39.stackResult690.1)).2
wave8_kernel_reduce cost691 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard627.name, Chunk39.stackResult691.1)).2
wave8_kernel_reduce cost692 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard628.name, Chunk39.stackResult692.1)).2
wave8_kernel_reduce cost693 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard629.name, Chunk39.stackResult693.1)).2
wave8_kernel_reduce cost694 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard630.name, Chunk39.stackResult694.1)).2
wave8_kernel_reduce cost695 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard631.name, Chunk39.stackResult695.1)).2
wave8_kernel_reduce cost696 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard632.name, Chunk39.stackResult696.1)).2
wave8_kernel_reduce cost697 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard633.name, Chunk39.stackResult697.1)).2
wave8_kernel_reduce cost698 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard634.name, Chunk39.stackResult698.1)).2
wave8_kernel_reduce cost699 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard635.name, Chunk39.stackResult699.1)).2
wave8_kernel_reduce cost700 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard636.name, Chunk39.stackResult700.1)).2
wave8_kernel_reduce cost701 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard637.name, Chunk39.stackResult701.1)).2
wave8_kernel_reduce cost702 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard638.name, Chunk39.stackResult702.1)).2
wave8_kernel_reduce cost703 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard639.name, Chunk39.stackResult703.1)).2

theorem head688 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard624.name, Chunk39.stackResult688.1)).2 ≤ 7313 := by
  rw [cost688_eq]
  decide

theorem head689 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard625.name, Chunk39.stackResult689.1)).2 ≤ 7313 := by
  rw [cost689_eq]
  decide

theorem head690 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard626.name, Chunk39.stackResult690.1)).2 ≤ 7313 := by
  rw [cost690_eq]
  decide

theorem head691 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard627.name, Chunk39.stackResult691.1)).2 ≤ 7313 := by
  rw [cost691_eq]
  decide

theorem head692 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard628.name, Chunk39.stackResult692.1)).2 ≤ 7313 := by
  rw [cost692_eq]
  decide

theorem head693 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard629.name, Chunk39.stackResult693.1)).2 ≤ 7313 := by
  rw [cost693_eq]
  decide

theorem head694 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard630.name, Chunk39.stackResult694.1)).2 ≤ 7313 := by
  rw [cost694_eq]
  decide

theorem head695 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard631.name, Chunk39.stackResult695.1)).2 ≤ 7313 := by
  rw [cost695_eq]
  decide

theorem head696 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard632.name, Chunk39.stackResult696.1)).2 ≤ 7313 := by
  rw [cost696_eq]
  decide

theorem head697 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard633.name, Chunk39.stackResult697.1)).2 ≤ 7313 := by
  rw [cost697_eq]
  decide

theorem head698 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard634.name, Chunk39.stackResult698.1)).2 ≤ 7313 := by
  rw [cost698_eq]
  decide

theorem head699 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard635.name, Chunk39.stackResult699.1)).2 ≤ 7313 := by
  rw [cost699_eq]
  decide

theorem head700 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard636.name, Chunk39.stackResult700.1)).2 ≤ 7313 := by
  rw [cost700_eq]
  decide

theorem head701 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard637.name, Chunk39.stackResult701.1)).2 ≤ 7313 := by
  rw [cost701_eq]
  decide

theorem head702 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard638.name, Chunk39.stackResult702.1)).2 ≤ 7313 := by
  rw [cost702_eq]
  decide

theorem head703 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard639.name, Chunk39.stackResult703.1)).2 ≤ 7313 := by
  rw [cost703_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk39.bodies := by
  unfold Chunk39.bodies
  apply bounded_cons _ _ _ head688
  apply bounded_cons _ _ _ head689
  apply bounded_cons _ _ _ head690
  apply bounded_cons _ _ _ head691
  apply bounded_cons _ _ _ head692
  apply bounded_cons _ _ _ head693
  apply bounded_cons _ _ _ head694
  apply bounded_cons _ _ _ head695
  apply bounded_cons _ _ _ head696
  apply bounded_cons _ _ _ head697
  apply bounded_cons _ _ _ head698
  apply bounded_cons _ _ _ head699
  apply bounded_cons _ _ _ head700
  apply bounded_cons _ _ _ head701
  apply bounded_cons _ _ _ head702
  apply bounded_cons _ _ _ head703
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded39
