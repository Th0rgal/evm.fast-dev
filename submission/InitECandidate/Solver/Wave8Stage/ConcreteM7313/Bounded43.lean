import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk43
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded43
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open StackToLabClock LoweredBudget

wave8_kernel_reduce cost752 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard688.name, Chunk43.stackResult752.1)).2
wave8_kernel_reduce cost753 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard689.name, Chunk43.stackResult753.1)).2
wave8_kernel_reduce cost754 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard690.name, Chunk43.stackResult754.1)).2
wave8_kernel_reduce cost755 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard691.name, Chunk43.stackResult755.1)).2
wave8_kernel_reduce cost756 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard692.name, Chunk43.stackResult756.1)).2
wave8_kernel_reduce cost757 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard693.name, Chunk43.stackResult757.1)).2
wave8_kernel_reduce cost758 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard694.name, Chunk43.stackResult758.1)).2
wave8_kernel_reduce cost759 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard695.name, Chunk43.stackResult759.1)).2
wave8_kernel_reduce cost760 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard696.name, Chunk43.stackResult760.1)).2
wave8_kernel_reduce cost761 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard697.name, Chunk43.stackResult761.1)).2
wave8_kernel_reduce cost762 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard698.name, Chunk43.stackResult762.1)).2
wave8_kernel_reduce cost763 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard699.name, Chunk43.stackResult763.1)).2
wave8_kernel_reduce cost764 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard700.name, Chunk43.stackResult764.1)).2
wave8_kernel_reduce cost765 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard701.name, Chunk43.stackResult765.1)).2
wave8_kernel_reduce cost766 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard702.name, Chunk43.stackResult766.1)).2
wave8_kernel_reduce cost767 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard703.name, Chunk43.stackResult767.1)).2

theorem head752 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard688.name, Chunk43.stackResult752.1)).2 ≤ 7313 := by
  rw [cost752_eq]
  decide

theorem head753 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard689.name, Chunk43.stackResult753.1)).2 ≤ 7313 := by
  rw [cost753_eq]
  decide

theorem head754 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard690.name, Chunk43.stackResult754.1)).2 ≤ 7313 := by
  rw [cost754_eq]
  decide

theorem head755 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard691.name, Chunk43.stackResult755.1)).2 ≤ 7313 := by
  rw [cost755_eq]
  decide

theorem head756 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard692.name, Chunk43.stackResult756.1)).2 ≤ 7313 := by
  rw [cost756_eq]
  decide

theorem head757 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard693.name, Chunk43.stackResult757.1)).2 ≤ 7313 := by
  rw [cost757_eq]
  decide

theorem head758 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard694.name, Chunk43.stackResult758.1)).2 ≤ 7313 := by
  rw [cost758_eq]
  decide

theorem head759 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard695.name, Chunk43.stackResult759.1)).2 ≤ 7313 := by
  rw [cost759_eq]
  decide

theorem head760 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard696.name, Chunk43.stackResult760.1)).2 ≤ 7313 := by
  rw [cost760_eq]
  decide

theorem head761 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard697.name, Chunk43.stackResult761.1)).2 ≤ 7313 := by
  rw [cost761_eq]
  decide

theorem head762 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard698.name, Chunk43.stackResult762.1)).2 ≤ 7313 := by
  rw [cost762_eq]
  decide

theorem head763 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard699.name, Chunk43.stackResult763.1)).2 ≤ 7313 := by
  rw [cost763_eq]
  decide

theorem head764 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard700.name, Chunk43.stackResult764.1)).2 ≤ 7313 := by
  rw [cost764_eq]
  decide

theorem head765 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard701.name, Chunk43.stackResult765.1)).2 ≤ 7313 := by
  rw [cost765_eq]
  decide

theorem head766 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard702.name, Chunk43.stackResult766.1)).2 ≤ 7313 := by
  rw [cost766_eq]
  decide

theorem head767 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard703.name, Chunk43.stackResult767.1)).2 ≤ 7313 := by
  rw [cost767_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk43.bodies := by
  unfold Chunk43.bodies
  apply bounded_cons _ _ _ head752
  apply bounded_cons _ _ _ head753
  apply bounded_cons _ _ _ head754
  apply bounded_cons _ _ _ head755
  apply bounded_cons _ _ _ head756
  apply bounded_cons _ _ _ head757
  apply bounded_cons _ _ _ head758
  apply bounded_cons _ _ _ head759
  apply bounded_cons _ _ _ head760
  apply bounded_cons _ _ _ head761
  apply bounded_cons _ _ _ head762
  apply bounded_cons _ _ _ head763
  apply bounded_cons _ _ _ head764
  apply bounded_cons _ _ _ head765
  apply bounded_cons _ _ _ head766
  apply bounded_cons _ _ _ head767
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded43
