import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk44
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded44
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open StackToLabClock LoweredBudget

wave8_kernel_reduce cost768 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard704.name, Chunk44.stackResult768.1)).2
wave8_kernel_reduce cost769 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard705.name, Chunk44.stackResult769.1)).2
wave8_kernel_reduce cost770 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard706.name, Chunk44.stackResult770.1)).2
wave8_kernel_reduce cost771 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard707.name, Chunk44.stackResult771.1)).2
wave8_kernel_reduce cost772 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard708.name, Chunk44.stackResult772.1)).2
wave8_kernel_reduce cost773 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard709.name, Chunk44.stackResult773.1)).2
wave8_kernel_reduce cost774 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard710.name, Chunk44.stackResult774.1)).2
wave8_kernel_reduce cost775 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard711.name, Chunk44.stackResult775.1)).2
wave8_kernel_reduce cost776 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard712.name, Chunk44.stackResult776.1)).2
wave8_kernel_reduce cost777 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard713.name, Chunk44.stackResult777.1)).2
wave8_kernel_reduce cost778 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard714.name, Chunk44.stackResult778.1)).2
wave8_kernel_reduce cost779 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard715.name, Chunk44.stackResult779.1)).2
wave8_kernel_reduce cost780 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard716.name, Chunk44.stackResult780.1)).2
wave8_kernel_reduce cost781 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard717.name, Chunk44.stackResult781.1)).2
wave8_kernel_reduce cost782 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard718.name, Chunk44.stackResult782.1)).2
wave8_kernel_reduce cost783 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard719.name, Chunk44.stackResult783.1)).2

theorem head768 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard704.name, Chunk44.stackResult768.1)).2 ≤ 7313 := by
  rw [cost768_eq]
  decide

theorem head769 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard705.name, Chunk44.stackResult769.1)).2 ≤ 7313 := by
  rw [cost769_eq]
  decide

theorem head770 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard706.name, Chunk44.stackResult770.1)).2 ≤ 7313 := by
  rw [cost770_eq]
  decide

theorem head771 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard707.name, Chunk44.stackResult771.1)).2 ≤ 7313 := by
  rw [cost771_eq]
  decide

theorem head772 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard708.name, Chunk44.stackResult772.1)).2 ≤ 7313 := by
  rw [cost772_eq]
  decide

theorem head773 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard709.name, Chunk44.stackResult773.1)).2 ≤ 7313 := by
  rw [cost773_eq]
  decide

theorem head774 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard710.name, Chunk44.stackResult774.1)).2 ≤ 7313 := by
  rw [cost774_eq]
  decide

theorem head775 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard711.name, Chunk44.stackResult775.1)).2 ≤ 7313 := by
  rw [cost775_eq]
  decide

theorem head776 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard712.name, Chunk44.stackResult776.1)).2 ≤ 7313 := by
  rw [cost776_eq]
  decide

theorem head777 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard713.name, Chunk44.stackResult777.1)).2 ≤ 7313 := by
  rw [cost777_eq]
  decide

theorem head778 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard714.name, Chunk44.stackResult778.1)).2 ≤ 7313 := by
  rw [cost778_eq]
  decide

theorem head779 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard715.name, Chunk44.stackResult779.1)).2 ≤ 7313 := by
  rw [cost779_eq]
  decide

theorem head780 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard716.name, Chunk44.stackResult780.1)).2 ≤ 7313 := by
  rw [cost780_eq]
  decide

theorem head781 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard717.name, Chunk44.stackResult781.1)).2 ≤ 7313 := by
  rw [cost781_eq]
  decide

theorem head782 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard718.name, Chunk44.stackResult782.1)).2 ≤ 7313 := by
  rw [cost782_eq]
  decide

theorem head783 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard719.name, Chunk44.stackResult783.1)).2 ≤ 7313 := by
  rw [cost783_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk44.bodies := by
  unfold Chunk44.bodies
  apply bounded_cons _ _ _ head768
  apply bounded_cons _ _ _ head769
  apply bounded_cons _ _ _ head770
  apply bounded_cons _ _ _ head771
  apply bounded_cons _ _ _ head772
  apply bounded_cons _ _ _ head773
  apply bounded_cons _ _ _ head774
  apply bounded_cons _ _ _ head775
  apply bounded_cons _ _ _ head776
  apply bounded_cons _ _ _ head777
  apply bounded_cons _ _ _ head778
  apply bounded_cons _ _ _ head779
  apply bounded_cons _ _ _ head780
  apply bounded_cons _ _ _ head781
  apply bounded_cons _ _ _ head782
  apply bounded_cons _ _ _ head783
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded44
