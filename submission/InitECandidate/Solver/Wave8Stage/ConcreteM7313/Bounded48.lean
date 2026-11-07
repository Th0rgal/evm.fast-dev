import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk48
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded48
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open StackToLabClock LoweredBudget

wave8_kernel_reduce cost832 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard768.name, Chunk48.stackResult832.1)).2
wave8_kernel_reduce cost833 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard769.name, Chunk48.stackResult833.1)).2
wave8_kernel_reduce cost834 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard770.name, Chunk48.stackResult834.1)).2
wave8_kernel_reduce cost835 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard771.name, Chunk48.stackResult835.1)).2
wave8_kernel_reduce cost836 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard772.name, Chunk48.stackResult836.1)).2
wave8_kernel_reduce cost837 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard773.name, Chunk48.stackResult837.1)).2
wave8_kernel_reduce cost838 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard774.name, Chunk48.stackResult838.1)).2
wave8_kernel_reduce cost839 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard775.name, Chunk48.stackResult839.1)).2
wave8_kernel_reduce cost840 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard776.name, Chunk48.stackResult840.1)).2
wave8_kernel_reduce cost841 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard777.name, Chunk48.stackResult841.1)).2
wave8_kernel_reduce cost842 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard778.name, Chunk48.stackResult842.1)).2
wave8_kernel_reduce cost843 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard779.name, Chunk48.stackResult843.1)).2
wave8_kernel_reduce cost844 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard780.name, Chunk48.stackResult844.1)).2
wave8_kernel_reduce cost845 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard781.name, Chunk48.stackResult845.1)).2
wave8_kernel_reduce cost846 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard782.name, Chunk48.stackResult846.1)).2
wave8_kernel_reduce cost847 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard783.name, Chunk48.stackResult847.1)).2

theorem head832 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard768.name, Chunk48.stackResult832.1)).2 ≤ 7313 := by
  rw [cost832_eq]
  decide

theorem head833 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard769.name, Chunk48.stackResult833.1)).2 ≤ 7313 := by
  rw [cost833_eq]
  decide

theorem head834 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard770.name, Chunk48.stackResult834.1)).2 ≤ 7313 := by
  rw [cost834_eq]
  decide

theorem head835 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard771.name, Chunk48.stackResult835.1)).2 ≤ 7313 := by
  rw [cost835_eq]
  decide

theorem head836 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard772.name, Chunk48.stackResult836.1)).2 ≤ 7313 := by
  rw [cost836_eq]
  decide

theorem head837 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard773.name, Chunk48.stackResult837.1)).2 ≤ 7313 := by
  rw [cost837_eq]
  decide

theorem head838 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard774.name, Chunk48.stackResult838.1)).2 ≤ 7313 := by
  rw [cost838_eq]
  decide

theorem head839 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard775.name, Chunk48.stackResult839.1)).2 ≤ 7313 := by
  rw [cost839_eq]
  decide

theorem head840 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard776.name, Chunk48.stackResult840.1)).2 ≤ 7313 := by
  rw [cost840_eq]
  decide

theorem head841 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard777.name, Chunk48.stackResult841.1)).2 ≤ 7313 := by
  rw [cost841_eq]
  decide

theorem head842 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard778.name, Chunk48.stackResult842.1)).2 ≤ 7313 := by
  rw [cost842_eq]
  decide

theorem head843 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard779.name, Chunk48.stackResult843.1)).2 ≤ 7313 := by
  rw [cost843_eq]
  decide

theorem head844 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard780.name, Chunk48.stackResult844.1)).2 ≤ 7313 := by
  rw [cost844_eq]
  decide

theorem head845 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard781.name, Chunk48.stackResult845.1)).2 ≤ 7313 := by
  rw [cost845_eq]
  decide

theorem head846 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard782.name, Chunk48.stackResult846.1)).2 ≤ 7313 := by
  rw [cost846_eq]
  decide

theorem head847 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard783.name, Chunk48.stackResult847.1)).2 ≤ 7313 := by
  rw [cost847_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk48.bodies := by
  unfold Chunk48.bodies
  apply bounded_cons _ _ _ head832
  apply bounded_cons _ _ _ head833
  apply bounded_cons _ _ _ head834
  apply bounded_cons _ _ _ head835
  apply bounded_cons _ _ _ head836
  apply bounded_cons _ _ _ head837
  apply bounded_cons _ _ _ head838
  apply bounded_cons _ _ _ head839
  apply bounded_cons _ _ _ head840
  apply bounded_cons _ _ _ head841
  apply bounded_cons _ _ _ head842
  apply bounded_cons _ _ _ head843
  apply bounded_cons _ _ _ head844
  apply bounded_cons _ _ _ head845
  apply bounded_cons _ _ _ head846
  apply bounded_cons _ _ _ head847
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded48
