import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk49
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded49
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open StackToLabClock LoweredBudget

wave8_kernel_reduce cost848 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard784.name, Chunk49.stackResult848.1)).2
wave8_kernel_reduce cost849 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard785.name, Chunk49.stackResult849.1)).2
wave8_kernel_reduce cost850 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard786.name, Chunk49.stackResult850.1)).2
wave8_kernel_reduce cost851 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard787.name, Chunk49.stackResult851.1)).2
wave8_kernel_reduce cost852 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard788.name, Chunk49.stackResult852.1)).2
wave8_kernel_reduce cost853 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard789.name, Chunk49.stackResult853.1)).2
wave8_kernel_reduce cost854 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard790.name, Chunk49.stackResult854.1)).2
wave8_kernel_reduce cost855 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard791.name, Chunk49.stackResult855.1)).2
wave8_kernel_reduce cost856 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard792.name, Chunk49.stackResult856.1)).2
wave8_kernel_reduce cost857 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard793.name, Chunk49.stackResult857.1)).2
wave8_kernel_reduce cost858 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard794.name, Chunk49.stackResult858.1)).2
wave8_kernel_reduce cost859 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard795.name, Chunk49.stackResult859.1)).2
wave8_kernel_reduce cost860 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard796.name, Chunk49.stackResult860.1)).2
wave8_kernel_reduce cost861 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard797.name, Chunk49.stackResult861.1)).2
wave8_kernel_reduce cost862 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard798.name, Chunk49.stackResult862.1)).2
wave8_kernel_reduce cost863 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard799.name, Chunk49.stackResult863.1)).2

theorem head848 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard784.name, Chunk49.stackResult848.1)).2 ≤ 7313 := by
  rw [cost848_eq]
  decide

theorem head849 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard785.name, Chunk49.stackResult849.1)).2 ≤ 7313 := by
  rw [cost849_eq]
  decide

theorem head850 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard786.name, Chunk49.stackResult850.1)).2 ≤ 7313 := by
  rw [cost850_eq]
  decide

theorem head851 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard787.name, Chunk49.stackResult851.1)).2 ≤ 7313 := by
  rw [cost851_eq]
  decide

theorem head852 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard788.name, Chunk49.stackResult852.1)).2 ≤ 7313 := by
  rw [cost852_eq]
  decide

theorem head853 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard789.name, Chunk49.stackResult853.1)).2 ≤ 7313 := by
  rw [cost853_eq]
  decide

theorem head854 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard790.name, Chunk49.stackResult854.1)).2 ≤ 7313 := by
  rw [cost854_eq]
  decide

theorem head855 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard791.name, Chunk49.stackResult855.1)).2 ≤ 7313 := by
  rw [cost855_eq]
  decide

theorem head856 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard792.name, Chunk49.stackResult856.1)).2 ≤ 7313 := by
  rw [cost856_eq]
  decide

theorem head857 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard793.name, Chunk49.stackResult857.1)).2 ≤ 7313 := by
  rw [cost857_eq]
  decide

theorem head858 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard794.name, Chunk49.stackResult858.1)).2 ≤ 7313 := by
  rw [cost858_eq]
  decide

theorem head859 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard795.name, Chunk49.stackResult859.1)).2 ≤ 7313 := by
  rw [cost859_eq]
  decide

theorem head860 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard796.name, Chunk49.stackResult860.1)).2 ≤ 7313 := by
  rw [cost860_eq]
  decide

theorem head861 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard797.name, Chunk49.stackResult861.1)).2 ≤ 7313 := by
  rw [cost861_eq]
  decide

theorem head862 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard798.name, Chunk49.stackResult862.1)).2 ≤ 7313 := by
  rw [cost862_eq]
  decide

theorem head863 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard799.name, Chunk49.stackResult863.1)).2 ≤ 7313 := by
  rw [cost863_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk49.bodies := by
  unfold Chunk49.bodies
  apply bounded_cons _ _ _ head848
  apply bounded_cons _ _ _ head849
  apply bounded_cons _ _ _ head850
  apply bounded_cons _ _ _ head851
  apply bounded_cons _ _ _ head852
  apply bounded_cons _ _ _ head853
  apply bounded_cons _ _ _ head854
  apply bounded_cons _ _ _ head855
  apply bounded_cons _ _ _ head856
  apply bounded_cons _ _ _ head857
  apply bounded_cons _ _ _ head858
  apply bounded_cons _ _ _ head859
  apply bounded_cons _ _ _ head860
  apply bounded_cons _ _ _ head861
  apply bounded_cons _ _ _ head862
  apply bounded_cons _ _ _ head863
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded49
