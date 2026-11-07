import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk45
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded45
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open StackToLabClock LoweredBudget

wave8_kernel_reduce cost784 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard720.name, Chunk45.stackResult784.1)).2
wave8_kernel_reduce cost785 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard721.name, Chunk45.stackResult785.1)).2
wave8_kernel_reduce cost786 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard722.name, Chunk45.stackResult786.1)).2
wave8_kernel_reduce cost787 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard723.name, Chunk45.stackResult787.1)).2
wave8_kernel_reduce cost788 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard724.name, Chunk45.stackResult788.1)).2
wave8_kernel_reduce cost789 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard725.name, Chunk45.stackResult789.1)).2
wave8_kernel_reduce cost790 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard726.name, Chunk45.stackResult790.1)).2
wave8_kernel_reduce cost791 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard727.name, Chunk45.stackResult791.1)).2
wave8_kernel_reduce cost792 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard728.name, Chunk45.stackResult792.1)).2
wave8_kernel_reduce cost793 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard729.name, Chunk45.stackResult793.1)).2
wave8_kernel_reduce cost794 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard730.name, Chunk45.stackResult794.1)).2
wave8_kernel_reduce cost795 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard731.name, Chunk45.stackResult795.1)).2
wave8_kernel_reduce cost796 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard732.name, Chunk45.stackResult796.1)).2
wave8_kernel_reduce cost797 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard733.name, Chunk45.stackResult797.1)).2
wave8_kernel_reduce cost798 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard734.name, Chunk45.stackResult798.1)).2
wave8_kernel_reduce cost799 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard735.name, Chunk45.stackResult799.1)).2

theorem head784 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard720.name, Chunk45.stackResult784.1)).2 ≤ 7313 := by
  rw [cost784_eq]
  decide

theorem head785 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard721.name, Chunk45.stackResult785.1)).2 ≤ 7313 := by
  rw [cost785_eq]
  decide

theorem head786 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard722.name, Chunk45.stackResult786.1)).2 ≤ 7313 := by
  rw [cost786_eq]
  decide

theorem head787 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard723.name, Chunk45.stackResult787.1)).2 ≤ 7313 := by
  rw [cost787_eq]
  decide

theorem head788 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard724.name, Chunk45.stackResult788.1)).2 ≤ 7313 := by
  rw [cost788_eq]
  decide

theorem head789 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard725.name, Chunk45.stackResult789.1)).2 ≤ 7313 := by
  rw [cost789_eq]
  decide

theorem head790 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard726.name, Chunk45.stackResult790.1)).2 ≤ 7313 := by
  rw [cost790_eq]
  decide

theorem head791 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard727.name, Chunk45.stackResult791.1)).2 ≤ 7313 := by
  rw [cost791_eq]
  decide

theorem head792 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard728.name, Chunk45.stackResult792.1)).2 ≤ 7313 := by
  rw [cost792_eq]
  decide

theorem head793 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard729.name, Chunk45.stackResult793.1)).2 ≤ 7313 := by
  rw [cost793_eq]
  decide

theorem head794 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard730.name, Chunk45.stackResult794.1)).2 ≤ 7313 := by
  rw [cost794_eq]
  decide

theorem head795 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard731.name, Chunk45.stackResult795.1)).2 ≤ 7313 := by
  rw [cost795_eq]
  decide

theorem head796 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard732.name, Chunk45.stackResult796.1)).2 ≤ 7313 := by
  rw [cost796_eq]
  decide

theorem head797 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard733.name, Chunk45.stackResult797.1)).2 ≤ 7313 := by
  rw [cost797_eq]
  decide

theorem head798 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard734.name, Chunk45.stackResult798.1)).2 ≤ 7313 := by
  rw [cost798_eq]
  decide

theorem head799 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard735.name, Chunk45.stackResult799.1)).2 ≤ 7313 := by
  rw [cost799_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk45.bodies := by
  unfold Chunk45.bodies
  apply bounded_cons _ _ _ head784
  apply bounded_cons _ _ _ head785
  apply bounded_cons _ _ _ head786
  apply bounded_cons _ _ _ head787
  apply bounded_cons _ _ _ head788
  apply bounded_cons _ _ _ head789
  apply bounded_cons _ _ _ head790
  apply bounded_cons _ _ _ head791
  apply bounded_cons _ _ _ head792
  apply bounded_cons _ _ _ head793
  apply bounded_cons _ _ _ head794
  apply bounded_cons _ _ _ head795
  apply bounded_cons _ _ _ head796
  apply bounded_cons _ _ _ head797
  apply bounded_cons _ _ _ head798
  apply bounded_cons _ _ _ head799
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded45
