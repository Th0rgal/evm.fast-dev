import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk01
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded01
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open StackToLabClock LoweredBudget

wave8_kernel_reduce cost80 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard16.name, Function80.stackResult.1)).2
wave8_kernel_reduce cost81 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard17.name, Function81.stackResult.1)).2
wave8_kernel_reduce cost82 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard18.name, Function82.stackResult.1)).2
wave8_kernel_reduce cost83 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard19.name, Function83.stackResult.1)).2
wave8_kernel_reduce cost84 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard20.name, Function84.stackResult.1)).2
wave8_kernel_reduce cost85 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard21.name, Function85.stackResult.1)).2
wave8_kernel_reduce cost86 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard22.name, Function86.stackResult.1)).2
wave8_kernel_reduce cost87 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard23.name, Function87.stackResult.1)).2
wave8_kernel_reduce cost88 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard24.name, Function88.stackResult.1)).2
wave8_kernel_reduce cost89 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard25.name, Function89.stackResult.1)).2
wave8_kernel_reduce cost90 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard26.name, Function90.stackResult.1)).2
wave8_kernel_reduce cost91 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard27.name, Function91.stackResult.1)).2
wave8_kernel_reduce cost92 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard28.name, Function92.stackResult.1)).2
wave8_kernel_reduce cost93 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard29.name, Function93.stackResult.1)).2
wave8_kernel_reduce cost94 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard30.name, Function94.stackResult.1)).2
wave8_kernel_reduce cost95 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard31.name, Function95.stackResult.1)).2

theorem head80 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard16.name, Function80.stackResult.1)).2 ≤ 7313 := by
  rw [cost80_eq]
  decide

theorem head81 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard17.name, Function81.stackResult.1)).2 ≤ 7313 := by
  rw [cost81_eq]
  decide

theorem head82 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard18.name, Function82.stackResult.1)).2 ≤ 7313 := by
  rw [cost82_eq]
  decide

theorem head83 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard19.name, Function83.stackResult.1)).2 ≤ 7313 := by
  rw [cost83_eq]
  decide

theorem head84 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard20.name, Function84.stackResult.1)).2 ≤ 7313 := by
  rw [cost84_eq]
  decide

theorem head85 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard21.name, Function85.stackResult.1)).2 ≤ 7313 := by
  rw [cost85_eq]
  decide

theorem head86 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard22.name, Function86.stackResult.1)).2 ≤ 7313 := by
  rw [cost86_eq]
  decide

theorem head87 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard23.name, Function87.stackResult.1)).2 ≤ 7313 := by
  rw [cost87_eq]
  decide

theorem head88 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard24.name, Function88.stackResult.1)).2 ≤ 7313 := by
  rw [cost88_eq]
  decide

theorem head89 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard25.name, Function89.stackResult.1)).2 ≤ 7313 := by
  rw [cost89_eq]
  decide

theorem head90 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard26.name, Function90.stackResult.1)).2 ≤ 7313 := by
  rw [cost90_eq]
  decide

theorem head91 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard27.name, Function91.stackResult.1)).2 ≤ 7313 := by
  rw [cost91_eq]
  decide

theorem head92 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard28.name, Function92.stackResult.1)).2 ≤ 7313 := by
  rw [cost92_eq]
  decide

theorem head93 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard29.name, Function93.stackResult.1)).2 ≤ 7313 := by
  rw [cost93_eq]
  decide

theorem head94 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard30.name, Function94.stackResult.1)).2 ≤ 7313 := by
  rw [cost94_eq]
  decide

theorem head95 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard31.name, Function95.stackResult.1)).2 ≤ 7313 := by
  rw [cost95_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk01.bodies := by
  unfold Chunk01.bodies
  apply bounded_cons _ _ _ head80
  apply bounded_cons _ _ _ head81
  apply bounded_cons _ _ _ head82
  apply bounded_cons _ _ _ head83
  apply bounded_cons _ _ _ head84
  apply bounded_cons _ _ _ head85
  apply bounded_cons _ _ _ head86
  apply bounded_cons _ _ _ head87
  apply bounded_cons _ _ _ head88
  apply bounded_cons _ _ _ head89
  apply bounded_cons _ _ _ head90
  apply bounded_cons _ _ _ head91
  apply bounded_cons _ _ _ head92
  apply bounded_cons _ _ _ head93
  apply bounded_cons _ _ _ head94
  apply bounded_cons _ _ _ head95
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded01
