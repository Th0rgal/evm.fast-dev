import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk00
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded00
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open StackToLabClock LoweredBudget

wave8_kernel_reduce cost64 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard00.name, Function64.stackResult.1)).2
wave8_kernel_reduce cost65 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard01.name, Function65.stackResult.1)).2
wave8_kernel_reduce cost66 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard02.name, Function66.stackResult.1)).2
wave8_kernel_reduce cost67 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard03.name, Function67.stackResult.1)).2
wave8_kernel_reduce cost68 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard04.name, Function68.stackResult.1)).2
wave8_kernel_reduce cost69 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard05.name, Function69.stackResult.1)).2
wave8_kernel_reduce cost70 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard06.name, Function70.stackResult.1)).2
wave8_kernel_reduce cost71 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard07.name, Function71.stackResult.1)).2
wave8_kernel_reduce cost72 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard08.name, Function72.stackResult.1)).2
wave8_kernel_reduce cost73 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard09.name, Function73.stackResult.1)).2
wave8_kernel_reduce cost74 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard10.name, Function74.stackResult.1)).2
wave8_kernel_reduce cost75 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard11.name, Function75.stackResult.1)).2
wave8_kernel_reduce cost76 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard12.name, Function76.stackResult.1)).2
wave8_kernel_reduce cost77 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard13.name, Function77.stackResult.1)).2
wave8_kernel_reduce cost78 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard14.name, Function78.stackResult.1)).2
wave8_kernel_reduce cost79 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard15.name, Function79.stackResult.1)).2

theorem head64 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard00.name, Function64.stackResult.1)).2 ≤ 7313 := by
  rw [cost64_eq]
  decide

theorem head65 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard01.name, Function65.stackResult.1)).2 ≤ 7313 := by
  rw [cost65_eq]
  decide

theorem head66 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard02.name, Function66.stackResult.1)).2 ≤ 7313 := by
  rw [cost66_eq]
  decide

theorem head67 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard03.name, Function67.stackResult.1)).2 ≤ 7313 := by
  rw [cost67_eq]
  decide

theorem head68 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard04.name, Function68.stackResult.1)).2 ≤ 7313 := by
  rw [cost68_eq]
  decide

theorem head69 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard05.name, Function69.stackResult.1)).2 ≤ 7313 := by
  rw [cost69_eq]
  decide

theorem head70 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard06.name, Function70.stackResult.1)).2 ≤ 7313 := by
  rw [cost70_eq]
  decide

theorem head71 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard07.name, Function71.stackResult.1)).2 ≤ 7313 := by
  rw [cost71_eq]
  decide

theorem head72 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard08.name, Function72.stackResult.1)).2 ≤ 7313 := by
  rw [cost72_eq]
  decide

theorem head73 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard09.name, Function73.stackResult.1)).2 ≤ 7313 := by
  rw [cost73_eq]
  decide

theorem head74 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard10.name, Function74.stackResult.1)).2 ≤ 7313 := by
  rw [cost74_eq]
  decide

theorem head75 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard11.name, Function75.stackResult.1)).2 ≤ 7313 := by
  rw [cost75_eq]
  decide

theorem head76 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard12.name, Function76.stackResult.1)).2 ≤ 7313 := by
  rw [cost76_eq]
  decide

theorem head77 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard13.name, Function77.stackResult.1)).2 ≤ 7313 := by
  rw [cost77_eq]
  decide

theorem head78 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard14.name, Function78.stackResult.1)).2 ≤ 7313 := by
  rw [cost78_eq]
  decide

theorem head79 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard15.name, Function79.stackResult.1)).2 ≤ 7313 := by
  rw [cost79_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk00.bodies := by
  unfold Chunk00.bodies
  apply bounded_cons _ _ _ head64
  apply bounded_cons _ _ _ head65
  apply bounded_cons _ _ _ head66
  apply bounded_cons _ _ _ head67
  apply bounded_cons _ _ _ head68
  apply bounded_cons _ _ _ head69
  apply bounded_cons _ _ _ head70
  apply bounded_cons _ _ _ head71
  apply bounded_cons _ _ _ head72
  apply bounded_cons _ _ _ head73
  apply bounded_cons _ _ _ head74
  apply bounded_cons _ _ _ head75
  apply bounded_cons _ _ _ head76
  apply bounded_cons _ _ _ head77
  apply bounded_cons _ _ _ head78
  apply bounded_cons _ _ _ head79
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded00
