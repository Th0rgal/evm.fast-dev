import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk16
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded16
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open StackToLabClock LoweredBudget

wave8_kernel_reduce cost320 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard256.name, Chunk16.stackResult320.1)).2
wave8_kernel_reduce cost321 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard257.name, Chunk16.stackResult321.1)).2
wave8_kernel_reduce cost322 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard258.name, Chunk16.stackResult322.1)).2
wave8_kernel_reduce cost323 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard259.name, Chunk16.stackResult323.1)).2
wave8_kernel_reduce cost324 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard260.name, Chunk16.stackResult324.1)).2
wave8_kernel_reduce cost325 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard261.name, Chunk16.stackResult325.1)).2
wave8_kernel_reduce cost326 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard262.name, Chunk16.stackResult326.1)).2
wave8_kernel_reduce cost327 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard263.name, Chunk16.stackResult327.1)).2
wave8_kernel_reduce cost328 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard264.name, Chunk16.stackResult328.1)).2
wave8_kernel_reduce cost329 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard265.name, Chunk16.stackResult329.1)).2
wave8_kernel_reduce cost330 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard266.name, Chunk16.stackResult330.1)).2
wave8_kernel_reduce cost331 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard267.name, Chunk16.stackResult331.1)).2
wave8_kernel_reduce cost332 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard268.name, Chunk16.stackResult332.1)).2
wave8_kernel_reduce cost333 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard269.name, Chunk16.stackResult333.1)).2
wave8_kernel_reduce cost334 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard270.name, Chunk16.stackResult334.1)).2
wave8_kernel_reduce cost335 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard271.name, Chunk16.stackResult335.1)).2

theorem head320 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard256.name, Chunk16.stackResult320.1)).2 ≤ 7313 := by
  rw [cost320_eq]
  decide

theorem head321 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard257.name, Chunk16.stackResult321.1)).2 ≤ 7313 := by
  rw [cost321_eq]
  decide

theorem head322 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard258.name, Chunk16.stackResult322.1)).2 ≤ 7313 := by
  rw [cost322_eq]
  decide

theorem head323 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard259.name, Chunk16.stackResult323.1)).2 ≤ 7313 := by
  rw [cost323_eq]
  decide

theorem head324 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard260.name, Chunk16.stackResult324.1)).2 ≤ 7313 := by
  rw [cost324_eq]
  decide

theorem head325 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard261.name, Chunk16.stackResult325.1)).2 ≤ 7313 := by
  rw [cost325_eq]
  decide

theorem head326 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard262.name, Chunk16.stackResult326.1)).2 ≤ 7313 := by
  rw [cost326_eq]
  decide

theorem head327 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard263.name, Chunk16.stackResult327.1)).2 ≤ 7313 := by
  rw [cost327_eq]
  decide

theorem head328 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard264.name, Chunk16.stackResult328.1)).2 ≤ 7313 := by
  rw [cost328_eq]
  decide

theorem head329 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard265.name, Chunk16.stackResult329.1)).2 ≤ 7313 := by
  rw [cost329_eq]
  decide

theorem head330 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard266.name, Chunk16.stackResult330.1)).2 ≤ 7313 := by
  rw [cost330_eq]
  decide

theorem head331 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard267.name, Chunk16.stackResult331.1)).2 ≤ 7313 := by
  rw [cost331_eq]
  decide

theorem head332 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard268.name, Chunk16.stackResult332.1)).2 ≤ 7313 := by
  rw [cost332_eq]
  decide

theorem head333 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard269.name, Chunk16.stackResult333.1)).2 ≤ 7313 := by
  rw [cost333_eq]
  decide

theorem head334 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard270.name, Chunk16.stackResult334.1)).2 ≤ 7313 := by
  rw [cost334_eq]
  decide

theorem head335 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard271.name, Chunk16.stackResult335.1)).2 ≤ 7313 := by
  rw [cost335_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk16.bodies := by
  unfold Chunk16.bodies
  apply bounded_cons _ _ _ head320
  apply bounded_cons _ _ _ head321
  apply bounded_cons _ _ _ head322
  apply bounded_cons _ _ _ head323
  apply bounded_cons _ _ _ head324
  apply bounded_cons _ _ _ head325
  apply bounded_cons _ _ _ head326
  apply bounded_cons _ _ _ head327
  apply bounded_cons _ _ _ head328
  apply bounded_cons _ _ _ head329
  apply bounded_cons _ _ _ head330
  apply bounded_cons _ _ _ head331
  apply bounded_cons _ _ _ head332
  apply bounded_cons _ _ _ head333
  apply bounded_cons _ _ _ head334
  apply bounded_cons _ _ _ head335
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded16
