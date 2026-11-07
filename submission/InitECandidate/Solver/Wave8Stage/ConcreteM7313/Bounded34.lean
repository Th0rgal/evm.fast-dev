import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk34
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded34
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open StackToLabClock LoweredBudget

wave8_kernel_reduce cost608 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard544.name, Chunk34.stackResult608.1)).2
wave8_kernel_reduce cost609 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard545.name, Chunk34.stackResult609.1)).2
wave8_kernel_reduce cost610 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard546.name, Chunk34.stackResult610.1)).2
wave8_kernel_reduce cost611 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard547.name, Chunk34.stackResult611.1)).2
wave8_kernel_reduce cost612 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard548.name, Chunk34.stackResult612.1)).2
wave8_kernel_reduce cost613 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard549.name, Chunk34.stackResult613.1)).2
wave8_kernel_reduce cost614 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard550.name, Chunk34.stackResult614.1)).2
wave8_kernel_reduce cost615 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard551.name, Chunk34.stackResult615.1)).2
wave8_kernel_reduce cost616 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard552.name, Chunk34.stackResult616.1)).2
wave8_kernel_reduce cost617 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard553.name, Chunk34.stackResult617.1)).2
wave8_kernel_reduce cost618 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard554.name, Chunk34.stackResult618.1)).2
wave8_kernel_reduce cost619 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard555.name, Chunk34.stackResult619.1)).2
wave8_kernel_reduce cost620 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard556.name, Chunk34.stackResult620.1)).2
wave8_kernel_reduce cost621 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard557.name, Chunk34.stackResult621.1)).2
wave8_kernel_reduce cost622 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard558.name, Chunk34.stackResult622.1)).2
wave8_kernel_reduce cost623 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard559.name, Chunk34.stackResult623.1)).2

theorem head608 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard544.name, Chunk34.stackResult608.1)).2 ≤ 7313 := by
  rw [cost608_eq]
  decide

theorem head609 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard545.name, Chunk34.stackResult609.1)).2 ≤ 7313 := by
  rw [cost609_eq]
  decide

theorem head610 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard546.name, Chunk34.stackResult610.1)).2 ≤ 7313 := by
  rw [cost610_eq]
  decide

theorem head611 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard547.name, Chunk34.stackResult611.1)).2 ≤ 7313 := by
  rw [cost611_eq]
  decide

theorem head612 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard548.name, Chunk34.stackResult612.1)).2 ≤ 7313 := by
  rw [cost612_eq]
  decide

theorem head613 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard549.name, Chunk34.stackResult613.1)).2 ≤ 7313 := by
  rw [cost613_eq]
  decide

theorem head614 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard550.name, Chunk34.stackResult614.1)).2 ≤ 7313 := by
  rw [cost614_eq]
  decide

theorem head615 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard551.name, Chunk34.stackResult615.1)).2 ≤ 7313 := by
  rw [cost615_eq]
  decide

theorem head616 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard552.name, Chunk34.stackResult616.1)).2 ≤ 7313 := by
  rw [cost616_eq]
  decide

theorem head617 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard553.name, Chunk34.stackResult617.1)).2 ≤ 7313 := by
  rw [cost617_eq]
  decide

theorem head618 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard554.name, Chunk34.stackResult618.1)).2 ≤ 7313 := by
  rw [cost618_eq]
  decide

theorem head619 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard555.name, Chunk34.stackResult619.1)).2 ≤ 7313 := by
  rw [cost619_eq]
  decide

theorem head620 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard556.name, Chunk34.stackResult620.1)).2 ≤ 7313 := by
  rw [cost620_eq]
  decide

theorem head621 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard557.name, Chunk34.stackResult621.1)).2 ≤ 7313 := by
  rw [cost621_eq]
  decide

theorem head622 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard558.name, Chunk34.stackResult622.1)).2 ≤ 7313 := by
  rw [cost622_eq]
  decide

theorem head623 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard559.name, Chunk34.stackResult623.1)).2 ≤ 7313 := by
  rw [cost623_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk34.bodies := by
  unfold Chunk34.bodies
  apply bounded_cons _ _ _ head608
  apply bounded_cons _ _ _ head609
  apply bounded_cons _ _ _ head610
  apply bounded_cons _ _ _ head611
  apply bounded_cons _ _ _ head612
  apply bounded_cons _ _ _ head613
  apply bounded_cons _ _ _ head614
  apply bounded_cons _ _ _ head615
  apply bounded_cons _ _ _ head616
  apply bounded_cons _ _ _ head617
  apply bounded_cons _ _ _ head618
  apply bounded_cons _ _ _ head619
  apply bounded_cons _ _ _ head620
  apply bounded_cons _ _ _ head621
  apply bounded_cons _ _ _ head622
  apply bounded_cons _ _ _ head623
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded34
