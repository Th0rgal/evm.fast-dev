import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk31
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 64000000
set_option cbv.maxSteps 40000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded31
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackToLabClock LoweredBudget

wave8_certified_reduce cost560 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard496.name, Chunk31.stackResult560.1)).2
wave8_certified_reduce cost561 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard497.name, Chunk31.stackResult561.1)).2
wave8_certified_reduce cost562 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard498.name, Chunk31.stackResult562.1)).2
wave8_certified_reduce cost563 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard499.name, Chunk31.stackResult563.1)).2
wave8_certified_reduce cost564 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard500.name, Chunk31.stackResult564.1)).2
wave8_certified_reduce cost565 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard501.name, Chunk31.stackResult565.1)).2
wave8_certified_reduce cost566 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard502.name, Chunk31.stackResult566.1)).2
wave8_certified_reduce cost567 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard503.name, Chunk31.stackResult567.1)).2
wave8_certified_reduce cost568 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard504.name, Chunk31.stackResult568.1)).2
wave8_certified_reduce cost569 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard505.name, Chunk31.stackResult569.1)).2
wave8_certified_reduce cost570 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard506.name, Chunk31.stackResult570.1)).2
wave8_certified_reduce cost571 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard507.name, Chunk31.stackResult571.1)).2
wave8_certified_reduce cost572 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard508.name, Chunk31.stackResult572.1)).2
wave8_certified_reduce cost573 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard509.name, Chunk31.stackResult573.1)).2
wave8_certified_reduce cost574 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard510.name, Chunk31.stackResult574.1)).2
wave8_certified_reduce cost575 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard511.name, Chunk31.stackResult575.1)).2

theorem head560 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard496.name, Chunk31.stackResult560.1)).2 ≤ 7313 := by
  rw [cost560_eq]
  decide

theorem head561 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard497.name, Chunk31.stackResult561.1)).2 ≤ 7313 := by
  rw [cost561_eq]
  decide

theorem head562 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard498.name, Chunk31.stackResult562.1)).2 ≤ 7313 := by
  rw [cost562_eq]
  decide

theorem head563 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard499.name, Chunk31.stackResult563.1)).2 ≤ 7313 := by
  rw [cost563_eq]
  decide

theorem head564 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard500.name, Chunk31.stackResult564.1)).2 ≤ 7313 := by
  rw [cost564_eq]
  decide

theorem head565 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard501.name, Chunk31.stackResult565.1)).2 ≤ 7313 := by
  rw [cost565_eq]
  decide

theorem head566 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard502.name, Chunk31.stackResult566.1)).2 ≤ 7313 := by
  rw [cost566_eq]
  decide

theorem head567 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard503.name, Chunk31.stackResult567.1)).2 ≤ 7313 := by
  rw [cost567_eq]
  decide

theorem head568 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard504.name, Chunk31.stackResult568.1)).2 ≤ 7313 := by
  rw [cost568_eq]
  decide

theorem head569 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard505.name, Chunk31.stackResult569.1)).2 ≤ 7313 := by
  rw [cost569_eq]
  decide

theorem head570 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard506.name, Chunk31.stackResult570.1)).2 ≤ 7313 := by
  rw [cost570_eq]
  decide

theorem head571 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard507.name, Chunk31.stackResult571.1)).2 ≤ 7313 := by
  rw [cost571_eq]
  decide

theorem head572 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard508.name, Chunk31.stackResult572.1)).2 ≤ 7313 := by
  rw [cost572_eq]
  decide

theorem head573 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard509.name, Chunk31.stackResult573.1)).2 ≤ 7313 := by
  rw [cost573_eq]
  decide

theorem head574 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard510.name, Chunk31.stackResult574.1)).2 ≤ 7313 := by
  rw [cost574_eq]
  decide

theorem head575 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard511.name, Chunk31.stackResult575.1)).2 ≤ 7313 := by
  rw [cost575_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk31.bodies := by
  unfold Chunk31.bodies
  apply bounded_cons _ _ _ head560
  apply bounded_cons _ _ _ head561
  apply bounded_cons _ _ _ head562
  apply bounded_cons _ _ _ head563
  apply bounded_cons _ _ _ head564
  apply bounded_cons _ _ _ head565
  apply bounded_cons _ _ _ head566
  apply bounded_cons _ _ _ head567
  apply bounded_cons _ _ _ head568
  apply bounded_cons _ _ _ head569
  apply bounded_cons _ _ _ head570
  apply bounded_cons _ _ _ head571
  apply bounded_cons _ _ _ head572
  apply bounded_cons _ _ _ head573
  apply bounded_cons _ _ _ head574
  apply bounded_cons _ _ _ head575
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded31
