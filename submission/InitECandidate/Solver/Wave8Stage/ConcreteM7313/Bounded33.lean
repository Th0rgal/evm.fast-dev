import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk33
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 64000000
set_option cbv.maxSteps 40000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded33
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackToLabClock LoweredBudget

wave8_certified_reduce cost592 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard528.name, Chunk33.stackResult592.1)).2
wave8_certified_reduce cost593 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard529.name, Chunk33.stackResult593.1)).2
wave8_certified_reduce cost594 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard530.name, Chunk33.stackResult594.1)).2
wave8_certified_reduce cost595 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard531.name, Chunk33.stackResult595.1)).2
wave8_certified_reduce cost596 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard532.name, Chunk33.stackResult596.1)).2
wave8_certified_reduce cost597 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard533.name, Chunk33.stackResult597.1)).2
wave8_certified_reduce cost598 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard534.name, Chunk33.stackResult598.1)).2
wave8_certified_reduce cost599 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard535.name, Chunk33.stackResult599.1)).2
wave8_certified_reduce cost600 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard536.name, Chunk33.stackResult600.1)).2
wave8_certified_reduce cost601 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard537.name, Chunk33.stackResult601.1)).2
wave8_certified_reduce cost602 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard538.name, Chunk33.stackResult602.1)).2
wave8_certified_reduce cost603 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard539.name, Chunk33.stackResult603.1)).2
wave8_certified_reduce cost604 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard540.name, Chunk33.stackResult604.1)).2
wave8_certified_reduce cost605 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard541.name, Chunk33.stackResult605.1)).2
wave8_certified_reduce cost606 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard542.name, Chunk33.stackResult606.1)).2
wave8_certified_reduce cost607 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard543.name, Chunk33.stackResult607.1)).2

theorem head592 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard528.name, Chunk33.stackResult592.1)).2 ≤ 7313 := by
  rw [cost592_eq]
  decide

theorem head593 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard529.name, Chunk33.stackResult593.1)).2 ≤ 7313 := by
  rw [cost593_eq]
  decide

theorem head594 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard530.name, Chunk33.stackResult594.1)).2 ≤ 7313 := by
  rw [cost594_eq]
  decide

theorem head595 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard531.name, Chunk33.stackResult595.1)).2 ≤ 7313 := by
  rw [cost595_eq]
  decide

theorem head596 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard532.name, Chunk33.stackResult596.1)).2 ≤ 7313 := by
  rw [cost596_eq]
  decide

theorem head597 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard533.name, Chunk33.stackResult597.1)).2 ≤ 7313 := by
  rw [cost597_eq]
  decide

theorem head598 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard534.name, Chunk33.stackResult598.1)).2 ≤ 7313 := by
  rw [cost598_eq]
  decide

theorem head599 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard535.name, Chunk33.stackResult599.1)).2 ≤ 7313 := by
  rw [cost599_eq]
  decide

theorem head600 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard536.name, Chunk33.stackResult600.1)).2 ≤ 7313 := by
  rw [cost600_eq]
  decide

theorem head601 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard537.name, Chunk33.stackResult601.1)).2 ≤ 7313 := by
  rw [cost601_eq]
  decide

theorem head602 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard538.name, Chunk33.stackResult602.1)).2 ≤ 7313 := by
  rw [cost602_eq]
  decide

theorem head603 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard539.name, Chunk33.stackResult603.1)).2 ≤ 7313 := by
  rw [cost603_eq]
  decide

theorem head604 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard540.name, Chunk33.stackResult604.1)).2 ≤ 7313 := by
  rw [cost604_eq]
  decide

theorem head605 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard541.name, Chunk33.stackResult605.1)).2 ≤ 7313 := by
  rw [cost605_eq]
  decide

theorem head606 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard542.name, Chunk33.stackResult606.1)).2 ≤ 7313 := by
  rw [cost606_eq]
  decide

theorem head607 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard543.name, Chunk33.stackResult607.1)).2 ≤ 7313 := by
  rw [cost607_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk33.bodies := by
  unfold Chunk33.bodies
  apply bounded_cons _ _ _ head592
  apply bounded_cons _ _ _ head593
  apply bounded_cons _ _ _ head594
  apply bounded_cons _ _ _ head595
  apply bounded_cons _ _ _ head596
  apply bounded_cons _ _ _ head597
  apply bounded_cons _ _ _ head598
  apply bounded_cons _ _ _ head599
  apply bounded_cons _ _ _ head600
  apply bounded_cons _ _ _ head601
  apply bounded_cons _ _ _ head602
  apply bounded_cons _ _ _ head603
  apply bounded_cons _ _ _ head604
  apply bounded_cons _ _ _ head605
  apply bounded_cons _ _ _ head606
  apply bounded_cons _ _ _ head607
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded33
