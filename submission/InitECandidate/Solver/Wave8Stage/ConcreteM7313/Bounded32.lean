import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk32
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 64000000
set_option cbv.maxSteps 40000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded32
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackToLabClock LoweredBudget

wave8_certified_reduce cost576 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard512.name, Chunk32.stackResult576.1)).2
wave8_certified_reduce cost577 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard513.name, Chunk32.stackResult577.1)).2
wave8_certified_reduce cost578 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard514.name, Chunk32.stackResult578.1)).2
wave8_certified_reduce cost579 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard515.name, Chunk32.stackResult579.1)).2
wave8_certified_reduce cost580 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard516.name, Chunk32.stackResult580.1)).2
wave8_certified_reduce cost581 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard517.name, Chunk32.stackResult581.1)).2
wave8_certified_reduce cost582 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard518.name, Chunk32.stackResult582.1)).2
wave8_certified_reduce cost583 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard519.name, Chunk32.stackResult583.1)).2
wave8_certified_reduce cost584 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard520.name, Chunk32.stackResult584.1)).2
wave8_certified_reduce cost585 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard521.name, Chunk32.stackResult585.1)).2
wave8_certified_reduce cost586 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard522.name, Chunk32.stackResult586.1)).2
wave8_certified_reduce cost587 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard523.name, Chunk32.stackResult587.1)).2
wave8_certified_reduce cost588 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard524.name, Chunk32.stackResult588.1)).2
wave8_certified_reduce cost589 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard525.name, Chunk32.stackResult589.1)).2
wave8_certified_reduce cost590 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard526.name, Chunk32.stackResult590.1)).2
wave8_certified_reduce cost591 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard527.name, Chunk32.stackResult591.1)).2

theorem head576 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard512.name, Chunk32.stackResult576.1)).2 ≤ 7313 := by
  rw [cost576_eq]
  decide

theorem head577 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard513.name, Chunk32.stackResult577.1)).2 ≤ 7313 := by
  rw [cost577_eq]
  decide

theorem head578 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard514.name, Chunk32.stackResult578.1)).2 ≤ 7313 := by
  rw [cost578_eq]
  decide

theorem head579 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard515.name, Chunk32.stackResult579.1)).2 ≤ 7313 := by
  rw [cost579_eq]
  decide

theorem head580 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard516.name, Chunk32.stackResult580.1)).2 ≤ 7313 := by
  rw [cost580_eq]
  decide

theorem head581 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard517.name, Chunk32.stackResult581.1)).2 ≤ 7313 := by
  rw [cost581_eq]
  decide

theorem head582 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard518.name, Chunk32.stackResult582.1)).2 ≤ 7313 := by
  rw [cost582_eq]
  decide

theorem head583 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard519.name, Chunk32.stackResult583.1)).2 ≤ 7313 := by
  rw [cost583_eq]
  decide

theorem head584 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard520.name, Chunk32.stackResult584.1)).2 ≤ 7313 := by
  rw [cost584_eq]
  decide

theorem head585 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard521.name, Chunk32.stackResult585.1)).2 ≤ 7313 := by
  rw [cost585_eq]
  decide

theorem head586 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard522.name, Chunk32.stackResult586.1)).2 ≤ 7313 := by
  rw [cost586_eq]
  decide

theorem head587 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard523.name, Chunk32.stackResult587.1)).2 ≤ 7313 := by
  rw [cost587_eq]
  decide

theorem head588 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard524.name, Chunk32.stackResult588.1)).2 ≤ 7313 := by
  rw [cost588_eq]
  decide

theorem head589 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard525.name, Chunk32.stackResult589.1)).2 ≤ 7313 := by
  rw [cost589_eq]
  decide

theorem head590 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard526.name, Chunk32.stackResult590.1)).2 ≤ 7313 := by
  rw [cost590_eq]
  decide

theorem head591 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard527.name, Chunk32.stackResult591.1)).2 ≤ 7313 := by
  rw [cost591_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk32.bodies := by
  unfold Chunk32.bodies
  apply bounded_cons _ _ _ head576
  apply bounded_cons _ _ _ head577
  apply bounded_cons _ _ _ head578
  apply bounded_cons _ _ _ head579
  apply bounded_cons _ _ _ head580
  apply bounded_cons _ _ _ head581
  apply bounded_cons _ _ _ head582
  apply bounded_cons _ _ _ head583
  apply bounded_cons _ _ _ head584
  apply bounded_cons _ _ _ head585
  apply bounded_cons _ _ _ head586
  apply bounded_cons _ _ _ head587
  apply bounded_cons _ _ _ head588
  apply bounded_cons _ _ _ head589
  apply bounded_cons _ _ _ head590
  apply bounded_cons _ _ _ head591
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded32
