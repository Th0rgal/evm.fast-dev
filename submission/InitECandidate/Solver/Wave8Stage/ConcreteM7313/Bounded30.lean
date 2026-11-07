import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk30
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 64000000
set_option cbv.maxSteps 40000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded30
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackToLabClock LoweredBudget

wave8_certified_reduce cost544 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard480.name, Chunk30.stackResult544.1)).2
wave8_certified_reduce cost545 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard481.name, Chunk30.stackResult545.1)).2
wave8_certified_reduce cost546 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard482.name, Chunk30.stackResult546.1)).2
wave8_certified_reduce cost547 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard483.name, Chunk30.stackResult547.1)).2
wave8_certified_reduce cost548 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard484.name, Chunk30.stackResult548.1)).2
wave8_certified_reduce cost549 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard485.name, Chunk30.stackResult549.1)).2
wave8_certified_reduce cost550 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard486.name, Chunk30.stackResult550.1)).2
wave8_certified_reduce cost551 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard487.name, Chunk30.stackResult551.1)).2
wave8_certified_reduce cost552 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard488.name, Chunk30.stackResult552.1)).2
wave8_certified_reduce cost553 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard489.name, Chunk30.stackResult553.1)).2
wave8_certified_reduce cost554 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard490.name, Chunk30.stackResult554.1)).2
wave8_certified_reduce cost555 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard491.name, Chunk30.stackResult555.1)).2
wave8_certified_reduce cost556 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard492.name, Chunk30.stackResult556.1)).2
wave8_certified_reduce cost557 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard493.name, Chunk30.stackResult557.1)).2
wave8_certified_reduce cost558 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard494.name, Chunk30.stackResult558.1)).2
wave8_certified_reduce cost559 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard495.name, Chunk30.stackResult559.1)).2

theorem head544 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard480.name, Chunk30.stackResult544.1)).2 ≤ 7313 := by
  rw [cost544_eq]
  decide

theorem head545 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard481.name, Chunk30.stackResult545.1)).2 ≤ 7313 := by
  rw [cost545_eq]
  decide

theorem head546 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard482.name, Chunk30.stackResult546.1)).2 ≤ 7313 := by
  rw [cost546_eq]
  decide

theorem head547 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard483.name, Chunk30.stackResult547.1)).2 ≤ 7313 := by
  rw [cost547_eq]
  decide

theorem head548 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard484.name, Chunk30.stackResult548.1)).2 ≤ 7313 := by
  rw [cost548_eq]
  decide

theorem head549 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard485.name, Chunk30.stackResult549.1)).2 ≤ 7313 := by
  rw [cost549_eq]
  decide

theorem head550 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard486.name, Chunk30.stackResult550.1)).2 ≤ 7313 := by
  rw [cost550_eq]
  decide

theorem head551 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard487.name, Chunk30.stackResult551.1)).2 ≤ 7313 := by
  rw [cost551_eq]
  decide

theorem head552 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard488.name, Chunk30.stackResult552.1)).2 ≤ 7313 := by
  rw [cost552_eq]
  decide

theorem head553 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard489.name, Chunk30.stackResult553.1)).2 ≤ 7313 := by
  rw [cost553_eq]
  decide

theorem head554 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard490.name, Chunk30.stackResult554.1)).2 ≤ 7313 := by
  rw [cost554_eq]
  decide

theorem head555 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard491.name, Chunk30.stackResult555.1)).2 ≤ 7313 := by
  rw [cost555_eq]
  decide

theorem head556 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard492.name, Chunk30.stackResult556.1)).2 ≤ 7313 := by
  rw [cost556_eq]
  decide

theorem head557 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard493.name, Chunk30.stackResult557.1)).2 ≤ 7313 := by
  rw [cost557_eq]
  decide

theorem head558 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard494.name, Chunk30.stackResult558.1)).2 ≤ 7313 := by
  rw [cost558_eq]
  decide

theorem head559 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard495.name, Chunk30.stackResult559.1)).2 ≤ 7313 := by
  rw [cost559_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk30.bodies := by
  unfold Chunk30.bodies
  apply bounded_cons _ _ _ head544
  apply bounded_cons _ _ _ head545
  apply bounded_cons _ _ _ head546
  apply bounded_cons _ _ _ head547
  apply bounded_cons _ _ _ head548
  apply bounded_cons _ _ _ head549
  apply bounded_cons _ _ _ head550
  apply bounded_cons _ _ _ head551
  apply bounded_cons _ _ _ head552
  apply bounded_cons _ _ _ head553
  apply bounded_cons _ _ _ head554
  apply bounded_cons _ _ _ head555
  apply bounded_cons _ _ _ head556
  apply bounded_cons _ _ _ head557
  apply bounded_cons _ _ _ head558
  apply bounded_cons _ _ _ head559
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded30
