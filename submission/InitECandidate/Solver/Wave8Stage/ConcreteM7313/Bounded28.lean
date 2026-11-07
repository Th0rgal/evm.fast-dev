import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk28
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 64000000
set_option cbv.maxSteps 40000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded28
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackToLabClock LoweredBudget

wave8_certified_reduce cost512 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard448.name, Chunk28.stackResult512.1)).2
wave8_certified_reduce cost513 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard449.name, Chunk28.stackResult513.1)).2
wave8_certified_reduce cost514 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard450.name, Chunk28.stackResult514.1)).2
wave8_certified_reduce cost515 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard451.name, Chunk28.stackResult515.1)).2
wave8_certified_reduce cost516 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard452.name, Chunk28.stackResult516.1)).2
wave8_certified_reduce cost517 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard453.name, Chunk28.stackResult517.1)).2
wave8_certified_reduce cost518 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard454.name, Chunk28.stackResult518.1)).2
wave8_certified_reduce cost519 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard455.name, Chunk28.stackResult519.1)).2
wave8_certified_reduce cost520 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard456.name, Chunk28.stackResult520.1)).2
wave8_certified_reduce cost521 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard457.name, Chunk28.stackResult521.1)).2
wave8_certified_reduce cost522 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard458.name, Chunk28.stackResult522.1)).2
wave8_certified_reduce cost523 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard459.name, Chunk28.stackResult523.1)).2
wave8_certified_reduce cost524 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard460.name, Chunk28.stackResult524.1)).2
wave8_certified_reduce cost525 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard461.name, Chunk28.stackResult525.1)).2
wave8_certified_reduce cost526 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard462.name, Chunk28.stackResult526.1)).2
wave8_certified_reduce cost527 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard463.name, Chunk28.stackResult527.1)).2

theorem head512 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard448.name, Chunk28.stackResult512.1)).2 ≤ 7313 := by
  rw [cost512_eq]
  decide

theorem head513 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard449.name, Chunk28.stackResult513.1)).2 ≤ 7313 := by
  rw [cost513_eq]
  decide

theorem head514 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard450.name, Chunk28.stackResult514.1)).2 ≤ 7313 := by
  rw [cost514_eq]
  decide

theorem head515 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard451.name, Chunk28.stackResult515.1)).2 ≤ 7313 := by
  rw [cost515_eq]
  decide

theorem head516 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard452.name, Chunk28.stackResult516.1)).2 ≤ 7313 := by
  rw [cost516_eq]
  decide

theorem head517 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard453.name, Chunk28.stackResult517.1)).2 ≤ 7313 := by
  rw [cost517_eq]
  decide

theorem head518 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard454.name, Chunk28.stackResult518.1)).2 ≤ 7313 := by
  rw [cost518_eq]
  decide

theorem head519 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard455.name, Chunk28.stackResult519.1)).2 ≤ 7313 := by
  rw [cost519_eq]
  decide

theorem head520 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard456.name, Chunk28.stackResult520.1)).2 ≤ 7313 := by
  rw [cost520_eq]
  decide

theorem head521 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard457.name, Chunk28.stackResult521.1)).2 ≤ 7313 := by
  rw [cost521_eq]
  decide

theorem head522 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard458.name, Chunk28.stackResult522.1)).2 ≤ 7313 := by
  rw [cost522_eq]
  decide

theorem head523 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard459.name, Chunk28.stackResult523.1)).2 ≤ 7313 := by
  rw [cost523_eq]
  decide

theorem head524 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard460.name, Chunk28.stackResult524.1)).2 ≤ 7313 := by
  rw [cost524_eq]
  decide

theorem head525 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard461.name, Chunk28.stackResult525.1)).2 ≤ 7313 := by
  rw [cost525_eq]
  decide

theorem head526 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard462.name, Chunk28.stackResult526.1)).2 ≤ 7313 := by
  rw [cost526_eq]
  decide

theorem head527 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard463.name, Chunk28.stackResult527.1)).2 ≤ 7313 := by
  rw [cost527_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk28.bodies := by
  unfold Chunk28.bodies
  apply bounded_cons _ _ _ head512
  apply bounded_cons _ _ _ head513
  apply bounded_cons _ _ _ head514
  apply bounded_cons _ _ _ head515
  apply bounded_cons _ _ _ head516
  apply bounded_cons _ _ _ head517
  apply bounded_cons _ _ _ head518
  apply bounded_cons _ _ _ head519
  apply bounded_cons _ _ _ head520
  apply bounded_cons _ _ _ head521
  apply bounded_cons _ _ _ head522
  apply bounded_cons _ _ _ head523
  apply bounded_cons _ _ _ head524
  apply bounded_cons _ _ _ head525
  apply bounded_cons _ _ _ head526
  apply bounded_cons _ _ _ head527
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded28
