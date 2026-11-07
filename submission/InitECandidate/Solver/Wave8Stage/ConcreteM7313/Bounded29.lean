import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk29
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 64000000
set_option cbv.maxSteps 40000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded29
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackToLabClock LoweredBudget

wave8_certified_reduce cost528 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard464.name, Chunk29.stackResult528.1)).2
wave8_certified_reduce cost529 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard465.name, Chunk29.stackResult529.1)).2
wave8_certified_reduce cost530 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard466.name, Chunk29.stackResult530.1)).2
wave8_certified_reduce cost531 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard467.name, Chunk29.stackResult531.1)).2
wave8_certified_reduce cost532 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard468.name, Chunk29.stackResult532.1)).2
wave8_certified_reduce cost533 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard469.name, Chunk29.stackResult533.1)).2
wave8_certified_reduce cost534 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard470.name, Chunk29.stackResult534.1)).2
wave8_certified_reduce cost535 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard471.name, Chunk29.stackResult535.1)).2
wave8_certified_reduce cost536 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard472.name, Chunk29.stackResult536.1)).2
wave8_certified_reduce cost537 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard473.name, Chunk29.stackResult537.1)).2
wave8_certified_reduce cost538 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard474.name, Chunk29.stackResult538.1)).2
wave8_certified_reduce cost539 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard475.name, Chunk29.stackResult539.1)).2
wave8_certified_reduce cost540 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard476.name, Chunk29.stackResult540.1)).2
wave8_certified_reduce cost541 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard477.name, Chunk29.stackResult541.1)).2
wave8_certified_reduce cost542 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard478.name, Chunk29.stackResult542.1)).2
wave8_certified_reduce cost543 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard479.name, Chunk29.stackResult543.1)).2

theorem head528 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard464.name, Chunk29.stackResult528.1)).2 ≤ 7313 := by
  rw [cost528_eq]
  decide

theorem head529 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard465.name, Chunk29.stackResult529.1)).2 ≤ 7313 := by
  rw [cost529_eq]
  decide

theorem head530 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard466.name, Chunk29.stackResult530.1)).2 ≤ 7313 := by
  rw [cost530_eq]
  decide

theorem head531 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard467.name, Chunk29.stackResult531.1)).2 ≤ 7313 := by
  rw [cost531_eq]
  decide

theorem head532 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard468.name, Chunk29.stackResult532.1)).2 ≤ 7313 := by
  rw [cost532_eq]
  decide

theorem head533 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard469.name, Chunk29.stackResult533.1)).2 ≤ 7313 := by
  rw [cost533_eq]
  decide

theorem head534 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard470.name, Chunk29.stackResult534.1)).2 ≤ 7313 := by
  rw [cost534_eq]
  decide

theorem head535 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard471.name, Chunk29.stackResult535.1)).2 ≤ 7313 := by
  rw [cost535_eq]
  decide

theorem head536 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard472.name, Chunk29.stackResult536.1)).2 ≤ 7313 := by
  rw [cost536_eq]
  decide

theorem head537 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard473.name, Chunk29.stackResult537.1)).2 ≤ 7313 := by
  rw [cost537_eq]
  decide

theorem head538 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard474.name, Chunk29.stackResult538.1)).2 ≤ 7313 := by
  rw [cost538_eq]
  decide

theorem head539 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard475.name, Chunk29.stackResult539.1)).2 ≤ 7313 := by
  rw [cost539_eq]
  decide

theorem head540 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard476.name, Chunk29.stackResult540.1)).2 ≤ 7313 := by
  rw [cost540_eq]
  decide

theorem head541 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard477.name, Chunk29.stackResult541.1)).2 ≤ 7313 := by
  rw [cost541_eq]
  decide

theorem head542 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard478.name, Chunk29.stackResult542.1)).2 ≤ 7313 := by
  rw [cost542_eq]
  decide

theorem head543 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard479.name, Chunk29.stackResult543.1)).2 ≤ 7313 := by
  rw [cost543_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk29.bodies := by
  unfold Chunk29.bodies
  apply bounded_cons _ _ _ head528
  apply bounded_cons _ _ _ head529
  apply bounded_cons _ _ _ head530
  apply bounded_cons _ _ _ head531
  apply bounded_cons _ _ _ head532
  apply bounded_cons _ _ _ head533
  apply bounded_cons _ _ _ head534
  apply bounded_cons _ _ _ head535
  apply bounded_cons _ _ _ head536
  apply bounded_cons _ _ _ head537
  apply bounded_cons _ _ _ head538
  apply bounded_cons _ _ _ head539
  apply bounded_cons _ _ _ head540
  apply bounded_cons _ _ _ head541
  apply bounded_cons _ _ _ head542
  apply bounded_cons _ _ _ head543
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded29
