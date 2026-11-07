import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk50
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 64000000
set_option cbv.maxSteps 40000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded50
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackToLabClock LoweredBudget

wave8_certified_reduce cost864 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard800.name, Chunk50.stackResult864.1)).2
wave8_certified_reduce cost865 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard801.name, Chunk50.stackResult865.1)).2
wave8_certified_reduce cost866 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard802.name, Chunk50.stackResult866.1)).2
wave8_certified_reduce cost867 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard803.name, Chunk50.stackResult867.1)).2
wave8_certified_reduce cost868 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard804.name, Chunk50.stackResult868.1)).2
wave8_certified_reduce cost869 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard805.name, Chunk50.stackResult869.1)).2
wave8_certified_reduce cost870 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard806.name, Chunk50.stackResult870.1)).2
wave8_certified_reduce cost871 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard807.name, Chunk50.stackResult871.1)).2
wave8_certified_reduce cost872 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard808.name, Chunk50.stackResult872.1)).2
wave8_certified_reduce cost873 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard809.name, Chunk50.stackResult873.1)).2
wave8_certified_reduce cost874 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard810.name, Chunk50.stackResult874.1)).2
wave8_certified_reduce cost875 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard811.name, Chunk50.stackResult875.1)).2
wave8_certified_reduce cost876 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard812.name, Chunk50.stackResult876.1)).2
wave8_certified_reduce cost877 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard813.name, Chunk50.stackResult877.1)).2

theorem head864 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard800.name, Chunk50.stackResult864.1)).2 ≤ 7313 := by
  rw [cost864_eq]
  decide

theorem head865 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard801.name, Chunk50.stackResult865.1)).2 ≤ 7313 := by
  rw [cost865_eq]
  decide

theorem head866 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard802.name, Chunk50.stackResult866.1)).2 ≤ 7313 := by
  rw [cost866_eq]
  decide

theorem head867 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard803.name, Chunk50.stackResult867.1)).2 ≤ 7313 := by
  rw [cost867_eq]
  decide

theorem head868 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard804.name, Chunk50.stackResult868.1)).2 ≤ 7313 := by
  rw [cost868_eq]
  decide

theorem head869 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard805.name, Chunk50.stackResult869.1)).2 ≤ 7313 := by
  rw [cost869_eq]
  decide

theorem head870 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard806.name, Chunk50.stackResult870.1)).2 ≤ 7313 := by
  rw [cost870_eq]
  decide

theorem head871 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard807.name, Chunk50.stackResult871.1)).2 ≤ 7313 := by
  rw [cost871_eq]
  decide

theorem head872 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard808.name, Chunk50.stackResult872.1)).2 ≤ 7313 := by
  rw [cost872_eq]
  decide

theorem head873 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard809.name, Chunk50.stackResult873.1)).2 ≤ 7313 := by
  rw [cost873_eq]
  decide

theorem head874 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard810.name, Chunk50.stackResult874.1)).2 ≤ 7313 := by
  rw [cost874_eq]
  decide

theorem head875 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard811.name, Chunk50.stackResult875.1)).2 ≤ 7313 := by
  rw [cost875_eq]
  decide

theorem head876 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard812.name, Chunk50.stackResult876.1)).2 ≤ 7313 := by
  rw [cost876_eq]
  decide

theorem head877 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard813.name, Chunk50.stackResult877.1)).2 ≤ 7313 := by
  rw [cost877_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk50.bodies := by
  unfold Chunk50.bodies
  apply bounded_cons _ _ _ head864
  apply bounded_cons _ _ _ head865
  apply bounded_cons _ _ _ head866
  apply bounded_cons _ _ _ head867
  apply bounded_cons _ _ _ head868
  apply bounded_cons _ _ _ head869
  apply bounded_cons _ _ _ head870
  apply bounded_cons _ _ _ head871
  apply bounded_cons _ _ _ head872
  apply bounded_cons _ _ _ head873
  apply bounded_cons _ _ _ head874
  apply bounded_cons _ _ _ head875
  apply bounded_cons _ _ _ head876
  apply bounded_cons _ _ _ head877
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded50
