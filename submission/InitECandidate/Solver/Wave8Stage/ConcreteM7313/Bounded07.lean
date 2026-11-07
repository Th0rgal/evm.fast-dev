import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk07
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded07
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open StackToLabClock LoweredBudget

wave8_kernel_reduce cost176 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard112.name, Chunk07.stackResult176.1)).2
wave8_kernel_reduce cost177 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard113.name, Chunk07.stackResult177.1)).2
wave8_kernel_reduce cost178 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard114.name, Chunk07.stackResult178.1)).2
wave8_kernel_reduce cost179 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard115.name, Chunk07.stackResult179.1)).2
wave8_kernel_reduce cost180 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard116.name, Chunk07.stackResult180.1)).2
wave8_kernel_reduce cost181 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard117.name, Chunk07.stackResult181.1)).2
wave8_kernel_reduce cost182 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard118.name, Chunk07.stackResult182.1)).2
wave8_kernel_reduce cost183 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard119.name, Chunk07.stackResult183.1)).2
wave8_kernel_reduce cost184 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard120.name, Chunk07.stackResult184.1)).2
wave8_kernel_reduce cost185 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard121.name, Chunk07.stackResult185.1)).2
wave8_kernel_reduce cost186 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard122.name, Chunk07.stackResult186.1)).2
wave8_kernel_reduce cost187 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard123.name, Chunk07.stackResult187.1)).2
wave8_kernel_reduce cost188 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard124.name, Chunk07.stackResult188.1)).2
wave8_kernel_reduce cost189 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard125.name, Chunk07.stackResult189.1)).2
wave8_kernel_reduce cost190 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard126.name, Chunk07.stackResult190.1)).2
wave8_kernel_reduce cost191 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard127.name, Chunk07.stackResult191.1)).2

theorem head176 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard112.name, Chunk07.stackResult176.1)).2 ≤ 7313 := by
  rw [cost176_eq]
  decide

theorem head177 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard113.name, Chunk07.stackResult177.1)).2 ≤ 7313 := by
  rw [cost177_eq]
  decide

theorem head178 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard114.name, Chunk07.stackResult178.1)).2 ≤ 7313 := by
  rw [cost178_eq]
  decide

theorem head179 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard115.name, Chunk07.stackResult179.1)).2 ≤ 7313 := by
  rw [cost179_eq]
  decide

theorem head180 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard116.name, Chunk07.stackResult180.1)).2 ≤ 7313 := by
  rw [cost180_eq]
  decide

theorem head181 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard117.name, Chunk07.stackResult181.1)).2 ≤ 7313 := by
  rw [cost181_eq]
  decide

theorem head182 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard118.name, Chunk07.stackResult182.1)).2 ≤ 7313 := by
  rw [cost182_eq]
  decide

theorem head183 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard119.name, Chunk07.stackResult183.1)).2 ≤ 7313 := by
  rw [cost183_eq]
  decide

theorem head184 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard120.name, Chunk07.stackResult184.1)).2 ≤ 7313 := by
  rw [cost184_eq]
  decide

theorem head185 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard121.name, Chunk07.stackResult185.1)).2 ≤ 7313 := by
  rw [cost185_eq]
  decide

theorem head186 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard122.name, Chunk07.stackResult186.1)).2 ≤ 7313 := by
  rw [cost186_eq]
  decide

theorem head187 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard123.name, Chunk07.stackResult187.1)).2 ≤ 7313 := by
  rw [cost187_eq]
  decide

theorem head188 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard124.name, Chunk07.stackResult188.1)).2 ≤ 7313 := by
  rw [cost188_eq]
  decide

theorem head189 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard125.name, Chunk07.stackResult189.1)).2 ≤ 7313 := by
  rw [cost189_eq]
  decide

theorem head190 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard126.name, Chunk07.stackResult190.1)).2 ≤ 7313 := by
  rw [cost190_eq]
  decide

theorem head191 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard127.name, Chunk07.stackResult191.1)).2 ≤ 7313 := by
  rw [cost191_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk07.bodies := by
  unfold Chunk07.bodies
  apply bounded_cons _ _ _ head176
  apply bounded_cons _ _ _ head177
  apply bounded_cons _ _ _ head178
  apply bounded_cons _ _ _ head179
  apply bounded_cons _ _ _ head180
  apply bounded_cons _ _ _ head181
  apply bounded_cons _ _ _ head182
  apply bounded_cons _ _ _ head183
  apply bounded_cons _ _ _ head184
  apply bounded_cons _ _ _ head185
  apply bounded_cons _ _ _ head186
  apply bounded_cons _ _ _ head187
  apply bounded_cons _ _ _ head188
  apply bounded_cons _ _ _ head189
  apply bounded_cons _ _ _ head190
  apply bounded_cons _ _ _ head191
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded07
