import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk10
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded10
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open StackToLabClock LoweredBudget

wave8_kernel_reduce cost224 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard160.name, Chunk10.stackResult224.1)).2
wave8_kernel_reduce cost225 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard161.name, Chunk10.stackResult225.1)).2
wave8_kernel_reduce cost226 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard162.name, Chunk10.stackResult226.1)).2
wave8_kernel_reduce cost227 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard163.name, Chunk10.stackResult227.1)).2
wave8_kernel_reduce cost228 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard164.name, Chunk10.stackResult228.1)).2
wave8_kernel_reduce cost229 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard165.name, Chunk10.stackResult229.1)).2
wave8_kernel_reduce cost230 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard166.name, Chunk10.stackResult230.1)).2
wave8_kernel_reduce cost231 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard167.name, Chunk10.stackResult231.1)).2
wave8_kernel_reduce cost232 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard168.name, Chunk10.stackResult232.1)).2
wave8_kernel_reduce cost233 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard169.name, Chunk10.stackResult233.1)).2
wave8_kernel_reduce cost234 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard170.name, Chunk10.stackResult234.1)).2
wave8_kernel_reduce cost235 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard171.name, Chunk10.stackResult235.1)).2
wave8_kernel_reduce cost236 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard172.name, Chunk10.stackResult236.1)).2
wave8_kernel_reduce cost237 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard173.name, Chunk10.stackResult237.1)).2
wave8_kernel_reduce cost238 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard174.name, Chunk10.stackResult238.1)).2
wave8_kernel_reduce cost239 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard175.name, Chunk10.stackResult239.1)).2

theorem head224 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard160.name, Chunk10.stackResult224.1)).2 ≤ 7313 := by
  rw [cost224_eq]
  decide

theorem head225 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard161.name, Chunk10.stackResult225.1)).2 ≤ 7313 := by
  rw [cost225_eq]
  decide

theorem head226 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard162.name, Chunk10.stackResult226.1)).2 ≤ 7313 := by
  rw [cost226_eq]
  decide

theorem head227 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard163.name, Chunk10.stackResult227.1)).2 ≤ 7313 := by
  rw [cost227_eq]
  decide

theorem head228 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard164.name, Chunk10.stackResult228.1)).2 ≤ 7313 := by
  rw [cost228_eq]
  decide

theorem head229 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard165.name, Chunk10.stackResult229.1)).2 ≤ 7313 := by
  rw [cost229_eq]
  decide

theorem head230 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard166.name, Chunk10.stackResult230.1)).2 ≤ 7313 := by
  rw [cost230_eq]
  decide

theorem head231 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard167.name, Chunk10.stackResult231.1)).2 ≤ 7313 := by
  rw [cost231_eq]
  decide

theorem head232 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard168.name, Chunk10.stackResult232.1)).2 ≤ 7313 := by
  rw [cost232_eq]
  decide

theorem head233 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard169.name, Chunk10.stackResult233.1)).2 ≤ 7313 := by
  rw [cost233_eq]
  decide

theorem head234 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard170.name, Chunk10.stackResult234.1)).2 ≤ 7313 := by
  rw [cost234_eq]
  decide

theorem head235 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard171.name, Chunk10.stackResult235.1)).2 ≤ 7313 := by
  rw [cost235_eq]
  decide

theorem head236 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard172.name, Chunk10.stackResult236.1)).2 ≤ 7313 := by
  rw [cost236_eq]
  decide

theorem head237 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard173.name, Chunk10.stackResult237.1)).2 ≤ 7313 := by
  rw [cost237_eq]
  decide

theorem head238 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard174.name, Chunk10.stackResult238.1)).2 ≤ 7313 := by
  rw [cost238_eq]
  decide

theorem head239 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard175.name, Chunk10.stackResult239.1)).2 ≤ 7313 := by
  rw [cost239_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk10.bodies := by
  unfold Chunk10.bodies
  apply bounded_cons _ _ _ head224
  apply bounded_cons _ _ _ head225
  apply bounded_cons _ _ _ head226
  apply bounded_cons _ _ _ head227
  apply bounded_cons _ _ _ head228
  apply bounded_cons _ _ _ head229
  apply bounded_cons _ _ _ head230
  apply bounded_cons _ _ _ head231
  apply bounded_cons _ _ _ head232
  apply bounded_cons _ _ _ head233
  apply bounded_cons _ _ _ head234
  apply bounded_cons _ _ _ head235
  apply bounded_cons _ _ _ head236
  apply bounded_cons _ _ _ head237
  apply bounded_cons _ _ _ head238
  apply bounded_cons _ _ _ head239
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded10
