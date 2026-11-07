import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk06
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded06
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open StackToLabClock LoweredBudget

wave8_kernel_reduce cost160 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard96.name, Chunk06.stackResult160.1)).2
wave8_kernel_reduce cost161 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard97.name, Chunk06.stackResult161.1)).2
wave8_kernel_reduce cost162 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard98.name, Chunk06.stackResult162.1)).2
wave8_kernel_reduce cost163 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard99.name, Chunk06.stackResult163.1)).2
wave8_kernel_reduce cost164 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard100.name, Chunk06.stackResult164.1)).2
wave8_kernel_reduce cost165 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard101.name, Chunk06.stackResult165.1)).2
wave8_kernel_reduce cost166 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard102.name, Chunk06.stackResult166.1)).2
wave8_kernel_reduce cost167 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard103.name, Chunk06.stackResult167.1)).2
wave8_kernel_reduce cost168 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard104.name, Chunk06.stackResult168.1)).2
wave8_kernel_reduce cost169 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard105.name, Chunk06.stackResult169.1)).2
wave8_kernel_reduce cost170 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard106.name, Chunk06.stackResult170.1)).2
wave8_kernel_reduce cost171 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard107.name, Chunk06.stackResult171.1)).2
wave8_kernel_reduce cost172 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard108.name, Chunk06.stackResult172.1)).2
wave8_kernel_reduce cost173 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard109.name, Chunk06.stackResult173.1)).2
wave8_kernel_reduce cost174 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard110.name, Chunk06.stackResult174.1)).2
wave8_kernel_reduce cost175 := stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard111.name, Chunk06.stackResult175.1)).2

theorem head160 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard96.name, Chunk06.stackResult160.1)).2 ≤ 7313 := by
  rw [cost160_eq]
  decide

theorem head161 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard97.name, Chunk06.stackResult161.1)).2 ≤ 7313 := by
  rw [cost161_eq]
  decide

theorem head162 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard98.name, Chunk06.stackResult162.1)).2 ≤ 7313 := by
  rw [cost162_eq]
  decide

theorem head163 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard99.name, Chunk06.stackResult163.1)).2 ≤ 7313 := by
  rw [cost163_eq]
  decide

theorem head164 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard100.name, Chunk06.stackResult164.1)).2 ≤ 7313 := by
  rw [cost164_eq]
  decide

theorem head165 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard101.name, Chunk06.stackResult165.1)).2 ≤ 7313 := by
  rw [cost165_eq]
  decide

theorem head166 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard102.name, Chunk06.stackResult166.1)).2 ≤ 7313 := by
  rw [cost166_eq]
  decide

theorem head167 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard103.name, Chunk06.stackResult167.1)).2 ≤ 7313 := by
  rw [cost167_eq]
  decide

theorem head168 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard104.name, Chunk06.stackResult168.1)).2 ≤ 7313 := by
  rw [cost168_eq]
  decide

theorem head169 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard105.name, Chunk06.stackResult169.1)).2 ≤ 7313 := by
  rw [cost169_eq]
  decide

theorem head170 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard106.name, Chunk06.stackResult170.1)).2 ≤ 7313 := by
  rw [cost170_eq]
  decide

theorem head171 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard107.name, Chunk06.stackResult171.1)).2 ≤ 7313 := by
  rw [cost171_eq]
  decide

theorem head172 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard108.name, Chunk06.stackResult172.1)).2 ≤ 7313 := by
  rw [cost172_eq]
  decide

theorem head173 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard109.name, Chunk06.stackResult173.1)).2 ≤ 7313 := by
  rw [cost173_eq]
  decide

theorem head174 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard110.name, Chunk06.stackResult174.1)).2 ≤ 7313 := by
  rw [cost174_eq]
  decide

theorem head175 : stepCost (lowerEntry GlobalFrameInfo.info (PrefixChecks.Shard111.name, Chunk06.stackResult175.1)).2 ≤ 7313 := by
  rw [cost175_eq]
  decide

theorem bounded : Bounded GlobalFrameInfo.info Chunk06.bodies := by
  unfold Chunk06.bodies
  apply bounded_cons _ _ _ head160
  apply bounded_cons _ _ _ head161
  apply bounded_cons _ _ _ head162
  apply bounded_cons _ _ _ head163
  apply bounded_cons _ _ _ head164
  apply bounded_cons _ _ _ head165
  apply bounded_cons _ _ _ head166
  apply bounded_cons _ _ _ head167
  apply bounded_cons _ _ _ head168
  apply bounded_cons _ _ _ head169
  apply bounded_cons _ _ _ head170
  apply bounded_cons _ _ _ head171
  apply bounded_cons _ _ _ head172
  apply bounded_cons _ _ _ head173
  apply bounded_cons _ _ _ head174
  apply bounded_cons _ _ _ head175
  exact bounded_nil GlobalFrameInfo.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded06
