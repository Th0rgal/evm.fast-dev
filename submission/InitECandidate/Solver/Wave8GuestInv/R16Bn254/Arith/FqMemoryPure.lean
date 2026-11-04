import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.U256MemoryPure
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqMulCalls
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqSubSource
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqAddSource

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def fqMemoryAllowed (name : MlS) : Bool :=
  decide (name ∈ [ofString "u256_lt", ofString "u256_sub", ofString "u256_add"])

theorem fqMemoryAllowed_pure (name : MlS) (h : fqMemoryAllowed name = true) :
    MemoryPureFunction name := by
  simp only [fqMemoryAllowed, decide_eq_true_eq, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl
  · exact u256Lt_memoryPure
  · exact u256Sub_memoryPure
  · exact u256Add_memoryPure

/-- Actual source fq_mul preserves memory for every outcome and arbitrary inputs. -/
theorem fqMul_memoryPure : MemoryPure (arithSourceBody Guest.Software.guestFn_fq_mul) :=
  memoryPure_of_syntax fqMemoryAllowed fqMemoryAllowed_pure _ (by decide)

theorem fqSub_memoryPure : MemoryPure (arithSourceBody Guest.Software.guestFn_fq_sub) :=
  memoryPure_of_syntax fqMemoryAllowed fqMemoryAllowed_pure _ (by decide)

theorem fqAdd_memoryPure : MemoryPure (arithSourceBody Guest.Software.guestFn_fq_add) :=
  memoryPure_of_syntax fqMemoryAllowed fqMemoryAllowed_pure _ (by decide)

theorem fqMul_function_memoryPure : MemoryPureFunction (ofString "fq_mul") :=
  memoryPureFunction_of_installed _ _ _ _ arith_lookup_fq_mul fqMul_memoryPure

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
