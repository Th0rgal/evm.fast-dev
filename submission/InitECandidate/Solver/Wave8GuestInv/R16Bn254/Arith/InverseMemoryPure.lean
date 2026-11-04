import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqMemoryPure
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqInverseCalls

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem u256AddCarry_memoryPure : MemoryPureFunction (ofString "u256_add_carry") := by
  apply memoryPureFunction_of_installed _ _ _ _ arith_lookup_u256_add_carry
  exact memoryPure_noCalls _ (by decide)

theorem u256IsZero_memoryPure : MemoryPureFunction (ofString "u256_is_zero") := by
  apply memoryPureFunction_of_installed _ _ _ _ arith_lookup_u256_is_zero
  exact memoryPure_noCalls _ (by decide)

theorem modHalf_memoryPure : MemoryPureFunction (ofString "mod_half") := by
  apply memoryPureFunction_of_installed _ _ _ _ arith_lookup_mod_half
  apply memoryPure_of_syntax (fun n => decide (n = ofString "u256_add_carry"))
  · intro n hn
    have he : n = ofString "u256_add_carry" := of_decide_eq_true hn
    subst n
    exact u256AddCarry_memoryPure
  · decide

theorem modSub_memoryPure : MemoryPureFunction (ofString "mod_sub") := by
  apply memoryPureFunction_of_installed _ _ _ _ arith_lookup_mod_sub
  exact memoryPure_of_syntax fqMemoryAllowed fqMemoryAllowed_pure _ (by decide)

def inverseMemoryAllowed (name : MlS) : Bool :=
  decide (name ∈ [ofString "u256_is_zero", ofString "mod_half", ofString "u256_lt",
    ofString "u256_sub", ofString "mod_sub"])

theorem inverseMemoryAllowed_pure (name : MlS) (h : inverseMemoryAllowed name = true) :
    MemoryPureFunction name := by
  simp only [inverseMemoryAllowed, decide_eq_true_eq, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl
  · exact u256IsZero_memoryPure
  · exact modHalf_memoryPure
  · exact u256Lt_memoryPure
  · exact u256Sub_memoryPure
  · exact modSub_memoryPure

theorem modinv_memoryPure : MemoryPureFunction (ofString "modinv_bin") := by
  apply memoryPureFunction_of_installed _ _ _ _ arith_lookup_modinv_bin
  exact memoryPure_of_syntax inverseMemoryAllowed inverseMemoryAllowed_pure _ (by decide)

def fqInverseMemoryAllowed (name : MlS) : Bool :=
  decide (name ∈ [ofString "modinv_bin", ofString "fq_mul"])

theorem fqInverseMemoryAllowed_pure (name : MlS) (h : fqInverseMemoryAllowed name = true) :
    MemoryPureFunction name := by
  simp only [fqInverseMemoryAllowed, decide_eq_true_eq, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl
  · exact modinv_memoryPure
  · exact fqMul_function_memoryPure

theorem fqInverse_memoryPure : MemoryPure (arithSourceBody Guest.Software.guestFn_fq_inv) :=
  memoryPure_of_syntax fqInverseMemoryAllowed fqInverseMemoryAllowed_pure _ (by decide)

theorem fqInverse_function_memoryPure : MemoryPureFunction (ofString "fq_inv") :=
  memoryPureFunction_of_installed _ _ _ _ arith_lookup_fq_inv fqInverse_memoryPure

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
