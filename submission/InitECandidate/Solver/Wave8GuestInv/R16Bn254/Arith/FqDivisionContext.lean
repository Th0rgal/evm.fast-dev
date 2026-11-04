import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.ArithContextSyntax
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolyDivisionZeroBody

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

theorem u256Lt_context : ArithContextPureFunction (ofString "u256_lt") := by
  apply arithContextPureFunction_of_installed _ _ _ _ arith_lookup_u256_lt
  exact arithContextPure_noCalls _ (by decide)

theorem u256Sub_context : ArithContextPureFunction (ofString "u256_sub") := by
  apply arithContextPureFunction_of_installed _ _ _ _ arith_lookup_u256_sub
  exact arithContextPure_noCalls _ (by decide)

theorem u256Add_context : ArithContextPureFunction (ofString "u256_add") := by
  apply arithContextPureFunction_of_installed _ _ _ _ arith_lookup_u256_add
  exact arithContextPure_noCalls _ (by decide)

theorem fqContextAllowed (name : MlS) (h : fqMemoryAllowed name = true) :
    ArithContextPureFunction name := by
  simp only [fqMemoryAllowed,decide_eq_true_eq,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl
  · exact u256Lt_context
  · exact u256Sub_context
  · exact u256Add_context

theorem fqMul_context : ArithContextPureFunction (ofString "fq_mul") := by
  apply arithContextPureFunction_of_installed _ _ _ _ arith_lookup_fq_mul
  exact arithContextPure_of_syntax fqMemoryAllowed fqContextAllowed _ (by decide)

theorem fqSub_context : ArithContextPureFunction (ofString "fq_sub") := by
  apply arithContextPureFunction_of_installed _ _ _ _ arith_lookup_fq_sub
  exact arithContextPure_of_syntax fqMemoryAllowed fqContextAllowed _ (by decide)

theorem zeroBytes_context : ArithContextPureFunction (ofString "is_zero_bytes") := by
  apply arithContextPureFunction_of_installed _ _ _ _ arith_lookup_is_zero_bytes
  exact arithContextPure_noCalls _ (by decide)

theorem fqDegree_context : ArithContextPureFunction (ofString "fq_poly_deg") := by
  apply arithContextPureFunction_of_installed _ _ _ _ arith_lookup_fq_poly_deg
  apply arithContextPure_of_syntax (fun n => decide (n = ofString "is_zero_bytes"))
  · intro n hn
    have he : n = ofString "is_zero_bytes" := of_decide_eq_true hn
    subst n
    exact zeroBytes_context
  · decide

theorem polySubmul_context : ArithContextPureFunction (ofString "fq_poly_submul") := by
  apply arithContextPureFunction_of_installed _ _ _ _ arith_lookup_fq_poly_submul
  apply arithContextPure_of_syntax (fun n => decide (n ∈ [ofString "fq_mul",ofString "fq_sub"]))
  · intro n hn
    simp only [decide_eq_true_eq,List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl | rfl
    · exact fqMul_context
    · exact fqSub_context
  · decide

/-- Every execution of the actual division body preserves all fields other
than locals, memory and clock. This includes FFI and global state. -/
theorem polyDivBody_context : ArithContextPure polyDivBody := by
  apply arithContextPure_of_syntax (fun n => decide (n ∈
    [ofString "fq_mul",ofString "fq_poly_submul",ofString "fq_poly_deg"]))
  · intro n hn
    simp only [decide_eq_true_eq,List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl | rfl | rfl
    · exact fqMul_context
    · exact polySubmul_context
    · exact fqDegree_context
  · decide

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
