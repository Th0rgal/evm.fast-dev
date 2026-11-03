import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqInitialState
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqMulColumns

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

/-- Actual fq_mul successful-return correctness. Any typed first operand and
one canonical second operand yield the canonical Montgomery product. -/
theorem fqMul_returned_canonical {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (A B : Limbs256) (ret : ValueHOL 64)
    (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup (ofString "a") = some A.toValue)
    (hb : s.locals.lookup (ofString "b") = some B.toValue)
    (hB : B.toNat < fqModulus.toNat)
    (he : evaluateHOLFiniteState s (arithSourceBody Guest.Software.guestFn_fq_mul) =
      (some (.returned ret), post)) :
    ∃ out : Limbs256, ret = out.toValue ∧ out.toNat < fqModulus.toNat ∧
      Nat.ModEq fqModulus.toNat (2 ^ 256 * out.toNat) (A.toNat * B.toNat) := by
  rw [fqMul_source_eq] at he
  change evaluateHOLFiniteState s (montDeclareWords fqMulInitializers fqMulColumn0) = _ at he
  have htrace := fqInitializers_trace s A B ha hb
  obtain ⟨inner, hcolumns⟩ := montInitTrace_returned htrace fqMulColumn0 ret he
  exact fqMulColumns_returned
    (s := montSetWords s (fqInitAssignments A B fqInitSpecs)) A B ret
    ((montSetWords_code s _).trans hc) hB (fqInitialState_slots s A B) hcolumns

end InitECandidate.Solver.Wave8GuestInv.Arith
