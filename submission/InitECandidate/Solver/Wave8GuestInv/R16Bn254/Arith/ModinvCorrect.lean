import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.InverseInitCorrect
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.U256ZeroCall

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

/-- A successful inverse of a nonzero input, for an odd modulus greater than
one, is canonical and satisfies the actual modular inverse equation. -/
theorem modinv_returned_correct {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (a m : Limbs256) (ret : ValueHOL 64)
    (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup (ofString "a") = some a.toValue)
    (hm : s.locals.lookup (ofString "m") = some m.toValue)
    (ha0 : a.toNat ≠ 0) (hmodd : m.toNat % 2 = 1) (hmgt : 1 < m.toNat)
    (hr : evaluateHOLFiniteState s (arithSourceBody Guest.Software.guestFn_modinv_bin) =
      (some (.returned ret), post)) :
    ∃ x : Limbs256, ret = x.toValue ∧ x.toNat < m.toNat ∧
      (a.toNat * x.toNat) % m.toNat = 1 := by
  rw [inverseSource_eq] at hr
  obtain ⟨resumed, inner, hl, hcode, hcont⟩ :=
    u256Zero_decCall_returned (ofString "az") (ofString "a") a _ ret hc ha hr
  have haz : resumed.locals.lookup (ofString "az") = some (.val (.word 0)) := by
    simp [hl, HolFiniteMapExact.lookup_update, FUPDATE, ha0]
  have hskip : evaluateHOLFiniteState resumed
      (.ite (.cmp .equal (.var .local (ofString "az")) (.const 1))
        (.return inverseZeroExpr) .skip) = (none, resumed) := by
    simp [evaluateHOLFiniteState_ite, evalHOLExact, haz,
      Compiler.Encoders.Asm.wordCmpHOL, evaluateHOLFiniteState_skip]
  rw [evaluateHOLFiniteState_seq_line780, hskip] at hcont
  obtain ⟨x, hret, hlt, hinv⟩ := inverseInitBody_returned_correct (s := resumed) a m ret (hcode.trans hc)
    (by simp [hl, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "az" ≠ ofString "a" by decide, ha])
    (by simp [hl, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "az" ≠ ofString "m" by decide, hm])
    hmodd hmgt hcont
  exact ⟨x, hret, hlt, (inverseCongruence_one _ _ _ hinv).trans (Nat.mod_eq_of_lt hmgt)⟩

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
