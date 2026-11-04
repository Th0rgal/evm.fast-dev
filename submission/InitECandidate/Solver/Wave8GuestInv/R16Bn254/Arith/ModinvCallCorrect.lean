import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.ModinvCorrect

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

theorem arith_lookup_modinv_bin :
    originalRuntimeCode.lookup (ofString "modinv_bin") =
      some ([(ofString "a", arithU256Shape), (ofString "m", arithU256Shape)],
        arithSourceBody Guest.Software.guestFn_modinv_bin, arithU256Shape) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 157 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_modinv_bin) rfl

/-- A scoped successful inverse call supplies the continuation with a
canonical modular inverse, including when its arguments are expressions. -/
theorem modinv_decCall_returned_correct {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (temp : MlS) (args : List (ExpHOL 64)) (cont : ProgHOL 64)
    (a m : Limbs256) (ret : ValueHOL 64)
    (hc : s.code = originalRuntimeCode)
    (hargs : evalListHOLFinite s (h := fun z => Classical.propDecidable (s.memaddrs z)) args =
      some [a.toValue, m.toValue])
    (ha0 : a.toNat ≠ 0) (hmodd : m.toNat % 2 = 1) (hmgt : 1 < m.toNat)
    (hr : evaluateHOLFiniteState s
      (.decCall temp arithU256Shape (ofString "modinv_bin") args cont) = (some (.returned ret), post)) :
    ∃ (x : Limbs256) (resumed inner : PanSemStateFiniteExact 64 F),
      x.toNat < m.toNat ∧ (a.toNat * x.toNat) % m.toNat = 1 ∧
      resumed.locals = s.locals.update (temp, x.toValue) ∧ resumed.code = s.code ∧
      evaluateHOLFiniteState resumed cont = (some (.returned ret), inner) := by
  obtain ⟨values, body, callee, rs, value, bpost, resumed, inner,
    he, hlk, _, hrun, _, hlocals, hcode, hcont, _⟩ := arith_decCall_returned hr
  have hv : values = [a.toValue, m.toValue] := Option.some.inj (he.symm.trans hargs)
  subst values
  rw [hc] at hlk
  obtain ⟨_, _, rfl, rfl, _⟩ := arith_two_arg_lookup_inv_shape
    originalRuntimeCode.lookup (ofString "modinv_bin") (ofString "a") (ofString "m")
    arithU256Shape arithU256Shape arithU256Shape
    (arithSourceBody Guest.Software.guestFn_modinv_bin) a.toValue m.toValue
    (by decide) arith_lookup_modinv_bin hlk
  obtain ⟨x, hx, hxrange, hinv⟩ := modinv_returned_correct
    (s := callEntryStateHOLFinite s ((HolFiniteMapExact.empty.update (ofString "a", a.toValue)).update
      (ofString "m", m.toValue))) a m value hc
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "m" ≠ ofString "a" by decide])
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]) ha0 hmodd hmgt hrun
  exact ⟨x, resumed, inner, hxrange, hinv, by simpa only [hx] using hlocals, hcode, hcont⟩

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
