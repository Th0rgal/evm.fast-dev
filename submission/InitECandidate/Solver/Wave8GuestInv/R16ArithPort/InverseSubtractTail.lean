import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.InverseCallFacts

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.PanTerminatingCombinators
attribute [local irreducible] wordAddCarryHOL subCarry256

structure InverseLocals where
  u : Limbs256
  v : Limbs256
  x1 : Limbs256
  x2 : Limbs256
  m : Limbs256

def InverseLocals.Matches (q : InverseLocals) {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  s.locals.lookup (ofString "u") = some q.u.toValue ∧
  s.locals.lookup (ofString "v") = some q.v.toValue ∧
  s.locals.lookup (ofString "x1") = some q.x1.toValue ∧
  s.locals.lookup (ofString "x2") = some q.x2.toValue ∧
  s.locals.lookup (ofString "m") = some q.m.toValue

def inverseSubtractTail : ProgHOL 64 :=
  .decCall (ofString "ult") .one (ofString "u256_lt")
    [.var .local (ofString "u"), .var .local (ofString "v")]
    (.ite (.cmp .equal (.var .local (ofString "ult")) (.const 0))
      (.seq (.call (some (some (.local, ofString "u"), none)) (ofString "u256_sub")
        [.var .local (ofString "u"), .var .local (ofString "v")])
        (.call (some (some (.local, ofString "x1"), none)) (ofString "mod_sub")
          [.var .local (ofString "x1"), .var .local (ofString "x2"), .var .local (ofString "m")]))
      (.seq (.call (some (some (.local, ofString "v"), none)) (ofString "u256_sub")
        [.var .local (ofString "v"), .var .local (ofString "u")])
        (.call (some (some (.local, ofString "x2"), none)) (ofString "mod_sub")
          [.var .local (ofString "x2"), .var .local (ofString "x1"), .var .local (ofString "m")])))

theorem arith_lookup_mod_sub :
    originalRuntimeCode.lookup (ofString "mod_sub") =
      some ([(ofString "x", arithU256Shape), (ofString "y", arithU256Shape), (ofString "m", arithU256Shape)],
        arithSourceBody Guest.Software.guestFn_mod_sub, arithU256Shape) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 159 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_mod_sub) rfl

theorem inverseSubtractTail_none {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (q : InverseLocals) (hc : s.code = originalRuntimeCode) (hq : q.Matches s)
    (hr : evaluateHOLFiniteState s inverseSubtractTail = (none, post)) :
    ∃ r : InverseLocals, r.Matches post ∧
      r.u.toNat = (inverseSubtract q.u.toNat q.v.toNat).1 ∧
      r.v.toNat = (inverseSubtract q.u.toNat q.v.toNat).2 := by
  obtain ⟨hu, hv, hx1, hx2, hm⟩ := hq
  unfold inverseSubtractTail at hr
  obtain ⟨resumed, inner, hlocals, hcode, hcont, hpost⟩ :=
    inverse_lt_decCall_none (ofString "ult") (ofString "u") (ofString "v") q.u q.v _ hc hu hv hr
  have hru : resumed.locals.lookup (ofString "u") = some q.u.toValue := by
    rw [hlocals]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, hu, show ofString "ult" ≠ ofString "u" by decide]
  have hrv : resumed.locals.lookup (ofString "v") = some q.v.toValue := by
    rw [hlocals]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, hv, show ofString "ult" ≠ ofString "v" by decide]
  have hlt : resumed.locals.lookup (ofString "ult") =
      some (.val (.word (if q.u.toNat < q.v.toNat then 1 else 0))) := by
    rw [hlocals]
    simp [HolFiniteMapExact.lookup_update, FUPDATE]
  rw [evaluateHOLFiniteState_ite] at hcont
  have hrc : resumed.code = originalRuntimeCode := hcode.trans hc
  by_cases hless : q.u.toNat < q.v.toNat
  · simp only [evalHOLExact, hlt, if_pos hless, Compiler.Encoders.Asm.wordCmpHOL] at hcont
    obtain ⟨mid, hsub, hmod⟩ := arith_seq_none hcont
    have hsublocals := inverse_sub_call_none (ofString "v") (ofString "v")
      (ofString "u") q.v q.u hrc hrv hru hsub
    have hmc : mid.code = originalRuntimeCode := by
      have h := evalP_code resumed
        (.call (some (some (.local, ofString "v"), none)) (ofString "u256_sub")
          [.var .local (ofString "v"), .var .local (ofString "u")])
      rw [hsub] at h
      exact h.trans hrc
    obtain ⟨xnew, hmodlocals⟩ := arith_call_local_u256_none (ofString "x2") (ofString "mod_sub")
      [.var .local (ofString "x2"), .var .local (ofString "x1"), .var .local (ofString "m")]
      _ _ hmc arith_lookup_mod_sub hmod
    refine ⟨{q with v := (subCarry256 q.v q.u).1, x2 := xnew}, ?_, ?_, ?_⟩
    · unfold InverseLocals.Matches
      simp [hpost, hmodlocals, hsublocals, hlocals, PanRunBounded.resVarEq_lookup,
        HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "u" ≠ ofString "v" by decide,
        show ofString "u" ≠ ofString "x1" by decide,
        show ofString "u" ≠ ofString "x2" by decide,
        show ofString "u" ≠ ofString "m" by decide,
        show ofString "u" ≠ ofString "ult" by decide,
        show ofString "v" ≠ ofString "u" by decide,
        show ofString "v" ≠ ofString "x1" by decide,
        show ofString "v" ≠ ofString "x2" by decide,
        show ofString "v" ≠ ofString "m" by decide,
        show ofString "v" ≠ ofString "ult" by decide,
        show ofString "x1" ≠ ofString "u" by decide,
        show ofString "x1" ≠ ofString "v" by decide,
        show ofString "x1" ≠ ofString "x2" by decide,
        show ofString "x1" ≠ ofString "m" by decide,
        show ofString "x1" ≠ ofString "ult" by decide,
        show ofString "x2" ≠ ofString "u" by decide,
        show ofString "x2" ≠ ofString "v" by decide,
        show ofString "x2" ≠ ofString "x1" by decide,
        show ofString "x2" ≠ ofString "m" by decide,
        show ofString "x2" ≠ ofString "ult" by decide,
        show ofString "m" ≠ ofString "u" by decide,
        show ofString "m" ≠ ofString "v" by decide,
        show ofString "m" ≠ ofString "x1" by decide,
        show ofString "m" ≠ ofString "x2" by decide,
        show ofString "m" ≠ ofString "ult" by decide,
        show ofString "ult" ≠ ofString "u" by decide,
        show ofString "ult" ≠ ofString "v" by decide,
        show ofString "ult" ≠ ofString "x1" by decide,
        show ofString "ult" ≠ ofString "x2" by decide,
        show ofString "ult" ≠ ofString "m" by decide, hu, hv, hx1, hx2, hm, if_false, if_true, and_self]
    · simp [inverseSubtract, show ¬ q.v.toNat ≤ q.u.toNat by omega]
    · simpa [inverseSubtract, show ¬ q.v.toNat ≤ q.u.toNat by omega] using
        subCarry256_no_borrow q.v q.u (by omega)
  · simp only [evalHOLExact, hlt, if_neg hless, Compiler.Encoders.Asm.wordCmpHOL] at hcont
    obtain ⟨mid, hsub, hmod⟩ := arith_seq_none hcont
    have hsublocals := inverse_sub_call_none (ofString "u") (ofString "u")
      (ofString "v") q.u q.v hrc hru hrv hsub
    have hmc : mid.code = originalRuntimeCode := by
      have h := evalP_code resumed
        (.call (some (some (.local, ofString "u"), none)) (ofString "u256_sub")
          [.var .local (ofString "u"), .var .local (ofString "v")])
      rw [hsub] at h
      exact h.trans hrc
    obtain ⟨xnew, hmodlocals⟩ := arith_call_local_u256_none (ofString "x1") (ofString "mod_sub")
      [.var .local (ofString "x1"), .var .local (ofString "x2"), .var .local (ofString "m")]
      _ _ hmc arith_lookup_mod_sub hmod
    refine ⟨{q with u := (subCarry256 q.u q.v).1, x1 := xnew}, ?_, ?_, ?_⟩
    · unfold InverseLocals.Matches
      simp [hpost, hmodlocals, hsublocals, hlocals, PanRunBounded.resVarEq_lookup,
        HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "u" ≠ ofString "v" by decide,
        show ofString "u" ≠ ofString "x1" by decide,
        show ofString "u" ≠ ofString "x2" by decide,
        show ofString "u" ≠ ofString "m" by decide,
        show ofString "u" ≠ ofString "ult" by decide,
        show ofString "v" ≠ ofString "u" by decide,
        show ofString "v" ≠ ofString "x1" by decide,
        show ofString "v" ≠ ofString "x2" by decide,
        show ofString "v" ≠ ofString "m" by decide,
        show ofString "v" ≠ ofString "ult" by decide,
        show ofString "x1" ≠ ofString "u" by decide,
        show ofString "x1" ≠ ofString "v" by decide,
        show ofString "x1" ≠ ofString "x2" by decide,
        show ofString "x1" ≠ ofString "m" by decide,
        show ofString "x1" ≠ ofString "ult" by decide,
        show ofString "x2" ≠ ofString "u" by decide,
        show ofString "x2" ≠ ofString "v" by decide,
        show ofString "x2" ≠ ofString "x1" by decide,
        show ofString "x2" ≠ ofString "m" by decide,
        show ofString "x2" ≠ ofString "ult" by decide,
        show ofString "m" ≠ ofString "u" by decide,
        show ofString "m" ≠ ofString "v" by decide,
        show ofString "m" ≠ ofString "x1" by decide,
        show ofString "m" ≠ ofString "x2" by decide,
        show ofString "m" ≠ ofString "ult" by decide,
        show ofString "ult" ≠ ofString "u" by decide,
        show ofString "ult" ≠ ofString "v" by decide,
        show ofString "ult" ≠ ofString "x1" by decide,
        show ofString "ult" ≠ ofString "x2" by decide,
        show ofString "ult" ≠ ofString "m" by decide, hu, hv, hx1, hx2, hm, if_false, if_true, and_self]
    · simpa [inverseSubtract, show q.v.toNat ≤ q.u.toNat by omega] using
        subCarry256_no_borrow q.u q.v (by omega)
    · simp [inverseSubtract, show q.v.toNat ≤ q.u.toNat by omega]
end InitECandidate.Solver.Wave8GuestInv.Arith
