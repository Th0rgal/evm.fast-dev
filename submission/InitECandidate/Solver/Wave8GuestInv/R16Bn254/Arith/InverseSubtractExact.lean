import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.ModSubCallExact
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.InverseCongruence

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
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.PanTerminatingCombinators
attribute [local irreducible] wordAddCarryHOL subCarry256

def inverseSubtractLocals (q : InverseLocals) : InverseLocals :=
  if q.u.toNat < q.v.toNat then
    {q with v := (subCarry256 q.v q.u).1, x2 := modSub256 q.x2 q.x1 q.m}
  else
    {q with u := (subCarry256 q.u q.v).1, x1 := modSub256 q.x1 q.x2 q.m}

theorem inverseSubtractTail_exact_none {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (q : InverseLocals) (hc : s.code = originalRuntimeCode) (hq : q.Matches s)
    (hr : evaluateHOLFiniteState s inverseSubtractTail = (none, post)) :
    (inverseSubtractLocals q).Matches post := by
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
    have hmodlocals := modSub_call_exact_none (ofString "x2") (ofString "x2")
      (ofString "x1") (ofString "m") q.x2 q.x1 q.m hmc
      (by simp [hsublocals, hlocals, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "v" ≠ ofString "x2" by decide,
        show ofString "ult" ≠ ofString "x2" by decide, hx2])
      (by simp [hsublocals, hlocals, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "v" ≠ ofString "x1" by decide,
        show ofString "ult" ≠ ofString "x1" by decide, hx1])
      (by simp [hsublocals, hlocals, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "v" ≠ ofString "m" by decide,
        show ofString "ult" ≠ ofString "m" by decide, hm]) hmod
    simp only [inverseSubtractLocals, hless, if_pos] 
    unfold InverseLocals.Matches
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
    have hmodlocals := modSub_call_exact_none (ofString "x1") (ofString "x1")
      (ofString "x2") (ofString "m") q.x1 q.x2 q.m hmc
      (by simp [hsublocals, hlocals, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "u" ≠ ofString "x1" by decide,
        show ofString "ult" ≠ ofString "x1" by decide, hx1])
      (by simp [hsublocals, hlocals, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "u" ≠ ofString "x2" by decide,
        show ofString "ult" ≠ ofString "x2" by decide, hx2])
      (by simp [hsublocals, hlocals, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "u" ≠ ofString "m" by decide,
        show ofString "ult" ≠ ofString "m" by decide, hm]) hmod
    simp only [inverseSubtractLocals, hless, if_neg] 
    unfold InverseLocals.Matches
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
def InverseLocals.CoefficientInvariant (input : Nat) (q : InverseLocals) : Prop :=
  InverseCongruence input q.m.toNat q.u.toNat q.x1.toNat ∧
  InverseCongruence input q.m.toNat q.v.toNat q.x2.toNat ∧
  q.x1.toNat < q.m.toNat ∧ q.x2.toNat < q.m.toNat ∧ q.m.toNat % 2 = 1

theorem inverseSubtractLocals_congruence (input : Nat) (q : InverseLocals)
    (h : q.CoefficientInvariant input) :
    (inverseSubtractLocals q).CoefficientInvariant input := by
  obtain ⟨hu, hv, hx1, hx2, hm⟩ := h
  unfold inverseSubtractLocals
  by_cases hlt : q.u.toNat < q.v.toNat
  · rw [if_pos hlt]
    obtain ⟨hi, hr⟩ := inverseCongruence_sub input q.v.toNat q.u.toNat q.x2 q.x1 q.m
      (by omega) hx2 hx1 hv hu
    refine ⟨hu, ?_, hx1, hr, hm⟩
    simpa only [subCarry256_no_borrow q.v q.u (by omega)] using hi
  · rw [if_neg hlt]
    obtain ⟨hi, hr⟩ := inverseCongruence_sub input q.u.toNat q.v.toNat q.x1 q.x2 q.m
      (by omega) hx1 hx2 hu hv
    refine ⟨?_, hv, hr, hx2, hm⟩
    simpa only [subCarry256_no_borrow q.u q.v (by omega)] using hi

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
