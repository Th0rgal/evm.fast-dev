import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.BlsSubtractCall
import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.BlsHalfNormalize
import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.BlsHalfLoop
import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.ReadOnlyPrefix

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.PanTerminatingCombinators
attribute [local irreducible] wordAddCarryHOL subCarry384

structure BlsInverseLocals where
  u : Limbs384
  v : Limbs384
  x1 : Limbs384
  x2 : Limbs384

def BlsInverseLocals.Matches (q : BlsInverseLocals) {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  s.locals.lookup (ofString "u") = some q.u.toValue ∧
  s.locals.lookup (ofString "v") = some q.v.toValue ∧
  s.locals.lookup (ofString "x1") = some q.x1.toValue ∧
  s.locals.lookup (ofString "x2") = some q.x2.toValue

def blsInverseSubtractTail : ProgHOL 64 :=
  .decCall (ofString "ult") .one (ofString "bls_fp_lt_raw")
    [.var .local (ofString "u"), .var .local (ofString "v")]
    (.ite (.cmp .equal (.var .local (ofString "ult")) (.const 0))
      (blsSubUpdate (ofString "d") (ofString "u") (ofString "v") (ofString "x1") (ofString "x2"))
      (blsSubUpdate (ofString "e") (ofString "v") (ofString "u") (ofString "x2") (ofString "x1")))

theorem blsInverseSubtractTail_none {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (q : BlsInverseLocals) (hc : s.code = originalRuntimeCode) (hq : q.Matches s)
    (hr : evaluateHOLFiniteState s blsInverseSubtractTail = (none, post)) :
    ∃ r : BlsInverseLocals, r.Matches post ∧
      r.u.toNat = (inverseSubtract q.u.toNat q.v.toNat).1 ∧
      r.v.toNat = (inverseSubtract q.u.toNat q.v.toNat).2 := by
  obtain ⟨hu, hv, hx1, hx2⟩ := hq
  unfold blsInverseSubtractTail at hr
  obtain ⟨resumed, inner, hlocals, hcode, hcont, hpost⟩ :=
    bls_lt_decCall_none (ofString "ult") (ofString "u") (ofString "v") q.u q.v _ hc hu hv hr
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
    obtain ⟨xnew, hresult⟩ := blsSubUpdate_none (ofString "e") (ofString "v")
      (ofString "u") (ofString "x2") (ofString "x1") q.v q.u (by decide) hrc hrv hru hcont
    refine ⟨{q with v := (subCarry384 q.v q.u).1, x2 := xnew}, ?_, ?_, ?_⟩
    · unfold BlsInverseLocals.Matches
      simp [hpost, hresult, hlocals, PanRunBounded.resVarEq_lookup,
        HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "u" ≠ ofString "v" by decide,
        show ofString "u" ≠ ofString "x1" by decide,
        show ofString "u" ≠ ofString "x2" by decide,
        show ofString "u" ≠ ofString "ult" by decide,
        show ofString "u" ≠ ofString "e" by decide,
        show ofString "v" ≠ ofString "u" by decide,
        show ofString "v" ≠ ofString "x1" by decide,
        show ofString "v" ≠ ofString "x2" by decide,
        show ofString "v" ≠ ofString "ult" by decide,
        show ofString "v" ≠ ofString "e" by decide,
        show ofString "x1" ≠ ofString "u" by decide,
        show ofString "x1" ≠ ofString "v" by decide,
        show ofString "x1" ≠ ofString "x2" by decide,
        show ofString "x1" ≠ ofString "ult" by decide,
        show ofString "x1" ≠ ofString "e" by decide,
        show ofString "x2" ≠ ofString "u" by decide,
        show ofString "x2" ≠ ofString "v" by decide,
        show ofString "x2" ≠ ofString "x1" by decide,
        show ofString "x2" ≠ ofString "ult" by decide,
        show ofString "x2" ≠ ofString "e" by decide,
        show ofString "ult" ≠ ofString "u" by decide,
        show ofString "ult" ≠ ofString "v" by decide,
        show ofString "ult" ≠ ofString "x1" by decide,
        show ofString "ult" ≠ ofString "x2" by decide,
        show ofString "ult" ≠ ofString "e" by decide,
        show ofString "e" ≠ ofString "u" by decide,
        show ofString "e" ≠ ofString "v" by decide,
        show ofString "e" ≠ ofString "x1" by decide,
        show ofString "e" ≠ ofString "x2" by decide,
        show ofString "e" ≠ ofString "ult" by decide, hu, hv, hx1, hx2]
    · simp [inverseSubtract, show ¬ q.v.toNat ≤ q.u.toNat by omega]
    · simpa [inverseSubtract, show ¬ q.v.toNat ≤ q.u.toNat by omega] using
        subCarry384_no_borrow q.v q.u (by omega)
  · simp only [evalHOLExact, hlt, if_neg hless, Compiler.Encoders.Asm.wordCmpHOL] at hcont
    obtain ⟨xnew, hresult⟩ := blsSubUpdate_none (ofString "d") (ofString "u")
      (ofString "v") (ofString "x1") (ofString "x2") q.u q.v (by decide) hrc hru hrv hcont
    refine ⟨{q with u := (subCarry384 q.u q.v).1, x1 := xnew}, ?_, ?_, ?_⟩
    · unfold BlsInverseLocals.Matches
      simp [hpost, hresult, hlocals, PanRunBounded.resVarEq_lookup,
        HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "u" ≠ ofString "v" by decide,
        show ofString "u" ≠ ofString "x1" by decide,
        show ofString "u" ≠ ofString "x2" by decide,
        show ofString "u" ≠ ofString "ult" by decide,
        show ofString "u" ≠ ofString "d" by decide,
        show ofString "v" ≠ ofString "u" by decide,
        show ofString "v" ≠ ofString "x1" by decide,
        show ofString "v" ≠ ofString "x2" by decide,
        show ofString "v" ≠ ofString "ult" by decide,
        show ofString "v" ≠ ofString "d" by decide,
        show ofString "x1" ≠ ofString "u" by decide,
        show ofString "x1" ≠ ofString "v" by decide,
        show ofString "x1" ≠ ofString "x2" by decide,
        show ofString "x1" ≠ ofString "ult" by decide,
        show ofString "x1" ≠ ofString "d" by decide,
        show ofString "x2" ≠ ofString "u" by decide,
        show ofString "x2" ≠ ofString "v" by decide,
        show ofString "x2" ≠ ofString "x1" by decide,
        show ofString "x2" ≠ ofString "ult" by decide,
        show ofString "x2" ≠ ofString "d" by decide,
        show ofString "ult" ≠ ofString "u" by decide,
        show ofString "ult" ≠ ofString "v" by decide,
        show ofString "ult" ≠ ofString "x1" by decide,
        show ofString "ult" ≠ ofString "x2" by decide,
        show ofString "ult" ≠ ofString "d" by decide,
        show ofString "d" ≠ ofString "u" by decide,
        show ofString "d" ≠ ofString "v" by decide,
        show ofString "d" ≠ ofString "x1" by decide,
        show ofString "d" ≠ ofString "x2" by decide,
        show ofString "d" ≠ ofString "ult" by decide, hu, hv, hx1, hx2]
    · simpa [inverseSubtract, show q.v.toNat ≤ q.u.toNat by omega] using
        subCarry384_no_borrow q.u q.v (by omega)
    · simp [inverseSubtract, show q.v.toNat ≤ q.u.toNat by omega]

private def decCallBody : ProgHOL 64 → ProgHOL 64
  | .decCall _ _ _ _ body => body | _ => .skip
private def decBody : ProgHOL 64 → ProgHOL 64
  | .dec _ _ _ body => body | _ => .skip
private def seqLeft : ProgHOL 64 → ProgHOL 64
  | .seq body _ => body | _ => .skip
private def seqRight : ProgHOL 64 → ProgHOL 64
  | .seq _ body => body | _ => .skip
private def whileBody : ProgHOL 64 → ProgHOL 64
  | .while _ body => body | _ => .skip

def blsInverseOuterLoop : ProgHOL 64 :=
  seqLeft (decBody (decBody (decBody (decBody (seqRight
    (decCallBody (arithSourceBody Guest.Software.guestFn_bls_fp_inv_raw)))))))
def blsInverseOuterBody : ProgHOL 64 := whileBody blsInverseOuterLoop

def blsInverseUHalfLoop : ProgHOL 64 := seqLeft (seqRight (seqRight blsInverseOuterBody))
def blsInverseVHalfLoop : ProgHOL 64 := seqLeft (seqRight (seqRight (seqRight blsInverseOuterBody)))

theorem blsInverseOuterLoop_eq : blsInverseOuterLoop = .while (.const 1) blsInverseOuterBody := rfl

theorem blsInverseUHalfLoop_eq : blsInverseUHalfLoop =
    .while (inverseEvenExpr (ofString "u")) (blsHalfStep (ofString "u") (ofString "x1")) := rfl

theorem blsInverseVHalfLoop_eq : blsInverseVHalfLoop =
    .while (inverseEvenExpr (ofString "v")) (blsHalfStep (ofString "v") (ofString "x2")) := rfl

def blsInverseExitCheck (counter coefficient : MlS) : ProgHOL 64 :=
  .ite (.cmp .equal (.op .or [.rfield 1 (.var .local counter),
    .rfield 2 (.var .local counter), .rfield 3 (.var .local counter),
    .rfield 4 (.var .local counter), .rfield 5 (.var .local counter)]) (.const 0))
    (.ite (.cmp .equal (.rfield 0 (.var .local counter)) (.const 1))
      (.return (.var .local coefficient)) .skip) .skip

theorem blsInverseExitCheck_passive (counter coefficient : MlS) :
    NoChangeOnNone (blsInverseExitCheck counter coefficient) :=
  NoChangeOnNone.ite _ (NoChangeOnNone.ite _ (NoChangeOnNone.ret _) NoChangeOnNone.skip) NoChangeOnNone.skip

theorem blsInverseOuterBody_eq : blsInverseOuterBody =
    .seq (blsInverseExitCheck (ofString "u") (ofString "x1"))
      (.seq (blsInverseExitCheck (ofString "v") (ofString "x2"))
        (.seq blsInverseUHalfLoop (.seq blsInverseVHalfLoop blsInverseSubtractTail))) := rfl

theorem blsInverseOuterBody_not_continue {F : Type} (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s blsInverseOuterBody).1 ≠ some .continue :=
  evaluate_noTopContinue blsInverseOuterBody (by decide) s
end InitECandidate.Solver.Wave8GuestInv.Arith
