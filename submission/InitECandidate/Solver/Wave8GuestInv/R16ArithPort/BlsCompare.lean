import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.BlsArithmetic
import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.U256Semantics

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The exact high-to-low six-word source comparison. -/
def lt384 (a b : Limbs384) : Bool :=
  if a.l5 = b.l5 then (if a.l4 = b.l4 then (if a.l3 = b.l3 then (if a.l2 = b.l2 then (if a.l1 = b.l1 then (decide (a.l0.toNat < b.l0.toNat)) else decide (a.l1.toNat < b.l1.toNat)) else decide (a.l2.toNat < b.l2.toNat)) else decide (a.l3.toNat < b.l3.toNat)) else decide (a.l4.toNat < b.l4.toNat)) else decide (a.l5.toNat < b.l5.toNat)

theorem lt384_correct (a b : Limbs384) : lt384 a b = decide (a.toNat < b.toNat) := by
  have ha0 := a.l0.isLt
  have ha1 := a.l1.isLt
  have ha2 := a.l2.isLt
  have ha3 := a.l3.isLt
  have ha4 := a.l4.isLt
  have ha5 := a.l5.isLt
  have hb0 := b.l0.isLt
  have hb1 := b.l1.isLt
  have hb2 := b.l2.isLt
  have hb3 := b.l3.isLt
  have hb4 := b.l4.isLt
  have hb5 := b.l5.isLt
  simp only [lt384, ← BitVec.toNat_inj]
  split_ifs <;> rw [decide_eq_decide] <;>
    dsimp only [Limbs384.toNat] <;> omega

theorem eval_bls_fp_lt_raw_body {F : Type}
    (s : PanSemStateFiniteExact 64 F) (a b : Limbs384)
    (ha : s.locals.lookup (ofString "a") = some a.toValue)
    (hb : s.locals.lookup (ofString "b") = some b.toValue) :
    evaluateHOLFiniteState s (arithSourceBody Guest.Software.guestFn_bls_fp_lt_raw) =
      (some (.returned (.val (.word (if lt384 a b then 1 else 0)))), emptyLocalsHOLFinite s) := by
  have hbody : arithSourceBody Guest.Software.guestFn_bls_fp_lt_raw = (.seq (.ite (.cmp .notEqual (.rfield 5 (.var .local (ofString "a"))) (.rfield 5 (.var .local (ofString "b")))) (.seq (.ite (.cmp .lower (.rfield 5 (.var .local (ofString "a"))) (.rfield 5 (.var .local (ofString "b")))) (.return (.const (1#64))) .skip) (.return (.const (0#64)))) .skip) (.seq (.ite (.cmp .notEqual (.rfield 4 (.var .local (ofString "a"))) (.rfield 4 (.var .local (ofString "b")))) (.seq (.ite (.cmp .lower (.rfield 4 (.var .local (ofString "a"))) (.rfield 4 (.var .local (ofString "b")))) (.return (.const (1#64))) .skip) (.return (.const (0#64)))) .skip) (.seq (.ite (.cmp .notEqual (.rfield 3 (.var .local (ofString "a"))) (.rfield 3 (.var .local (ofString "b")))) (.seq (.ite (.cmp .lower (.rfield 3 (.var .local (ofString "a"))) (.rfield 3 (.var .local (ofString "b")))) (.return (.const (1#64))) .skip) (.return (.const (0#64)))) .skip) (.seq (.ite (.cmp .notEqual (.rfield 2 (.var .local (ofString "a"))) (.rfield 2 (.var .local (ofString "b")))) (.seq (.ite (.cmp .lower (.rfield 2 (.var .local (ofString "a"))) (.rfield 2 (.var .local (ofString "b")))) (.return (.const (1#64))) .skip) (.return (.const (0#64)))) .skip) (.seq (.ite (.cmp .notEqual (.rfield 1 (.var .local (ofString "a"))) (.rfield 1 (.var .local (ofString "b")))) (.seq (.ite (.cmp .lower (.rfield 1 (.var .local (ofString "a"))) (.rfield 1 (.var .local (ofString "b")))) (.return (.const (1#64))) .skip) (.return (.const (0#64)))) .skip) (.seq (.ite (.cmp .lower (.rfield 0 (.var .local (ofString "a"))) (.rfield 0 (.var .local (ofString "b")))) (.return (.const (1#64))) .skip) (.return (.const (0#64))))))))) := rfl
  rw [hbody]
  by_cases h5 : a.l5 = b.l5
  ·
    by_cases h4 : a.l4 = b.l4
    ·
      by_cases h3 : a.l3 = b.l3
      ·
        by_cases h2 : a.l2 = b.l2
        ·
          by_cases h1 : a.l1 = b.l1
          ·
            by_cases hl : a.l0.toNat < b.l0.toNat <;>
              simp [lt384, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite,
      evaluateHOLFiniteState_return, evaluateHOLFiniteState_skip,
      evalHOLExact, Limbs384.toValue, ha, hb, Compiler.Encoders.Asm.wordCmpHOL,
      BitVec.ult, BitVec.lt_def, BitVec.le_def, shapeOfHOLExact, sizeOfShapeWithContextHOL, h5, h4, h3, h2, h1, hl]
          · by_cases hl : a.l1.toNat < b.l1.toNat <;>
              simp [lt384, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite,
      evaluateHOLFiniteState_return, evaluateHOLFiniteState_skip,
      evalHOLExact, Limbs384.toValue, ha, hb, Compiler.Encoders.Asm.wordCmpHOL,
      BitVec.ult, BitVec.lt_def, BitVec.le_def, shapeOfHOLExact, sizeOfShapeWithContextHOL, h5, h4, h3, h2, h1, hl]
        · by_cases hl : a.l2.toNat < b.l2.toNat <;>
            simp [lt384, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite,
      evaluateHOLFiniteState_return, evaluateHOLFiniteState_skip,
      evalHOLExact, Limbs384.toValue, ha, hb, Compiler.Encoders.Asm.wordCmpHOL,
      BitVec.ult, BitVec.lt_def, BitVec.le_def, shapeOfHOLExact, sizeOfShapeWithContextHOL, h5, h4, h3, h2, hl]
      · by_cases hl : a.l3.toNat < b.l3.toNat <;>
          simp [lt384, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite,
      evaluateHOLFiniteState_return, evaluateHOLFiniteState_skip,
      evalHOLExact, Limbs384.toValue, ha, hb, Compiler.Encoders.Asm.wordCmpHOL,
      BitVec.ult, BitVec.lt_def, BitVec.le_def, shapeOfHOLExact, sizeOfShapeWithContextHOL, h5, h4, h3, hl]
    · by_cases hl : a.l4.toNat < b.l4.toNat <;>
        simp [lt384, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite,
      evaluateHOLFiniteState_return, evaluateHOLFiniteState_skip,
      evalHOLExact, Limbs384.toValue, ha, hb, Compiler.Encoders.Asm.wordCmpHOL,
      BitVec.ult, BitVec.lt_def, BitVec.le_def, shapeOfHOLExact, sizeOfShapeWithContextHOL, h5, h4, hl]
  · by_cases hl : a.l5.toNat < b.l5.toNat <;>
      simp [lt384, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite,
      evaluateHOLFiniteState_return, evaluateHOLFiniteState_skip,
      evalHOLExact, Limbs384.toValue, ha, hb, Compiler.Encoders.Asm.wordCmpHOL,
      BitVec.ult, BitVec.lt_def, BitVec.le_def, shapeOfHOLExact, sizeOfShapeWithContextHOL, h5, hl]
end InitECandidate.Solver.Wave8GuestInv.Arith
