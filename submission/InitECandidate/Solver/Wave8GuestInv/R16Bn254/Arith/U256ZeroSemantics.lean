import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.ReturnedFacts
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.BlsCallFacts

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

theorem limbs256_zero_iff (a : Limbs256) :
    a.toNat = 0 ↔ a.l0 = 0#64 ∧ a.l1 = 0#64 ∧ a.l2 = 0#64 ∧ a.l3 = 0#64 := by
  constructor
  · intro h
    have h0 : a.l0.toNat = 0 := by dsimp [Limbs256.toNat] at h; omega
    have h1 : a.l1.toNat = 0 := by dsimp [Limbs256.toNat] at h; omega
    have h2 : a.l2.toNat = 0 := by dsimp [Limbs256.toNat] at h; omega
    have h3 : a.l3.toNat = 0 := by dsimp [Limbs256.toNat] at h; omega
    exact ⟨BitVec.toNat_inj.mp h0, BitVec.toNat_inj.mp h1,
      BitVec.toNat_inj.mp h2, BitVec.toNat_inj.mp h3⟩
  · rintro ⟨h0,h1,h2,h3⟩
    simp [Limbs256.toNat,h0,h1,h2,h3]

theorem eval_u256_is_zero_body {F : Type} (s : PanSemStateFiniteExact 64 F) (a : Limbs256)
    (ha : s.locals.lookup (ofString "a") = some a.toValue) :
    evaluateHOLFiniteState s (arithSourceBody Guest.Software.guestFn_u256_is_zero) =
      (some (.returned (.val (.word (if a.toNat = 0 then 1 else 0)))), emptyLocalsHOLFinite s) := by
  have hb : arithSourceBody Guest.Software.guestFn_u256_is_zero =
      .seq (.ite (.cmp .equal (.op .or [.rfield 0 (.var .local (ofString "a")),
        .rfield 1 (.var .local (ofString "a")), .rfield 2 (.var .local (ofString "a")),
        .rfield 3 (.var .local (ofString "a"))]) (.const 0)) (.return (.const 1)) .skip)
        (.return (.const 0)) := rfl
  rw [hb]
  by_cases hz : a.toNat = 0
  · have hh := (limbs256_zero_iff a).mp hz
    simp [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, evaluateHOLFiniteState_return,
      evalHOLExact, evalListHOLExact, ha, Limbs256.toValue, wordOpHOL, wordOp, valueIsWord,
      valueWord, OrOp.or, Compiler.Encoders.Asm.wordCmpHOL, hz, hh.1, hh.2.1, hh.2.2.1, hh.2.2.2,
      shapeOfHOLExact, sizeOfShapeWithContextHOL]
  · have hh : ¬ (a.l0 = 0#64 ∧ a.l1 = 0#64 ∧ a.l2 = 0#64 ∧ a.l3 = 0#64) := fun h => hz ((limbs256_zero_iff a).mpr h)
    simp [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, evaluateHOLFiniteState_return,
      evaluateHOLFiniteState_skip, evalHOLExact, evalListHOLExact, ha, Limbs256.toValue,
      wordOpHOL, wordOp, valueIsWord, valueWord, OrOp.or, Compiler.Encoders.Asm.wordCmpHOL,
      BitVec.or_eq_zero_iff, hz, hh, shapeOfHOLExact, sizeOfShapeWithContextHOL]

theorem arith_lookup_u256_is_zero :
    originalRuntimeCode.lookup (ofString "u256_is_zero") =
      some ([(ofString "a", arithU256Shape)], arithSourceBody Guest.Software.guestFn_u256_is_zero, .one) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 42 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_is_zero) rfl

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
