import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.ModinvCallCorrect

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 2000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

def fqModulus : Limbs256 :=
  ⟨4332616871279656263,10917124144477883021,13281191951274694749,3486998266802970665⟩

def fqInverseAdjustment : Limbs256 :=
  ⟨12812017116984455391,7129779742913871286,17257524443456604923,2377177743836652868⟩

def limbs256ConstExpr (a : Limbs256) : ExpHOL 64 :=
  .rstruct [.const a.l0, .const a.l1, .const a.l2, .const a.l3]

theorem fqModulus_odd : fqModulus.toNat % 2 = 1 := by decide
theorem fqModulus_gt_one : 1 < fqModulus.toNat := by decide

theorem fqInverseAdjustment_eq :
    fqInverseAdjustment.toNat = 2 ^ 768 % fqModulus.toNat := by decide

def fqInverseTail : ProgHOL 64 :=
  .call none (ofString "fq_mul") [.var .local (ofString "i"), limbs256ConstExpr fqInverseAdjustment]

theorem fqInverse_source_eq : arithSourceBody Guest.Software.guestFn_fq_inv =
    .decCall (ofString "i") arithU256Shape (ofString "modinv_bin")
      [.var .local (ofString "a"), limbs256ConstExpr fqModulus] fqInverseTail := rfl

/-- The actual fq_inv source passes a canonical integer inverse to its final
Montgomery multiplication. This theorem does not yet certify that multiplication. -/
theorem fqInverse_returned_prefix {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (a : Limbs256) (ret : ValueHOL 64) (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup (ofString "a") = some a.toValue) (ha0 : a.toNat ≠ 0)
    (hr : evaluateHOLFiniteState s (arithSourceBody Guest.Software.guestFn_fq_inv) =
      (some (.returned ret), post)) :
    ∃ (x : Limbs256) (resumed inner : PanSemStateFiniteExact 64 F),
      x.toNat < fqModulus.toNat ∧ (a.toNat * x.toNat) % fqModulus.toNat = 1 ∧
      resumed.locals = s.locals.update (ofString "i", x.toValue) ∧ resumed.code = s.code ∧
      evaluateHOLFiniteState resumed fqInverseTail = (some (.returned ret), inner) := by
  rw [fqInverse_source_eq] at hr
  exact modinv_decCall_returned_correct (ofString "i") _ _ a fqModulus ret hc
    (by simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, ha, limbs256ConstExpr, Limbs256.toValue])
    ha0 fqModulus_odd fqModulus_gt_one hr

end InitECandidate.Solver.Wave8GuestInv.Arith
