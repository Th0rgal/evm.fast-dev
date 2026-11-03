import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.P256PositiveBody
import InitECandidate.Solver.PanTerminatingCombinators

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanTerminatingCombinators

attribute [local irreducible] wordAddCarryHOL addCarry256 subCarry256

private theorem signed_less_eq (left right : BitVec 64) :
    holAsmSignedLess left right = left.slt right := by
  have bl := left.isLt
  have br := right.isLt
  simp only [holAsmSignedLess, BitVec.slt_eq_decide, BitVec.toInt_eq_msb_cond,
    BitVec.msb_eq_decide]
  repeat (any_goals first | split)
  all_goals simp_all only [decide_eq_true_eq]
  all_goals apply Bool.eq_iff_iff.mpr
  all_goals simp_all [decide_eq_true_eq]
  all_goals omega


private theorem arith_cmp_active {F : Type} (s : PanSemStateFiniteExact 64 F)
    (op : Cmp) (left right : ExpHOL 64) (result : BitVec 64)
    (hc : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp op left right) = some (.val (.word result)))
    (hnz : result ≠ 0) :
    ∃ w v : BitVec 64,
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) left = some (.val (.word w)) ∧
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) right = some (.val (.word v)) ∧
      wordCmpHOL op w v = true := by
  rw [evalHOLFinite_cmp] at hc
  split at hc
  · rename_i w v hl hr
    refine ⟨w, v, hl, hr, ?_⟩
    by_cases hcmp : wordCmpHOL op w v = true
    · exact hcmp
    · simp [hcmp] at hc
      subst result
      exact False.elim (hnz rfl)
  · simp at hc

private def p256NegativeStateRank {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup (ofString "c"), s.locals.lookup (ofString "r") with
  | some (.val (.word c)), some (.rStruct [.val (.word r0), .val (.word r1), .val (.word r2), .val (.word r3)]) =>
      negativeCarryWordRank c ⟨r0, r1, r2, r3⟩
  | _, _ => 0

private theorem p256NegativeStateRank_bound {F : Type} (s : PanSemStateFiniteExact 64 F) :
    p256NegativeStateRank s ≤ 2 ^ 65 := by
  unfold p256NegativeStateRank
  split
  · exact negativeCarryWordRank_bound _ _
  · omega

private def p256PositiveStateRank {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup (ofString "c"), s.locals.lookup (ofString "r") with
  | some (.val (.word c)), some (.rStruct [.val (.word r0), .val (.word r1), .val (.word r2), .val (.word r3)]) =>
      positiveCarryWordRank c ⟨r0, r1, r2, r3⟩
  | _, _ => 0

private theorem p256PositiveStateRank_bound {F : Type} (s : PanSemStateFiniteExact 64 F) :
    p256PositiveStateRank s ≤ 2 ^ 64 := by
  unfold p256PositiveStateRank
  split
  · exact positiveCarryWordRank_bound _ _
  · omega

private theorem p256NegativeBody_bound : TerminatingProgBounded p256NegativeBody 1 := by
  exact TerminatingProgBounded.decCall ub_u256_add_carry _ _ _
    (TerminatingProgBounded.straight _ rfl)

private theorem p256PositiveBody_bound : TerminatingProgBounded p256PositiveBody 2 := by
  exact TerminatingProgBounded.decCall ub_u256_lt _ _ _
    (TerminatingProgBounded.seq (TerminatingProgBounded.call ub_u256_sub _ _)
      (TerminatingProgBounded.straight _ rfl))

theorem p256NegativeLoop_bound :
    TerminatingProgBounded (.while (.cmp .less (.var .local (ofString "c")) (.const 0)) p256NegativeBody)
      ((2 ^ 65 + 1) * 2) := by
  apply TerminatingProgBounded.while_step p256NegativeStateRank
  · apply while_step_of_progBounded p256NegativeStateRank _ p256NegativeBody_bound
    intro F s result hcode hcond hnz hclk
    dsimp only
    intro hflow
    obtain ⟨w, v, hl, hv, hcmp⟩ := arith_cmp_active s .less _ _ result hcond hnz
    have hz : v = 0 := by
      change some (ValueHOL.val (.word (0 : BitVec 64))) = some (ValueHOL.val (.word v)) at hv
      simpa using hv.symm
    subst v
    rw [evalHOLFinite_var_local] at hl
    have hsign : w.toInt < 0 := by
      simpa only [wordCmpHOL, signed_less_eq, BitVec.slt_iff_toInt_lt,
        show (0 : BitVec 64).toInt = 0 from rfl] using hcmp
    have hnone : (evaluateHOLFiniteState (decClockHOLFinite s) p256NegativeBody).1 = none :=
      hflow.resolve_right (evaluate_noTopContinue p256NegativeBody (by decide) _)
    have hrun : evaluateHOLFiniteState (decClockHOLFinite s) p256NegativeBody =
        (none, (evaluateHOLFiniteState (decClockHOLFinite s) p256NegativeBody).2) := Prod.ext hnone rfl
    obtain ⟨r, hr, hrpost, hcpost⟩ := p256NegativeBody_none (s := decClockHOLFinite s) hcode hl hrun
    change s.locals.lookup (ofString "r") = some r.toValue at hr
    simpa only [p256NegativeStateRank, hl, hr, hcpost, hrpost, Limbs256.toValue]
      using negativeCarryWordRank_decreases w r hsign
  · exact p256NegativeStateRank_bound
theorem p256PositiveLoop_bound :
    TerminatingProgBounded (.while (.cmp .less (.const 0) (.var .local (ofString "c"))) p256PositiveBody)
      ((2 ^ 64 + 1) * 3) := by
  apply TerminatingProgBounded.while_step p256PositiveStateRank
  · apply while_step_of_progBounded p256PositiveStateRank _ p256PositiveBody_bound
    intro F s result hcode hcond hnz hclk
    dsimp only
    intro hflow
    obtain ⟨w, v, hl, hv, hcmp⟩ := arith_cmp_active s .less _ _ result hcond hnz
    have hz : w = 0 := by
      change some (ValueHOL.val (.word (0 : BitVec 64))) = some (ValueHOL.val (.word w)) at hl
      simpa using hl.symm
    subst w
    rw [evalHOLFinite_var_local] at hv
    have hsign : 0 < v.toInt := by
      simpa only [wordCmpHOL, signed_less_eq, BitVec.slt_iff_toInt_lt,
        show (0 : BitVec 64).toInt = 0 from rfl] using hcmp
    have hnone : (evaluateHOLFiniteState (decClockHOLFinite s) p256PositiveBody).1 = none :=
      hflow.resolve_right (evaluate_noTopContinue p256PositiveBody (by decide) _)
    have hrun : evaluateHOLFiniteState (decClockHOLFinite s) p256PositiveBody =
        (none, (evaluateHOLFiniteState (decClockHOLFinite s) p256PositiveBody).2) := Prod.ext hnone rfl
    obtain ⟨r, hr, hrpost, hcpost⟩ := p256PositiveBody_none (s := decClockHOLFinite s) hcode hv hrun
    change s.locals.lookup (ofString "r") = some r.toValue at hr
    simpa only [p256PositiveStateRank, hv, hr, hcpost, hrpost, Limbs256.toValue, p256Borrow]
      using positiveCarryWordRank_decreases v r hsign
  · exact p256PositiveStateRank_bound
end InitECandidate.Solver.Wave8GuestInv.Arith
