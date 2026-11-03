import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.BlsHalfStep
import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.WhileTrap

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanTerminatingCombinators

def blsZeroTrap (counter coefficient : MlS) {F : Type}
    (s : PanSemStateFiniteExact 64 F) : Prop :=
  s.code = originalRuntimeCode ∧ ∃ a x : Limbs384,
    s.locals.lookup counter = some a.toValue ∧ a.toNat = 0 ∧
    s.locals.lookup coefficient = some x.toValue

theorem while_bls_half_zero {F : Type} (s : PanSemStateFiniteExact 64 F)
    (counter coefficient : MlS) (hcx : counter ≠ coefficient)
    (hp : blsZeroTrap counter coefficient s) :
    (evaluateHOLFiniteState s (.while (inverseEvenExpr counter) (blsHalfStep counter coefficient))).1 =
      some .timeOut := by
  apply while_timeout_of_trap (blsZeroTrap counter coefficient) _ _ _ _ _ s hp
  · intro t ht; exact ht
  · intro t ht
    obtain ⟨hc, a, x, ha, hz, hx⟩ := ht
    refine ⟨1, ?_, by decide⟩
    change arithEval t (inverseEvenExpr counter) = _
    rw [blsEvenExpr_eval t counter a ha]
    simp [hz]
  · intro t ht
    obtain ⟨hc, a, x, ha, hz, hx⟩ := ht
    rcases blsHalfStep_typed t counter coefficient a x hcx hc ha hx with ht | ⟨r, hn, hl⟩
    · exact Or.inl ht
    · refine Or.inr ⟨hn, (evalP_code t (blsHalfStep counter coefficient)).trans hc,
        half384 a, r, ?_, ?_, ?_⟩
      · rw [hl]
        simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hcx]
      · rw [half384_toNat, hz]
      · rw [hl]
        simp [HolFiniteMapExact.lookup_update, FUPDATE]

def blsHalfPositive (counter coefficient : MlS) {F : Type}
    (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ a x : Limbs384, s.locals.lookup counter = some a.toValue ∧ 0 < a.toNat ∧
    s.locals.lookup coefficient = some x.toValue

def blsHalfRank (counter : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup counter with
  | some (.rStruct [.val (.word a), .val (.word b), .val (.word c),
      .val (.word d), .val (.word e), .val (.word f)]) =>
    (Limbs384.mk a b c d e f).toNat.size
  | _ => 0

theorem blsHalfRank_lookup {F : Type} (s : PanSemStateFiniteExact 64 F)
    (counter : MlS) (a : Limbs384) (ha : s.locals.lookup counter = some a.toValue) :
    blsHalfRank counter s = a.toNat.size := by
  simp [blsHalfRank, ha, Limbs384.toValue]

theorem while_bls_half_positive (counter coefficient : MlS) (hcx : counter ≠ coefficient) :
    TerminatingProgBoundedOn (blsHalfPositive counter coefficient)
      (.while (inverseEvenExpr counter) (blsHalfStep counter coefficient))
      ((384 + 1) * (blsHalfStepCost + 1)) := by
  have hs : LoopStep (blsHalfRank counter) (inverseEvenExpr counter)
      (blsHalfStep counter coefficient) blsHalfStepCost (blsHalfPositive counter coefficient) := by
    apply while_step_of_progBoundedOn (blsHalfPositive counter coefficient) (blsHalfRank counter) _
      (fun s hc _ => blsHalfStep_bound counter coefficient s hc) (fun _ hp => hp)
    intro F s word hc hp hcond hnz hclock
    dsimp only
    intro hflow
    obtain ⟨a, x, ha, hpos, hx⟩ := hp
    have he := blsEvenExpr_eval s counter a ha
    change arithEval s (inverseEvenExpr counter) = some (.val (.word word)) at hcond
    rw [he] at hcond
    have heven : a.toNat % 2 = 0 := by
      by_contra hodd
      simp only [if_neg hodd, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hcond
      exact hnz hcond.symm
    rcases blsHalfStep_typed (decClockHOLFinite s) counter coefficient a x hcx hc ha hx with ht | ⟨r, hn, hl⟩
    · rcases hflow with hf | hf <;> rw [ht] at hf <;> cases hf
    · have hpa : (evaluateHOLFiniteState (decClockHOLFinite s) (blsHalfStep counter coefficient)).2.locals.lookup counter =
          some (half384 a).toValue := by
        rw [hl]
        simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hcx]
      have hpx : (evaluateHOLFiniteState (decClockHOLFinite s) (blsHalfStep counter coefficient)).2.locals.lookup coefficient =
          some r.toValue := by
        rw [hl]
        simp [HolFiniteMapExact.lookup_update, FUPDATE]
      refine ⟨?_, half384 a, r, hpa, half384_positive_of_even a hpos heven, hpx⟩
      rw [blsHalfRank_lookup _ counter _ hpa, blsHalfRank_lookup s counter a ha]
      exact half384_size_lt a hpos
  intro F s hc hp
  apply TerminatingProgBoundedOn.while_measure (blsHalfRank counter) _ _ hs s hc
  refine ⟨hp, ?_⟩
  obtain ⟨a, x, ha, _, _⟩ := hp
  rw [blsHalfRank_lookup s counter a ha]
  exact Nat.size_le.mpr a.toNat_lt

theorem while_bls_half_typed (counter coefficient : MlS) (hcx : counter ≠ coefficient) :
    TerminatingProgBoundedOn (blsHalfTyped counter coefficient)
      (.while (inverseEvenExpr counter) (blsHalfStep counter coefficient))
      ((384 + 1) * (blsHalfStepCost + 1)) := by
  intro F s hc hp hnt
  obtain ⟨a, x, ha, hx⟩ := hp
  by_cases hz : a.toNat = 0
  · exact False.elim (hnt (while_bls_half_zero s counter coefficient hcx ⟨hc, a, x, ha, hz, hx⟩))
  · exact while_bls_half_positive counter coefficient hcx s hc ⟨a, x, ha, by omega, hx⟩ hnt
end InitECandidate.Solver.Wave8GuestInv.Arith
