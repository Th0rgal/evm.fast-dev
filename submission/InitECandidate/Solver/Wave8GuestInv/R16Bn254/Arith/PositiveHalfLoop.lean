import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.InverseHalfSemantics
import InitECandidate.Solver.PanTerminatingCombinators

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanTerminatingCombinators

def inversePositive (counter : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ a : Limbs256, s.locals.lookup counter = some a.toValue ∧ 0 < a.toNat

def inverseHalfRank (counter : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup counter with
  | some (.rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) =>
    (Limbs256.mk a b c d).toNat.size
  | _ => 0

theorem inverseHalfRank_lookup {F : Type} (s : PanSemStateFiniteExact 64 F)
    (counter : MlS) (a : Limbs256) (h : s.locals.lookup counter = some a.toValue) :
    inverseHalfRank counter s = a.toNat.size := by
  simp [inverseHalfRank, h, Limbs256.toValue]

theorem while_inverse_half_positive (counter : MlS) {tail : ProgHOL 64} {B : Nat}
    (htail : TerminatingProgBounded tail B) (havoid : avoidsLocal counter tail = true) :
    TerminatingProgBoundedOn (inversePositive counter)
      (.while (inverseEvenExpr counter) (.seq (.assign .local counter (inverseHalfExpr counter)) tail))
      ((256 + 1) * (B + 1)) := by
  have hentry : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      inversePositive counter s → inversePositive counter (decClockHOLFinite s) := fun _ h => h
  have hb : TerminatingProgBounded
      (.seq (.assign .local counter (inverseHalfExpr counter)) tail) B := by
    intro F s hc
    simpa only [Nat.zero_add] using (TerminatingProgBounded.seq
      (TerminatingProgBounded.straight (.assign .local counter (inverseHalfExpr counter)) rfl) htail s hc)
  have hs : LoopStep (inverseHalfRank counter) (inverseEvenExpr counter)
      (.seq (.assign .local counter (inverseHalfExpr counter)) tail) B (inversePositive counter) := by
    apply while_step_of_progBoundedOn (inversePositive counter) (inverseHalfRank counter) _
      (fun s hc _ => hb s hc) hentry
    intro F s word hc hp hcond hnz hclock
    dsimp only
    intro hflow
    obtain ⟨a, hl, ha⟩ := hp
    have he := inverseEvenExpr_eval s counter a hl
    change arithEval s (inverseEvenExpr counter) = some (.val (.word word)) at hcond
    rw [he] at hcond
    have heven : a.toNat % 2 = 0 := by
      by_contra hodd
      simp only [if_neg hodd, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hcond
      exact hnz hcond.symm
    have run1 := inverseHalf_assign (decClockHOLFinite s) counter a hl
    rw [evaluateHOLFiniteState_seq_line780, run1] at hflow ⊢
    dsimp only at hflow ⊢
    have hkeep := evaluate_avoidsLocal_flowing counter tail havoid
      (setVarHOLFinite counter (half256 a).toValue (decClockHOLFinite s))
      (hflow.elim Or.inl (fun h => Or.inr (Or.inr h)))
    have hpost : (evaluateHOLFiniteState
        (setVarHOLFinite counter (half256 a).toValue (decClockHOLFinite s)) tail).2.locals.lookup counter =
        some (half256 a).toValue := by
      simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE] using hkeep
    refine ⟨?_, half256 a, hpost, half256_positive_of_even a ha heven⟩
    rw [inverseHalfRank_lookup _ counter _ hpost, inverseHalfRank_lookup s counter a hl]
    exact half256_size_lt a ha
  intro F s hc hp
  apply TerminatingProgBoundedOn.while_measure (inverseHalfRank counter) _ _ hs s hc
  refine ⟨hp, ?_⟩
  obtain ⟨a, hl, _⟩ := hp
  rw [inverseHalfRank_lookup s counter a hl]
  exact Nat.size_le.mpr a.toNat_lt

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
