import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.CounterOn

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanTerminatingCombinators
open Flapjack.Compiler.Encoders.Asm

private def constUpRank (counter : MlS) (limit : BitVec 64) {F : Type}
    (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup counter with
  | some (.val (.word w)) => limit.toNat - w.toNat
  | _ => 0

/-- An unsigned literal guard gives a small bound even from arbitrary loop-entry
locals: a counter already at or above the limit does not enter the body. -/
theorem while_up_unsigned_const_on (counter : MlS) (limit : BitVec 64)
    {body : ProgHOL 64} {B : Nat} (hbody : TerminatingProgBoundedOn GuestInv body B)
    (hadd : CounterAdd counter 1 body) :
    TerminatingProgBoundedOn GuestInv (.while (.cmp .lower (.var .local counter) (.const limit)) body)
      ((limit.toNat + 1) * (B + 1)) := by
  have hentry : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), GuestInv s → GuestInv (decClockHOLFinite s) :=
    fun s h => guestInv_congr (s := s) rfl rfl rfl rfl h
  have hs : LoopStep (constUpRank counter limit) (.cmp .lower (.var .local counter) (.const limit)) body B GuestInv := by
    apply while_step_of_progBoundedOn GuestInv (constUpRank counter limit) _ hbody hentry
    intro F s result hcode hguest hcond hnz hclk
    dsimp only
    intro hflow
    refine ⟨?_, guestInv_evaluate (decClockHOLFinite s) body (hentry s hguest)⟩
    obtain ⟨w, v, hl, hv, hcmp⟩ := cmp_counter_active s counter .lower (.const limit) result hcond hnz
    have hvlim : v = limit := by
      simpa only [evalHOLFinite_const, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] using hv.symm
    subst v
    have hlt : w.toNat < limit.toNat := by
      simpa only [wordCmpHOL, decide_eq_true_eq, BitVec.lt_def] using hcmp
    have hvmax := limit.isLt
    have hone : (1 : BitVec 64).toNat = 1 := by decide
    have hnext : (w + 1).toNat = w.toNat + 1 := by
      rw [BitVec.toNat_add, hone]
      apply Nat.mod_eq_of_lt
      omega
    have hl' : (decClockHOLFinite s).locals.lookup counter = some (.val (.word w)) := hl
    have heffect := hadd (decClockHOLFinite s) w hl' hflow
    simp only [constUpRank, heffect, hl, hnext]
    omega
  intro F s hcode hguest
  apply TerminatingProgBoundedOn.while_measure (constUpRank counter limit) _ _ hs s hcode
  refine ⟨hguest, ?_⟩
  unfold constUpRank
  split <;> omega


private def unsignedUpRank (counter : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup counter with
  | some (.val (.word w)) => 18446744073709551615 - w.toNat
  | _ => 0

private theorem unsignedUpRank_le (counter : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) :
    unsignedUpRank counter s ≤ 2 ^ 64 := by
  unfold unsignedUpRank
  split <;> omega

theorem while_up_unsigned_one_on (counter : MlS) (bound : ExpHOL 64)
    {body : ProgHOL 64} {B : Nat} (hbody : TerminatingProgBoundedOn GuestInv body B)
    (hadd : CounterAdd counter 1 body) :
    TerminatingProgBoundedOn GuestInv (.while (.cmp .lower (.var .local counter) bound) body)
      ((2 ^ 64 + 1) * (B + 1)) := by
  have hentry : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), GuestInv s → GuestInv (decClockHOLFinite s) :=
    fun s h => guestInv_congr (s := s) rfl rfl rfl rfl h
  have hs : LoopStep (unsignedUpRank counter) (.cmp .lower (.var .local counter) bound) body B GuestInv := by
    apply while_step_of_progBoundedOn GuestInv (unsignedUpRank counter) _ hbody hentry
    intro F s result hcode hguest hcond hnz hclk
    dsimp only
    intro hflow
    refine ⟨?_, guestInv_evaluate (decClockHOLFinite s) body (hentry s hguest)⟩
    obtain ⟨w, v, hl, hv, hcmp⟩ := cmp_counter_active s counter .lower bound result hcond hnz
    have hlt : w.toNat < v.toNat := by
      simpa only [wordCmpHOL, decide_eq_true_eq, BitVec.lt_def] using hcmp
    have hvmax := v.isLt
    have hone : (1 : BitVec 64).toNat = 1 := by decide
    have hnext : (w + 1).toNat = w.toNat + 1 := by
      rw [BitVec.toNat_add, hone]
      apply Nat.mod_eq_of_lt
      omega
    have hl' : (decClockHOLFinite s).locals.lookup counter = some (.val (.word w)) := hl
    have heffect := hadd (decClockHOLFinite s) w hl' hflow
    simp only [unsignedUpRank, heffect, hl, hnext]
    omega
  intro F s hcode hguest
  exact TerminatingProgBoundedOn.while_measure (unsignedUpRank counter) _ _ hs s hcode
    ⟨hguest, unsignedUpRank_le counter s⟩


end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
