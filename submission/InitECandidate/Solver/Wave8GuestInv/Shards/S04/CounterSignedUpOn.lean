-- Copied from origin/wave8/leaves-arith-astra (506c16a5c77088d70988c91e8a2473c05867ddf9), CounterSignedUpOn.lean.
import InitECandidate.Solver.Wave8GuestInv.Shards.S04.Light
import InitECandidate.Solver.Wave8GuestInv.Shards.S04.CounterEffects

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Solver.Wave8Leaves.S04.Light.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanTerminatingCombinators
open Flapjack.Compiler.Encoders.Asm

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

private def signedUpRank (counter : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup counter with
  | some (.val (.word w)) => (9223372036854775807 - w.toInt).toNat
  | _ => 0

private theorem signedUpRank_le (counter : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) :
    signedUpRank counter s ≤ 2 ^ 64 := by
  unfold signedUpRank
  split
  · rename_i w h
    have := BitVec.le_toInt w
    omega
  · omega

/-- Signed increasing-counter loop. The bound-expression hypothesis prevents
signed overflow; step 1 works for every word-valued upper bound. -/
theorem while_up_signed_on (counter : MlS) (step : BitVec 64) (bound : ExpHOL 64)
    {body : ProgHOL 64} {B : Nat} (hbody : TerminatingProgBoundedOn GuestInv body B)
    (hadd : CounterAdd counter step body) (hstep : 0 < step.toInt)
    (hbound : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : BitVec 64),
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) bound = some (.val (.word v)) →
      v.toInt + step.toInt ≤ 9223372036854775808) :
    TerminatingProgBoundedOn GuestInv (.while (.cmp .less (.var .local counter) bound) body)
      ((2 ^ 64 + 1) * (B + 1)) := by
  have hentry : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), GuestInv s → GuestInv (decClockHOLFinite s) :=
    fun s h => guestInv_congr (s := s) rfl rfl rfl rfl h
  have hs : LoopStep (signedUpRank counter) (.cmp .less (.var .local counter) bound) body B GuestInv := by
    apply while_step_of_progBoundedOn GuestInv (signedUpRank counter) _ hbody hentry
    intro F s result hcode hguest hcond hnz hclk
    dsimp only
    intro hflow
    refine ⟨?_, guestInv_evaluate (decClockHOLFinite s) body (hentry s hguest)⟩
    obtain ⟨w, v, hl, hv, hcmp⟩ := cmp_counter_active s counter .less bound result hcond hnz
    have hlt : w.toInt < v.toInt := by
      simpa only [wordCmpHOL, signed_less_eq, BitVec.slt_iff_toInt_lt] using hcmp
    have hlim := hbound s v hv
    have hwmin := BitVec.le_toInt w
    have hwmax := BitVec.toInt_le (x := w)
    have hnext : (w + step).toInt = w.toInt + step.toInt := by
      rw [BitVec.toInt_add]
      apply Int.bmod_eq_of_le <;> omega
    have hl' : (decClockHOLFinite s).locals.lookup counter = some (.val (.word w)) := hl
    have heffect := hadd (decClockHOLFinite s) w hl' hflow
    simp only [signedUpRank, heffect, hl, hnext]
    omega
  intro F s hcode hguest
  exact TerminatingProgBoundedOn.while_measure (signedUpRank counter) _ _ hs s hcode
    ⟨hguest, signedUpRank_le counter s⟩

theorem while_up_signed_one_on (counter : MlS) (bound : ExpHOL 64)
    {body : ProgHOL 64} {B : Nat} (hbody : TerminatingProgBoundedOn GuestInv body B)
    (hadd : CounterAdd counter 1 body) :
    TerminatingProgBoundedOn GuestInv (.while (.cmp .less (.var .local counter) bound) body)
      ((2 ^ 64 + 1) * (B + 1)) := by
  apply while_up_signed_on counter 1 bound hbody hadd (by decide)
  intro F s v hv
  have := BitVec.toInt_le (x := v)
  have hone : (1 : BitVec 64).toInt = 1 := by decide
  rw [hone]
  omega


end InitECandidate.Solver.Wave8Leaves.S04.Light.Arith
