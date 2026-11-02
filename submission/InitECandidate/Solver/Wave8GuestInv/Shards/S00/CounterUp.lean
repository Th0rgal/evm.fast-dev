import InitECandidate.Solver.PanTerminatingCombinators
import InitECandidate.Solver.Wave8GuestInv.Shards.S00.LightSpec

/-! Copied from wave8/leaves-arith-astra at 506c16a5c77088d70988c91e8a2473c05867ddf9, CounterUp.lean.
Only local import paths changed. -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Solver.Wave8Leaves.S00Spec.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanTerminatingCombinators
open Flapjack.Compiler.Encoders.Asm

/-- Semantic counter effect on iterations which continue the enclosing loop. -/
def CounterAdd (counter : MlS) (step : BitVec 64) (body : ProgHOL 64) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (w : BitVec 64),
    s.locals.lookup counter = some (.val (.word w)) →
    let out := evaluateHOLFiniteState s body
    (out.1 = none ∨ out.1 = some .continue) →
    out.2.locals.lookup counter = some (.val (.word (w + step)))

theorem CounterAdd.assign (counter : MlS) (step : BitVec 64) :
    CounterAdd counter step (.assign .local counter (.op .add [.var .local counter, .const step])) := by
  intro F s w hlocal
  have run : evaluateHOLFiniteState s
      (.assign .local counter (.op .add [.var .local counter, .const step])) =
      (none, setVarHOLFinite counter (.val (.word (w + step))) s) := by
    simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact,
      hlocal, wordOpHOL, wordOp, valueIsWord, valueWord,
      lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
      shapeOfHOLExact, shapeEqHOL]
  rw [run]
  simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

theorem CounterAdd.seq (counter : MlS) (step : BitVec 64) (first : ProgHOL 64)
    {rest : ProgHOL 64} (havoid : avoidsLocal counter first = true)
    (hnocont : noTopContinue first = true) (hrest : CounterAdd counter step rest) :
    CounterAdd counter step (.seq first rest) := by
  intro F s w hlocal
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780]
  cases hrun : evaluateHOLFiniteState s first with
  | mk r mid =>
    have hkeep := evaluate_avoidsLocal_flowing counter first havoid s
    have hnc := evaluate_noTopContinue first hnocont s
    rw [hrun] at hkeep hnc
    cases r with
    | none =>
      dsimp only at hkeep ⊢
      exact hrest mid w ((hkeep (Or.inl rfl)).trans hlocal)
    | some result =>
      dsimp only at hnc ⊢
      intro hflow
      rcases hflow with h | h
      · cases h
      · exact False.elim (hnc h)

theorem CounterAdd.dec (counter : MlS) (step : BitVec 64) (name : MlS)
    (shape : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64}
    (hne : counter ≠ name) (hbody : CounterAdd counter step body) :
    CounterAdd counter step (.dec name shape init body) := by
  intro F s w hlocal
  dsimp only
  intro hflow
  cases hrun : evaluateHOLFiniteState s (.dec name shape init body) with
  | mk result post =>
    rw [hrun] at hflow
    dsimp only at hflow ⊢
    obtain ⟨value, inner, hinner, hrestore⟩ :=
      dec_flowing (hflow.elim Or.inl (fun h => Or.inr (Or.inr h))) hrun
    have hentry : (setVarHOLFinite name value s).locals.lookup counter = some (.val (.word w)) := by
      simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne] using hlocal
    have h := hbody (setVarHOLFinite name value s) w hentry
    dsimp only at h
    rw [hinner] at h
    dsimp only at h
    rw [hrestore, InitECandidate.Solver.PanRunBounded.resVarEq_lookup]
    simpa [hne] using h hflow

theorem CounterAdd.decCall (counter : MlS) (step : BitVec 64) (name : MlS)
    (shape : ShapeHOL) (fname : MlS) (args : List (ExpHOL 64)) {body : ProgHOL 64}
    (hne : counter ≠ name) (hbody : CounterAdd counter step body) :
    CounterAdd counter step (.decCall name shape fname args body) := by
  intro F s w hlocal
  dsimp only
  intro hflow
  cases hrun : evaluateHOLFiniteState s (.decCall name shape fname args body) with
  | mk result post =>
    rw [hrun] at hflow
    dsimp only at hflow ⊢
    obtain ⟨value, resumed, inner, hpres, hclock, hinner, hrestore⟩ :=
      decCall_flowing (hflow.elim Or.inl (fun h => Or.inr (Or.inr h))) hrun
    have h := hbody resumed w ((hpres counter hne).trans hlocal)
    dsimp only at h
    rw [hinner] at h
    dsimp only at h
    rw [hrestore, InitECandidate.Solver.PanRunBounded.resVarEq_lookup]
    simpa [hne] using h hflow

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

theorem cmp_counter_active {F : Type} (s : PanSemStateFiniteExact 64 F)
    (counter : MlS) (op : Cmp) (bound : ExpHOL 64) (result : BitVec 64)
    (hc : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp op (.var .local counter) bound) = some (.val (.word result)))
    (hnz : result ≠ 0) :
    ∃ w v : BitVec 64, s.locals.lookup counter = some (.val (.word w)) ∧
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) bound = some (.val (.word v)) ∧
      wordCmpHOL op w v = true := by
  rw [evalHOLFinite_cmp, evalHOLFinite_var_local] at hc
  split at hc
  · rename_i w v hl hr
    refine ⟨w, v, hl, hr, ?_⟩
    by_cases hcmp : wordCmpHOL op w v = true
    · exact hcmp
    · simp [hcmp] at hc
      subst result
      exact False.elim (hnz rfl)
  · simp at hc

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
theorem while_up_signed (counter : MlS) (step : BitVec 64) (bound : ExpHOL 64)
    {body : ProgHOL 64} {B : Nat} (hbody : TerminatingProgBounded body B)
    (hadd : CounterAdd counter step body) (hstep : 0 < step.toInt)
    (hbound : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : BitVec 64),
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) bound = some (.val (.word v)) →
      v.toInt + step.toInt ≤ 9223372036854775808) :
    TerminatingProgBounded (.while (.cmp .less (.var .local counter) bound) body)
      ((2 ^ 64 + 1) * (B + 1)) := by
  apply TerminatingProgBounded.while_step (signedUpRank counter)
  · apply while_step_of_progBounded (signedUpRank counter) _ hbody
    intro F s result hcode hcond hnz hclk
    dsimp only
    intro hflow
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
  · exact signedUpRank_le counter

theorem while_up_signed_one (counter : MlS) (bound : ExpHOL 64)
    {body : ProgHOL 64} {B : Nat} (hbody : TerminatingProgBounded body B)
    (hadd : CounterAdd counter 1 body) :
    TerminatingProgBounded (.while (.cmp .less (.var .local counter) bound) body)
      ((2 ^ 64 + 1) * (B + 1)) := by
  apply while_up_signed counter 1 bound hbody hadd (by decide)
  intro F s v hv
  have := BitVec.toInt_le (x := v)
  have hone : (1 : BitVec 64).toInt = 1 := by decide
  rw [hone]
  omega

private def unsignedUpRank (counter : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup counter with
  | some (.val (.word w)) => 18446744073709551615 - w.toNat
  | _ => 0

private theorem unsignedUpRank_le (counter : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) :
    unsignedUpRank counter s ≤ 2 ^ 64 := by
  unfold unsignedUpRank
  split <;> omega

theorem while_up_unsigned_one (counter : MlS) (bound : ExpHOL 64)
    {body : ProgHOL 64} {B : Nat} (hbody : TerminatingProgBounded body B)
    (hadd : CounterAdd counter 1 body) :
    TerminatingProgBounded (.while (.cmp .lower (.var .local counter) bound) body)
      ((2 ^ 64 + 1) * (B + 1)) := by
  apply TerminatingProgBounded.while_step (unsignedUpRank counter)
  · apply while_step_of_progBounded (unsignedUpRank counter) _ hbody
    intro F s result hcode hcond hnz hclk
    dsimp only
    intro hflow
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
  · exact unsignedUpRank_le counter

#print axioms while_up_signed_one
#print axioms while_up_unsigned_one
end InitECandidate.Solver.Wave8Leaves.S00Spec.Arith
