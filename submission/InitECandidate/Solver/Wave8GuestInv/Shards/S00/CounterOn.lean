import InitECandidate.Solver.Wave8GuestInv.Shards.S00.CounterMore

/-! Copied from wave8/leaves-arith-astra at 506c16a5c77088d70988c91e8a2473c05867ddf9, CounterOn.lean.
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

private def unsignedDownRank (counter : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup counter with
  | some (.val (.word w)) => w.toNat
  | _ => 0

private theorem unsignedDownRank_le (counter : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) :
    unsignedDownRank counter s ≤ 2 ^ 64 := by
  unfold unsignedDownRank
  split
  · rename_i w h
    exact Nat.le_of_lt w.isLt
  · omega

/-- A decrement before a counter-preserving tail decreases the unsigned rank,
for the unsigned-positive guard used by field exponentiation. -/
theorem while_down_first_unsigned_on (counter : MlS) {tail : ProgHOL 64} {B : Nat}
    (htail : TerminatingProgBoundedOn GuestInv tail B)
    (havoid : avoidsLocal counter tail = true) :
    TerminatingProgBoundedOn GuestInv
      (.while (.cmp .lower (.const 0) (.var .local counter))
        (.seq (.assign .local counter (.op .sub [.var .local counter, .const 1])) tail))
      ((2 ^ 64 + 1) * (B + 1)) := by
  have hentry : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), GuestInv s → GuestInv (decClockHOLFinite s) :=
    fun s h => guestInv_congr (s := s) rfl rfl rfl rfl h
  have hs : LoopStep (unsignedDownRank counter)
      (.cmp .lower (.const 0) (.var .local counter))
      (.seq (.assign .local counter (.op .sub [.var .local counter, .const 1])) tail) B GuestInv := by
    have hb : TerminatingProgBoundedOn GuestInv
        (.seq (.assign .local counter (.op .sub [.var .local counter, .const 1])) tail) B := by
      intro F state hcode hguest
      simpa only [Nat.zero_add] using
        (TerminatingProgBoundedOn.seq_guestInv
          (fun s hc _ => TerminatingProgBounded.straight
            (.assign .local counter (.op .sub [.var .local counter, .const 1])) rfl s hc) htail state hcode hguest)
    apply while_step_of_progBoundedOn GuestInv (unsignedDownRank counter)
      (.cmp .lower (.const 0) (.var .local counter)) hb hentry
    intro F s result hcode hguest hcond hnz hclk
    dsimp only
    intro hflow
    refine ⟨?_, guestInv_evaluate (decClockHOLFinite s) _ (hentry s hguest)⟩
    cases hlocal : s.locals.lookup counter with
    | none =>
      rw [evalHOLFinite_eq_toExact] at hcond
      simp [evalHOLExact, hlocal] at hcond
    | some v =>
      cases v with
      | rStruct fields =>
        rw [evalHOLFinite_eq_toExact] at hcond
        simp [evalHOLExact, hlocal] at hcond
      | nStruct name fields =>
        rw [evalHOLFinite_eq_toExact] at hcond
        simp [evalHOLExact, hlocal] at hcond
      | val wv =>
        cases wv with
        | word w =>
          have hw : w ≠ 0 := by
            intro hz
            subst w
            rw [evalHOLFinite_eq_toExact] at hcond
            simp [evalHOLExact, hlocal, Compiler.Encoders.Asm.wordCmpHOL,
              Compiler.Encoders.Asm.holAsmSignedLess] at hcond
            subst result
            exact hnz rfl
          have run1 : evaluateHOLFiniteState (decClockHOLFinite s)
              (.assign .local counter (.op .sub [.var .local counter, .const 1])) =
              (none, setVarHOLFinite counter (.val (.word (w - 1))) (decClockHOLFinite s)) := by
            simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact,
              decClockHOLFinite, hlocal, wordOpHOL, wordOp, valueIsWord, valueWord,
              lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
              shapeOfHOLExact, shapeEqHOL]
          rw [evaluateHOLFiniteState_seq_line780, run1] at hflow ⊢
          dsimp only at hflow ⊢
          have hkeep := evaluate_avoidsLocal_flowing counter tail havoid
            (setVarHOLFinite counter (.val (.word (w - 1))) (decClockHOLFinite s))
            (hflow.elim Or.inl (fun h => Or.inr (Or.inr h)))
          have hlookup : (evaluateHOLFiniteState
              (setVarHOLFinite counter (.val (.word (w - 1))) (decClockHOLFinite s)) tail).2.locals.lookup counter =
              some (.val (.word (w - 1))) := by
            simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE] using hkeep
          simp only [unsignedDownRank, hlookup, hlocal]
          have hwpos : 0 < w.toNat := by
            have : w.toNat ≠ 0 := by
              intro h
              apply hw
              apply BitVec.toNat_inj.mp
              have hz : (0 : BitVec 64).toNat = 0 := by decide
              rw [hz]
              exact h
            omega
          rw [BitVec.toNat_sub]
          change (18446744073709551615 + w.toNat) % 18446744073709551616 < w.toNat
          have hlt := w.isLt
          omega
  intro F s hcode hguest
  exact TerminatingProgBoundedOn.while_measure (unsignedDownRank counter) _ _ hs
    s hcode ⟨hguest, unsignedDownRank_le counter s⟩


end InitECandidate.Solver.Wave8Leaves.S00Spec.Arith
