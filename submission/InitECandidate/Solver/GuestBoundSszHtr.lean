import InitECandidate.Solver.GuestBoundMain
import InitECandidate.Solver.GuestBoundLoopFree
import InitECandidate.Solver.GuestBoundCryptoDiv

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.GuestBoundSszHtr

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.PanRunBoundedExt
open InitECandidate.Solver.GuestBoundMain
open InitECandidate.Solver.GuestBoundLoopFree

/-! ## 1. Loop combinators for variable limits, `.rfield` limits, and signed countdowns -/

private theorem progBounded_seq_straight (p q : ProgHOL 64) {k : Nat}
    (hp : extStraightLine p = true) (hq : ProgBounded q k) :
    ProgBounded (.seq p q) k :=
  ProgBounded.weaken (ProgBounded.seq (ProgBounded.straight p hp) hq) (Nat.zero_add k).le

private def DecStep (counter : MlS) (body : ProgHOL 64) (cost : Nat) : Prop :=
  ∀ {F : Type} (state : PanSemStateFiniteExact 64 F),
    state.code = originalRuntimeCode →
    ∀ w : BitVec 64, state.locals.lookup counter = some (.val (.word w)) →
    cost ≤ state.clock →
    state.clock ≤ (evaluateHOLFiniteState state body).2.clock + cost ∧
      (evaluateHOLFiniteState state body).2.clock ≤ state.clock ∧
      (evaluateHOLFiniteState state body).1 ≠ some .timeOut ∧
      (evaluateHOLFiniteState state body).1 ≠ some .continue ∧
      ((evaluateHOLFiniteState state body).1 = none →
        (evaluateHOLFiniteState state body).2.locals.lookup counter = some (.val (.word (w - 1))) ∧
        (evaluateHOLFiniteState state body).2.code = state.code)

private theorem decStep_decr_then_straight (counter : MlS) (rest : ProgHOL 64)
    (hrest : extStraightLine rest = true) (havoid : avoidsLocal counter rest = true)
    (hnoCont : noTopContinue rest = true) :
    DecStep counter (.seq (.assign .local counter (.op .sub [.var .local counter, .const 1])) rest) 0 := by
  intro F state code w atCounter _budget
  have hi : evaluateHOLFiniteState state
      (.assign .local counter (.op .sub [.var .local counter, .const 1])) =
      (none, setVarHOLFinite counter (.val (.word (w - 1))) state) := by
    simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, atCounter, wordOpHOL, wordOp,
      valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
      shapeOfHOLExact, shapeEqHOL]
  let s1 := setVarHOLFinite counter (.val (.word (w - 1))) state
  have hs1_i : s1.locals.lookup counter = some (.val (.word (w - 1))) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs1_code : s1.code = originalRuntimeCode := code
  have rBound := ProgBounded.straight rest hrest s1 hs1_code (Nat.zero_le _)
  have rFrame := evaluate_avoidsLocal_flowing counter rest havoid s1
  have rNoCont := evaluate_noTopContinue rest hnoCont s1
  have rMeta := PanRunBounded.evaluateHOLFiniteState_metadata s1 rest
  rw [evaluateHOLFiniteState_seq_line780, hi]
  dsimp only
  cases rRun : evaluateHOLFiniteState s1 rest with
  | mk res s2 =>
    rw [rRun] at rBound rFrame rNoCont rMeta
    dsimp only at rBound rFrame rNoCont rMeta ⊢
    obtain ⟨spent, kept, safe⟩ := rBound
    have hs1_clk : s1.clock = state.clock := rfl
    rw [hs1_clk] at spent kept
    refine ⟨spent, kept, safe, rNoCont, fun hnorm => ?_⟩
    exact ⟨(rFrame (Or.inl hnorm)).trans hs1_i, rMeta.1⟩

private theorem eval_zero_less_condition {F : Type} (state : PanSemStateFiniteExact 64 F) (counter : MlS)
    (w : BitVec 64) (hw : w.toNat < 2 ^ 63)
    (atCounter : state.locals.lookup counter = some (.val (.word w))) :
    evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      (.cmp .less (.const 0) (.var .local counter)) =
      some (.val (.word (if 0 < w.toNat then 1 else 0))) := by
  rw [evalHOLFinite_eq_toExact]
  have h0 : (0 : BitVec 64).toNat = 0 := rfl
  simp only [evalHOLExact, atCounter, Compiler.Encoders.Asm.wordCmpHOL,
    holAsmSignedLess_small 0 w (by rw [h0]; decide) hw, h0]
  by_cases lt : 0 < w.toNat <;> simp [lt]

private theorem downWhile_less_run (counter : MlS) {body : ProgHOL 64} {cost : Nat}
    (counted : DecStep counter body cost) :
    ∀ n : Nat, n < 2 ^ 63 → ∀ {F : Type} (state : PanSemStateFiniteExact 64 F),
      state.code = originalRuntimeCode →
      ∀ w : BitVec 64, state.locals.lookup counter = some (.val (.word w)) →
      w.toNat ≤ n → n * (cost + 1) ≤ state.clock →
      state.clock ≤ (evaluateHOLFiniteState state
        (.while (.cmp .less (.const 0) (.var .local counter)) body)).2.clock + n * (cost + 1) ∧
        (evaluateHOLFiniteState state (.while (.cmp .less (.const 0) (.var .local counter)) body)).2.clock ≤
          state.clock ∧
        (evaluateHOLFiniteState state (.while (.cmp .less (.const 0) (.var .local counter)) body)).1 ≠
          some .timeOut := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn_lt F state code w atCounter within budget
    have hw_lt : w.toNat < 2 ^ 63 := by omega
    have condition := eval_zero_less_condition state counter w hw_lt atCounter
    rw [evaluateHOLFiniteState_while_total, condition]
    by_cases lt : 0 < w.toNat
    · rw [if_pos lt]
      simp only [show (1 : BitVec 64) ≠ 0 by decide, if_true, ne_eq, not_false_eq_true]
      have positiveRank : 0 < n := by omega
      have oneIteration : cost + 1 ≤ n * (cost + 1) := Nat.le_mul_of_pos_left _ positiveRank
      have clock : state.clock ≠ 0 := by omega
      rw [if_neg clock, fixClockHOLFinite_evaluateState]
      have decCode : (decClockHOLFinite state).code = originalRuntimeCode := code
      have stepRun := counted (decClockHOLFinite state) decCode w atCounter
        (by change cost ≤ state.clock - 1; omega)
      cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
      | mk result middle =>
        rw [bodyRun] at stepRun
        dsimp only at stepRun
        obtain ⟨spent, kept, safe, noCont, advance⟩ := stepRun
        change state.clock - 1 ≤ middle.clock + cost at spent
        change middle.clock ≤ state.clock - 1 at kept
        cases result with
        | none =>
          dsimp only
          obtain ⟨nextCounter, nextCode⟩ := advance rfl
          have one_toNat : (1 : BitVec 64).toNat = 1 := rfl
          have hle : (1 : BitVec 64) ≤ w := by
            rw [BitVec.le_def, one_toNat]; omega
          have natural : (w - 1).toNat = w.toNat - 1 := by
            rw [BitVec.toNat_sub_of_le hle, one_toNat]
          have hmul : (n - 1) * (cost + 1) + (cost + 1) = n * (cost + 1) := by
            have hsucc : n - 1 + 1 = n := by omega
            calc (n - 1) * (cost + 1) + (cost + 1) = (n - 1 + 1) * (cost + 1) := by
                  rw [Nat.add_mul, Nat.one_mul]
              _ = n * (cost + 1) := by rw [hsucc]
          have tail := ih (n - 1) (by omega) (by omega) middle (nextCode.trans code) (w - 1) nextCounter
            (by rw [natural]; omega) (by omega)
          obtain ⟨t1, t2, t3⟩ := tail
          exact ⟨by omega, by omega, t3⟩
        | some r =>
          cases r with
          | «continue» => exact absurd rfl noCont
          | «break» => exact ⟨by simp; omega, by simp; omega, by simp⟩
          | timeOut => exact absurd rfl safe
          | _ => exact ⟨by simp; omega, by simp; omega, by simp⟩
    · rw [if_neg lt]
      simp

private theorem countedDownLessDec (counter : MlS) (K : BitVec 64) (hK : K.toNat < 2 ^ 63)
    {body tail : ProgHOL 64} {cost tailCost : Nat}
    (counted : DecStep counter body cost)
    (rest : ProgBounded tail tailCost) :
    ProgBounded (.dec counter .one (.const K)
      (.seq (.while (.cmp .less (.const 0) (.var .local counter)) body) tail))
      (K.toNat * (cost + 1) + tailCost) := by
  intro F state code budget
  rw [evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true]
  let entered := setVarHOLFinite counter (.val (.word K)) state
  have atCounter : entered.locals.lookup counter = some (.val (.word K)) := by
    simp [entered, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have loop := downWhile_less_run counter counted K.toNat hK entered code K atCounter (le_refl _)
    (by change K.toNat * (cost + 1) ≤ state.clock; omega)
  have meta' := PanRunBounded.evaluateHOLFiniteState_metadata entered
    (.while (.cmp .less (.const 0) (.var .local counter)) body)
  change state.clock ≤ (evaluateHOLFiniteState entered _).2.clock + _ ∧
    (evaluateHOLFiniteState entered _).2.clock ≤ state.clock ∧
    (evaluateHOLFiniteState entered _).1 ≠ some .timeOut
  rw [evaluateHOLFiniteState_seq_line780]
  cases loopRun : evaluateHOLFiniteState entered (.while (.cmp .less (.const 0) (.var .local counter)) body) with
  | mk result middle =>
    rw [loopRun] at loop meta'
    dsimp only at loop meta'
    obtain ⟨spent, kept, safe⟩ := loop
    change state.clock ≤ middle.clock + K.toNat * (cost + 1) at spent
    change middle.clock ≤ state.clock at kept
    cases result with
    | none =>
      dsimp only
      obtain ⟨t1, t2, t3⟩ := rest middle (meta'.1.trans code) (by omega)
      exact ⟨by omega, by omega, t3⟩
    | some r =>
      dsimp only
      exact ⟨by omega, kept, safe⟩

private theorem progBounded_varCountedDec (counter limit : MlS) (op : Cmp)
    (hop : op = .less ∨ op = .lower)
    {body tail : ProgHOL 64} {cost tailCost : Nat}
    (counted : CountedBody counter 1 body cost)
    (preservesLimit : avoidsLocal limit body = true)
    (rest : ProgBounded tail tailCost) :
    ProgBounded (.dec counter .one (.const 0)
      (.seq (.while (.cmp op (.var .local counter) (.var .local limit)) body) tail))
      ((2 ^ 64 - 1) * (cost + 1) + tailCost) := by
  intro F state code budget
  rw [evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true]
  let entered := setVarHOLFinite counter (.val (.word 0)) state
  have atCounter : entered.locals.lookup counter = some (.val (.word 0)) := by
    simp [entered, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  change state.clock ≤ (evaluateHOLFiniteState entered _).2.clock + _ ∧
    (evaluateHOLFiniteState entered _).2.clock ≤ state.clock ∧
    (evaluateHOLFiniteState entered _).1 ≠ some .timeOut
  cases hlim : entered.locals.lookup limit with
  | none =>
    have hcond : evalHOLFinite entered (h := fun a => Classical.propDecidable (entered.memaddrs a))
        (.cmp op (.var .local counter) (.var .local limit)) = none := by
      rw [evalHOLFinite_eq_toExact]
      simp [evalHOLExact, atCounter, hlim]
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total, hcond]
    dsimp only
    exact ⟨by change state.clock ≤ state.clock + _; omega, le_refl _, by simp⟩
  | some vlim =>
    cases vlim with
    | rStruct _ =>
      have hcond : evalHOLFinite entered (h := fun a => Classical.propDecidable (entered.memaddrs a))
          (.cmp op (.var .local counter) (.var .local limit)) = none := by
        rw [evalHOLFinite_eq_toExact]
        simp [evalHOLExact, atCounter, hlim]
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total, hcond]
      dsimp only
      exact ⟨by change state.clock ≤ state.clock + _; omega, le_refl _, by simp⟩
    | nStruct _ _ =>
      have hcond : evalHOLFinite entered (h := fun a => Classical.propDecidable (entered.memaddrs a))
          (.cmp op (.var .local counter) (.var .local limit)) = none := by
        rw [evalHOLFinite_eq_toExact]
        simp [evalHOLExact, atCounter, hlim]
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total, hcond]
      dsimp only
      exact ⟨by change state.clock ≤ state.clock + _; omega, le_refl _, by simp⟩
    | val wl =>
      cases wl with
      | word K =>
        have loop := variableCountedWhile_zero_bounded counter limit op hop counted preservesLimit
          entered code K atCounter hlim
          (by change (2 ^ 64 - 1) * (cost + 1) ≤ state.clock; omega)
        have meta' := PanRunBounded.evaluateHOLFiniteState_metadata entered
          (.while (.cmp op (.var .local counter) (.var .local limit)) body)
        rw [evaluateHOLFiniteState_seq_line780]
        cases loopRun : evaluateHOLFiniteState entered
            (.while (.cmp op (.var .local counter) (.var .local limit)) body) with
        | mk result middle =>
          rw [loopRun] at loop meta'
          dsimp only at loop meta'
          obtain ⟨spent, kept, safe⟩ := loop
          change state.clock ≤ middle.clock + (2 ^ 64 - 1) * (cost + 1) at spent
          change middle.clock ≤ state.clock at kept
          cases result with
          | none =>
            dsimp only
            obtain ⟨t1, t2, t3⟩ := rest middle (meta'.1.trans code) (by omega)
            exact ⟨by omega, by omega, t3⟩
          | some r =>
            dsimp only
            exact ⟨by omega, kept, safe⟩

private theorem progBounded_varCountedDecDec (counter auxVar limit : MlS) (auxInit : ExpHOL 64)
    (op : Cmp) (hop : op = .less ∨ op = .lower) (haux : counter ≠ auxVar)
    {body tail : ProgHOL 64} {cost tailCost : Nat}
    (counted : CountedBody counter 1 body cost)
    (preservesLimit : avoidsLocal limit body = true)
    (rest : ProgBounded tail tailCost) :
    ProgBounded (.dec counter .one (.const 0)
      (.dec auxVar .one auxInit
        (.seq (.while (.cmp op (.var .local counter) (.var .local limit)) body) tail)))
      ((2 ^ 64 - 1) * (cost + 1) + tailCost) := by
  intro F state code budget
  rw [evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true]
  let s1 := setVarHOLFinite counter (.val (.word 0)) state
  change state.clock ≤ (evaluateHOLFiniteState s1 _).2.clock + _ ∧
    (evaluateHOLFiniteState s1 _).2.clock ≤ state.clock ∧
    (evaluateHOLFiniteState s1 _).1 ≠ some .timeOut
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · exact ⟨by change state.clock ≤ state.clock + _; omega, le_refl _, by simp⟩
  · rename_i vaux _
    split
    · let entered := setVarHOLFinite auxVar vaux s1
      have atCounter : entered.locals.lookup counter = some (.val (.word 0)) := by
        simp [entered, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm haux]
      have enteredCode : entered.code = originalRuntimeCode := code
      have innerRun :
          state.clock ≤ (evaluateHOLFiniteState entered
              (.seq (.while (.cmp op (.var .local counter) (.var .local limit)) body) tail)).2.clock +
              ((2 ^ 64 - 1) * (cost + 1) + tailCost) ∧
            (evaluateHOLFiniteState entered
              (.seq (.while (.cmp op (.var .local counter) (.var .local limit)) body) tail)).2.clock ≤ state.clock ∧
            (evaluateHOLFiniteState entered
              (.seq (.while (.cmp op (.var .local counter) (.var .local limit)) body) tail)).1 ≠ some .timeOut := by
        cases hlim : entered.locals.lookup limit with
        | none =>
          have hcond : evalHOLFinite entered (h := fun a => Classical.propDecidable (entered.memaddrs a))
              (.cmp op (.var .local counter) (.var .local limit)) = none := by
            rw [evalHOLFinite_eq_toExact]
            simp [evalHOLExact, atCounter, hlim]
          rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total, hcond]
          dsimp only
          exact ⟨by change state.clock ≤ state.clock + _; omega, le_refl _, by simp⟩
        | some vlim =>
          cases vlim with
          | rStruct _ =>
            have hcond : evalHOLFinite entered (h := fun a => Classical.propDecidable (entered.memaddrs a))
                (.cmp op (.var .local counter) (.var .local limit)) = none := by
              rw [evalHOLFinite_eq_toExact]
              simp [evalHOLExact, atCounter, hlim]
            rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total, hcond]
            dsimp only
            exact ⟨by change state.clock ≤ state.clock + _; omega, le_refl _, by simp⟩
          | nStruct _ _ =>
            have hcond : evalHOLFinite entered (h := fun a => Classical.propDecidable (entered.memaddrs a))
                (.cmp op (.var .local counter) (.var .local limit)) = none := by
              rw [evalHOLFinite_eq_toExact]
              simp [evalHOLExact, atCounter, hlim]
            rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total, hcond]
            dsimp only
            exact ⟨by change state.clock ≤ state.clock + _; omega, le_refl _, by simp⟩
          | val wl =>
            cases wl with
            | word K =>
              have loop := variableCountedWhile_zero_bounded counter limit op hop counted preservesLimit
                entered enteredCode K atCounter hlim
                (by change (2 ^ 64 - 1) * (cost + 1) ≤ state.clock; omega)
              have meta' := PanRunBounded.evaluateHOLFiniteState_metadata entered
                (.while (.cmp op (.var .local counter) (.var .local limit)) body)
              rw [evaluateHOLFiniteState_seq_line780]
              cases loopRun : evaluateHOLFiniteState entered
                  (.while (.cmp op (.var .local counter) (.var .local limit)) body) with
              | mk result middle =>
                rw [loopRun] at loop meta'
                dsimp only at loop meta'
                obtain ⟨spent, kept, safe⟩ := loop
                change state.clock ≤ middle.clock + (2 ^ 64 - 1) * (cost + 1) at spent
                change middle.clock ≤ state.clock at kept
                cases result with
                | none =>
                  dsimp only
                  obtain ⟨t1, t2, t3⟩ := rest middle (meta'.1.trans enteredCode) (by omega)
                  exact ⟨by omega, by omega, t3⟩
                | some r =>
                  dsimp only
                  exact ⟨by omega, kept, safe⟩
      cases hrun : evaluateHOLFiniteState entered
          (.seq (.while (.cmp op (.var .local counter) (.var .local limit)) body) tail) with
      | mk res post =>
        rw [hrun] at innerRun
        dsimp only at innerRun ⊢
        exact innerRun
    · exact ⟨by change state.clock ≤ state.clock + _; omega, le_refl _, by simp⟩

private theorem progBounded_varCountedAssign (counter limit : MlS) (op : Cmp)
    (hop : op = .less ∨ op = .lower) (start : BitVec 64) (hstart : start = 0)
    {body tail : ProgHOL 64} {cost tailCost : Nat}
    (counted : CountedBody counter 1 body cost)
    (preservesLimit : avoidsLocal limit body = true)
    (rest : ProgBounded tail tailCost) :
    ProgBounded (.seq (.assign .local counter (.const start))
      (.seq (.while (.cmp op (.var .local counter) (.var .local limit)) body) tail))
      ((2 ^ 64 - 1) * (cost + 1) + tailCost) := by
  intro F state code budget
  by_cases valid : isValidValueHOLExact state.toExact .local counter (.val (.word start)) = true
  · have assignRun : evaluateHOLFiniteState state (.assign .local counter (.const start)) =
        (none, setKvarHOLFinite .local counter (.val (.word start)) state) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, valid]
    rw [evaluateHOLFiniteState_seq_line780, assignRun]
    dsimp only
    let entered := setKvarHOLFinite .local counter (.val (.word start)) state
    have atCounter : entered.locals.lookup counter = some (.val (.word 0)) := by
      simp [entered, hstart, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have enteredCode : entered.code = originalRuntimeCode := code
    cases hlim : entered.locals.lookup limit with
    | none =>
      have hcond : evalHOLFinite entered (h := fun a => Classical.propDecidable (entered.memaddrs a))
          (.cmp op (.var .local counter) (.var .local limit)) = none := by
        rw [evalHOLFinite_eq_toExact]
        simp [evalHOLExact, atCounter, hlim]
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total, hcond]
      dsimp only
      exact ⟨by change state.clock ≤ state.clock + _; omega, le_refl _, by simp⟩
    | some vlim =>
      cases vlim with
      | rStruct _ =>
        have hcond : evalHOLFinite entered (h := fun a => Classical.propDecidable (entered.memaddrs a))
            (.cmp op (.var .local counter) (.var .local limit)) = none := by
          rw [evalHOLFinite_eq_toExact]
          simp [evalHOLExact, atCounter, hlim]
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total, hcond]
        dsimp only
        exact ⟨by change state.clock ≤ state.clock + _; omega, le_refl _, by simp⟩
      | nStruct _ _ =>
        have hcond : evalHOLFinite entered (h := fun a => Classical.propDecidable (entered.memaddrs a))
            (.cmp op (.var .local counter) (.var .local limit)) = none := by
          rw [evalHOLFinite_eq_toExact]
          simp [evalHOLExact, atCounter, hlim]
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total, hcond]
        dsimp only
        exact ⟨by change state.clock ≤ state.clock + _; omega, le_refl _, by simp⟩
      | val wl =>
        cases wl with
        | word K =>
          have loop := variableCountedWhile_zero_bounded counter limit op hop counted preservesLimit
            entered enteredCode K atCounter hlim
            (by change (2 ^ 64 - 1) * (cost + 1) ≤ state.clock; omega)
          have meta' := PanRunBounded.evaluateHOLFiniteState_metadata entered
            (.while (.cmp op (.var .local counter) (.var .local limit)) body)
          rw [evaluateHOLFiniteState_seq_line780]
          cases loopRun : evaluateHOLFiniteState entered
              (.while (.cmp op (.var .local counter) (.var .local limit)) body) with
          | mk result middle =>
            rw [loopRun] at loop meta'
            dsimp only at loop meta'
            obtain ⟨spent, kept, safe⟩ := loop
            change state.clock ≤ middle.clock + (2 ^ 64 - 1) * (cost + 1) at spent
            change middle.clock ≤ state.clock at kept
            cases result with
            | none =>
              dsimp only
              obtain ⟨t1, t2, t3⟩ := rest middle (meta'.1.trans enteredCode) (by omega)
              exact ⟨by omega, by omega, t3⟩
            | some r =>
              dsimp only
              exact ⟨by omega, kept, safe⟩
  · have failed : evaluateHOLFiniteState state (.assign .local counter (.const start)) = (some .error, state) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, valid]
    rw [evaluateHOLFiniteState_seq_line780, failed]
    simp

private theorem rfieldCountedWhile_run (counter structVar : MlS) (idx : Nat) (op : Cmp)
    (hop : op = .less ∨ op = .lower) (vs : List (ValueHOL 64)) (K : BitVec 64)
    (hidx : vs[idx]? = some (.val (.word K)))
    (signed : op = .less → K.toNat < 2 ^ 63)
    {body : ProgHOL 64} {cost : Nat} (counted : CountedBody counter 1 body cost)
    (preservesStruct : avoidsLocal structVar body = true) :
    ∀ n : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F),
      state.code = originalRuntimeCode →
      ∀ w : BitVec 64, state.locals.lookup counter = some (.val (.word w)) →
      state.locals.lookup structVar = some (.rStruct vs) → w.toNat ≤ K.toNat →
      K.toNat - w.toNat = n → n * (cost + 1) ≤ state.clock →
      let evaluated := evaluateHOLFiniteState state
        (.while (.cmp op (.var .local counter) (.rfield idx (.var .local structVar))) body)
      state.clock ≤ evaluated.2.clock + n * (cost + 1) ∧
        evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro F state code w atCounter atStruct within distance budget
    have condition : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
        (.cmp op (.var .local counter) (.rfield idx (.var .local structVar))) =
        some (.val (.word (if w.toNat < K.toNat then 1 else 0))) := by
      rw [evalHOLFinite_eq_toExact]
      rcases hop with rfl | rfl
      · have small := signed rfl
        simp only [evalHOLExact, atCounter, atStruct, hidx]
        simp only [Compiler.Encoders.Asm.wordCmpHOL, holAsmSignedLess_small w K (by omega) small]
        by_cases lt : w.toNat < K.toNat <;> simp [lt]
      · simp only [evalHOLExact, atCounter, atStruct, hidx, Compiler.Encoders.Asm.wordCmpHOL]
        by_cases lt : w.toNat < K.toNat <;> simp [lt, BitVec.lt_def]
    dsimp only
    rw [evaluateHOLFiniteState_while_total, condition]
    by_cases lt : w.toNat < K.toNat
    · rw [if_pos lt]
      simp only [show (1 : BitVec 64) ≠ 0 by decide, if_true, ne_eq, not_false_eq_true]
      have positiveRank : 0 < n := by omega
      have oneIteration : cost + 1 ≤ n * (cost + 1) := Nat.le_mul_of_pos_left _ positiveRank
      have clock : state.clock ≠ 0 := by omega
      rw [if_neg clock, fixClockHOLFinite_evaluateState]
      have stepRun := counted.run (decClockHOLFinite state) code w atCounter
        (by change cost ≤ state.clock - 1; omega)
      have frame := evaluate_avoidsLocal_flowing structVar body preservesStruct (decClockHOLFinite state)
      cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
      | mk result middle =>
        rw [bodyRun] at stepRun frame
        dsimp only at stepRun frame
        obtain ⟨spent, kept, safe, noCont, advance⟩ := stepRun
        change state.clock - 1 ≤ middle.clock + cost at spent
        change middle.clock ≤ state.clock - 1 at kept
        cases result with
        | none =>
          dsimp only
          obtain ⟨nextCounter, nextCode⟩ := advance rfl
          have natural : (w + 1).toNat = w.toNat + 1 := by
            rw [BitVec.toNat_add_of_lt (by have bound := K.isLt; simp; omega)]
            rfl
          have nextRank : K.toNat - (w + 1).toNat < n := by rw [natural]; omega
          have nextStruct : middle.locals.lookup structVar = some (.rStruct vs) := by
            rw [frame (Or.inl rfl)]
            exact atStruct
          have decrease : (K.toNat - (w + 1).toNat) * (cost + 1) + (cost + 1) ≤ n * (cost + 1) := by
            rw [← Nat.succ_mul]
            exact Nat.mul_le_mul_right _ (by omega)
          have tail := ih (K.toNat - (w + 1).toNat) nextRank middle (nextCode.trans code)
            (w + 1) nextCounter nextStruct (by rw [natural]; omega) rfl (by omega)
          obtain ⟨t1, t2, t3⟩ := tail
          exact ⟨by omega, by omega, t3⟩
        | some r =>
          cases r with
          | «continue» => exact absurd rfl noCont
          | «break» => exact ⟨by simp; omega, by simp; omega, by simp⟩
          | timeOut => exact absurd rfl safe
          | _ => exact ⟨by simp; omega, by simp; omega, by simp⟩
    · rw [if_neg lt]
      simp

private theorem progBounded_rfieldCountedDec (counter structVar : MlS) (idx : Nat) (op : Cmp)
    (hop : op = .less ∨ op = .lower)
    {body tail : ProgHOL 64} {cost tailCost : Nat}
    (counted : CountedBody counter 1 body cost)
    (preservesStruct : avoidsLocal structVar body = true)
    (rest : ProgBounded tail tailCost) :
    ProgBounded (.dec counter .one (.const 0)
      (.seq (.while (.cmp op (.var .local counter) (.rfield idx (.var .local structVar))) body) tail))
      ((2 ^ 64 - 1) * (cost + 1) + tailCost) := by
  intro F state code budget
  rw [evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true]
  let entered := setVarHOLFinite counter (.val (.word 0)) state
  have atCounter : entered.locals.lookup counter = some (.val (.word 0)) := by
    simp [entered, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  change state.clock ≤ (evaluateHOLFiniteState entered _).2.clock + _ ∧
    (evaluateHOLFiniteState entered _).2.clock ≤ state.clock ∧
    (evaluateHOLFiniteState entered _).1 ≠ some .timeOut
  cases hst : entered.locals.lookup structVar with
  | none =>
    have hcond : evalHOLFinite entered (h := fun a => Classical.propDecidable (entered.memaddrs a))
        (.cmp op (.var .local counter) (.rfield idx (.var .local structVar))) = none := by
      rw [evalHOLFinite_eq_toExact]
      simp [evalHOLExact, atCounter, hst]
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total, hcond]
    dsimp only
    exact ⟨by change state.clock ≤ state.clock + _; omega, le_refl _, by simp⟩
  | some vst =>
    cases vst with
    | val _ =>
      have hcond : evalHOLFinite entered (h := fun a => Classical.propDecidable (entered.memaddrs a))
          (.cmp op (.var .local counter) (.rfield idx (.var .local structVar))) = none := by
        rw [evalHOLFinite_eq_toExact]
        simp [evalHOLExact, atCounter, hst]
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total, hcond]
      dsimp only
      exact ⟨by change state.clock ≤ state.clock + _; omega, le_refl _, by simp⟩
    | nStruct _ _ =>
      have hcond : evalHOLFinite entered (h := fun a => Classical.propDecidable (entered.memaddrs a))
          (.cmp op (.var .local counter) (.rfield idx (.var .local structVar))) = none := by
        rw [evalHOLFinite_eq_toExact]
        simp [evalHOLExact, atCounter, hst]
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total, hcond]
      dsimp only
      exact ⟨by change state.clock ≤ state.clock + _; omega, le_refl _, by simp⟩
    | rStruct vs =>
      cases hidx : vs[idx]? with
      | none =>
        have hcond : evalHOLFinite entered (h := fun a => Classical.propDecidable (entered.memaddrs a))
            (.cmp op (.var .local counter) (.rfield idx (.var .local structVar))) = none := by
          rw [evalHOLFinite_eq_toExact]
          simp [evalHOLExact, atCounter, hst, hidx]
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total, hcond]
        dsimp only
        exact ⟨by change state.clock ≤ state.clock + _; omega, le_refl _, by simp⟩
      | some vf =>
        cases vf with
        | rStruct _ =>
          have hcond : evalHOLFinite entered (h := fun a => Classical.propDecidable (entered.memaddrs a))
              (.cmp op (.var .local counter) (.rfield idx (.var .local structVar))) = none := by
            rw [evalHOLFinite_eq_toExact]
            simp [evalHOLExact, atCounter, hst, hidx]
          rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total, hcond]
          dsimp only
          exact ⟨by change state.clock ≤ state.clock + _; omega, le_refl _, by simp⟩
        | nStruct _ _ =>
          have hcond : evalHOLFinite entered (h := fun a => Classical.propDecidable (entered.memaddrs a))
              (.cmp op (.var .local counter) (.rfield idx (.var .local structVar))) = none := by
            rw [evalHOLFinite_eq_toExact]
            simp [evalHOLExact, atCounter, hst, hidx]
          rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total, hcond]
          dsimp only
          exact ⟨by change state.clock ≤ state.clock + _; omega, le_refl _, by simp⟩
        | val wl =>
          cases wl with
          | word K =>
            have loop :
                let evaluated := evaluateHOLFiniteState entered
                  (.while (.cmp op (.var .local counter) (.rfield idx (.var .local structVar))) body)
                state.clock ≤ evaluated.2.clock + (2 ^ 64 - 1) * (cost + 1) ∧
                  evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
              by_cases signed : op = .less → K.toNat < 2 ^ 63
              · have ceiling : K.toNat * (cost + 1) ≤ (2 ^ 64 - 1) * (cost + 1) :=
                  Nat.mul_le_mul_right _ (by have bound := K.isLt; omega)
                have bounded := rfieldCountedWhile_run counter structVar idx op hop vs K hidx signed
                  counted preservesStruct K.toNat entered code 0 atCounter hst (by simp) (by simp)
                  (by change K.toNat * (cost + 1) ≤ state.clock; omega)
                dsimp only at bounded ⊢
                have hent : entered.clock = state.clock := rfl
                rw [hent] at bounded
                exact ⟨by omega, bounded.2.1, bounded.2.2⟩
              · have comparison : op = .less := by
                  rcases hop with eq | eq
                  · exact eq
                  · exfalso; exact signed (fun impossible => by cases eq.symm.trans impossible)
                have negative : ¬ K.toNat < 9223372036854775808 := fun small => signed (fun _ => small)
                subst op
                have condition : evalHOLFinite entered
                    (h := fun a => Classical.propDecidable (entered.memaddrs a))
                    (.cmp .less (.var .local counter) (.rfield idx (.var .local structVar))) =
                    some (.val (.word 0)) := by
                  rw [evalHOLFinite_eq_toExact]
                  simp [evalHOLExact, atCounter, hst, hidx, Compiler.Encoders.Asm.wordCmpHOL,
                    Compiler.Encoders.Asm.holAsmSignedLess, negative]
                dsimp only
                rw [evaluateHOLFiniteState_while_total, condition]
                exact ⟨by change state.clock ≤ state.clock + _; omega, le_refl _, by simp⟩
            have meta' := PanRunBounded.evaluateHOLFiniteState_metadata entered
              (.while (.cmp op (.var .local counter) (.rfield idx (.var .local structVar))) body)
            rw [evaluateHOLFiniteState_seq_line780]
            cases loopRun : evaluateHOLFiniteState entered
                (.while (.cmp op (.var .local counter) (.rfield idx (.var .local structVar))) body) with
            | mk result middle =>
              rw [loopRun] at loop meta'
              dsimp only at loop meta'
              obtain ⟨spent, kept, safe⟩ := loop
              cases result with
              | none =>
                dsimp only
                obtain ⟨t1, t2, t3⟩ := rest middle (meta'.1.trans code) (by omega)
                exact ⟨by omega, by omega, t3⟩
              | some r =>
                dsimp only
                exact ⟨by omega, kept, safe⟩

private theorem progBounded_guarded_notLower_const (var : MlS) (C : BitVec 64)
    {thenBranch elseBranch : ProgHOL 64} {cost : Nat}
    (hthen : ∀ (K : BitVec 64), K.toNat ≤ C.toNat →
      ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
        s.code = originalRuntimeCode →
        s.locals.lookup var = some (.val (.word K)) →
        cost ≤ s.clock →
        RunBounded s thenBranch cost)
    (helse : ProgBounded elseBranch cost) :
    ProgBounded (.ite (.cmp .notLower (.const C) (.var .local var)) thenBranch elseBranch) cost := by
  intro F state hcode hbudget
  rw [evaluateHOLFiniteState_ite]
  cases hvar : state.locals.lookup var with
  | none =>
    simp [evalHOLExact, hvar]
  | some vv =>
    cases vv with
    | rStruct _ => simp [evalHOLExact, hvar]
    | nStruct _ _ => simp [evalHOLExact, hvar]
    | val wlv =>
      cases wlv with
      | word K =>
        by_cases hlt : C < K
        · simp only [evalHOLExact, hvar, Compiler.Encoders.Asm.wordCmpHOL, hlt, if_true]
          exact helse state hcode hbudget
        · simp only [evalHOLExact, hvar, Compiler.Encoders.Asm.wordCmpHOL, hlt, if_false,
            show (1 : BitVec 64) ≠ 0 by decide]
          have hle : K.toNat ≤ C.toNat := by
            rw [BitVec.lt_def] at hlt
            omega
          exact hthen K hle state hcode hvar hbudget

/-! ## 2. Leaf helpers and core Merkle / bytes HTR routines -/

theorem funBounded_min : FunBounded (ofString "min") 0 :=
  funBounded_of_guestAst 31 (by rw [guestAst_len]; decide) Guest.Software.guestFn_min 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_max : FunBounded (ofString "max") 0 :=
  funBounded_of_guestAst 32 (by rw [guestAst_len]; decide) Guest.Software.guestFn_max 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_udivmod : FunBounded (ofString "udivmod") 65 := by
  refine funBounded_of_guestAst 33 (by rw [guestAst_len]; decide) Guest.Software.guestFn_udivmod 65 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_udivmod,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.seq
      (ProgBounded.iteMax _ (ProgBounded.call funBounded_trap_with _ _) (ProgBounded.straight _ rfl))
      (progBounded_seq_straight _ _ rfl
        (ProgBounded.dec _ _ _
          (ProgBounded.dec _ _ _
            (countedDownLessDec (ofString "i") (BitVec.ofNat 64 64) (by decide)
              (decStep_decr_then_straight (ofString "i") _ rfl rfl rfl)
              (ProgBounded.straight _ rfl))))))
    (by decide)

private theorem runBounded_call_three_arg3_word {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (fn : MlS) (e1 e2 : ExpHOL 64)
    (var : MlS) (K : BitVec 64) {cost : Nat}
    (hvar : state.locals.lookup var = some (.val (.word K)))
    (hconst : RunBounded state (.call (some (destination, none)) fn [e1, e2, .const K]) cost) :
    RunBounded state (.call (some (destination, none)) fn [e1, e2, .var .local var]) cost := by
  have heval : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [e1, e2, .var .local var] =
      evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [e1, e2, .const K] := by
    simp only [evalListHOLFinite_eq_toExact, evalListHOLExact, evalHOLExact, hvar]
  unfold RunBounded at hconst ⊢
  rw [evaluateHOLFiniteState_call, heval, ← evaluateHOLFiniteState_call]
  exact hconst

theorem funBounded_sha256_pair : FunBounded (ofString "sha256_pair") 0 :=
  funBounded_of_guestAst 96 (by rw [guestAst_len]; decide) Guest.Software.guestFn_sha256_pair 0 rfl
    (ProgBounded.straight _ (by decide))

theorem funBounded_mix_in_length : FunBounded (ofString "mix_in_length") 16 :=
  funBounded_of_guestAst 187 (by rw [guestAst_len]; decide) Guest.Software.guestFn_mix_in_length 16 rfl
    (ProgBounded.weaken
      (ProgBounded.seq (progBounded_memzero_const _ _ 32#64 (by decide))
        (ProgBounded.seq (ProgBounded.call funBounded_st_le64 _ _)
          (ProgBounded.seq (ProgBounded.call funBounded_sha256_pair _ _)
            (ProgBounded.straight _ rfl))))
      (by decide))

theorem funBounded_htr_u64_at : FunBounded (ofString "htr_u64_at") 21 :=
  funBounded_of_guestAst 195 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htr_u64_at 21 rfl
    (ProgBounded.weaken
      (ProgBounded.seq (progBounded_memzero_const _ _ 32#64 (by decide))
        (ProgBounded.seq (progBounded_memcpy_const _ _ _ 8#64 (by decide))
          (ProgBounded.straight _ rfl)))
      (by decide))

theorem funBounded_htr_plist_chunks
    (K_merkleize_progressive : Nat)
    (h_merkleize_progressive : FunBounded (ofString "merkleize_progressive") K_merkleize_progressive) :
    FunBounded (ofString "htr_plist_chunks") (K_merkleize_progressive + 18) :=
  funBounded_of_guestAst 189 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htr_plist_chunks _ rfl
    (ProgBounded.weaken
      (ProgBounded.seq (ProgBounded.call h_merkleize_progressive _ _)
        (ProgBounded.seq (ProgBounded.call funBounded_mix_in_length _ _)
          (ProgBounded.straight _ rfl)))
      (by omega))

theorem funBounded_htr_pbytes
    (K_pack_bytes K_merkleize_progressive : Nat)
    (h_pack_bytes : FunBounded (ofString "pack_bytes") K_pack_bytes)
    (h_merkleize_progressive : FunBounded (ofString "merkleize_progressive") K_merkleize_progressive) :
    FunBounded (ofString "htr_pbytes") (K_pack_bytes + K_merkleize_progressive + 23) :=
  funBounded_of_guestAst 190 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htr_pbytes _ rfl
    (ProgBounded.weaken
      (ProgBounded.decCall funBounded_heap_mark _ _ _
        (ProgBounded.decCall h_pack_bytes _ _ _
          (ProgBounded.seq
            (ProgBounded.call (funBounded_htr_plist_chunks K_merkleize_progressive h_merkleize_progressive) _ _)
            (ProgBounded.seq (ProgBounded.call funBounded_heap_release _ _)
              (ProgBounded.straight _ rfl)))))
      (by omega))

theorem funBounded_htr_pcontainer
    (K_merkleize_progressive : Nat)
    (h_merkleize_progressive : FunBounded (ofString "merkleize_progressive") K_merkleize_progressive) :
    FunBounded (ofString "htr_pcontainer") (K_merkleize_progressive + (2 ^ 64 - 1) + 18) := by
  refine funBounded_of_guestAst 191 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htr_pcontainer _ rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_htr_pcontainer,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine ProgBounded.weaken
    (ProgBounded.decCall funBounded_heap_mark _ _ _
      (ProgBounded.decCall funBounded_alloc _ _ _
        (ProgBounded.seq (ProgBounded.call h_merkleize_progressive _ _)
          (ProgBounded.dec _ _ _
            (ProgBounded.seq (progBounded_memzero_const _ _ 32#64 (by decide))
              (progBounded_varCountedDec (ofString "i") (ofString "n") .less (Or.inl rfl)
                (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr)
                rfl
                (ProgBounded.seq (ProgBounded.call funBounded_sha256_pair _ _)
                  (ProgBounded.seq (ProgBounded.call funBounded_heap_release _ _)
                    (ProgBounded.straight _ rfl)))))))))
    ?_
  have h32 : (32#64).toNat = 32 := rfl
  rw [h32]
  generalize (2 : Nat) ^ 64 - 1 = W
  omega

theorem funBounded_htr_bytes_vector
    (K_pack_bytes K_merkleize : Nat)
    (h_pack_bytes : FunBounded (ofString "pack_bytes") K_pack_bytes)
    (h_merkleize : FunBounded (ofString "merkleize") K_merkleize) :
    FunBounded (ofString "htr_bytes_vector") (K_pack_bytes + K_merkleize + 28) := by
  refine funBounded_of_guestAst 193 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htr_bytes_vector _ rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_htr_bytes_vector,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine ProgBounded.weaken
    (ProgBounded.seq
      (progBounded_guarded_notLower_const (ofString "n") 32#64
        (cost := 24)
        (fun K hle F s hs_code hs_n hs_bud => by
          have h32 : (32#64).toNat = 32 := rfl
          rw [h32] at hle
          have hsmall : K.toNat + 32 < 2 ^ 64 := by omega
          have hm1 : RunBounded s
              (.call (some (none, none)) (ofString "memzero")
                [.var .local (ofString "out"), .const 32#64]) 12 :=
            (progBounded_memzero_const none (.var .local (ofString "out")) 32#64 (by decide))
              s hs_code (by change (32#64).toNat / 8 + 8 ≤ s.clock; rw [h32]; omega)
          refine RunBounded.seq hm1 (a := 12) (b := 12) (by omega) ?_
          intro s1 hs1_eq hs1_code hs1_bud
          have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word K)) := by
            have havoid := evaluate_avoidsLocal_flowing (ofString "n")
              (.call (some (none, none)) (ofString "memzero")
                [.var .local (ofString "out"), .const 32#64])
              rfl s (by rw [hs1_eq]; exact Or.inl rfl)
            rw [hs1_eq] at havoid
            exact havoid.trans hs_n
          have hmc_const : RunBounded s1
              (.call (some (none, none)) (ofString "memcpy")
                [.var .local (ofString "out"), .var .local (ofString "p"), .const K]) 12 :=
            RunBounded.weaken
              ((progBounded_memcpy_const none (.var .local (ofString "out"))
                  (.var .local (ofString "p")) K hsmall)
                s1 (hs1_code.trans hs_code) (by omega))
              (by omega)
          have hmc : RunBounded s1
              (.call (some (none, none)) (ofString "memcpy")
                [.var .local (ofString "out"), .var .local (ofString "p"), .var .local (ofString "n")]) 12 :=
            runBounded_call_three_arg3_word s1 none (ofString "memcpy")
              (.var .local (ofString "out")) (.var .local (ofString "p")) (ofString "n") K hs1_n hmc_const
          refine RunBounded.seq hmc (a := 12) (b := 0) (by omega) ?_
          intro s2 _ hs2_code hs2_bud
          exact (ProgBounded.straight (.return (.const 0#64)) rfl)
            s2 (hs2_code.trans (hs1_code.trans hs_code)) hs2_bud)
        (ProgBounded.weaken (ProgBounded.straight .skip rfl) (by decide)))
      (ProgBounded.decCall funBounded_heap_mark _ _ _
        (ProgBounded.decCall h_pack_bytes _ _ _
          (ProgBounded.seq (ProgBounded.call h_merkleize _ _)
            (ProgBounded.seq (ProgBounded.call funBounded_heap_release _ _)
              (ProgBounded.straight _ rfl))))))
    (by omega)

theorem funBounded_htr_bytes_list
    (K_pack_bytes K_merkleize : Nat)
    (h_pack_bytes : FunBounded (ofString "pack_bytes") K_pack_bytes)
    (h_merkleize : FunBounded (ofString "merkleize") K_merkleize) :
    FunBounded (ofString "htr_bytes_list") (K_pack_bytes + K_merkleize + 21) :=
  funBounded_of_guestAst 194 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htr_bytes_list _ rfl
    (ProgBounded.weaken
      (ProgBounded.decCall funBounded_heap_mark _ _ _
        (ProgBounded.decCall h_pack_bytes _ _ _
          (ProgBounded.seq (ProgBounded.call h_merkleize _ _)
            (ProgBounded.seq (ProgBounded.call funBounded_heap_release _ _)
              (ProgBounded.seq (ProgBounded.call funBounded_mix_in_length _ _)
                (ProgBounded.straight _ rfl))))))
      (by omega))

/-! ## 3. SSZ container and variable-list decoders -/

theorem funBounded_ssz_check_offsets :
    FunBounded (ofString "ssz_check_offsets") (3 * (2 ^ 64 - 1) + 1) := by
  refine funBounded_of_guestAst 201 (by rw [guestAst_len]; decide) Guest.Software.guestFn_ssz_check_offsets _ rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_ssz_check_offsets,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine ProgBounded.weaken
    (ProgBounded.seq (ProgBounded.straight _ rfl)
      (progBounded_varCountedDec (ofString "i") (ofString "n") .less (Or.inl rfl)
        (CountedBody.dec _ _ _ (by decide)
          (CountedBody.seq _
            (ProgBounded.iteMax _ (ProgBounded.call funBounded_ssz_fail _ _) (ProgBounded.straight _ rfl))
            rfl rfl
            (CountedBody.seq _
              (ProgBounded.iteMax _
                (ProgBounded.iteMax _ (ProgBounded.call funBounded_ssz_fail _ _) (ProgBounded.straight _ rfl))
                (ProgBounded.straight _ rfl))
              rfl rfl
              CountedBody.incr)))
        rfl
        (ProgBounded.seq
          (ProgBounded.iteMax _ (ProgBounded.call funBounded_ssz_fail _ _) (ProgBounded.straight _ rfl))
          (ProgBounded.straight _ rfl))))
    (by decide)

theorem funBounded_ssz_split_var_list :
    FunBounded (ofString "ssz_split_var_list") (2 * (2 ^ 64 - 1) + 5) := by
  refine funBounded_of_guestAst 202 (by rw [guestAst_len]; decide) Guest.Software.guestFn_ssz_split_var_list _ rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_ssz_split_var_list,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.seq (ProgBounded.straight _ rfl)
      (ProgBounded.seq
        (ProgBounded.iteMax _ (ProgBounded.call funBounded_ssz_fail _ _) (ProgBounded.straight _ rfl))
        (ProgBounded.dec _ _ _
          (ProgBounded.seq
            (ProgBounded.iteMax _ (ProgBounded.call funBounded_ssz_fail _ _) (ProgBounded.straight _ rfl))
            (ProgBounded.dec _ _ _
              (ProgBounded.seq
                (ProgBounded.iteMax _ (ProgBounded.call funBounded_ssz_fail _ _) (ProgBounded.straight _ rfl))
                (ProgBounded.decCall funBounded_alloc _ _ _
                  (progBounded_varCountedDecDec (ofString "i") (ofString "prev") (ofString "count") _
                    .less (Or.inl rfl) (by decide)
                    (CountedBody.dec _ _ _ (by decide)
                      (CountedBody.seq _
                        (ProgBounded.iteMax _ (ProgBounded.call funBounded_ssz_fail _ _) (ProgBounded.straight _ rfl))
                        rfl rfl
                        (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
                          (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
                            (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
                              CountedBody.incr)))))
                    rfl
                    (ProgBounded.straight _ rfl)))))))))
    (by decide)

theorem funBounded_ssz_fixed_list_count : FunBounded (ofString "ssz_fixed_list_count") 68 := by
  refine funBounded_of_guestAst 203 (by rw [guestAst_len]; decide) Guest.Software.guestFn_ssz_fixed_list_count 68 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_ssz_fixed_list_count,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_udivmod _ _ _
      (ProgBounded.seq
        (ProgBounded.iteMax _ (ProgBounded.call funBounded_ssz_fail _ _) (ProgBounded.straight _ rfl))
        (ProgBounded.seq
          (ProgBounded.iteMax _ (ProgBounded.call funBounded_ssz_fail _ _) (ProgBounded.straight _ rfl))
          (ProgBounded.straight _ rfl))))
    (by decide)

theorem funBounded_decode_bytes_list :
    FunBounded (ofString "decode_bytes_list") (4 * (2 ^ 64 - 1) + 6) := by
  refine funBounded_of_guestAst 206 (by rw [guestAst_len]; decide) Guest.Software.guestFn_decode_bytes_list _ rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_decode_bytes_list,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_ssz_split_var_list _ _ _
      (progBounded_rfieldCountedDec (ofString "i") (ofString "r") 1 .less (Or.inl rfl)
        (CountedBody.seq _
          (ProgBounded.iteMax _ (ProgBounded.call funBounded_ssz_fail _ _) (ProgBounded.straight _ rfl))
          rfl rfl
          CountedBody.incr)
        rfl
        (ProgBounded.straight _ rfl)))
    (by decide)

theorem funBounded_decode_requests : FunBounded (ofString "decode_requests") 370 := by
  refine funBounded_of_guestAst 205 (by rw [guestAst_len]; decide) Guest.Software.guestFn_decode_requests 370 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_decode_requests,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.seq
      (ProgBounded.iteMax _ (ProgBounded.call funBounded_ssz_fail _ _) (ProgBounded.straight _ rfl))
      (ProgBounded.countedDec (ofString "i") .less (Or.inl rfl) 5 1 0
        (by decide) (by decide) (by decide) (cost := 0)
        (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr)
        (ProgBounded.seq
          (progBounded_ssz_check_offsets_const _ _ _ _ 5#64 (by decide))
          (ProgBounded.decCall funBounded_alloc _ _ _
            (ProgBounded.dec _ _ _
              (ProgBounded.dec _ _ _
                (ProgBounded.dec _ _ _
                  (ProgBounded.dec _ _ _
                    (ProgBounded.dec _ _ _
                      (ProgBounded.decCall funBounded_ssz_fixed_list_count _ _ _
                        (ProgBounded.decCall funBounded_ssz_fixed_list_count _ _ _
                          (ProgBounded.decCall funBounded_ssz_fixed_list_count _ _ _
                            (ProgBounded.decCall funBounded_ssz_fixed_list_count _ _ _
                              (ProgBounded.decCall funBounded_ssz_fixed_list_count _ _ _
                                (ProgBounded.straight _ rfl)))))))))))))))
    (by decide)

theorem funBounded_decode_payload :
    FunBounded (ofString "decode_payload") (2 * (2 ^ 64 - 1) + 93) := by
  refine funBounded_of_guestAst 204 (by rw [guestAst_len]; decide) Guest.Software.guestFn_decode_payload _ rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_decode_payload,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine ProgBounded.weaken
    (ProgBounded.seq
      (ProgBounded.iteMax _ (ProgBounded.call funBounded_ssz_fail _ _) (ProgBounded.straight _ rfl))
      (ProgBounded.decCall funBounded_alloc _ _ _
        (progBounded_seq_straight _ _ rfl
          (progBounded_seq_straight _ _ rfl
            (ProgBounded.dec _ _ _
              (ProgBounded.dec _ _ _
                (ProgBounded.dec _ _ _
                  (ProgBounded.dec _ _ _
                    (progBounded_seq_straight _ _ rfl
                      (progBounded_seq_straight _ _ rfl
                        (progBounded_seq_straight _ _ rfl
                          (progBounded_seq_straight _ _ rfl
                            (ProgBounded.seq
                              (progBounded_ssz_check_offsets_const _ _ _ _ 4#64 (by decide))
                              (ProgBounded.seq
                                (ProgBounded.iteMax _ (ProgBounded.call funBounded_ssz_fail _ _) (ProgBounded.straight _ rfl))
                                (progBounded_seq_straight _ _ rfl
                                  (progBounded_seq_straight _ _ rfl
                                    (ProgBounded.decCall funBounded_ssz_split_var_list _ _ _
                                      (progBounded_seq_straight _ _ rfl
                                        (progBounded_seq_straight _ _ rfl
                                          (ProgBounded.decCall funBounded_ssz_fixed_list_count _ _ _
                                            (ProgBounded.straight _ rfl)))))))))))))))))))))
    ?_
  have h4 : (4#64).toNat = 4 := rfl
  rw [h4]
  generalize (2 : Nat) ^ 64 - 1 = W
  omega

theorem funBounded_decode_stateless_input :
    FunBounded (ofString "decode_stateless_input") (14 * (2 ^ 64 - 1) + 595) := by
  refine funBounded_of_guestAst 207 (by rw [guestAst_len]; decide) Guest.Software.guestFn_decode_stateless_input _ rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_decode_stateless_input,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine ProgBounded.weaken
    (ProgBounded.seq
      (ProgBounded.iteMax _ (ProgBounded.call funBounded_ssz_fail _ _) (ProgBounded.straight _ rfl))
      (ProgBounded.seq
        (ProgBounded.iteMax _ (ProgBounded.call funBounded_ssz_fail _ _) (ProgBounded.straight _ rfl))
        (progBounded_seq_straight _ _ rfl
          (progBounded_seq_straight _ _ rfl
            (ProgBounded.seq
              (ProgBounded.iteMax _ (ProgBounded.call funBounded_ssz_fail _ _) (ProgBounded.straight _ rfl))
              (progBounded_seq_straight _ _ rfl
                (progBounded_seq_straight _ _ rfl
                  (ProgBounded.seq
                    (progBounded_ssz_check_offsets_const _ _ _ _ 2#64 (by decide))
                    (ProgBounded.dec _ _ _
                      (ProgBounded.dec _ _ _
                        (ProgBounded.decCall funBounded_alloc _ _ _
                          (progBounded_seq_straight _ _ rfl
                            (ProgBounded.dec _ _ _
                              (ProgBounded.dec _ _ _
                                (ProgBounded.seq
                                  (ProgBounded.iteMax _ (ProgBounded.call funBounded_ssz_fail _ _) (ProgBounded.straight _ rfl))
                                  (ProgBounded.dec _ _ _
                                    (ProgBounded.dec _ _ _
                                      (ProgBounded.dec _ _ _
                                        (progBounded_seq_straight _ _ rfl
                                          (progBounded_seq_straight _ _ rfl
                                            (progBounded_seq_straight _ _ rfl
                                              (ProgBounded.seq
                                                (progBounded_ssz_check_offsets_const _ _ _ _ 3#64 (by decide))
                                                (ProgBounded.decCall funBounded_decode_payload _ _ _
                                                  (progBounded_seq_straight _ _ rfl
                                                    (ProgBounded.decCall funBounded_ssz_fixed_list_count _ _ _
                                                      (progBounded_seq_straight _ _ rfl
                                                        (progBounded_seq_straight _ _ rfl
                                                          (progBounded_seq_straight _ _ rfl
                                                            (ProgBounded.decCall funBounded_decode_requests _ _ _
                                                              (progBounded_seq_straight _ _ rfl
                                                                (ProgBounded.dec _ _ _
                                                                  (ProgBounded.dec _ _ _
                                                                    (ProgBounded.seq
                                                                      (ProgBounded.iteMax _ (ProgBounded.call funBounded_ssz_fail _ _) (ProgBounded.straight _ rfl))
                                                                      (ProgBounded.countedDec (ofString "i") .less (Or.inl rfl) 3 1 0
                                                                        (by decide) (by decide) (by decide) (cost := 0)
                                                                        (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr)
                                                                        (ProgBounded.seq
                                                                          (progBounded_ssz_check_offsets_const _ _ _ _ 3#64 (by decide))
                                                                          (ProgBounded.dec _ _ _
                                                                            (ProgBounded.dec _ _ _
                                                                              (ProgBounded.dec _ _ _
                                                                                (ProgBounded.decCall funBounded_decode_bytes_list _ _ _
                                                                                  (progBounded_seq_straight _ _ rfl
                                                                                    (progBounded_seq_straight _ _ rfl
                                                                                      (ProgBounded.decCall funBounded_decode_bytes_list _ _ _
                                                                                        (progBounded_seq_straight _ _ rfl
                                                                                          (progBounded_seq_straight _ _ rfl
                                                                                            (ProgBounded.decCall funBounded_decode_bytes_list _ _ _
                                                                                              (ProgBounded.straight _ rfl))))))))))))))))))))))))))))))))))))))))))))))
    (by decide)

theorem funBounded_decode_host_input :
    FunBounded (ofString "decode_host_input") (14 * (2 ^ 64 - 1) + 134218411) := by
  refine funBounded_of_guestAst 200 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_decode_host_input _ rfl ?_
  exact ProgBounded.weaken
    (ProgBounded.seq (ProgBounded.call funBounded_precheck_host_ssz_header _ _)
      (ProgBounded.decCall funBounded_input_blob_verified _ _ _
        (ProgBounded.tail funBounded_decode_stateless_input _)))
    (by decide)

/-! ## 4. HTR container and request-list hashers -/

theorem funBounded_htr_withdrawal
    (K_pack_bytes K_merkleize : Nat)
    (h_pack_bytes : FunBounded (ofString "pack_bytes") K_pack_bytes)
    (h_merkleize : FunBounded (ofString "merkleize") K_merkleize) :
    FunBounded (ofString "htr_withdrawal") (K_pack_bytes + 2 * K_merkleize + 100) := by
  refine funBounded_of_guestAst 208 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_htr_withdrawal _ rfl ?_
  have hbv := funBounded_htr_bytes_vector K_pack_bytes K_merkleize h_pack_bytes h_merkleize
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_heap_mark _ _ _
      (ProgBounded.decCall funBounded_alloc _ _ _
        (ProgBounded.seq (ProgBounded.call funBounded_htr_u64_at _ _)
          (ProgBounded.seq (ProgBounded.call funBounded_htr_u64_at _ _)
            (ProgBounded.seq (ProgBounded.call hbv _ _)
              (ProgBounded.seq (ProgBounded.call funBounded_htr_u64_at _ _)
                (ProgBounded.seq (ProgBounded.call h_merkleize _ _)
                  (ProgBounded.seq (ProgBounded.call funBounded_heap_release _ _)
                    (ProgBounded.straight _ rfl)))))))))
    (by omega)

theorem funBounded_htr_list_roots
    (K_merkleize : Nat)
    (h_merkleize : FunBounded (ofString "merkleize") K_merkleize) :
    FunBounded (ofString "htr_list_roots") (K_merkleize + 18) :=
  funBounded_of_guestAst 209 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_htr_list_roots _ rfl
    (ProgBounded.weaken
      (ProgBounded.seq (ProgBounded.call h_merkleize _ _)
        (ProgBounded.seq (ProgBounded.call funBounded_mix_in_length _ _)
          (ProgBounded.straight _ rfl)))
      (by omega))

theorem funBounded_htr_payload
    (K_pack_bytes K_merkleize K_merkleize_progressive : Nat)
    (h_pack_bytes : FunBounded (ofString "pack_bytes") K_pack_bytes)
    (h_merkleize : FunBounded (ofString "merkleize") K_merkleize)
    (h_merkleize_progressive : FunBounded (ofString "merkleize_progressive") K_merkleize_progressive) :
    FunBounded (ofString "htr_payload")
      ((2 ^ 64 - 1) * (K_pack_bytes + K_merkleize_progressive + 25) +
        (2 ^ 64 - 1) * (K_pack_bytes + 2 * K_merkleize + 102) +
        4 * K_pack_bytes + 3 * K_merkleize + 4 * K_merkleize_progressive +
        (2 ^ 64 - 1) + 414) := by
  refine funBounded_of_guestAst 210 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_htr_payload _ rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_htr_payload,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  have hbv := funBounded_htr_bytes_vector K_pack_bytes K_merkleize h_pack_bytes h_merkleize
  have hbl := funBounded_htr_bytes_list K_pack_bytes K_merkleize h_pack_bytes h_merkleize
  have hpb := funBounded_htr_pbytes K_pack_bytes K_merkleize_progressive h_pack_bytes h_merkleize_progressive
  have hpc := funBounded_htr_plist_chunks K_merkleize_progressive h_merkleize_progressive
  have hwd := funBounded_htr_withdrawal K_pack_bytes K_merkleize h_pack_bytes h_merkleize
  have hpcont := funBounded_htr_pcontainer K_merkleize_progressive h_merkleize_progressive
  refine ProgBounded.weaken
    (ProgBounded.dec _ _ _
      (ProgBounded.decCall funBounded_heap_mark _ _ _
        (ProgBounded.decCall funBounded_alloc _ _ _
          (ProgBounded.seq (progBounded_memcpy_const _ _ _ 32#64 (by decide))
            (ProgBounded.seq (ProgBounded.call hbv _ _)
              (ProgBounded.seq (progBounded_memcpy_const _ _ _ 32#64 (by decide))
                (ProgBounded.seq (progBounded_memcpy_const _ _ _ 32#64 (by decide))
                  (ProgBounded.seq (ProgBounded.call hbv _ _)
                    (ProgBounded.seq (progBounded_memcpy_const _ _ _ 32#64 (by decide))
                      (ProgBounded.seq (ProgBounded.call funBounded_htr_u64_at _ _)
                        (ProgBounded.seq (ProgBounded.call funBounded_htr_u64_at _ _)
                          (ProgBounded.seq (ProgBounded.call funBounded_htr_u64_at _ _)
                            (ProgBounded.seq (ProgBounded.call funBounded_htr_u64_at _ _)
                              (ProgBounded.seq (ProgBounded.call hbl _ _)
                                (ProgBounded.seq (progBounded_memcpy_const _ _ _ 32#64 (by decide))
                                  (ProgBounded.seq (progBounded_memcpy_const _ _ _ 32#64 (by decide))
                                    (ProgBounded.dec _ _ _
                                      (ProgBounded.dec _ _ _
                                        (ProgBounded.decCall funBounded_heap_mark _ _ _
                                          (ProgBounded.decCall funBounded_alloc _ _ _
                                            (progBounded_varCountedDec (ofString "i") (ofString "ntx") .less (Or.inl rfl)
                                              (CountedBody.seq _ (ProgBounded.call hpb _ _) rfl rfl CountedBody.incr)
                                              rfl
                                              (ProgBounded.seq (ProgBounded.call hpc _ _)
                                                (ProgBounded.seq (ProgBounded.call funBounded_heap_release _ _)
                                                  (ProgBounded.dec _ _ _
                                                    (ProgBounded.dec _ _ _
                                                      (ProgBounded.seq (ProgBounded.alloc _ _)
                                                        (progBounded_varCountedAssign (ofString "i") (ofString "nwd") .less (Or.inl rfl) 0#64 rfl
                                                          (CountedBody.seq _ (ProgBounded.call hwd _ _) rfl rfl CountedBody.incr)
                                                          rfl
                                                          (ProgBounded.seq (ProgBounded.call hpc _ _)
                                                            (ProgBounded.seq (ProgBounded.call funBounded_heap_release _ _)
                                                              (ProgBounded.seq (ProgBounded.call funBounded_htr_u64_at _ _)
                                                                (ProgBounded.seq (ProgBounded.call funBounded_htr_u64_at _ _)
                                                                  (ProgBounded.seq (ProgBounded.call hpb _ _)
                                                                    (ProgBounded.seq (ProgBounded.call funBounded_htr_u64_at _ _)
                                                                      (ProgBounded.seq (ProgBounded.call hpcont _ _)
                                                                        (ProgBounded.seq (ProgBounded.call funBounded_heap_release _ _)
                                                                          (ProgBounded.straight _ rfl)))))))))))))))))))))))))))))))))))))
    ?_
  have h32 : (32#64).toNat = 32 := rfl
  rw [h32]
  generalize (2 : Nat) ^ 64 - 1 = W
  generalize W * (K_pack_bytes + K_merkleize_progressive + 23 + 1 + 1) = A
  generalize W * (K_pack_bytes + K_merkleize_progressive + 25) = A'
  generalize W * (K_pack_bytes + 2 * K_merkleize + 100 + 1 + 1) = B
  generalize W * (K_pack_bytes + 2 * K_merkleize + 102) = B'
  omega

theorem funBounded_htr_deposit
    (K_pack_bytes K_merkleize : Nat)
    (h_pack_bytes : FunBounded (ofString "pack_bytes") K_pack_bytes)
    (h_merkleize : FunBounded (ofString "merkleize") K_merkleize) :
    FunBounded (ofString "htr_deposit") (2 * K_pack_bytes + 3 * K_merkleize + 117) := by
  refine funBounded_of_guestAst 211 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_htr_deposit _ rfl ?_
  have hbv := funBounded_htr_bytes_vector K_pack_bytes K_merkleize h_pack_bytes h_merkleize
  refine ProgBounded.weaken
    (ProgBounded.decCall funBounded_heap_mark _ _ _
      (ProgBounded.decCall funBounded_alloc _ _ _
        (ProgBounded.seq (ProgBounded.call hbv _ _)
          (ProgBounded.seq (progBounded_memcpy_const _ _ _ 32#64 (by decide))
            (ProgBounded.seq (ProgBounded.call funBounded_htr_u64_at _ _)
              (ProgBounded.seq (ProgBounded.call hbv _ _)
                (ProgBounded.seq (ProgBounded.call funBounded_htr_u64_at _ _)
                  (ProgBounded.seq (ProgBounded.call h_merkleize _ _)
                    (ProgBounded.seq (ProgBounded.call funBounded_heap_release _ _)
                      (ProgBounded.straight _ rfl))))))))))
    ?_
  have h32 : (32#64).toNat = 32 := rfl
  rw [h32]
  omega

theorem funBounded_htr_wdreq
    (K_pack_bytes K_merkleize : Nat)
    (h_pack_bytes : FunBounded (ofString "pack_bytes") K_pack_bytes)
    (h_merkleize : FunBounded (ofString "merkleize") K_merkleize) :
    FunBounded (ofString "htr_wdreq") (2 * K_pack_bytes + 3 * K_merkleize + 85) := by
  refine funBounded_of_guestAst 212 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_htr_wdreq _ rfl ?_
  have hbv := funBounded_htr_bytes_vector K_pack_bytes K_merkleize h_pack_bytes h_merkleize
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_heap_mark _ _ _
      (ProgBounded.decCall funBounded_alloc _ _ _
        (ProgBounded.seq (ProgBounded.call hbv _ _)
          (ProgBounded.seq (ProgBounded.call hbv _ _)
            (ProgBounded.seq (ProgBounded.call funBounded_htr_u64_at _ _)
              (ProgBounded.seq (ProgBounded.call h_merkleize _ _)
                (ProgBounded.seq (ProgBounded.call funBounded_heap_release _ _)
                  (ProgBounded.straight _ rfl))))))))
    (by omega)

theorem funBounded_htr_cons
    (K_pack_bytes K_merkleize : Nat)
    (h_pack_bytes : FunBounded (ofString "pack_bytes") K_pack_bytes)
    (h_merkleize : FunBounded (ofString "merkleize") K_merkleize) :
    FunBounded (ofString "htr_cons") (3 * K_pack_bytes + 4 * K_merkleize + 92) := by
  refine funBounded_of_guestAst 213 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_htr_cons _ rfl ?_
  have hbv := funBounded_htr_bytes_vector K_pack_bytes K_merkleize h_pack_bytes h_merkleize
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_heap_mark _ _ _
      (ProgBounded.decCall funBounded_alloc _ _ _
        (ProgBounded.seq (ProgBounded.call hbv _ _)
          (ProgBounded.seq (ProgBounded.call hbv _ _)
            (ProgBounded.seq (ProgBounded.call hbv _ _)
              (ProgBounded.seq (ProgBounded.call h_merkleize _ _)
                (ProgBounded.seq (ProgBounded.call funBounded_heap_release _ _)
                  (ProgBounded.straight _ rfl))))))))
    (by omega)

theorem funBounded_htr_bdep
    (K_pack_bytes K_merkleize : Nat)
    (h_pack_bytes : FunBounded (ofString "pack_bytes") K_pack_bytes)
    (h_merkleize : FunBounded (ofString "merkleize") K_merkleize) :
    FunBounded (ofString "htr_bdep") (2 * K_pack_bytes + 3 * K_merkleize + 95) := by
  refine funBounded_of_guestAst 214 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_htr_bdep _ rfl ?_
  have hbv := funBounded_htr_bytes_vector K_pack_bytes K_merkleize h_pack_bytes h_merkleize
  refine ProgBounded.weaken
    (ProgBounded.decCall funBounded_heap_mark _ _ _
      (ProgBounded.decCall funBounded_alloc _ _ _
        (ProgBounded.seq (ProgBounded.call hbv _ _)
          (ProgBounded.seq (progBounded_memcpy_const _ _ _ 32#64 (by decide))
            (ProgBounded.seq (ProgBounded.call funBounded_htr_u64_at _ _)
              (ProgBounded.seq (ProgBounded.call hbv _ _)
                (ProgBounded.seq (ProgBounded.call h_merkleize _ _)
                  (ProgBounded.seq (ProgBounded.call funBounded_heap_release _ _)
                    (ProgBounded.straight _ rfl)))))))))
    ?_
  have h32 : (32#64).toNat = 32 := rfl
  rw [h32]
  omega

theorem funBounded_htr_bexit
    (K_pack_bytes K_merkleize : Nat)
    (h_pack_bytes : FunBounded (ofString "pack_bytes") K_pack_bytes)
    (h_merkleize : FunBounded (ofString "merkleize") K_merkleize) :
    FunBounded (ofString "htr_bexit") (2 * K_pack_bytes + 3 * K_merkleize + 63) := by
  refine funBounded_of_guestAst 215 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_htr_bexit _ rfl ?_
  have hbv := funBounded_htr_bytes_vector K_pack_bytes K_merkleize h_pack_bytes h_merkleize
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_heap_mark _ _ _
      (ProgBounded.decCall funBounded_alloc _ _ _
        (ProgBounded.seq (ProgBounded.call hbv _ _)
          (ProgBounded.seq (ProgBounded.call hbv _ _)
            (ProgBounded.seq (ProgBounded.call h_merkleize _ _)
              (ProgBounded.seq (ProgBounded.call funBounded_heap_release _ _)
                (ProgBounded.straight _ rfl)))))))
    (by omega)

theorem funBounded_htr_request_list
    (K_pack_bytes K_merkleize K_merkleize_progressive : Nat)
    (h_pack_bytes : FunBounded (ofString "pack_bytes") K_pack_bytes)
    (h_merkleize : FunBounded (ofString "merkleize") K_merkleize)
    (h_merkleize_progressive : FunBounded (ofString "merkleize_progressive") K_merkleize_progressive) :
    FunBounded (ofString "htr_request_list")
      ((2 ^ 64 - 1) * (11 * K_pack_bytes + 16 * K_merkleize + 458) +
        K_merkleize_progressive + 23) := by
  refine funBounded_of_guestAst 216 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_htr_request_list _ rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_htr_request_list,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  have hdep := funBounded_htr_deposit K_pack_bytes K_merkleize h_pack_bytes h_merkleize
  have hwdreq := funBounded_htr_wdreq K_pack_bytes K_merkleize h_pack_bytes h_merkleize
  have hcons := funBounded_htr_cons K_pack_bytes K_merkleize h_pack_bytes h_merkleize
  have hbdep := funBounded_htr_bdep K_pack_bytes K_merkleize h_pack_bytes h_merkleize
  have hbexit := funBounded_htr_bexit K_pack_bytes K_merkleize h_pack_bytes h_merkleize
  have hpc := funBounded_htr_plist_chunks K_merkleize_progressive h_merkleize_progressive
  refine ProgBounded.weaken
    (ProgBounded.decCall funBounded_heap_mark _ _ _
      (ProgBounded.decCall funBounded_alloc _ _ _
        (progBounded_varCountedDec (ofString "i") (ofString "n") .less (Or.inl rfl)
          (CountedBody.seq _
            (ProgBounded.iteMax _ (ProgBounded.call hdep _ _) (ProgBounded.straight _ rfl))
            rfl rfl
            (CountedBody.seq _
              (ProgBounded.iteMax _ (ProgBounded.call hwdreq _ _) (ProgBounded.straight _ rfl))
              rfl rfl
              (CountedBody.seq _
                (ProgBounded.iteMax _ (ProgBounded.call hcons _ _) (ProgBounded.straight _ rfl))
                rfl rfl
                (CountedBody.seq _
                  (ProgBounded.iteMax _ (ProgBounded.call hbdep _ _) (ProgBounded.straight _ rfl))
                  rfl rfl
                  (CountedBody.seq _
                    (ProgBounded.iteMax _ (ProgBounded.call hbexit _ _) (ProgBounded.straight _ rfl))
                    rfl rfl
                    CountedBody.incr)))))
          rfl
          (ProgBounded.seq (ProgBounded.call hpc _ _)
            (ProgBounded.seq (ProgBounded.call funBounded_heap_release _ _)
              (ProgBounded.straight _ rfl))))))
    ?_
  refine Nat.add_le_add ?_ (by omega)
  exact Nat.mul_le_mul_left _ (by omega)

theorem funBounded_htr_requests
    (K_pack_bytes K_merkleize K_merkleize_progressive : Nat)
    (h_pack_bytes : FunBounded (ofString "pack_bytes") K_pack_bytes)
    (h_merkleize : FunBounded (ofString "merkleize") K_merkleize)
    (h_merkleize_progressive : FunBounded (ofString "merkleize_progressive") K_merkleize_progressive) :
    FunBounded (ofString "htr_requests")
      (5 * ((2 ^ 64 - 1) * (11 * K_pack_bytes + 16 * K_merkleize + 458)) +
        6 * K_merkleize_progressive + (2 ^ 64 - 1) + 143) := by
  refine funBounded_of_guestAst 217 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_htr_requests _ rfl ?_
  have hrl := funBounded_htr_request_list K_pack_bytes K_merkleize K_merkleize_progressive
    h_pack_bytes h_merkleize h_merkleize_progressive
  have hpcont := funBounded_htr_pcontainer K_merkleize_progressive h_merkleize_progressive
  refine ProgBounded.weaken
    (ProgBounded.decCall funBounded_heap_mark _ _ _
      (ProgBounded.decCall funBounded_alloc _ _ _
        (ProgBounded.seq (ProgBounded.call hrl _ _)
          (ProgBounded.seq (ProgBounded.call hrl _ _)
            (ProgBounded.seq (ProgBounded.call hrl _ _)
              (ProgBounded.seq (ProgBounded.call hrl _ _)
                (ProgBounded.seq (ProgBounded.call hrl _ _)
                  (ProgBounded.seq (ProgBounded.call hpcont _ _)
                    (ProgBounded.seq (ProgBounded.call funBounded_heap_release _ _)
                      (ProgBounded.straight _ rfl))))))))))
    ?_
  generalize (2 ^ 64 - 1) * (11 * K_pack_bytes + 16 * K_merkleize + 458) = M
  generalize (2 : Nat) ^ 64 - 1 = W
  omega

/-! ## 5. Reduced top-level `main` bound -/

theorem funBounded_main_reduced
    (K_pack_bytes K_merkleize K_merkleize_progressive K_run_attempt : Nat)
    (h_pack_bytes : FunBounded (ofString "pack_bytes") K_pack_bytes)
    (h_merkleize : FunBounded (ofString "merkleize") K_merkleize)
    (h_merkleize_progressive : FunBounded (ofString "merkleize_progressive") K_merkleize_progressive)
    (h_run_attempt : FunBounded (ofString "run_attempt") K_run_attempt) :
    FunBounded (ofString "main")
      ((2 ^ 64 - 1) * (K_pack_bytes + K_merkleize_progressive + 25) +
        (2 ^ 64 - 1) * (K_pack_bytes + 2 * K_merkleize + 102) +
        5 * ((2 ^ 64 - 1) * (11 * K_pack_bytes + 16 * K_merkleize + 458)) +
        4 * K_pack_bytes + 4 * K_merkleize + 11 * K_merkleize_progressive + K_run_attempt +
        18 * (2 ^ 64 - 1) + 134220134) := by
  have hmain := funBounded_main_concrete
    (14 * (2 ^ 64 - 1) + 595)
    ((2 ^ 64 - 1) * (K_pack_bytes + K_merkleize_progressive + 25) +
      (2 ^ 64 - 1) * (K_pack_bytes + 2 * K_merkleize + 102) +
      4 * K_pack_bytes + 3 * K_merkleize + 4 * K_merkleize_progressive +
      (2 ^ 64 - 1) + 414)
    (K_merkleize_progressive + 18)
    (5 * ((2 ^ 64 - 1) * (11 * K_pack_bytes + 16 * K_merkleize + 458)) +
      6 * K_merkleize_progressive + (2 ^ 64 - 1) + 143)
    K_merkleize
    K_run_attempt
    funBounded_decode_stateless_input
    (funBounded_htr_payload K_pack_bytes K_merkleize K_merkleize_progressive
      h_pack_bytes h_merkleize h_merkleize_progressive)
    (funBounded_htr_plist_chunks K_merkleize_progressive h_merkleize_progressive)
    (funBounded_htr_requests K_pack_bytes K_merkleize K_merkleize_progressive
      h_pack_bytes h_merkleize h_merkleize_progressive)
    h_merkleize
    h_run_attempt
  obtain ⟨parameters, body, returnShape, lookup, bounded⟩ := hmain
  refine ⟨parameters, body, returnShape, lookup, ProgBounded.weaken bounded ?_⟩
  have hle :
      (14 * (2 ^ 64 - 1) + 595) +
        ((2 ^ 64 - 1) * (K_pack_bytes + K_merkleize_progressive + 25) +
          (2 ^ 64 - 1) * (K_pack_bytes + 2 * K_merkleize + 102) +
          4 * K_pack_bytes + 3 * K_merkleize + 4 * K_merkleize_progressive +
          (2 ^ 64 - 1) + 414) +
        (K_merkleize_progressive + 18) +
        (5 * ((2 ^ 64 - 1) * (11 * K_pack_bytes + 16 * K_merkleize + 458)) +
          6 * K_merkleize_progressive + (2 ^ 64 - 1) + 143) +
        K_merkleize + K_run_attempt + 2 * (2 ^ 64 - 1) + 134218964 ≤
      (2 ^ 64 - 1) * (K_pack_bytes + K_merkleize_progressive + 25) +
        (2 ^ 64 - 1) * (K_pack_bytes + 2 * K_merkleize + 102) +
        5 * ((2 ^ 64 - 1) * (11 * K_pack_bytes + 16 * K_merkleize + 458)) +
        4 * K_pack_bytes + 4 * K_merkleize + 11 * K_merkleize_progressive + K_run_attempt +
        18 * (2 ^ 64 - 1) + 134220134 := by
    generalize (2 ^ 64 - 1) * (K_pack_bytes + K_merkleize_progressive + 25) = A
    generalize (2 ^ 64 - 1) * (K_pack_bytes + 2 * K_merkleize + 102) = B
    generalize (2 ^ 64 - 1) * (11 * K_pack_bytes + 16 * K_merkleize + 458) = C
    generalize (2 : Nat) ^ 64 - 1 = W
    omega
  have hb := hmain state hcode (by omega) values body locals returnShape hlookup
  exact ⟨by omega, hb.2.1, hb.2.2⟩

end InitECandidate.Solver.GuestBoundSszHtr
