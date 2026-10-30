import InitECandidate.Solver.PanRunBoundedExt
import InitECandidate.Solver.GuestTrapAlign

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace InitECandidate.Solver.GuestBoundCryptoDiv

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.PanRunBoundedExt

theorem funBounded_nlz32 : FunBounded (ofString "nlz32") 0 :=
  funBounded_of_guestAst 62 (by rw [guestAst_len]; decide) Guest.Software.guestFn_nlz32 0 rfl
    (ProgBounded.straight _ rfl)

private theorem countedBody_seq_straight {counter : MlS} {step : BitVec 64}
    (first : ProgHOL 64) {tail : ProgHOL 64} {cost : Nat}
    (hs : extStraightLine first = true)
    (ha : avoidsLocal counter first = true)
    (hn : noTopContinue first = true)
    (hrest : CountedBody counter step tail cost) :
    CountedBody counter step (.seq first tail) cost := by
  simpa using CountedBody.seq first (ProgBounded.straight first hs) ha hn hrest

theorem funBounded_keccak_init : FunBounded (ofString "keccak_init") 6 := by
  refine funBounded_of_guestAst 100 (by rw [guestAst_len]; decide) Guest.Software.guestFn_keccak_init 6 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_keccak_init,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.seq (ProgBounded.alloc _ _)
      (ProgBounded.seq (ProgBounded.alloc _ _)
        (ProgBounded.seq (ProgBounded.alloc _ _)
          (ProgBounded.straight _ (by decide)))))
    (by decide)

theorem funBounded_keccak_f1600 : FunBounded (ofString "keccak_f1600") 24 := by
  refine funBounded_of_guestAst 101 (by rw [guestAst_len]; decide) Guest.Software.guestFn_keccak_f1600 24 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_keccak_f1600,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  iterate 25 apply ProgBounded.dec
  refine ProgBounded.weaken
    (ProgBounded.countedDec (ofString "r") .less (Or.inl rfl) 24 1 0
      (by decide) (by decide) (by decide) (cost := 0) ?_ (ProgBounded.straight _ (by decide)))
    (by decide)
  iterate 60 (refine CountedBody.dec _ _ _ (by decide) ?_)
  iterate 26 (refine countedBody_seq_straight _ (by decide) (by decide) (by decide) ?_)
  exact CountedBody.incr

theorem funBounded_keccak_absorb_block : FunBounded (ofString "keccak_absorb_block") 161 := by
  refine funBounded_of_guestAst 102 (by rw [guestAst_len]; decide) Guest.Software.guestFn_keccak_absorb_block 161 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_keccak_absorb_block,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  intro F state hcode hbudget
  apply RunBounded.decConst
  let s0 := setVarHOLFinite (ofString "i") (.val (.word 0)) state
  have hs0_code : s0.code = originalRuntimeCode := hcode
  have hs0_i : s0.locals.lookup (ofString "i") = some (.val (.word 0)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have htail : ProgBounded
      (.seq (.call (some (none, none)) (ofString "keccak_f1600") [.var .local (ofString "stp")])
        (.return (.const 0))) 25 :=
    ProgBounded.seq (ProgBounded.call funBounded_keccak_f1600 none [.var .local (ofString "stp")])
      (ProgBounded.straight _ (by decide))
  refine RunBounded.seq ?_ (a := 136) (b := 25) (by change 136 + 25 ≤ state.clock; omega)
    (fun next _ nextCode nextBudget => htail next (nextCode.trans hs0_code) nextBudget)
  apply RunBounded.ite
  · unfold RunBounded
    exact countedWhile_from (ofString "i") .less (Or.inl rfl) 136 8 (by decide) (by decide) (cost := 0)
      (countedBody_seq_straight _ (by decide) (by decide) (by decide) CountedBody.incr)
      s0 hs0_code 0 hs0_i (by decide) (by change 136 * (0 + 1) ≤ state.clock; omega)
  · unfold RunBounded
    exact countedWhile_from (ofString "i") .less (Or.inl rfl) 136 8 (by decide) (by decide) (cost := 0)
      (countedBody_seq_straight _ (by decide) (by decide) (by decide) CountedBody.incr)
      s0 hs0_code 0 hs0_i (by decide) (by change 136 * (0 + 1) ≤ state.clock; omega)

inductive DecBody (counter : MlS) : ProgHOL 64 → Nat → Prop
  | decr : DecBody counter (.assign .local counter (.op .sub [.var .local counter, .const 1])) 0
  | seq (first : ProgHOL 64) {tail : ProgHOL 64} {a b : Nat} (bounded : ProgBounded first a)
      (avoid : avoidsLocal counter first = true) (noCont : noTopContinue first = true)
      (rest : DecBody counter tail b) : DecBody counter (.seq first tail) (a + b)
  | dec (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL 64) {body : ProgHOL 64} {cost : Nat}
      (distinct : counter ≠ name) (rest : DecBody counter body cost) :
      DecBody counter (.dec name shape initializer body) cost

private theorem decBody_run {counter : MlS} {body : ProgHOL 64} {cost : Nat}
    (counted : DecBody counter body cost) {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode) (w : BitVec 64)
    (atCounter : state.locals.lookup counter = some (.val (.word w))) (budget : cost ≤ state.clock) :
    state.clock ≤ (evaluateHOLFiniteState state body).2.clock + cost ∧
      (evaluateHOLFiniteState state body).2.clock ≤ state.clock ∧
      (evaluateHOLFiniteState state body).1 ≠ some .timeOut ∧
      (evaluateHOLFiniteState state body).1 ≠ some .continue ∧
      ((evaluateHOLFiniteState state body).1 = none →
        (evaluateHOLFiniteState state body).2.locals.lookup counter = some (.val (.word (w - 1))) ∧
        (evaluateHOLFiniteState state body).2.code = state.code) := by
  induction counted generalizing state with
  | decr =>
    have run : evaluateHOLFiniteState state (.assign .local counter (.op .sub [.var .local counter, .const 1])) =
        (none, setVarHOLFinite counter (.val (.word (w - 1))) state) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, atCounter, wordOpHOL, wordOp,
        valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
        shapeOfHOLExact, shapeEqHOL]
    rw [run]
    refine ⟨by simp [setVarHOLFinite], by simp [setVarHOLFinite], by simp, by simp, fun _ => ⟨?_, rfl⟩⟩
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  | seq first bounded avoid noCont rest ih =>
    rename_i tail a b
    have firstBound := bounded state code (by omega)
    have frame := evaluate_avoidsLocal_flowing counter first avoid state
    have noContinue := evaluate_noTopContinue first noCont state
    have meta' := PanRunBounded.evaluateHOLFiniteState_metadata state first
    rw [evaluateHOLFiniteState_seq_line780]
    cases firstRun : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [firstRun] at firstBound frame noContinue meta'
      dsimp only at firstBound frame noContinue meta'
      obtain ⟨spent, kept, safe⟩ := firstBound
      cases result with
      | none =>
        dsimp only
        have kept' := frame (Or.inl rfl)
        obtain ⟨t1, t2, t3, t4, t5⟩ := ih middle (meta'.1.trans code) (by rw [kept']; exact atCounter) (by omega)
        refine ⟨by omega, by omega, t3, t4, fun normal => ?_⟩
        obtain ⟨i1, i2⟩ := t5 normal
        exact ⟨i1, i2.trans meta'.1⟩
      | some r =>
        dsimp only
        refine ⟨by omega, by omega, safe, noContinue, fun h => by simp at h⟩
  | dec name shape initializer distinct rest ih =>
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · exact ⟨Nat.le_add_right _ _, le_refl _, by simp, by simp, by simp⟩
    · rename_i val _
      split
      · let inner := setVarHOLFinite name val state
        have atInner : inner.locals.lookup counter = some (.val (.word w)) := by
          simp [inner, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm distinct, atCounter]
        obtain ⟨t1, t2, t3, t4, t5⟩ := ih inner code atInner budget
        cases run : evaluateHOLFiniteState inner _ with
        | mk res post =>
          rw [run] at t1 t2 t3 t4 t5
          dsimp only at t1 t2 t3 t4 t5 ⊢
          refine ⟨t1, t2, t3, t4, fun normal => ?_⟩
          obtain ⟨i1, i2⟩ := t5 normal
          refine ⟨?_, i2⟩
          rw [PanRunBounded.resVarEq_lookup, if_neg distinct]
          exact i1
      · exact ⟨Nat.le_add_right _ _, le_refl _, by simp, by simp, by simp⟩

theorem eval_zero_lt_condition {F : Type} (state : PanSemStateFiniteExact 64 F) (counter : MlS)
    (w : BitVec 64) (atCounter : state.locals.lookup counter = some (.val (.word w))) :
    evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      (.cmp .lower (.const 0) (.var .local counter)) =
      some (.val (.word (if 0 < w.toNat then 1 else 0))) := by
  rw [evalHOLFinite_eq_toExact]
  simp only [evalHOLExact, atCounter, Compiler.Encoders.Asm.wordCmpHOL]
  by_cases lt : 0 < w.toNat <;> simp [lt, BitVec.lt_def]

theorem downWhile_run (counter : MlS) {body : ProgHOL 64} {cost : Nat}
    (counted : DecBody counter body cost) :
    ∀ n : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.code = originalRuntimeCode →
      ∀ w : BitVec 64, state.locals.lookup counter = some (.val (.word w)) →
      w.toNat ≤ n → n * (cost + 1) ≤ state.clock →
      state.clock ≤ (evaluateHOLFiniteState state
        (.while (.cmp .lower (.const 0) (.var .local counter)) body)).2.clock + n * (cost + 1) ∧
        (evaluateHOLFiniteState state (.while (.cmp .lower (.const 0) (.var .local counter)) body)).2.clock ≤
          state.clock ∧
        (evaluateHOLFiniteState state (.while (.cmp .lower (.const 0) (.var .local counter)) body)).1 ≠
          some .timeOut := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro F state code w atCounter within budget
    have condition := eval_zero_lt_condition state counter w atCounter
    rw [evaluateHOLFiniteState_while_total, condition]
    by_cases lt : 0 < w.toNat
    · rw [if_pos lt]
      simp only [show (1 : BitVec 64) ≠ 0 by decide, if_true, ne_eq, not_false_eq_true]
      have positiveRank : 0 < n := by omega
      have clock : state.clock ≠ 0 := by
        have : cost + 1 ≤ n * (cost + 1) := Nat.le_mul_of_pos_left _ positiveRank
        omega
      rw [if_neg clock]
      rw [fixClockHOLFinite_evaluateState]
      have decCode : (decClockHOLFinite state).code = originalRuntimeCode := code
      have stepRun := decBody_run counted (decClockHOLFinite state) decCode w atCounter (by
        change cost ≤ state.clock - 1
        have : cost + 1 ≤ n * (cost + 1) := Nat.le_mul_of_pos_left _ positiveRank
        omega)
      have meta' := PanRunBounded.evaluateHOLFiniteState_metadata (decClockHOLFinite state) body
      cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
      | mk result middle =>
        rw [bodyRun] at stepRun meta'
        dsimp only at stepRun meta'
        obtain ⟨spent, kept, safe, noCont, advance⟩ := stepRun
        change state.clock - 1 ≤ middle.clock + cost at spent
        change middle.clock ≤ state.clock - 1 at kept
        have oneIteration : cost + 1 ≤ n * (cost + 1) := Nat.le_mul_of_pos_left _ positiveRank
        cases result with
        | none =>
          dsimp only
          obtain ⟨nextCounter, nextCode⟩ := advance rfl
          have one_toNat : (1 : BitVec 64).toNat = 1 := rfl
          have hle : (1 : BitVec 64) ≤ w := by
            rw [BitVec.le_def, one_toNat]; omega
          have natural : (w - 1).toNat = w.toNat - 1 := by
            rw [BitVec.toNat_sub_of_le hle, one_toNat]
          have spent' : state.clock ≤ middle.clock + cost + 1 := Nat.sub_le_iff_le_add.mp spent
          have hmul : (n - 1) * (cost + 1) + (cost + 1) = n * (cost + 1) := by
            have hsucc : n - 1 + 1 = n := by omega
            calc (n - 1) * (cost + 1) + (cost + 1) = (n - 1 + 1) * (cost + 1) := by
                  rw [Nat.add_mul, Nat.one_mul]
              _ = n * (cost + 1) := by rw [hsucc]
          have tail := ih (n - 1) (by omega) middle (nextCode.trans code) (w - 1) nextCounter
            (by rw [natural]; omega) (by omega)
          obtain ⟨t1, t2, t3⟩ := tail
          refine ⟨?_, by omega, t3⟩
          omega
        | some r =>
          cases r with
          | «continue» => exact absurd rfl noCont
          | «break» => exact ⟨by simp; omega, by simp; omega, by simp⟩
          | timeOut => exact absurd rfl safe
          | _ => exact ⟨by simp; omega, by simp; omega, by simp⟩
    · rw [if_neg lt]
      simp

theorem ProgBounded.countedDownDec (counter : MlS) (K : BitVec 64)
    {body tail : ProgHOL 64} {cost tailCost : Nat} (counted : DecBody counter body cost)
    (rest : ProgBounded tail tailCost) :
    ProgBounded (.dec counter .one (.const K)
      (.seq (.while (.cmp .lower (.const 0) (.var .local counter)) body) tail))
      (K.toNat * (cost + 1) + tailCost) := by
  intro F state code budget
  rw [evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true]
  let entered := setVarHOLFinite counter (.val (.word K)) state
  have atCounter : entered.locals.lookup counter = some (.val (.word K)) := by
    simp [entered, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have loop := downWhile_run counter counted K.toNat entered code K atCounter (le_refl _) (by
    change K.toNat * (cost + 1) ≤ state.clock; omega)
  have meta' := PanRunBounded.evaluateHOLFiniteState_metadata entered (.while (.cmp .lower (.const 0) (.var .local counter)) body)
  change state.clock ≤ (evaluateHOLFiniteState entered _).2.clock + _ ∧
    (evaluateHOLFiniteState entered _).2.clock ≤ state.clock ∧ (evaluateHOLFiniteState entered _).1 ≠ some .timeOut
  rw [evaluateHOLFiniteState_seq_line780]
  cases loopRun : evaluateHOLFiniteState entered (.while (.cmp .lower (.const 0) (.var .local counter)) body) with
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

theorem eval_zero_less_or_lower_condition {F : Type} (state : PanSemStateFiniteExact 64 F) (counter : MlS)
    (op : Cmp) (hop : op = .less ∨ op = .lower) (w : BitVec 64)
    (hsmall : op = .less → w.toNat < 2 ^ 63)
    (atCounter : state.locals.lookup counter = some (.val (.word w))) :
    evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      (.cmp op (.const 0) (.var .local counter)) =
      some (.val (.word (if 0 < w.toNat then 1 else 0))) := by
  rcases hop with rfl | rfl
  · rw [evalHOLFinite_eq_toExact]
    have h0 : (0 : BitVec 64).toNat < 2 ^ 63 := by decide
    simp only [evalHOLExact, atCounter, Compiler.Encoders.Asm.wordCmpHOL,
      holAsmSignedLess_small 0 w h0 (hsmall rfl)]
    by_cases lt : 0 < w.toNat <;> simp [lt]
  · exact eval_zero_lt_condition state counter w atCounter

theorem downWhile_less_run (counter : MlS) {body : ProgHOL 64} {cost : Nat}
    (hbefore : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      state.code = originalRuntimeCode →
      state.locals.lookup counter = some (.val (.word w)) →
      0 < w.toNat →
      cost ≤ state.clock →
      state.clock ≤ (evaluateHOLFiniteState state body).2.clock + cost ∧
        (evaluateHOLFiniteState state body).2.clock ≤ state.clock ∧
        (evaluateHOLFiniteState state body).1 ≠ some .timeOut ∧
        (evaluateHOLFiniteState state body).1 ≠ some .continue ∧
        ((evaluateHOLFiniteState state body).1 = none →
          (evaluateHOLFiniteState state body).2.locals.lookup counter = some (.val (.word (w - 1))) ∧
          (evaluateHOLFiniteState state body).2.code = state.code)) :
    ∀ n : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.code = originalRuntimeCode →
      ∀ (op : Cmp), (op = .less ∨ op = .lower) →
      ∀ w : BitVec 64, state.locals.lookup counter = some (.val (.word w)) →
      (op = .less → w.toNat < 2 ^ 63) →
      w.toNat ≤ n → n * (cost + 1) ≤ state.clock →
      state.clock ≤ (evaluateHOLFiniteState state
        (.while (.cmp op (.const 0) (.var .local counter)) body)).2.clock + n * (cost + 1) ∧
        (evaluateHOLFiniteState state (.while (.cmp op (.const 0) (.var .local counter)) body)).2.clock ≤
          state.clock ∧
        (evaluateHOLFiniteState state (.while (.cmp op (.const 0) (.var .local counter)) body)).1 ≠
          some .timeOut := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro F state code op hop w atCounter hsmall within budget
    have condition := eval_zero_less_or_lower_condition state counter op hop w hsmall atCounter
    rw [evaluateHOLFiniteState_while_total, condition]
    by_cases lt : 0 < w.toNat
    · rw [if_pos lt]
      simp only [show (1 : BitVec 64) ≠ 0 by decide, if_true, ne_eq, not_false_eq_true]
      have positiveRank : 0 < n := by omega
      have oneIteration : cost + 1 ≤ n * (cost + 1) := Nat.le_mul_of_pos_left _ positiveRank
      have clock : state.clock ≠ 0 := by omega
      rw [if_neg clock, fixClockHOLFinite_evaluateState]
      have stepRun := hbefore (decClockHOLFinite state) w code atCounter lt
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
          have hle : (1 : BitVec 64) ≤ w := by rw [BitVec.le_def, one_toNat]; omega
          have natural : (w - 1).toNat = w.toNat - 1 := by
            rw [BitVec.toNat_sub_of_le hle, one_toNat]
          have hsmall' : op = .less → (w - 1).toNat < 2 ^ 63 := by
            intro hop'; have := hsmall hop'; rw [natural]; omega
          have hmul : (n - 1) * (cost + 1) + (cost + 1) = n * (cost + 1) := by
            have hsucc : n - 1 + 1 = n := by omega
            calc (n - 1) * (cost + 1) + (cost + 1) = (n - 1 + 1) * (cost + 1) := by
                  rw [Nat.add_mul, Nat.one_mul]
              _ = n * (cost + 1) := by rw [hsucc]
          obtain ⟨t1, t2, t3⟩ := ih (n - 1) (by omega) middle (nextCode.trans code) op hop (w - 1)
            nextCounter hsmall' (by rw [natural]; omega) (by omega)
          exact ⟨by omega, by omega, t3⟩
        | some r =>
          cases r with
          | «continue» => exact absurd rfl noCont
          | «break» => exact ⟨by simp; omega, by simp; omega, by simp⟩
          | timeOut => exact absurd rfl safe
          | _ => exact ⟨by simp; omega, by simp; omega, by simp⟩
    · rw [if_neg lt]
      simp

private theorem decFirst_step {counter : MlS} {tail : ProgHOL 64} {cost : Nat}
    (htail : ProgBounded tail cost) (havoid : avoidsLocal counter tail = true)
    (hnocont : noTopContinue tail = true)
    {F : Type} (state : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (atCounter : state.locals.lookup counter = some (.val (.word w)))
    (_hlt : 0 < w.toNat) (budget : cost ≤ state.clock) :
    let body : ProgHOL 64 := .seq (.assign .local counter (.op .sub [.var .local counter, .const 1])) tail
    state.clock ≤ (evaluateHOLFiniteState state body).2.clock + cost ∧
      (evaluateHOLFiniteState state body).2.clock ≤ state.clock ∧
      (evaluateHOLFiniteState state body).1 ≠ some .timeOut ∧
      (evaluateHOLFiniteState state body).1 ≠ some .continue ∧
      ((evaluateHOLFiniteState state body).1 = none →
        (evaluateHOLFiniteState state body).2.locals.lookup counter = some (.val (.word (w - 1))) ∧
        (evaluateHOLFiniteState state body).2.code = state.code) := by
  dsimp only
  have run1 : evaluateHOLFiniteState state (.assign .local counter (.op .sub [.var .local counter, .const 1])) =
      (none, setVarHOLFinite counter (.val (.word (w - 1))) state) := by
    simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, atCounter, wordOpHOL, wordOp,
      valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
      shapeOfHOLExact, shapeEqHOL]
  rw [evaluateHOLFiniteState_seq_line780, run1]
  dsimp only
  let s1 := setVarHOLFinite counter (.val (.word (w - 1))) state
  have hs1_clk : s1.clock = state.clock := rfl
  have hs1_code : s1.code = originalRuntimeCode := code
  have hs1_cnt : s1.locals.lookup counter = some (.val (.word (w - 1))) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hb := htail s1 hs1_code (by rw [hs1_clk]; exact budget)
  have hfr := evaluate_avoidsLocal_flowing counter tail havoid s1
  have hnc := evaluate_noTopContinue tail hnocont s1
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata s1 tail
  rcases hrun : evaluateHOLFiniteState s1 tail with ⟨res, s2⟩
  rw [hrun] at hb hfr hnc hmeta
  dsimp only at hb hfr hnc hmeta ⊢
  refine ⟨by rw [← hs1_clk]; exact hb.1, by rw [← hs1_clk]; exact hb.2.1, hb.2.2, hnc, fun hnone => ?_⟩
  exact ⟨(hfr (Or.inl hnone)).trans hs1_cnt, hmeta.1⟩

theorem ProgBounded.countedDownDecFirst (counter : MlS) (op : Cmp) (hop : op = .less ∨ op = .lower)
    (K : BitVec 64) (hsmall : op = .less → K.toNat < 2 ^ 63)
    {tailLoop tail : ProgHOL 64} {cost tailCost : Nat}
    (htail : ProgBounded tailLoop cost)
    (havoid : avoidsLocal counter tailLoop = true)
    (hnocont : noTopContinue tailLoop = true)
    (rest : ProgBounded tail tailCost) :
    ProgBounded (.dec counter .one (.const K)
      (.seq (.while (.cmp op (.const 0) (.var .local counter))
        (.seq (.assign .local counter (.op .sub [.var .local counter, .const 1])) tailLoop)) tail))
      (K.toNat * (cost + 1) + tailCost) := by
  intro F state code budget
  rw [evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true]
  let entered := setVarHOLFinite counter (.val (.word K)) state
  let lbody : ProgHOL 64 := .seq (.assign .local counter (.op .sub [.var .local counter, .const 1])) tailLoop
  have atCounter : entered.locals.lookup counter = some (.val (.word K)) := by
    simp [entered, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have loop := downWhile_less_run counter
    (fun s w hc hat hlt hb => decFirst_step htail havoid hnocont s w hc hat hlt hb)
    K.toNat entered code op hop K atCounter hsmall (le_refl _)
    (by change K.toNat * (cost + 1) ≤ state.clock; omega)
  have meta' := PanRunBounded.evaluateHOLFiniteState_metadata entered (.while (.cmp op (.const 0) (.var .local counter)) lbody)
  change state.clock ≤ (evaluateHOLFiniteState entered _).2.clock + _ ∧
    (evaluateHOLFiniteState entered _).2.clock ≤ state.clock ∧ (evaluateHOLFiniteState entered _).1 ≠ some .timeOut
  rw [evaluateHOLFiniteState_seq_line780]
  cases loopRun : evaluateHOLFiniteState entered (.while (.cmp op (.const 0) (.var .local counter)) lbody) with
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

theorem funBounded_div64by32 : FunBounded (ofString "div64by32") 32 := by
  refine funBounded_of_guestAst 63 (by rw [guestAst_len]; decide) Guest.Software.guestFn_div64by32 32 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_div64by32,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply ProgBounded.dec
  apply ProgBounded.dec
  exact ProgBounded.weaken
    (ProgBounded.countedDownDecFirst (ofString "i") .less (Or.inl rfl) 32 (fun _ => by decide)
      (ProgBounded.seq (ProgBounded.straight _ (by decide))
        (ProgBounded.ite _ (ProgBounded.straight _ (by decide)) (ProgBounded.straight _ (by decide))))
      (by decide) (by decide) (ProgBounded.straight _ (by decide)))
    (by decide)

theorem progBounded_downLowerDecrFirst (counter : MlS) {tailLoop : ProgHOL 64} {cost : Nat}
    (htail : ProgBounded tailLoop cost)
    (havoid : avoidsLocal counter tailLoop = true)
    (hnocont : noTopContinue tailLoop = true) :
    ProgBounded (.while (.cmp .lower (.const 0) (.var .local counter))
      (.seq (.assign .local counter (.op .sub [.var .local counter, .const 1])) tailLoop))
      ((2 ^ 64 - 1) * (cost + 1)) := by
  intro F state code budget
  cases hcnt : state.locals.lookup counter with
  | none =>
    rw [evaluateHOLFiniteState_while_total]
    have hnone : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
        (.cmp .lower (.const 0) (.var .local counter)) = none := by
      rw [evalHOLFinite_eq_toExact]; simp [evalHOLExact, hcnt]
    rw [hnone]; simp
  | some v =>
    cases v with
    | rStruct fields =>
      rw [evaluateHOLFiniteState_while_total]
      have hnone : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
          (.cmp .lower (.const 0) (.var .local counter)) = none := by
        rw [evalHOLFinite_eq_toExact]; simp [evalHOLExact, hcnt]
      rw [hnone]; simp
    | nStruct name fields =>
      rw [evaluateHOLFiniteState_while_total]
      have hnone : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
          (.cmp .lower (.const 0) (.var .local counter)) = none := by
        rw [evalHOLFinite_eq_toExact]; simp [evalHOLExact, hcnt]
      rw [hnone]; simp
    | val wv =>
      cases wv with
      | word w =>
        have hw : w.toNat ≤ 2 ^ 64 - 1 := by have := w.isLt; omega
        exact downWhile_less_run counter
          (fun s w' hc hat hlt hb => decFirst_step htail havoid hnocont s w' hc hat hlt hb)
          (2 ^ 64 - 1) state code .lower (Or.inr rfl) w hcnt (fun h => by cases h) hw budget

theorem progBounded_downLowerDecBody (counter : MlS) {body : ProgHOL 64} {cost : Nat}
    (counted : DecBody counter body cost) :
    ProgBounded (.while (.cmp .lower (.const 0) (.var .local counter)) body)
      ((2 ^ 64 - 1) * (cost + 1)) := by
  intro F state code budget
  cases hcnt : state.locals.lookup counter with
  | none =>
    rw [evaluateHOLFiniteState_while_total]
    have hnone : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
        (.cmp .lower (.const 0) (.var .local counter)) = none := by
      rw [evalHOLFinite_eq_toExact]; simp [evalHOLExact, hcnt]
    rw [hnone]; simp
  | some v =>
    cases v with
    | rStruct fields =>
      rw [evaluateHOLFiniteState_while_total]
      have hnone : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
          (.cmp .lower (.const 0) (.var .local counter)) = none := by
        rw [evalHOLFinite_eq_toExact]; simp [evalHOLExact, hcnt]
      rw [hnone]; simp
    | nStruct name fields =>
      rw [evaluateHOLFiniteState_while_total]
      have hnone : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
          (.cmp .lower (.const 0) (.var .local counter)) = none := by
        rw [evalHOLFinite_eq_toExact]; simp [evalHOLExact, hcnt]
      rw [hnone]; simp
    | val wv =>
      cases wv with
      | word w =>
        have hw : w.toNat ≤ 2 ^ 64 - 1 := by have := w.isLt; omega
        exact downWhile_run counter counted (2 ^ 64 - 1) state code w hcnt hw budget

theorem progBounded_upLowerAny (counter limit : MlS) {body : ProgHOL 64} {cost : Nat}
    (counted : CountedBody counter 1 body cost)
    (preservesLimit : avoidsLocal limit body = true) :
    ProgBounded (.while (.cmp .lower (.var .local counter) (.var .local limit)) body)
      ((2 ^ 64 - 1) * (cost + 1)) := by
  intro F state code budget
  cases hcnt : state.locals.lookup counter with
  | none =>
    rw [evaluateHOLFiniteState_while_total]
    have hnone : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
        (.cmp .lower (.var .local counter) (.var .local limit)) = none := by
      rw [evalHOLFinite_eq_toExact]; simp [evalHOLExact, hcnt]
    rw [hnone]; simp
  | some vc =>
    cases vc with
    | rStruct fields =>
      rw [evaluateHOLFiniteState_while_total]
      have hnone : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
          (.cmp .lower (.var .local counter) (.var .local limit)) = none := by
        rw [evalHOLFinite_eq_toExact]; simp [evalHOLExact, hcnt]
      rw [hnone]; simp
    | nStruct name fields =>
      rw [evaluateHOLFiniteState_while_total]
      have hnone : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
          (.cmp .lower (.var .local counter) (.var .local limit)) = none := by
        rw [evalHOLFinite_eq_toExact]; simp [evalHOLExact, hcnt]
      rw [hnone]; simp
    | val wc =>
      cases wc with
      | word w =>
        cases hlim : state.locals.lookup limit with
        | none =>
          rw [evaluateHOLFiniteState_while_total]
          have hnone : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
              (.cmp .lower (.var .local counter) (.var .local limit)) = none := by
            rw [evalHOLFinite_eq_toExact]; simp [evalHOLExact, hcnt, hlim]
          rw [hnone]; simp
        | some vl =>
          cases vl with
          | rStruct fields =>
            rw [evaluateHOLFiniteState_while_total]
            have hnone : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
                (.cmp .lower (.var .local counter) (.var .local limit)) = none := by
              rw [evalHOLFinite_eq_toExact]; simp [evalHOLExact, hcnt, hlim]
            rw [hnone]; simp
          | nStruct name fields =>
            rw [evaluateHOLFiniteState_while_total]
            have hnone : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
                (.cmp .lower (.var .local counter) (.var .local limit)) = none := by
              rw [evalHOLFinite_eq_toExact]; simp [evalHOLExact, hcnt, hlim]
            rw [hnone]; simp
          | val wl =>
            cases wl with
            | word K =>
              by_cases hle : w.toNat ≤ K.toNat
              · have hceil : (K.toNat - w.toNat) * (cost + 1) ≤ (2 ^ 64 - 1) * (cost + 1) :=
                  Nat.mul_le_mul_right _ (by have := K.isLt; omega)
                have hrun := variableCountedWhile_run counter limit .lower (Or.inr rfl) K
                  (fun h => by cases h) counted preservesLimit (K.toNat - w.toNat) state code w
                  hcnt hlim hle rfl (by omega)
                dsimp only at hrun ⊢
                exact ⟨by omega, hrun.2.1, hrun.2.2⟩
              · rw [evaluateHOLFiniteState_while_total]
                have hzero : evalHOLFinite state
                    (h := fun a => Classical.propDecidable (state.memaddrs a))
                    (.cmp .lower (.var .local counter) (.var .local limit)) = some (.val (.word 0)) := by
                  rw [evalHOLFinite_eq_toExact]
                  simp [evalHOLExact, hcnt, hlim, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
                  omega
                rw [hzero]; simp

private def divmnuAgainBody : ProgHOL 64 :=
  .seq (.assign .local (ofString "again") (.const 0))
    (.ite (.cmp .lower (.var .local (ofString "rhat")) (.const 4294967296))
      (.ite (.cmp .lower
          (.op .or [.shift .lsl (.var .local (ofString "rhat")) (.const 32),
            .var .local (ofString "ujn2")])
          (.panop .mul [.var .local (ofString "qhat"), .var .local (ofString "vsec")]))
        (.seq (.assign .local (ofString "qhat") (.op .sub [.var .local (ofString "qhat"), .const 1]))
          (.seq (.assign .local (ofString "rhat") (.op .add [.var .local (ofString "rhat"), .var .local (ofString "vtop")]))
            (.assign .local (ofString "again") (.const 1))))
        .skip)
      .skip)

private def divmnuAgainRank {F : Type} (s : PanSemStateFiniteExact 64 F) (n : Nat) : Prop :=
  match s.locals.lookup (ofString "again") with
  | some (.val (.word a)) =>
    if a = 1 then
      match s.locals.lookup (ofString "qhat") with
      | some (.val (.word q)) => q.toNat + 1 ≤ n
      | _ => 1 ≤ n
    else True
  | _ => True

private theorem progBounded_divmnu_again :
    ProgBounded (.while (.cmp .equal (.var .local (ofString "again")) (.const 1)) divmnuAgainBody)
      (2 ^ 64) := by
  intro F state code budget
  have hrank0 : divmnuAgainRank state (2 ^ 64) := by
    unfold divmnuAgainRank
    split
    · split
      · split
        · rename_i q _; have := q.isLt; omega
        · omega
      · trivial
    · trivial
  have hexit : ∀ {F' : Type} (s : PanSemStateFiniteExact 64 F'), divmnuAgainRank s 0 →
      ∀ w : BitVec 64,
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .equal (.var .local (ofString "again")) (.const 1)) = some (.val (.word w)) → w = 0 := by
    intro F' s hr0 w heval
    rw [evalHOLFinite_eq_toExact] at heval
    unfold divmnuAgainRank at hr0
    cases hagain : s.locals.lookup (ofString "again") with
    | none => simp [evalHOLExact, hagain] at heval
    | some va =>
      cases va with
      | rStruct _ => simp [evalHOLExact, hagain] at heval
      | nStruct _ _ => simp [evalHOLExact, hagain] at heval
      | val wa =>
        cases wa with
        | word a =>
          rw [hagain] at hr0
          dsimp only at hr0
          by_cases ha1 : a = 1
          · rw [if_pos ha1] at hr0
            cases hq : s.locals.lookup (ofString "qhat") with
            | none => rw [hq] at hr0; omega
            | some vq =>
              cases vq with
              | rStruct _ => rw [hq] at hr0; omega
              | nStruct _ _ => rw [hq] at hr0; omega
              | val wq =>
                cases wq with
                | word q => rw [hq] at hr0; omega
          · have ha1' : a ≠ 1#64 := ha1
            simp [evalHOLExact, hagain, Compiler.Encoders.Asm.wordCmpHOL, ha1'] at heval
            exact heval.symm
  have hstep : ∀ {F' : Type} (s : PanSemStateFiniteExact 64 F') (n : Nat) (w : BitVec 64),
      s.code = originalRuntimeCode →
      divmnuAgainRank s (n + 1) →
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .equal (.var .local (ofString "again")) (.const 1)) = some (.val (.word w)) →
      w ≠ 0 → 0 + 1 ≤ s.clock →
      s.clock - 1 ≤ (evaluateHOLFiniteState (decClockHOLFinite s) divmnuAgainBody).2.clock + 0 ∧
        (evaluateHOLFiniteState (decClockHOLFinite s) divmnuAgainBody).2.clock ≤ s.clock - 1 ∧
        (evaluateHOLFiniteState (decClockHOLFinite s) divmnuAgainBody).1 ≠ some .timeOut ∧
        ((evaluateHOLFiniteState (decClockHOLFinite s) divmnuAgainBody).1 = none ∨
            (evaluateHOLFiniteState (decClockHOLFinite s) divmnuAgainBody).1 = some .continue →
          ∃ m, m ≤ n ∧ divmnuAgainRank (evaluateHOLFiniteState (decClockHOLFinite s) divmnuAgainBody).2 m ∧
            (evaluateHOLFiniteState (decClockHOLFinite s) divmnuAgainBody).2.code = s.code) ∧
        ((evaluateHOLFiniteState (decClockHOLFinite s) divmnuAgainBody).1 = some .break → False ∧
          ∃ m, divmnuAgainRank (evaluateHOLFiniteState (decClockHOLFinite s) divmnuAgainBody).2 m ∧
            (evaluateHOLFiniteState (decClockHOLFinite s) divmnuAgainBody).2.code = s.code) := by
    intro F' s n w hscode hrank heval hw0 _hclk
    have hs1_bnd := (ProgBounded.straight divmnuAgainBody (by decide)) (decClockHOLFinite s) hscode (Nat.zero_le _)
    have hnobrk := evaluate_noTopBreak divmnuAgainBody (by decide) (decClockHOLFinite s)
    have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata (decClockHOLFinite s) divmnuAgainBody
    rw [evalHOLFinite_eq_toExact] at heval
    have hagain1 : s.locals.lookup (ofString "again") = some (.val (.word 1)) := by
      cases hagain : s.locals.lookup (ofString "again") with
      | none => simp [evalHOLExact, hagain] at heval
      | some va =>
        cases va with
        | rStruct _ => simp [evalHOLExact, hagain] at heval
        | nStruct _ _ => simp [evalHOLExact, hagain] at heval
        | val wa =>
          cases wa with
          | word a =>
            by_cases ha1 : a = 1
            · subst ha1; rfl
            · have ha1' : a ≠ 1#64 := ha1
              simp [evalHOLExact, hagain, Compiler.Encoders.Asm.wordCmpHOL, ha1'] at heval
              exact absurd heval.symm hw0
    refine ⟨hs1_bnd.1, hs1_bnd.2.1, hs1_bnd.2.2, ?_, fun hb => absurd hb hnobrk⟩
    intro _hcont
    refine ⟨n, le_refl _, ?_, hmeta.1⟩
    unfold divmnuAgainRank at hrank
    rw [hagain1] at hrank
    dsimp only at hrank
    rw [if_pos rfl] at hrank
    let s0 := decClockHOLFinite s
    have hs0_again : s0.locals.lookup (ofString "again") = some (.val (.word 1)) := hagain1
    have hs0_qhat : s0.locals.lookup (ofString "qhat") = s.locals.lookup (ofString "qhat") := rfl
    have hasgn0 : evaluateHOLFiniteState s0 (.assign .local (ofString "again") (.const 0)) =
        (none, setVarHOLFinite (ofString "again") (.val (.word 0)) s0) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, hs0_again, lookupKvarHOLExact,
        isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
    change divmnuAgainRank (evaluateHOLFiniteState s0 divmnuAgainBody).2 n
    unfold divmnuAgainBody
    rw [evaluateHOLFiniteState_seq_line780, hasgn0]
    dsimp only
    let s1 := setVarHOLFinite (ofString "again") (.val (.word 0)) s0
    have hs1_again0 : divmnuAgainRank s1 n := by
      unfold divmnuAgainRank
      have : s1.locals.lookup (ofString "again") = some (.val (.word 0)) := by
        simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      rw [this]; dsimp only; rw [if_neg (by decide)]; trivial
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · simp only [evaluateHOLFiniteState_skip]; exact hs1_again0
      · rw [evaluateHOLFiniteState_ite]
        split
        · split
          · simp only [evaluateHOLFiniteState_skip]; exact hs1_again0
          · rename_i _ c2 hc2 hnz2
            have hc2' : @evalHOLExact 64 F' _ s1.toExact
                (fun a => Classical.propDecidable (s1.memaddrs a))
                (.cmp .lower
                  (.op .or [.shift .lsl (.var .local (ofString "rhat")) (.const 32),
                    .var .local (ofString "ujn2")])
                  (.panop .mul [.var .local (ofString "qhat"), .var .local (ofString "vsec")])) =
                some (ValueHOL.val (HolWordLab.word c2)) := hc2
            clear hc2
            simp only [evalHOLExact, evalListHOLExact] at hc2'
            cases hrhat : s1.locals.lookup (ofString "rhat") with
            | none => simp [hrhat] at hc2'
            | some vr =>
              cases vr with
              | rStruct _ => simp [hrhat] at hc2'
              | nStruct _ _ => simp [hrhat] at hc2'
              | val wr =>
                cases wr with
                | word rhat =>
                  cases hujn2 : s1.locals.lookup (ofString "ujn2") with
                  | none => simp [hrhat, hujn2] at hc2'
                  | some vu =>
                    cases vu with
                    | rStruct _ => simp [hrhat, hujn2, wordShiftHOL, valueIsWord] at hc2'
                    | nStruct _ _ => simp [hrhat, hujn2, wordShiftHOL, valueIsWord] at hc2'
                    | val wu =>
                      cases wu with
                      | word ujn2 =>
                        cases hq : s1.locals.lookup (ofString "qhat") with
                        | none => simp [hq] at hc2'
                        | some vq =>
                          cases vq with
                          | rStruct _ =>
                            cases hvsec : s1.locals.lookup (ofString "vsec") <;>
                              simp [hq, hvsec, valueIsWord] at hc2'
                          | nStruct _ _ =>
                            cases hvsec : s1.locals.lookup (ofString "vsec") <;>
                              simp [hq, hvsec, valueIsWord] at hc2'
                          | val wq =>
                            cases wq with
                            | word q =>
                              have hs_q : s.locals.lookup (ofString "qhat") = some (.val (.word q)) := by
                                have hq' : s1.locals.lookup (ofString "qhat") = s0.locals.lookup (ofString "qhat") := by
                                  simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                                  intro h; cases h
                                exact (hq'.symm.trans hq).symm ▸ rfl
                              rw [hs_q] at hrank
                              have hq_pos : 0 < q.toNat := by
                                by_cases hq0 : q = 0
                                · subst hq0
                                  cases hvsec : s1.locals.lookup (ofString "vsec") with
                                  | none => simp [hq, hvsec] at hc2'
                                  | some vv =>
                                    cases vv with
                                    | rStruct _ => simp [hq, hvsec, valueIsWord] at hc2'
                                    | nStruct _ _ => simp [hq, hvsec, valueIsWord] at hc2'
                                    | val wv =>
                                      cases wv with
                                      | word vsec =>
                                        have hq0' : (0 : BitVec 64) = 0#64 := rfl
                                        rw [hq0'] at hq
                                        simp [hq, hvsec, hrhat, hujn2,
                                          panOpHOL, wordOpHOL, wordOp, wordShiftHOL, valueIsWord, valueWord,
                                          Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def] at hc2'
                                        exact absurd hc2'.symm hnz2
                                · exact Nat.pos_of_ne_zero (fun h => hq0 (BitVec.eq_of_toNat_eq h))
                              have hasgn_q : evaluateHOLFiniteState s1
                                  (.assign .local (ofString "qhat") (.op .sub [.var .local (ofString "qhat"), .const 1])) =
                                  (none, setVarHOLFinite (ofString "qhat") (.val (.word (q - 1))) s1) := by
                                simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hq,
                                  wordOpHOL, wordOp, valueIsWord, valueWord, lookupKvarHOLExact,
                                  isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
                              rw [evaluateHOLFiniteState_seq_line780, hasgn_q]
                              dsimp only
                              let s2 := setVarHOLFinite (ofString "qhat") (.val (.word (q - 1))) s1
                              rw [evaluateHOLFiniteState_seq_line780]
                              cases hr2 : evaluateHOLFiniteState s2
                                (.assign .local (ofString "rhat") (.op .add [.var .local (ofString "rhat"), .var .local (ofString "vtop")])) with
                              | mk res2 s3 =>
                                cases res2 with
                                | some _ =>
                                  dsimp only
                                  have hs2_eq : s3 = s2 := by
                                    simp [evaluateHOLFiniteState_assign] at hr2
                                    split at hr2 <;> try simp at hr2
                                    · exact hr2.2.symm
                                    · split at hr2 <;> simp at hr2; exact hr2.2.symm
                                  subst hs2_eq
                                  unfold divmnuAgainRank
                                  have : s2.locals.lookup (ofString "again") = some (.val (.word 0)) := by
                                    simp [s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                                    intro h; cases h
                                  rw [this]; dsimp only; rw [if_neg (by decide)]; trivial
                                | none =>
                                  dsimp only
                                  have hs3_again : s3.locals.lookup (ofString "again") = some (.val (.word 0)) := by
                                    have hfr := evaluate_avoidsLocal_flowing (ofString "again")
                                      (.assign .local (ofString "rhat") (.op .add [.var .local (ofString "rhat"), .var .local (ofString "vtop")]))
                                      (by decide) s2 (by rw [hr2]; exact Or.inl rfl)
                                    rw [hr2] at hfr; dsimp only at hfr
                                    rw [hfr]
                                    simp [s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                                    intro h; cases h
                                  have hs3_qhat : s3.locals.lookup (ofString "qhat") = some (.val (.word (q - 1))) := by
                                    have hfr := evaluate_avoidsLocal_flowing (ofString "qhat")
                                      (.assign .local (ofString "rhat") (.op .add [.var .local (ofString "rhat"), .var .local (ofString "vtop")]))
                                      (by decide) s2 (by rw [hr2]; exact Or.inl rfl)
                                    rw [hr2] at hfr; dsimp only at hfr
                                    rw [hfr]
                                    simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                                  have hasgn_a1 : evaluateHOLFiniteState s3 (.assign .local (ofString "again") (.const 1)) =
                                      (none, setVarHOLFinite (ofString "again") (.val (.word 1)) s3) := by
                                    simp [evaluateHOLFiniteState_assign, evalHOLExact, hs3_again, lookupKvarHOLExact,
                                      isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
                                  rw [hasgn_a1]
                                  dsimp only
                                  unfold divmnuAgainRank
                                  have hs4_again : (setVarHOLFinite (ofString "again") (.val (.word 1)) s3).locals.lookup (ofString "again") =
                                      some (.val (.word 1)) := by
                                    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                                  have hs4_qhat : (setVarHOLFinite (ofString "again") (.val (.word 1)) s3).locals.lookup (ofString "qhat") =
                                      some (.val (.word (q - 1))) := by
                                    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_qhat]
                                    intro h; cases h
                                  rw [hs4_again]; dsimp only; rw [if_pos rfl, hs4_qhat]; dsimp only
                                  have h1le : (1 : BitVec 64) ≤ q := by
                                    rw [BitVec.le_def]; change 1 ≤ q.toNat; omega
                                  have hsub : (q - 1).toNat = q.toNat - 1 := by
                                    rw [BitVec.toNat_sub_of_le h1le]; rfl
                                  omega
        · exact hs1_again0
    · exact hs1_again0
  have hout := rankedWhile_run (.cmp .equal (.var .local (ofString "again")) (.const 1))
    divmnuAgainBody 0 divmnuAgainRank False hexit hstep (2 ^ 64) state code hrank0
    (by simp; exact budget)
  simp only [Nat.zero_add, Nat.mul_one] at hout
  exact ⟨hout.1, hout.2.1, hout.2.2.1⟩

def divmnuClockBound : Nat :=
  (2 ^ 64 - 1) * 34 + (2 ^ 64 - 1) * (4 * 2 ^ 64 + 34) + 5 * (2 ^ 64 - 1) + 2

theorem funBounded_divmnu : FunBounded (ofString "divmnu") divmnuClockBound := by
  refine funBounded_of_guestAst 67 (by rw [guestAst_len]; decide) Guest.Software.guestFn_divmnu divmnuClockBound rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_divmnu,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply ProgBounded.weaken
  · apply ProgBounded.dec
    apply ProgBounded.dec
    apply ProgBounded.seq
    · apply ProgBounded.iteMax
      · apply ProgBounded.dec
        apply ProgBounded.dec
        apply ProgBounded.seq
        · apply ProgBounded.straight; decide
        · apply ProgBounded.seq
          · apply progBounded_downLowerDecrFirst
            · apply ProgBounded.decCall funBounded_div64by32
              apply ProgBounded.straight; decide
            · decide
            · decide
          · apply ProgBounded.straight; decide
      · apply ProgBounded.straight; decide
    · apply ProgBounded.dec
      apply ProgBounded.dec
      apply ProgBounded.decCall funBounded_nlz32
      apply ProgBounded.seq
      · apply ProgBounded.straight; decide
      · apply ProgBounded.seq
        · apply progBounded_downLowerDecBody
          apply DecBody.seq
          · apply ProgBounded.straight; decide
          · decide
          · decide
          · exact DecBody.decr
        · apply ProgBounded.seq
          · apply ProgBounded.straight; decide
          · apply ProgBounded.seq
            · apply ProgBounded.straight; decide
            · apply ProgBounded.seq
              · apply ProgBounded.straight; decide
              · apply ProgBounded.seq
                · apply progBounded_downLowerDecBody
                  apply DecBody.seq
                  · apply ProgBounded.straight; decide
                  · decide
                  · decide
                  · exact DecBody.decr
                · apply ProgBounded.seq
                  · apply ProgBounded.straight; decide
                  · apply ProgBounded.dec
                    apply ProgBounded.dec
                    apply ProgBounded.seq
                    · apply ProgBounded.straight; decide
                    · apply ProgBounded.seq
                      · apply progBounded_downLowerDecrFirst
                        · apply ProgBounded.dec
                          apply ProgBounded.dec
                          apply ProgBounded.dec
                          apply ProgBounded.dec
                          apply ProgBounded.dec
                          apply ProgBounded.seq
                          · apply ProgBounded.iteMax
                            · apply ProgBounded.straight; decide
                            · apply ProgBounded.decCall funBounded_div64by32
                              apply ProgBounded.straight; decide
                          · apply ProgBounded.dec
                            apply ProgBounded.seq
                            · exact progBounded_divmnu_again
                            · apply ProgBounded.dec
                              apply ProgBounded.seq
                              · apply ProgBounded.straight; decide
                              · apply ProgBounded.seq
                                · apply progBounded_upLowerAny (cost := 0)
                                  · refine CountedBody.dec _ _ _ (by decide) ?_
                                    refine CountedBody.dec _ _ _ (by decide) ?_
                                    refine countedBody_seq_straight _ (by decide) (by decide) (by decide) ?_
                                    refine countedBody_seq_straight _ (by decide) (by decide) (by decide) ?_
                                    exact CountedBody.incr
                                  · decide
                                · apply ProgBounded.dec
                                  apply ProgBounded.iteMax
                                  · apply ProgBounded.seq
                                    · apply ProgBounded.straight; decide
                                    · apply ProgBounded.seq
                                      · apply ProgBounded.straight; decide
                                      · apply ProgBounded.seq
                                        · apply ProgBounded.straight; decide
                                        · apply ProgBounded.seq
                                          · apply progBounded_upLowerAny (cost := 0)
                                            · refine CountedBody.dec _ _ _ (by decide) ?_
                                              refine countedBody_seq_straight _ (by decide) (by decide) (by decide) ?_
                                              refine countedBody_seq_straight _ (by decide) (by decide) (by decide) ?_
                                              exact CountedBody.incr
                                            · decide
                                          · apply ProgBounded.straight; decide
                                  · apply ProgBounded.straight; decide
                        · decide
                        · decide
                      · apply ProgBounded.seq
                        · apply ProgBounded.straight; decide
                        · apply ProgBounded.seq
                          · apply progBounded_upLowerAny (cost := 0)
                            · refine countedBody_seq_straight _ (by decide) (by decide) (by decide) ?_
                              exact CountedBody.incr
                            · decide
                          · apply ProgBounded.seq
                            · apply ProgBounded.straight; decide
                            · apply ProgBounded.seq
                              · apply progBounded_upLowerAny (cost := 0)
                                · refine countedBody_seq_straight _ (by decide) (by decide) (by decide) ?_
                                  exact CountedBody.incr
                                · decide
                              · apply ProgBounded.straight; decide
  · unfold divmnuClockBound; omega

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
  refine ProgBounded.weaken ?_ (show 1 + (0 + (64 * (0 + 1) + 0)) ≤ 65 by decide)
  apply ProgBounded.seq
  · exact ProgBounded.iteMax _ (ProgBounded.call funBounded_trap_with none _) (ProgBounded.straight _ (by decide))
  · apply ProgBounded.seq
    · exact ProgBounded.iteMax _ (ProgBounded.straight _ (by decide)) (ProgBounded.straight _ (by decide))
    · apply ProgBounded.dec
      apply ProgBounded.dec
      exact ProgBounded.countedDownDecFirst (ofString "i") .less (Or.inl rfl) 64 (fun _ => by decide)
        (ProgBounded.seq (ProgBounded.straight _ (by decide))
          (ProgBounded.ite _ (ProgBounded.straight _ (by decide)) (ProgBounded.straight _ (by decide))))
        (by decide) (by decide) (ProgBounded.straight _ (by decide))

private theorem wordShiftHOL_lsl_one_64 : wordShiftHOL Shift.lsl (1#64) 64 = none := by
  simp [wordShiftHOL]

theorem funBounded_ceil_log2 : FunBounded (ofString "ceil_log2") 64 := by
  refine funBounded_of_guestAst 36 (by rw [guestAst_len]; decide) Guest.Software.guestFn_ceil_log2 64 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_ceil_log2,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, List.map, Option.map]
  intro F state hcode hbudget
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · exact ⟨Nat.le_add_right _ _, le_refl _, by simp⟩
  · rename_i val hval
    split
    · have hval0 : val = .val (.word (0#64)) := by
        symm
        simpa [evalHOLFinite_eq_toExact, evalHOLExact] using hval
      subst hval0
      set inner := setVarHOLFinite (ofString "d") (.val (.word (0#64))) state with hinner
      have hclk : inner.clock = state.clock := rfl
      have hat : inner.locals.lookup (ofString "d") = some (.val (.word (0#64))) := by
        simp [hinner, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hstop : ∀ {G : Type} (s : PanSemStateFiniteExact 64 G),
          s.locals.lookup (ofString "d") = some (.val (.word (64#64))) →
          evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
            (.cmp .lower (.shift .lsl (.const 1) (.var .local (ofString "d")))
              (.var .local (ofString "n"))) = none ∨
          evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
            (.cmp .lower (.shift .lsl (.const 1) (.var .local (ofString "d")))
              (.var .local (ofString "n"))) = some (.val (.word (0#64))) := by
        intro G s hd
        rw [evalHOLFinite_eq_toExact]
        simp [evalHOLExact, hd, wordShiftHOL_lsl_one_64]
      have hwhile := cappedCountedWhile_run (ofString "d")
        (.cmp .lower (.shift .lsl (.const 1) (.var .local (ofString "d")))
          (.var .local (ofString "n")))
        64 hstop CountedBody.incr 64 inner hcode 0 hat (by decide) (by decide) hbudget
      rw [evaluateHOLFiniteState_seq_line780]
      rcases hr : evaluateHOLFiniteState inner
        (.while (.cmp .lower (.shift .lsl (.const 1) (.var .local (ofString "d")))
          (.var .local (ofString "n")))
          (.assign .local (ofString "d") (.op .add [.var .local (ofString "d"), .const 1]))) with ⟨res, post⟩
      rw [hr] at hwhile
      dsimp only at hwhile
      obtain ⟨hw1, hw2, hw3⟩ := hwhile
      cases res with
      | none =>
        dsimp only
        have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata inner
          (.while (.cmp .lower (.shift .lsl (.const 1) (.var .local (ofString "d")))
            (.var .local (ofString "n")))
            (.assign .local (ofString "d") (.op .add [.var .local (ofString "d"), .const 1])))
        rw [hr] at hmeta
        have htb : ProgBounded (.return (.var .local (ofString "d"))) 0 := ProgBounded.straight _ rfl
        have ht := htb post (hmeta.1.trans hcode) (Nat.zero_le _)
        rcases hrr : evaluateHOLFiniteState post (.return (.var .local (ofString "d"))) with ⟨res2, post2⟩
        rw [hrr] at ht
        have hc : (res2, post2).2.clock = post2.clock := rfl
        exact ⟨by omega, by omega, ht.2.2⟩
      | some r =>
        dsimp only
        exact ⟨by omega, by omega, hw3⟩
    · exact ⟨Nat.le_add_right _ _, le_refl _, by simp⟩

theorem funBounded_sha256_pair : FunBounded (ofString "sha256_pair") 0 :=
  funBounded_of_guestAst 96 (by rw [guestAst_len]; decide) Guest.Software.guestFn_sha256_pair 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_mix_in_length : FunBounded (ofString "mix_in_length") 16 := by
  refine funBounded_of_guestAst 187 (by rw [guestAst_len]; decide) Guest.Software.guestFn_mix_in_length 16 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_mix_in_length,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.seq (progBounded_memzero_const none _ 32 (by decide))
      (ProgBounded.seq (ProgBounded.call funBounded_st_le64 none _)
        (ProgBounded.seq (ProgBounded.call funBounded_sha256_pair none _)
          (ProgBounded.straight _ rfl))))
    (by decide)

theorem funBounded_u256_from_word : FunBounded (ofString "u256_from_word") 0 :=
  funBounded_of_guestAst 39 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_from_word 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_u256_is_zero : FunBounded (ofString "u256_is_zero") 0 :=
  funBounded_of_guestAst 42 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_is_zero 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_u256_lt : FunBounded (ofString "u256_lt") 0 :=
  funBounded_of_guestAst 46 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_lt 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_u256_add : FunBounded (ofString "u256_add") 0 :=
  funBounded_of_guestAst 56 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_add 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_mul64x64 : FunBounded (ofString "mul64x64") 0 :=
  funBounded_of_guestAst 59 (by rw [guestAst_len]; decide) Guest.Software.guestFn_mul64x64 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_u256_mul : FunBounded (ofString "u256_mul") 7 := by
  refine funBounded_of_guestAst 60 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_mul 7 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_u256_mul,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine ProgBounded.weaken ?_ (show max (0 + 1 + 0) 0 + (0 + 1 + (0 + 1 + (0 + 1 + (0 + 1 + (0 + 1 + (0 + 1 + 0)))))) ≤ 7 by decide)
  apply ProgBounded.seq
  · exact ProgBounded.iteMax _
      (ProgBounded.decCall funBounded_mul64x64 _ _ _ (ProgBounded.straight _ rfl))
      (ProgBounded.straight _ rfl)
  · iterate 6 (apply ProgBounded.decCall funBounded_mul64x64)
    exact ProgBounded.straight _ rfl

theorem funBounded_u256_mul_full : FunBounded (ofString "u256_mul_full") 16 := by
  refine funBounded_of_guestAst 61 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_mul_full 16 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_u256_mul_full,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply ProgBounded.weaken
  · iterate 16 (apply ProgBounded.decCall funBounded_mul64x64)
    exact ProgBounded.straight _ rfl
  · decide

theorem funBounded_u256_to_digits : FunBounded (ofString "u256_to_digits") 0 :=
  funBounded_of_guestAst 64 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_to_digits 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_digits_to_u256 : FunBounded (ofString "digits_to_u256") 0 :=
  funBounded_of_guestAst 65 (by rw [guestAst_len]; decide) Guest.Software.guestFn_digits_to_u256 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_digits_len : FunBounded (ofString "digits_len") (2 ^ 64 - 1) := by
  refine funBounded_of_guestAst 66 (by rw [guestAst_len]; decide) Guest.Software.guestFn_digits_len (2 ^ 64 - 1) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_digits_len,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine ProgBounded.weaken ?_ (show (2 ^ 64 - 1) * (0 + 1) + 0 ≤ 2 ^ 64 - 1 by omega)
  apply ProgBounded.seq
  · exact progBounded_downLowerDecBody (ofString "n") (cost := 0)
      (DecBody.seq _ (ProgBounded.straight _ (by decide)) (by decide) (by decide) DecBody.decr)
  · exact ProgBounded.straight _ (by decide)

def digitsDivmodClockBound : Nat :=
  1 + (2 ^ 64) + (2 ^ 64) + 16 + 1 + 8 + (divmnuClockBound + 1) + 1

theorem funBounded_digits_divmod : FunBounded (ofString "digits_divmod") digitsDivmodClockBound := by
  refine funBounded_of_guestAst 68 (by rw [guestAst_len]; decide) Guest.Software.guestFn_digits_divmod digitsDivmodClockBound rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_digits_divmod,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply ProgBounded.weaken
  · iterate 3 apply ProgBounded.dec
    apply ProgBounded.seq
    · exact ProgBounded.call funBounded_u256_to_digits none _
    · apply ProgBounded.decCall funBounded_digits_len
      apply ProgBounded.decCall funBounded_digits_len
      exact ProgBounded.countedDec (ofString "i") .lower (Or.inr rfl) (16#64) (1#64) (0#64)
        (by decide) (by decide) (by decide) (cost := 0)
        (countedBody_seq_straight _ rfl rfl rfl CountedBody.incr)
        (ProgBounded.seq
          (ProgBounded.iteMax _
            (ProgBounded.tail funBounded_digits_to_u256 _)
            (ProgBounded.straight _ rfl))
          (ProgBounded.countedAssign (ofString "i") .lower (Or.inr rfl) (8#64) (1#64) (0#64)
            (by decide) (by decide) (by decide) (cost := 0)
            (countedBody_seq_straight _ rfl rfl rfl CountedBody.incr)
            (ProgBounded.seq
              (ProgBounded.call funBounded_divmnu none _)
              (ProgBounded.tail funBounded_digits_to_u256 _))))
  · change _ ≤ digitsDivmodClockBound
    have h16 : (16#64).toNat = 16 := rfl
    have h8 : (8#64).toNat = 8 := rfl
    rw [h16, h8]
    unfold digitsDivmodClockBound
    omega

def u256DivmodClockBound : Nat :=
  1 + 66 + 1 + (digitsDivmodClockBound + 1) + 1

theorem funBounded_u256_divmod : FunBounded (ofString "u256_divmod") u256DivmodClockBound := by
  refine funBounded_of_guestAst 69 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_divmod u256DivmodClockBound rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_u256_divmod,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply ProgBounded.weaken
  · apply ProgBounded.seq
    · exact ProgBounded.iteMax _ (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl)
    · apply ProgBounded.decCall funBounded_u256_lt
      apply ProgBounded.seq
      · exact ProgBounded.iteMax _ (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl)
      · apply ProgBounded.seq
        · exact ProgBounded.iteMax _
            (ProgBounded.decCall funBounded_udivmod _ _ _ (ProgBounded.straight _ rfl))
            (ProgBounded.straight _ rfl)
        · apply ProgBounded.dec
          apply ProgBounded.seq
          · exact ProgBounded.call funBounded_u256_to_digits none _
          · apply ProgBounded.decCall funBounded_digits_divmod
            apply ProgBounded.decCall funBounded_digits_to_u256
            exact ProgBounded.straight _ rfl
  · unfold u256DivmodClockBound; omega

def u256DivClockBound : Nat := u256DivmodClockBound + 1

theorem funBounded_u256_div : FunBounded (ofString "u256_div") u256DivClockBound := by
  refine funBounded_of_guestAst 70 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_div u256DivClockBound rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_u256_div,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_u256_divmod _ _ _ (ProgBounded.straight _ rfl))
    (by unfold u256DivClockBound; omega)

theorem funBounded_u256_mod : FunBounded (ofString "u256_mod") u256DivClockBound := by
  refine funBounded_of_guestAst 71 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_mod u256DivClockBound rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_u256_mod,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_u256_divmod _ _ _ (ProgBounded.straight _ rfl))
    (by unfold u256DivClockBound; omega)

theorem lookup_keccak256 :
    originalRuntimeCode.lookup (ofString "keccak256") =
      some ([(ofString "p", .one), (ofString "n", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_keccak256, .one) :=
  lookup_of_guestAst_getElem 103 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_keccak256) rfl

private theorem evalListHOLFinite_three_word2 {F : Type}
    (state : PanSemStateFiniteExact 64 F) (e1 e2 e3 : ExpHOL 64) (K : BitVec 64) {vs : List (ValueHOL 64)}
    (hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [e1, e2, e3] = some vs)
    (hk : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) e2 = some (.val (.word K))) :
    ∃ v1 v3, vs = [v1, .val (.word K), v3] := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  rw [evalHOLFinite_eq_toExact] at hk
  simp only [evalListHOLExact] at hargs
  rw [hk] at hargs
  rcases h1 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) e1 with _ | v1
  · rw [h1] at hargs; cases hargs
  · rw [h1] at hargs
    rcases h3 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) e3 with _ | v3
    · rw [h3] at hargs; cases hargs
    · rw [h3] at hargs
      cases hargs
      exact ⟨v1, v3, rfl⟩

private theorem three_arg_lookup_mid_n (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (fn p1 p3 : MlS) (body : ProgHOL 64)
    (hp1n : p1 ≠ ofString "n") (hp13 : p1 ≠ p3) (hnp3 : ofString "n" ≠ p3)
    (hlookup_fn : code fn = some ([(p1, .one), (ofString "n", .one), (p3, .one)], body, .one))
    {v1 v3 : ValueHOL 64} {K : BitVec 64}
    {foundBody : ProgHOL 64} {locals : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hfound : PanSemStateFiniteExact.lookupCodeHOLFinite code fn [v1, .val (.word K), v3] =
      some (foundBody, locals, rs)) :
    foundBody = body ∧ locals.lookup (ofString "n") = some (.val (.word K)) := by
  have hbody := lookupCodeHOLFinite_installed_body code fn _ body foundBody .one rs
    [v1, .val (.word K), v3] locals hlookup_fn hfound
  refine ⟨hbody, ?_⟩
  cases v1 with
  | rStruct _ =>
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
    split at hfound
    · cases hfound
    · rename_i _ _ _ raw
      simp [lookupCodeHOLExact, hlookup_fn, shapeOfHOLExact, shapeEqHOL] at raw
  | nStruct _ _ =>
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
    split at hfound
    · cases hfound
    · rename_i _ _ _ raw
      simp [lookupCodeHOLExact, hlookup_fn, shapeOfHOLExact, shapeEqHOL] at raw
  | val wl1 =>
    cases wl1 with
    | word w1 =>
      cases v3 with
      | rStruct _ =>
        unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
        split at hfound
        · cases hfound
        · rename_i _ _ _ raw
          simp [lookupCodeHOLExact, hlookup_fn, shapeOfHOLExact, shapeEqHOL] at raw
      | nStruct _ _ =>
        unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
        split at hfound
        · cases hfound
        · rename_i _ _ _ raw
          simp [lookupCodeHOLExact, hlookup_fn, shapeOfHOLExact, shapeEqHOL] at raw
      | val wl3 =>
        cases wl3 with
        | word w3 =>
          rw [pan_three_word_lookup code fn p1 (ofString "n") p3 body w1 K w3 hp1n hp13 hnp3 hlookup_fn] at hfound
          cases hfound
          have hp3n : p3 ≠ ofString "n" := Ne.symm hnp3
          simp [HolFiniteMapExact.lookup_update, FUPDATE, hp3n, hnp3]

private theorem runBounded_memcpy_call {F : Type}
    (state : PanSemStateFiniteExact 64 F) (destination : Option (VarKind × MlS))
    (dst src sizeExp : ExpHOL 64) (K : BitVec 64)
    (hsmall : K.toNat + 32 < 2 ^ 64)
    (hcode : state.code = originalRuntimeCode)
    (heval : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) sizeExp =
      some (.val (.word K)))
    (hbudget : K.toNat / 8 + 8 ≤ state.clock) :
    RunBounded state (.call (some (destination, none)) (ofString "memcpy") [dst, src, sizeExp])
      (K.toNat / 8 + 8) := by
  cases hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [dst, src, sizeExp] with
  | none =>
    unfold RunBounded
    rw [evaluateHOLFiniteState_call, hargs]
    simp
  | some vs =>
    have hvs : ∃ w1 w2 : BitVec 64,
        (evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
          [.const w1, .const w2, .const K] = some vs) ∨
        lookupCodeHOLFinite state.code.lookup (ofString "memcpy") vs = none := by
      rw [evalListHOLFinite_eq_toExact] at hargs
      rw [evalHOLFinite_eq_toExact] at heval
      simp only [evalListHOLExact] at hargs
      rw [heval] at hargs
      rcases h1 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) dst with _ | v1
      · rw [h1] at hargs; cases hargs
      · rw [h1] at hargs
        rcases h2 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) src with _ | v2
        · rw [h2] at hargs; cases hargs
        · rw [h2] at hargs
          cases hargs
          cases v1 with
          | rStruct _ =>
            refine ⟨0, 0, Or.inr ?_⟩
            rw [hcode]
            unfold PanSemStateFiniteExact.lookupCodeHOLFinite
            split
            · rfl
            · rename_i _ _ _ raw
              simp [lookupCodeHOLExact, lookup_memcpy, shapeOfHOLExact, shapeEqHOL] at raw
          | nStruct _ _ =>
            refine ⟨0, 0, Or.inr ?_⟩
            rw [hcode]
            unfold PanSemStateFiniteExact.lookupCodeHOLFinite
            split
            · rfl
            · rename_i _ _ _ raw
              simp [lookupCodeHOLExact, lookup_memcpy, shapeOfHOLExact, shapeEqHOL] at raw
          | val wl1 =>
            cases wl1 with
            | word w1 =>
              cases v2 with
              | rStruct _ =>
                refine ⟨0, 0, Or.inr ?_⟩
                rw [hcode]
                unfold PanSemStateFiniteExact.lookupCodeHOLFinite
                split
                · rfl
                · rename_i _ _ _ raw
                  simp [lookupCodeHOLExact, lookup_memcpy, shapeOfHOLExact, shapeEqHOL] at raw
              | nStruct _ _ =>
                refine ⟨0, 0, Or.inr ?_⟩
                rw [hcode]
                unfold PanSemStateFiniteExact.lookupCodeHOLFinite
                split
                · rfl
                · rename_i _ _ _ raw
                  simp [lookupCodeHOLExact, lookup_memcpy, shapeOfHOLExact, shapeEqHOL] at raw
              | val wl2 =>
                cases wl2 with
                | word w2 =>
                  refine ⟨w1, w2, Or.inl ?_⟩
                  rw [evalListHOLFinite_eq_toExact]
                  rfl
    obtain ⟨w1, w2, hcargs | hnone⟩ := hvs
    · have hconst := progBounded_memcpy_const destination (.const w1) (.const w2) K hsmall state hcode hbudget
      unfold RunBounded at hconst ⊢
      rw [evaluateHOLFiniteState_call, hargs]
      rw [evaluateHOLFiniteState_call, hcargs] at hconst
      exact hconst
    · unfold RunBounded
      rw [evaluateHOLFiniteState_call, hargs]
      dsimp only
      rw [hnone]
      simp

private theorem runBounded_memzero_call {F : Type}
    (state : PanSemStateFiniteExact 64 F) (destination : Option (VarKind × MlS))
    (dst sizeExp : ExpHOL 64) (K : BitVec 64)
    (hsmall : K.toNat + 32 < 2 ^ 64)
    (hcode : state.code = originalRuntimeCode)
    (heval : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) sizeExp =
      some (.val (.word K)))
    (hbudget : K.toNat / 8 + 8 ≤ state.clock) :
    RunBounded state (.call (some (destination, none)) (ofString "memzero") [dst, sizeExp])
      (K.toNat / 8 + 8) := by
  cases hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [dst, sizeExp] with
  | none =>
    unfold RunBounded
    rw [evaluateHOLFiniteState_call, hargs]
    simp
  | some vs =>
    have hvs : ∃ w1 : BitVec 64,
        (evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
          [.const w1, .const K] = some vs) ∨
        lookupCodeHOLFinite state.code.lookup (ofString "memzero") vs = none := by
      rw [evalListHOLFinite_eq_toExact] at hargs
      rw [evalHOLFinite_eq_toExact] at heval
      simp only [evalListHOLExact] at hargs
      rw [heval] at hargs
      rcases h1 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) dst with _ | v1
      · rw [h1] at hargs; cases hargs
      · rw [h1] at hargs
        cases hargs
        cases v1 with
        | rStruct _ =>
          refine ⟨0, Or.inr ?_⟩
          rw [hcode]
          unfold PanSemStateFiniteExact.lookupCodeHOLFinite
          split
          · rfl
          · rename_i _ _ _ raw
            simp [lookupCodeHOLExact, lookup_memzero, shapeOfHOLExact, shapeEqHOL] at raw
        | nStruct _ _ =>
          refine ⟨0, Or.inr ?_⟩
          rw [hcode]
          unfold PanSemStateFiniteExact.lookupCodeHOLFinite
          split
          · rfl
          · rename_i _ _ _ raw
            simp [lookupCodeHOLExact, lookup_memzero, shapeOfHOLExact, shapeEqHOL] at raw
        | val wl1 =>
          cases wl1 with
          | word w1 =>
            refine ⟨w1, Or.inl ?_⟩
            rw [evalListHOLFinite_eq_toExact]
            rfl
    obtain ⟨w1, hcargs | hnone⟩ := hvs
    · have hconst := progBounded_memzero_const destination (.const w1) K hsmall state hcode hbudget
      unfold RunBounded at hconst ⊢
      rw [evaluateHOLFiniteState_call, hargs]
      rw [evaluateHOLFiniteState_call, hcargs] at hconst
      exact hconst
    · unfold RunBounded
      rw [evaluateHOLFiniteState_call, hargs]
      dsimp only
      rw [hnone]
      simp

private theorem runBounded_transfer_outer {F : Type}
    {s_outer s : PanSemStateFiniteExact 64 F} {prog : ProgHOL 64} {c_pre c_rem : Nat}
    (hpre_spent : s_outer.clock ≤ s.clock + c_pre)
    (hpre_kept : s.clock ≤ s_outer.clock)
    (hrun : RunBounded s prog c_rem) :
    s_outer.clock ≤ (evaluateHOLFiniteState s prog).2.clock + (c_pre + c_rem) ∧
      (evaluateHOLFiniteState s prog).2.clock ≤ s_outer.clock ∧
      (evaluateHOLFiniteState s prog).1 ≠ some .timeOut := by
  obtain ⟨r1, r2, r3⟩ := hrun
  exact ⟨by omega, by omega, r3⟩

abbrev keccak256BodyClockBound (n : Nat) : Nat :=
  (n / 136) * 163 + 256

theorem runBounded_keccak256_body {F : Type}
    (state : PanSemStateFiniteExact 64 F) (K : BitVec 64)
    (hsmall : K.toNat + 136 < 2 ^ 64)
    (hcode : state.code = originalRuntimeCode)
    (atN : state.locals.lookup (ofString "n") = some (.val (.word K)))
    (hbudget : keccak256BodyClockBound K.toNat ≤ state.clock) :
    RunBounded state (sourceFnBody Guest.Software.guestFn_keccak256) (keccak256BodyClockBound K.toNat) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_keccak256,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply RunBounded.dec
  intro vstp _
  let s1 := setVarHOLFinite (ofString "stp") vstp state
  have hs1_code : s1.code = originalRuntimeCode := hcode
  have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word K)) := by
    have hne : ofString "stp" ≠ ofString "n" := by decide
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, atN]
  have hmz200 : ProgBounded
      (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "stp"), .const (200#64)]) 33 :=
    ProgBounded.weaken (progBounded_memzero_const none (.var .local (ofString "stp")) (200#64) (by decide)) (by decide)
  refine (RunBounded.seq (hmz200 s1 hs1_code (by
      change 33 ≤ state.clock
      unfold keccak256BodyClockBound at hbudget; omega))
    (a := 33) (b := (K.toNat / 136) * 163 + 223)
    (by
      change 33 + ((K.toNat / 136) * 163 + 223) ≤ state.clock
      unfold keccak256BodyClockBound at hbudget; omega)
    (fun s2 hs1_run hs2_code hs2_budget => ?_)).weaken
    (by unfold keccak256BodyClockBound; omega)
  have hs2_n : s2.locals.lookup (ofString "n") = some (.val (.word K)) := by
    have hav := evaluate_avoidsLocal_flowing (ofString "n")
      (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "stp"), .const (200#64)])
      rfl s1
    rw [hs1_run] at hav
    exact (hav (Or.inl rfl)).trans hs1_n
  apply RunBounded.decConst
  let s3 := setVarHOLFinite (ofString "i") (.val (.word (0#64))) s2
  have hs3_code : s3.code = originalRuntimeCode := hs2_code.trans hs1_code
  have hs3_i : s3.locals.lookup (ofString "i") = some (.val (.word (0#64))) := by
    simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs3_n : s3.locals.lookup (ofString "n") = some (.val (.word K)) := by
    have hne : ofString "i" ≠ ofString "n" := by decide
    simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hs2_n]
  have habsorb_body : CountedBody (ofString "i") (136#64)
      (.seq
        (.call (some (none, none)) (ofString "keccak_absorb_block")
          [.var .local (ofString "stp"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")]])
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (136#64)]))) 162 := by
    simpa using CountedBody.seq _
      (ProgBounded.call funBounded_keccak_absorb_block none
        [.var .local (ofString "stp"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")]])
      rfl rfl CountedBody.incr
  have h136_nat : (136#64).toNat = 136 := rfl
  have h0_nat : (0#64).toNat = 0 := rfl
  have hloop := notLowerStrideWhile_run (ofString "i") (ofString "n") K (136#64)
    (by rw [h136_nat]; exact hsmall) (by decide) habsorb_body rfl rfl
    (K.toNat / 136) s3 hs3_code (0#64) hs3_i hs3_n (by rw [h0_nat]; omega)
    (by rw [h0_nat, h136_nat]; simp)
    (by change (K.toNat / 136) * (162 + 1) ≤ s2.clock; omega)
  unfold RunBounded
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hlr : evaluateHOLFiniteState s3
      (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const (136#64)]))
        (.seq
          (.call (some (none, none)) (ofString "keccak_absorb_block")
            [.var .local (ofString "stp"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")]])
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (136#64)])))) with ⟨lres, s4⟩
  rw [hlr] at hloop
  dsimp only at hloop ⊢
  cases lres with
  | some r =>
    dsimp only
    exact ⟨by change s2.clock ≤ s4.clock + _; have := hloop.1; change s2.clock ≤ s4.clock + _ at this; omega,
      hloop.2.1, hloop.2.2.1⟩
  | none =>
    dsimp only
    obtain ⟨wi, hs4_i, hs4_n, _, hwi_le, hwi_rem, hs4_code⟩ := hloop.2.2.2 rfl
    rw [h136_nat] at hwi_rem
    have hsub_eval : @evalHOLExact 64 F _ s4.toExact (fun a => Classical.propDecidable (s4.memaddrs a))
        (.op .sub [.var .local (ofString "n"), .var .local (ofString "i")]) = some (.val (.word (K - wi))) := by
      simp [evalHOLExact, evalListHOLExact, hs4_n, hs4_i, valueIsWord, valueWord, wordOpHOL, wordOp]
    have hrem_nat : (K - wi).toNat = K.toNat - wi.toNat := BitVec.toNat_sub_of_le hwi_le
    have hrem_lt : (K - wi).toNat < 136 := by omega
    have hrem_small : (K - wi).toNat + 32 < 2 ^ 64 := by omega
    have hrem_div : (K - wi).toNat / 8 + 8 ≤ 24 := by omega
    have h4_code : s4.code = originalRuntimeCode := hs4_code.trans hs3_code
    have hs4_budget : 223 ≤ s4.clock := by
      have := hloop.1
      change s2.clock ≤ s4.clock + (K.toNat / 136) * 163 at this
      omega
    refine runBounded_transfer_outer (s_outer := s2) (s := s4)
      (c_pre := (K.toNat / 136) * 163) (c_rem := 223)
      (by have := hloop.1; change s2.clock ≤ s4.clock + (K.toNat / 136) * 163 at this; exact this)
      (by have := hloop.2.1; change s4.clock ≤ s2.clock at this; exact this) ?_
    refine RunBounded.decWord s4 (ofString "rem") _ (K - wi) hsub_eval ?_
    let s5 := setVarHOLFinite (ofString "rem") (.val (.word (K - wi))) s4
    have hs5_code : s5.code = originalRuntimeCode := h4_code
    have hs5_rem : s5.locals.lookup (ofString "rem") = some (.val (.word (K - wi))) := by
      simp [s5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hmz136 : ProgBounded
        (.call (some (none, none)) (ofString "memzero") [.var .global (ofString "keccak_pad"), .const (136#64)]) 25 :=
      ProgBounded.weaken (progBounded_memzero_const none (.var .global (ofString "keccak_pad")) (136#64) (by decide)) (by decide)
    refine RunBounded.seq (hmz136 s5 hs5_code (by change 25 ≤ s4.clock; omega))
      (a := 25) (b := 198) (by change 25 + 198 ≤ s4.clock; omega)
      (fun s6 hs5_run hs6_code hs6_budget => ?_)
    have hs6_rem : s6.locals.lookup (ofString "rem") = some (.val (.word (K - wi))) := by
      have hav := evaluate_avoidsLocal_flowing (ofString "rem")
        (.call (some (none, none)) (ofString "memzero") [.var .global (ofString "keccak_pad"), .const (136#64)])
        rfl s5
      rw [hs5_run] at hav
      exact (hav (Or.inl rfl)).trans hs5_rem
    have h6c : s6.code = originalRuntimeCode := hs6_code.trans hs5_code
    have hmc_rem : RunBounded s6
        (.call (some (none, none)) (ofString "memcpy")
          [.var .global (ofString "keccak_pad"),
            .op .add [.var .local (ofString "p"), .var .local (ofString "i")],
            .var .local (ofString "rem")]) 24 :=
      (runBounded_memcpy_call s6 none
        (.var .global (ofString "keccak_pad"))
        (.op .add [.var .local (ofString "p"), .var .local (ofString "i")])
        (.var .local (ofString "rem")) (K - wi) hrem_small h6c
        (by rw [evalHOLFinite_eq_toExact]; simp [evalHOLExact, hs6_rem])
        (by omega)).weaken hrem_div
    refine RunBounded.seq hmc_rem (a := 24) (b := 174) (by omega)
      (fun s7 _ hs7_code hs7_budget => ?_)
    exact (ProgBounded.weaken
      (ProgBounded.seq (ProgBounded.straight _ rfl)
        (ProgBounded.seq (ProgBounded.straight _ rfl)
          (ProgBounded.seq (ProgBounded.call funBounded_keccak_absorb_block none _)
            (ProgBounded.seq
              (ProgBounded.iteMax _
                (ProgBounded.straight _ rfl)
                (progBounded_memcpy_const none _ _ (32#64) (by decide)))
              (ProgBounded.straight _ rfl)))))
      (by decide)) s7 (hs7_code.trans h6c) hs7_budget

theorem progBounded_keccak256_exp (destination : Option (VarKind × MlS))
    (p sizeExp out : ExpHOL 64) (K : BitVec 64) (hsmall : K.toNat + 136 < 2 ^ 64)
    (heval : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) sizeExp = some (.val (.word K))) :
    ProgBounded (.call (some (destination, none)) (ofString "keccak256") [p, sizeExp, out])
      (keccak256BodyClockBound K.toNat + 1) := by
  intro F state hcode hbudget
  cases hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [p, sizeExp, out] with
  | none =>
    rw [evaluateHOLFiniteState_call, hargs]
    simp
  | some vs =>
    obtain ⟨v1, v3, rfl⟩ := evalListHOLFinite_three_word2 state p sizeExp out K hargs (heval state)
    exact RunBounded.call hargs hbudget (fun body locals rs hfound => by
      rw [hcode] at hfound
      obtain ⟨rfl, hn⟩ := three_arg_lookup_mid_n originalRuntimeCode.lookup
        (ofString "keccak256") (ofString "p") (ofString "out")
        (sourceFnBody Guest.Software.guestFn_keccak256)
        (by decide) (by decide) (by decide) lookup_keccak256 hfound
      exact runBounded_keccak256_body (callEntryStateHOLFinite state locals) K hsmall hcode hn
        (by change keccak256BodyClockBound K.toNat ≤ state.clock - 1; omega))

theorem progBounded_keccak256_const (destination : Option (VarKind × MlS))
    (p out : ExpHOL 64) (K : BitVec 64) (hsmall : K.toNat + 136 < 2 ^ 64) :
    ProgBounded (.call (some (destination, none)) (ofString "keccak256") [p, .const K, out])
      (keccak256BodyClockBound K.toNat + 1) :=
  progBounded_keccak256_exp destination p (.const K) out K hsmall
    (fun s => by rw [evalHOLFinite_eq_toExact]; rfl)

theorem funBounded_min : FunBounded (ofString "min") 0 :=
  funBounded_of_guestAst 31 (by rw [guestAst_len]; decide) Guest.Software.guestFn_min 0 rfl
    (ProgBounded.straight _ rfl)

private def u256Val (w0 w1 w2 w3 : BitVec 64) : ValueHOL 64 :=
  .rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]

private abbrev u256ZeroVal : ValueHOL 64 := u256Val 0 0 0 0

private def u256ShapeHOL : ShapeHOL := .comb [.one, .one, .one, .one]

private theorem lookup_u256_from_word :
    originalRuntimeCode.lookup (ofString "u256_from_word") =
      some ([(ofString "w", .one)], sourceFnBody Guest.Software.guestFn_u256_from_word, u256ShapeHOL) :=
  lookup_of_guestAst_getElem 39 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_from_word) rfl

private theorem lookup_u256_is_zero :
    originalRuntimeCode.lookup (ofString "u256_is_zero") =
      some ([(ofString "a", u256ShapeHOL)], sourceFnBody Guest.Software.guestFn_u256_is_zero, .one) :=
  lookup_of_guestAst_getElem 42 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_is_zero) rfl

private theorem lookup_mul64x64 :
    originalRuntimeCode.lookup (ofString "mul64x64") =
      some ([(ofString "a", .one), (ofString "b", .one)],
        sourceFnBody Guest.Software.guestFn_mul64x64, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 59 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_mul64x64) rfl

private theorem lookup_u256_mul :
    originalRuntimeCode.lookup (ofString "u256_mul") =
      some ([(ofString "a", u256ShapeHOL), (ofString "b", u256ShapeHOL)],
        sourceFnBody Guest.Software.guestFn_u256_mul, u256ShapeHOL) :=
  lookup_of_guestAst_getElem 60 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_mul) rfl

private theorem lookup_u256_divmod :
    originalRuntimeCode.lookup (ofString "u256_divmod") =
      some ([(ofString "a", u256ShapeHOL), (ofString "b", u256ShapeHOL)],
        sourceFnBody Guest.Software.guestFn_u256_divmod,
        .comb [.one, .one, .one, .one, .one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 69 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_divmod) rfl

private theorem lookup_u256_div :
    originalRuntimeCode.lookup (ofString "u256_div") =
      some ([(ofString "a", u256ShapeHOL), (ofString "b", u256ShapeHOL)],
        sourceFnBody Guest.Software.guestFn_u256_div, u256ShapeHOL) :=
  lookup_of_guestAst_getElem 70 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_div) rfl

private theorem pan_one_arg_lookup {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name parameter : MlS) (ps rs : ShapeHOL) (body : ProgHOL width) (val : ValueHOL width)
    (hshape : shapeEqHOL ps (shapeOfHOLExact val) = true)
    (lookup : code name = some ([(parameter, ps)], body, rs)) :
    PanSemStateFiniteExact.lookupCodeHOLFinite code name [val] =
      some (body, HolFiniteMapExact.empty.update (parameter, val), rs) := by
  have raw : lookupCodeHOLExact code name [val] =
      some (body, (fun key => if key = parameter then some val else none), rs) := by
    simp [lookupCodeHOLExact, lookup, hshape]
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite
  split
  · rename_i missing
    rw [raw] at missing
    cases missing
  · rename_i foundBody foundLocals foundShape found
    have equal := Option.some.inj (found.symm.trans raw)
    obtain ⟨rfl, rest⟩ := Prod.mk.inj equal
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj rest
    apply congrArg (fun locals => some (foundBody, locals, foundShape))
    apply HolFiniteMapExact.ext
    funext key
    by_cases same : key = parameter
    · subst same
      simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty]
    · have different : parameter ≠ key := Ne.symm same
      simp [same, different, HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY]

private theorem pan_two_arg_lookup {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name first second : MlS) (ps1 ps2 rs : ShapeHOL) (body : ProgHOL width) (v1 v2 : ValueHOL width)
    (different : first ≠ second)
    (hshape1 : shapeEqHOL ps1 (shapeOfHOLExact v1) = true)
    (hshape2 : shapeEqHOL ps2 (shapeOfHOLExact v2) = true)
    (lookup : code name = some ([(first, ps1), (second, ps2)], body, rs)) :
    PanSemStateFiniteExact.lookupCodeHOLFinite code name [v1, v2] =
      some (body, (HolFiniteMapExact.empty.update (first, v1)).update (second, v2), rs) := by
  have raw : lookupCodeHOLExact code name [v1, v2] =
      some (body, (fun key => if key = second then some v2 else if key = first then some v1 else none), rs) := by
    simp [lookupCodeHOLExact, lookup, hshape1, hshape2, different]
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite
  split
  · rename_i missing
    rw [raw] at missing
    cases missing
  · rename_i foundBody foundLocals foundShape found
    have equal := Option.some.inj (found.symm.trans raw)
    obtain ⟨rfl, rest⟩ := Prod.mk.inj equal
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj rest
    apply congrArg (fun locals => some (foundBody, locals, foundShape))
    apply HolFiniteMapExact.ext
    funext key
    by_cases two : key = second
    · subst two
      simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty]
    · have backTwo : second ≠ key := Ne.symm two
      by_cases one : key = first
      · subst one
        simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, different, Ne.symm different]
      · have backOne : first ≠ key := Ne.symm one
        simp [one, two, backOne, backTwo, HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY]

private theorem eval_u256_from_word_body {F : Type}
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hw : s.locals.lookup (ofString "w") = some (.val (.word w))) :
    evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_from_word) =
      (some (.returned (u256Val w 0 0 0)), emptyLocalsHOLFinite s) := by
  have hbody : sourceFnBody Guest.Software.guestFn_u256_from_word =
      .return (.rstruct [.var .local (ofString "w"), .const (0#64), .const (0#64), .const (0#64)]) := rfl
  rw [hbody, evaluateHOLFiniteState_return]
  have hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.rstruct [.var .local (ofString "w"), .const (0#64), .const (0#64), .const (0#64)]) =
      some (u256Val w 0 0 0) := by
    simp [evalHOLExact, evalListHOLExact, hw, u256Val]
  rw [hev]
  dsimp only
  have hsz : Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL s.structs
      (shapeOfHOLExact (u256Val w 0 0 0)) ≤ 32 := by
    simp [u256Val, shapeOfHOLExact, sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL]
  rw [if_pos hsz]

private theorem eval_u256_is_zero_body_zero {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (ha : s.locals.lookup (ofString "a") = some u256ZeroVal) :
    evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_is_zero) =
      (some (.returned (.val (.word 1))), emptyLocalsHOLFinite s) := by
  have hbody : sourceFnBody Guest.Software.guestFn_u256_is_zero =
      .seq (.ite (.cmp .equal (.op .or [.rfield 0 (.var .local (ofString "a")),
          .rfield 1 (.var .local (ofString "a")),
          .rfield 2 (.var .local (ofString "a")),
          .rfield 3 (.var .local (ofString "a"))]) (.const (0#64)))
        (.return (.const (1#64))) .skip)
        (.return (.const (0#64))) := rfl
  rw [hbody, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
  have hor4_0 : wordOpHOL .or [0#64, 0#64, 0#64, 0#64] = some 0#64 := by decide
  have hcmp0 : Compiler.Encoders.Asm.wordCmpHOL .equal (0#64) (0#64) = true := by decide
  have hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.op .or [.rfield 0 (.var .local (ofString "a")),
        .rfield 1 (.var .local (ofString "a")),
        .rfield 2 (.var .local (ofString "a")),
        .rfield 3 (.var .local (ofString "a"))]) (.const (0#64))) = some (.val (.word 1)) := by
    simp [evalHOLExact, evalListHOLExact, ha, u256ZeroVal, u256Val, valueIsWord, valueWord, hor4_0, hcmp0]
  rw [hcond]
  dsimp only
  rw [if_neg (by decide : ¬ ((1 : BitVec 64) = 0))]
  rw [evaluateHOLFiniteState_return]
  have hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.const (1#64)) =
      some (.val (.word 1)) := rfl
  rw [hev]
  dsimp only
  have hsz : Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL s.structs
      (shapeOfHOLExact (.val (.word 1) : ValueHOL 64)) ≤ 32 := by
    simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
  rw [if_pos hsz]

private theorem mul64x64_body_eq : sourceFnBody Guest.Software.guestFn_mul64x64 =
    .dec (ofString "a0") .one (.op .and [.var .local (ofString "a"), .const (4294967295#64)])
      (.dec (ofString "a1") .one (.shift .lsr (.var .local (ofString "a")) (.const (32#64)))
        (.dec (ofString "b0") .one (.op .and [.var .local (ofString "b"), .const (4294967295#64)])
          (.dec (ofString "b1") .one (.shift .lsr (.var .local (ofString "b")) (.const (32#64)))
            (.dec (ofString "p00") .one (.panop .mul [.var .local (ofString "a0"), .var .local (ofString "b0")])
              (.dec (ofString "p11") .one (.panop .mul [.var .local (ofString "a1"), .var .local (ofString "b1")])
                (.dec (ofString "mid") (.comb [.one, .one]) (.rstruct [.const (0#64), .const (0#64)])
                  (.seq
                    (.primitive (ofString "mid") .addCarry
                      [.panop .mul [.var .local (ofString "a0"), .var .local (ofString "b1")],
                       .panop .mul [.var .local (ofString "a1"), .var .local (ofString "b0")],
                       .const (0#64)])
                    (.dec (ofString "lo") (.comb [.one, .one]) (.rstruct [.const (0#64), .const (0#64)])
                      (.seq
                        (.primitive (ofString "lo") .addCarry
                          [.var .local (ofString "p00"),
                           .shift .lsl (.rfield 0 (.var .local (ofString "mid"))) (.const (32#64)),
                           .const (0#64)])
                        (.dec (ofString "hi") .one
                          (.op .add
                            [.var .local (ofString "p11"),
                             .shift .lsr (.rfield 0 (.var .local (ofString "mid"))) (.const (32#64)),
                             .shift .lsl (.rfield 1 (.var .local (ofString "mid"))) (.const (32#64)),
                             .rfield 1 (.var .local (ofString "lo"))])
                          (.return (.rstruct [.rfield 0 (.var .local (ofString "lo")), .var .local (ofString "hi")])))))))))))) := rfl

private theorem eval_dec_ret {F : Type}
    {name : MlS} {sh : ShapeHOL} {e : ExpHOL 64} {body : ProgHOL 64}
    {st : PanSemStateFiniteExact 64 F} {v retVal : ValueHOL 64}
    (hev : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) e = some v)
    (hsh : shapeEqHOL sh (shapeOfHOLExact v) = true)
    (hbody : ∀ st' : PanSemStateFiniteExact 64 F,
      st'.locals = st.locals.update (name, v) →
      ∃ post,
        evaluateHOLFiniteState st' body = (some (.returned retVal), post) ∧
        emptyLocalsHOLFinite post = emptyLocalsHOLFinite st') :
    ∃ post',
      evaluateHOLFiniteState st (.dec name sh e body) = (some (.returned retVal), post') ∧
      emptyLocalsHOLFinite post' = emptyLocalsHOLFinite st := by
  obtain ⟨post, hrun, hemp⟩ := hbody (setVarHOLFinite name v st) rfl
  refine ⟨{ post with locals := HolFiniteMapExact.resVarEq post.locals (name, st.locals.lookup name) }, ?_, ?_⟩
  · rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    rw [hev]
    dsimp only
    rw [if_pos hsh, hrun]
  · have hemp' : emptyLocalsHOLFinite { post with locals := HolFiniteMapExact.resVarEq post.locals (name, st.locals.lookup name) } =
        emptyLocalsHOLFinite post := rfl
    rw [hemp', hemp]
    rfl

private theorem eval_prim_seq_ret {F : Type}
    {name : MlS} {op : PrimOp} {args : List (ExpHOL 64)} {tail : ProgHOL 64}
    {st : PanSemStateFiniteExact 64 F} {vals : List (ValueHOL 64)} {v retVal : ValueHOL 64}
    (hargs : @evalListHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) args = some vals)
    (hpo : panPrimopHOLExact op vals = some v)
    (hval : st.isValidValueHOLFinite .local name v = true)
    (htail : ∀ st' : PanSemStateFiniteExact 64 F,
      st'.locals = st.locals.update (name, v) →
      ∃ post,
        evaluateHOLFiniteState st' tail = (some (.returned retVal), post) ∧
        emptyLocalsHOLFinite post = emptyLocalsHOLFinite st') :
    ∃ post',
      evaluateHOLFiniteState st (.seq (.primitive name op args) tail) = (some (.returned retVal), post') ∧
      emptyLocalsHOLFinite post' = emptyLocalsHOLFinite st := by
  obtain ⟨post, hrun, hemp⟩ := htail (setVarHOLFinite name v st) rfl
  refine ⟨post, ?_, ?_⟩
  · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_primitive, hargs]
    dsimp only
    rw [hpo]
    dsimp only
    rw [if_pos hval]
    exact hrun
  · rw [hemp]; rfl

private theorem eval_mul64x64_body_zero_left {F : Type}
    (s : PanSemStateFiniteExact 64 F) (wb : BitVec 64)
    (ha : s.locals.lookup (ofString "a") = some (.val (.word (0#64))))
    (hb : s.locals.lookup (ofString "b") = some (.val (.word wb))) :
    ∃ post,
      evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_mul64x64) =
        (some (.returned (.rStruct [.val (.word (0#64)), .val (.word (0#64))])), post) ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite s := by
  rw [mul64x64_body_eq]
  have hlk_eq {m : HolFiniteMapExact MlS (ValueHOL 64)} (k : MlS) (v : ValueHOL 64) :
      (m.update (k, v)).lookup k = some v := by
    simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hlk_ne {m : HolFiniteMapExact MlS (ValueHOL 64)} {k1 k2 : MlS} (v : ValueHOL 64) (hne : k1 ≠ k2) :
      (m.update (k1, v)).lookup k2 = m.lookup k2 := by
    simp [HolFiniteMapExact.lookup_update, FUPDATE, hne]
  have hand0 : wordOpHOL .and [0#64, 4294967295#64] = some 0#64 := by decide
  have hlsr0 : wordShiftHOL .lsr (0#64) 32 = some 0#64 := by decide
  have hlsl0 : wordShiftHOL .lsl (0#64) 32 = some 0#64 := by decide
  have hadd4_0 : wordOpHOL .add [0#64, 0#64, 0#64, 0#64] = some 0#64 := by decide
  have h32 : (32#64).toNat = 32 := rfl
  have hsh1 : shapeEqHOL .one (shapeOfHOLExact (.val (.word (0#64)) : ValueHOL 64)) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  have hsh2 : shapeEqHOL (.comb [.one, .one]) (shapeOfHOLExact (.rStruct [.val (.word (0#64)), .val (.word (0#64))] : ValueHOL 64)) = true := by
    simp [shapeEqHOL, shapeEqHOL.shapeEqListHOL, shapeOfHOLExact]
  have hpo0 : panPrimopHOLExact PrimOp.addCarry ([.val (.word (0#64)), .val (.word (0#64)), .val (.word (0#64))] : List (ValueHOL 64)) =
      some (.rStruct [.val (.word (0#64)), .val (.word (0#64))]) := by
    simp [panPrimopHOLExact, wordAddCarryHOL]
  refine eval_dec_ret (v := .val (.word (0#64)))
    (by simp [evalHOLExact, evalListHOLExact, ha, valueIsWord, valueWord, hand0]) hsh1 ?_
  intro s1 hl1
  have hs1_a0 : s1.locals.lookup (ofString "a0") = some (.val (.word (0#64))) := by rw [hl1]; exact hlk_eq _ _
  have hs1_a : s1.locals.lookup (ofString "a") = some (.val (.word (0#64))) := by rw [hl1, hlk_ne _ (by decide)]; exact ha
  have hs1_b : s1.locals.lookup (ofString "b") = some (.val (.word wb)) := by rw [hl1, hlk_ne _ (by decide)]; exact hb
  clear hl1 ha hb s
  refine eval_dec_ret (v := .val (.word (0#64)))
    (by simp [evalHOLExact, hs1_a, h32, hlsr0]) hsh1 ?_
  intro s2 hl2
  have hs2_a1 : s2.locals.lookup (ofString "a1") = some (.val (.word (0#64))) := by rw [hl2]; exact hlk_eq _ _
  have hs2_a0 : s2.locals.lookup (ofString "a0") = some (.val (.word (0#64))) := by rw [hl2, hlk_ne _ (by decide)]; exact hs1_a0
  have hs2_b : s2.locals.lookup (ofString "b") = some (.val (.word wb)) := by rw [hl2, hlk_ne _ (by decide)]; exact hs1_b
  clear hl2 hs1_a0 hs1_a hs1_b s1
  have hwb0 : ∃ wb0 : BitVec 64, wordOpHOL .and [wb, 4294967295#64] = some wb0 :=
    ⟨_, rfl⟩
  obtain ⟨wb0, hwb0⟩ := hwb0
  refine eval_dec_ret (v := .val (.word wb0))
    (by simp [evalHOLExact, evalListHOLExact, hs2_b, valueIsWord, valueWord, hwb0])
    (by simp [shapeEqHOL, shapeOfHOLExact]) ?_
  intro s3 hl3
  have hs3_b0 : s3.locals.lookup (ofString "b0") = some (.val (.word wb0)) := by rw [hl3]; exact hlk_eq _ _
  have hs3_a1 : s3.locals.lookup (ofString "a1") = some (.val (.word (0#64))) := by rw [hl3, hlk_ne _ (by decide)]; exact hs2_a1
  have hs3_a0 : s3.locals.lookup (ofString "a0") = some (.val (.word (0#64))) := by rw [hl3, hlk_ne _ (by decide)]; exact hs2_a0
  have hs3_b : s3.locals.lookup (ofString "b") = some (.val (.word wb)) := by rw [hl3, hlk_ne _ (by decide)]; exact hs2_b
  clear hl3 hs2_a1 hs2_a0 hs2_b hwb0 s2
  have hwb1 : ∃ wb1 : BitVec 64, wordShiftHOL .lsr wb 32 = some wb1 :=
    ⟨wb >>> 32, by simp [wordShiftHOL]⟩
  obtain ⟨wb1, hwb1⟩ := hwb1
  refine eval_dec_ret (v := .val (.word wb1))
    (by simp [evalHOLExact, hs3_b, h32, hwb1])
    (by simp [shapeEqHOL, shapeOfHOLExact]) ?_
  intro s4 hl4
  have hs4_b1 : s4.locals.lookup (ofString "b1") = some (.val (.word wb1)) := by rw [hl4]; exact hlk_eq _ _
  have hs4_b0 : s4.locals.lookup (ofString "b0") = some (.val (.word wb0)) := by rw [hl4, hlk_ne _ (by decide)]; exact hs3_b0
  have hs4_a1 : s4.locals.lookup (ofString "a1") = some (.val (.word (0#64))) := by rw [hl4, hlk_ne _ (by decide)]; exact hs3_a1
  have hs4_a0 : s4.locals.lookup (ofString "a0") = some (.val (.word (0#64))) := by rw [hl4, hlk_ne _ (by decide)]; exact hs3_a0
  clear hl4 hs3_b0 hs3_a1 hs3_a0 hs3_b hwb1 s3
  refine eval_dec_ret (v := .val (.word (0#64)))
    (by simp [evalHOLExact, evalListHOLExact, hs4_a0, hs4_b0, valueIsWord, valueWord, panOpHOL]) hsh1 ?_
  intro s5 hl5
  have hs5_p00 : s5.locals.lookup (ofString "p00") = some (.val (.word (0#64))) := by rw [hl5]; exact hlk_eq _ _
  have hs5_b1 : s5.locals.lookup (ofString "b1") = some (.val (.word wb1)) := by rw [hl5, hlk_ne _ (by decide)]; exact hs4_b1
  have hs5_b0 : s5.locals.lookup (ofString "b0") = some (.val (.word wb0)) := by rw [hl5, hlk_ne _ (by decide)]; exact hs4_b0
  have hs5_a1 : s5.locals.lookup (ofString "a1") = some (.val (.word (0#64))) := by rw [hl5, hlk_ne _ (by decide)]; exact hs4_a1
  have hs5_a0 : s5.locals.lookup (ofString "a0") = some (.val (.word (0#64))) := by rw [hl5, hlk_ne _ (by decide)]; exact hs4_a0
  clear hl5 hs4_b1 hs4_b0 hs4_a1 hs4_a0 s4
  refine eval_dec_ret (v := .val (.word (0#64)))
    (by simp [evalHOLExact, evalListHOLExact, hs5_a1, hs5_b1, valueIsWord, valueWord, panOpHOL]) hsh1 ?_
  intro s6 hl6
  have hs6_p11 : s6.locals.lookup (ofString "p11") = some (.val (.word (0#64))) := by rw [hl6]; exact hlk_eq _ _
  have hs6_p00 : s6.locals.lookup (ofString "p00") = some (.val (.word (0#64))) := by rw [hl6, hlk_ne _ (by decide)]; exact hs5_p00
  have hs6_b1 : s6.locals.lookup (ofString "b1") = some (.val (.word wb1)) := by rw [hl6, hlk_ne _ (by decide)]; exact hs5_b1
  have hs6_b0 : s6.locals.lookup (ofString "b0") = some (.val (.word wb0)) := by rw [hl6, hlk_ne _ (by decide)]; exact hs5_b0
  have hs6_a1 : s6.locals.lookup (ofString "a1") = some (.val (.word (0#64))) := by rw [hl6, hlk_ne _ (by decide)]; exact hs5_a1
  have hs6_a0 : s6.locals.lookup (ofString "a0") = some (.val (.word (0#64))) := by rw [hl6, hlk_ne _ (by decide)]; exact hs5_a0
  clear hl6 hs5_p00 hs5_b1 hs5_b0 hs5_a1 hs5_a0 s5
  refine eval_dec_ret (v := .rStruct [.val (.word (0#64)), .val (.word (0#64))])
    (by simp [evalHOLExact, evalListHOLExact]) hsh2 ?_
  intro s7 hl7
  have hs7_mid : s7.locals.lookup (ofString "mid") = some (.rStruct [.val (.word (0#64)), .val (.word (0#64))]) := by rw [hl7]; exact hlk_eq _ _
  have hs7_p11 : s7.locals.lookup (ofString "p11") = some (.val (.word (0#64))) := by rw [hl7, hlk_ne _ (by decide)]; exact hs6_p11
  have hs7_p00 : s7.locals.lookup (ofString "p00") = some (.val (.word (0#64))) := by rw [hl7, hlk_ne _ (by decide)]; exact hs6_p00
  have hs7_b1 : s7.locals.lookup (ofString "b1") = some (.val (.word wb1)) := by rw [hl7, hlk_ne _ (by decide)]; exact hs6_b1
  have hs7_b0 : s7.locals.lookup (ofString "b0") = some (.val (.word wb0)) := by rw [hl7, hlk_ne _ (by decide)]; exact hs6_b0
  have hs7_a1 : s7.locals.lookup (ofString "a1") = some (.val (.word (0#64))) := by rw [hl7, hlk_ne _ (by decide)]; exact hs6_a1
  have hs7_a0 : s7.locals.lookup (ofString "a0") = some (.val (.word (0#64))) := by rw [hl7, hlk_ne _ (by decide)]; exact hs6_a0
  clear hl7 hs6_p11 hs6_p00 hs6_b1 hs6_b0 hs6_a1 hs6_a0 s6
  refine eval_prim_seq_ret
    (by simp [evalListHOLExact, evalHOLExact, hs7_a0, hs7_a1, hs7_b0, hs7_b1, valueIsWord, valueWord, panOpHOL])
    hpo0
    (by simp [isValidValueHOLFinite, lookupKvarHOLFinite, hs7_mid, shapeEqHOL, shapeEqHOL.shapeEqListHOL, shapeOfHOLExact]) ?_
  intro s8 hl8
  have hs8_mid : s8.locals.lookup (ofString "mid") = some (.rStruct [.val (.word (0#64)), .val (.word (0#64))]) := by rw [hl8]; exact hlk_eq _ _
  have hs8_p11 : s8.locals.lookup (ofString "p11") = some (.val (.word (0#64))) := by rw [hl8, hlk_ne _ (by decide)]; exact hs7_p11
  have hs8_p00 : s8.locals.lookup (ofString "p00") = some (.val (.word (0#64))) := by rw [hl8, hlk_ne _ (by decide)]; exact hs7_p00
  clear hl8 hs7_mid hs7_p11 hs7_p00 hs7_b1 hs7_b0 hs7_a1 hs7_a0 s7
  refine eval_dec_ret (v := .rStruct [.val (.word (0#64)), .val (.word (0#64))])
    (by simp [evalHOLExact, evalListHOLExact]) hsh2 ?_
  intro s9 hl9
  have hs9_lo : s9.locals.lookup (ofString "lo") = some (.rStruct [.val (.word (0#64)), .val (.word (0#64))]) := by rw [hl9]; exact hlk_eq _ _
  have hs9_mid : s9.locals.lookup (ofString "mid") = some (.rStruct [.val (.word (0#64)), .val (.word (0#64))]) := by rw [hl9, hlk_ne _ (by decide)]; exact hs8_mid
  have hs9_p11 : s9.locals.lookup (ofString "p11") = some (.val (.word (0#64))) := by rw [hl9, hlk_ne _ (by decide)]; exact hs8_p11
  have hs9_p00 : s9.locals.lookup (ofString "p00") = some (.val (.word (0#64))) := by rw [hl9, hlk_ne _ (by decide)]; exact hs8_p00
  clear hl9 hs8_mid hs8_p11 hs8_p00 s8
  refine eval_prim_seq_ret
    (by simp [evalListHOLExact, evalHOLExact, hs9_p00, hs9_mid, h32, hlsl0])
    hpo0
    (by simp [isValidValueHOLFinite, lookupKvarHOLFinite, hs9_lo, shapeEqHOL, shapeEqHOL.shapeEqListHOL, shapeOfHOLExact]) ?_
  intro s10 hl10
  have hs10_lo : s10.locals.lookup (ofString "lo") = some (.rStruct [.val (.word (0#64)), .val (.word (0#64))]) := by rw [hl10]; exact hlk_eq _ _
  have hs10_mid : s10.locals.lookup (ofString "mid") = some (.rStruct [.val (.word (0#64)), .val (.word (0#64))]) := by rw [hl10, hlk_ne _ (by decide)]; exact hs9_mid
  have hs10_p11 : s10.locals.lookup (ofString "p11") = some (.val (.word (0#64))) := by rw [hl10, hlk_ne _ (by decide)]; exact hs9_p11
  clear hl10 hs9_lo hs9_mid hs9_p11 hs9_p00 s9
  refine eval_dec_ret (v := .val (.word (0#64)))
    (by simp [evalHOLExact, evalListHOLExact, hs10_p11, hs10_mid, hs10_lo, valueIsWord, valueWord, h32, hlsr0, hlsl0, hadd4_0]) hsh1 ?_
  intro s11 hl11
  have hs11_hi : s11.locals.lookup (ofString "hi") = some (.val (.word (0#64))) := by rw [hl11]; exact hlk_eq _ _
  have hs11_lo : s11.locals.lookup (ofString "lo") = some (.rStruct [.val (.word (0#64)), .val (.word (0#64))]) := by rw [hl11, hlk_ne _ (by decide)]; exact hs10_lo
  clear hl11 hs10_lo hs10_mid hs10_p11 s10
  refine ⟨emptyLocalsHOLFinite s11, ?_, rfl⟩
  rw [evaluateHOLFiniteState_return]
  have hev_ret : @evalHOLExact 64 F _ s11.toExact (fun a => Classical.propDecidable (s11.memaddrs a))
      (.rstruct [.rfield 0 (.var .local (ofString "lo")), .var .local (ofString "hi")]) =
      some (.rStruct [.val (.word (0#64)), .val (.word (0#64))]) := by
    simp [evalHOLExact, evalListHOLExact, hs11_lo, hs11_hi]
  rw [hev_ret]
  dsimp only
  have hsz : Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL s11.structs
      (shapeOfHOLExact (.rStruct [.val (.word (0#64)), .val (.word (0#64))] : ValueHOL 64)) ≤ 32 := by
    simp [shapeOfHOLExact, sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL]
  rw [if_pos hsz]

private theorem one_arg_lookup_inv {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name param : MlS) (ps rs : ShapeHOL) (body : ProgHOL width) (v : ValueHOL width)
    {foundBody : ProgHOL width} {callee : HolFiniteMapExact MlS (ValueHOL width)} {foundRs : ShapeHOL}
    (lookup : code name = some ([(param, ps)], body, rs))
    (hfound : PanSemStateFiniteExact.lookupCodeHOLFinite code name [v] = some (foundBody, callee, foundRs)) :
    foundBody = body ∧ callee = HolFiniteMapExact.empty.update (param, v) ∧ foundRs = rs := by
  have hshape : shapeEqHOL ps (shapeOfHOLExact v) = true := by
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
    split at hfound
    · cases hfound
    · rename_i _ _ _ raw
      simp [lookupCodeHOLExact, lookup] at raw
      exact raw.1
  rw [pan_one_arg_lookup code name param ps rs body v hshape lookup] at hfound
  cases hfound
  exact ⟨rfl, rfl, rfl⟩

private theorem two_arg_lookup_inv {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name first second : MlS) (ps1 ps2 rs : ShapeHOL) (body : ProgHOL width) (v1 v2 : ValueHOL width)
    {foundBody : ProgHOL width} {callee : HolFiniteMapExact MlS (ValueHOL width)} {foundRs : ShapeHOL}
    (different : first ≠ second)
    (lookup : code name = some ([(first, ps1), (second, ps2)], body, rs))
    (hfound : PanSemStateFiniteExact.lookupCodeHOLFinite code name [v1, v2] = some (foundBody, callee, foundRs)) :
    foundBody = body ∧
      callee = (HolFiniteMapExact.empty.update (first, v1)).update (second, v2) ∧
      foundRs = rs := by
  have hshapes : shapeEqHOL ps1 (shapeOfHOLExact v1) = true ∧ shapeEqHOL ps2 (shapeOfHOLExact v2) = true := by
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
    split at hfound
    · cases hfound
    · rename_i _ _ _ raw
      simp [lookupCodeHOLExact, lookup, different] at raw
      exact ⟨raw.1.1, raw.1.2⟩
  rw [pan_two_arg_lookup code name first second ps1 ps2 rs body v1 v2 different hshapes.1 hshapes.2 lookup] at hfound
  cases hfound
  exact ⟨rfl, rfl, rfl⟩

private theorem shape_one_is_word {v : ValueHOL 64}
    (h : shapeEqHOL (shapeOfHOLExact v) .one = true) :
    ∃ w : BitVec 64, v = .val (.word w) := by
  cases v with
  | val wl =>
    cases wl with
    | word w => exact ⟨w, rfl⟩
  | rStruct _ => simp [shapeOfHOLExact, shapeEqHOL] at h
  | nStruct _ _ => simp [shapeOfHOLExact, shapeEqHOL] at h

private theorem seq_none {F : Type} {s post : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64}
    (h : evaluateHOLFiniteState s (.seq a b) = (none, post)) :
    ∃ mid, evaluateHOLFiniteState s a = (none, mid) ∧
      evaluateHOLFiniteState mid b = (none, post) := by
  rw [evaluateHOLFiniteState_seq_line780] at h
  cases ha : evaluateHOLFiniteState s a with
  | mk r mid =>
    rw [ha] at h
    cases r with
    | none => exact ⟨mid, rfl, h⟩
    | some _ => simp at h

private theorem dec_none {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {name : MlS} {sh : ShapeHOL} {e : ExpHOL 64} {body : ProgHOL 64}
    (h : evaluateHOLFiniteState s (.dec name sh e body) = (none, post)) :
    ∃ v inner,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e = some v ∧
      shapeEqHOL sh (shapeOfHOLExact v) = true ∧
      evaluateHOLFiniteState (setVarHOLFinite name v s) body = (none, inner) ∧
      post.locals = HolFiniteMapExact.resVarEq inner.locals (name, s.locals.lookup name) := by
  rw [evaluateHOLFiniteState_dec_total] at h
  dsimp only at h
  split at h
  · simp at h
  · rename_i v hv
    split at h
    · rename_i hsh
      cases hb : evaluateHOLFiniteState (setVarHOLFinite name v s) body with
      | mk r inner =>
        rw [hb] at h
        obtain ⟨he, hp⟩ := Prod.mk.inj h
        subst he
        exact ⟨v, inner, hv, hsh, hb, by rw [← hp]⟩
    · simp at h

private theorem decCall_none {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {name fn : MlS} {sh : ShapeHOL} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (h : evaluateHOLFiniteState s (.decCall name sh fn args cont) = (none, post)) :
    ∃ (vals : List (ValueHOL 64)) (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
      (rs : ShapeHOL) (w : ValueHOL 64) (bpost resumed inner : PanSemStateFiniteExact 64 F),
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vals ∧
      lookupCodeHOLFinite s.code.lookup fn vals = some (body, callee, rs) ∧
      s.clock ≠ 0 ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned w), bpost) ∧
      shapeEqHOL (shapeOfHOLExact w) sh = true ∧
      resumed.locals = s.locals.update (name, w) ∧
      resumed.code = s.code ∧
      evaluateHOLFiniteState resumed cont = (none, inner) ∧
      post.locals = HolFiniteMapExact.resVarEq inner.locals (name, s.locals.lookup name) := by
  rw [evaluateHOLFiniteState_decCall_total] at h
  cases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with
  | none => rw [hargs] at h; simp at h
  | some vals =>
    rw [hargs] at h; dsimp only at h
    cases hlk : lookupCodeHOLFinite s.code.lookup fn vals with
    | none => rw [hlk] at h; simp at h
    | some installed =>
      obtain ⟨body, callee, rs⟩ := installed
      rw [hlk] at h; dsimp only at h
      split at h
      · simp at h
      · rename_i hclk
        have hrem := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s callee) body
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body).1
        cases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
        | mk r1 bpost =>
          rw [hrun] at h hrem hmeta
          dsimp only at hmeta hrem
          have hfix : fixClockHOLFinite (callEntryStateHOLFinite s callee) (r1, bpost) = (r1, bpost) := by
            simp [fixClockHOLFinite, Nat.not_lt.mpr hrem]
          rw [hfix] at h; dsimp only at h
          rcases r1 with _ | (_ | _ | _ | _ | w | _ | _)
          all_goals first | (simp at h; done) | skip
          simp only [] at h
          split at h
          · rename_i hboth
            obtain ⟨he, hp⟩ := Prod.mk.inj h
            have hsh : shapeEqHOL (shapeOfHOLExact w) sh = true := by
              simp [Bool.and_eq_true] at hboth; exact hboth.1
            let resumed : PanSemStateFiniteExact 64 F := setVarHOLFinite name w { bpost with locals := s.locals }
            let inner : PanSemStateFiniteExact 64 F := (evaluateHOLFiniteState resumed cont).2
            refine ⟨vals, body, callee, rs, w, bpost, resumed, inner, rfl, hlk, hclk, hrun, hsh, rfl, hmeta,
              Prod.ext he rfl, by rw [← hp]⟩
          · simp at h

private theorem decCall_returned {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {name fn : MlS} {sh : ShapeHOL} {args : List (ExpHOL 64)} {cont : ProgHOL 64} {retVal : ValueHOL 64}
    (h : evaluateHOLFiniteState s (.decCall name sh fn args cont) = (some (.returned retVal), post)) :
    ∃ (vals : List (ValueHOL 64)) (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
      (rs : ShapeHOL) (w : ValueHOL 64) (bpost resumed inner : PanSemStateFiniteExact 64 F),
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vals ∧
      lookupCodeHOLFinite s.code.lookup fn vals = some (body, callee, rs) ∧
      s.clock ≠ 0 ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned w), bpost) ∧
      shapeEqHOL (shapeOfHOLExact w) sh = true ∧
      resumed.locals = s.locals.update (name, w) ∧
      resumed.code = s.code ∧
      evaluateHOLFiniteState resumed cont = (some (.returned retVal), inner) := by
  rw [evaluateHOLFiniteState_decCall_total] at h
  cases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with
  | none => rw [hargs] at h; simp at h
  | some vals =>
    rw [hargs] at h; dsimp only at h
    cases hlk : lookupCodeHOLFinite s.code.lookup fn vals with
    | none => rw [hlk] at h; simp at h
    | some installed =>
      obtain ⟨body, callee, rs⟩ := installed
      rw [hlk] at h; dsimp only at h
      split at h
      · simp at h
      · rename_i hclk
        have hrem := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s callee) body
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body).1
        cases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
        | mk r1 bpost =>
          rw [hrun] at h hrem hmeta
          dsimp only at hmeta hrem
          have hfix : fixClockHOLFinite (callEntryStateHOLFinite s callee) (r1, bpost) = (r1, bpost) := by
            simp [fixClockHOLFinite, Nat.not_lt.mpr hrem]
          rw [hfix] at h; dsimp only at h
          rcases r1 with _ | (_ | _ | _ | _ | w | _ | _)
          all_goals first | (simp at h; done) | skip
          simp only [] at h
          split at h
          · rename_i hboth
            obtain ⟨he, _hp⟩ := Prod.mk.inj h
            have hsh : shapeEqHOL (shapeOfHOLExact w) sh = true := by
              simp [Bool.and_eq_true] at hboth; exact hboth.1
            let resumed : PanSemStateFiniteExact 64 F := setVarHOLFinite name w { bpost with locals := s.locals }
            let inner : PanSemStateFiniteExact 64 F := (evaluateHOLFiniteState resumed cont).2
            refine ⟨vals, body, callee, rs, w, bpost, resumed, inner, rfl, hlk, hclk, hrun, hsh, rfl, hmeta,
              Prod.ext he rfl⟩
          · simp at h

private theorem call_local_none {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {dest fn : MlS} {args : List (ExpHOL 64)}
    (h : evaluateHOLFiniteState s (.call (some (some (.local, dest), none)) fn args) = (none, post)) :
    ∃ (vals : List (ValueHOL 64)) (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
      (rs : ShapeHOL) (w : ValueHOL 64) (bpost : PanSemStateFiniteExact 64 F),
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vals ∧
      lookupCodeHOLFinite s.code.lookup fn vals = some (body, callee, rs) ∧
      s.clock ≠ 0 ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned w), bpost) ∧
      shapeEqHOL (shapeOfHOLExact w) rs = true ∧
      post.locals = s.locals.update (dest, w) ∧
      post.code = s.code := by
  rw [evaluateHOLFiniteState_call] at h
  cases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with
  | none => rw [hargs] at h; simp at h
  | some vals =>
    rw [hargs] at h; dsimp only at h
    cases hlk : lookupCodeHOLFinite s.code.lookup fn vals with
    | none => rw [hlk] at h; simp at h
    | some installed =>
      obtain ⟨body, callee, rs⟩ := installed
      rw [hlk] at h; dsimp only at h
      split at h
      · simp at h
      · rename_i hclk
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body).1
        cases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
        | mk r1 bpost =>
          rw [hrun] at h hmeta
          dsimp only at hmeta
          rcases r1 with _ | (_ | _ | _ | _ | w | _ | _)
          all_goals first | (simp [emptyLocalsHOLFinite] at h; done) | skip
          dsimp only at h
          split at h
          · rename_i hrs
            split at h
            · simp [setKvarHOLFinite, setVarHOLFinite] at h
              refine ⟨vals, body, callee, rs, w, bpost, rfl, hlk, hclk, hrun, hrs, ?_, ?_⟩
              · rw [← h]
              · rw [← h]; exact hmeta
            · simp at h
          · simp at h

private theorem return_returned_inv {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {e : ExpHOL 64} {retVal v : ValueHOL 64}
    (hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e = some v)
    (h : evaluateHOLFiniteState s (.return e) = (some (.returned retVal), post)) :
    retVal = v := by
  rw [evaluateHOLFiniteState_return, hev] at h
  dsimp only at h
  split at h
  · simp at h; exact h.1.symm
  · simp at h

private theorem decCall_return_not_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name fn : MlS) (sh : ShapeHOL) (args : List (ExpHOL 64)) (e : ExpHOL 64) :
    (evaluateHOLFiniteState s (.decCall name sh fn args (.return e))).1 ≠ none := by
  intro hnone
  cases h : evaluateHOLFiniteState s (.decCall name sh fn args (.return e)) with
  | mk r post =>
    rw [h] at hnone; dsimp only at hnone; subst hnone
    obtain ⟨_, _, _, _, _, _, resumed, inner, _, _, _, _, _, _, _, hret, _⟩ := decCall_none h
    rw [evaluateHOLFiniteState_return] at hret
    split at hret
    · simp at hret
    · split at hret <;> simp at hret

private theorem seq_returned_first {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {a b : ProgHOL 64} {retVal : ValueHOL 64}
    (hnn : (evaluateHOLFiniteState s a).1 ≠ none)
    (h : evaluateHOLFiniteState s (.seq a b) = (some (.returned retVal), post)) :
    evaluateHOLFiniteState s a = (some (.returned retVal), post) := by
  rw [evaluateHOLFiniteState_seq_line780] at h
  cases ha : evaluateHOLFiniteState s a with
  | mk r mid =>
    rw [ha] at h hnn
    cases r with
    | none => exact False.elim (hnn rfl)
    | some _ => exact h

private theorem shape_u256_is_four_words {v : ValueHOL 64}
    (h : shapeEqHOL u256ShapeHOL (shapeOfHOLExact v) = true) :
    ∃ w0 w1 w2 w3 : BitVec 64, v = u256Val w0 w1 w2 w3 := by
  cases v with
  | val wl => cases wl with | word _ => simp [u256ShapeHOL, shapeOfHOLExact, shapeEqHOL] at h
  | nStruct _ _ => simp [u256ShapeHOL, shapeOfHOLExact, shapeEqHOL] at h
  | rStruct vs =>
    rcases vs with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨_, _⟩⟩⟩⟩⟩
    all_goals try (simp [u256ShapeHOL, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h; done)
    simp only [u256ShapeHOL, shapeOfHOLExact, List.map, shapeEqHOL, shapeEqHOL.shapeEqListHOL, Bool.and_eq_true] at h
    rcases v0 with ⟨⟨w0⟩⟩ | _ | _ <;> try (simp [shapeOfHOLExact, shapeEqHOL] at h; done)
    rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> try (simp [shapeOfHOLExact, shapeEqHOL] at h; done)
    rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;> try (simp [shapeOfHOLExact, shapeEqHOL] at h; done)
    rcases v3 with ⟨⟨w3⟩⟩ | _ | _ <;> try (simp [shapeOfHOLExact, shapeEqHOL] at h; done)
    exact ⟨w0, w1, w2, w3, rfl⟩

private theorem one_arg_lookup_inv_shape {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name param : MlS) (ps rs : ShapeHOL) (body : ProgHOL width) (v : ValueHOL width)
    {foundBody : ProgHOL width} {callee : HolFiniteMapExact MlS (ValueHOL width)} {foundRs : ShapeHOL}
    (lookup : code name = some ([(param, ps)], body, rs))
    (hfound : PanSemStateFiniteExact.lookupCodeHOLFinite code name [v] = some (foundBody, callee, foundRs)) :
    shapeEqHOL ps (shapeOfHOLExact v) = true ∧
      foundBody = body ∧ callee = HolFiniteMapExact.empty.update (param, v) ∧ foundRs = rs := by
  have hshape : shapeEqHOL ps (shapeOfHOLExact v) = true := by
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
    split at hfound
    · cases hfound
    · rename_i _ _ _ raw
      simp [lookupCodeHOLExact, lookup] at raw
      exact raw.1
  exact ⟨hshape, one_arg_lookup_inv code name param ps rs body v lookup hfound⟩

private theorem two_arg_lookup_inv_shape {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name first second : MlS) (ps1 ps2 rs : ShapeHOL) (body : ProgHOL width) (v1 v2 : ValueHOL width)
    {foundBody : ProgHOL width} {callee : HolFiniteMapExact MlS (ValueHOL width)} {foundRs : ShapeHOL}
    (different : first ≠ second)
    (lookup : code name = some ([(first, ps1), (second, ps2)], body, rs))
    (hfound : PanSemStateFiniteExact.lookupCodeHOLFinite code name [v1, v2] = some (foundBody, callee, foundRs)) :
    shapeEqHOL ps1 (shapeOfHOLExact v1) = true ∧
      shapeEqHOL ps2 (shapeOfHOLExact v2) = true ∧
      foundBody = body ∧
      callee = (HolFiniteMapExact.empty.update (first, v1)).update (second, v2) ∧
      foundRs = rs := by
  have hshapes : shapeEqHOL ps1 (shapeOfHOLExact v1) = true ∧ shapeEqHOL ps2 (shapeOfHOLExact v2) = true := by
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
    split at hfound
    · cases hfound
    · rename_i _ _ _ raw
      simp [lookupCodeHOLExact, lookup, different] at raw
      exact ⟨raw.1.1, raw.1.2⟩
  exact ⟨hshapes.1, hshapes.2,
    two_arg_lookup_inv code name first second ps1 ps2 rs body v1 v2 different lookup hfound⟩

private theorem returned_u256_mul_body_zero_left {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {retVal : ValueHOL 64} {wb : BitVec 64}
    (hcode : s.code = originalRuntimeCode)
    (ha : s.locals.lookup (ofString "a") = some u256ZeroVal)
    (hb : s.locals.lookup (ofString "b") = some (u256Val wb 0 0 0))
    (h : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_mul) =
      (some (.returned retVal), post)) :
    retVal = u256ZeroVal := by
  have hbody : ∃ slow, sourceFnBody Guest.Software.guestFn_u256_mul =
      .seq
        (.ite (.cmp .equal
            (.op .or [.rfield 1 (.var .local (ofString "a")),
                      .rfield 2 (.var .local (ofString "a")),
                      .rfield 3 (.var .local (ofString "a")),
                      .rfield 1 (.var .local (ofString "b")),
                      .rfield 2 (.var .local (ofString "b")),
                      .rfield 3 (.var .local (ofString "b"))])
            (.const (0#64)))
          (.decCall (ofString "p") (.comb [.one, .one]) (ofString "mul64x64")
            [.rfield 0 (.var .local (ofString "a")), .rfield 0 (.var .local (ofString "b"))]
            (.return (.rstruct
              [.rfield 0 (.var .local (ofString "p")),
               .rfield 1 (.var .local (ofString "p")),
               .const (0#64), .const (0#64)])))
          .skip)
        slow := ⟨_, rfl⟩
  obtain ⟨slow, hbody⟩ := hbody
  rw [hbody] at h
  have hor0 : wordOpHOL .or [0#64, 0#64, 0#64, 0#64, 0#64, 0#64] = some 0#64 := by decide
  have hcmp0 : Compiler.Encoders.Asm.wordCmpHOL .equal (0#64) (0#64) = true := by decide
  have hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal
        (.op .or [.rfield 1 (.var .local (ofString "a")),
                  .rfield 2 (.var .local (ofString "a")),
                  .rfield 3 (.var .local (ofString "a")),
                  .rfield 1 (.var .local (ofString "b")),
                  .rfield 2 (.var .local (ofString "b")),
                  .rfield 3 (.var .local (ofString "b"))])
        (.const (0#64))) = some (.val (.word (1#64))) := by
    simp [evalHOLExact, evalListHOLExact, ha, hb, u256ZeroVal, u256Val, valueIsWord, valueWord, hor0, hcmp0]
  have hite : evaluateHOLFiniteState s
      (.ite (.cmp .equal
          (.op .or [.rfield 1 (.var .local (ofString "a")),
                    .rfield 2 (.var .local (ofString "a")),
                    .rfield 3 (.var .local (ofString "a")),
                    .rfield 1 (.var .local (ofString "b")),
                    .rfield 2 (.var .local (ofString "b")),
                    .rfield 3 (.var .local (ofString "b"))])
          (.const (0#64)))
        (.decCall (ofString "p") (.comb [.one, .one]) (ofString "mul64x64")
          [.rfield 0 (.var .local (ofString "a")), .rfield 0 (.var .local (ofString "b"))]
          (.return (.rstruct
            [.rfield 0 (.var .local (ofString "p")),
             .rfield 1 (.var .local (ofString "p")),
             .const (0#64), .const (0#64)])))
        .skip) =
      evaluateHOLFiniteState s
        (.decCall (ofString "p") (.comb [.one, .one]) (ofString "mul64x64")
          [.rfield 0 (.var .local (ofString "a")), .rfield 0 (.var .local (ofString "b"))]
          (.return (.rstruct
            [.rfield 0 (.var .local (ofString "p")),
             .rfield 1 (.var .local (ofString "p")),
             .const (0#64), .const (0#64)]))) := by
    rw [evaluateHOLFiniteState_ite, hcond]
    simp
  have hnn : (evaluateHOLFiniteState s
      (.ite (.cmp .equal
          (.op .or [.rfield 1 (.var .local (ofString "a")),
                    .rfield 2 (.var .local (ofString "a")),
                    .rfield 3 (.var .local (ofString "a")),
                    .rfield 1 (.var .local (ofString "b")),
                    .rfield 2 (.var .local (ofString "b")),
                    .rfield 3 (.var .local (ofString "b"))])
          (.const (0#64)))
        (.decCall (ofString "p") (.comb [.one, .one]) (ofString "mul64x64")
          [.rfield 0 (.var .local (ofString "a")), .rfield 0 (.var .local (ofString "b"))]
          (.return (.rstruct
            [.rfield 0 (.var .local (ofString "p")),
             .rfield 1 (.var .local (ofString "p")),
             .const (0#64), .const (0#64)])))
        .skip)).1 ≠ none := by
    rw [hite]
    exact decCall_return_not_none s _ _ _ _ _
  have h1 := seq_returned_first hnn h
  rw [hite] at h1
  obtain ⟨vals, body, callee, rs, w, bpost, resumed, inner, hargs, hlk, _, hrun, _, hres_l, _, hret⟩ :=
    decCall_returned h1
  have hvals : vals = [.val (.word (0#64)), .val (.word wb)] := by
    have hev : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.rfield 0 (.var .local (ofString "a")), .rfield 0 (.var .local (ofString "b"))] =
        some [.val (.word (0#64)), .val (.word wb)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, ha, hb, u256ZeroVal, u256Val]
    exact Option.some.inj (hargs.symm.trans hev)
  subst hvals
  have hlk_orig : originalRuntimeCode.lookup (ofString "mul64x64") =
      some ([(ofString "a", .one), (ofString "b", .one)],
        sourceFnBody Guest.Software.guestFn_mul64x64, .comb [.one, .one]) := lookup_mul64x64
  rw [hcode] at hlk
  obtain ⟨rfl, rfl, _⟩ := two_arg_lookup_inv originalRuntimeCode.lookup (ofString "mul64x64")
    (ofString "a") (ofString "b") .one .one (.comb [.one, .one])
    (sourceFnBody Guest.Software.guestFn_mul64x64) (.val (.word (0#64))) (.val (.word wb))
    (by decide) hlk_orig hlk
  obtain ⟨mpost, hmrun, _⟩ := eval_mul64x64_body_zero_left
    (callEntryStateHOLFinite s
      ((HolFiniteMapExact.empty.update (ofString "a", .val (.word (0#64)))).update
        (ofString "b", .val (.word wb)))) wb
    (by
      have hne : ofString "b" ≠ ofString "a" := by decide
      simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne])
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
  have hw : w = .rStruct [.val (.word (0#64)), .val (.word (0#64))] := by
    rw [hmrun] at hrun; simp at hrun; exact hrun.1.symm
  subst hw
  have hp_lk : resumed.locals.lookup (ofString "p") =
      some (.rStruct [.val (.word (0#64)), .val (.word (0#64))]) := by
    rw [hres_l]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  exact return_returned_inv
    (by simp [evalHOLExact, evalListHOLExact, hp_lk, u256ZeroVal, u256Val]) hret

private theorem returned_u256_divmod_body_zero_right {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {retVal : ValueHOL 64}
    (hb : s.locals.lookup (ofString "b") = some u256ZeroVal)
    (h : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_divmod) =
      (some (.returned retVal), post)) :
    retVal = .rStruct
      [.val (.word (0#64)), .val (.word (0#64)), .val (.word (0#64)), .val (.word (0#64)),
       .val (.word (0#64)), .val (.word (0#64)), .val (.word (0#64)), .val (.word (0#64))] := by
  have hbody : ∃ rest, sourceFnBody Guest.Software.guestFn_u256_divmod =
      .seq
        (.ite (.cmp .equal
            (.op .or [.rfield 0 (.var .local (ofString "b")),
                      .rfield 1 (.var .local (ofString "b")),
                      .rfield 2 (.var .local (ofString "b")),
                      .rfield 3 (.var .local (ofString "b"))])
            (.const (0#64)))
          (.return (.rstruct
            [.const (0#64), .const (0#64), .const (0#64), .const (0#64),
             .const (0#64), .const (0#64), .const (0#64), .const (0#64)]))
          .skip)
        rest := ⟨_, rfl⟩
  obtain ⟨rest, hbody⟩ := hbody
  rw [hbody] at h
  have hor0 : wordOpHOL .or [0#64, 0#64, 0#64, 0#64] = some 0#64 := by decide
  have hcmp0 : Compiler.Encoders.Asm.wordCmpHOL .equal (0#64) (0#64) = true := by decide
  have hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal
        (.op .or [.rfield 0 (.var .local (ofString "b")),
                  .rfield 1 (.var .local (ofString "b")),
                  .rfield 2 (.var .local (ofString "b")),
                  .rfield 3 (.var .local (ofString "b"))])
        (.const (0#64))) = some (.val (.word (1#64))) := by
    simp [evalHOLExact, evalListHOLExact, hb, u256ZeroVal, u256Val, valueIsWord, valueWord, hor0, hcmp0]
  have hite : evaluateHOLFiniteState s
      (.ite (.cmp .equal
          (.op .or [.rfield 0 (.var .local (ofString "b")),
                    .rfield 1 (.var .local (ofString "b")),
                    .rfield 2 (.var .local (ofString "b")),
                    .rfield 3 (.var .local (ofString "b"))])
          (.const (0#64)))
        (.return (.rstruct
          [.const (0#64), .const (0#64), .const (0#64), .const (0#64),
           .const (0#64), .const (0#64), .const (0#64), .const (0#64)]))
        .skip) =
      evaluateHOLFiniteState s
        (.return (.rstruct
          [.const (0#64), .const (0#64), .const (0#64), .const (0#64),
           .const (0#64), .const (0#64), .const (0#64), .const (0#64)])) := by
    rw [evaluateHOLFiniteState_ite, hcond]
    simp
  have hnn : (evaluateHOLFiniteState s
      (.ite (.cmp .equal
          (.op .or [.rfield 0 (.var .local (ofString "b")),
                    .rfield 1 (.var .local (ofString "b")),
                    .rfield 2 (.var .local (ofString "b")),
                    .rfield 3 (.var .local (ofString "b"))])
          (.const (0#64)))
        (.return (.rstruct
          [.const (0#64), .const (0#64), .const (0#64), .const (0#64),
           .const (0#64), .const (0#64), .const (0#64), .const (0#64)]))
        .skip)).1 ≠ none := by
    rw [hite, evaluateHOLFiniteState_return]
    split
    · simp
    · split <;> simp
  have h1 := seq_returned_first hnn h
  rw [hite] at h1
  exact return_returned_inv (by simp [evalHOLExact, evalListHOLExact]) h1

private theorem returned_u256_div_body_zero_right {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {retVal va : ValueHOL 64}
    (hcode : s.code = originalRuntimeCode)
    (ha : s.locals.lookup (ofString "a") = some va)
    (hb : s.locals.lookup (ofString "b") = some u256ZeroVal)
    (h : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_div) =
      (some (.returned retVal), post)) :
    retVal = u256ZeroVal := by
  have hbody : sourceFnBody Guest.Software.guestFn_u256_div =
      .decCall (ofString "qr")
        (.comb [.one, .one, .one, .one, .one, .one, .one, .one])
        (ofString "u256_divmod")
        [.var .local (ofString "a"), .var .local (ofString "b")]
        (.return (.rstruct
          [.rfield 0 (.var .local (ofString "qr")),
           .rfield 1 (.var .local (ofString "qr")),
           .rfield 2 (.var .local (ofString "qr")),
           .rfield 3 (.var .local (ofString "qr"))])) := rfl
  rw [hbody] at h
  obtain ⟨vals, body, callee, rs, w, bpost, resumed, inner, hargs, hlk, _, hrun, _, hres_l, _, hret⟩ :=
    decCall_returned h
  have hvals : vals = [va, u256ZeroVal] := by
    have hev : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.var .local (ofString "a"), .var .local (ofString "b")] = some [va, u256ZeroVal] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, ha, hb]
    exact Option.some.inj (hargs.symm.trans hev)
  subst hvals
  rw [hcode] at hlk
  obtain ⟨rfl, rfl, _⟩ := two_arg_lookup_inv originalRuntimeCode.lookup (ofString "u256_divmod")
    (ofString "a") (ofString "b") u256ShapeHOL u256ShapeHOL
    (.comb [.one, .one, .one, .one, .one, .one, .one, .one])
    (sourceFnBody Guest.Software.guestFn_u256_divmod) va u256ZeroVal
    (by decide) lookup_u256_divmod hlk
  have hw := returned_u256_divmod_body_zero_right
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]) hrun
  subst hw
  have hqr_lk : resumed.locals.lookup (ofString "qr") =
      some (.rStruct
        [.val (.word (0#64)), .val (.word (0#64)), .val (.word (0#64)), .val (.word (0#64)),
         .val (.word (0#64)), .val (.word (0#64)), .val (.word (0#64)), .val (.word (0#64))]) := by
    rw [hres_l]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  exact return_returned_inv
    (by simp [evalHOLExact, evalListHOLExact, hqr_lk, u256ZeroVal, u256Val]) hret

private theorem assign_local_none {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {name : MlS} {e : ExpHOL 64}
    (h : evaluateHOLFiniteState s (.assign .local name e) = (none, post)) :
    ∃ v,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e = some v ∧
      post.locals = s.locals.update (name, v) ∧
      post.code = s.code := by
  rw [evaluateHOLFiniteState_assign] at h
  split at h
  · simp at h
  · rename_i v hv
    split at h
    · simp [setKvarHOLFinite, setVarHOLFinite] at h
      exact ⟨v, hv, by rw [← h], by rw [← h]⟩
    · simp at h

private def taylorExpCond : ExpHOL 64 :=
  .cmp .equal (.var .local (ofString "nz")) (.const (0#64))

private def taylorExpTail : ProgHOL 64 :=
  .decCall (ofString "di") u256ShapeHOL (ofString "u256_from_word")
    [.var .local (ofString "i")]
    (.seq
      (.call (some (some (.local, ofString "di"), none)) (ofString "u256_mul")
        [.var .local (ofString "di"), .var .local (ofString "den")])
      (.seq
        (.call (some (some (.local, ofString "acc"), none)) (ofString "u256_div")
          [.var .local (ofString "p"), .var .local (ofString "di")])
        (.seq
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (1#64)]))
          (.call (some (some (.local, ofString "nz"), none)) (ofString "u256_is_zero")
            [.var .local (ofString "acc")]))))

private def taylorExpLoopBody : ProgHOL 64 :=
  .seq
    (.call (some (some (.local, ofString "out"), none)) (ofString "u256_add")
      [.var .local (ofString "out"), .var .local (ofString "acc")])
    (.decCall (ofString "prod")
      (.comb [.one, .one, .one, .one, .one, .one, .one, .one])
      (ofString "u256_mul_full")
      [.var .local (ofString "acc"), .var .local (ofString "num")]
      (.seq
        (.ite (.cmp .notEqual
            (.op .or [.rfield 4 (.var .local (ofString "prod")),
                      .rfield 5 (.var .local (ofString "prod")),
                      .rfield 6 (.var .local (ofString "prod")),
                      .rfield 7 (.var .local (ofString "prod"))])
            (.const (0#64)))
          (.call (some (none, none)) (ofString "trap_with") [.const (3#64)])
          .skip)
        (.dec (ofString "p") u256ShapeHOL
          (.rstruct [.rfield 0 (.var .local (ofString "prod")),
                     .rfield 1 (.var .local (ofString "prod")),
                     .rfield 2 (.var .local (ofString "prod")),
                     .rfield 3 (.var .local (ofString "prod"))])
          taylorExpTail)))

def taylorExpIterCost : Nat := 30 + u256DivClockBound

private theorem progBounded_taylorExpLoopBody :
    ProgBounded taylorExpLoopBody taylorExpIterCost := by
  unfold taylorExpLoopBody taylorExpTail
  apply ProgBounded.weaken
  · apply ProgBounded.seq (ProgBounded.call funBounded_u256_add (some (.local, ofString "out")) _)
    apply ProgBounded.decCall funBounded_u256_mul_full
    apply ProgBounded.seq
    · exact ProgBounded.iteMax _ (ProgBounded.call funBounded_trap_with none _) (ProgBounded.straight _ rfl)
    · apply ProgBounded.dec
      apply ProgBounded.decCall funBounded_u256_from_word
      apply ProgBounded.seq (ProgBounded.call funBounded_u256_mul (some (.local, ofString "di")) _)
      apply ProgBounded.seq (ProgBounded.call funBounded_u256_div (some (.local, ofString "acc")) _)
      apply ProgBounded.seq (ProgBounded.straight _ rfl)
      exact ProgBounded.call funBounded_u256_is_zero (some (.local, ofString "nz")) _
  · change 0 + 1 + (16 + 1 + (max (0 + 1) 0 + (0 + 1 + (7 + 1 + (u256DivClockBound + 1 + (0 + (0 + 1))))))) ≤
      30 + u256DivClockBound
    omega

private theorem taylorExpTail_none {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {wi wden : BitVec 64}
    (hcode : s.code = originalRuntimeCode)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word wi)))
    (hden : s.locals.lookup (ofString "den") = some (u256Val wden 0 0 0))
    (h : evaluateHOLFiniteState s taylorExpTail = (none, post)) :
    ∃ wnz' : BitVec 64,
      post.locals.lookup (ofString "i") = some (.val (.word (wi + 1#64))) ∧
      post.locals.lookup (ofString "nz") = some (.val (.word wnz')) ∧
      (wi = 0#64 → wnz' = 1#64) := by
  unfold taylorExpTail at h
  obtain ⟨vals1, body1, callee1, rs1, wdi, bpost1, s1, inner1, hargs1, hlk1, _, hrun1, _, hl1, hc1, hcont1, hpost_l⟩ :=
    decCall_none h
  have hvals1 : vals1 = [.val (.word wi)] := by
    have hev : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.var .local (ofString "i")] = some [.val (.word wi)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hi]
    exact Option.some.inj (hargs1.symm.trans hev)
  subst hvals1
  rw [hcode] at hlk1
  obtain ⟨rfl, rfl, _⟩ := one_arg_lookup_inv originalRuntimeCode.lookup (ofString "u256_from_word")
    (ofString "w") .one u256ShapeHOL (sourceFnBody Guest.Software.guestFn_u256_from_word)
    (.val (.word wi)) lookup_u256_from_word hlk1
  have hfrom := eval_u256_from_word_body
    (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "w", .val (.word wi)))) wi
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
  have hwdi : wdi = u256Val wi 0 0 0 := by
    rw [hfrom] at hrun1; simp at hrun1; exact hrun1.1.symm
  subst hwdi
  have hs1_code : s1.code = originalRuntimeCode := hc1.trans hcode
  have hs1_di : s1.locals.lookup (ofString "di") = some (u256Val wi 0 0 0) := by
    rw [hl1]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hs1_den : s1.locals.lookup (ofString "den") = some (u256Val wden 0 0 0) := by
    have hne : ofString "di" ≠ ofString "den" := by decide
    rw [hl1]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hne, hden]
  have hs1_i : s1.locals.lookup (ofString "i") = some (.val (.word wi)) := by
    have hne : ofString "di" ≠ ofString "i" := by decide
    rw [hl1]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hne, hi]
  obtain ⟨s2, hc_mul, hcont2⟩ := seq_none hcont1
  obtain ⟨vals2, body2, callee2, rs2, wdi2, bpost2, hargs2, hlk2, _, hrun2, _, hl2, hc2⟩ :=
    call_local_none hc_mul
  have hvals2 : vals2 = [u256Val wi 0 0 0, u256Val wden 0 0 0] := by
    have hev : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
        [.var .local (ofString "di"), .var .local (ofString "den")] =
        some [u256Val wi 0 0 0, u256Val wden 0 0 0] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs1_di, hs1_den]
    exact Option.some.inj (hargs2.symm.trans hev)
  subst hvals2
  rw [hs1_code] at hlk2
  obtain ⟨rfl, rfl, _⟩ := two_arg_lookup_inv originalRuntimeCode.lookup (ofString "u256_mul")
    (ofString "a") (ofString "b") u256ShapeHOL u256ShapeHOL u256ShapeHOL
    (sourceFnBody Guest.Software.guestFn_u256_mul) (u256Val wi 0 0 0) (u256Val wden 0 0 0)
    (by decide) lookup_u256_mul hlk2
  have hs2_code : s2.code = originalRuntimeCode := hc2.trans hs1_code
  have hs2_di : s2.locals.lookup (ofString "di") = some wdi2 := by
    rw [hl2]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hs2_i : s2.locals.lookup (ofString "i") = some (.val (.word wi)) := by
    have hne : ofString "di" ≠ ofString "i" := by decide
    rw [hl2]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hne, hs1_i]
  have hwdi2_zero : wi = 0#64 → wdi2 = u256ZeroVal := by
    intro hwi0
    subst hwi0
    have hne : ofString "b" ≠ ofString "a" := by decide
    exact returned_u256_mul_body_zero_left (wb := wden)
      (by simp [callEntryStateHOLFinite, hs1_code])
      (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, u256ZeroVal])
      (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
      hrun2
  obtain ⟨s3, hc_div, hcont3⟩ := seq_none hcont2
  obtain ⟨vals3, body3, callee3, rs3, wacc, bpost3, hargs3, hlk3, _, hrun3, _, hl3, hc3⟩ :=
    call_local_none hc_div
  have hs3_code : s3.code = originalRuntimeCode := hc3.trans hs2_code
  have hs3_acc : s3.locals.lookup (ofString "acc") = some wacc := by
    rw [hl3]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hs3_i : s3.locals.lookup (ofString "i") = some (.val (.word wi)) := by
    have hne : ofString "acc" ≠ ofString "i" := by decide
    rw [hl3]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hne, hs2_i]
  have hwacc_zero : wi = 0#64 → wacc = u256ZeroVal := by
    intro hwi0
    have hdi0 := hwdi2_zero hwi0
    cases hp : s2.locals.lookup (ofString "p") with
    | none =>
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hp] at hargs3
    | some vp =>
      have hvals3 : vals3 = [vp, wdi2] := by
        have hev : evalListHOLFinite s2 (h := fun a => Classical.propDecidable (s2.memaddrs a))
            [.var .local (ofString "p"), .var .local (ofString "di")] = some [vp, wdi2] := by
          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hp, hs2_di]
        exact Option.some.inj (hargs3.symm.trans hev)
      subst hvals3
      subst hdi0
      rw [hs2_code] at hlk3
      obtain ⟨rfl, rfl, _⟩ := two_arg_lookup_inv originalRuntimeCode.lookup (ofString "u256_div")
        (ofString "a") (ofString "b") u256ShapeHOL u256ShapeHOL u256ShapeHOL
        (sourceFnBody Guest.Software.guestFn_u256_div) vp u256ZeroVal
        (by decide) lookup_u256_div hlk3
      have hne : ofString "b" ≠ ofString "a" := by decide
      exact returned_u256_div_body_zero_right (va := vp)
        (by simp [callEntryStateHOLFinite, hs2_code])
        (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne])
        (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
        hrun3
  obtain ⟨s4, hc_asgn, hc_nz⟩ := seq_none hcont3
  obtain ⟨vi, hevi, hl4, hc4⟩ := assign_local_none hc_asgn
  have hvi : vi = .val (.word (wi + 1#64)) := by
    have hev : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
        (.op .add [.var .local (ofString "i"), .const (1#64)]) = some (.val (.word (wi + 1#64))) := by
      simp [evalHOLExact, evalListHOLExact, hs3_i, valueIsWord, valueWord, wordOpHOL, wordOp]
    exact Option.some.inj (hevi.symm.trans hev)
  subst hvi
  have hs4_code : s4.code = originalRuntimeCode := hc4.trans hs3_code
  have hs4_i : s4.locals.lookup (ofString "i") = some (.val (.word (wi + 1#64))) := by
    rw [hl4]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hs4_acc : s4.locals.lookup (ofString "acc") = some wacc := by
    have hne : ofString "i" ≠ ofString "acc" := by decide
    rw [hl4]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hne, hs3_acc]
  obtain ⟨vals5, body5, callee5, rs5, wnz, bpost5, hargs5, hlk5, _, hrun5, hrs5, hl5, _⟩ :=
    call_local_none hc_nz
  have hvals5 : vals5 = [wacc] := by
    have hev : evalListHOLFinite s4 (h := fun a => Classical.propDecidable (s4.memaddrs a))
        [.var .local (ofString "acc")] = some [wacc] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs4_acc]
    exact Option.some.inj (hargs5.symm.trans hev)
  subst hvals5
  rw [hs4_code] at hlk5
  obtain ⟨rfl, rfl, rfl⟩ := one_arg_lookup_inv originalRuntimeCode.lookup (ofString "u256_is_zero")
    (ofString "a") u256ShapeHOL .one (sourceFnBody Guest.Software.guestFn_u256_is_zero)
    wacc lookup_u256_is_zero hlk5
  obtain ⟨wnz', hwnz'⟩ := shape_one_is_word hrs5
  subst hwnz'
  have hinner_i : inner1.locals.lookup (ofString "i") = some (.val (.word (wi + 1#64))) := by
    have hne : ofString "nz" ≠ ofString "i" := by decide
    rw [hl5]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hne, hs4_i]
  have hinner_nz : inner1.locals.lookup (ofString "nz") = some (.val (.word wnz')) := by
    rw [hl5]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  refine ⟨wnz', ?_, ?_, ?_⟩
  · have hne : ofString "i" ≠ ofString "di" := by decide
    rw [hpost_l, PanRunBounded.resVarEq_lookup, if_neg hne]
    exact hinner_i
  · have hne : ofString "nz" ≠ ofString "di" := by decide
    rw [hpost_l, PanRunBounded.resVarEq_lookup, if_neg hne]
    exact hinner_nz
  · intro hwi0
    have hacc0 := hwacc_zero hwi0
    subst hacc0
    have hisz := eval_u256_is_zero_body_zero
      (callEntryStateHOLFinite s4 (HolFiniteMapExact.empty.update (ofString "a", u256ZeroVal)))
      (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    rw [hisz] at hrun5
    simp at hrun5
    exact hrun5.1.symm

private theorem taylorExpLoopBody_none {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {wi wden : BitVec 64}
    (hcode : s.code = originalRuntimeCode)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word wi)))
    (hden : s.locals.lookup (ofString "den") = some (u256Val wden 0 0 0))
    (h : evaluateHOLFiniteState s taylorExpLoopBody = (none, post)) :
    ∃ wnz' : BitVec 64,
      post.locals.lookup (ofString "den") = some (u256Val wden 0 0 0) ∧
      post.locals.lookup (ofString "i") = some (.val (.word (wi + 1#64))) ∧
      post.locals.lookup (ofString "nz") = some (.val (.word wnz')) ∧
      post.code = s.code ∧
      (wi = 0#64 → wnz' = 1#64) := by
  have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata s taylorExpLoopBody).1
  have havoid_den := evaluate_avoidsLocal_flowing (ofString "den") taylorExpLoopBody (by decide) s
    (by rw [h]; exact Or.inl rfl)
  rw [h] at hmeta havoid_den
  dsimp only at hmeta havoid_den
  have hpost_den : post.locals.lookup (ofString "den") = some (u256Val wden 0 0 0) :=
    havoid_den.trans hden
  unfold taylorExpLoopBody at h
  obtain ⟨s1, hc_add, hcont1⟩ := seq_none h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hl1, hc1⟩ := call_local_none hc_add
  have hs1_code : s1.code = originalRuntimeCode := hc1.trans hcode
  have hs1_i : s1.locals.lookup (ofString "i") = some (.val (.word wi)) := by
    have hne : ofString "out" ≠ ofString "i" := by decide
    rw [hl1]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hne, hi]
  have hs1_den : s1.locals.lookup (ofString "den") = some (u256Val wden 0 0 0) := by
    have hne : ofString "out" ≠ ofString "den" := by decide
    rw [hl1]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hne, hden]
  obtain ⟨_, _, _, _, _, _, s2, inner2, _, _, _, _, _, hl2, hc2, hcont2, hpost_l2⟩ := decCall_none hcont1
  have hs2_code : s2.code = originalRuntimeCode := hc2.trans hs1_code
  have hs2_i : s2.locals.lookup (ofString "i") = some (.val (.word wi)) := by
    have hne : ofString "prod" ≠ ofString "i" := by decide
    rw [hl2]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hne, hs1_i]
  have hs2_den : s2.locals.lookup (ofString "den") = some (u256Val wden 0 0 0) := by
    have hne : ofString "prod" ≠ ofString "den" := by decide
    rw [hl2]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hne, hs1_den]
  obtain ⟨s3, hc_ite, hcont3⟩ := seq_none hcont2
  let iteProg : ProgHOL 64 :=
    .ite (.cmp .notEqual
        (.op .or [.rfield 4 (.var .local (ofString "prod")),
                  .rfield 5 (.var .local (ofString "prod")),
                  .rfield 6 (.var .local (ofString "prod")),
                  .rfield 7 (.var .local (ofString "prod"))])
        (.const (0#64)))
      (.call (some (none, none)) (ofString "trap_with") [.const (3#64)])
      .skip
  have hm3 := (PanRunBounded.evaluateHOLFiniteState_metadata s2 iteProg).1
  have ha3_i := evaluate_avoidsLocal_flowing (ofString "i") iteProg (by decide) s2
    (by rw [hc_ite]; exact Or.inl rfl)
  have ha3_den := evaluate_avoidsLocal_flowing (ofString "den") iteProg (by decide) s2
    (by rw [hc_ite]; exact Or.inl rfl)
  rw [hc_ite] at hm3 ha3_i ha3_den
  dsimp only at hm3 ha3_i ha3_den
  have hs3_code : s3.code = originalRuntimeCode := hm3.trans hs2_code
  have hs3_i : s3.locals.lookup (ofString "i") = some (.val (.word wi)) := ha3_i.trans hs2_i
  have hs3_den : s3.locals.lookup (ofString "den") = some (u256Val wden 0 0 0) := ha3_den.trans hs2_den
  obtain ⟨vp, inner3, _, _, htail, hinner2_l⟩ := dec_none hcont3
  have hs4_code : (setVarHOLFinite (ofString "p") vp s3).code = originalRuntimeCode := hs3_code
  have hs4_i : (setVarHOLFinite (ofString "p") vp s3).locals.lookup (ofString "i") =
      some (.val (.word wi)) := by
    have hne : ofString "p" ≠ ofString "i" := by decide
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hs3_i]
  have hs4_den : (setVarHOLFinite (ofString "p") vp s3).locals.lookup (ofString "den") =
      some (u256Val wden 0 0 0) := by
    have hne : ofString "p" ≠ ofString "den" := by decide
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hs3_den]
  obtain ⟨wnz', hi3, hnz3, hzero3⟩ := taylorExpTail_none hs4_code hs4_i hs4_den htail
  refine ⟨wnz', hpost_den, ?_, ?_, hmeta, hzero3⟩
  · have hne1 : ofString "i" ≠ ofString "prod" := by decide
    have hne2 : ofString "i" ≠ ofString "p" := by decide
    rw [hpost_l2, PanRunBounded.resVarEq_lookup, if_neg hne1,
        hinner2_l, PanRunBounded.resVarEq_lookup, if_neg hne2]
    exact hi3
  · have hne1 : ofString "nz" ≠ ofString "prod" := by decide
    have hne2 : ofString "nz" ≠ ofString "p" := by decide
    rw [hpost_l2, PanRunBounded.resVarEq_lookup, if_neg hne1,
        hinner2_l, PanRunBounded.resVarEq_lookup, if_neg hne2]
    exact hnz3

private def taylorExpRankVal (wi wnz : BitVec 64) : Nat :=
  if wnz ≠ 0#64 then 0
  else if wi = 0#64 then 1
  else 2 ^ 64 - wi.toNat + 1

private def TaylorExpRank {F : Type} (s : PanSemStateFiniteExact 64 F) (n : Nat) : Prop :=
  ∃ wden wi wnz : BitVec 64,
    s.locals.lookup (ofString "den") = some (u256Val wden 0 0 0) ∧
    s.locals.lookup (ofString "i") = some (.val (.word wi)) ∧
    s.locals.lookup (ofString "nz") = some (.val (.word wnz)) ∧
    n = taylorExpRankVal wi wnz

private theorem taylorExpRankVal_step (wi wnz' : BitVec 64)
    (hzero : wi = 0#64 → wnz' = 1#64) :
    taylorExpRankVal (wi + 1#64) wnz' + 1 ≤ taylorExpRankVal wi (0#64) := by
  have h1lt : (1#64).toNat = 1 := rfl
  by_cases hwi0 : wi = 0#64
  · have hnz1 : wnz' = 1#64 := hzero hwi0
    subst hwi0; subst hnz1
    decide
  · have hwi_pos : 0 < wi.toNat := by
      cases Nat.eq_zero_or_pos wi.toNat with
      | inl hz => exact False.elim (hwi0 (BitVec.eq_of_toNat_eq hz))
      | inr hp => exact hp
    have hwi_lt : wi.toNat < 2 ^ 64 := wi.isLt
    unfold taylorExpRankVal
    rw [if_neg (by decide : ¬ (0#64 : BitVec 64) ≠ 0#64), if_neg hwi0]
    by_cases hnz' : wnz' ≠ 0#64
    · rw [if_pos hnz']
      omega
    · rw [if_neg hnz']
      by_cases hwrap : wi + 1#64 = 0#64
      · rw [if_pos hwrap]
        omega
      · rw [if_neg hwrap]
        have hadd : (wi + 1#64).toNat = (wi.toNat + 1) % 2 ^ 64 := by
          simp [BitVec.toNat_add, h1lt]
        have hlt2 : wi.toNat + 1 < 2 ^ 64 := by
          by_contra hge
          have heq : wi.toNat + 1 = 2 ^ 64 := by omega
          apply hwrap
          apply BitVec.eq_of_toNat_eq
          rw [hadd, heq, Nat.mod_self]
          rfl
        rw [hadd, Nat.mod_eq_of_lt hlt2]
        omega

private theorem noTopCont_taylorExpLoopBody : noTopContinue taylorExpLoopBody = true := rfl

private theorem noTopBrk_taylorExpLoopBody : noTopBreak taylorExpLoopBody = true := rfl

set_option maxRecDepth 20000 in
private theorem taylorExpWhile_bounded {F : Type}
    (s : PanSemStateFiniteExact 64 F) (wden wi wnz : BitVec 64)
    (hcode : s.code = originalRuntimeCode)
    (hden : s.locals.lookup (ofString "den") = some (u256Val wden 0 0 0))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word wi)))
    (hnz : s.locals.lookup (ofString "nz") = some (.val (.word wnz)))
    (hwi_pos : wi ≠ 0#64)
    (hbudget : (2 ^ 64) * (taylorExpIterCost + 1) ≤ s.clock) :
    let evaluated := evaluateHOLFiniteState s (.while taylorExpCond taylorExpLoopBody)
    s.clock ≤ evaluated.2.clock + (2 ^ 64) * (taylorExpIterCost + 1) ∧
      evaluated.2.clock ≤ s.clock ∧
      evaluated.1 ≠ some .timeOut := by
  let p64 : Nat := 18446744073709551616
  have hp64 : 2 ^ 64 = p64 := rfl
  let stepCost : Nat := taylorExpIterCost + 1
  have hsc : taylorExpIterCost + 1 = stepCost := rfl
  rw [hp64, hsc] at hbudget ⊢
  have hrank : TaylorExpRank s (taylorExpRankVal wi wnz) :=
    ⟨wden, wi, wnz, hden, hi, hnz, rfl⟩
  have hrle : taylorExpRankVal wi wnz ≤ p64 := by
    unfold taylorExpRankVal
    rw [hp64]
    by_cases hnz_c : wnz ≠ 0#64
    · rw [if_pos hnz_c]; omega
    · rw [if_neg hnz_c, if_neg hwi_pos]
      have hpos : 0 < wi.toNat := by
        cases Nat.eq_zero_or_pos wi.toNat with
        | inl hz => exact False.elim (hwi_pos (BitVec.eq_of_toNat_eq hz))
        | inr hp => exact hp
      omega
  have hmle : taylorExpRankVal wi wnz * stepCost ≤ p64 * stepCost :=
    Nat.mul_le_mul_right _ hrle
  have hrun := rankedWhile_run taylorExpCond taylorExpLoopBody taylorExpIterCost
    TaylorExpRank False
    (by
      intro F' st hR0 w hcond
      obtain ⟨_, wi0, wnz0, _, _, hnz0, hr0⟩ := hR0
      have hnz_ne : wnz0 ≠ 0#64 := by
        unfold taylorExpRankVal at hr0
        rw [hp64] at hr0
        by_cases hz : wnz0 ≠ 0#64
        · exact hz
        · rw [if_neg hz] at hr0
          by_cases hw0 : wi0 = 0#64
          · rw [if_pos hw0] at hr0; omega
          · rw [if_neg hw0] at hr0; omega
      have hcmp : Compiler.Encoders.Asm.wordCmpHOL .equal wnz0 (0#64) = false := by
        cases hc : Compiler.Encoders.Asm.wordCmpHOL .equal wnz0 (0#64)
        · rfl
        · simp [Compiler.Encoders.Asm.wordCmpHOL] at hc
          exact False.elim (hnz_ne hc)
      have hev : evalHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a)) taylorExpCond =
          some (.val (.word (0#64))) := by
        simp [taylorExpCond, evalHOLFinite, evalHOLExact, hnz0, hcmp]
      have hinj := Option.some.inj (hcond.symm.trans hev)
      have hv : HolWordLab.word w = HolWordLab.word (0#64) := ValueHOL.val.inj hinj
      exact HolWordLab.word.inj hv)
    (by
      intro F' st n w hc hRn hcond hw hclk
      obtain ⟨wden1, wi1, wnz1, hden1, hi1, hnz1, hr1⟩ := hRn
      have hwnz0 : wnz1 = 0#64 := by
        by_contra hne0
        have : w = 0#64 := by
          have hcmp : Compiler.Encoders.Asm.wordCmpHOL .equal wnz1 (0#64) = false := by
            cases hc' : Compiler.Encoders.Asm.wordCmpHOL .equal wnz1 (0#64)
            · rfl
            · simp [Compiler.Encoders.Asm.wordCmpHOL] at hc'
              exact False.elim (hne0 hc')
          have hev : evalHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a)) taylorExpCond =
              some (.val (.word (0#64))) := by
            simp [taylorExpCond, evalHOLFinite, evalHOLExact, hnz1, hcmp]
          have hinj := Option.some.inj (hcond.symm.trans hev)
          have hv : HolWordLab.word w = HolWordLab.word (0#64) := ValueHOL.val.inj hinj
          exact HolWordLab.word.inj hv
        exact hw this
      subst hwnz0
      have hbnd := progBounded_taylorExpLoopBody (decClockHOLFinite st) hc
        (by change taylorExpIterCost ≤ st.clock - 1; omega)
      have hnoCont := evaluate_noTopContinue taylorExpLoopBody noTopCont_taylorExpLoopBody (decClockHOLFinite st)
      have hnoBrk := evaluate_noTopBreak taylorExpLoopBody noTopBrk_taylorExpLoopBody (decClockHOLFinite st)
      refine ⟨hbnd.1, hbnd.2.1, hbnd.2.2, ?_, fun hb => False.elim (hnoBrk hb)⟩
      intro hnc
      rcases hnc with hnone | hcont
      · cases hbody : evaluateHOLFiniteState (decClockHOLFinite st) taylorExpLoopBody with
        | mk r post =>
          rw [hbody] at hnone
          dsimp only at hnone
          subst hnone
          obtain ⟨wnz', hden', hi', hnz', hcode', hzero'⟩ :=
            taylorExpLoopBody_none (s := decClockHOLFinite st) hc hi1 hden1 hbody
          have hstep := taylorExpRankVal_step wi1 wnz' hzero'
          refine ⟨taylorExpRankVal (wi1 + 1#64) wnz', by omega, ?_, hcode'⟩
          exact ⟨wden1, wi1 + 1#64, wnz', hden', hi', hnz', rfl⟩
      · exact False.elim (hnoCont hcont))
    (taylorExpRankVal wi wnz) s hcode hrank
    (by rw [hsc]; exact Nat.le_trans hmle hbudget)
  have h1 := hrun.1
  rw [hsc] at h1
  exact ⟨Nat.le_trans h1 (Nat.add_le_add_left hmle _), hrun.2.1, hrun.2.2.1⟩

private theorem decCall_bounded_preserve {F : Type}
    {fn : MlS} {fnCost tailCost : Nat} (hfn : FunBounded fn fnCost)
    (s : PanSemStateFiniteExact 64 F) (name : MlS) (sh : ShapeHOL)
    (args : List (ExpHOL 64)) (cont : ProgHOL 64)
    (hcode : s.code = originalRuntimeCode)
    (hbudget : fnCost + 1 + tailCost ≤ s.clock)
    (htail : ∀ (w : ValueHOL 64) (next : PanSemStateFiniteExact 64 F),
      shapeEqHOL (shapeOfHOLExact w) sh = true →
      next.code = originalRuntimeCode →
      next.locals = s.locals.update (name, w) →
      tailCost ≤ next.clock →
      next.clock ≤ (evaluateHOLFiniteState next cont).2.clock + tailCost ∧
        (evaluateHOLFiniteState next cont).2.clock ≤ next.clock ∧
        (evaluateHOLFiniteState next cont).1 ≠ some .timeOut) :
    let evaluated := evaluateHOLFiniteState s (.decCall name sh fn args cont)
    s.clock ≤ evaluated.2.clock + (fnCost + 1 + tailCost) ∧
      evaluated.2.clock ≤ s.clock ∧
      evaluated.1 ≠ some .timeOut := by
  cases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with
  | none =>
    rw [evaluateHOLFiniteState_decCall_args_none s name sh fn args cont hargs]
    simp
  | some values =>
    cases hlk : lookupCodeHOLFinite s.code.lookup fn values with
    | none =>
      rw [evaluateHOLFiniteState_decCall_lookup_none s name sh fn args cont values hargs hlk]
      simp
    | some installed =>
      obtain ⟨body, callee, rs⟩ := installed
      have bounded := ProgBounded.bodies_of_fun hfn s hcode (by omega) values body callee rs hlk
      change (callEntryStateHOLFinite s callee).clock ≤
          (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).2.clock + fnCost ∧
        (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).2.clock ≤
          (callEntryStateHOLFinite s callee).clock ∧
        (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).1 ≠ some .timeOut at bounded
      have meta' := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body).1
      cases ran : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
      | mk result post =>
        rw [ran] at bounded meta'
        dsimp only at bounded meta'
        obtain ⟨spent, kept, safe⟩ := bounded
        change s.clock - 1 ≤ post.clock + fnCost at spent
        change post.clock ≤ s.clock - 1 at kept
        have postRem : post.clock ≤ s.clock := by omega
        rw [evaluateHOLFiniteState_decCall_total, hargs]
        dsimp only
        rw [hlk]
        dsimp only
        have hnz : s.clock ≠ 0 := by omega
        rw [if_neg hnz, ran]
        have fixed : fixClockHOLFinite (callEntryStateHOLFinite s callee) (result, post) = (result, post) := by
          have hk : ¬ (callEntryStateHOLFinite s callee).clock < post.clock :=
            Nat.not_lt.mpr kept
          simp [fixClockHOLFinite, hk]
        rw [fixed]
        dsimp only
        rcases result with _ | (_ | _ | _ | _ | w | _ | _)
        all_goals first
          | (exact False.elim (safe rfl))
          | (exact ⟨by change s.clock ≤ post.clock + (fnCost + 1 + tailCost); omega, postRem, by simp⟩)
          | skip
        simp only []
        split
        · rename_i hboth
          have hsh : shapeEqHOL (shapeOfHOLExact w) sh = true := by
            simp [Bool.and_eq_true] at hboth; exact hboth.1
          let resumed := setVarHOLFinite name w { post with locals := s.locals }
          have ht := htail w resumed hsh (meta'.trans hcode) rfl (by change tailCost ≤ post.clock; omega)
          change post.clock ≤ (evaluateHOLFiniteState resumed cont).2.clock + tailCost ∧
            (evaluateHOLFiniteState resumed cont).2.clock ≤ post.clock ∧
            (evaluateHOLFiniteState resumed cont).1 ≠ some .timeOut at ht
          change s.clock ≤ (evaluateHOLFiniteState resumed cont).2.clock + (fnCost + 1 + tailCost) ∧
            (evaluateHOLFiniteState resumed cont).2.clock ≤ s.clock ∧
            (evaluateHOLFiniteState resumed cont).1 ≠ some .timeOut
          exact ⟨by omega, by omega, ht.2.2⟩
        · exact ⟨by change s.clock ≤ post.clock + (fnCost + 1 + tailCost); omega, postRem, by simp⟩

private theorem seq_bounded_preserve {F : Type}
    {first tail : ProgHOL 64} {a b : Nat}
    (hfirst : ProgBounded first a) (key : MlS) (havoid : avoidsLocal key first = true)
    (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode)
    (hbudget : a + b ≤ s.clock)
    (htail : ∀ next : PanSemStateFiniteExact 64 F,
      next.code = originalRuntimeCode →
      next.locals.lookup key = s.locals.lookup key →
      b ≤ next.clock →
      next.clock ≤ (evaluateHOLFiniteState next tail).2.clock + b ∧
        (evaluateHOLFiniteState next tail).2.clock ≤ next.clock ∧
        (evaluateHOLFiniteState next tail).1 ≠ some .timeOut) :
    let evaluated := evaluateHOLFiniteState s (.seq first tail)
    s.clock ≤ evaluated.2.clock + (a + b) ∧
      evaluated.2.clock ≤ s.clock ∧
      evaluated.1 ≠ some .timeOut := by
  have fb := hfirst s hcode (by omega)
  have hm := (PanRunBounded.evaluateHOLFiniteState_metadata s first).1
  have ha := evaluate_avoidsLocal_flowing key first havoid s
  rw [evaluateHOLFiniteState_seq_line780]
  cases hrun : evaluateHOLFiniteState s first with
  | mk res next =>
    rw [hrun] at fb hm ha
    dsimp only at fb hm ha ⊢
    cases res with
    | some _ =>
      dsimp only
      exact ⟨by have := fb.1; omega, fb.2.1, fb.2.2⟩
    | none =>
      dsimp only
      have ht := htail next (hm.trans hcode) (ha (Or.inl rfl)) (by have := fb.1; omega)
      exact ⟨by have := fb.1; have := ht.1; omega, Nat.le_trans ht.2.1 fb.2.1, ht.2.2⟩

private theorem dec_bounded_preserve {F : Type}
    (s : PanSemStateFiniteExact 64 F) (name : MlS) (sh : ShapeHOL) (e : ExpHOL 64)
    (body : ProgHOL 64) (v : ValueHOL 64) (cost : Nat)
    (hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e = some v)
    (hsh : shapeEqHOL sh (shapeOfHOLExact v) = true)
    (hcode : s.code = originalRuntimeCode)
    (hbudget : cost ≤ s.clock)
    (hbody : ∀ next : PanSemStateFiniteExact 64 F,
      next.code = originalRuntimeCode →
      next.locals = s.locals.update (name, v) →
      cost ≤ next.clock →
      next.clock ≤ (evaluateHOLFiniteState next body).2.clock + cost ∧
        (evaluateHOLFiniteState next body).2.clock ≤ next.clock ∧
        (evaluateHOLFiniteState next body).1 ≠ some .timeOut) :
    let evaluated := evaluateHOLFiniteState s (.dec name sh e body)
    s.clock ≤ evaluated.2.clock + cost ∧
      evaluated.2.clock ≤ s.clock ∧
      evaluated.1 ≠ some .timeOut := by
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [hev]
  dsimp only
  rw [if_pos hsh]
  exact hbody (setVarHOLFinite name v s) hcode rfl hbudget

private def taylorExpPostLoopProg : ProgHOL 64 :=
  .seq
    (.call (some (some (.local, ofString "out"), none)) (ofString "u256_div")
      [.var .local (ofString "out"), .var .local (ofString "den")])
    (.return (.var .local (ofString "out")))

private def taylorExpP7 : ProgHOL 64 :=
  .decCall (ofString "nz") .one (ofString "u256_is_zero")
    [.var .local (ofString "acc")]
    (.seq (.while taylorExpCond taylorExpLoopBody) taylorExpPostLoopProg)

private def taylorExpP6 : ProgHOL 64 :=
  .dec (ofString "zero") u256ShapeHOL
    (.rstruct [.const (0#64), .const (0#64), .const (0#64), .const (0#64)])
    taylorExpP7

private def taylorExpP5 : ProgHOL 64 :=
  .dec (ofString "i") .one (.const (1#64)) taylorExpP6

private def taylorExpP4 : ProgHOL 64 :=
  .dec (ofString "out") u256ShapeHOL
    (.rstruct [.const (0#64), .const (0#64), .const (0#64), .const (0#64)])
    taylorExpP5

private def taylorExpP3 : ProgHOL 64 :=
  .seq
    (.call (some (some (.local, ofString "acc"), none)) (ofString "u256_mul")
      [.var .local (ofString "acc"), .var .local (ofString "den")])
    taylorExpP4

private def taylorExpP2 : ProgHOL 64 :=
  .decCall (ofString "acc") u256ShapeHOL (ofString "u256_from_word")
    [.var .local (ofString "factor")] taylorExpP3

private def taylorExpRestProg : ProgHOL 64 :=
  .decCall (ofString "num") u256ShapeHOL (ofString "u256_from_word")
    [.var .local (ofString "numerator")] taylorExpP2

private def taylorExpWhileCost : Nat := 18446744073709551616 * (taylorExpIterCost + 1)

private def taylorExpPostCost : Nat := u256DivClockBound + 1

private def taylorExpLoopAndPostCost : Nat := taylorExpWhileCost + taylorExpPostCost

private def taylorExpRestCost : Nat := 11 + taylorExpLoopAndPostCost

def taylorExpClockBound : Nat := 13 + taylorExpLoopAndPostCost

private theorem taylorExpPostLoop_bounded :
    ProgBounded taylorExpPostLoopProg taylorExpPostCost := by
  unfold taylorExpPostLoopProg taylorExpPostCost
  apply ProgBounded.weaken
  · exact ProgBounded.seq
      (ProgBounded.call funBounded_u256_div (some (.local, ofString "out")) _)
      (ProgBounded.straight _ rfl)
  · omega

private theorem taylorExpP4_bounded {F : Type}
    (s4 : PanSemStateFiniteExact 64 F) (wden : BitVec 64)
    (hc4 : s4.code = originalRuntimeCode)
    (hs4_den : s4.locals.lookup (ofString "den") = some (u256Val wden 0 0 0))
    (hclk4 : taylorExpLoopAndPostCost + 1 ≤ s4.clock) :
    let evaluated := evaluateHOLFiniteState s4 taylorExpP4
    s4.clock ≤ evaluated.2.clock + (taylorExpLoopAndPostCost + 1) ∧
      evaluated.2.clock ≤ s4.clock ∧
      evaluated.1 ≠ some .timeOut := by
  have hlk_eq {m : HolFiniteMapExact MlS (ValueHOL 64)} (k : MlS) (v : ValueHOL 64) :
      (m.update (k, v)).lookup k = some v := by
    simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hlk_ne {m : HolFiniteMapExact MlS (ValueHOL 64)} {k1 k2 : MlS} (v : ValueHOL 64) (hne : k1 ≠ k2) :
      (m.update (k1, v)).lookup k2 = m.lookup k2 := by
    simp [HolFiniteMapExact.lookup_update, FUPDATE, hne]
  have hev_z4 : ∀ (st : PanSemStateFiniteExact 64 F),
      @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
        (.rstruct [.const (0#64), .const (0#64), .const (0#64), .const (0#64)]) =
      some u256ZeroVal := fun st => by
    simp [evalHOLExact, evalListHOLExact, u256ZeroVal, u256Val]
  have hsh_z4 : shapeEqHOL u256ShapeHOL (shapeOfHOLExact u256ZeroVal) = true := by
    simp [u256ShapeHOL, u256ZeroVal, u256Val, shapeEqHOL, shapeEqHOL.shapeEqListHOL, shapeOfHOLExact]
  have hsh_1 : shapeEqHOL .one (shapeOfHOLExact (.val (.word (1#64)) : ValueHOL 64)) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  have hwtc : 2 ^ 64 * (taylorExpIterCost + 1) = taylorExpWhileCost := rfl
  refine dec_bounded_preserve s4 (ofString "out") u256ShapeHOL
    (.rstruct [.const (0#64), .const (0#64), .const (0#64), .const (0#64)])
    taylorExpP5 u256ZeroVal (taylorExpLoopAndPostCost + 1)
    (hev_z4 s4) hsh_z4 hc4 hclk4 (fun s5 hc5 hl5 hclk5 => ?_)
  have hs5_den : s5.locals.lookup (ofString "den") = some (u256Val wden 0 0 0) := by
    rw [hl5, hlk_ne _ (by decide)]; exact hs4_den
  refine dec_bounded_preserve s5 (ofString "i") .one (.const (1#64))
    taylorExpP6 (.val (.word (1#64))) (taylorExpLoopAndPostCost + 1)
    (by simp [evalHOLExact]) hsh_1 hc5 hclk5 (fun s6 hc6 hl6 hclk6 => ?_)
  have hs6_den : s6.locals.lookup (ofString "den") = some (u256Val wden 0 0 0) := by
    rw [hl6, hlk_ne _ (by decide)]; exact hs5_den
  have hs6_i : s6.locals.lookup (ofString "i") = some (.val (.word (1#64))) := by
    rw [hl6]; exact hlk_eq _ _
  refine dec_bounded_preserve s6 (ofString "zero") u256ShapeHOL
    (.rstruct [.const (0#64), .const (0#64), .const (0#64), .const (0#64)])
    taylorExpP7 u256ZeroVal (taylorExpLoopAndPostCost + 1)
    (hev_z4 s6) hsh_z4 hc6 hclk6 (fun s7 hc7 hl7 hclk7 => ?_)
  have hs7_den : s7.locals.lookup (ofString "den") = some (u256Val wden 0 0 0) := by
    rw [hl7, hlk_ne _ (by decide)]; exact hs6_den
  have hs7_i : s7.locals.lookup (ofString "i") = some (.val (.word (1#64))) := by
    rw [hl7, hlk_ne _ (by decide)]; exact hs6_i
  have hp7 := decCall_bounded_preserve funBounded_u256_is_zero s7
    (ofString "nz") .one [.var .local (ofString "acc")]
    (.seq (.while taylorExpCond taylorExpLoopBody) taylorExpPostLoopProg)
    (tailCost := taylorExpLoopAndPostCost) hc7 (by omega)
    (fun wnzVal s8 hsh8 hc8 hl8 hclk8 => by
      obtain ⟨wnz, rfl⟩ := shape_one_is_word hsh8
      have hs8_den : s8.locals.lookup (ofString "den") = some (u256Val wden 0 0 0) := by
        rw [hl8, hlk_ne _ (by decide)]; exact hs7_den
      have hs8_i : s8.locals.lookup (ofString "i") = some (.val (.word (1#64))) := by
        rw [hl8, hlk_ne _ (by decide)]; exact hs7_i
      have hs8_nz : s8.locals.lookup (ofString "nz") = some (.val (.word wnz)) := by
        rw [hl8]; exact hlk_eq _ _
      have hwb := taylorExpWhile_bounded s8 wden (1#64) wnz hc8 hs8_den hs8_i hs8_nz
        (by decide) (by rw [hwtc]; unfold taylorExpLoopAndPostCost at hclk8; omega)
      rw [hwtc] at hwb
      exact evaluate_sequence_code_bounded s8
        (.while taylorExpCond taylorExpLoopBody) taylorExpPostLoopProg
        taylorExpWhileCost taylorExpPostCost
        hwb
        (fun next hnc hnb => taylorExpPostLoop_bounded next (hnc.trans hc8) hnb)
        (by unfold taylorExpLoopAndPostCost at hclk8; exact hclk8))
  unfold taylorExpP7
  exact ⟨by have := hp7.1; omega, hp7.2.1, hp7.2.2⟩

private theorem taylorExpRest_bounded {F : Type}
    (s1 : PanSemStateFiniteExact 64 F) (wden : BitVec 64)
    (hs1_code : s1.code = originalRuntimeCode)
    (hs1_den : s1.locals.lookup (ofString "den") = some (u256Val wden 0 0 0))
    (hs1_clk : taylorExpRestCost ≤ s1.clock) :
    let evaluated := evaluateHOLFiniteState s1 taylorExpRestProg
    s1.clock ≤ evaluated.2.clock + taylorExpRestCost ∧
      evaluated.2.clock ≤ s1.clock ∧
      evaluated.1 ≠ some .timeOut := by
  have hlk_ne {m : HolFiniteMapExact MlS (ValueHOL 64)} {k1 k2 : MlS} (v : ValueHOL 64) (hne : k1 ≠ k2) :
      (m.update (k1, v)).lookup k2 = m.lookup k2 := by
    simp [HolFiniteMapExact.lookup_update, FUPDATE, hne]
  have hmul_bnd : ProgBounded
      (.call (some (some (.local, ofString "acc"), none)) (ofString "u256_mul")
        [.var .local (ofString "acc"), .var .local (ofString "den")]) 8 :=
    ProgBounded.call funBounded_u256_mul (some (.local, ofString "acc"))
      [.var .local (ofString "acc"), .var .local (ofString "den")]
  have havoid : avoidsLocal (ofString "den")
      (.call (some (some (.local, ofString "acc"), none)) (ofString "u256_mul")
        [.var .local (ofString "acc"), .var .local (ofString "den")]) = true := rfl
  have hrc : taylorExpRestCost = 0 + 1 + (0 + 1 + (8 + (taylorExpLoopAndPostCost + 1))) := by
    unfold taylorExpRestCost; omega
  have h1 := decCall_bounded_preserve funBounded_u256_from_word s1
    (ofString "num") u256ShapeHOL [.var .local (ofString "numerator")] taylorExpP2
    (tailCost := 0 + 1 + (8 + (taylorExpLoopAndPostCost + 1)))
    hs1_code (by rw [← hrc]; exact hs1_clk)
    (fun _ s2 _ hc2 hl2 hclk2 => by
      have hs2_den : s2.locals.lookup (ofString "den") = some (u256Val wden 0 0 0) := by
        rw [hl2, hlk_ne _ (by decide)]; exact hs1_den
      exact decCall_bounded_preserve funBounded_u256_from_word s2
        (ofString "acc") u256ShapeHOL [.var .local (ofString "factor")] taylorExpP3
        (tailCost := 8 + (taylorExpLoopAndPostCost + 1))
        hc2 hclk2
        (fun _ s3 _ hc3 hl3 hclk3 => by
          have hs3_den : s3.locals.lookup (ofString "den") = some (u256Val wden 0 0 0) := by
            rw [hl3, hlk_ne _ (by decide)]; exact hs2_den
          exact seq_bounded_preserve (tail := taylorExpP4) hmul_bnd (ofString "den") havoid s3 hc3
            (b := taylorExpLoopAndPostCost + 1) hclk3
            (fun s4 hc4 hden4 hclk4 =>
              taylorExpP4_bounded s4 wden hc4 (hden4.trans hs3_den) hclk4)))
  unfold taylorExpRestProg
  exact ⟨by have := h1.1; rw [hrc]; omega, h1.2.1, h1.2.2⟩

private theorem taylorExpBody_eq :
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
      (extractFn Guest.Software.guestFn_taylor_exponential).body =
    .decCall (ofString "den") u256ShapeHOL (ofString "u256_from_word")
      [.var .local (ofString "denominator")] taylorExpRestProg := rfl

theorem funBounded_taylor_exponential :
    FunBounded (ofString "taylor_exponential") taylorExpClockBound := by
  refine funBounded_of_guestAst 232 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_taylor_exponential taylorExpClockBound rfl ?_
  rw [taylorExpBody_eq]
  intro F state hcode hbudget
  have htcb : taylorExpClockBound = taylorExpRestCost + 2 := by
    unfold taylorExpClockBound taylorExpRestCost
    omega
  rw [htcb] at hbudget
  cases hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "denominator")] with
  | none =>
    rw [evaluateHOLFiniteState_decCall_args_none state _ _ _ _ _ hargs]
    simp
  | some vals =>
    cases hlk : lookupCodeHOLFinite state.code.lookup (ofString "u256_from_word") vals with
    | none =>
      rw [evaluateHOLFiniteState_decCall_lookup_none state _ _ _ _ _ vals hargs hlk]
      simp
    | some installed =>
      obtain ⟨fbody, callee, rs⟩ := installed
      have hvals_len : ∃ v0, vals = [v0] := by
        cases h0 : state.locals.lookup (ofString "denominator") with
        | none => simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, h0] at hargs
        | some v0 =>
          have hev : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
              [.var .local (ofString "denominator")] = some [v0] := by
            simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, h0]
          exact ⟨v0, Option.some.inj (hargs.symm.trans hev)⟩
      obtain ⟨v0, rfl⟩ := hvals_len
      have hlk' : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "u256_from_word") [v0] =
          some (fbody, callee, rs) := by rwa [← hcode]
      obtain ⟨hsh0, rfl, hcallee, rfl⟩ := one_arg_lookup_inv_shape originalRuntimeCode.lookup
        (ofString "u256_from_word") (ofString "w") .one u256ShapeHOL
        (sourceFnBody Guest.Software.guestFn_u256_from_word) v0 lookup_u256_from_word hlk'
      have hsh0' : shapeEqHOL (shapeOfHOLExact v0) .one = true := by
        cases v0 with
        | val wl => cases wl with | word _ => simp [shapeOfHOLExact, shapeEqHOL]
        | rStruct _ => simp [shapeOfHOLExact, shapeEqHOL] at hsh0
        | nStruct _ _ => simp [shapeOfHOLExact, shapeEqHOL] at hsh0
      obtain ⟨wden, rfl⟩ := shape_one_is_word hsh0'
      have hfrom := eval_u256_from_word_body (callEntryStateHOLFinite state callee) wden
        (by rw [hcallee]; simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
      have hnz_clk : state.clock ≠ 0 := by omega
      have h1_clk : state.clock ≤ (emptyLocalsHOLFinite (callEntryStateHOLFinite state callee)).clock + 1 := by
        change state.clock ≤ (state.clock - 1) + 1; omega
      have hwhole := evaluate_decCall_continuation_bounded state
        (emptyLocalsHOLFinite (callEntryStateHOLFinite state callee))
        (ofString "den") (ofString "u256_from_word") u256ShapeHOL u256ShapeHOL
        [.var .local (ofString "denominator")] [.val (.word wden)]
        (sourceFnBody Guest.Software.guestFn_u256_from_word) taylorExpRestProg callee
        (some (.returned (u256Val wden 0 0 0))) 1 taylorExpRestCost
        hargs hlk hnz_clk hfrom (le_refl _) h1_clk
        (fun h => by cases h)
        (fun val hval => by
          have hv : val = u256Val wden 0 0 0 := (PanSemResultExact.returned.inj (Option.some.inj hval)).symm
          subst hv
          let s1 := setVarHOLFinite (ofString "den") (u256Val wden 0 0 0)
            { emptyLocalsHOLFinite (callEntryStateHOLFinite state callee) with locals := state.locals }
          have hs1_clk : taylorExpRestCost ≤ s1.clock := by
            change taylorExpRestCost ≤ state.clock - 1; omega
          have hs1_den : s1.locals.lookup (ofString "den") = some (u256Val wden 0 0 0) := by
            simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          exact taylorExpRest_bounded s1 wden hcode hs1_den hs1_clk)
      exact ⟨by have := hwhole.1; omega, hwhole.2.1, hwhole.2.2⟩

end InitECandidate.Solver.GuestBoundCryptoDiv
