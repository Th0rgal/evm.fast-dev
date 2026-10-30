import InitECandidate.Solver.PanRunBoundedExt

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace InitECandidate.Solver.GuestBoundEvmInterpreter

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.PanRunBoundedExt

private theorem progBounded_seq_straight (first : ProgHOL 64) {tail : ProgHOL 64} {cost : Nat}
    (hs : extStraightLine first = true) (ht : ProgBounded tail cost) :
    ProgBounded (.seq first tail) cost := by
  simpa using ProgBounded.seq (ProgBounded.straight first hs) ht

private theorem countedBody_seq_straight {counter : MlS} {step : BitVec 64}
    (first : ProgHOL 64) {tail : ProgHOL 64} {cost : Nat}
    (hs : extStraightLine first = true)
    (ha : avoidsLocal counter first = true)
    (hn : noTopContinue first = true)
    (hrest : CountedBody counter step tail cost) :
    CountedBody counter step (.seq first tail) cost := by
  simpa using CountedBody.seq first (ProgBounded.straight first hs) ha hn hrest

private theorem evalListHOLFinite_two_word2 {F : Type}
    (state : PanSemStateFiniteExact 64 F) (e1 e2 : ExpHOL 64) (K : BitVec 64)
    {vs : List (ValueHOL 64)}
    (hargs : evalListHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a)) [e1, e2] = some vs)
    (hk : evalHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a)) e2 = some (.val (.word K))) :
    ∃ v1, vs = [v1, .val (.word K)] := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  rw [evalHOLFinite_eq_toExact] at hk
  simp only [evalListHOLExact] at hargs
  rw [hk] at hargs
  rcases h1 : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) e1 with _ | v1
  · rw [h1] at hargs
    cases hargs
  · rw [h1] at hargs
    cases hargs
    exact ⟨v1, rfl⟩

private theorem evalListHOLFinite_three_word2 {F : Type}
    (state : PanSemStateFiniteExact 64 F) (e1 e2 e3 : ExpHOL 64) (K : BitVec 64)
    {vs : List (ValueHOL 64)}
    (hargs : evalListHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a)) [e1, e2, e3] = some vs)
    (hk : evalHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a)) e2 = some (.val (.word K))) :
    ∃ v1 v3, vs = [v1, .val (.word K), v3] := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  rw [evalHOLFinite_eq_toExact] at hk
  simp only [evalListHOLExact] at hargs
  rw [hk] at hargs
  rcases h1 : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) e1 with _ | v1
  · rw [h1] at hargs
    cases hargs
  · rw [h1] at hargs
    rcases h3 : @evalHOLExact 64 F _ state.toExact
        (fun a => Classical.propDecidable (state.memaddrs a)) e3 with _ | v3
    · rw [h3] at hargs
      cases hargs
    · rw [h3] at hargs
      cases hargs
      exact ⟨v1, v3, rfl⟩

private theorem evalListHOLFinite_three_word3 {F : Type}
    (state : PanSemStateFiniteExact 64 F) (e1 e2 e3 : ExpHOL 64) (K : BitVec 64)
    {vs : List (ValueHOL 64)}
    (hargs : evalListHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a)) [e1, e2, e3] = some vs)
    (hk : evalHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a)) e3 = some (.val (.word K))) :
    ∃ v1 v2, vs = [v1, v2, .val (.word K)] := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  rw [evalHOLFinite_eq_toExact] at hk
  simp only [evalListHOLExact] at hargs
  rw [hk] at hargs
  rcases h1 : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) e1 with _ | v1
  · rw [h1] at hargs
    cases hargs
  · rw [h1] at hargs
    rcases h2 : @evalHOLExact 64 F _ state.toExact
        (fun a => Classical.propDecidable (state.memaddrs a)) e2 with _ | v2
    · rw [h2] at hargs
      cases hargs
    · rw [h2] at hargs
      cases hargs
      exact ⟨v1, v2, rfl⟩

private theorem two_arg_lookup_second
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (fn p1 p2 : MlS) (body : ProgHOL 64) (rsShape : ShapeHOL) (hp : p1 ≠ p2)
    (hlookup_fn : code fn = some ([(p1, .one), (p2, .one)], body, rsShape))
    {v1 : ValueHOL 64} {K : BitVec 64}
    {foundBody : ProgHOL 64} {locals : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hfound : PanSemStateFiniteExact.lookupCodeHOLFinite code fn [v1, .val (.word K)] =
      some (foundBody, locals, rs)) :
    foundBody = body ∧ locals.lookup p2 = some (.val (.word K)) := by
  have hbody := lookupCodeHOLFinite_installed_body code fn _ body foundBody rsShape rs
    [v1, .val (.word K)] locals hlookup_fn hfound
  refine ⟨hbody, ?_⟩
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
  split at hfound
  · cases hfound
  · rename_i exactBody exactLocals exactShape raw
    cases v1 with
    | rStruct _ =>
      simp [lookupCodeHOLExact, hlookup_fn, shapeOfHOLExact, shapeEqHOL] at raw
    | nStruct _ _ =>
      simp [lookupCodeHOLExact, hlookup_fn, shapeOfHOLExact, shapeEqHOL] at raw
    | val wl =>
      cases wl with
      | word w1 =>
        have hraw : lookupCodeHOLExact code fn [.val (.word w1), .val (.word K)] =
            some (body,
              (fun key =>
                if key = p2 then some (.val (.word K))
                else if key = p1 then some (.val (.word w1))
                else none),
              rsShape) := by
          simp [lookupCodeHOLExact, hlookup_fn, shapeOfHOLExact, shapeEqHOL, hp]
        have heq := Option.some.inj (raw.symm.trans hraw)
        have hloc : exactLocals =
            (fun key =>
              if key = p2 then some (.val (.word K))
              else if key = p1 then some (.val (.word w1))
              else none) := (Prod.mk.inj (Prod.mk.inj heq).2).1
        have hfin := Option.some.inj hfound
        have hfl : locals.lookup = exactLocals := by
          rw [← (Prod.mk.inj (Prod.mk.inj hfin).2).1]
          rfl
        rw [hfl, hloc]
        simp

private theorem three_arg_lookup_mid
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (fn p1 p2 p3 : MlS) (body : ProgHOL 64)
    (hp12 : p1 ≠ p2) (hp13 : p1 ≠ p3) (hp23 : p2 ≠ p3)
    (hlookup_fn : code fn = some ([(p1, .one), (p2, .one), (p3, .one)], body, .one))
    {v1 v3 : ValueHOL 64} {K : BitVec 64}
    {foundBody : ProgHOL 64} {locals : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hfound : PanSemStateFiniteExact.lookupCodeHOLFinite code fn [v1, .val (.word K), v3] =
      some (foundBody, locals, rs)) :
    foundBody = body ∧ locals.lookup p2 = some (.val (.word K)) := by
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
          rw [pan_three_word_lookup code fn p1 p2 p3 body w1 K w3 hp12 hp13 hp23 hlookup_fn]
            at hfound
          cases hfound
          simp [HolFiniteMapExact.lookup_update, FUPDATE, hp23, Ne.symm hp23]

private theorem three_arg_lookup_third
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (fn p1 p2 p3 : MlS) (body : ProgHOL 64)
    (hp12 : p1 ≠ p2) (hp13 : p1 ≠ p3) (hp23 : p2 ≠ p3)
    (hlookup_fn : code fn = some ([(p1, .one), (p2, .one), (p3, .one)], body, .one))
    {v1 v2 : ValueHOL 64} {K : BitVec 64}
    {foundBody : ProgHOL 64} {locals : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hfound : PanSemStateFiniteExact.lookupCodeHOLFinite code fn [v1, v2, .val (.word K)] =
      some (foundBody, locals, rs)) :
    foundBody = body ∧ locals.lookup p3 = some (.val (.word K)) := by
  have hbody := lookupCodeHOLFinite_installed_body code fn _ body foundBody .one rs
    [v1, v2, .val (.word K)] locals hlookup_fn hfound
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
      cases v2 with
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
      | val wl2 =>
        cases wl2 with
        | word w2 =>
          rw [pan_three_word_lookup code fn p1 p2 p3 body w1 w2 K hp12 hp13 hp23 hlookup_fn]
            at hfound
          cases hfound
          simp [HolFiniteMapExact.lookup_update, FUPDATE]

inductive DecBody (counter : MlS) : ProgHOL 64 → Nat → Prop
  | decr : DecBody counter (.assign .local counter (.op .sub [.var .local counter, .const 1])) 0
  | decrThen {tail : ProgHOL 64} {b : Nat} (bounded : ProgBounded tail b)
      (avoid : avoidsLocal counter tail = true) (noCont : noTopContinue tail = true) :
      DecBody counter
        (.seq (.assign .local counter (.op .sub [.var .local counter, .const 1])) tail) b
  | seq (first : ProgHOL 64) {tail : ProgHOL 64} {a b : Nat} (bounded : ProgBounded first a)
      (avoid : avoidsLocal counter first = true) (noCont : noTopContinue first = true)
      (rest : DecBody counter tail b) : DecBody counter (.seq first tail) (a + b)
  | dec (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL 64) {body : ProgHOL 64} {cost : Nat}
      (distinct : counter ≠ name) (rest : DecBody counter body cost) :
      DecBody counter (.dec name shape initializer body) cost

private theorem decBody_run {counter : MlS} {body : ProgHOL 64} {cost : Nat}
    (counted : DecBody counter body cost) {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode) (w : BitVec 64)
    (atCounter : state.locals.lookup counter = some (.val (.word w)))
    (budget : cost ≤ state.clock) :
    state.clock ≤ (evaluateHOLFiniteState state body).2.clock + cost ∧
      (evaluateHOLFiniteState state body).2.clock ≤ state.clock ∧
      (evaluateHOLFiniteState state body).1 ≠ some .timeOut ∧
      (evaluateHOLFiniteState state body).1 ≠ some .continue ∧
      ((evaluateHOLFiniteState state body).1 = none →
        (evaluateHOLFiniteState state body).2.locals.lookup counter = some (.val (.word (w - 1))) ∧
        (evaluateHOLFiniteState state body).2.code = state.code) := by
  induction counted generalizing state with
  | decr =>
    have run : evaluateHOLFiniteState state
        (.assign .local counter (.op .sub [.var .local counter, .const 1])) =
        (none, setVarHOLFinite counter (.val (.word (w - 1))) state) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, atCounter,
        wordOpHOL, wordOp, valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact,
        setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
    rw [run]
    refine ⟨by simp [setVarHOLFinite], by simp [setVarHOLFinite], by simp, by simp, ?_⟩
    intro _
    refine ⟨?_, rfl⟩
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  | decrThen bounded avoid noCont =>
    rename_i tail b
    have run : evaluateHOLFiniteState state
        (.assign .local counter (.op .sub [.var .local counter, .const 1])) =
        (none, setVarHOLFinite counter (.val (.word (w - 1))) state) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, atCounter,
        wordOpHOL, wordOp, valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact,
        setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
    let entered := setVarHOLFinite counter (.val (.word (w - 1))) state
    have atNext : entered.locals.lookup counter = some (.val (.word (w - 1))) := by
      simp [entered, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have tailBound := bounded entered code budget
    have frame := evaluate_avoidsLocal_flowing counter tail avoid entered
    have noContinue := evaluate_noTopContinue tail noCont entered
    have meta' := PanRunBounded.evaluateHOLFiniteState_metadata entered tail
    rw [evaluateHOLFiniteState_seq_line780, run]
    dsimp only
    cases tailRun : evaluateHOLFiniteState entered tail with
    | mk result middle =>
      rw [tailRun] at tailBound frame noContinue meta'
      dsimp only at tailBound frame noContinue meta'
      obtain ⟨spent, kept, safe⟩ := tailBound
      change state.clock ≤ middle.clock + b at spent
      change middle.clock ≤ state.clock at kept
      refine ⟨spent, kept, safe, noContinue, fun normal => ?_⟩
      have kept' := frame (Or.inl normal)
      exact ⟨kept'.trans atNext, meta'.1⟩
  | seq first bounded avoid noCont rest ih =>
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
        obtain ⟨t1, t2, t3, t4, t5⟩ :=
          ih middle (meta'.1.trans code) (by rw [kept']; exact atCounter) (by omega)
        refine ⟨by omega, by omega, t3, t4, fun normal => ?_⟩
        obtain ⟨i1, i2⟩ := t5 normal
        exact ⟨i1, i2.trans meta'.1⟩
      | some r =>
        dsimp only
        exact ⟨by omega, by omega, safe, noContinue, fun h => by simp at h⟩
  | dec name shape initializer distinct rest ih =>
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · exact ⟨Nat.le_add_right _ _, le_refl _, by simp, by simp, by simp⟩
    · rename_i val _
      split
      · let inner := setVarHOLFinite name val state
        have atInner : inner.locals.lookup counter = some (.val (.word w)) := by
          simp [inner, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            Ne.symm distinct, atCounter]
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

private theorem eval_zero_lt_condition {F : Type} (state : PanSemStateFiniteExact 64 F)
    (counter : MlS) (op : Cmp) (hop : op = .less ∨ op = .lower) (w : BitVec 64)
    (signed : op = .less → w.toNat < 2 ^ 63)
    (atCounter : state.locals.lookup counter = some (.val (.word w))) :
    evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      (.cmp op (.const 0) (.var .local counter)) =
      some (.val (.word (if 0 < w.toNat then 1 else 0))) := by
  rw [evalHOLFinite_eq_toExact]
  rcases hop with rfl | rfl
  · have small := signed rfl
    simp only [evalHOLExact, atCounter, Compiler.Encoders.Asm.wordCmpHOL,
      holAsmSignedLess_small 0 w (by decide) small]
    by_cases lt : 0 < w.toNat <;> simp [lt]
  · simp only [evalHOLExact, atCounter, Compiler.Encoders.Asm.wordCmpHOL]
    by_cases lt : 0 < w.toNat <;> simp [lt, BitVec.lt_def]

theorem downWhile_run (counter : MlS) (op : Cmp) (hop : op = .less ∨ op = .lower)
    {body : ProgHOL 64} {cost : Nat} (counted : DecBody counter body cost) :
    ∀ n : Nat, (op = .less → n < 2 ^ 63) →
      ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.code = originalRuntimeCode →
      ∀ w : BitVec 64, state.locals.lookup counter = some (.val (.word w)) →
      w.toNat ≤ n → n * (cost + 1) ≤ state.clock →
      state.clock ≤ (evaluateHOLFiniteState state
        (.while (.cmp op (.const 0) (.var .local counter)) body)).2.clock + n * (cost + 1) ∧
        (evaluateHOLFiniteState state
          (.while (.cmp op (.const 0) (.var .local counter)) body)).2.clock ≤ state.clock ∧
        (evaluateHOLFiniteState state
          (.while (.cmp op (.const 0) (.var .local counter)) body)).1 ≠ some .timeOut := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hnsigned F state code w atCounter within budget
    have condition := eval_zero_lt_condition state counter op hop w
      (fun h => by have := hnsigned h; omega) atCounter
    rw [evaluateHOLFiniteState_while_total, condition]
    by_cases lt : 0 < w.toNat
    · rw [if_pos lt]
      simp only [show (1 : BitVec 64) ≠ 0 by decide, if_true, ne_eq, not_false_eq_true]
      have positiveRank : 0 < n := by omega
      have oneIteration : cost + 1 ≤ n * (cost + 1) := Nat.le_mul_of_pos_left _ positiveRank
      have clock : state.clock ≠ 0 := by omega
      rw [if_neg clock, fixClockHOLFinite_evaluateState]
      have decCode : (decClockHOLFinite state).code = originalRuntimeCode := code
      have stepRun := decBody_run counted (decClockHOLFinite state) decCode w atCounter
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
            rw [BitVec.le_def, one_toNat]
            omega
          have natural : (w - 1).toNat = w.toNat - 1 := by
            rw [BitVec.toNat_sub_of_le hle, one_toNat]
          have spent' : state.clock ≤ middle.clock + cost + 1 := Nat.sub_le_iff_le_add.mp spent
          have hmul : (n - 1) * (cost + 1) + (cost + 1) = n * (cost + 1) := by
            have hsucc : n - 1 + 1 = n := by omega
            calc
              (n - 1) * (cost + 1) + (cost + 1) = (n - 1 + 1) * (cost + 1) := by
                rw [Nat.add_mul, Nat.one_mul]
              _ = n * (cost + 1) := by rw [hsucc]
          have tail := ih (n - 1) (by omega)
            (fun h => by have := hnsigned h; omega)
            middle (nextCode.trans code) (w - 1) nextCounter
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

private theorem countedDownDec (counter : MlS) (op : Cmp) (hop : op = .less ∨ op = .lower)
    (K : BitVec 64) (hnsigned : op = .less → K.toNat < 2 ^ 63)
    {body tail : ProgHOL 64} {cost tailCost : Nat} (counted : DecBody counter body cost)
    (rest : ProgBounded tail tailCost) :
    ProgBounded (.dec counter .one (.const K)
      (.seq (.while (.cmp op (.const 0) (.var .local counter)) body) tail))
      (K.toNat * (cost + 1) + tailCost) := by
  intro F state code budget
  rw [evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true]
  let entered := setVarHOLFinite counter (.val (.word K)) state
  have atCounter : entered.locals.lookup counter = some (.val (.word K)) := by
    simp [entered, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have loop := downWhile_run counter op hop counted K.toNat hnsigned entered code K atCounter
    (le_refl _) (by change K.toNat * (cost + 1) ≤ state.clock; omega)
  have meta' := PanRunBounded.evaluateHOLFiniteState_metadata entered
    (.while (.cmp op (.const 0) (.var .local counter)) body)
  change state.clock ≤ (evaluateHOLFiniteState entered _).2.clock + _ ∧
    (evaluateHOLFiniteState entered _).2.clock ≤ state.clock ∧
    (evaluateHOLFiniteState entered _).1 ≠ some .timeOut
  rw [evaluateHOLFiniteState_seq_line780]
  cases loopRun : evaluateHOLFiniteState entered
      (.while (.cmp op (.const 0) (.var .local counter)) body) with
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

private theorem lookup_udivmod :
    originalRuntimeCode.lookup (ofString "udivmod") =
      some ([(ofString "a", .one), (ofString "b", .one)],
        sourceFnBody Guest.Software.guestFn_udivmod, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 33 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_udivmod) rfl

private theorem funBounded_udivmod : FunBounded (ofString "udivmod") 65 := by
  refine funBounded_of_guestAst 33 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_udivmod 65 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_udivmod,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine ProgBounded.weaken
    (ProgBounded.seq
      (ProgBounded.iteMax _ (ProgBounded.call funBounded_trap_with none [.const 2])
        (ProgBounded.straight _ rfl))
      (progBounded_seq_straight _ rfl
        (ProgBounded.dec _ _ _
          (ProgBounded.dec _ _ _
            (countedDownDec (ofString "i") .less (Or.inl rfl) 64#64 (by decide)
              (DecBody.decrThen (ProgBounded.straight _ rfl) rfl rfl)
              (ProgBounded.straight _ rfl))))))
    ?_
  have h64 : (64#64).toNat = 64 := rfl
  rw [h64]
  omega

private theorem funBounded_udiv : FunBounded (ofString "udiv") 66 :=
  funBounded_of_guestAst 34 (by rw [guestAst_len]; decide) Guest.Software.guestFn_udiv 66 rfl
    (ProgBounded.decCall funBounded_udivmod _ _ _ (ProgBounded.straight _ rfl))

private theorem funBounded_umod : FunBounded (ofString "umod") 66 :=
  funBounded_of_guestAst 35 (by rw [guestAst_len]; decide) Guest.Software.guestFn_umod 66 rfl
    (ProgBounded.decCall funBounded_udivmod _ _ _ (ProgBounded.straight _ rfl))

private theorem funBounded_udiv_small5 : FunBounded (ofString "udiv_small5") 67 :=
  funBounded_of_guestAst 874 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_udiv_small5 67 rfl
    (ProgBounded.decCall funBounded_udiv _ _ _ (ProgBounded.straight _ rfl))

private theorem funBounded_min : FunBounded (ofString "min") 0 :=
  funBounded_of_guestAst 31 (by rw [guestAst_len]; decide) Guest.Software.guestFn_min 0 rfl
    (ProgBounded.straight _ rfl)

private theorem funBounded_max : FunBounded (ofString "max") 0 :=
  funBounded_of_guestAst 32 (by rw [guestAst_len]; decide) Guest.Software.guestFn_max 0 rfl
    (ProgBounded.straight _ rfl)

private theorem funBounded_u256_ws_init : FunBounded (ofString "u256_ws_init") 2 := by
  refine funBounded_of_guestAst 38 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_ws_init 2 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_u256_ws_init,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.seq
      (ProgBounded.iteMax _ (ProgBounded.alloc _ _) (ProgBounded.straight _ rfl))
      (ProgBounded.straight _ rfl))
    (by omega)

private theorem funBounded_u256_from_word : FunBounded (ofString "u256_from_word") 0 :=
  funBounded_of_guestAst 39 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_from_word 0 rfl (ProgBounded.straight _ rfl)

private theorem funBounded_u256_low : FunBounded (ofString "u256_low") 0 :=
  funBounded_of_guestAst 40 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_low 0 rfl (ProgBounded.straight _ rfl)

private theorem funBounded_u256_fits_word : FunBounded (ofString "u256_fits_word") 0 :=
  funBounded_of_guestAst 41 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_fits_word 0 rfl (ProgBounded.straight _ rfl)

private theorem funBounded_u256_is_zero : FunBounded (ofString "u256_is_zero") 0 :=
  funBounded_of_guestAst 42 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_is_zero 0 rfl (ProgBounded.straight _ rfl)

private theorem funBounded_u256_limb : FunBounded (ofString "u256_limb") 0 :=
  funBounded_of_guestAst 43 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_limb 0 rfl (ProgBounded.straight _ rfl)

private theorem funBounded_u256_bit : FunBounded (ofString "u256_bit") 1 :=
  funBounded_of_guestAst 44 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_bit 1 rfl
    (progBounded_seq_straight _ rfl
      (ProgBounded.decCall funBounded_u256_limb _ _ _ (ProgBounded.straight _ rfl)))

private theorem funBounded_u256_eq : FunBounded (ofString "u256_eq") 0 :=
  funBounded_of_guestAst 45 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_eq 0 rfl (ProgBounded.straight _ rfl)

private theorem funBounded_u256_lt : FunBounded (ofString "u256_lt") 0 :=
  funBounded_of_guestAst 46 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_lt 0 rfl (ProgBounded.straight _ rfl)

private theorem funBounded_u256_gt : FunBounded (ofString "u256_gt") 1 :=
  funBounded_of_guestAst 47 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_gt 1 rfl
    (ProgBounded.tail funBounded_u256_lt _)

private theorem funBounded_u256_slt : FunBounded (ofString "u256_slt") 0 :=
  funBounded_of_guestAst 48 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_slt 0 rfl (ProgBounded.straight _ rfl)

private theorem funBounded_u256_sgt : FunBounded (ofString "u256_sgt") 1 :=
  funBounded_of_guestAst 49 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_sgt 1 rfl
    (ProgBounded.tail funBounded_u256_slt _)

private theorem funBounded_u256_cmp : FunBounded (ofString "u256_cmp") 2 :=
  funBounded_of_guestAst 50 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_cmp 2 rfl
    (ProgBounded.decCall funBounded_u256_lt _ _ _
      (progBounded_seq_straight _ rfl
        (ProgBounded.decCall funBounded_u256_eq _ _ _ (ProgBounded.straight _ rfl))))

private theorem funBounded_u256_not : FunBounded (ofString "u256_not") 0 :=
  funBounded_of_guestAst 51 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_not 0 rfl (ProgBounded.straight _ rfl)

private theorem funBounded_u256_and : FunBounded (ofString "u256_and") 0 :=
  funBounded_of_guestAst 52 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_and 0 rfl (ProgBounded.straight _ rfl)

private theorem funBounded_u256_or : FunBounded (ofString "u256_or") 0 :=
  funBounded_of_guestAst 53 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_or 0 rfl (ProgBounded.straight _ rfl)

private theorem funBounded_u256_xor : FunBounded (ofString "u256_xor") 0 :=
  funBounded_of_guestAst 54 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_xor 0 rfl (ProgBounded.straight _ rfl)

private theorem funBounded_u256_add_carry : FunBounded (ofString "u256_add_carry") 0 :=
  funBounded_of_guestAst 55 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_add_carry 0 rfl (ProgBounded.straight _ rfl)

private theorem funBounded_u256_add : FunBounded (ofString "u256_add") 0 :=
  funBounded_of_guestAst 56 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_add 0 rfl (ProgBounded.straight _ rfl)

private theorem funBounded_u256_sub : FunBounded (ofString "u256_sub") 0 :=
  funBounded_of_guestAst 57 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_sub 0 rfl (ProgBounded.straight _ rfl)

private theorem funBounded_u256_neg : FunBounded (ofString "u256_neg") 0 :=
  funBounded_of_guestAst 58 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_neg 0 rfl (ProgBounded.straight _ rfl)

private theorem funBounded_mul64x64 : FunBounded (ofString "mul64x64") 0 :=
  funBounded_of_guestAst 59 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_mul64x64 0 rfl (ProgBounded.straight _ rfl)

private theorem funBounded_u256_mul : FunBounded (ofString "u256_mul") 7 := by
  refine funBounded_of_guestAst 60 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_mul 7 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_u256_mul,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.seq
      (ProgBounded.iteMax _
        (ProgBounded.decCall funBounded_mul64x64 _ _ _ (ProgBounded.straight _ rfl))
        (ProgBounded.straight _ rfl))
      (ProgBounded.decCall funBounded_mul64x64 _ _ _
        (ProgBounded.decCall funBounded_mul64x64 _ _ _
          (ProgBounded.decCall funBounded_mul64x64 _ _ _
            (ProgBounded.decCall funBounded_mul64x64 _ _ _
              (ProgBounded.decCall funBounded_mul64x64 _ _ _
                (ProgBounded.decCall funBounded_mul64x64 _ _ _
                  (ProgBounded.straight _ rfl))))))))
    (by omega)

private theorem funBounded_u256_mul_full : FunBounded (ofString "u256_mul_full") 16 := by
  refine funBounded_of_guestAst 61 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_mul_full 16 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_u256_mul_full,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  iterate 16 refine ProgBounded.decCall funBounded_mul64x64 _ _ _ ?_
  exact ProgBounded.straight _ rfl

private theorem funBounded_u256_abs : FunBounded (ofString "u256_abs") 1 :=
  funBounded_of_guestAst 72 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_abs 1 rfl
    (ProgBounded.weaken
      (ProgBounded.seq
        (ProgBounded.iteMax _ (ProgBounded.tail funBounded_u256_neg _) (ProgBounded.straight _ rfl))
        (ProgBounded.straight _ rfl))
      (by omega))

private theorem funBounded_bit_length64 : FunBounded (ofString "bit_length64") 0 :=
  funBounded_of_guestAst 77 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_bit_length64 0 rfl (ProgBounded.straight _ rfl)

private theorem funBounded_u256_bit_length : FunBounded (ofString "u256_bit_length") 4 := by
  refine funBounded_of_guestAst 78 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_bit_length 4 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_u256_bit_length,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.seq
      (ProgBounded.iteMax _
        (ProgBounded.decCall funBounded_bit_length64 _ _ _ (ProgBounded.straight _ rfl))
        (ProgBounded.straight _ rfl))
      (ProgBounded.seq
        (ProgBounded.iteMax _
          (ProgBounded.decCall funBounded_bit_length64 _ _ _ (ProgBounded.straight _ rfl))
          (ProgBounded.straight _ rfl))
        (ProgBounded.seq
          (ProgBounded.iteMax _
            (ProgBounded.decCall funBounded_bit_length64 _ _ _ (ProgBounded.straight _ rfl))
            (ProgBounded.straight _ rfl))
          (ProgBounded.tail funBounded_bit_length64 _))))
    (by omega)

private theorem funBounded_u256_byte_length : FunBounded (ofString "u256_byte_length") 5 :=
  funBounded_of_guestAst 79 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_byte_length 5 rfl
    (ProgBounded.decCall funBounded_u256_bit_length _ _ _ (ProgBounded.straight _ rfl))

private theorem funBounded_u256_shl : FunBounded (ofString "u256_shl") 0 :=
  funBounded_of_guestAst 81 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_shl 0 rfl (ProgBounded.straight _ rfl)

private theorem funBounded_u256_shr : FunBounded (ofString "u256_shr") 0 :=
  funBounded_of_guestAst 82 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_shr 0 rfl (ProgBounded.straight _ rfl)

private theorem funBounded_u256_sar : FunBounded (ofString "u256_sar") 3 := by
  refine funBounded_of_guestAst 83 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_sar 3 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_u256_sar,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.dec _ _ _
    (progBounded_seq_straight _ rfl
      (ProgBounded.decCall funBounded_u256_shr _ _ _
        (ProgBounded.weaken
          (ProgBounded.seq
            (ProgBounded.iteMax _
              (ProgBounded.iteMax _
                (ProgBounded.decCall funBounded_u256_shl _ _ _
                  (ProgBounded.call funBounded_u256_or _ _))
                (ProgBounded.straight _ rfl))
              (ProgBounded.straight _ rfl))
            (ProgBounded.straight _ rfl))
          (by omega))))

private theorem funBounded_u256_signextend : FunBounded (ofString "u256_signextend") 5 := by
  refine funBounded_of_guestAst 84 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_signextend 5 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_u256_signextend,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact progBounded_seq_straight _ rfl
    (ProgBounded.dec _ _ _
      (ProgBounded.decCall funBounded_u256_bit _ _ _
        (ProgBounded.decCall funBounded_u256_shl _ _ _
          (ProgBounded.weaken
            (ProgBounded.seq
              (ProgBounded.iteMax _
                (ProgBounded.tail funBounded_u256_or _)
                (ProgBounded.straight _ rfl))
              (ProgBounded.decCall funBounded_u256_not _ _ _
                (ProgBounded.tail funBounded_u256_and _)))
            (by omega)))))

private theorem funBounded_u256_byte : FunBounded (ofString "u256_byte") 1 :=
  funBounded_of_guestAst 85 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_byte 1 rfl
    (progBounded_seq_straight _ rfl
      (ProgBounded.dec _ _ _
        (ProgBounded.decCall funBounded_u256_limb _ _ _ (ProgBounded.straight _ rfl))))

private theorem funBounded_u256_to_be32 : FunBounded (ofString "u256_to_be32") 8 := by
  refine funBounded_of_guestAst 87 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_to_be32 8 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_u256_to_be32,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.seq
      (ProgBounded.iteMax _
        (ProgBounded.decCall funBounded_bswap64 _ _ _
          (progBounded_seq_straight _ rfl
            (ProgBounded.seq (ProgBounded.call funBounded_bswap64 _ _)
              (progBounded_seq_straight _ rfl
                (ProgBounded.seq (ProgBounded.call funBounded_bswap64 _ _)
                  (progBounded_seq_straight _ rfl
                    (ProgBounded.seq (ProgBounded.call funBounded_bswap64 _ _)
                      (ProgBounded.straight _ rfl))))))))
        (ProgBounded.straight _ rfl))
      (ProgBounded.seq (ProgBounded.call funBounded_st_be64 _ _)
        (ProgBounded.seq (ProgBounded.call funBounded_st_be64 _ _)
          (ProgBounded.seq (ProgBounded.call funBounded_st_be64 _ _)
            (ProgBounded.seq (ProgBounded.call funBounded_st_be64 _ _)
              (ProgBounded.straight _ rfl))))))
    (by omega)

private theorem funBounded_htab_new : FunBounded (ofString "htab_new") 8 := by
  refine funBounded_of_guestAst 128 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_htab_new 8 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_htab_new,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine ProgBounded.decCall funBounded_alloc _ _ _ ?_
  apply ProgBounded.dec
  apply ProgBounded.dec
  refine progBounded_seq_straight _ rfl
    (progBounded_seq_straight _ rfl
      (progBounded_seq_straight _ rfl
        (progBounded_seq_straight _ rfl
          (progBounded_seq_straight _ rfl ?_))))
  refine ProgBounded.decCall funBounded_alloc _ _ _ (progBounded_seq_straight _ rfl ?_)
  refine ProgBounded.decCall funBounded_alloc _ _ _ (progBounded_seq_straight _ rfl ?_)
  refine ProgBounded.decCall funBounded_alloc _ _ _ (ProgBounded.straight _ rfl)

private theorem funBounded_htab_new_scratch : FunBounded (ofString "htab_new_scratch") 8 := by
  refine funBounded_of_guestAst 129 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_htab_new_scratch 8 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_htab_new_scratch,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine ProgBounded.decCall funBounded_scratch_alloc _ _ _ ?_
  apply ProgBounded.dec
  apply ProgBounded.dec
  refine progBounded_seq_straight _ rfl
    (progBounded_seq_straight _ rfl
      (progBounded_seq_straight _ rfl
        (progBounded_seq_straight _ rfl
          (progBounded_seq_straight _ rfl ?_))))
  refine ProgBounded.decCall funBounded_scratch_alloc _ _ _ (progBounded_seq_straight _ rfl ?_)
  refine ProgBounded.decCall funBounded_scratch_alloc _ _ _ (progBounded_seq_straight _ rfl ?_)
  refine ProgBounded.decCall funBounded_scratch_alloc _ _ _ (ProgBounded.straight _ rfl)

private theorem funBounded_htab_count : FunBounded (ofString "htab_count") 0 :=
  funBounded_of_guestAst 141 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_htab_count 0 rfl (ProgBounded.straight _ rfl)

private theorem funBounded_htab_item : FunBounded (ofString "htab_item") 0 :=
  funBounded_of_guestAst 143 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_htab_item 0 rfl (ProgBounded.straight _ rfl)

private theorem funBounded_tx_has_access_list : FunBounded (ofString "tx_has_access_list") 0 :=
  funBounded_of_guestAst 315 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_tx_has_access_list 0 rfl (ProgBounded.straight _ rfl)

private theorem funBounded_calculate_total_blob_gas :
    FunBounded (ofString "calculate_total_blob_gas") 0 :=
  funBounded_of_guestAst 317 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_calculate_total_blob_gas 0 rfl (ProgBounded.straight _ rfl)

private theorem funBounded_tx_chain_id : FunBounded (ofString "tx_chain_id") 4 := by
  refine funBounded_of_guestAst 338 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_tx_chain_id 4 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_tx_chain_id,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact progBounded_seq_straight _ rfl
    (ProgBounded.dec _ _ _
      (ProgBounded.decCall funBounded_u256_fits_word _ _ _
        (progBounded_seq_straight _ rfl
          (ProgBounded.decCall funBounded_u256_sub _ _ _
            (ProgBounded.decCall funBounded_u256_shr _ _ _
              (ProgBounded.seq (ProgBounded.call funBounded_u256_fits_word _ _)
                (ProgBounded.straight _ rfl)))))))

private theorem funBounded_state_fresh_tx : FunBounded (ofString "state_fresh_tx") 74 := by
  refine funBounded_of_guestAst 355 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_state_fresh_tx 74 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_state_fresh_tx,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine ProgBounded.weaken
    (ProgBounded.seq (ProgBounded.alloc _ _)
      (progBounded_seq_straight _ rfl
        (ProgBounded.decCall funBounded_htab_new _ _ _
          (progBounded_seq_straight _ rfl
            (ProgBounded.seq (ProgBounded.call funBounded_htab_new _ _)
              (progBounded_seq_straight _ rfl
                (ProgBounded.seq (ProgBounded.call funBounded_htab_new _ _)
                  (progBounded_seq_straight _ rfl
                    (ProgBounded.seq (ProgBounded.call funBounded_htab_new _ _)
                      (progBounded_seq_straight _ rfl
                        (ProgBounded.seq (ProgBounded.call funBounded_htab_new _ _)
                          (progBounded_seq_straight _ rfl
                            (ProgBounded.seq (ProgBounded.call funBounded_htab_new _ _)
                              (progBounded_seq_straight _ rfl
                                (ProgBounded.seq (ProgBounded.call funBounded_htab_new _ _)
                                  (progBounded_seq_straight _ rfl
                                    (ProgBounded.seq (ProgBounded.call funBounded_htab_new _ _)
                                      (ProgBounded.straight _ rfl))))))))))))))))))
    (by omega)

private theorem funBounded_sk_make : FunBounded (ofString "sk_make") 22 := by
  refine funBounded_of_guestAst 360 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_sk_make 22 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_sk_make,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine ProgBounded.weaken
    (ProgBounded.seq (progBounded_memcpy_const _ _ _ 20#64 (by decide))
      (ProgBounded.seq (progBounded_memcpy_const _ _ _ 32#64 (by decide))
        (ProgBounded.straight _ rfl)))
    ?_
  have h20 : (20#64).toNat = 20 := rfl
  have h32 : (32#64).toNat = 32 := rfl
  rw [h20, h32]
  omega

private theorem funBounded_acct_is_empty : FunBounded (ofString "acct_is_empty") 14 := by
  refine funBounded_of_guestAst 384 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_acct_is_empty 14 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_acct_is_empty,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine ProgBounded.weaken
    (progBounded_seq_straight _ rfl
      (progBounded_memeq_decCall_const _ _ _ _ 32#64 (by decide)
        (progBounded_seq_straight _ rfl
          (ProgBounded.decCall funBounded_u256_is_zero _ _ _ (ProgBounded.straight _ rfl)))))
    ?_
  have h32 : (32#64).toNat = 32 := rfl
  rw [h32]
  omega

private theorem funBounded_track_ancestor_access :
    FunBounded (ofString "track_ancestor_access") 0 :=
  funBounded_of_guestAst 402 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_track_ancestor_access 0 rfl (ProgBounded.straight _ rfl)

private theorem funBounded_lst_new : FunBounded (ofString "lst_new") 4 := by
  refine funBounded_of_guestAst 408 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_lst_new 4 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_lst_new,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.decCall funBounded_alloc _ _ _
    (ProgBounded.decCall funBounded_alloc _ _ _ (ProgBounded.straight _ rfl))

private theorem funBounded_lst_new_scratch : FunBounded (ofString "lst_new_scratch") 4 := by
  refine funBounded_of_guestAst 409 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_lst_new_scratch 4 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_lst_new_scratch,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.decCall funBounded_scratch_alloc _ _ _
    (ProgBounded.decCall funBounded_scratch_alloc _ _ _ (ProgBounded.straight _ rfl))

private theorem funBounded_precompile_index : FunBounded (ofString "precompile_index") 20 := by
  refine funBounded_of_guestAst 822 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_precompile_index 20 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_precompile_index,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine ProgBounded.weaken
    (progBounded_is_zero_bytes_decCall_const _ _ _ 18#64 (ProgBounded.straight _ rfl))
    ?_
  have h18 : (18#64).toNat = 18 := rfl
  rw [h18]
  omega

private theorem funBounded_tx_is_blob : FunBounded (ofString "tx_is_blob") 0 :=
  funBounded_of_guestAst 865 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_tx_is_blob 0 rfl (ProgBounded.straight _ rfl)

private theorem funBounded_tx_is_setcode : FunBounded (ofString "tx_is_setcode") 0 :=
  funBounded_of_guestAst 866 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_tx_is_setcode 0 rfl (ProgBounded.straight _ rfl)

private theorem funBounded_fee_mul : FunBounded (ofString "fee_mul") 17 := by
  refine funBounded_of_guestAst 867 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_fee_mul 17 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_fee_mul,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.decCall funBounded_u256_mul_full _ _ _ (ProgBounded.straight _ rfl)

private theorem funBounded_keccak_f1600 : FunBounded (ofString "keccak_f1600") 24 := by
  refine funBounded_of_guestAst 101 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_keccak_f1600 24 rfl ?_
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

private theorem funBounded_keccak_absorb_block :
    FunBounded (ofString "keccak_absorb_block") 161 := by
  refine funBounded_of_guestAst 102 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_keccak_absorb_block 161 rfl ?_
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
    exact countedWhile_from (ofString "i") .less (Or.inl rfl) 136 8 (by decide) (by decide)
      (cost := 0) (countedBody_seq_straight _ (by decide) (by decide) (by decide) CountedBody.incr)
      s0 hs0_code 0 hs0_i (by decide) (by change 136 * (0 + 1) ≤ state.clock; omega)
  · unfold RunBounded
    exact countedWhile_from (ofString "i") .less (Or.inl rfl) 136 8 (by decide) (by decide)
      (cost := 0) (countedBody_seq_straight _ (by decide) (by decide) (by decide) CountedBody.incr)
      s0 hs0_code 0 hs0_i (by decide) (by change 136 * (0 + 1) ≤ state.clock; omega)

private theorem lookup_keccak256 :
    originalRuntimeCode.lookup (ofString "keccak256") =
      some ([(ofString "p", .one), (ofString "n", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_keccak256, .one) :=
  lookup_of_guestAst_getElem 103 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_keccak256) rfl

private theorem runBounded_keccak256_small_body {F : Type}
    (state : PanSemStateFiniteExact 64 F) (K : BitVec 64)
    (hlt : K.toNat < 136)
    (hcode : state.code = originalRuntimeCode)
    (atN : state.locals.lookup (ofString "n") = some (.val (.word K)))
    (hbudget : K.toNat / 8 + 240 ≤ state.clock) :
    RunBounded state (sourceFnBody Guest.Software.guestFn_keccak256) (K.toNat / 8 + 240) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_keccak256,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply RunBounded.dec
  intro stpVal _
  let s1 := setVarHOLFinite (ofString "stp") stpVal state
  have hs1_clk : s1.clock = state.clock := rfl
  have hs1_code : s1.code = originalRuntimeCode := hcode
  have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word K)) := by
    have hne : ofString "stp" ≠ ofString "n" := by decide
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, atN]
  have hmz200 : ProgBounded
      (.call (some (none, none)) (ofString "memzero")
        [.var .local (ofString "stp"), .const 200#64]) 33 :=
    ProgBounded.weaken
      (progBounded_memzero_const none (.var .local (ofString "stp")) 200#64 (by decide))
      (by decide)
  have hmz200_run := hmz200 s1 hs1_code (by rw [hs1_clk]; omega)
  have hmz200_fn := evaluate_avoidsLocal_flowing (ofString "n")
    (.call (some (none, none)) (ofString "memzero")
      [.var .local (ofString "stp"), .const 200#64]) rfl s1
  have hmz200_meta := PanRunBounded.evaluateHOLFiniteState_metadata s1
    (.call (some (none, none)) (ofString "memzero")
      [.var .local (ofString "stp"), .const 200#64])
  change RunBounded s1 _ (K.toNat / 8 + 240)
  unfold RunBounded
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hrun1 : evaluateHOLFiniteState s1
      (.call (some (none, none)) (ofString "memzero")
        [.var .local (ofString "stp"), .const 200#64]) with ⟨r1, s2⟩
  rw [hrun1] at hmz200_run hmz200_fn hmz200_meta
  dsimp only at hmz200_run hmz200_fn hmz200_meta ⊢
  cases r1 with
  | some r =>
    dsimp only
    exact ⟨by omega, hmz200_run.2.1, hmz200_run.2.2⟩
  | none =>
    dsimp only
    have hs2_code : s2.code = originalRuntimeCode := hmz200_meta.1.trans hs1_code
    have hs2_n : s2.locals.lookup (ofString "n") = some (.val (.word K)) :=
      (hmz200_fn (Or.inl rfl)).trans hs1_n
    rw [evaluateHOLFiniteState_dec_total]
    simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true]
    let s3 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) s2
    have hs3_clk : s3.clock = s2.clock := rfl
    have hs3_code : s3.code = originalRuntimeCode := hs2_code
    have hs3_i : s3.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
      simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hs3_n : s3.locals.lookup (ofString "n") = some (.val (.word K)) := by
      have hne : ofString "i" ≠ ofString "n" := by decide
      simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hs2_n]
    change s1.clock ≤ (evaluateHOLFiniteState s3 _).2.clock + (K.toNat / 8 + 240) ∧
      (evaluateHOLFiniteState s3 _).2.clock ≤ s1.clock ∧
      (evaluateHOLFiniteState s3 _).1 ≠ some .timeOut
    rw [evaluateHOLFiniteState_seq_line780]
    have hwhile_exit :
        evaluateHOLFiniteState s3
          (.while (.cmp .notLower (.var .local (ofString "n"))
              (.op .add [.var .local (ofString "i"), .const 136#64]))
            (.seq
              (.call (some (none, none)) (ofString "keccak_absorb_block")
                [.var .local (ofString "stp"),
                 .op .add [.var .local (ofString "p"), .var .local (ofString "i")]])
              (.assign .local (ofString "i")
                (.op .add [.var .local (ofString "i"), .const 136#64])))) =
        (none, s3) := by
      rw [evaluateHOLFiniteState_while_total]
      have hcond : evalHOLFinite s3 (h := fun a => Classical.propDecidable (s3.memaddrs a))
          (.cmp .notLower (.var .local (ofString "n"))
            (.op .add [.var .local (ofString "i"), .const 136#64])) =
          some (.val (.word 0)) := by
        rw [evalHOLFinite_eq_toExact]
        have hlt_bv : K < 136#64 := by
          rw [BitVec.lt_def]
          exact hlt
        simp [evalHOLExact, evalListHOLExact, hs3_n, hs3_i, wordOpHOL, wordOp,
          valueIsWord, valueWord, Compiler.Encoders.Asm.wordCmpHOL, hlt_bv]
      rw [hcond]
      simp
    rw [hwhile_exit]
    dsimp only
    have hrem_eval : @evalHOLExact 64 F _ s3.toExact
        (fun a => Classical.propDecidable (s3.memaddrs a))
        (.op .sub [.var .local (ofString "n"), .var .local (ofString "i")]) =
        some (.val (.word K)) := by
      simp [evalHOLExact, evalListHOLExact, hs3_n, hs3_i, wordOpHOL, wordOp,
        valueIsWord, valueWord]
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    rw [hrem_eval]
    simp only [shapeOfHOLExact, shapeEqHOL, if_true]
    let s4 := setVarHOLFinite (ofString "rem") (.val (.word K)) s3
    have hs4_clk : s4.clock = s3.clock := rfl
    have hs4_code : s4.code = originalRuntimeCode := hs3_code
    have hs4_rem : s4.locals.lookup (ofString "rem") = some (.val (.word K)) := by
      simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    change s1.clock ≤ (evaluateHOLFiniteState s4 _).2.clock + (K.toNat / 8 + 240) ∧
      (evaluateHOLFiniteState s4 _).2.clock ≤ s1.clock ∧
      (evaluateHOLFiniteState s4 _).1 ≠ some .timeOut
    have hmz136 : ProgBounded
        (.call (some (none, none)) (ofString "memzero")
          [.var .global (ofString "keccak_pad"), .const 136#64]) 25 :=
      ProgBounded.weaken
        (progBounded_memzero_const none (.var .global (ofString "keccak_pad")) 136#64 (by decide))
        (by decide)
    have hmz136_run := hmz136 s4 hs4_code (by omega)
    have hmz136_frem := evaluate_avoidsLocal_flowing (ofString "rem")
      (.call (some (none, none)) (ofString "memzero")
        [.var .global (ofString "keccak_pad"), .const 136#64]) rfl s4
    have hmz136_meta := PanRunBounded.evaluateHOLFiniteState_metadata s4
      (.call (some (none, none)) (ofString "memzero")
        [.var .global (ofString "keccak_pad"), .const 136#64])
    rw [evaluateHOLFiniteState_seq_line780]
    rcases hrun2 : evaluateHOLFiniteState s4
        (.call (some (none, none)) (ofString "memzero")
          [.var .global (ofString "keccak_pad"), .const 136#64]) with ⟨r2, s5⟩
    rw [hrun2] at hmz136_run hmz136_frem hmz136_meta
    dsimp only at hmz136_run hmz136_frem hmz136_meta ⊢
    cases r2 with
    | some r =>
      dsimp only
      exact ⟨by omega, by omega, hmz136_run.2.2⟩
    | none =>
      dsimp only
      have hs5_code : s5.code = originalRuntimeCode := hmz136_meta.1.trans hs4_code
      have hs5_rem : s5.locals.lookup (ofString "rem") = some (.val (.word K)) :=
        (hmz136_frem (Or.inl rfl)).trans hs4_rem
      rw [evaluateHOLFiniteState_seq_line780]
      have heq_mc :
          evaluateHOLFiniteState s5
            (.call (some (none, none)) (ofString "memcpy")
              [.var .global (ofString "keccak_pad"),
               .op .add [.var .local (ofString "p"), .var .local (ofString "i")],
               .var .local (ofString "rem")]) =
          evaluateHOLFiniteState s5
            (.call (some (none, none)) (ofString "memcpy")
              [.var .global (ofString "keccak_pad"),
               .op .add [.var .local (ofString "p"), .var .local (ofString "i")],
               .const K]) := by
        have hargs_eq :
            evalListHOLFinite s5 (h := fun a => Classical.propDecidable (s5.memaddrs a))
              [.var .global (ofString "keccak_pad"),
               .op .add [.var .local (ofString "p"), .var .local (ofString "i")],
               .var .local (ofString "rem")] =
            evalListHOLFinite s5 (h := fun a => Classical.propDecidable (s5.memaddrs a))
              [.var .global (ofString "keccak_pad"),
               .op .add [.var .local (ofString "p"), .var .local (ofString "i")],
               .const K] := by
          simp only [evalListHOLFinite_eq_toExact, evalListHOLExact]
          have hrem_k : @evalHOLExact 64 F _ s5.toExact
              (fun a => Classical.propDecidable (s5.memaddrs a))
              (.var .local (ofString "rem")) =
              @evalHOLExact 64 F _ s5.toExact
                (fun a => Classical.propDecidable (s5.memaddrs a)) (.const K) := by
            simp [evalHOLExact, hs5_rem]
          rw [hrem_k]
        rw [evaluateHOLFiniteState_call, evaluateHOLFiniteState_call, hargs_eq]
      have hmc_rem : RunBounded s5
          (.call (some (none, none)) (ofString "memcpy")
            [.var .global (ofString "keccak_pad"),
             .op .add [.var .local (ofString "p"), .var .local (ofString "i")],
             .var .local (ofString "rem")])
          (K.toNat / 8 + 8) := by
        unfold RunBounded
        rw [heq_mc]
        exact progBounded_memcpy_const none
          (.var .global (ofString "keccak_pad"))
          (.op .add [.var .local (ofString "p"), .var .local (ofString "i")])
          K (by omega) s5 hs5_code (by omega)
      have hmc_meta := PanRunBounded.evaluateHOLFiniteState_metadata s5
        (.call (some (none, none)) (ofString "memcpy")
          [.var .global (ofString "keccak_pad"),
           .op .add [.var .local (ofString "p"), .var .local (ofString "i")],
           .var .local (ofString "rem")])
      unfold RunBounded at hmc_rem
      rcases hrun3 : evaluateHOLFiniteState s5
          (.call (some (none, none)) (ofString "memcpy")
            [.var .global (ofString "keccak_pad"),
             .op .add [.var .local (ofString "p"), .var .local (ofString "i")],
             .var .local (ofString "rem")]) with ⟨r3, s6⟩
      rw [hrun3] at hmc_rem hmc_meta
      dsimp only at hmc_rem hmc_meta ⊢
      cases r3 with
      | some r =>
        dsimp only
        exact ⟨by omega, by omega, hmc_rem.2.2⟩
      | none =>
        dsimp only
        have hs6_code : s6.code = originalRuntimeCode := hmc_meta.1.trans hs5_code
        have htail : ProgBounded
            (.seq
              (.storeByte
                (.op .add [.var .global (ofString "keccak_pad"), .var .local (ofString "rem")])
                (.const 1#64))
              (.seq
                (.storeByte (.op .add [.var .global (ofString "keccak_pad"), .const 135#64])
                  (.op .or
                    [.loadByte (.op .add [.var .global (ofString "keccak_pad"), .const 135#64]),
                     .const 128#64]))
                (.seq
                  (.call (some (none, none)) (ofString "keccak_absorb_block")
                    [.var .local (ofString "stp"), .var .global (ofString "keccak_pad")])
                  (.seq
                    (.ite
                      (.cmp .equal (.op .and [.var .local (ofString "out"), .const 7#64])
                        (.const 0#64))
                      (.seq
                        (.store (.var .local (ofString "out"))
                          (.load .one (.var .local (ofString "stp"))))
                        (.seq
                          (.store (.op .add [.var .local (ofString "out"), .const 8#64])
                            (.load .one (.op .add [.var .local (ofString "stp"), .const 8#64])))
                          (.seq
                            (.store (.op .add [.var .local (ofString "out"), .const 16#64])
                              (.load .one (.op .add [.var .local (ofString "stp"), .const 16#64])))
                            (.store (.op .add [.var .local (ofString "out"), .const 24#64])
                              (.load .one
                                (.op .add [.var .local (ofString "stp"), .const 24#64]))))))
                      (.call (some (none, none)) (ofString "memcpy")
                        [.var .local (ofString "out"), .var .local (ofString "stp"), .const 32#64]))
                    (.return (.const 0#64))))))
            174 := by
          refine progBounded_seq_straight _ rfl (progBounded_seq_straight _ rfl ?_)
          refine ProgBounded.weaken
            (ProgBounded.seq (ProgBounded.call funBounded_keccak_absorb_block _ _)
              (ProgBounded.seq
                (ProgBounded.iteMax _ (ProgBounded.straight _ rfl)
                  (progBounded_memcpy_const _ _ _ 32#64 (by decide)))
                (ProgBounded.straight _ rfl)))
            ?_
          have h32 : (32#64).toNat = 32 := rfl
          rw [h32]
          omega
        have ht := htail s6 hs6_code (by omega)
        exact ⟨by omega, by omega, ht.2.2⟩

private theorem runBounded_keccak256_small_exp {F : Type}
    (destination : Option (VarKind × MlS)) (p nExp out : ExpHOL 64)
    (state : PanSemStateFiniteExact 64 F) (K : BitVec 64) (hlt : K.toNat < 136)
    (hcode : state.code = originalRuntimeCode)
    (hn : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) nExp =
      some (.val (.word K)))
    (hbudget : K.toNat / 8 + 241 ≤ state.clock) :
    RunBounded state (.call (some (destination, none)) (ofString "keccak256") [p, nExp, out])
      (K.toNat / 8 + 241) := by
  cases hargs : evalListHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a)) [p, nExp, out] with
  | none =>
    unfold RunBounded
    rw [evaluateHOLFiniteState_call, hargs]
    simp
  | some vs =>
    obtain ⟨v1, v3, rfl⟩ := evalListHOLFinite_three_word2 state p nExp out K hargs hn
    exact RunBounded.call hargs hbudget (fun body locals rs hfound => by
      rw [hcode] at hfound
      obtain ⟨rfl, hnLoc⟩ := three_arg_lookup_mid originalRuntimeCode.lookup
        (ofString "keccak256") (ofString "p") (ofString "n") (ofString "out")
        (sourceFnBody Guest.Software.guestFn_keccak256)
        (by decide) (by decide) (by decide) lookup_keccak256 hfound
      exact runBounded_keccak256_small_body (callEntryStateHOLFinite state locals) K hlt hcode hnLoc
        (by change K.toNat / 8 + 240 ≤ state.clock - 1; omega))

private theorem progBounded_keccak256_small_const
    (destination : Option (VarKind × MlS)) (p out : ExpHOL 64)
    (K : BitVec 64) (hlt : K.toNat < 136) :
    ProgBounded (.call (some (destination, none)) (ofString "keccak256") [p, .const K, out])
      (K.toNat / 8 + 241) := by
  intro F state hcode hbudget
  exact runBounded_keccak256_small_exp destination p (.const K) out state K hlt hcode
    (by rw [evalHOLFinite_eq_toExact]; rfl) hbudget

private theorem lookup_u256_from_be :
    originalRuntimeCode.lookup (ofString "u256_from_be") =
      some ([(ofString "p", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_u256_from_be, .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 86 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_from_be) rfl

private theorem runBounded_u256_from_be_body {F : Type}
    (state : PanSemStateFiniteExact 64 F) (K : BitVec 64)
    (hcode : state.code = originalRuntimeCode)
    (atN : state.locals.lookup (ofString "n") = some (.val (.word K)))
    (hbudget : K.toNat + 4 ≤ state.clock) :
    RunBounded state (sourceFnBody Guest.Software.guestFn_u256_from_be) (K.toNat + 4) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_u256_from_be,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  have hfast : ProgBounded
      (.ite
        (.op .and
          [.cmp .equal (.var .local (ofString "n")) (.const 32#64),
           .cmp .equal (.op .and [.var .local (ofString "p"), .const 7#64]) (.const 0#64)])
        (.dec (ofString "w") .one (.load .one (.var .local (ofString "p")))
          (.decCall (ofString "l3") .one (ofString "bswap64") [.var .local (ofString "w")]
            (.seq
              (.assign .local (ofString "w")
                (.load .one (.op .add [.var .local (ofString "p"), .const 8#64])))
              (.decCall (ofString "l2") .one (ofString "bswap64") [.var .local (ofString "w")]
                (.seq
                  (.assign .local (ofString "w")
                    (.load .one (.op .add [.var .local (ofString "p"), .const 16#64])))
                  (.decCall (ofString "l1") .one (ofString "bswap64") [.var .local (ofString "w")]
                    (.seq
                      (.assign .local (ofString "w")
                        (.load .one (.op .add [.var .local (ofString "p"), .const 24#64])))
                      (.decCall (ofString "l0") .one (ofString "bswap64")
                        [.var .local (ofString "w")]
                        (.return
                          (.rStruct
                            [.var .local (ofString "l0"), .var .local (ofString "l1"),
                             .var .local (ofString "l2"), .var .local (ofString "l3")]))))))))))
        .skip) 4 :=
    ProgBounded.weaken
      (ProgBounded.iteMax _
        (ProgBounded.dec _ _ _
          (ProgBounded.decCall funBounded_bswap64 _ _ _
            (progBounded_seq_straight _ rfl
              (ProgBounded.decCall funBounded_bswap64 _ _ _
                (progBounded_seq_straight _ rfl
                  (ProgBounded.decCall funBounded_bswap64 _ _ _
                    (progBounded_seq_straight _ rfl
                      (ProgBounded.decCall funBounded_bswap64 _ _ _
                        (ProgBounded.straight _ rfl)))))))))
        (ProgBounded.straight _ rfl))
      (by omega)
  rw [Nat.add_comm K.toNat 4]
  refine RunBounded.seq (state := state) (a := 4) (b := K.toNat)
    (hfast state hcode (by omega)) (by omega) ?_
  intro next result nextCode nextBudget
  have hkeep : next.locals.lookup (ofString "n") = some (.val (.word K)) := by
    have hf := evaluate_avoidsLocal_flowing (ofString "n") _ rfl state
      (by rw [result]; exact Or.inl rfl)
    rw [result] at hf
    exact hf.trans atN
  iterate 5 apply RunBounded.decConst
  let s0 := setVarHOLFinite (ofString "i") (.val (.word 0))
    (setVarHOLFinite (ofString "l3") (.val (.word 0))
      (setVarHOLFinite (ofString "l2") (.val (.word 0))
        (setVarHOLFinite (ofString "l1") (.val (.word 0))
          (setVarHOLFinite (ofString "l0") (.val (.word 0)) next))))
  have hs0_code : s0.code = originalRuntimeCode := nextCode.trans hcode
  have hs0_i : s0.locals.lookup (ofString "i") = some (.val (.word 0)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs0_n : s0.locals.lookup (ofString "n") = some (.val (.word K)) := by
    simp only [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hkeep]
    repeat rw [if_neg (by decide)]
  have hbody : CountedBody (ofString "i") 1 _ 0 :=
    CountedBody.dec _ _ _ (by decide)
      (CountedBody.dec _ _ _ (by decide)
        (CountedBody.dec _ _ _ (by decide)
          (countedBody_seq_straight _ rfl rfl rfl
            (countedBody_seq_straight _ rfl rfl rfl
              (countedBody_seq_straight _ rfl rfl rfl
                (countedBody_seq_straight _ rfl rfl rfl CountedBody.incr))))))
  have hloop := variableCountedWhile_run (ofString "i") (ofString "n") .lower (Or.inr rfl) K
    (fun h => by cases h) hbody rfl K.toNat s0 hs0_code 0 hs0_i hs0_n (by simp) (by simp)
    (by simp only [Nat.zero_add, Nat.mul_one]; change K.toNat ≤ next.clock; omega)
  simp only [Nat.zero_add, Nat.mul_one] at hloop
  have hs0_clock : s0.clock = next.clock := rfl
  exact (RunBounded.seq (state := s0) hloop (a := K.toNat) (b := 0) (by rw [hs0_clock]; omega)
    (fun last _ lastCode lastBudget =>
      (ProgBounded.straight _ rfl) last (lastCode.trans hs0_code) lastBudget)).weaken (by omega)

private theorem progBounded_u256_from_be_decCall_const (name : MlS) (p : ExpHOL 64)
    (K : BitVec 64) {tail : ProgHOL 64} {tailCost : Nat} (htail : ProgBounded tail tailCost) :
    ProgBounded
      (.decCall name (.comb [.one, .one, .one, .one]) (ofString "u256_from_be") [p, .const K] tail)
      (K.toNat + 5 + tailCost) := by
  intro F state hcode hbudget
  cases hargs : evalListHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a)) [p, .const K] with
  | none =>
    rw [evaluateHOLFiniteState_decCall_args_none state name _ (ofString "u256_from_be")
      [p, .const K] tail hargs]
    simp
  | some vs =>
    obtain ⟨v1, rfl⟩ := evalListHOLFinite_two_word2 state p (.const K) K hargs
      (by rw [evalHOLFinite_eq_toExact]; rfl)
    have hcall := RunBounded.decCall (state := state) (name := name)
      (shape := .comb [.one, .one, .one, .one]) (function := ofString "u256_from_be")
      (arguments := [p, .const K]) (continuation := tail) (bodyCost := K.toNat + 4)
      (tailCost := tailCost) hargs (by omega)
      (fun body locals rs hfound => by
        rw [hcode] at hfound
        obtain ⟨rfl, hnLoc⟩ := two_arg_lookup_second originalRuntimeCode.lookup
          (ofString "u256_from_be") (ofString "p") (ofString "n")
          (sourceFnBody Guest.Software.guestFn_u256_from_be) (.comb [.one, .one, .one, .one])
          (by decide) lookup_u256_from_be hfound
        refine ⟨runBounded_u256_from_be_body (callEntryStateHOLFinite state locals) K hcode hnLoc
          (by change K.toNat + 4 ≤ state.clock - 1; omega), ?_⟩
        intro value post hran hpostBudget
        have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata
          (callEntryStateHOLFinite state locals) (sourceFnBody Guest.Software.guestFn_u256_from_be)
        rw [hran] at hmeta
        exact htail (setVarHOLFinite name value {post with locals := state.locals})
          (hmeta.1.trans hcode) hpostBudget)
    exact hcall.weaken (by omega)

private def WordBound (M : Nat) (v : ValueHOL 64) : Prop :=
  ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat ≤ M

private theorem lookup_bit_length64 :
    originalRuntimeCode.lookup (ofString "bit_length64") =
      some ([(ofString "x", .one)], sourceFnBody Guest.Software.guestFn_bit_length64, .one) :=
  lookup_of_guestAst_getElem 77 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_bit_length64) rfl

private theorem lookup_u256_bit_length :
    originalRuntimeCode.lookup (ofString "u256_bit_length") =
      some ([(ofString "a", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_u256_bit_length, .one) :=
  lookup_of_guestAst_getElem 78 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_bit_length) rfl

private theorem lookup_u256_byte_length :
    originalRuntimeCode.lookup (ofString "u256_byte_length") =
      some ([(ofString "a", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_u256_byte_length, .one) :=
  lookup_of_guestAst_getElem 79 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_byte_length) rfl

private theorem lookup_u256_to_be_min :
    originalRuntimeCode.lookup (ofString "u256_to_be_min") =
      some ([(ofString "a", .comb [.one, .one, .one, .one]), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_u256_to_be_min, .one) :=
  lookup_of_guestAst_getElem 88 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_to_be_min) rfl

private theorem bit_length64_body_returns_le64 {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (retVal : ValueHOL 64)
    (hrun : evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_bit_length64) =
      (some (.returned retVal), post)) :
    WordBound 64 retVal := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_bit_length64,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
    at hrun
  rw [evaluateHOLFiniteState_dec_total] at hrun
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true] at hrun
  let s0 := setVarHOLFinite (ofString "n") (.val (.word 0#64)) state
  have stepIte : ∀ {st : PanSemStateFiniteExact 64 F} {n x : BitVec 64} (k : BitVec 64)
      (hklt : k.toNat < 64) (tail : ProgHOL 64),
      st.locals.lookup (ofString "n") = some (.val (.word n)) →
      st.locals.lookup (ofString "x") = some (.val (.word x)) →
      evaluateHOLFiniteState st
        (.seq
          (.ite (.cmp .notEqual (.shift .lsr (.var .local (ofString "x")) (.const k))
              (.const 0#64))
            (.seq
              (.assign .local (ofString "n")
                (.op .add [.var .local (ofString "n"), .const k]))
              (.assign .local (ofString "x")
                (.shift .lsr (.var .local (ofString "x")) (.const k))))
            .skip)
          tail) =
      evaluateHOLFiniteState
        (if (x >>> k.toNat) ≠ 0#64 then
          setVarHOLFinite (ofString "x") (.val (.word (x >>> k.toNat)))
            (setVarHOLFinite (ofString "n") (.val (.word (n + k))) st)
         else st)
        tail := by
    intro st n x k hklt tail hn hx
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
    have hnotge : ¬ (64 ≤ k.toNat) := Nat.not_le.mpr hklt
    have hcond : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
        (.cmp .notEqual (.shift .lsr (.var .local (ofString "x")) (.const k))
          (.const 0#64)) =
        some (.val (.word (if (x >>> k.toNat) ≠ 0#64 then 1#64 else 0#64))) := by
      simp only [evalHOLExact, hx, wordShiftHOL, hnotge, if_false,
        Compiler.Encoders.Asm.wordCmpHOL]
      by_cases hnz : (x >>> k.toNat) ≠ 0#64 <;> simp [hnz]
    rw [hcond]
    by_cases hnz : (x >>> k.toNat) ≠ 0#64
    · rw [if_pos hnz]
      have h10 : (1#64 : BitVec 64) ≠ 0 := by decide
      simp only [h10, if_false, if_pos hnz]
      have hassign1 : evaluateHOLFiniteState st
          (.assign .local (ofString "n")
            (.op .add [.var .local (ofString "n"), .const k])) =
          (none, setVarHOLFinite (ofString "n") (.val (.word (n + k))) st) := by
        simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hn,
          wordOpHOL, wordOp, valueIsWord, valueWord, lookupKvarHOLExact,
          PanSemStateFiniteExact.isValidValueHOLFinite, isValidValueHOLExact,
          setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
      have hx' : (setVarHOLFinite (ofString "n") (.val (.word (n + k))) st).locals.lookup
          (ofString "x") = some (.val (.word x)) := by
        have hne : ofString "n" ≠ ofString "x" := by decide
        simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hx]
      have hassign2 : evaluateHOLFiniteState
          (setVarHOLFinite (ofString "n") (.val (.word (n + k))) st)
          (.assign .local (ofString "x")
            (.shift .lsr (.var .local (ofString "x")) (.const k))) =
          (none,
            setVarHOLFinite (ofString "x") (.val (.word (x >>> k.toNat)))
              (setVarHOLFinite (ofString "n") (.val (.word (n + k))) st)) := by
        simp [evaluateHOLFiniteState_assign, evalHOLExact, hx', wordShiftHOL, hnotge,
          lookupKvarHOLExact, PanSemStateFiniteExact.isValidValueHOLFinite,
          isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
      rw [evaluateHOLFiniteState_seq_line780, hassign1]
      dsimp only
      rw [hassign2]
    · rw [if_neg hnz, if_neg hnz]
      have h00 : (0#64 : BitVec 64) = 0 := rfl
      simp only [h00, if_true, evaluateHOLFiniteState_skip]
  have hrun1 := (Prod.mk.inj hrun).1
  clear hrun
  rcases hx0 : s0.locals.lookup (ofString "x") with _ | vx
  · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hrun1
    have hnone : @evalHOLExact 64 F _ s0.toExact (fun a => Classical.propDecidable (s0.memaddrs a))
        (.cmp .notEqual (.shift .lsr (.var .local (ofString "x")) (.const 32#64)) (.const 0#64)) =
        none := by
      simp [evalHOLExact, hx0]
    rw [hnone] at hrun1
    simp at hrun1
  · cases vx with
    | rStruct _ =>
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hrun1
      have hnone :
          @evalHOLExact 64 F _ s0.toExact (fun a => Classical.propDecidable (s0.memaddrs a))
            (.cmp .notEqual (.shift .lsr (.var .local (ofString "x")) (.const 32#64))
              (.const 0#64)) = none := by
        simp [evalHOLExact, hx0]
      rw [hnone] at hrun1
      simp at hrun1
    | nStruct _ _ =>
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hrun1
      have hnone :
          @evalHOLExact 64 F _ s0.toExact (fun a => Classical.propDecidable (s0.memaddrs a))
            (.cmp .notEqual (.shift .lsr (.var .local (ofString "x")) (.const 32#64))
              (.const 0#64)) = none := by
        simp [evalHOLExact, hx0]
      rw [hnone] at hrun1
      simp at hrun1
    | val wlx =>
      cases wlx with
      | word x0 =>
        have stepRun : ∀ (st : PanSemStateFiniteExact 64 F) (n x k : BitVec 64) (M : Nat)
            (tail : ProgHOL 64),
            st.locals.lookup (ofString "n") = some (.val (.word n)) →
            st.locals.lookup (ofString "x") = some (.val (.word x)) →
            x.toNat < 2 ^ (2 * k.toNat) →
            n.toNat ≤ M →
            M ≤ 64 →
            2 * k.toNat ≤ 64 →
            0 < k.toNat →
            ∃ (st' : PanSemStateFiniteExact 64 F) (n' x' : BitVec 64),
              evaluateHOLFiniteState st
                (.seq
                  (.ite (.cmp .notEqual
                      (.shift .lsr (.var .local (ofString "x")) (.const k))
                      (.const 0#64))
                    (.seq
                      (.assign .local (ofString "n")
                        (.op .add [.var .local (ofString "n"), .const k]))
                      (.assign .local (ofString "x")
                        (.shift .lsr (.var .local (ofString "x")) (.const k))))
                    .skip)
                  tail) =
                evaluateHOLFiniteState st' tail ∧
              st'.locals.lookup (ofString "n") = some (.val (.word n')) ∧
              st'.locals.lookup (ofString "x") = some (.val (.word x')) ∧
              x'.toNat < 2 ^ k.toNat ∧
              n'.toNat ≤ M + k.toNat := by
          intro st n x k M tail hn hx hxlt hnle hm64 hk64 hkpos
          have hklt : k.toNat < 64 := by omega
          by_cases hnz : (x >>> k.toNat) ≠ 0#64
          · refine ⟨setVarHOLFinite (ofString "x") (.val (.word (x >>> k.toNat)))
              (setVarHOLFinite (ofString "n") (.val (.word (n + k))) st),
              n + k, x >>> k.toNat, ?_, ?_, ?_, ?_, ?_⟩
            · rw [stepIte k hklt tail hn hx, if_pos hnz]
            · have hne : ofString "x" ≠ ofString "n" := by decide
              simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne]
            · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
              have hpow : 2 ^ (2 * k.toNat) = 2 ^ k.toNat * 2 ^ k.toNat := by
                rw [Nat.two_mul, Nat.pow_add]
              rw [hpow] at hxlt
              exact Nat.div_lt_of_lt_mul hxlt
            · have h264 : 2 ^ 64 = 18446744073709551616 := rfl
              rw [BitVec.toNat_add_of_lt (by omega)]
              omega
          · refine ⟨st, n, x, ?_, hn, hx, ?_, by omega⟩
            · rw [stepIte k hklt tail hn hx, if_neg hnz]
            · have hzeq : x >>> k.toNat = 0#64 := Classical.not_not.mp hnz
              have hz0 : (x >>> k.toNat).toNat = 0 := by rw [hzeq]; rfl
              rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at hz0
              by_contra hge
              have hle : 2 ^ k.toNat ≤ x.toNat := Nat.not_lt.mp hge
              have hpos_pow : 0 < 2 ^ k.toNat := Nat.pos_of_ne_zero (by positivity)
              have hdiv_pos : 0 < x.toNat / 2 ^ k.toNat := Nat.div_pos hle hpos_pow
              omega
        have hn0 : s0.locals.lookup (ofString "n") = some (.val (.word 0#64)) := by
          simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        obtain ⟨s1, n1, x1, heq1, hn1, hx1, hx1lt, hn1le⟩ :=
          stepRun s0 0#64 x0 32#64 0 _ hn0 hx0 x0.isLt (by decide) (by decide) (by decide)
            (by decide)
        rw [heq1] at hrun1
        clear heq1
        obtain ⟨s2, n2, x2, heq2, hn2, hx2, hx2lt, hn2le⟩ :=
          stepRun s1 n1 x1 16#64 32 _ hn1 hx1 hx1lt hn1le (by decide) (by decide) (by decide)
        rw [heq2] at hrun1
        clear heq2
        obtain ⟨s3, n3, x3, heq3, hn3, hx3, hx3lt, hn3le⟩ :=
          stepRun s2 n2 x2 8#64 48 _ hn2 hx2 hx2lt hn2le (by decide) (by decide) (by decide)
        rw [heq3] at hrun1
        clear heq3
        obtain ⟨s4, n4, x4, heq4, hn4, hx4, hx4lt, hn4le⟩ :=
          stepRun s3 n3 x3 4#64 56 _ hn3 hx3 hx3lt hn3le (by decide) (by decide) (by decide)
        rw [heq4] at hrun1
        clear heq4
        obtain ⟨s5, n5, x5, heq5, hn5, hx5, hx5lt, hn5le⟩ :=
          stepRun s4 n4 x4 2#64 60 _ hn4 hx4 hx4lt hn4le (by decide) (by decide) (by decide)
        rw [heq5] at hrun1
        clear heq5
        obtain ⟨s6, n6, x6, heq6, hn6, hx6, hx6lt, hn6le⟩ :=
          stepRun s5 n5 x5 1#64 62 _ hn5 hx5 hx5lt hn5le (by decide) (by decide) (by decide)
        have hretEq : evaluateHOLFiniteState s6
            (.return (.op .add [.var .local (ofString "n"), .var .local (ofString "x")])) =
            (some (.returned (.val (.word (n6 + x6)))), s6.emptyLocalsHOLFinite) := by
          simp [evaluateHOLFiniteState_return, evalHOLExact, evalListHOLExact, hn6, hx6,
            wordOpHOL, wordOp, valueIsWord, valueWord, shapeOfHOLExact,
            sizeOfShapeWithContextHOL]
        rw [heq6, hretEq] at hrun1
        clear heq6 hretEq
        have hret : retVal = .val (.word (n6 + x6)) := by
          cases hrun1
          rfl
        refine ⟨n6 + x6, hret, ?_⟩
        have hx6le : x6.toNat ≤ 1 := by change x6.toNat < 2 at hx6lt; omega
        have hn6le' : n6.toNat ≤ 63 := hn6le
        have h264 : 2 ^ 64 = 18446744073709551616 := rfl
        rw [BitVec.toNat_add_of_lt (by omega)]
        omega

private theorem decCall_returned_inv {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {name function : MlS} {shape : ShapeHOL}
    {arguments : List (ExpHOL 64)} {continuation : ProgHOL 64} {retVal : ValueHOL 64}
    (hrun : evaluateHOLFiniteState s (.decCall name shape function arguments continuation) =
      (some (.returned retVal), post)) :
    ∃ (values : List (ValueHOL 64)) (body : ProgHOL 64)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
      (w : ValueHOL 64) (bodyPost inner : PanSemStateFiniteExact 64 F),
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments =
        some values ∧
      lookupCodeHOLFinite s.code.lookup function values = some (body, callee, returnShape) ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
        (some (.returned w), bodyPost) ∧
      evaluateHOLFiniteState (setVarHOLFinite name w {bodyPost with locals := s.locals})
        continuation = (some (.returned retVal), inner) := by
  rw [evaluateHOLFiniteState_decCall_total] at hrun
  cases args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      arguments with
  | none => rw [args] at hrun; simp at hrun
  | some values =>
    rw [args] at hrun
    dsimp only at hrun
    cases lookup : lookupCodeHOLFinite s.code.lookup function values with
    | none => rw [lookup] at hrun; simp at hrun
    | some installed =>
      obtain ⟨body, callee, returnShape⟩ := installed
      rw [lookup] at hrun
      dsimp only at hrun
      split at hrun
      · simp at hrun
      · have remaining := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s callee) body
        cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
        | mk r1 bodyPost =>
          rw [bodyRun] at hrun remaining
          have fixed : fixClockHOLFinite (callEntryStateHOLFinite s callee) (r1, bodyPost) =
              (r1, bodyPost) := by
            simp [fixClockHOLFinite, Nat.not_lt.mpr remaining]
          rw [fixed] at hrun
          dsimp only at hrun
          rcases r1 with _ | (_ | _ | _ | _ | w | _ | _)
          all_goals first
            | (simp at hrun; done)
            | skip
          simp only [] at hrun
          split at hrun
          · obtain ⟨e, _⟩ := Prod.mk.inj hrun
            exact ⟨values, body, callee, returnShape, w, bodyPost, _, rfl, rfl, rfl,
              Prod.ext e rfl⟩
          · simp at hrun

private theorem tailCall_returned_inv {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {function : MlS}
    {arguments : List (ExpHOL 64)} {retVal : ValueHOL 64}
    (hrun : evaluateHOLFiniteState s (.call none function arguments) =
      (some (.returned retVal), post)) :
    ∃ (values : List (ValueHOL 64)) (body : ProgHOL 64)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
      (bodyPost : PanSemStateFiniteExact 64 F),
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments =
        some values ∧
      lookupCodeHOLFinite s.code.lookup function values = some (body, callee, returnShape) ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
        (some (.returned retVal), bodyPost) := by
  rw [evaluateHOLFiniteState_call] at hrun
  cases args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      arguments with
  | none => rw [args] at hrun; simp at hrun
  | some values =>
    rw [args] at hrun
    dsimp only at hrun
    cases lookup : lookupCodeHOLFinite s.code.lookup function values with
    | none => rw [lookup] at hrun; simp at hrun
    | some installed =>
      obtain ⟨body, callee, returnShape⟩ := installed
      rw [lookup] at hrun
      dsimp only at hrun
      split at hrun
      · simp at hrun
      · cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
        | mk r1 bodyPost =>
          rw [bodyRun] at hrun
          rcases r1 with _ | (_ | _ | _ | _ | w | _ | _)
          all_goals first
            | (simp at hrun; done)
            | skip
          dsimp only at hrun
          split at hrun
          · simp only [Prod.mk.injEq, Option.some.injEq, PanSemResultExact.returned.injEq] at hrun
            obtain ⟨rfl, _⟩ := hrun
            exact ⟨values, body, callee, returnShape, bodyPost, rfl, rfl, rfl⟩
          · simp at hrun

private theorem u256_bit_length_body_returns_le256 {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (retVal : ValueHOL 64)
    (hcode : state.code = originalRuntimeCode)
    (hrun : evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_u256_bit_length) =
      (some (.returned retVal), post)) :
    WordBound 256 retVal := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_u256_bit_length,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
    at hrun
  have branchBound : ∀ {st stPost : PanSemStateFiniteExact 64 F} {nm : MlS} {arg : ExpHOL 64}
      {off : BitVec 64} {r : ValueHOL 64},
      st.code = originalRuntimeCode →
      off.toNat ≤ 192 →
      evaluateHOLFiniteState st
        (.decCall nm .one (ofString "bit_length64") [arg]
          (.return (.op .add [.const off, .var .local nm]))) =
        (some (.returned r), stPost) →
      WordBound 256 r := by
    intro st stPost nm arg off r hstCode hoff hbr
    obtain ⟨vs, b, loc, rs, w, bPost, inner, _, hlk, hbRun, hcont⟩ := decCall_returned_inv hbr
    have hbEq := lookupCodeHOLFinite_installed_body st.code.lookup (ofString "bit_length64")
      _ _ b _ rs vs loc (by rw [hstCode]; exact lookup_bit_length64) hlk
    subst hbEq
    obtain ⟨nw, rfl, hnwle⟩ := bit_length64_body_returns_le64 _ bPost w hbRun
    have hnm : (setVarHOLFinite nm (.val (.word nw)) {bPost with locals := st.locals}).locals.lookup
        nm = some (.val (.word nw)) := by
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hretEq : evaluateHOLFiniteState
        (setVarHOLFinite nm (.val (.word nw)) {bPost with locals := st.locals})
        (.return (.op .add [.const off, .var .local nm])) =
        (some (.returned (.val (.word (off + nw)))),
          (setVarHOLFinite nm (.val (.word nw))
            {bPost with locals := st.locals}).emptyLocalsHOLFinite) := by
      simp [evaluateHOLFiniteState_return, evalHOLExact, evalListHOLExact, hnm,
        wordOpHOL, wordOp, valueIsWord, valueWord, shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [hretEq] at hcont
    cases hcont
    refine ⟨off + nw, rfl, ?_⟩
    have h264 : 2 ^ 64 = 18446744073709551616 := rfl
    rw [BitVec.toNat_add_of_lt (by omega)]
    omega
  have stepSeqIte : ∀ {st stPost : PanSemStateFiniteExact 64 F} {cond : ExpHOL 64}
      {nm : MlS} {arg : ExpHOL 64} {off : BitVec 64} {tail : ProgHOL 64},
      st.code = originalRuntimeCode →
      off.toNat ≤ 192 →
      evaluateHOLFiniteState st
        (.seq (.ite cond (.decCall nm .one (ofString "bit_length64") [arg]
            (.return (.op .add [.const off, .var .local nm]))) .skip) tail) =
        (some (.returned retVal), stPost) →
      WordBound 256 retVal ∨ evaluateHOLFiniteState st tail = (some (.returned retVal), stPost) := by
    intro st stPost cond nm arg off tail hstCode hoff hseq
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hseq
    split at hseq
    · split at hseq
      · rw [evaluateHOLFiniteState_skip] at hseq
        exact Or.inr hseq
      · cases hcall : evaluateHOLFiniteState st
            (.decCall nm .one (ofString "bit_length64") [arg]
              (.return (.op .add [.const off, .var .local nm]))) with
        | mk r1 mid =>
          rw [hcall] at hseq
          cases r1 with
          | none =>
            obtain ⟨_, _, _, _, _, hcont⟩ :=
              decCall_flowing (Or.inl rfl) hcall
            rw [evaluateHOLFiniteState_return] at hcont
            split at hcont <;> first | simp at hcont | (split at hcont <;> simp at hcont)
          | some r1v =>
            dsimp only at hseq
            rw [hseq] at hcall
            exact Or.inl (branchBound hstCode hoff hcall)
    · simp at hseq
  rcases stepSeqIte hcode (by decide) hrun with h | hrun2
  · exact h
  · rcases stepSeqIte hcode (by decide) hrun2 with h | hrun3
    · exact h
    · rcases stepSeqIte hcode (by decide) hrun3 with h | hrun4
      · exact h
      · obtain ⟨vs, b, loc, rs, bPost, _, hlk, hbRun⟩ := tailCall_returned_inv hrun4
        have hbEq := lookupCodeHOLFinite_installed_body state.code.lookup (ofString "bit_length64")
          _ _ b _ rs vs loc (by rw [hcode]; exact lookup_bit_length64) hlk
        subst hbEq
        obtain ⟨nw, rfl, hnwle⟩ := bit_length64_body_returns_le64 _ bPost retVal hbRun
        exact ⟨nw, rfl, by omega⟩

private theorem u256_byte_length_body_returns_le32 {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (retVal : ValueHOL 64)
    (hcode : state.code = originalRuntimeCode)
    (hrun : evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_u256_byte_length) =
      (some (.returned retVal), post)) :
    WordBound 32 retVal := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_u256_byte_length,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
    at hrun
  obtain ⟨vs, b, loc, rs, w, bPost, inner, _, hlk, hbRun, hcont⟩ := decCall_returned_inv hrun
  have hbEq := lookupCodeHOLFinite_installed_body state.code.lookup (ofString "u256_bit_length")
    _ _ b _ rs vs loc (by rw [hcode]; exact lookup_u256_bit_length) hlk
  subst hbEq
  obtain ⟨nw, rfl, hnwle⟩ :=
    u256_bit_length_body_returns_le256 (callEntryStateHOLFinite state loc) bPost w hcode hbRun
  have hn : (setVarHOLFinite (ofString "n") (.val (.word nw))
      {bPost with locals := state.locals}).locals.lookup (ofString "n") =
      some (.val (.word nw)) := by
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hnotge : ¬ (64 ≤ (3#64 : BitVec 64).toNat) := by decide
  have hretEq : evaluateHOLFiniteState
      (setVarHOLFinite (ofString "n") (.val (.word nw)) {bPost with locals := state.locals})
      (.return (.shift .lsr (.op .add [.var .local (ofString "n"), .const 7#64]) (.const 3#64))) =
      (some (.returned (.val (.word ((nw + 7#64) >>> (3#64).toNat)))),
        (setVarHOLFinite (ofString "n") (.val (.word nw))
          {bPost with locals := state.locals}).emptyLocalsHOLFinite) := by
    simp [evaluateHOLFiniteState_return, evalHOLExact, evalListHOLExact, hn, wordOpHOL, wordOp,
      valueIsWord, valueWord, wordShiftHOL, hnotge, shapeOfHOLExact, sizeOfShapeWithContextHOL]
  rw [hretEq] at hcont
  cases hcont
  refine ⟨(nw + 7#64) >>> (3#64).toNat, rfl, ?_⟩
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have h264 : 2 ^ 64 = 18446744073709551616 := rfl
  have h7 : (7#64 : BitVec 64).toNat = 7 := rfl
  have hadd : (nw + 7#64).toNat = nw.toNat + 7 := by
    rw [BitVec.toNat_add_of_lt (by omega)]
    exact congrArg (nw.toNat + ·) h7
  rw [hadd]
  change (nw.toNat + 7) / 8 ≤ 32
  omega

private inductive UpBody (counter : MlS) : ProgHOL 64 → Nat → Prop
  | incr : UpBody counter (.assign .local counter (.op .add [.var .local counter, .const 1])) 0
  | incrThen {tail : ProgHOL 64} {b : Nat} (bounded : ProgBounded tail b)
      (avoid : avoidsLocal counter tail = true) (noCont : noTopContinue tail = true) :
      UpBody counter
        (.seq (.assign .local counter (.op .add [.var .local counter, .const 1])) tail) b
  | seq (first : ProgHOL 64) {tail : ProgHOL 64} {a b : Nat} (bounded : ProgBounded first a)
      (avoid : avoidsLocal counter first = true) (noCont : noTopContinue first = true)
      (rest : UpBody counter tail b) : UpBody counter (.seq first tail) (a + b)
  | dec (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL 64) {body : ProgHOL 64} {cost : Nat}
      (distinct : counter ≠ name) (rest : UpBody counter body cost) :
      UpBody counter (.dec name shape initializer body) cost
  | decCall {name function : MlS} {shape : ShapeHOL} {arguments : List (ExpHOL 64)}
      {continuation : ProgHOL 64} {fnCost tailCost : Nat}
      (installed : FunBounded function fnCost) (distinct : counter ≠ name)
      (rest : UpBody counter continuation tailCost) :
      UpBody counter (.decCall name shape function arguments continuation)
        (fnCost + 1 + tailCost)

private theorem upBody_run {counter : MlS} {body : ProgHOL 64} {cost : Nat}
    (counted : UpBody counter body cost) {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode) (w : BitVec 64)
    (atCounter : state.locals.lookup counter = some (.val (.word w))) (budget : cost ≤ state.clock) :
    state.clock ≤ (evaluateHOLFiniteState state body).2.clock + cost ∧
      (evaluateHOLFiniteState state body).2.clock ≤ state.clock ∧
      (evaluateHOLFiniteState state body).1 ≠ some .timeOut ∧
      (evaluateHOLFiniteState state body).1 ≠ some .continue ∧
      ((evaluateHOLFiniteState state body).1 = none →
        (evaluateHOLFiniteState state body).2.locals.lookup counter = some (.val (.word (w + 1))) ∧
        (evaluateHOLFiniteState state body).2.code = state.code) := by
  induction counted generalizing state with
  | incr =>
    have run : evaluateHOLFiniteState state
        (.assign .local counter (.op .add [.var .local counter, .const 1])) =
        (none, setVarHOLFinite counter (.val (.word (w + 1))) state) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, atCounter,
        wordOpHOL, wordOp, valueIsWord, valueWord, lookupKvarHOLExact,
        PanSemStateFiniteExact.isValidValueHOLFinite, isValidValueHOLExact,
        setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
    rw [run]
    refine ⟨by simp [setVarHOLFinite], by simp [setVarHOLFinite], by simp, by simp, fun _ => ⟨?_, rfl⟩⟩
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  | incrThen bounded avoid noCont =>
    rename_i tail b
    have run : evaluateHOLFiniteState state
        (.assign .local counter (.op .add [.var .local counter, .const 1])) =
        (none, setVarHOLFinite counter (.val (.word (w + 1))) state) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, atCounter,
        wordOpHOL, wordOp, valueIsWord, valueWord, lookupKvarHOLExact,
        PanSemStateFiniteExact.isValidValueHOLFinite, isValidValueHOLExact,
        setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
    let entered := setVarHOLFinite counter (.val (.word (w + 1))) state
    have atNext : entered.locals.lookup counter = some (.val (.word (w + 1))) := by
      simp [entered, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have tailBound := bounded entered code budget
    have frame := evaluate_avoidsLocal_flowing counter tail avoid entered
    have noContinue := evaluate_noTopContinue tail noCont entered
    have meta' := PanRunBounded.evaluateHOLFiniteState_metadata entered tail
    rw [evaluateHOLFiniteState_seq_line780, run]
    dsimp only
    cases tailRun : evaluateHOLFiniteState entered tail with
    | mk result middle =>
      rw [tailRun] at tailBound frame noContinue meta'
      dsimp only at tailBound frame noContinue meta'
      obtain ⟨spent, kept, safe⟩ := tailBound
      change state.clock ≤ middle.clock + b at spent
      change middle.clock ≤ state.clock at kept
      cases result with
      | none =>
        refine ⟨spent, kept, by simp, by simp, fun _ => ⟨?_, meta'.1⟩⟩
        rw [frame (Or.inl rfl)]
        exact atNext
      | some r =>
        exact ⟨spent, kept, safe, noContinue, fun h => by simp at h⟩
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
        obtain ⟨t1, t2, t3, t4, t5⟩ :=
          ih middle (meta'.1.trans code) (by rw [kept']; exact atCounter) (by omega)
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
          simp [inner, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            Ne.symm distinct, atCounter]
        obtain ⟨t1, t2, t3, t4, t5⟩ := ih inner code atInner budget
        cases run : evaluateHOLFiniteState inner _ with
        | mk res post =>
          rw [run] at t1 t2 t3 t4 t5
          dsimp only at t1 t2 t3 t4 t5 ⊢
          refine ⟨t1, t2, t3, t4, fun normal => ?_⟩
          obtain ⟨i1, i2⟩ := t5 normal
          refine ⟨?_, i2⟩
          rw [resVarEq_lookup, if_neg distinct]
          exact i1
      · exact ⟨Nat.le_add_right _ _, le_refl _, by simp, by simp, by simp⟩
  | decCall installed distinct rest ih =>
    rename_i name function shape arguments continuation fnCost tailCost
    cases args : evalListHOLFinite state
        (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
    | none =>
      rw [evaluateHOLFiniteState_decCall_args_none state name shape function arguments
        continuation args]
      exact ⟨Nat.le_add_right _ _, le_refl _, by simp, by simp, by simp⟩
    | some values =>
      cases lookup : lookupCodeHOLFinite state.code.lookup function values with
      | none =>
        rw [evaluateHOLFiniteState_decCall_lookup_none state name shape function arguments
          continuation values args lookup]
        exact ⟨Nat.le_add_right _ _, le_refl _, by simp, by simp, by simp⟩
      | some found =>
        obtain ⟨fnBody, callee, returnShape⟩ := found
        have bounded := ProgBounded.bodies_of_fun installed state code (by omega) values fnBody
          callee returnShape lookup
        change (callEntryStateHOLFinite state callee).clock ≤
            (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) fnBody).2.clock +
              fnCost ∧
          (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) fnBody).2.clock ≤
            (callEntryStateHOLFinite state callee).clock ∧
          (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) fnBody).1 ≠
            some .timeOut at bounded
        have metaFn := PanRunBounded.evaluateHOLFiniteState_metadata
          (callEntryStateHOLFinite state callee) fnBody
        have nonzero : state.clock ≠ 0 := by omega
        rw [evaluateHOLFiniteState_decCall_total, args]
        dsimp only
        rw [lookup]
        dsimp only
        rw [if_neg nonzero]
        cases ran : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) fnBody with
        | mk fnRes fnPost =>
          rw [ran] at bounded metaFn
          obtain ⟨fnSpent, fnKept, fnSafe⟩ := bounded
          change state.clock - 1 ≤ fnPost.clock + fnCost at fnSpent
          change fnPost.clock ≤ state.clock - 1 at fnKept
          have fixed : fixClockHOLFinite (callEntryStateHOLFinite state callee) (fnRes, fnPost) =
              (fnRes, fnPost) := by
            simp [fixClockHOLFinite, Nat.not_lt.mpr fnKept]
          rw [fixed]
          dsimp only
          cases fnRes with
          | none =>
            exact ⟨by omega, by omega, by simp, by simp, by simp⟩
          | some r =>
            cases r with
            | returned retV =>
              simp only []
              split
              · let resumed := setVarHOLFinite name retV {fnPost with locals := state.locals}
                have hresCode : resumed.code = originalRuntimeCode := metaFn.1.trans code
                have atResumed : resumed.locals.lookup counter = some (.val (.word w)) := by
                  simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                    Ne.symm distinct, atCounter]
                obtain ⟨t1, t2, t3, t4, t5⟩ := ih resumed hresCode atResumed
                  (by change tailCost ≤ fnPost.clock; omega)
                cases contRun : evaluateHOLFiniteState resumed continuation with
                | mk cRes cPost =>
                  rw [contRun] at t1 t2 t3 t4 t5
                  dsimp only at t1 t2 t3 t4 t5 ⊢
                  change fnPost.clock ≤ cPost.clock + tailCost at t1
                  change cPost.clock ≤ fnPost.clock at t2
                  refine ⟨by omega, by omega, t3, t4, fun normal => ?_⟩
                  obtain ⟨i1, i2⟩ := t5 normal
                  refine ⟨?_, i2.trans metaFn.1⟩
                  rw [resVarEq_lookup, if_neg distinct]
                  exact i1
              · exact ⟨by omega, by omega, by simp, by simp, by simp⟩
            | timeOut => exact absurd rfl fnSafe
            | error => exact ⟨by omega, by omega, by simp, by simp, by simp⟩
            | «break» => exact ⟨by omega, by omega, by simp, by simp, by simp⟩
            | «continue» => exact ⟨by omega, by omega, by simp, by simp, by simp⟩
            | exception _ _ => exact ⟨by omega, by omega, by simp, by simp, by simp⟩
            | finalFfi _ => exact ⟨by omega, by omega, by simp, by simp, by simp⟩

private theorem upWhile_lower_run (counter limit : MlS) (K : BitVec 64)
    {body : ProgHOL 64} {cost : Nat} (counted : UpBody counter body cost)
    (preservesLimit : avoidsLocal limit body = true) :
    ∀ n : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F),
      state.code = originalRuntimeCode →
      ∀ w : BitVec 64, state.locals.lookup counter = some (.val (.word w)) →
      state.locals.lookup limit = some (.val (.word K)) → w.toNat ≤ K.toNat →
      K.toNat - w.toNat = n → n * (cost + 1) ≤ state.clock →
      let evaluated := evaluateHOLFiniteState state
        (.while (.cmp .lower (.var .local counter) (.var .local limit)) body)
      state.clock ≤ evaluated.2.clock + n * (cost + 1) ∧
        evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro F state code w atCounter atLimit within distance budget
    have condition := eval_variable_counted_condition state counter limit .lower (Or.inr rfl)
      K w (fun h => by cases h) within atCounter atLimit
    dsimp only
    rw [evaluateHOLFiniteState_while_total, condition]
    by_cases lt : w.toNat < K.toNat
    · rw [if_pos lt]
      simp only [show (1 : BitVec 64) ≠ 0 by decide, if_true, ne_eq, not_false_eq_true]
      have positiveRank : 0 < n := by omega
      have oneIteration : cost + 1 ≤ n * (cost + 1) := Nat.le_mul_of_pos_left _ positiveRank
      have clock : state.clock ≠ 0 := by omega
      rw [if_neg clock, fixClockHOLFinite_evaluateState]
      have stepRun := upBody_run counted (decClockHOLFinite state) code w atCounter
        (by change cost ≤ state.clock - 1; omega)
      have frame := evaluate_avoidsLocal_flowing limit body preservesLimit (decClockHOLFinite state)
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
          have nextLimit : middle.locals.lookup limit = some (.val (.word K)) := by
            rw [frame (Or.inl rfl)]
            exact atLimit
          have decrease : (K.toNat - (w + 1).toNat) * (cost + 1) + (cost + 1) ≤ n * (cost + 1) := by
            rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
          have tail := ih (K.toNat - (w + 1).toNat) nextRank middle (nextCode.trans code)
            (w + 1) nextCounter nextLimit (by rw [natural]; omega) rfl (by omega)
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

private theorem funBounded_u256_exp : FunBounded (ofString "u256_exp") 5125 := by
  refine funBounded_of_guestAst 80 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_exp 5125 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_u256_exp,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine ProgBounded.dec _ _ _ (ProgBounded.dec _ _ _ ?_)
  intro F state hcode hbudget
  cases hargs : evalListHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "b")] with
  | none =>
    rw [evaluateHOLFiniteState_decCall_args_none state (ofString "len") .one
      (ofString "u256_bit_length") [.var .local (ofString "b")] _ hargs]
    simp
  | some vs =>
    refine RunBounded.weaken (RunBounded.decCall (bodyCost := 4) (tailCost := 5120) hargs
      (by omega) ?_) (by omega)
    intro body locals rs hfound
    have hbEq := lookupCodeHOLFinite_installed_body state.code.lookup
      (ofString "u256_bit_length") _ _ body _ rs vs locals
      (by rw [hcode]; exact lookup_u256_bit_length) hfound
    subst hbEq
    have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata
      (callEntryStateHOLFinite state locals)
      (sourceFnBody Guest.Software.guestFn_u256_bit_length)
    have hbodyBound := ProgBounded.bodies_of_fun funBounded_u256_bit_length state hcode
      (by omega) vs (sourceFnBody Guest.Software.guestFn_u256_bit_length) locals rs hfound
    refine ⟨hbodyBound, ?_⟩
    intro val post hran hpost_clk
    rw [hran] at hmeta
    obtain ⟨lenW, rfl, hlenLe⟩ :=
      u256_bit_length_body_returns_le256 (callEntryStateHOLFinite state locals) post val
        hcode hran
    let s1 := setVarHOLFinite (ofString "len") (.val (.word lenW))
      {post with locals := state.locals}
    have hs1Code : s1.code = originalRuntimeCode := hmeta.1.trans hcode
    change RunBounded s1 _ 5120
    apply RunBounded.decConst
    let s2 := setVarHOLFinite (ofString "t") (.val (.word 0#64)) s1
    have ht2 : s2.locals.lookup (ofString "t") = some (.val (.word 0#64)) := by
      simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hlen2 : s2.locals.lookup (ofString "len") = some (.val (.word lenW)) := by
      have hne : ofString "t" ≠ ofString "len" := by decide
      simp [s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne]
    have hloopBody : UpBody (ofString "t")
        (.decCall (ofString "bit") .one (ofString "u256_bit")
          [.var .local (ofString "b"), .var .local (ofString "t")]
          (.seq
            (.ite (.cmp .equal (.var .local (ofString "bit")) (.const 1#64))
              (.call (some (some (.local, ofString "result"), none)) (ofString "u256_mul")
                [.var .local (ofString "result"), .var .local (ofString "base")])
              .skip)
            (.seq
              (.assign .local (ofString "t")
                (.op .add [.var .local (ofString "t"), .const 1#64]))
              (.ite (.cmp .lower (.var .local (ofString "t")) (.var .local (ofString "len")))
                (.call (some (some (.local, ofString "base"), none)) (ofString "u256_mul")
                  [.var .local (ofString "base"), .var .local (ofString "base")])
                .skip))))
        18 := by
      have hmul1 : ProgBounded
          (.ite (.cmp .equal (.var .local (ofString "bit")) (.const 1#64))
            (.call (some (some (.local, ofString "result"), none)) (ofString "u256_mul")
              [.var .local (ofString "result"), .var .local (ofString "base")])
            .skip) 8 :=
        ProgBounded.weaken
          (ProgBounded.iteMax _ (ProgBounded.call funBounded_u256_mul _ _)
            (ProgBounded.straight _ rfl))
          (by omega)
      have hmul2 : ProgBounded
          (.ite (.cmp .lower (.var .local (ofString "t")) (.var .local (ofString "len")))
            (.call (some (some (.local, ofString "base"), none)) (ofString "u256_mul")
              [.var .local (ofString "base"), .var .local (ofString "base")])
            .skip) 8 :=
        ProgBounded.weaken
          (ProgBounded.iteMax _ (ProgBounded.call funBounded_u256_mul _ _)
            (ProgBounded.straight _ rfl))
          (by omega)
      have hinner : UpBody (ofString "t") _ 16 :=
        UpBody.seq _ hmul1 rfl rfl (UpBody.incrThen hmul2 rfl rfl)
      exact UpBody.decCall (name := ofString "bit") funBounded_u256_bit (by decide) hinner
    have hwhile : RunBounded s2
        (.while (.cmp .lower (.var .local (ofString "t")) (.var .local (ofString "len"))) _)
        (lenW.toNat * 19) :=
      upWhile_lower_run (ofString "t") (ofString "len") lenW hloopBody rfl lenW.toNat
        s2 hs1Code 0#64 ht2 hlen2 (by simp) (by simp)
        (by change lenW.toNat * 19 ≤ post.clock; omega)
    have hseq := RunBounded.seq (hwhile.weaken (larger := 5120) (by omega))
      (tail := .return (.var .local (ofString "result")))
      (b := 0) (by change 5120 + 0 ≤ post.clock; omega)
      (fun next _ hnextCode hnextClk =>
        RunBounded.ofProg (ProgBounded.straight _ rfl) (hnextCode.trans hs1Code) hnextClk)
    exact hseq.weaken (by omega)

private theorem funBounded_u256_to_be_min : FunBounded (ofString "u256_to_be_min") 70 := by
  refine funBounded_of_guestAst 88 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_to_be_min 70 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_u256_to_be_min,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  intro F state hcode hbudget
  cases hargs : evalListHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "a")] with
  | none =>
    rw [evaluateHOLFiniteState_decCall_args_none state (ofString "len") .one
      (ofString "u256_byte_length") [.var .local (ofString "a")] _ hargs]
    simp
  | some vs =>
    refine RunBounded.weaken (RunBounded.decCall (bodyCost := 5) (tailCost := 64) hargs
      (by omega) ?_) (by omega)
    intro body locals rs hfound
    have hbEq := lookupCodeHOLFinite_installed_body state.code.lookup
      (ofString "u256_byte_length") _ _ body _ rs vs locals
      (by rw [hcode]; exact lookup_u256_byte_length) hfound
    subst hbEq
    have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata
      (callEntryStateHOLFinite state locals)
      (sourceFnBody Guest.Software.guestFn_u256_byte_length)
    have hbodyBound := ProgBounded.bodies_of_fun funBounded_u256_byte_length state hcode
      (by omega) vs (sourceFnBody Guest.Software.guestFn_u256_byte_length) locals rs hfound
    refine ⟨hbodyBound, ?_⟩
    intro val post hran hpost_clk
    rw [hran] at hmeta
    obtain ⟨lenW, rfl, hlenLe⟩ :=
      u256_byte_length_body_returns_le32 (callEntryStateHOLFinite state locals) post val
        hcode hran
    let s1 := setVarHOLFinite (ofString "len") (.val (.word lenW))
      {post with locals := state.locals}
    have hs1Code : s1.code = originalRuntimeCode := hmeta.1.trans hcode
    change RunBounded s1 _ 64
    apply RunBounded.decConst
    let s2 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) s1
    have hi2 : s2.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
      simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hlen2 : s2.locals.lookup (ofString "len") = some (.val (.word lenW)) := by
      have hne : ofString "i" ≠ ofString "len" := by decide
      simp [s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne]
    have hloopBody : UpBody (ofString "i")
        (.dec (ofString "pos") .one
          (.op .sub [.op .sub [.var .local (ofString "len"), .const 1#64],
            .var .local (ofString "i")])
          (.decCall (ofString "l") .one (ofString "u256_limb")
            [.var .local (ofString "a"),
              .shift .lsr (.var .local (ofString "pos")) (.const 3#64)]
            (.seq
              (.storeByte (.op .add [.var .local (ofString "out"), .var .local (ofString "i")])
                (.op .and
                  [.shift .lsr (.var .local (ofString "l"))
                    (.panop .mul
                      [.op .and [.var .local (ofString "pos"), .const 7#64], .const 8#64]),
                    .const 255#64]))
              (.assign .local (ofString "i")
                (.op .add [.var .local (ofString "i"), .const 1#64])))))
        1 := by
      refine UpBody.dec _ _ _ (by decide) ?_
      exact UpBody.decCall (name := ofString "l") funBounded_u256_limb (by decide)
        (UpBody.seq _ (ProgBounded.straight _ rfl) rfl rfl UpBody.incr)
    have hwhile : RunBounded s2
        (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "len"))) _)
        (lenW.toNat * 2) :=
      upWhile_lower_run (ofString "i") (ofString "len") lenW hloopBody rfl lenW.toNat
        s2 hs1Code 0#64 hi2 hlen2 (by simp) (by simp)
        (by change lenW.toNat * 2 ≤ post.clock; omega)
    have hseq := RunBounded.seq (hwhile.weaken (larger := 64) (by omega))
      (tail := .return (.var .local (ofString "len")))
      (b := 0) (by change 64 + 0 ≤ post.clock; omega)
      (fun next _ hnextCode hnextClk =>
        RunBounded.ofProg (ProgBounded.straight _ rfl) (hnextCode.trans hs1Code) hnextClk)
    exact hseq.weaken (by omega)

private def noTopReturn : ProgHOL 64 → Bool
  | .return _ => false
  | .seq first second => noTopReturn first && noTopReturn second
  | .ite _ yes no => noTopReturn yes && noTopReturn no
  | .dec _ _ _ body => noTopReturn body
  | .decCall _ _ _ _ continuation => noTopReturn continuation
  | .while _ body => noTopReturn body
  | .skip | .assign _ _ _ | .primitive _ _ _ | .store _ _ | .storeByte _ _ | .store32 _ _
  | .break | .continue | .raise _ _ | .extCall _ _ _ _ _ | .shMemLoad _ _ _ _
  | .shMemStore _ _ _ | .annot _ _ => true
  | .call (some (_, none)) _ _ => true
  | _ => false

private theorem evaluate_noTopReturn {F : Type} (program : ProgHOL 64)
    (supported : noTopReturn program = true) (state : PanSemStateFiniteExact 64 F)
    (retVal : ValueHOL 64) :
    (evaluateHOLFiniteState state program).1 ≠ some (.returned retVal) := by
  cases shape : program with
  | «return» _ => simp [shape, noTopReturn] at supported
  | seq first second =>
    have children : noTopReturn first = true ∧ noTopReturn second = true := by
      simpa only [shape, noTopReturn, Bool.and_eq_true] using supported
    have remaining := evaluateHOLFiniteState_clock_le state first
    rw [evaluateHOLFiniteState_seq_line780]
    have one := evaluate_noTopReturn first children.1 state retVal
    cases firstRun : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [firstRun] at one remaining
      cases result with
      | none => exact evaluate_noTopReturn second children.2 middle retVal
      | some _ => exact one
  | ite condition yes no =>
    have children : noTopReturn yes = true ∧ noTopReturn no = true := by
      simpa only [shape, noTopReturn, Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noTopReturn no children.2 state retVal
      · exact evaluate_noTopReturn yes children.1 state retVal
    · simp
  | dec name kind initializer body =>
    have child : noTopReturn body = true := by simpa only [shape, noTopReturn] using supported
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · simp
    · split
      · exact evaluate_noTopReturn body child _ retVal
      · simp
  | decCall name shape' function arguments continuation =>
    have child : noTopReturn continuation = true := by
      simpa only [shape, noTopReturn] using supported
    intro hret
    cases run : evaluateHOLFiniteState state
        (.decCall name shape' function arguments continuation) with
    | mk result post =>
      rw [run] at hret
      dsimp only at hret
      subst hret
      obtain ⟨_, _, _, _, w, bodyPost, inner, _, _, _, contRun⟩ := decCall_returned_inv run
      have hne := evaluate_noTopReturn continuation child
        (setVarHOLFinite name w {bodyPost with locals := state.locals}) retVal
      rw [contRun] at hne
      exact hne rfl
  | skip => simp [evaluateHOLFiniteState_skip]
  | «break» => simp [evaluateHOLFiniteState_break]
  | «continue» => simp [evaluateHOLFiniteState_continue]
  | annot _ _ => simp [evaluateHOLFiniteState_annot]
  | raise name value =>
    rw [evaluateHOLFiniteState_raise]; split
    · dsimp only; split <;> simp
    · simp
  | store destination value =>
    rcases (evaluate_store_control_frame state destination value).1 with h | h <;> rw [h] <;> simp
  | storeByte destination value =>
    rcases (evaluate_storeByte_control_frame state destination value).1 with h | h <;>
      rw [h] <;> simp
  | store32 address value =>
    rw [evaluateHOLFiniteState_store32]
    repeat' first | split | simp
  | shMemLoad _ _ _ _ =>
    rw [evaluateHOLFiniteState_shMemLoad_source]
    split
    · split
      · dsimp only
        unfold shMemLoadHOLFiniteExact
        repeat' first | split | simp
      · simp
    · simp
  | shMemStore _ _ _ =>
    classical
    rw [evaluateHOLFiniteState_shMemStore_total]
    dsimp only
    split
    · unfold shMemStoreHOLExact
      repeat' first | split | simp
    · simp
  | assign _ _ _ =>
    rw [evaluateHOLFiniteState_assign]; split
    · simp
    · split <;> simp
  | primitive _ _ _ =>
    rw [evaluateHOLFiniteState_primitive]
    repeat' first | split | simp
  | extCall _ _ _ _ _ =>
    rw [evaluateHOLFiniteState_extCall_source]
    repeat' first | split | simp
  | call info function arguments =>
    have handlerFree : ∃ d, info = some (d, none) := by
      rcases info with _ | ⟨d, _ | h⟩
      · simp [shape, noTopReturn] at supported
      · exact ⟨d, rfl⟩
      · simp [shape, noTopReturn] at supported
    rw [evaluateHOLFiniteState_call]
    rcases handlerFree with ⟨d, rfl⟩
    dsimp only
    repeat' first | split | simp | simp_all
  | «while» condition body =>
    have child : noTopReturn body = true := by simpa only [shape, noTopReturn] using supported
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · simp
        · dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body
          have bodyNoRet := evaluate_noTopReturn body child (decClockHOLFinite state) retVal
          cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
          | mk result middle =>
            rw [bodyRun] at remaining bodyNoRet
            have smaller : middle.clock < state.clock := by
              change middle.clock ≤ state.clock - 1 at remaining
              omega
            cases result with
            | none =>
              exact evaluate_noTopReturn (.while condition body) (by simpa [noTopReturn] using child)
                middle retVal
            | some r =>
              cases r with
              | «continue» =>
                exact evaluate_noTopReturn (.while condition body)
                  (by simpa [noTopReturn] using child) middle retVal
              | returned v =>
                dsimp only at bodyNoRet ⊢
                exact bodyNoRet
              | _ => simp
      · simp
    · simp
  | _ => simp [shape, noTopReturn] at supported
termination_by (state.clock, sizeOf program)
decreasing_by all_goals (simp_all [decClockHOLFinite, setVarHOLFinite]; omega)

private theorem u256_to_be_min_body_returns_le32 {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (retVal : ValueHOL 64)
    (hcode : state.code = originalRuntimeCode)
    (hrun : evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_u256_to_be_min) =
      (some (.returned retVal), post)) :
    WordBound 32 retVal := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_u256_to_be_min,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
    at hrun
  obtain ⟨vs, b, loc, rs, w, bPost, inner1, _, hlk, hbRun, hcont⟩ := decCall_returned_inv hrun
  have hbEq := lookupCodeHOLFinite_installed_body state.code.lookup (ofString "u256_byte_length")
    _ _ b _ rs vs loc (by rw [hcode]; exact lookup_u256_byte_length) hlk
  subst hbEq
  obtain ⟨lenW, rfl, hlenLe⟩ :=
    u256_byte_length_body_returns_le32 (callEntryStateHOLFinite state loc) bPost w hcode hbRun
  rw [evaluateHOLFiniteState_dec_total] at hcont
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true] at hcont
  have hcont1 := (Prod.mk.inj hcont).1
  clear hcont
  let s2 := setVarHOLFinite (ofString "i") (.val (.word 0#64))
    (setVarHOLFinite (ofString "len") (.val (.word lenW)) {bPost with locals := state.locals})
  have hlen2 : s2.locals.lookup (ofString "len") = some (.val (.word lenW)) := by
    have hne : ofString "i" ≠ ofString "len" := by decide
    simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne]
  let wprog : ProgHOL 64 :=
    .while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "len")))
      (.dec (ofString "pos") .one
        (.op .sub [.op .sub [.var .local (ofString "len"), .const 1#64],
          .var .local (ofString "i")])
        (.decCall (ofString "l") .one (ofString "u256_limb")
          [.var .local (ofString "a"),
            .shift .lsr (.var .local (ofString "pos")) (.const 3#64)]
          (.seq
            (.storeByte (.op .add [.var .local (ofString "out"), .var .local (ofString "i")])
              (.op .and
                [.shift .lsr (.var .local (ofString "l"))
                  (.panop .mul
                    [.op .and [.var .local (ofString "pos"), .const 7#64], .const 8#64]),
                  .const 255#64]))
            (.assign .local (ofString "i")
              (.op .add [.var .local (ofString "i"), .const 1#64])))))
  have hframe := evaluate_avoidsLocal_flowing (ofString "len") wprog rfl s2
  have hnoRet := evaluate_noTopReturn wprog rfl s2 retVal
  rw [evaluateHOLFiniteState_seq_line780] at hcont1
  cases hwRun : evaluateHOLFiniteState
      (setVarHOLFinite (ofString "i") (.val (.word 0#64))
        (setVarHOLFinite (ofString "len") (.val (.word lenW))
          {bPost with locals := state.locals}))
      wprog with
  | mk wRes wMid =>
    rw [hwRun] at hcont1
    have hwRun' : evaluateHOLFiniteState s2 wprog = (wRes, wMid) := hwRun
    rw [hwRun'] at hframe hnoRet
    dsimp only at hcont1 hframe hnoRet
    cases wRes with
    | none =>
      dsimp only at hcont1
      have hlenMid : wMid.locals.lookup (ofString "len") = some (.val (.word lenW)) := by
        rw [hframe (Or.inl rfl)]
        exact hlen2
      have hretEq : evaluateHOLFiniteState wMid (.return (.var .local (ofString "len"))) =
          (some (.returned (.val (.word lenW))), wMid.emptyLocalsHOLFinite) := by
        simp [evaluateHOLFiniteState_return, evalHOLExact, hlenMid, shapeOfHOLExact]
      rw [hretEq] at hcont1
      cases hcont1
      exact ⟨lenW, rfl, hlenLe⟩
    | some wr =>
      dsimp only at hcont1
      exact absurd hcont1 hnoRet

private theorem lookup_rlp_be_len :
    originalRuntimeCode.lookup (ofString "rlp_be_len") =
      some ([(ofString "v", .one)], sourceFnBody Guest.Software.guestFn_rlp_be_len, .one) :=
  lookup_of_guestAst_getElem 118 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_be_len) rfl

private theorem lookup_rlp_put_be :
    originalRuntimeCode.lookup (ofString "rlp_put_be") =
      some ([(ofString "dst", .one), (ofString "v", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_put_be, .one) :=
  lookup_of_guestAst_getElem 119 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_put_be) rfl

private theorem lookup_rlp_write_header :
    originalRuntimeCode.lookup (ofString "rlp_write_header") =
      some ([(ofString "dst", .one), (ofString "base", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_write_header, .one) :=
  lookup_of_guestAst_getElem 120 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_write_header) rfl

private theorem lookup_rlp_header_len :
    originalRuntimeCode.lookup (ofString "rlp_header_len") =
      some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_rlp_header_len, .one) :=
  lookup_of_guestAst_getElem 121 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_header_len) rfl

private theorem lookup_rlp_encode_bytes :
    originalRuntimeCode.lookup (ofString "rlp_encode_bytes") =
      some ([(ofString "dst", .one), (ofString "src", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_encode_bytes, .one) :=
  lookup_of_guestAst_getElem 122 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_encode_bytes) rfl

private theorem lookup_rlp_encode_word :
    originalRuntimeCode.lookup (ofString "rlp_encode_word") =
      some ([(ofString "dst", .one), (ofString "w", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_encode_word, .one) :=
  lookup_of_guestAst_getElem 123 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_encode_word) rfl

private theorem lookup_rlp_encode_list_header :
    originalRuntimeCode.lookup (ofString "rlp_encode_list_header") =
      some ([(ofString "dst", .one), (ofString "payload_len", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_encode_list_header, .one) :=
  lookup_of_guestAst_getElem 124 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_encode_list_header) rfl

private theorem lookup_rlp_list_header_len :
    originalRuntimeCode.lookup (ofString "rlp_list_header_len") =
      some ([(ofString "payload_len", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_list_header_len, .one) :=
  lookup_of_guestAst_getElem 126 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_list_header_len) rfl

private theorem lookup_rlp_put_u256 :
    originalRuntimeCode.lookup (ofString "rlp_put_u256") =
      some ([(ofString "dst", .one), (ofString "v", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_rlp_put_u256, .one) :=
  lookup_of_guestAst_getElem 228 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_put_u256) rfl

private theorem rlp_be_len_while_spec {F : Type}
    (k : Nat) (st : PanSemStateFiniteExact 64 F) (v n : BitVec 64)
    (hv : st.locals.lookup (ofString "v") = some (.val (.word v)))
    (hn : st.locals.lookup (ofString "n") = some (.val (.word n)))
    (hbound : v.toNat < 2 ^ (8 * k))
    (hclk : k ≤ st.clock) :
    let wprog : ProgHOL 64 :=
      .while (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64))
        (.seq
          (.assign .local (ofString "v")
            (.shift .lsr (.var .local (ofString "v")) (.const 8#64)))
          (.assign .local (ofString "n")
            (.op .add [.var .local (ofString "n"), .const 1#64])))
    st.clock ≤ (evaluateHOLFiniteState st wprog).2.clock + k ∧
      (evaluateHOLFiniteState st wprog).2.clock ≤ st.clock ∧
      (evaluateHOLFiniteState st wprog).1 = none ∧
      (evaluateHOLFiniteState st wprog).2.code = st.code ∧
      ∃ (n' : BitVec 64) (d : Nat), d ≤ k ∧ n' = n + BitVec.ofNat 64 d ∧
        (evaluateHOLFiniteState st wprog).2.locals.lookup (ofString "n") =
          some (.val (.word n')) := by
  induction k generalizing st v n with
  | zero =>
    intro wprog
    have hv0 : v = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      change v.toNat = 0
      omega
    subst hv0
    have hcond : @evalHOLExact 64 F _ st.toExact
        (fun a => Classical.propDecidable (st.memaddrs a))
        (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64)) =
        some (.val (.word 0#64)) := by
      simp [evalHOLExact, hv, Compiler.Encoders.Asm.wordCmpHOL]
    have hstep : evaluateHOLFiniteState st wprog = (none, st) := by
      simp [wprog, evaluateHOLFiniteState_while_total, hcond]
    rw [hstep]
    exact ⟨by omega, le_refl _, rfl, rfl, n, 0, le_refl _, by simp, hn⟩
  | succ m ih =>
    intro wprog
    by_cases hvz : v = 0#64
    · subst hvz
      have hcond : @evalHOLExact 64 F _ st.toExact
          (fun a => Classical.propDecidable (st.memaddrs a))
          (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64)) =
          some (.val (.word 0#64)) := by
        simp [evalHOLExact, hv, Compiler.Encoders.Asm.wordCmpHOL]
      have hstep : evaluateHOLFiniteState st wprog = (none, st) := by
        simp [wprog, evaluateHOLFiniteState_while_total, hcond]
      rw [hstep]
      exact ⟨by omega, le_refl _, rfl, rfl, n, 0, by omega, by simp, hn⟩
    · have hcond : @evalHOLExact 64 F _ st.toExact
          (fun a => Classical.propDecidable (st.memaddrs a))
          (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64)) =
          some (.val (.word 1#64)) := by
        simp [evalHOLExact, hv, Compiler.Encoders.Asm.wordCmpHOL, hvz]
      have hnz : st.clock ≠ 0 := by omega
      have hne_vn : ofString "v" ≠ ofString "n" := by decide
      have h8 : (8#64 : BitVec 64).toNat = 8 := rfl
      have hnotge8 : ¬ (64 ≤ (8#64 : BitVec 64).toNat) := by rw [h8]; omega
      let st1 := setVarHOLFinite (ofString "v") (.val (.word (v >>> (8#64).toNat)))
        (decClockHOLFinite st)
      have hv1 : evaluateHOLFiniteState (decClockHOLFinite st)
          (.assign .local (ofString "v")
            (.shift .lsr (.var .local (ofString "v")) (.const 8#64))) =
          (none, st1) := by
        have hvd : (decClockHOLFinite st).locals.lookup (ofString "v") =
            some (.val (.word v)) := hv
        simp [st1, evaluateHOLFiniteState_assign, evalHOLExact, hvd, wordShiftHOL, hnotge8,
          lookupKvarHOLExact, PanSemStateFiniteExact.isValidValueHOLFinite, isValidValueHOLExact,
          setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
      have hn1_lk : st1.locals.lookup (ofString "n") = some (.val (.word n)) := by
        simp [st1, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          hne_vn, hn]
      let st2 := setVarHOLFinite (ofString "n") (.val (.word (n + 1#64))) st1
      have hn2 : evaluateHOLFiniteState st1
          (.assign .local (ofString "n")
            (.op .add [.var .local (ofString "n"), .const 1#64])) =
          (none, st2) := by
        simp [st2, evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hn1_lk,
          wordOpHOL, wordOp, valueIsWord, valueWord, lookupKvarHOLExact,
          PanSemStateFiniteExact.isValidValueHOLFinite, isValidValueHOLExact,
          setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
      have hbodyStep : evaluateHOLFiniteState (decClockHOLFinite st)
          (.seq
            (.assign .local (ofString "v")
              (.shift .lsr (.var .local (ofString "v")) (.const 8#64)))
            (.assign .local (ofString "n")
              (.op .add [.var .local (ofString "n"), .const 1#64]))) =
          (none, st2) := by
        rw [evaluateHOLFiniteState_seq_line780, hv1]
        exact hn2
      have hwStep : evaluateHOLFiniteState st wprog = evaluateHOLFiniteState st2 wprog := by
        dsimp only [wprog]
        rw [evaluateHOLFiniteState_while_total]
        simp only [hcond, show (1#64 : BitVec 64) ≠ 0#64 by decide, if_true, hnz, if_false,
          fixClockHOLFinite_evaluateState]
        rw [hbodyStep]
      have hv_st2 : st2.locals.lookup (ofString "v") =
          some (.val (.word (v >>> (8#64).toNat))) := by
        simp [st2, st1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          Ne.symm hne_vn]
      have hn_st2 : st2.locals.lookup (ofString "n") = some (.val (.word (n + 1#64))) := by
        simp [st2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hv_shr : (v >>> (8#64).toNat).toNat < 2 ^ (8 * m) := by
        rw [h8, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
        have hp : 2 ^ (8 * (m + 1)) = 2 ^ 8 * 2 ^ (8 * m) := by
          rw [show 8 * (m + 1) = 8 + 8 * m by omega, Nat.pow_add]
        rw [hp] at hbound
        omega
      have hclk2 : m ≤ st2.clock := by
        change m ≤ st.clock - 1
        omega
      obtain ⟨ih1, ih2, ih3, ih4, n', d, hd, rfl, ihn⟩ :=
        ih st2 (v >>> (8#64).toNat) (n + 1#64) hv_st2 hn_st2 hv_shr hclk2
      rw [hwStep]
      change st.clock - 1 ≤ (evaluateHOLFiniteState st2 wprog).2.clock + m at ih1
      change (evaluateHOLFiniteState st2 wprog).2.clock ≤ st.clock - 1 at ih2
      refine ⟨by omega, by omega, ih3, ih4, n + 1#64 + BitVec.ofNat 64 d, d + 1, by omega, ?_, ihn⟩
      rw [BitVec.add_assoc]
      congr 1
      change BitVec.ofNat 64 1 + BitVec.ofNat 64 d = BitVec.ofNat 64 (d + 1)
      rw [← BitVec.ofNat_add, Nat.add_comm]

private theorem funBounded_rlp_be_len : FunBounded (ofString "rlp_be_len") 8 := by
  refine ⟨[(ofString "v", .one)], sourceFnBody Guest.Software.guestFn_rlp_be_len, .one,
    lookup_rlp_be_len, ?_⟩
  intro F state hcode hbudget
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_be_len,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply RunBounded.decConst
  unfold RunBounded
  let s1 := setVarHOLFinite (ofString "n") (.val (.word 0#64)) state
  let wbody : ProgHOL 64 :=
    .seq
      (.assign .local (ofString "v")
        (.shift .lsr (.var .local (ofString "v")) (.const 8#64)))
      (.assign .local (ofString "n")
        (.op .add [.var .local (ofString "n"), .const 1#64]))
  cases hv : s1.locals.lookup (ofString "v") with
  | none =>
    rw [evaluateHOLFiniteState_seq_line780]
    have hcond : @evalHOLExact 64 F _ s1.toExact
        (fun a => Classical.propDecidable (s1.memaddrs a))
        (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64)) = none := by
      simp [evalHOLExact, hv]
    have hstep : evaluateHOLFiniteState
        (setVarHOLFinite (ofString "n") (.val (.word 0#64)) state)
        (.while (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64)) wbody) =
        (some .error, s1) := by
      simp [s1, evaluateHOLFiniteState_while_total, hcond]
    rw [hstep]
    simp [s1, setVarHOLFinite]
  | some val =>
    cases val with
    | rStruct _ =>
      rw [evaluateHOLFiniteState_seq_line780]
      have hcond : @evalHOLExact 64 F _ s1.toExact
          (fun a => Classical.propDecidable (s1.memaddrs a))
          (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64)) = none := by
        simp [evalHOLExact, hv]
      have hstep : evaluateHOLFiniteState
          (setVarHOLFinite (ofString "n") (.val (.word 0#64)) state)
          (.while (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64)) wbody) =
          (some .error, s1) := by
        simp [s1, evaluateHOLFiniteState_while_total, hcond]
      rw [hstep]
      simp [s1, setVarHOLFinite]
    | nStruct _ _ =>
      rw [evaluateHOLFiniteState_seq_line780]
      have hcond : @evalHOLExact 64 F _ s1.toExact
          (fun a => Classical.propDecidable (s1.memaddrs a))
          (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64)) = none := by
        simp [evalHOLExact, hv]
      have hstep : evaluateHOLFiniteState
          (setVarHOLFinite (ofString "n") (.val (.word 0#64)) state)
          (.while (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64)) wbody) =
          (some .error, s1) := by
        simp [s1, evaluateHOLFiniteState_while_total, hcond]
      rw [hstep]
      simp [s1, setVarHOLFinite]
    | val wl =>
      cases wl with
      | word vw =>
        have hn1 : s1.locals.lookup (ofString "n") = some (.val (.word 0#64)) := by
          simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        obtain ⟨hw1, hw2, hw3, hw4, n', d, hd, rfl, hn'⟩ :=
          rlp_be_len_while_spec 8 s1 vw 0#64 hv hn1 vw.isLt hbudget
        rw [evaluateHOLFiniteState_seq_line780]
        cases hwRun : evaluateHOLFiniteState
            (setVarHOLFinite (ofString "n") (.val (.word 0#64)) state)
            (.while (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64)) wbody) with
        | mk wRes wMid =>
          have hwRun' : evaluateHOLFiniteState s1
              (.while (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64)) wbody) =
              (wRes, wMid) := hwRun
          rw [hwRun'] at hw1 hw2 hw3 hn'
          dsimp only at hw1 hw2 hw3 hn'
          subst hw3
          dsimp only
          have hret : evaluateHOLFiniteState wMid (.return (.var .local (ofString "n"))) =
              (some (.returned (.val (.word (0#64 + BitVec.ofNat 64 d)))),
                wMid.emptyLocalsHOLFinite) := by
            simp [evaluateHOLFiniteState_return, evalHOLExact, hn', shapeOfHOLExact]
          rw [hret]
          change state.clock ≤ wMid.clock + 8 at hw1
          change wMid.clock ≤ state.clock at hw2
          simp only [emptyLocalsHOLFinite, ne_eq, Option.some.injEq, reduceCtorEq, not_false_eq_true,
            and_true]
          exact ⟨hw1, hw2⟩

private theorem rlp_be_len_body_returns_le8 {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (retVal : ValueHOL 64)
    (hclk : 8 ≤ state.clock)
    (hrun : evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_rlp_be_len) =
      (some (.returned retVal), post)) :
    WordBound 8 retVal := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_be_len,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
    at hrun
  rw [evaluateHOLFiniteState_dec_total] at hrun
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true] at hrun
  have hrun1 := (Prod.mk.inj hrun).1
  clear hrun
  let s1 := setVarHOLFinite (ofString "n") (.val (.word 0#64)) state
  let wbody : ProgHOL 64 :=
    .seq
      (.assign .local (ofString "v")
        (.shift .lsr (.var .local (ofString "v")) (.const 8#64)))
      (.assign .local (ofString "n")
        (.op .add [.var .local (ofString "n"), .const 1#64]))
  cases hv : s1.locals.lookup (ofString "v") with
  | none =>
    rw [evaluateHOLFiniteState_seq_line780] at hrun1
    have hcond : @evalHOLExact 64 F _ s1.toExact
        (fun a => Classical.propDecidable (s1.memaddrs a))
        (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64)) = none := by
      simp [evalHOLExact, hv]
    have hstep : evaluateHOLFiniteState
        (setVarHOLFinite (ofString "n") (.val (.word 0#64)) state)
        (.while (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64)) wbody) =
        (some .error, s1) := by
      simp [s1, evaluateHOLFiniteState_while_total, hcond]
    rw [hstep] at hrun1
    simp at hrun1
  | some val =>
    cases val with
    | rStruct _ =>
      rw [evaluateHOLFiniteState_seq_line780] at hrun1
      have hcond : @evalHOLExact 64 F _ s1.toExact
          (fun a => Classical.propDecidable (s1.memaddrs a))
          (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64)) = none := by
        simp [evalHOLExact, hv]
      have hstep : evaluateHOLFiniteState
          (setVarHOLFinite (ofString "n") (.val (.word 0#64)) state)
          (.while (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64)) wbody) =
          (some .error, s1) := by
        simp [s1, evaluateHOLFiniteState_while_total, hcond]
      rw [hstep] at hrun1
      simp at hrun1
    | nStruct _ _ =>
      rw [evaluateHOLFiniteState_seq_line780] at hrun1
      have hcond : @evalHOLExact 64 F _ s1.toExact
          (fun a => Classical.propDecidable (s1.memaddrs a))
          (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64)) = none := by
        simp [evalHOLExact, hv]
      have hstep : evaluateHOLFiniteState
          (setVarHOLFinite (ofString "n") (.val (.word 0#64)) state)
          (.while (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64)) wbody) =
          (some .error, s1) := by
        simp [s1, evaluateHOLFiniteState_while_total, hcond]
      rw [hstep] at hrun1
      simp at hrun1
    | val wl =>
      cases wl with
      | word vw =>
        have hn1 : s1.locals.lookup (ofString "n") = some (.val (.word 0#64)) := by
          simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        obtain ⟨_, _, hw3, _, _, d, hd, rfl, hn'⟩ :=
          rlp_be_len_while_spec 8 s1 vw 0#64 hv hn1 vw.isLt hclk
        rw [evaluateHOLFiniteState_seq_line780] at hrun1
        cases hwRun : evaluateHOLFiniteState
            (setVarHOLFinite (ofString "n") (.val (.word 0#64)) state)
            (.while (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64)) wbody) with
        | mk wRes wMid =>
          rw [hwRun] at hrun1
          have hwRun' : evaluateHOLFiniteState s1
              (.while (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64)) wbody) =
              (wRes, wMid) := hwRun
          rw [hwRun'] at hw3 hn'
          dsimp only at hrun1 hw3 hn'
          subst hw3
          dsimp only at hrun1
          have hret : evaluateHOLFiniteState wMid (.return (.var .local (ofString "n"))) =
              (some (.returned (.val (.word (0#64 + BitVec.ofNat 64 d)))),
                wMid.emptyLocalsHOLFinite) := by
            simp [evaluateHOLFiniteState_return, evalHOLExact, hn', shapeOfHOLExact]
          rw [hret] at hrun1
          cases hrun1
          refine ⟨0#64 + BitVec.ofNat 64 d, rfl, ?_⟩
          simp only [BitVec.zero_add, BitVec.toNat_ofNat]
          omega

private theorem runBounded_rlp_put_be_body {F : Type}
    (state : PanSemStateFiniteExact 64 F) (K : BitVec 64)
    (hcode : state.code = originalRuntimeCode)
    (atN : state.locals.lookup (ofString "n") = some (.val (.word K)))
    (hbudget : K.toNat ≤ state.clock) :
    RunBounded state (sourceFnBody Guest.Software.guestFn_rlp_put_be) K.toNat := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_put_be,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  have hn_eval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) (.var .local (ofString "n")) =
      some (.val (.word K)) := by
    simp [evalHOLExact, atN]
  apply RunBounded.decWord state (ofString "i") (.var .local (ofString "n")) K hn_eval
  let s0 := setVarHOLFinite (ofString "i") (.val (.word K)) state
  have hs0_code : s0.code = originalRuntimeCode := hcode
  have hs0_i : s0.locals.lookup (ofString "i") = some (.val (.word K)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hdecBody : DecBody (ofString "i")
      (.seq
        (.assign .local (ofString "i")
          (.op .sub [.var .local (ofString "i"), .const 1#64]))
        (.seq
          (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
            (.var .local (ofString "v")))
          (.assign .local (ofString "v")
            (.shift .lsr (.var .local (ofString "v")) (.const 8#64))))) 0 :=
    DecBody.decrThen (ProgBounded.straight _ rfl) rfl rfl
  have hloop : RunBounded s0
      (.while (.cmp .lower (.const 0#64) (.var .local (ofString "i"))) _)
      (K.toNat * 1) :=
    downWhile_run (ofString "i") .lower (Or.inr rfl) hdecBody K.toNat
      (fun h => by cases h) s0 hs0_code K hs0_i (le_refl _)
      (by change K.toNat * 1 ≤ state.clock; omega)
  have hseq := RunBounded.seq (hloop.weaken (larger := K.toNat) (by omega))
    (tail := .return (.const 0#64))
    (b := 0) (by change K.toNat + 0 ≤ state.clock; omega)
    (fun next _ hnextCode hnextClk =>
      RunBounded.ofProg (ProgBounded.straight _ rfl) (hnextCode.trans hs0_code) hnextClk)
  exact hseq.weaken (by omega)

private theorem progBounded_rlp_put_be_exp (destination : Option (VarKind × MlS))
    (dst v sizeExp : ExpHOL 64) (K : BitVec 64)
    (heval : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) sizeExp =
        some (.val (.word K))) :
    ProgBounded (.call (some (destination, none)) (ofString "rlp_put_be") [dst, v, sizeExp])
      (K.toNat + 1) := by
  intro F state hcode hbudget
  cases hargs : evalListHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a)) [dst, v, sizeExp] with
  | none =>
    rw [evaluateHOLFiniteState_call, hargs]
    simp
  | some vs =>
    obtain ⟨v1, v2, rfl⟩ := evalListHOLFinite_three_word3 state dst v sizeExp K hargs (heval state)
    exact RunBounded.call hargs hbudget (fun body locals rs hfound => by
      rw [hcode] at hfound
      obtain ⟨rfl, hn⟩ := three_arg_lookup_third originalRuntimeCode.lookup
        (ofString "rlp_put_be") (ofString "dst") (ofString "v") (ofString "n")
        (sourceFnBody Guest.Software.guestFn_rlp_put_be)
        (by decide) (by decide) (by decide) lookup_rlp_put_be hfound
      exact runBounded_rlp_put_be_body (callEntryStateHOLFinite state locals) K hcode hn
        (by change K.toNat ≤ state.clock - 1; omega))

private theorem funBounded_rlp_write_header : FunBounded (ofString "rlp_write_header") 18 := by
  refine ⟨[(ofString "dst", .one), (ofString "base", .one), (ofString "n", .one)],
    sourceFnBody Guest.Software.guestFn_rlp_write_header, .one,
    lookup_rlp_write_header, ?_⟩
  intro F state hcode hbudget
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_write_header,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  have hite : RunBounded state
      (.ite (.cmp .notLower (.const 55#64) (.var .local (ofString "n")))
        (.seq
          (.storeByte (.var .local (ofString "dst"))
            (.op .add [.var .local (ofString "base"), .var .local (ofString "n")]))
          (.return (.const 1#64)))
        .skip) 0 :=
    RunBounded.ofProg
      (ProgBounded.iteMax _ (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl))
      hcode (by omega)
  refine (RunBounded.seq hite (b := 18) (by omega) ?_).weaken (by omega)
  intro next _ hnextCode hnextClk
  have hcode' : next.code = originalRuntimeCode := hnextCode.trans hcode
  cases hargs : evalListHOLFinite next
      (h := fun a => Classical.propDecidable (next.memaddrs a))
      [.var .local (ofString "n")] with
  | none =>
    unfold RunBounded
    rw [evaluateHOLFiniteState_decCall_total, hargs]
    simp
  | some vs =>
    refine RunBounded.weaken
      (RunBounded.decCall (bodyCost := 8) (tailCost := 9) hargs (by omega) ?_)
      (by omega)
    intro body locals rs hfound
    have hbody := lookupCodeHOLFinite_installed_body next.code.lookup (ofString "rlp_be_len")
      _ _ body _ rs vs locals (by rw [hcode']; exact lookup_rlp_be_len) hfound
    subst hbody
    have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata
      (callEntryStateHOLFinite next locals)
      (sourceFnBody Guest.Software.guestFn_rlp_be_len)
    have hbodyBound := ProgBounded.bodies_of_fun funBounded_rlp_be_len next hcode'
      (by omega) vs (sourceFnBody Guest.Software.guestFn_rlp_be_len) locals rs hfound
    refine ⟨hbodyBound, ?_⟩
    intro val post hran hpostClk
    rw [hran] at hmeta
    obtain ⟨llW, rfl, hllLe⟩ := rlp_be_len_body_returns_le8
      (callEntryStateHOLFinite next locals) post val
      (by change 8 ≤ next.clock - 1; omega) hran
    let s1 := setVarHOLFinite (ofString "ll") (.val (.word llW))
      {post with locals := next.locals}
    have hs1Code : s1.code = originalRuntimeCode := hmeta.1.trans hcode'
    have hll1 : s1.locals.lookup (ofString "ll") = some (.val (.word llW)) := by
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    change RunBounded s1 _ 9
    have hst : RunBounded s1
        (.storeByte (.var .local (ofString "dst"))
          (.op .add [.var .local (ofString "base"), .const 55#64,
            .var .local (ofString "ll")])) 0 :=
      RunBounded.ofProg (ProgBounded.straight _ rfl) hs1Code (by omega)
    refine (RunBounded.seq hst (b := 9) (by change 0 + 9 ≤ post.clock; omega) ?_).weaken
      (by omega)
    intro s2 hs2Run hs2Code hs2Clk
    have hframe2 := evaluate_avoidsLocal_flowing (ofString "ll")
      (.storeByte (.var .local (ofString "dst"))
        (.op .add [.var .local (ofString "base"), .const 55#64,
          .var .local (ofString "ll")])) rfl s1
    rw [hs2Run] at hframe2
    have hll2 : s2.locals.lookup (ofString "ll") = some (.val (.word llW)) :=
      (hframe2 (Or.inl rfl)).trans hll1
    have hs2Code' : s2.code = originalRuntimeCode := hs2Code.trans hs1Code
    have hcall : RunBounded s2
        (.call (some (none, none)) (ofString "rlp_put_be")
          [.op .add [.var .local (ofString "dst"), .const 1#64],
            .var .local (ofString "n"), .var .local (ofString "ll")])
        (llW.toNat + 1) := by
      cases hcArgs : evalListHOLFinite s2
          (h := fun a => Classical.propDecidable (s2.memaddrs a))
          [.op .add [.var .local (ofString "dst"), .const 1#64],
            .var .local (ofString "n"), .var .local (ofString "ll")] with
      | none =>
        unfold RunBounded
        rw [evaluateHOLFiniteState_call, hcArgs]
        simp
      | some cvs =>
        have hllEval : evalHOLFinite s2
            (h := fun a => Classical.propDecidable (s2.memaddrs a))
            (.var .local (ofString "ll")) = some (.val (.word llW)) := by
          rw [evalHOLFinite_eq_toExact]
          simp [evalHOLExact, hll2]
        obtain ⟨cv1, cv2, rfl⟩ := evalListHOLFinite_three_word3 s2 _ _ _ llW hcArgs hllEval
        exact RunBounded.call hcArgs (by omega) (fun cbody clocals crs chfound => by
          rw [hs2Code'] at chfound
          obtain ⟨rfl, chn⟩ := three_arg_lookup_third originalRuntimeCode.lookup
            (ofString "rlp_put_be") (ofString "dst") (ofString "v") (ofString "n")
            (sourceFnBody Guest.Software.guestFn_rlp_put_be)
            (by decide) (by decide) (by decide) lookup_rlp_put_be chfound
          exact runBounded_rlp_put_be_body (callEntryStateHOLFinite s2 clocals) llW hs2Code'
            chn (by change llW.toNat ≤ s2.clock - 1; omega))
    have hseq := RunBounded.seq (hcall.weaken (larger := 9) (by omega))
      (tail := .return (.op .add [.const 1#64, .var .local (ofString "ll")]))
      (b := 0) (by omega)
      (fun s3 _ hs3Code hs3Clk =>
        RunBounded.ofProg (ProgBounded.straight _ rfl) (hs3Code.trans hs2Code') hs3Clk)
    exact hseq.weaken (by omega)

private theorem rlp_write_header_body_returns_le9 {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (retVal : ValueHOL 64)
    (hcode : state.code = originalRuntimeCode)
    (hclk : 9 ≤ state.clock)
    (hrun : evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_rlp_write_header) =
      (some (.returned retVal), post)) :
    WordBound 9 retVal := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_write_header,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
    at hrun
  let iteProg : ProgHOL 64 :=
    .ite (.cmp .notLower (.const 55#64) (.var .local (ofString "n")))
      (.seq
        (.storeByte (.var .local (ofString "dst"))
          (.op .add [.var .local (ofString "base"), .var .local (ofString "n")]))
        (.return (.const 1#64)))
      .skip
  rw [evaluateHOLFiniteState_seq_line780] at hrun
  cases hiteRun : evaluateHOLFiniteState state iteProg with
  | mk iRes iMid =>
    rw [hiteRun] at hrun
    cases iRes with
    | some ir =>
      dsimp only at hrun
      cases hrun
      simp only [iteProg, evaluateHOLFiniteState_ite] at hiteRun
      split at hiteRun
      · split at hiteRun
        · rw [evaluateHOLFiniteState_skip] at hiteRun
          simp at hiteRun
        · rw [evaluateHOLFiniteState_seq_line780] at hiteRun
          cases hst : evaluateHOLFiniteState state
              (.storeByte (.var .local (ofString "dst"))
                (.op .add [.var .local (ofString "base"), .var .local (ofString "n")])) with
          | mk sRes sMid =>
            rw [hst] at hiteRun
            cases sRes with
            | none =>
              dsimp only at hiteRun
              have hret1 : evaluateHOLFiniteState sMid (.return (.const 1#64)) =
                  (some (.returned (.val (.word 1#64))), sMid.emptyLocalsHOLFinite) := by
                simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact]
              rw [hret1] at hiteRun
              cases hiteRun
              exact ⟨1#64, rfl, by decide⟩
            | some sr =>
              have hno := evaluate_noTopReturn
                (.storeByte (.var .local (ofString "dst"))
                  (.op .add [.var .local (ofString "base"), .var .local (ofString "n")]))
                rfl state retVal
              rw [hst] at hno
              dsimp only at hiteRun hno
              cases hiteRun
              exact absurd rfl hno
      · simp at hiteRun
    | none =>
      dsimp only at hrun
      have hmeta0 := PanRunBounded.evaluateHOLFiniteState_metadata state iteProg
      have hiteBound : RunBounded state iteProg 0 :=
        RunBounded.ofProg
          (ProgBounded.iteMax _ (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl))
          hcode (by omega)
      unfold RunBounded at hiteBound
      rw [hiteRun] at hmeta0 hiteBound
      dsimp only at hmeta0 hiteBound
      have hiCode : iMid.code = originalRuntimeCode := hmeta0.1.trans hcode
      have hiClk : 9 ≤ iMid.clock := by omega
      obtain ⟨vs, b, loc, rs, w, bPost, inner1, _, hlk, hbRun, hcont⟩ := decCall_returned_inv hrun
      have hbEq := lookupCodeHOLFinite_installed_body iMid.code.lookup (ofString "rlp_be_len")
        _ _ b _ rs vs loc (by rw [hiCode]; exact lookup_rlp_be_len) hlk
      subst hbEq
      obtain ⟨llW, rfl, hllLe⟩ := rlp_be_len_body_returns_le8
        (callEntryStateHOLFinite iMid loc) bPost w
        (by change 8 ≤ iMid.clock - 1; omega) hbRun
      let s1 := setVarHOLFinite (ofString "ll") (.val (.word llW))
        {bPost with locals := iMid.locals}
      have hll1 : s1.locals.lookup (ofString "ll") = some (.val (.word llW)) := by
        simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      let pfx : ProgHOL 64 :=
        .seq
          (.storeByte (.var .local (ofString "dst"))
            (.op .add [.var .local (ofString "base"), .const 55#64,
              .var .local (ofString "ll")]))
          (.call (some (none, none)) (ofString "rlp_put_be")
            [.op .add [.var .local (ofString "dst"), .const 1#64],
              .var .local (ofString "n"), .var .local (ofString "ll")])
      have hcont1 : (evaluateHOLFiniteState s1
          (.seq pfx (.return (.op .add [.const 1#64, .var .local (ofString "ll")])))).1 =
          some (.returned retVal) := by
        have heq : evaluateHOLFiniteState s1
            (.seq pfx (.return (.op .add [.const 1#64, .var .local (ofString "ll")]))) =
            evaluateHOLFiniteState
              (setVarHOLFinite (ofString "ll") (.val (.word llW)) {bPost with locals := iMid.locals})
              (.seq
                (.storeByte (.var .local (ofString "dst"))
                  (.op .add [.var .local (ofString "base"), .const 55#64,
                    .var .local (ofString "ll")]))
                (.seq
                  (.call (some (none, none)) (ofString "rlp_put_be")
                    [.op .add [.var .local (ofString "dst"), .const 1#64],
                      .var .local (ofString "n"), .var .local (ofString "ll")])
                  (.return (.op .add [.const 1#64, .var .local (ofString "ll")])))) := by
          change evaluateHOLFiniteState s1 (.seq pfx _) = _
          simp only [s1, pfx, evaluateHOLFiniteState_seq_line780]
          rcases evaluateHOLFiniteState
              (setVarHOLFinite (ofString "ll") (.val (.word llW)) {bPost with locals := iMid.locals})
              (.storeByte (.var .local (ofString "dst"))
                (.op .add [.var .local (ofString "base"), .const 55#64,
                  .var .local (ofString "ll")])) with ⟨_ | rA, mA⟩ <;> rfl
        rw [heq, hcont]
      have hframe := evaluate_avoidsLocal_flowing (ofString "ll") pfx rfl s1
      have hnoRet := evaluate_noTopReturn pfx rfl s1 retVal
      rw [evaluateHOLFiniteState_seq_line780] at hcont1
      cases hpRun : evaluateHOLFiniteState s1 pfx with
      | mk pRes pMid =>
        rw [hpRun] at hcont1 hframe hnoRet
        dsimp only at hcont1 hframe hnoRet
        cases pRes with
        | some pr => exact absurd hcont1 hnoRet
        | none =>
          dsimp only at hcont1
          have hllMid : pMid.locals.lookup (ofString "ll") = some (.val (.word llW)) :=
            (hframe (Or.inl rfl)).trans hll1
          have hretEq : evaluateHOLFiniteState pMid
              (.return (.op .add [.const 1#64, .var .local (ofString "ll")])) =
              (some (.returned (.val (.word (1#64 + llW)))), pMid.emptyLocalsHOLFinite) := by
            simp [evaluateHOLFiniteState_return, evalHOLExact, evalListHOLExact, hllMid,
              wordOpHOL, wordOp, valueIsWord, valueWord, shapeOfHOLExact]
          rw [hretEq] at hcont1
          cases hcont1
          refine ⟨1#64 + llW, rfl, ?_⟩
          have h264 : 2 ^ 64 = 18446744073709551616 := rfl
          have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
          rw [BitVec.toNat_add_of_lt (by omega), h1]
          omega

private theorem funBounded_rlp_header_len : FunBounded (ofString "rlp_header_len") 9 := by
  refine funBounded_of_guestAst 121 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_rlp_header_len 9 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_rlp_header_len,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.seq
      (ProgBounded.iteMax _ (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl))
      (ProgBounded.decCall funBounded_rlp_be_len _ _ _ (ProgBounded.straight _ rfl)))
    (by omega)

private theorem rlp_header_len_body_returns_le9 {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (retVal : ValueHOL 64)
    (hcode : state.code = originalRuntimeCode)
    (hclk : 9 ≤ state.clock)
    (hrun : evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_rlp_header_len) =
      (some (.returned retVal), post)) :
    WordBound 9 retVal := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_header_len,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
    at hrun
  let iteProg : ProgHOL 64 :=
    .ite (.cmp .notLower (.const 55#64) (.var .local (ofString "n")))
      (.return (.const 1#64))
      .skip
  rw [evaluateHOLFiniteState_seq_line780] at hrun
  cases hiteRun : evaluateHOLFiniteState state iteProg with
  | mk iRes iMid =>
    rw [hiteRun] at hrun
    cases iRes with
    | some ir =>
      dsimp only at hrun
      cases hrun
      simp only [iteProg, evaluateHOLFiniteState_ite] at hiteRun
      split at hiteRun
      · split at hiteRun
        · rw [evaluateHOLFiniteState_skip] at hiteRun
          simp at hiteRun
        · have hret1 : evaluateHOLFiniteState state (.return (.const 1#64)) =
              (some (.returned (.val (.word 1#64))), state.emptyLocalsHOLFinite) := by
            simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact]
          rw [hret1] at hiteRun
          cases hiteRun
          exact ⟨1#64, rfl, by decide⟩
      · simp at hiteRun
    | none =>
      dsimp only at hrun
      have hmeta0 := PanRunBounded.evaluateHOLFiniteState_metadata state iteProg
      have hiteBound : RunBounded state iteProg 0 :=
        RunBounded.ofProg
          (ProgBounded.iteMax _ (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl))
          hcode (by omega)
      unfold RunBounded at hiteBound
      rw [hiteRun] at hmeta0 hiteBound
      dsimp only at hmeta0 hiteBound
      have hiCode : iMid.code = originalRuntimeCode := hmeta0.1.trans hcode
      have hiClk : 9 ≤ iMid.clock := by omega
      obtain ⟨vs, b, loc, rs, w, bPost, inner1, _, hlk, hbRun, hcont⟩ := decCall_returned_inv hrun
      have hbEq := lookupCodeHOLFinite_installed_body iMid.code.lookup (ofString "rlp_be_len")
        _ _ b _ rs vs loc (by rw [hiCode]; exact lookup_rlp_be_len) hlk
      subst hbEq
      obtain ⟨llW, rfl, hllLe⟩ := rlp_be_len_body_returns_le8
        (callEntryStateHOLFinite iMid loc) bPost w
        (by change 8 ≤ iMid.clock - 1; omega) hbRun
      have hll : (setVarHOLFinite (ofString "ll") (.val (.word llW))
          {bPost with locals := iMid.locals}).locals.lookup (ofString "ll") =
          some (.val (.word llW)) := by
        simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hretEq : evaluateHOLFiniteState
          (setVarHOLFinite (ofString "ll") (.val (.word llW)) {bPost with locals := iMid.locals})
          (.return (.op .add [.const 1#64, .var .local (ofString "ll")])) =
          (some (.returned (.val (.word (1#64 + llW)))),
            (setVarHOLFinite (ofString "ll") (.val (.word llW))
              {bPost with locals := iMid.locals}).emptyLocalsHOLFinite) := by
        simp [evaluateHOLFiniteState_return, evalHOLExact, evalListHOLExact, hll,
          wordOpHOL, wordOp, valueIsWord, valueWord, shapeOfHOLExact]
      rw [hretEq] at hcont
      cases hcont
      refine ⟨1#64 + llW, rfl, ?_⟩
      have h264 : 2 ^ 64 = 18446744073709551616 := rfl
      have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
      rw [BitVec.toNat_add_of_lt (by omega), h1]
      omega

private theorem runBounded_rlp_encode_bytes_body {F : Type}
    (state : PanSemStateFiniteExact 64 F) (K : BitVec 64)
    (hsmall : K.toNat + 32 < 2 ^ 64)
    (hcode : state.code = originalRuntimeCode)
    (atN : state.locals.lookup (ofString "n") = some (.val (.word K)))
    (hbudget : K.toNat / 8 + 27 ≤ state.clock) :
    RunBounded state (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes)
      (K.toNat / 8 + 27) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_encode_bytes,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  let iteProg : ProgHOL 64 :=
    .ite (.cmp .equal (.var .local (ofString "n")) (.const 1#64))
      (.dec (ofString "b") .one (.loadByte (.var .local (ofString "src")))
        (.ite (.cmp .lower (.var .local (ofString "b")) (.const 128#64))
          (.seq
            (.storeByte (.var .local (ofString "dst")) (.var .local (ofString "b")))
            (.return (.const 1#64)))
          .skip))
      .skip
  have hite : RunBounded state iteProg 0 :=
    RunBounded.ofProg
      (ProgBounded.iteMax _
        (ProgBounded.dec _ _ _
          (ProgBounded.iteMax _ (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl)))
        (ProgBounded.straight _ rfl))
      hcode (by omega)
  refine (RunBounded.seq hite (b := K.toNat / 8 + 27) (by omega) ?_).weaken (by omega)
  intro next hiteRun hnextCode hnextClk
  have hframe0 := evaluate_avoidsLocal_flowing (ofString "n") iteProg rfl state
  rw [hiteRun] at hframe0
  have hnNext : next.locals.lookup (ofString "n") = some (.val (.word K)) :=
    (hframe0 (Or.inl rfl)).trans atN
  have hcode' : next.code = originalRuntimeCode := hnextCode.trans hcode
  cases hargs : evalListHOLFinite next
      (h := fun a => Classical.propDecidable (next.memaddrs a))
      [.var .local (ofString "dst"), .const 128#64, .var .local (ofString "n")] with
  | none =>
    unfold RunBounded
    rw [evaluateHOLFiniteState_decCall_total, hargs]
    simp
  | some vs =>
    refine RunBounded.weaken
      (RunBounded.decCall (bodyCost := 18) (tailCost := K.toNat / 8 + 8) hargs (by omega) ?_)
      (by omega)
    intro body locals rs hfound
    have hbody := lookupCodeHOLFinite_installed_body next.code.lookup
      (ofString "rlp_write_header") _ _ body _ rs vs locals
      (by rw [hcode']; exact lookup_rlp_write_header) hfound
    subst hbody
    have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata
      (callEntryStateHOLFinite next locals)
      (sourceFnBody Guest.Software.guestFn_rlp_write_header)
    have hbodyBound := ProgBounded.bodies_of_fun funBounded_rlp_write_header next hcode'
      (by omega) vs (sourceFnBody Guest.Software.guestFn_rlp_write_header) locals rs hfound
    refine ⟨hbodyBound, ?_⟩
    intro val post hran hpostClk
    rw [hran] at hmeta
    let s1 := setVarHOLFinite (ofString "h") val {post with locals := next.locals}
    have hs1Code : s1.code = originalRuntimeCode := hmeta.1.trans hcode'
    have hn1 : s1.locals.lookup (ofString "n") = some (.val (.word K)) := by
      have hne : ofString "h" ≠ ofString "n" := by decide
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hnNext]
    change RunBounded s1 _ (K.toNat / 8 + 8)
    have hmc : RunBounded s1
        (.call (some (none, none)) (ofString "memcpy")
          [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
            .var .local (ofString "src"), .var .local (ofString "n")])
        (K.toNat / 8 + 8) := by
      cases hmArgs : evalListHOLFinite s1
          (h := fun a => Classical.propDecidable (s1.memaddrs a))
          [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
            .var .local (ofString "src"), .var .local (ofString "n")] with
      | none =>
        unfold RunBounded
        rw [evaluateHOLFiniteState_call, hmArgs]
        simp
      | some mvs =>
        have hnEval : evalHOLFinite s1
            (h := fun a => Classical.propDecidable (s1.memaddrs a))
            (.var .local (ofString "n")) = some (.val (.word K)) := by
          rw [evalHOLFinite_eq_toExact]
          simp [evalHOLExact, hn1]
        obtain ⟨mv1, mv2, rfl⟩ := evalListHOLFinite_three_word3 s1 _ _ _ K hmArgs hnEval
        have hprog := progBounded_memcpy_const none
          (.op .add [.var .local (ofString "dst"), .var .local (ofString "h")])
          (.var .local (ofString "src")) K hsmall s1 hs1Code
          (by change K.toNat / 8 + 8 ≤ post.clock; omega)
        unfold RunBounded
        rw [evaluateHOLFiniteState_call, hmArgs]
        dsimp only
        have hmArgsConst : evalListHOLFinite s1
            (h := fun a => Classical.propDecidable (s1.memaddrs a))
            [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
              .var .local (ofString "src"), .const K] =
            some [mv1, mv2, .val (.word K)] := by
          rw [evalListHOLFinite_eq_toExact] at hmArgs ⊢
          rw [evalHOLFinite_eq_toExact] at hnEval
          simp only [evalListHOLExact] at hmArgs ⊢
          rw [hnEval] at hmArgs
          simpa [evalHOLExact] using hmArgs
        rw [evaluateHOLFiniteState_call, hmArgsConst] at hprog
        exact hprog
    have hseq := RunBounded.seq hmc
      (tail := .return (.op .add [.var .local (ofString "h"), .var .local (ofString "n")]))
      (b := 0) (by change K.toNat / 8 + 8 + 0 ≤ post.clock; omega)
      (fun s2 _ hs2Code hs2Clk =>
        RunBounded.ofProg (ProgBounded.straight _ rfl) (hs2Code.trans hs1Code) hs2Clk)
    exact hseq.weaken (by omega)

private theorem rlp_encode_bytes_body_returns_bound {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (K : BitVec 64) (retVal : ValueHOL 64)
    (hsmall : K.toNat + 32 < 2 ^ 64)
    (hcode : state.code = originalRuntimeCode)
    (atN : state.locals.lookup (ofString "n") = some (.val (.word K)))
    (hclk : 10 ≤ state.clock)
    (hrun : evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes) =
      (some (.returned retVal), post)) :
    WordBound (K.toNat + 9) retVal := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_encode_bytes,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
    at hrun
  let iteProg : ProgHOL 64 :=
    .ite (.cmp .equal (.var .local (ofString "n")) (.const 1#64))
      (.dec (ofString "b") .one (.loadByte (.var .local (ofString "src")))
        (.ite (.cmp .lower (.var .local (ofString "b")) (.const 128#64))
          (.seq
            (.storeByte (.var .local (ofString "dst")) (.var .local (ofString "b")))
            (.return (.const 1#64)))
          .skip))
      .skip
  rw [evaluateHOLFiniteState_seq_line780] at hrun
  cases hiteRun : evaluateHOLFiniteState state iteProg with
  | mk iRes iMid =>
    rw [hiteRun] at hrun
    cases iRes with
    | some ir =>
      dsimp only at hrun
      cases hrun
      simp only [iteProg, evaluateHOLFiniteState_ite] at hiteRun
      split at hiteRun
      · split at hiteRun
        · rw [evaluateHOLFiniteState_skip] at hiteRun
          simp at hiteRun
        · rw [evaluateHOLFiniteState_dec_total] at hiteRun
          dsimp only at hiteRun
          split at hiteRun
          · simp at hiteRun
          · rename_i bVal _
            split at hiteRun
            · let sb := setVarHOLFinite (ofString "b") bVal state
              cases hbRun : evaluateHOLFiniteState sb
                  (.ite (.cmp .lower (.var .local (ofString "b")) (.const 128#64))
                    (.seq
                      (.storeByte (.var .local (ofString "dst")) (.var .local (ofString "b")))
                      (.return (.const 1#64)))
                    .skip) with
              | mk bRes bMid =>
                rw [hbRun] at hiteRun
                dsimp only at hiteRun
                obtain ⟨hbr, _⟩ := Prod.mk.inj hiteRun
                subst hbr
                rw [evaluateHOLFiniteState_ite] at hbRun
                split at hbRun
                · split at hbRun
                  · rw [evaluateHOLFiniteState_skip] at hbRun
                    simp at hbRun
                  · rw [evaluateHOLFiniteState_seq_line780] at hbRun
                    cases hst : evaluateHOLFiniteState sb
                        (.storeByte (.var .local (ofString "dst"))
                          (.var .local (ofString "b"))) with
                    | mk sRes sMid =>
                      rw [hst] at hbRun
                      cases sRes with
                      | none =>
                        dsimp only at hbRun
                        have hret1 : evaluateHOLFiniteState sMid (.return (.const 1#64)) =
                            (some (.returned (.val (.word 1#64))),
                              sMid.emptyLocalsHOLFinite) := by
                          simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact]
                        rw [hret1] at hbRun
                        cases hbRun
                        exact ⟨1#64, rfl, by change 1 ≤ K.toNat + 9; omega⟩
                      | some sr =>
                        have hno := evaluate_noTopReturn
                          (.storeByte (.var .local (ofString "dst"))
                            (.var .local (ofString "b")))
                          rfl sb retVal
                        rw [hst] at hno
                        dsimp only at hbRun hno
                        cases hbRun
                        exact absurd rfl hno
                · simp at hbRun
            · simp at hiteRun
      · simp at hiteRun
    | none =>
      dsimp only at hrun
      have hmeta0 := PanRunBounded.evaluateHOLFiniteState_metadata state iteProg
      have hframe0 := evaluate_avoidsLocal_flowing (ofString "n") iteProg rfl state
      have hiteBound : RunBounded state iteProg 0 :=
        RunBounded.ofProg
          (ProgBounded.iteMax _
            (ProgBounded.dec _ _ _
              (ProgBounded.iteMax _ (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl)))
            (ProgBounded.straight _ rfl))
          hcode (by omega)
      unfold RunBounded at hiteBound
      rw [hiteRun] at hmeta0 hframe0 hiteBound
      dsimp only at hmeta0 hframe0 hiteBound
      have hiCode : iMid.code = originalRuntimeCode := hmeta0.1.trans hcode
      have hnMid : iMid.locals.lookup (ofString "n") = some (.val (.word K)) :=
        (hframe0 (Or.inl rfl)).trans atN
      have hiClk : 10 ≤ iMid.clock := by omega
      obtain ⟨vs, b, loc, rs, w, bPost, inner1, _, hlk, hbRun, hcont⟩ := decCall_returned_inv hrun
      have hbEq := lookupCodeHOLFinite_installed_body iMid.code.lookup
        (ofString "rlp_write_header") _ _ b _ rs vs loc
        (by rw [hiCode]; exact lookup_rlp_write_header) hlk
      subst hbEq
      obtain ⟨hW, rfl, hhLe⟩ := rlp_write_header_body_returns_le9
        (callEntryStateHOLFinite iMid loc) bPost w hiCode
        (by change 9 ≤ iMid.clock - 1; omega) hbRun
      let s1 := setVarHOLFinite (ofString "h") (.val (.word hW))
        {bPost with locals := iMid.locals}
      have hh1 : s1.locals.lookup (ofString "h") = some (.val (.word hW)) := by
        simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hn1 : s1.locals.lookup (ofString "n") = some (.val (.word K)) := by
        have hne : ofString "h" ≠ ofString "n" := by decide
        simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hnMid]
      let mcProg : ProgHOL 64 :=
        .call (some (none, none)) (ofString "memcpy")
          [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
            .var .local (ofString "src"), .var .local (ofString "n")]
      have hframeH := evaluate_avoidsLocal_flowing (ofString "h") mcProg rfl s1
      have hframeN := evaluate_avoidsLocal_flowing (ofString "n") mcProg rfl s1
      have hnoRet := evaluate_noTopReturn mcProg rfl s1 retVal
      rw [evaluateHOLFiniteState_seq_line780] at hcont
      cases hmcRun : evaluateHOLFiniteState
          (setVarHOLFinite (ofString "h") (.val (.word hW)) {bPost with locals := iMid.locals})
          mcProg with
      | mk mRes mMid =>
        rw [hmcRun] at hcont
        have hmcRun' : evaluateHOLFiniteState s1 mcProg = (mRes, mMid) := hmcRun
        rw [hmcRun'] at hframeH hframeN hnoRet
        dsimp only at hcont hframeH hframeN hnoRet
        cases mRes with
        | some mr =>
          cases hcont
          exact absurd rfl hnoRet
        | none =>
          dsimp only at hcont
          have hhM : mMid.locals.lookup (ofString "h") = some (.val (.word hW)) :=
            (hframeH (Or.inl rfl)).trans hh1
          have hnM : mMid.locals.lookup (ofString "n") = some (.val (.word K)) :=
            (hframeN (Or.inl rfl)).trans hn1
          have hretEq : evaluateHOLFiniteState mMid
              (.return (.op .add [.var .local (ofString "h"), .var .local (ofString "n")])) =
              (some (.returned (.val (.word (hW + K)))), mMid.emptyLocalsHOLFinite) := by
            simp [evaluateHOLFiniteState_return, evalHOLExact, evalListHOLExact, hhM, hnM,
              wordOpHOL, wordOp, valueIsWord, valueWord, shapeOfHOLExact]
          rw [hretEq] at hcont
          cases hcont
          refine ⟨hW + K, rfl, ?_⟩
          rw [BitVec.toNat_add_of_lt (by omega)]
          omega

private theorem progBounded_rlp_encode_bytes_exp (destination : Option (VarKind × MlS))
    (dst src sizeExp : ExpHOL 64) (K : BitVec 64) (hsmall : K.toNat + 32 < 2 ^ 64)
    (heval : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) sizeExp =
        some (.val (.word K))) :
    ProgBounded (.call (some (destination, none)) (ofString "rlp_encode_bytes")
      [dst, src, sizeExp]) (K.toNat / 8 + 28) := by
  intro F state hcode hbudget
  cases hargs : evalListHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a)) [dst, src, sizeExp] with
  | none =>
    rw [evaluateHOLFiniteState_call, hargs]
    simp
  | some vs =>
    obtain ⟨v1, v2, rfl⟩ :=
      evalListHOLFinite_three_word3 state dst src sizeExp K hargs (heval state)
    exact RunBounded.call hargs hbudget (fun body locals rs hfound => by
      rw [hcode] at hfound
      obtain ⟨rfl, hn⟩ := three_arg_lookup_third originalRuntimeCode.lookup
        (ofString "rlp_encode_bytes") (ofString "dst") (ofString "src") (ofString "n")
        (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes)
        (by decide) (by decide) (by decide) lookup_rlp_encode_bytes hfound
      exact runBounded_rlp_encode_bytes_body (callEntryStateHOLFinite state locals) K hsmall
        hcode hn (by change K.toNat / 8 + 27 ≤ state.clock - 1; omega))

private theorem funBounded_rlp_encode_word : FunBounded (ofString "rlp_encode_word") 18 := by
  refine ⟨[(ofString "dst", .one), (ofString "w", .one)],
    sourceFnBody Guest.Software.guestFn_rlp_encode_word, .one,
    lookup_rlp_encode_word, ?_⟩
  intro F state hcode hbudget
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_encode_word,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  have hite1 : RunBounded state
      (.ite (.cmp .equal (.var .local (ofString "w")) (.const 0#64))
        (.seq
          (.storeByte (.var .local (ofString "dst")) (.const 128#64))
          (.return (.const 1#64)))
        .skip) 0 :=
    RunBounded.ofProg
      (ProgBounded.iteMax _ (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl))
      hcode (by omega)
  refine (RunBounded.seq hite1 (b := 18) (by omega) ?_).weaken (by omega)
  intro n1 _ hn1Code hn1Clk
  have hcode1 : n1.code = originalRuntimeCode := hn1Code.trans hcode
  have hite2 : RunBounded n1
      (.ite (.cmp .lower (.var .local (ofString "w")) (.const 128#64))
        (.seq
          (.storeByte (.var .local (ofString "dst")) (.var .local (ofString "w")))
          (.return (.const 1#64)))
        .skip) 0 :=
    RunBounded.ofProg
      (ProgBounded.iteMax _ (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl))
      hcode1 (by omega)
  refine (RunBounded.seq hite2 (b := 18) (by omega) ?_).weaken (by omega)
  intro next _ hnextCode hnextClk
  have hcode' : next.code = originalRuntimeCode := hnextCode.trans hcode1
  cases hargs : evalListHOLFinite next
      (h := fun a => Classical.propDecidable (next.memaddrs a))
      [.var .local (ofString "w")] with
  | none =>
    unfold RunBounded
    rw [evaluateHOLFiniteState_decCall_total, hargs]
    simp
  | some vs =>
    refine RunBounded.weaken
      (RunBounded.decCall (bodyCost := 8) (tailCost := 9) hargs (by omega) ?_)
      (by omega)
    intro body locals rs hfound
    have hbody := lookupCodeHOLFinite_installed_body next.code.lookup (ofString "rlp_be_len")
      _ _ body _ rs vs locals (by rw [hcode']; exact lookup_rlp_be_len) hfound
    subst hbody
    have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata
      (callEntryStateHOLFinite next locals)
      (sourceFnBody Guest.Software.guestFn_rlp_be_len)
    have hbodyBound := ProgBounded.bodies_of_fun funBounded_rlp_be_len next hcode'
      (by omega) vs (sourceFnBody Guest.Software.guestFn_rlp_be_len) locals rs hfound
    refine ⟨hbodyBound, ?_⟩
    intro val post hran hpostClk
    rw [hran] at hmeta
    obtain ⟨llW, rfl, hllLe⟩ := rlp_be_len_body_returns_le8
      (callEntryStateHOLFinite next locals) post val
      (by change 8 ≤ next.clock - 1; omega) hran
    let s1 := setVarHOLFinite (ofString "ll") (.val (.word llW))
      {post with locals := next.locals}
    have hs1Code : s1.code = originalRuntimeCode := hmeta.1.trans hcode'
    have hll1 : s1.locals.lookup (ofString "ll") = some (.val (.word llW)) := by
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    change RunBounded s1 _ 9
    have hst : RunBounded s1
        (.storeByte (.var .local (ofString "dst"))
          (.op .add [.const 128#64, .var .local (ofString "ll")])) 0 :=
      RunBounded.ofProg (ProgBounded.straight _ rfl) hs1Code (by omega)
    refine (RunBounded.seq hst (b := 9) (by change 0 + 9 ≤ post.clock; omega) ?_).weaken
      (by omega)
    intro s2 hs2Run hs2Code hs2Clk
    have hframe2 := evaluate_avoidsLocal_flowing (ofString "ll")
      (.storeByte (.var .local (ofString "dst"))
        (.op .add [.const 128#64, .var .local (ofString "ll")])) rfl s1
    rw [hs2Run] at hframe2
    have hll2 : s2.locals.lookup (ofString "ll") = some (.val (.word llW)) :=
      (hframe2 (Or.inl rfl)).trans hll1
    have hs2Code' : s2.code = originalRuntimeCode := hs2Code.trans hs1Code
    have hcall : RunBounded s2
        (.call (some (none, none)) (ofString "rlp_put_be")
          [.op .add [.var .local (ofString "dst"), .const 1#64],
            .var .local (ofString "w"), .var .local (ofString "ll")])
        (llW.toNat + 1) := by
      cases hcArgs : evalListHOLFinite s2
          (h := fun a => Classical.propDecidable (s2.memaddrs a))
          [.op .add [.var .local (ofString "dst"), .const 1#64],
            .var .local (ofString "w"), .var .local (ofString "ll")] with
      | none =>
        unfold RunBounded
        rw [evaluateHOLFiniteState_call, hcArgs]
        simp
      | some cvs =>
        have hllEval : evalHOLFinite s2
            (h := fun a => Classical.propDecidable (s2.memaddrs a))
            (.var .local (ofString "ll")) = some (.val (.word llW)) := by
          rw [evalHOLFinite_eq_toExact]
          simp [evalHOLExact, hll2]
        obtain ⟨cv1, cv2, rfl⟩ := evalListHOLFinite_three_word3 s2 _ _ _ llW hcArgs hllEval
        exact RunBounded.call hcArgs (by omega) (fun cbody clocals crs chfound => by
          rw [hs2Code'] at chfound
          obtain ⟨rfl, chn⟩ := three_arg_lookup_third originalRuntimeCode.lookup
            (ofString "rlp_put_be") (ofString "dst") (ofString "v") (ofString "n")
            (sourceFnBody Guest.Software.guestFn_rlp_put_be)
            (by decide) (by decide) (by decide) lookup_rlp_put_be chfound
          exact runBounded_rlp_put_be_body (callEntryStateHOLFinite s2 clocals) llW hs2Code'
            chn (by change llW.toNat ≤ s2.clock - 1; omega))
    have hseq := RunBounded.seq (hcall.weaken (larger := 9) (by omega))
      (tail := .return (.op .add [.const 1#64, .var .local (ofString "ll")]))
      (b := 0) (by omega)
      (fun s3 _ hs3Code hs3Clk =>
        RunBounded.ofProg (ProgBounded.straight _ rfl) (hs3Code.trans hs2Code') hs3Clk)
    exact hseq.weaken (by omega)

private theorem rlp_encode_word_body_returns_le9 {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (retVal : ValueHOL 64)
    (hcode : state.code = originalRuntimeCode)
    (hclk : 9 ≤ state.clock)
    (hrun : evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_rlp_encode_word) =
      (some (.returned retVal), post)) :
    WordBound 9 retVal := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_encode_word,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
    at hrun
  have stepIte : ∀ {st stPost : PanSemStateFiniteExact 64 F} {cond : ExpHOL 64}
      {valExp : ExpHOL 64} {tail : ProgHOL 64},
      st.code = originalRuntimeCode →
      9 ≤ st.clock →
      evaluateHOLFiniteState st
        (.seq (.ite cond (.seq (.storeByte (.var .local (ofString "dst")) valExp)
            (.return (.const 1#64))) .skip) tail) =
        (some (.returned retVal), stPost) →
      WordBound 9 retVal ∨
        ∃ mid, mid.code = originalRuntimeCode ∧ 9 ≤ mid.clock ∧
          evaluateHOLFiniteState mid tail = (some (.returned retVal), stPost) := by
    intro st stPost cond valExp tail hstCode hstClk hseq
    let ip : ProgHOL 64 :=
      .ite cond (.seq (.storeByte (.var .local (ofString "dst")) valExp)
        (.return (.const 1#64))) .skip
    rw [evaluateHOLFiniteState_seq_line780] at hseq
    cases hi : evaluateHOLFiniteState st ip with
    | mk ir im =>
      rw [hi] at hseq
      cases ir with
      | some _ =>
        dsimp only at hseq
        cases hseq
        simp only [ip, evaluateHOLFiniteState_ite] at hi
        split at hi
        · split at hi
          · rw [evaluateHOLFiniteState_skip] at hi
            simp at hi
          · rw [evaluateHOLFiniteState_seq_line780] at hi
            cases hst : evaluateHOLFiniteState st
                (.storeByte (.var .local (ofString "dst")) valExp) with
            | mk sr sm =>
              rw [hst] at hi
              cases sr with
              | none =>
                dsimp only at hi
                have hr1 : evaluateHOLFiniteState sm (.return (.const 1#64)) =
                    (some (.returned (.val (.word 1#64))), sm.emptyLocalsHOLFinite) := by
                  simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact]
                rw [hr1] at hi
                cases hi
                exact Or.inl ⟨1#64, rfl, by decide⟩
              | some _ =>
                have hno := evaluate_noTopReturn
                  (.storeByte (.var .local (ofString "dst")) valExp) rfl st retVal
                rw [hst] at hno
                dsimp only at hi hno
                cases hi
                exact absurd rfl hno
        · simp at hi
      | none =>
        dsimp only at hseq
        have hm := PanRunBounded.evaluateHOLFiniteState_metadata st ip
        have hb : RunBounded st ip 0 :=
          RunBounded.ofProg
            (ProgBounded.iteMax _ (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl))
            hstCode (by omega)
        unfold RunBounded at hb
        rw [hi] at hm hb
        dsimp only at hm hb
        exact Or.inr ⟨im, hm.1.trans hstCode, by omega, hseq⟩
  rcases stepIte hcode hclk hrun with h | ⟨m1, hm1Code, hm1Clk, hrun2⟩
  · exact h
  · rcases stepIte hm1Code hm1Clk hrun2 with h | ⟨iMid, hiCode, hiClk, hrun3⟩
    · exact h
    · obtain ⟨vs, b, loc, rs, w, bPost, inner1, _, hlk, hbRun, hcont⟩ := decCall_returned_inv hrun3
      have hbEq := lookupCodeHOLFinite_installed_body iMid.code.lookup (ofString "rlp_be_len")
        _ _ b _ rs vs loc (by rw [hiCode]; exact lookup_rlp_be_len) hlk
      subst hbEq
      obtain ⟨llW, rfl, hllLe⟩ := rlp_be_len_body_returns_le8
        (callEntryStateHOLFinite iMid loc) bPost w
        (by change 8 ≤ iMid.clock - 1; omega) hbRun
      let s1 := setVarHOLFinite (ofString "ll") (.val (.word llW))
        {bPost with locals := iMid.locals}
      have hll1 : s1.locals.lookup (ofString "ll") = some (.val (.word llW)) := by
        simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      let pfx : ProgHOL 64 :=
        .seq
          (.storeByte (.var .local (ofString "dst"))
            (.op .add [.const 128#64, .var .local (ofString "ll")]))
          (.call (some (none, none)) (ofString "rlp_put_be")
            [.op .add [.var .local (ofString "dst"), .const 1#64],
              .var .local (ofString "w"), .var .local (ofString "ll")])
      have hcont1 : (evaluateHOLFiniteState s1
          (.seq pfx (.return (.op .add [.const 1#64, .var .local (ofString "ll")])))).1 =
          some (.returned retVal) := by
        have heq : evaluateHOLFiniteState s1
            (.seq pfx (.return (.op .add [.const 1#64, .var .local (ofString "ll")]))) =
            evaluateHOLFiniteState
              (setVarHOLFinite (ofString "ll") (.val (.word llW)) {bPost with locals := iMid.locals})
              (.seq
                (.storeByte (.var .local (ofString "dst"))
                  (.op .add [.const 128#64, .var .local (ofString "ll")]))
                (.seq
                  (.call (some (none, none)) (ofString "rlp_put_be")
                    [.op .add [.var .local (ofString "dst"), .const 1#64],
                      .var .local (ofString "w"), .var .local (ofString "ll")])
                  (.return (.op .add [.const 1#64, .var .local (ofString "ll")])))) := by
          change evaluateHOLFiniteState s1 (.seq pfx _) = _
          simp only [s1, pfx, evaluateHOLFiniteState_seq_line780]
          rcases evaluateHOLFiniteState
              (setVarHOLFinite (ofString "ll") (.val (.word llW)) {bPost with locals := iMid.locals})
              (.storeByte (.var .local (ofString "dst"))
                (.op .add [.const 128#64, .var .local (ofString "ll")])) with ⟨_ | rA, mA⟩ <;> rfl
        rw [heq, hcont]
      have hframe := evaluate_avoidsLocal_flowing (ofString "ll") pfx rfl s1
      have hnoRet := evaluate_noTopReturn pfx rfl s1 retVal
      rw [evaluateHOLFiniteState_seq_line780] at hcont1
      cases hpRun : evaluateHOLFiniteState s1 pfx with
      | mk pRes pMid =>
        rw [hpRun] at hcont1 hframe hnoRet
        dsimp only at hcont1 hframe hnoRet
        cases pRes with
        | some pr => exact absurd hcont1 hnoRet
        | none =>
          dsimp only at hcont1
          have hllMid : pMid.locals.lookup (ofString "ll") = some (.val (.word llW)) :=
            (hframe (Or.inl rfl)).trans hll1
          have hretEq : evaluateHOLFiniteState pMid
              (.return (.op .add [.const 1#64, .var .local (ofString "ll")])) =
              (some (.returned (.val (.word (1#64 + llW)))), pMid.emptyLocalsHOLFinite) := by
            simp [evaluateHOLFiniteState_return, evalHOLExact, evalListHOLExact, hllMid,
              wordOpHOL, wordOp, valueIsWord, valueWord, shapeOfHOLExact]
          rw [hretEq] at hcont1
          cases hcont1
          refine ⟨1#64 + llW, rfl, ?_⟩
          have h264 : 2 ^ 64 = 18446744073709551616 := rfl
          have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
          rw [BitVec.toNat_add_of_lt (by omega), h1]
          omega

private theorem funBounded_rlp_encode_list_header :
    FunBounded (ofString "rlp_encode_list_header") 19 := by
  refine funBounded_of_guestAst 124 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_rlp_encode_list_header 19 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_rlp_encode_list_header,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.tail funBounded_rlp_write_header _

private theorem funBounded_rlp_list_header_len :
    FunBounded (ofString "rlp_list_header_len") 10 := by
  refine funBounded_of_guestAst 126 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_rlp_list_header_len 10 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_rlp_list_header_len,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.tail funBounded_rlp_header_len _

private theorem rlp_list_header_len_body_returns_le9 {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (retVal : ValueHOL 64)
    (hcode : state.code = originalRuntimeCode)
    (hclk : 10 ≤ state.clock)
    (hrun : evaluateHOLFiniteState state
      (sourceFnBody Guest.Software.guestFn_rlp_list_header_len) =
      (some (.returned retVal), post)) :
    WordBound 9 retVal := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_list_header_len,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
    at hrun
  obtain ⟨vs, b, loc, rs, bPost, _, hlk, hbRun⟩ := tailCall_returned_inv hrun
  have hbEq := lookupCodeHOLFinite_installed_body state.code.lookup (ofString "rlp_header_len")
    _ _ b _ rs vs loc (by rw [hcode]; exact lookup_rlp_header_len) hlk
  subst hbEq
  exact rlp_header_len_body_returns_le9 (callEntryStateHOLFinite state loc) bPost retVal
    hcode (by change 9 ≤ state.clock - 1; omega) hbRun

private theorem funBounded_rlp_put_u256 : FunBounded (ofString "rlp_put_u256") 107 := by
  refine funBounded_of_guestAst 228 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_rlp_put_u256 107 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_rlp_put_u256,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine ProgBounded.weaken
    (ProgBounded.decCall funBounded_heap_mark _ _ _
      (ProgBounded.decCall (tailCost := 104) funBounded_alloc _ _ _ ?_))
    (by omega)
  intro F state hcode hbudget
  cases hargs : evalListHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "v"), .var .local (ofString "tmp")] with
  | none =>
    rw [evaluateHOLFiniteState_decCall_args_none state (ofString "n") .one
      (ofString "u256_to_be_min") [.var .local (ofString "v"), .var .local (ofString "tmp")] _
      hargs]
    simp
  | some vs =>
    refine RunBounded.weaken
      (RunBounded.decCall (bodyCost := 70) (tailCost := 33) hargs (by omega) ?_)
      (by omega)
    intro body locals rs hfound
    have hbEq := lookupCodeHOLFinite_installed_body state.code.lookup
      (ofString "u256_to_be_min") _ _ body _ rs vs locals
      (by rw [hcode]; exact lookup_u256_to_be_min) hfound
    subst hbEq
    have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata
      (callEntryStateHOLFinite state locals)
      (sourceFnBody Guest.Software.guestFn_u256_to_be_min)
    have hbodyBound := ProgBounded.bodies_of_fun funBounded_u256_to_be_min state hcode
      (by omega) vs (sourceFnBody Guest.Software.guestFn_u256_to_be_min) locals rs hfound
    refine ⟨hbodyBound, ?_⟩
    intro val post hran hpostClk
    rw [hran] at hmeta
    obtain ⟨nW, rfl, hnLe⟩ :=
      u256_to_be_min_body_returns_le32 (callEntryStateHOLFinite state locals) post val hcode hran
    let s1 := setVarHOLFinite (ofString "n") (.val (.word nW)) {post with locals := state.locals}
    have hs1Code : s1.code = originalRuntimeCode := hmeta.1.trans hcode
    have hn1 : s1.locals.lookup (ofString "n") = some (.val (.word nW)) := by
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    change RunBounded s1 _ 33
    cases heArgs : evalListHOLFinite s1
        (h := fun a => Classical.propDecidable (s1.memaddrs a))
        [.var .local (ofString "dst"), .var .local (ofString "tmp"),
          .var .local (ofString "n")] with
    | none =>
      unfold RunBounded
      rw [evaluateHOLFiniteState_decCall_total, heArgs]
      simp
    | some evs =>
      have hnEval : evalHOLFinite s1
          (h := fun a => Classical.propDecidable (s1.memaddrs a))
          (.var .local (ofString "n")) = some (.val (.word nW)) := by
        rw [evalHOLFinite_eq_toExact]
        simp [evalHOLExact, hn1]
      obtain ⟨ev1, ev2, rfl⟩ := evalListHOLFinite_three_word3 s1 _ _ _ nW heArgs hnEval
      refine RunBounded.weaken
        (RunBounded.decCall (bodyCost := nW.toNat / 8 + 27) (tailCost := 1) heArgs
          (by change nW.toNat / 8 + 27 + 1 + 1 ≤ post.clock; omega) ?_)
        (by omega)
      intro ebody elocals ers ehfound
      have heb_tmp : s1.code = originalRuntimeCode := hs1Code
      rw [heb_tmp] at ehfound
      obtain ⟨rfl, ehn⟩ := three_arg_lookup_third originalRuntimeCode.lookup
        (ofString "rlp_encode_bytes") (ofString "dst") (ofString "src") (ofString "n")
        (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes)
        (by decide) (by decide) (by decide) lookup_rlp_encode_bytes ehfound
      have heMeta := PanRunBounded.evaluateHOLFiniteState_metadata
        (callEntryStateHOLFinite s1 elocals)
        (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes)
      have hnSmall : nW.toNat + 32 < 2 ^ 64 := by
        have h264 : 2 ^ 64 = 18446744073709551616 := rfl
        omega
      refine ⟨runBounded_rlp_encode_bytes_body (callEntryStateHOLFinite s1 elocals) nW
        hnSmall hs1Code ehn (by change nW.toNat / 8 + 27 ≤ post.clock - 1; omega), ?_⟩
      intro wVal wPost hwRun hwClk
      rw [hwRun] at heMeta
      let s2 := setVarHOLFinite (ofString "w") wVal {wPost with locals := s1.locals}
      have hs2Code : s2.code = originalRuntimeCode := heMeta.1.trans hs1Code
      exact RunBounded.ofProg
        (ProgBounded.weaken
          (ProgBounded.seq (ProgBounded.call funBounded_heap_release _ _)
            (ProgBounded.straight _ rfl))
          (by omega))
        hs2Code hwClk

private theorem rlp_put_u256_body_returns_le41 {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (retVal : ValueHOL 64)
    (hcode : state.code = originalRuntimeCode)
    (hclk : 85 ≤ state.clock)
    (hrun : evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_rlp_put_u256) =
      (some (.returned retVal), post)) :
    WordBound 41 retVal := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_put_u256,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
    at hrun
  obtain ⟨vs1, b1, loc1, rs1, markVal, p1, in1, _, hlk1, hb1, hc1⟩ := decCall_returned_inv hrun
  have hm1 := PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state loc1) b1
  have hbd1 : RunBounded (callEntryStateHOLFinite state loc1) b1 0 :=
    ProgBounded.bodies_of_fun funBounded_heap_mark state hcode (by omega)
      vs1 b1 loc1 rs1 hlk1
  unfold RunBounded at hbd1
  rw [hb1] at hm1 hbd1
  dsimp only at hm1 hbd1
  let st1 := setVarHOLFinite (ofString "mark") markVal {p1 with locals := state.locals}
  have hst1Code : st1.code = originalRuntimeCode := hm1.1.trans hcode
  have hst1Clk : 84 ≤ st1.clock := by
    have hsp := hbd1.1
    change state.clock - 1 ≤ p1.clock + 0 at hsp
    change 84 ≤ p1.clock
    omega
  obtain ⟨vs2, b2, loc2, rs2, tmpVal, p2, in2, _, hlk2, hb2, hc2⟩ := decCall_returned_inv hc1
  have hm2 := PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite st1 loc2) b2
  have hbd2 : RunBounded (callEntryStateHOLFinite st1 loc2) b2 1 :=
    ProgBounded.bodies_of_fun funBounded_alloc st1 hst1Code (by omega)
      vs2 b2 loc2 rs2 hlk2
  unfold RunBounded at hbd2
  rw [hb2] at hm2 hbd2
  dsimp only at hm2 hbd2
  let st2 := setVarHOLFinite (ofString "tmp") tmpVal {p2 with locals := st1.locals}
  have hst2Code : st2.code = originalRuntimeCode := hm2.1.trans hst1Code
  have hst2Clk : 82 ≤ st2.clock := by
    have hsp := hbd2.1
    change st1.clock - 1 ≤ p2.clock + 1 at hsp
    change 82 ≤ p2.clock
    omega
  obtain ⟨vs3, b3, loc3, rs3, nVal, p3, in3, _, hlk3, hb3, hc3⟩ := decCall_returned_inv hc2
  have hb3Eq := lookupCodeHOLFinite_installed_body st2.code.lookup
    (ofString "u256_to_be_min") _ _ b3 _ rs3 vs3 loc3
    (by rw [hst2Code]; exact lookup_u256_to_be_min) hlk3
  subst hb3Eq
  have hm3 := PanRunBounded.evaluateHOLFiniteState_metadata
    (callEntryStateHOLFinite st2 loc3) (sourceFnBody Guest.Software.guestFn_u256_to_be_min)
  have hbd3 : RunBounded (callEntryStateHOLFinite st2 loc3)
      (sourceFnBody Guest.Software.guestFn_u256_to_be_min) 70 :=
    ProgBounded.bodies_of_fun funBounded_u256_to_be_min st2 hst2Code (by omega)
      vs3 (sourceFnBody Guest.Software.guestFn_u256_to_be_min) loc3 rs3 hlk3
  unfold RunBounded at hbd3
  rw [hb3] at hm3 hbd3
  dsimp only at hm3 hbd3
  obtain ⟨nW, rfl, hnLe⟩ :=
    u256_to_be_min_body_returns_le32 (callEntryStateHOLFinite st2 loc3) p3 nVal hst2Code hb3
  let st3 := setVarHOLFinite (ofString "n") (.val (.word nW)) {p3 with locals := st2.locals}
  have hst3Code : st3.code = originalRuntimeCode := hm3.1.trans hst2Code
  have hst3Clk : 11 ≤ st3.clock := by
    have hsp := hbd3.1
    change st2.clock - 1 ≤ p3.clock + 70 at hsp
    change 11 ≤ p3.clock
    omega
  have hn3 : st3.locals.lookup (ofString "n") = some (.val (.word nW)) := by
    simp [st3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  obtain ⟨vs4, b4, loc4, rs4, wVal, p4, in4, hargs4, hlk4, hb4, hc4⟩ := decCall_returned_inv hc3
  have hnEval3 : evalHOLFinite st3
      (h := fun a => Classical.propDecidable (st3.memaddrs a))
      (.var .local (ofString "n")) = some (.val (.word nW)) := by
    rw [evalHOLFinite_eq_toExact]
    simp [evalHOLExact, hn3]
  obtain ⟨ev1, ev2, rfl⟩ := evalListHOLFinite_three_word3 st3 _ _ _ nW hargs4 hnEval3
  have hlk4' : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "rlp_encode_bytes") [ev1, ev2, .val (.word nW)] = some (b4, loc4, rs4) := by
    rw [← hst3Code]
    exact hlk4
  obtain ⟨rfl, hnLoc4⟩ := three_arg_lookup_third originalRuntimeCode.lookup
    (ofString "rlp_encode_bytes") (ofString "dst") (ofString "src") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes)
    (by decide) (by decide) (by decide) lookup_rlp_encode_bytes hlk4'
  have hnSmall : nW.toNat + 32 < 2 ^ 64 := by
    have h264 : 2 ^ 64 = 18446744073709551616 := rfl
    omega
  obtain ⟨wW, rfl, hwLe⟩ := rlp_encode_bytes_body_returns_bound
    (callEntryStateHOLFinite st3 loc4) p4 nW wVal hnSmall hst3Code hnLoc4
    (by change 10 ≤ st3.clock - 1; omega) hb4
  let st4 := setVarHOLFinite (ofString "w") (.val (.word wW)) {p4 with locals := st3.locals}
  have hw4 : st4.locals.lookup (ofString "w") = some (.val (.word wW)) := by
    simp [st4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  let relProg : ProgHOL 64 :=
    .call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")]
  have hframeW := evaluate_avoidsLocal_flowing (ofString "w") relProg rfl st4
  have hnoRetW := evaluate_noTopReturn relProg rfl st4 retVal
  rw [evaluateHOLFiniteState_seq_line780] at hc4
  cases hrelRun : evaluateHOLFiniteState
      (setVarHOLFinite (ofString "w") (.val (.word wW)) {p4 with locals := st3.locals})
      relProg with
  | mk rRes rMid =>
    rw [hrelRun] at hc4
    have hrelRun' : evaluateHOLFiniteState st4 relProg = (rRes, rMid) := hrelRun
    rw [hrelRun'] at hframeW hnoRetW
    dsimp only at hc4 hframeW hnoRetW
    cases rRes with
    | some _ =>
      cases hc4
      exact absurd rfl hnoRetW
    | none =>
      dsimp only at hc4
      have hwMid : rMid.locals.lookup (ofString "w") = some (.val (.word wW)) :=
        (hframeW (Or.inl rfl)).trans hw4
      have hretEq : evaluateHOLFiniteState rMid (.return (.var .local (ofString "w"))) =
          (some (.returned (.val (.word wW))), rMid.emptyLocalsHOLFinite) := by
        simp [evaluateHOLFiniteState_return, evalHOLExact, hwMid, shapeOfHOLExact]
      rw [hretEq] at hc4
      cases hc4
      exact ⟨wW, rfl, by omega⟩

end InitECandidate.Solver.GuestBoundEvmInterpreter
