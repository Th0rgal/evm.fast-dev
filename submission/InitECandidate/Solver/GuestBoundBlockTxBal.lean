import InitECandidate.Solver.PanRunBoundedExt

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace InitECandidate.Solver.GuestBoundBlockTxBal

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.PanRunBoundedExt

/-! ## Section 1: Structural Loop Combinators -/

mutual

def expLocalsAvoided : ExpHOL 64 → ProgHOL 64 → Bool
  | .const _, _ => true
  | .var .local name, p => avoidsLocal name p
  | .rfield _ inner, p => expLocalsAvoided inner p
  | .cmp _ a b, p => expLocalsAvoided a p && expLocalsAvoided b p
  | .shift _ a b, p => expLocalsAvoided a p && expLocalsAvoided b p
  | .op _ args, p => expListLocalsAvoided args p
  | .panop _ args, p => expListLocalsAvoided args p
  | .rstruct args, p => expListLocalsAvoided args p
  | .nfield _ _, _ | .nstruct _ _, _
  | .var .global _, _ | .baseAddr, _ | .topAddr, _ | .bytesInWord, _
  | .load _ _, _ | .loadByte _, _ | .load32 _, _ => false
termination_by structural e _ => e

def expListLocalsAvoided : List (ExpHOL 64) → ProgHOL 64 → Bool
  | [], _ => true
  | e :: es, p => expLocalsAvoided e p && expListLocalsAvoided es p
termination_by structural es _ => es

end

mutual

private theorem evalHOLExact_eq_of_expLocalsAvoided {F : Type}
    (s1 s2 : PanSemStateFiniteExact 64 F) (p : ProgHOL 64)
    (heq : ∀ k, avoidsLocal k p = true → s1.locals.lookup k = s2.locals.lookup k) :
    (e : ExpHOL 64) → expLocalsAvoided e p = true →
      @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a)) e =
      @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a)) e
  | .const _, _ => rfl
  | .var .local name, ha => by
    simp only [expLocalsAvoided] at ha
    simp only [evalHOLExact]
    exact heq name ha
  | .var .global _, ha | .nfield _ _, ha | .nstruct _ _, ha
  | .baseAddr, ha | .topAddr, ha | .bytesInWord, ha
  | .load _ _, ha | .loadByte _, ha | .load32 _, ha => by simp [expLocalsAvoided] at ha
  | .rfield idx inner, ha => by
    simp only [expLocalsAvoided] at ha
    simp only [evalHOLExact, evalHOLExact_eq_of_expLocalsAvoided s1 s2 p heq inner ha]
  | .cmp cop a b, ha => by
    simp only [expLocalsAvoided, Bool.and_eq_true] at ha
    simp only [evalHOLExact,
      evalHOLExact_eq_of_expLocalsAvoided s1 s2 p heq a ha.1,
      evalHOLExact_eq_of_expLocalsAvoided s1 s2 p heq b ha.2]
  | .shift sh a b, ha => by
    simp only [expLocalsAvoided, Bool.and_eq_true] at ha
    simp only [evalHOLExact,
      evalHOLExact_eq_of_expLocalsAvoided s1 s2 p heq a ha.1,
      evalHOLExact_eq_of_expLocalsAvoided s1 s2 p heq b ha.2]
  | .op bop args, ha => by
    simp only [expLocalsAvoided] at ha
    simp only [evalHOLExact, evalListHOLExact_eq_of_expLocalsAvoided s1 s2 p heq args ha]
  | .panop pop args, ha => by
    simp only [expLocalsAvoided] at ha
    simp only [evalHOLExact, evalListHOLExact_eq_of_expLocalsAvoided s1 s2 p heq args ha]
  | .rstruct args, ha => by
    simp only [expLocalsAvoided] at ha
    simp only [evalHOLExact, evalListHOLExact_eq_of_expLocalsAvoided s1 s2 p heq args ha]
termination_by structural e => e

private theorem evalListHOLExact_eq_of_expLocalsAvoided {F : Type}
    (s1 s2 : PanSemStateFiniteExact 64 F) (p : ProgHOL 64)
    (heq : ∀ k, avoidsLocal k p = true → s1.locals.lookup k = s2.locals.lookup k) :
    (es : List (ExpHOL 64)) → expListLocalsAvoided es p = true →
      @evalListHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a)) es =
      @evalListHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a)) es
  | [], _ => rfl
  | e :: es, ha => by
    simp only [expListLocalsAvoided, Bool.and_eq_true] at ha
    simp only [evalListHOLExact,
      evalHOLExact_eq_of_expLocalsAvoided s1 s2 p heq e ha.1,
      evalListHOLExact_eq_of_expLocalsAvoided s1 s2 p heq es ha.2]
termination_by structural es => es

end

theorem evalHOLFinite_eq_of_expLocalsAvoided {F : Type}
    (s1 s2 : PanSemStateFiniteExact 64 F) (p : ProgHOL 64)
    (heq : ∀ k, avoidsLocal k p = true → s1.locals.lookup k = s2.locals.lookup k)
    (e : ExpHOL 64) (ha : expLocalsAvoided e p = true) :
    evalHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a)) e =
    evalHOLFinite s2 (h := fun a => Classical.propDecidable (s2.memaddrs a)) e := by
  rw [evalHOLFinite_eq_toExact, evalHOLFinite_eq_toExact]
  exact evalHOLExact_eq_of_expLocalsAvoided s1 s2 p heq e ha

inductive StepCountedBody (counter : MlS) : BitVec 64 → ProgHOL 64 → Nat → Prop
  | incr (step : BitVec 64) :
      StepCountedBody counter step
        (.assign .local counter (.op .add [.var .local counter, .const step])) 0
  | decr :
      StepCountedBody counter (-1)
        (.assign .local counter (.op .sub [.var .local counter, .const 1])) 0
  | avoid (p : ProgHOL 64) {cost : Nat}
      (bounded : ProgBounded p cost)
      (havoid : avoidsLocal counter p = true)
      (noCont : noTopContinue p = true) :
      StepCountedBody counter 0 p cost
  | seq {step : BitVec 64} (first : ProgHOL 64) {tail : ProgHOL 64} {a b : Nat}
      (bounded : ProgBounded first a)
      (avoid : avoidsLocal counter first = true)
      (noCont : noTopContinue first = true)
      (rest : StepCountedBody counter step tail b) :
      StepCountedBody counter step (.seq first tail) (a + b)
  | seqStep {s1 s2 : BitVec 64} {first tail : ProgHOL 64} {a b : Nat}
      (h1 : StepCountedBody counter s1 first a)
      (h2 : StepCountedBody counter s2 tail b) :
      StepCountedBody counter (s1 + s2) (.seq first tail) (a + b)
  | dec {step : BitVec 64} (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL 64)
      {body : ProgHOL 64} {cost : Nat}
      (distinct : counter ≠ name)
      (rest : StepCountedBody counter step body cost) :
      StepCountedBody counter step (.dec name shape initializer body) cost
  | ite {step : BitVec 64} (cond : ExpHOL 64) {yes no : ProgHOL 64} {a b : Nat}
      (hyes : StepCountedBody counter step yes a)
      (hno : StepCountedBody counter step no b) :
      StepCountedBody counter step (.ite cond yes no) (max a b)
  | decCallGen {step : BitVec 64} (name : MlS) (shape : ShapeHOL) (fn : MlS) (args : List (ExpHOL 64))
      {cont : ProgHOL 64} {ov contCost : Nat}
      (hwrap : ProgBounded cont contCost → ProgBounded (.decCall name shape fn args cont) (ov + contCost))
      (distinct : counter ≠ name)
      (rest : StepCountedBody counter step cont contCost) :
      StepCountedBody counter step (.decCall name shape fn args cont) (ov + contCost)

theorem StepCountedBody.toProgBounded {counter : MlS} {step : BitVec 64} {body : ProgHOL 64} {cost : Nat}
    (counted : StepCountedBody counter step body cost) :
    ProgBounded body cost := by
  induction counted with
  | incr _ => exact ProgBounded.straight _ rfl
  | decr => exact ProgBounded.straight _ rfl
  | avoid _ bounded _ _ => exact bounded
  | seq _ bounded _ _ _ ih => exact ProgBounded.seq bounded ih
  | seqStep _ _ ih1 ih2 => exact ProgBounded.seq ih1 ih2
  | dec name shape init _ _ ih => exact ProgBounded.dec name shape init ih
  | ite cond _ _ ihy ihn => exact ProgBounded.iteMax cond ihy ihn
  | decCallGen _ _ _ _ hwrap _ _ ih => exact hwrap ih

theorem StepCountedBody.noTopContinue_true {counter : MlS} {step : BitVec 64} {body : ProgHOL 64} {cost : Nat}
    (counted : StepCountedBody counter step body cost) :
    noTopContinue body = true := by
  induction counted with
  | incr _ => rfl
  | decr => rfl
  | avoid _ _ _ noCont => exact noCont
  | seq _ _ _ noCont _ ih => simp [noTopContinue, noCont, ih]
  | seqStep _ _ ih1 ih2 => simp [noTopContinue, ih1, ih2]
  | dec _ _ _ _ _ ih => simp [noTopContinue, ih]
  | ite _ _ _ ihy ihn => simp [noTopContinue, ihy, ihn]
  | decCallGen _ _ _ _ _ _ _ ih => simp [noTopContinue, ih]

theorem StepCountedBody.advance_none {counter : MlS} {step : BitVec 64} {body : ProgHOL 64} {cost : Nat}
    (counted : StepCountedBody counter step body cost) {F : Type} (state : PanSemStateFiniteExact 64 F)
    (w : BitVec 64) (atCounter : state.locals.lookup counter = some (.val (.word w)))
    {post : PanSemStateFiniteExact 64 F}
    (hrun : evaluateHOLFiniteState state body = (none, post)) :
    post.locals.lookup counter = some (.val (.word (w + step))) := by
  induction counted generalizing state w post with
  | incr s =>
    have run : evaluateHOLFiniteState state (.assign .local counter (.op .add [.var .local counter, .const s])) =
        (none, setVarHOLFinite counter (.val (.word (w + s))) state) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, atCounter, wordOpHOL, wordOp,
        valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
        shapeOfHOLExact, shapeEqHOL]
    rw [run] at hrun
    cases hrun
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  | decr =>
    have run : evaluateHOLFiniteState state (.assign .local counter (.op .sub [.var .local counter, .const 1])) =
        (none, setVarHOLFinite counter (.val (.word (w - 1))) state) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, atCounter, wordOpHOL, wordOp,
        valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
        shapeOfHOLExact, shapeEqHOL]
    rw [run] at hrun
    cases hrun
    have hsub : w - (1 : BitVec 64) = w + (-1 : BitVec 64) := BitVec.sub_eq_add_neg w 1
    rw [← hsub]
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  | avoid p _ havoid _ =>
    have frame := evaluate_avoidsLocal_flowing counter p havoid state
    rw [hrun] at frame
    have hkept := frame (Or.inl rfl)
    simpa using hkept.trans atCounter
  | seq first _ avoid _ _ ih =>
    have frame := evaluate_avoidsLocal_flowing counter first avoid state
    rw [evaluateHOLFiniteState_seq_line780] at hrun
    cases firstRun : evaluateHOLFiniteState state first with
    | mk res mid =>
      rw [firstRun] at hrun frame
      cases res with
      | none =>
        dsimp only at hrun frame
        exact ih mid w ((frame (Or.inl rfl)).trans atCounter) hrun
      | some r =>
        dsimp only at hrun
        cases hrun
  | seqStep _ _ ih1 ih2 =>
    rw [evaluateHOLFiniteState_seq_line780] at hrun
    cases firstRun : evaluateHOLFiniteState state _ with
    | mk res mid =>
      rw [firstRun] at hrun
      cases res with
      | none =>
        dsimp only at hrun
        have hm := ih1 state w atCounter firstRun
        have hp := ih2 mid _ hm hrun
        have hassoc : ∀ a b c : BitVec 64, a + b + c = a + (b + c) := BitVec.add_assoc
        simpa [hassoc] using hp
      | some r =>
        dsimp only at hrun
        cases hrun
  | dec name shape init distinct _ ih =>
    obtain ⟨val, inner, hinner, hpost⟩ := dec_flowing (Or.inl rfl) hrun
    have hc : (setVarHOLFinite name val state).locals.lookup counter = some (.val (.word w)) := by
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm distinct, atCounter]
    have atInner := ih (setVarHOLFinite name val state) w hc hinner
    rw [hpost, PanRunBounded.resVarEq_lookup, if_neg distinct]
    exact atInner
  | ite cond _ _ ihy ihn =>
    rw [evaluateHOLFiniteState_ite] at hrun
    split at hrun
    · split at hrun
      · exact ihn state w atCounter hrun
      · exact ihy state w atCounter hrun
    · simp at hrun
  | decCallGen name shape fn args _ distinct _ ih =>
    obtain ⟨_v, resumed, inner, hloc, _hclk, contRun, hpost⟩ := decCall_flowing (Or.inl rfl) hrun
    have atResumed : resumed.locals.lookup counter = some (.val (.word w)) :=
      (hloc counter distinct).trans atCounter
    have hinner := ih resumed w atResumed contRun
    rw [hpost, PanRunBounded.resVarEq_lookup, if_neg distinct]
    exact hinner

theorem StepCountedBody.run {counter : MlS} {step : BitVec 64} {body : ProgHOL 64} {cost : Nat}
    (counted : StepCountedBody counter step body cost) {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode) (w : BitVec 64)
    (atCounter : state.locals.lookup counter = some (.val (.word w))) (budget : cost ≤ state.clock) :
    state.clock ≤ (evaluateHOLFiniteState state body).2.clock + cost ∧
      (evaluateHOLFiniteState state body).2.clock ≤ state.clock ∧
      (evaluateHOLFiniteState state body).1 ≠ some .timeOut ∧
      (evaluateHOLFiniteState state body).1 ≠ some .continue ∧
      ((evaluateHOLFiniteState state body).1 = none →
        (evaluateHOLFiniteState state body).2.locals.lookup counter = some (.val (.word (w + step))) ∧
        (evaluateHOLFiniteState state body).2.code = state.code) := by
  have hb := counted.toProgBounded state code budget
  have hnc := evaluate_noTopContinue body counted.noTopContinue_true state
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata state body
  refine ⟨hb.1, hb.2.1, hb.2.2, hnc, fun hnone => ?_⟩
  cases hrun : evaluateHOLFiniteState state body with
  | mk res post =>
    rw [hrun] at hnone hmeta
    dsimp only at hnone hmeta ⊢
    subst hnone
    exact ⟨counted.advance_none state w atCounter hrun, hmeta.1⟩

theorem StepCountedBody.decCall {counter : MlS} {step : BitVec 64}
    {fn : MlS} {fnCost contCost : Nat} (installed : FunBounded fn fnCost)
    (name : MlS) (shape : ShapeHOL) (args : List (ExpHOL 64)) {cont : ProgHOL 64}
    (distinct : counter ≠ name)
    (rest : StepCountedBody counter step cont contCost) :
    StepCountedBody counter step (.decCall name shape fn args cont) (fnCost + 1 + contCost) :=
  StepCountedBody.decCallGen name shape fn args (ProgBounded.decCall installed name shape args) distinct rest

theorem StepCountedBody.decCallSpecial {counter : MlS} {step : BitVec 64}
    {fn : MlS} {ov contCost : Nat}
    (name : MlS) (shape : ShapeHOL) (args : List (ExpHOL 64)) {cont : ProgHOL 64}
    (hov : specialDecCallOverhead fn args = some ov)
    (distinct : counter ≠ name)
    (rest : StepCountedBody counter step cont contCost) :
    StepCountedBody counter step (.decCall name shape fn args cont) (ov + contCost) :=
  StepCountedBody.decCallGen name shape fn args (specialDecCallOverhead_sound name shape fn args hov) distinct rest

theorem StepCountedBody.seqZeroRight {counter : MlS} {step : BitVec 64}
    {first tail : ProgHOL 64} {a b : Nat}
    (h1 : StepCountedBody counter step first a)
    (h2 : ProgBounded tail b)
    (havoid : avoidsLocal counter tail = true)
    (hnoCont : noTopContinue tail = true) :
    StepCountedBody counter step (.seq first tail) (a + b) := by
  simpa using StepCountedBody.seqStep h1 (StepCountedBody.avoid tail h2 havoid hnoCont)

private theorem eval_exp_counted_condition {F : Type}
    (state : PanSemStateFiniteExact 64 F) (counter : MlS) (op : Cmp)
    (hop : op = .less ∨ op = .lower) (limitExp : ExpHOL 64) (K w : BitVec 64)
    (signed : op = .less → K.toNat < 2 ^ 63) (within : w.toNat ≤ K.toNat)
    (atCounter : state.locals.lookup counter = some (.val (.word w)))
    (atLimit : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) limitExp =
      some (.val (.word K))) :
    evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      (.cmp op (.var .local counter) limitExp) =
      some (.val (.word (if w.toNat < K.toNat then 1 else 0))) := by
  rw [evalHOLFinite_eq_toExact] at atLimit ⊢
  rcases hop with rfl | rfl
  · have small := signed rfl
    simp only [evalHOLExact, atCounter, atLimit]
    simp only [Compiler.Encoders.Asm.wordCmpHOL, holAsmSignedLess_small w K (by omega) small]
    by_cases lt : w.toNat < K.toNat <;> simp [lt]
  · simp only [evalHOLExact, atCounter, atLimit]
    simp only [Compiler.Encoders.Asm.wordCmpHOL]
    by_cases lt : w.toNat < K.toNat <;> simp [lt, BitVec.lt_def]

theorem expCountedWhile_run (counter : MlS) (limitExp : ExpHOL 64) (op : Cmp)
    (hop : op = .less ∨ op = .lower) (K step : BitVec 64)
    (hpos : 0 < step.toNat)
    (hnoWrap : K.toNat + step.toNat ≤ 2 ^ 64)
    (signed : op = .less → K.toNat + step.toNat ≤ 2 ^ 63)
    {body : ProgHOL 64} {cost : Nat} (counted : StepCountedBody counter step body cost)
    (preservesLimit : expLocalsAvoided limitExp body = true) :
    ∀ n : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F),
      state.code = originalRuntimeCode →
      ∀ w : BitVec 64, state.locals.lookup counter = some (.val (.word w)) →
      evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) limitExp =
        some (.val (.word K)) →
      (w.toNat < K.toNat → K.toNat - w.toNat ≤ n) →
      (op = .less → w.toNat < 2 ^ 63) →
      n * (cost + 1) ≤ state.clock →
      let evaluated := evaluateHOLFiniteState state (.while (.cmp op (.var .local counter) limitExp) body)
      state.clock ≤ evaluated.2.clock + n * (cost + 1) ∧
        evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro F state code w atCounter atLimit hdist hwSigned budget
    dsimp only
    rw [evaluateHOLFiniteState_while_total]
    by_cases lt : w.toNat < K.toNat
    · have condition := eval_exp_counted_condition state counter op hop limitExp K w
        (fun hl => by have := signed hl; omega) (Nat.le_of_lt lt) atCounter atLimit
      rw [condition, if_pos lt]
      simp only [show (1 : BitVec 64) ≠ 0 by decide, if_true, ne_eq, not_false_eq_true]
      have hrem : K.toNat - w.toNat ≤ n := hdist lt
      have positiveRank : 0 < n := by omega
      have oneIteration : cost + 1 ≤ n * (cost + 1) := Nat.le_mul_of_pos_left _ positiveRank
      have clock : state.clock ≠ 0 := by omega
      rw [if_neg clock, fixClockHOLFinite_evaluateState]
      have stepRun := counted.run (decClockHOLFinite state) code w atCounter
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
          have natural : (w + step).toNat = w.toNat + step.toNat := by
            rw [BitVec.toNat_add_of_lt (by omega)]
          have nextRank : n - 1 < n := by omega
          have nextLimit :
              evalHOLFinite middle (h := fun a => Classical.propDecidable (middle.memaddrs a)) limitExp =
                some (.val (.word K)) := by
            have heq := evalHOLFinite_eq_of_expLocalsAvoided middle (decClockHOLFinite state) body
              (fun k hk => by
                have hf := evaluate_avoidsLocal_flowing k body hk (decClockHOLFinite state)
                rw [bodyRun] at hf
                exact hf (Or.inl rfl))
              limitExp preservesLimit
            have hdec := evalHOLFinite_eq_of_expLocalsAvoided (decClockHOLFinite state) state body
              (fun _ _ => rfl) limitExp preservesLimit
            exact (heq.trans hdec).trans atLimit
          have decrease : (n - 1) * (cost + 1) + (cost + 1) ≤ n * (cost + 1) := by
            rw [← Nat.succ_mul]
            exact Nat.mul_le_mul_right _ (by omega)
          have tail := ih (n - 1) nextRank middle (nextCode.trans code)
            (w + step) nextCounter nextLimit
            (fun hlt2 => by rw [natural] at hlt2 ⊢; omega)
            (fun hl => by have := signed hl; rw [natural]; omega)
            (by omega)
          obtain ⟨t1, t2, t3⟩ := tail
          exact ⟨by omega, by omega, t3⟩
        | some r =>
          cases r with
          | «continue» => exact absurd rfl noCont
          | «break» => exact ⟨by simp; omega, by simp; omega, by simp⟩
          | timeOut => exact absurd rfl safe
          | _ => exact ⟨by simp; omega, by simp; omega, by simp⟩
    · have hcondFalse :
          evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
            (.cmp op (.var .local counter) limitExp) = some (.val (.word 0)) := by
        rw [evalHOLFinite_eq_toExact] at atLimit ⊢
        rcases hop with rfl | rfl
        · have hw := hwSigned rfl
          by_cases hK : K.toNat < 2 ^ 63
          · simp only [evalHOLExact, atCounter, atLimit, Compiler.Encoders.Asm.wordCmpHOL,
              holAsmSignedLess_small w K hw hK, lt, decide_false, Bool.false_eq_true, ↓reduceIte]
          · have hK' : ¬ K.toNat < 9223372036854775808 := hK
            have hw' : w.toNat < 9223372036854775808 := hw
            simp [evalHOLExact, atCounter, atLimit, Compiler.Encoders.Asm.wordCmpHOL,
              Compiler.Encoders.Asm.holAsmSignedLess, hw', hK']
        · simp only [evalHOLExact, atCounter, atLimit, Compiler.Encoders.Asm.wordCmpHOL]
          simp [lt, BitVec.lt_def]
      rw [hcondFalse]
      simp

theorem expCountedWhile_zero_bounded {F : Type}
    (counter : MlS) (limitExp : ExpHOL 64) (op : Cmp) (hop : op = .less ∨ op = .lower)
    {body : ProgHOL 64} {cost : Nat} (counted : StepCountedBody counter 1 body cost)
    (preservesLimit : expLocalsAvoided limitExp body = true)
    (state : PanSemStateFiniteExact 64 F) (code : state.code = originalRuntimeCode)
    (atCounter : state.locals.lookup counter = some (.val (.word 0)))
    (budget : (2 ^ 64 - 1) * (cost + 1) ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.while (.cmp op (.var .local counter) limitExp) body)
    state.clock ≤ evaluated.2.clock + (2 ^ 64 - 1) * (cost + 1) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  dsimp only
  cases hlim : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) limitExp with
  | none =>
    rw [evaluateHOLFiniteState_while_total]
    have hcond : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
        (.cmp op (.var .local counter) limitExp) = none := by
      rw [evalHOLFinite_eq_toExact] at hlim ⊢
      simp [evalHOLExact, atCounter, hlim]
    rw [hcond]; simp
  | some v =>
    cases v with
    | rStruct _ =>
      rw [evaluateHOLFiniteState_while_total]
      have hcond : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
          (.cmp op (.var .local counter) limitExp) = none := by
        rw [evalHOLFinite_eq_toExact] at hlim ⊢
        simp [evalHOLExact, atCounter, hlim]
      rw [hcond]; simp
    | nStruct _ _ =>
      rw [evaluateHOLFiniteState_while_total]
      have hcond : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
          (.cmp op (.var .local counter) limitExp) = none := by
        rw [evalHOLFinite_eq_toExact] at hlim ⊢
        simp [evalHOLExact, atCounter, hlim]
      rw [hcond]; simp
    | val wv =>
      cases wv with
      | word K =>
        by_cases signed : op = .less → K.toNat < 2 ^ 63
        · have ceiling : K.toNat * (cost + 1) ≤ (2 ^ 64 - 1) * (cost + 1) :=
            Nat.mul_le_mul_right _ (by have bound := K.isLt; omega)
          have hnoWrap : K.toNat + (1 : BitVec 64).toNat ≤ 2 ^ 64 := by
            have bound := K.isLt; simp; omega
          have hsig : op = .less → K.toNat + (1 : BitVec 64).toNat ≤ 2 ^ 63 := by
            intro hl
            have hlt := signed hl
            simp
            omega
          have bounded := expCountedWhile_run counter limitExp op hop K 1 (by decide) hnoWrap hsig
            counted preservesLimit K.toNat state code 0 atCounter hlim
            (fun _ => by simp) (fun _ => by decide) (by omega)
          dsimp only at bounded
          exact ⟨by omega, bounded.2.1, bounded.2.2⟩
        · have comparison : op = .less := by
            rcases hop with eq | eq
            · exact eq
            · exfalso; exact signed (fun impossible => by cases eq.symm.trans impossible)
          have negative : ¬ K.toNat < 9223372036854775808 := fun small => signed (fun _ => small)
          subst op
          have condition : evalHOLFinite state
              (h := fun a => Classical.propDecidable (state.memaddrs a))
              (.cmp .less (.var .local counter) limitExp) = some (.val (.word 0)) := by
            rw [evalHOLFinite_eq_toExact] at hlim ⊢
            simp [evalHOLExact, atCounter, hlim, Compiler.Encoders.Asm.wordCmpHOL,
              Compiler.Encoders.Asm.holAsmSignedLess, negative]
          rw [evaluateHOLFiniteState_while_total, condition]
          simp

theorem ProgBounded.expCountedDec (counter : MlS) (op : Cmp) (hop : op = .less ∨ op = .lower)
    (limitExp : ExpHOL 64) {body tail : ProgHOL 64} {cost tailCost : Nat}
    (counted : StepCountedBody counter 1 body cost)
    (preservesLimit : expLocalsAvoided limitExp body = true)
    (rest : ProgBounded tail tailCost) :
    ProgBounded (.dec counter .one (.const 0)
      (.seq (.while (.cmp op (.var .local counter) limitExp) body) tail))
      ((2 ^ 64 - 1) * (cost + 1) + tailCost) := by
  intro F state code budget
  rw [evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true]
  let entered := setVarHOLFinite counter (.val (.word 0)) state
  have atCounter : entered.locals.lookup counter = some (.val (.word 0)) := by
    simp [entered, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have loop := expCountedWhile_zero_bounded counter limitExp op hop counted preservesLimit
    entered code atCounter (by change (2 ^ 64 - 1) * (cost + 1) ≤ state.clock; omega)
  have meta' := PanRunBounded.evaluateHOLFiniteState_metadata entered
    (.while (.cmp op (.var .local counter) limitExp) body)
  change state.clock ≤ (evaluateHOLFiniteState entered _).2.clock + _ ∧
    (evaluateHOLFiniteState entered _).2.clock ≤ state.clock ∧
    (evaluateHOLFiniteState entered _).1 ≠ some .timeOut
  rw [evaluateHOLFiniteState_seq_line780]
  cases loopRun : evaluateHOLFiniteState entered (.while (.cmp op (.var .local counter) limitExp) body) with
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

theorem ProgBounded.expCountedDecNoTail (counter : MlS) (op : Cmp) (hop : op = .less ∨ op = .lower)
    (limitExp : ExpHOL 64) {body : ProgHOL 64} {cost : Nat}
    (counted : StepCountedBody counter 1 body cost)
    (preservesLimit : expLocalsAvoided limitExp body = true) :
    ProgBounded (.dec counter .one (.const 0)
      (.while (.cmp op (.var .local counter) limitExp) body))
      ((2 ^ 64 - 1) * (cost + 1)) := by
  intro F state code budget
  rw [evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true]
  let entered := setVarHOLFinite counter (.val (.word 0)) state
  have atCounter : entered.locals.lookup counter = some (.val (.word 0)) := by
    simp [entered, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have loop := expCountedWhile_zero_bounded counter limitExp op hop counted preservesLimit
    entered code atCounter (by change (2 ^ 64 - 1) * (cost + 1) ≤ state.clock; omega)
  cases loopRun : evaluateHOLFiniteState entered (.while (.cmp op (.var .local counter) limitExp) body) with
  | mk result middle =>
    rw [loopRun] at loop
    dsimp only at loop ⊢
    exact loop

theorem ProgBounded.expCountedAssign (counter : MlS) (op : Cmp) (hop : op = .less ∨ op = .lower)
    (limitExp : ExpHOL 64) {body tail : ProgHOL 64} {cost tailCost : Nat}
    (counted : StepCountedBody counter 1 body cost)
    (preservesLimit : expLocalsAvoided limitExp body = true)
    (rest : ProgBounded tail tailCost) :
    ProgBounded (.seq (.assign .local counter (.const 0))
      (.seq (.while (.cmp op (.var .local counter) limitExp) body) tail))
      ((2 ^ 64 - 1) * (cost + 1) + tailCost) := by
  intro F state code budget
  by_cases valid : isValidValueHOLExact state.toExact .local counter (.val (.word (0#64))) = true
  · have assignRun : evaluateHOLFiniteState state (.assign .local counter (.const 0)) =
        (none, setKvarHOLFinite .local counter (.val (.word 0)) state) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, valid]
    rw [evaluateHOLFiniteState_seq_line780, assignRun]
    dsimp only
    let entered := setKvarHOLFinite .local counter (.val (.word 0)) state
    have atCounter : entered.locals.lookup counter = some (.val (.word 0)) := by
      simp [entered, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have loop := expCountedWhile_zero_bounded counter limitExp op hop counted preservesLimit
      entered code atCounter (by change (2 ^ 64 - 1) * (cost + 1) ≤ state.clock; omega)
    have meta' := PanRunBounded.evaluateHOLFiniteState_metadata entered
      (.while (.cmp op (.var .local counter) limitExp) body)
    change state.clock ≤ (evaluateHOLFiniteState entered _).2.clock + _ ∧
      (evaluateHOLFiniteState entered _).2.clock ≤ state.clock ∧
      (evaluateHOLFiniteState entered _).1 ≠ some .timeOut
    rw [evaluateHOLFiniteState_seq_line780]
    cases loopRun : evaluateHOLFiniteState entered (.while (.cmp op (.var .local counter) limitExp) body) with
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
  · have assignRun : evaluateHOLFiniteState state (.assign .local counter (.const 0)) = (some .error, state) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, valid]
    rw [evaluateHOLFiniteState_seq_line780, assignRun]
    simp

theorem ProgBounded.expCountedAssignNoTail (counter : MlS) (op : Cmp) (hop : op = .less ∨ op = .lower)
    (limitExp : ExpHOL 64) {body : ProgHOL 64} {cost : Nat}
    (counted : StepCountedBody counter 1 body cost)
    (preservesLimit : expLocalsAvoided limitExp body = true) :
    ProgBounded (.seq (.assign .local counter (.const 0))
      (.while (.cmp op (.var .local counter) limitExp) body))
      ((2 ^ 64 - 1) * (cost + 1)) := by
  intro F state code budget
  by_cases valid : isValidValueHOLExact state.toExact .local counter (.val (.word (0#64))) = true
  · have assignRun : evaluateHOLFiniteState state (.assign .local counter (.const 0)) =
        (none, setKvarHOLFinite .local counter (.val (.word 0)) state) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, valid]
    rw [evaluateHOLFiniteState_seq_line780, assignRun]
    dsimp only
    let entered := setKvarHOLFinite .local counter (.val (.word 0)) state
    have atCounter : entered.locals.lookup counter = some (.val (.word 0)) := by
      simp [entered, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have loop := expCountedWhile_zero_bounded counter limitExp op hop counted preservesLimit
      entered code atCounter (by change (2 ^ 64 - 1) * (cost + 1) ≤ state.clock; omega)
    cases loopRun : evaluateHOLFiniteState entered (.while (.cmp op (.var .local counter) limitExp) body) with
    | mk result middle =>
      rw [loopRun] at loop
      dsimp only at loop ⊢
      exact loop
  · have assignRun : evaluateHOLFiniteState state (.assign .local counter (.const 0)) = (some .error, state) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, valid]
    rw [evaluateHOLFiniteState_seq_line780, assignRun]
    simp

theorem ProgBounded.constCountedDec (counter : MlS) (op : Cmp) (hop : op = .less ∨ op = .lower)
    (K : BitVec 64) (hK : K.toNat + 1 < 2 ^ 63)
    {body tail : ProgHOL 64} {cost tailCost : Nat}
    (counted : StepCountedBody counter 1 body cost)
    (rest : ProgBounded tail tailCost) :
    ProgBounded (.dec counter .one (.const 0)
      (.seq (.while (.cmp op (.var .local counter) (.const K)) body) tail))
      (K.toNat * (cost + 1) + tailCost) := by
  intro F state code budget
  rw [evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true]
  let entered := setVarHOLFinite counter (.val (.word 0)) state
  have atCounter : entered.locals.lookup counter = some (.val (.word 0)) := by
    simp [entered, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hlim : evalHOLFinite entered (h := fun a => Classical.propDecidable (entered.memaddrs a)) (.const K) =
      some (.val (.word K)) := by
    rw [evalHOLFinite_eq_toExact]; rfl
  have loop := expCountedWhile_run counter (.const K) op hop K 1 (by decide)
    (by simp; omega) (fun _ => by simp; omega) counted rfl K.toNat entered code 0 atCounter hlim
    (fun _ => by simp) (fun _ => by decide) (by change K.toNat * (cost + 1) ≤ state.clock; omega)
  have meta' := PanRunBounded.evaluateHOLFiniteState_metadata entered
    (.while (.cmp op (.var .local counter) (.const K)) body)
  change state.clock ≤ (evaluateHOLFiniteState entered _).2.clock + _ ∧
    (evaluateHOLFiniteState entered _).2.clock ≤ state.clock ∧
    (evaluateHOLFiniteState entered _).1 ≠ some .timeOut
  rw [evaluateHOLFiniteState_seq_line780]
  cases loopRun : evaluateHOLFiniteState entered (.while (.cmp op (.var .local counter) (.const K)) body) with
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

theorem ProgBounded.constCountedDecNoTail (counter : MlS) (op : Cmp) (hop : op = .less ∨ op = .lower)
    (K : BitVec 64) (hK : K.toNat + 1 < 2 ^ 63)
    {body : ProgHOL 64} {cost : Nat}
    (counted : StepCountedBody counter 1 body cost) :
    ProgBounded (.dec counter .one (.const 0)
      (.while (.cmp op (.var .local counter) (.const K)) body))
      (K.toNat * (cost + 1)) := by
  intro F state code budget
  rw [evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true]
  let entered := setVarHOLFinite counter (.val (.word 0)) state
  have atCounter : entered.locals.lookup counter = some (.val (.word 0)) := by
    simp [entered, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hlim : evalHOLFinite entered (h := fun a => Classical.propDecidable (entered.memaddrs a)) (.const K) =
      some (.val (.word K)) := by
    rw [evalHOLFinite_eq_toExact]; rfl
  have loop := expCountedWhile_run counter (.const K) op hop K 1 (by decide)
    (by simp; omega) (fun _ => by simp; omega) counted rfl K.toNat entered code 0 atCounter hlim
    (fun _ => by simp) (fun _ => by decide) (by change K.toNat * (cost + 1) ≤ state.clock; omega)
  cases loopRun : evaluateHOLFiniteState entered (.while (.cmp op (.var .local counter) (.const K)) body) with
  | mk result middle =>
    rw [loopRun] at loop
    dsimp only at loop ⊢
    exact loop

theorem ProgBounded.constStepCountedDec (counter : MlS) (op : Cmp) (hop : op = .less ∨ op = .lower)
    (K step : BitVec 64) (hpos : 0 < step.toNat) (hK : K.toNat + step.toNat ≤ 2 ^ 63)
    {body tail : ProgHOL 64} {cost tailCost : Nat}
    (counted : StepCountedBody counter step body cost)
    (rest : ProgBounded tail tailCost) :
    ProgBounded (.dec counter .one (.const 0)
      (.seq (.while (.cmp op (.var .local counter) (.const K)) body) tail))
      (K.toNat * (cost + 1) + tailCost) := by
  intro F state code budget
  rw [evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true]
  let entered := setVarHOLFinite counter (.val (.word 0)) state
  have atCounter : entered.locals.lookup counter = some (.val (.word 0)) := by
    simp [entered, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hlim : evalHOLFinite entered (h := fun a => Classical.propDecidable (entered.memaddrs a)) (.const K) =
      some (.val (.word K)) := by
    rw [evalHOLFinite_eq_toExact]; rfl
  have loop := expCountedWhile_run counter (.const K) op hop K step hpos
    (by omega) (fun _ => hK) counted rfl K.toNat entered code 0 atCounter hlim
    (fun _ => by simp) (fun _ => by decide) (by change K.toNat * (cost + 1) ≤ state.clock; omega)
  have meta' := PanRunBounded.evaluateHOLFiniteState_metadata entered
    (.while (.cmp op (.var .local counter) (.const K)) body)
  change state.clock ≤ (evaluateHOLFiniteState entered _).2.clock + _ ∧
    (evaluateHOLFiniteState entered _).2.clock ≤ state.clock ∧
    (evaluateHOLFiniteState entered _).1 ≠ some .timeOut
  rw [evaluateHOLFiniteState_seq_line780]
  cases loopRun : evaluateHOLFiniteState entered (.while (.cmp op (.var .local counter) (.const K)) body) with
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

theorem downCountedWhile_run (counter : MlS) (op : Cmp) (hop : op = .less ∨ op = .lower)
    {body : ProgHOL 64} {cost : Nat} (counted : StepCountedBody counter (-1) body cost) :
    ∀ n : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F),
      state.code = originalRuntimeCode →
      ∀ w : BitVec 64, state.locals.lookup counter = some (.val (.word w)) →
      w.toNat ≤ n →
      (op = .less → w.toNat < 2 ^ 63) →
      n * (cost + 1) ≤ state.clock →
      let evaluated := evaluateHOLFiniteState state (.while (.cmp op (.const 0) (.var .local counter)) body)
      state.clock ≤ evaluated.2.clock + n * (cost + 1) ∧
        evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro F state code w atCounter hdist hwSigned budget
    dsimp only
    rw [evaluateHOLFiniteState_while_total]
    by_cases pos : 0 < w.toNat
    · have hcond : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
          (.cmp op (.const 0) (.var .local counter)) = some (.val (.word 1)) := by
        rw [evalHOLFinite_eq_toExact]
        rcases hop with rfl | rfl
        · have hw := hwSigned rfl
          simp only [evalHOLExact, atCounter, Compiler.Encoders.Asm.wordCmpHOL,
            holAsmSignedLess_small 0 w (by decide) hw]
          simp [pos]
        · simp only [evalHOLExact, atCounter, Compiler.Encoders.Asm.wordCmpHOL]
          simp [pos, BitVec.lt_def]
      rw [hcond]
      simp only [show (1 : BitVec 64) ≠ 0 by decide, if_true, ne_eq, not_false_eq_true]
      have positiveRank : 0 < n := by omega
      have oneIteration : cost + 1 ≤ n * (cost + 1) := Nat.le_mul_of_pos_left _ positiveRank
      have clock : state.clock ≠ 0 := by omega
      rw [if_neg clock, fixClockHOLFinite_evaluateState]
      have stepRun := counted.run (decClockHOLFinite state) code w atCounter
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
          have hsub : w + (-1 : BitVec 64) = w - 1 := (BitVec.sub_eq_add_neg w 1).symm
          have hnat : (w + (-1 : BitVec 64)).toNat = w.toNat - 1 := by
            rw [hsub, BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; omega)]
            simp
          have nextRank : n - 1 < n := by omega
          have decrease : (n - 1) * (cost + 1) + (cost + 1) ≤ n * (cost + 1) := by
            rw [← Nat.succ_mul]
            exact Nat.mul_le_mul_right _ (by omega)
          have tail := ih (n - 1) nextRank middle (nextCode.trans code)
            (w + (-1 : BitVec 64)) nextCounter (by rw [hnat]; omega)
            (fun hl => by have := hwSigned hl; rw [hnat]; omega)
            (by omega)
          obtain ⟨t1, t2, t3⟩ := tail
          exact ⟨by omega, by omega, t3⟩
        | some r =>
          cases r with
          | «continue» => exact absurd rfl noCont
          | «break» => exact ⟨by simp; omega, by simp; omega, by simp⟩
          | timeOut => exact absurd rfl safe
          | _ => exact ⟨by simp; omega, by simp; omega, by simp⟩
    · have hzero : w.toNat = 0 := by omega
      have hw0 : w = 0 := BitVec.eq_of_toNat_eq (by simpa using hzero)
      subst hw0
      have hcond : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
          (.cmp op (.const 0) (.var .local counter)) = some (.val (.word 0)) := by
        rw [evalHOLFinite_eq_toExact]
        rcases hop with rfl | rfl <;>
          simp [evalHOLExact, atCounter, Compiler.Encoders.Asm.wordCmpHOL,
            Compiler.Encoders.Asm.holAsmSignedLess]
      rw [hcond]
      simp

theorem ProgBounded.downCountedConstDec (counter : MlS) (op : Cmp) (hop : op = .less ∨ op = .lower)
    (K : BitVec 64) (hK : op = .less → K.toNat < 2 ^ 63)
    {body tail : ProgHOL 64} {cost tailCost : Nat}
    (counted : StepCountedBody counter (-1) body cost)
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
  have loop := downCountedWhile_run counter op hop counted K.toNat entered code K atCounter
    (le_refl _) hK (by change K.toNat * (cost + 1) ≤ state.clock; omega)
  have meta' := PanRunBounded.evaluateHOLFiniteState_metadata entered
    (.while (.cmp op (.const 0) (.var .local counter)) body)
  change state.clock ≤ (evaluateHOLFiniteState entered _).2.clock + _ ∧
    (evaluateHOLFiniteState entered _).2.clock ≤ state.clock ∧
    (evaluateHOLFiniteState entered _).1 ≠ some .timeOut
  rw [evaluateHOLFiniteState_seq_line780]
  cases loopRun : evaluateHOLFiniteState entered (.while (.cmp op (.const 0) (.var .local counter)) body) with
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

theorem ProgBounded.downCountedVarDec (counter srcVar : MlS)
    {body tail : ProgHOL 64} {cost tailCost : Nat}
    (counted : StepCountedBody counter (-1) body cost)
    (rest : ProgBounded tail tailCost) :
    ProgBounded (.dec counter .one (.var .local srcVar)
      (.seq (.while (.cmp .lower (.const 0) (.var .local counter)) body) tail))
      ((2 ^ 64 - 1) * (cost + 1) + tailCost) := by
  intro F state code budget
  apply RunBounded.dec
  intro val _hval
  cases val with
  | rStruct fs =>
    let entered := setVarHOLFinite counter (.rStruct fs) state
    change RunBounded entered _ _
    unfold RunBounded
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total]
    have hc : evalHOLFinite entered (h := fun a => Classical.propDecidable (entered.memaddrs a))
        (.cmp .lower (.const 0) (.var .local counter)) = none := by
      rw [evalHOLFinite_eq_toExact]
      simp [entered, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rw [hc]; simp
  | nStruct nm fs =>
    let entered := setVarHOLFinite counter (.nStruct nm fs) state
    change RunBounded entered _ _
    unfold RunBounded
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total]
    have hc : evalHOLFinite entered (h := fun a => Classical.propDecidable (entered.memaddrs a))
        (.cmp .lower (.const 0) (.var .local counter)) = none := by
      rw [evalHOLFinite_eq_toExact]
      simp [entered, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rw [hc]; simp
  | val wv =>
    cases wv with
    | word K =>
      let entered := setVarHOLFinite counter (.val (.word K)) state
      have atCounter : entered.locals.lookup counter = some (.val (.word K)) := by
        simp [entered, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hceil : K.toNat * (cost + 1) ≤ (2 ^ 64 - 1) * (cost + 1) :=
        Nat.mul_le_mul_right _ (by have := K.isLt; omega)
      have loop := downCountedWhile_run counter .lower (Or.inr rfl) counted K.toNat entered code K atCounter
        (le_refl _) (fun h => by cases h) (by change K.toNat * (cost + 1) ≤ state.clock; omega)
      exact (RunBounded.seq loop (a := K.toNat * (cost + 1)) (b := tailCost)
        (by change K.toNat * (cost + 1) + tailCost ≤ state.clock; omega)
        (fun next _ nextCode nextBudget => rest next (nextCode.trans code) nextBudget)).weaken (by omega)

theorem shiftDownWhile_run (varName counterName : MlS) (hdistinct : varName ≠ counterName) :
    ∀ m : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F),
      state.code = originalRuntimeCode →
      ∀ w : BitVec 64, state.locals.lookup varName = some (.val (.word w)) →
      w.toNat < 256 ^ m →
      m ≤ state.clock →
      let body := ProgHOL.seq
        (.assign .local varName (.shift .lsr (.var .local varName) (.const 8)))
        (.assign .local counterName (.op .add [.var .local counterName, .const 1]))
      let evaluated := evaluateHOLFiniteState state
        (.while (.cmp .notEqual (.var .local varName) (.const 0)) body)
      state.clock ≤ evaluated.2.clock + m ∧
        evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  intro m
  induction m with
  | zero =>
    intro F state _code w atVar hlt _budget
    have hw0 : w = 0 := BitVec.eq_of_toNat_eq (by
      have h0 : w.toNat < 1 := by simpa using hlt
      simpa using h0)
    subst hw0
    dsimp only
    rw [evaluateHOLFiniteState_while_total]
    have hc : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
        (.cmp .notEqual (.var .local varName) (.const 0)) = some (.val (.word 0)) := by
      rw [evalHOLFinite_eq_toExact]
      simp [evalHOLExact, atVar, Compiler.Encoders.Asm.wordCmpHOL]
    rw [hc]; simp
  | succ m ih =>
    intro F state code w atVar hlt budget
    dsimp only
    rw [evaluateHOLFiniteState_while_total]
    by_cases hw0 : w = 0#64
    · subst hw0
      have hc : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
          (.cmp .notEqual (.var .local varName) (.const 0)) = some (.val (.word 0)) := by
        rw [evalHOLFinite_eq_toExact]
        simp [evalHOLExact, atVar, Compiler.Encoders.Asm.wordCmpHOL]
      rw [hc]; simp
    · have hc : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
          (.cmp .notEqual (.var .local varName) (.const 0)) = some (.val (.word 1)) := by
        rw [evalHOLFinite_eq_toExact]
        simp [evalHOLExact, atVar, Compiler.Encoders.Asm.wordCmpHOL, hw0]
      rw [hc]
      simp only [show (1 : BitVec 64) ≠ 0 by decide, if_true, ne_eq, not_false_eq_true]
      have hclk : state.clock ≠ 0 := by omega
      rw [if_neg hclk, fixClockHOLFinite_evaluateState]
      let body : ProgHOL 64 := ProgHOL.seq
        (.assign .local varName (.shift .lsr (.var .local varName) (.const 8)))
        (.assign .local counterName (.op .add [.var .local counterName, .const 1]))
      have hb := (ProgBounded.straight body rfl) (decClockHOLFinite state) code (by change 0 ≤ state.clock - 1; omega)
      have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata (decClockHOLFinite state) body
      have hnc := evaluate_noTopContinue body rfl (decClockHOLFinite state)
      have hv_run : evaluateHOLFiniteState (decClockHOLFinite state)
          (.assign .local varName (.shift .lsr (.var .local varName) (.const 8))) =
          (none, setVarHOLFinite varName (.val (.word (w >>> (8 : Nat)))) (decClockHOLFinite state)) := by
        simp [evaluateHOLFiniteState_assign, evalHOLExact, decClockHOLFinite, atVar, wordShiftHOL,
          lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite, setVarHOLFinite,
          shapeOfHOLExact, shapeEqHOL]
      have hframe := evaluate_avoidsLocal_flowing varName
        (.assign .local counterName (.op .add [.var .local counterName, .const 1]))
        (by simp [avoidsLocal, Ne.symm hdistinct])
        (setVarHOLFinite varName (.val (.word (w >>> (8 : Nat)))) (decClockHOLFinite state))
      rcases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with ⟨res, mid⟩
      rw [bodyRun] at hb hmeta hnc
      dsimp only at hb hmeta hnc
      obtain ⟨spent, kept, safe⟩ := hb
      change state.clock - 1 ≤ mid.clock + 0 at spent
      change mid.clock ≤ state.clock - 1 at kept
      cases res with
      | none =>
        dsimp only
        have hseq := bodyRun
        dsimp only [body] at hseq
        rw [evaluateHOLFiniteState_seq_line780, hv_run] at hseq
        dsimp only at hseq
        rw [hseq] at hframe
        have hmid_var : mid.locals.lookup varName = some (.val (.word (w >>> (8 : Nat)))) := by
          rw [hframe (Or.inl rfl)]
          simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hshr : (w >>> (8 : Nat)).toNat < 256 ^ m := by
          rw [BitVec.toNat_ushiftRight]
          have hpow : 256 ^ (m + 1) = 256 ^ m * 256 := Nat.pow_succ 256 m
          have hsh : w.toNat >>> 8 = w.toNat / 256 := Nat.shiftRight_eq_div_pow w.toNat 8
          omega
        obtain ⟨t1, t2, t3⟩ := ih mid (hmeta.1.trans code) (w >>> (8 : Nat)) hmid_var hshr (by omega)
        exact ⟨by omega, by omega, t3⟩
      | some r =>
        cases r with
        | «continue» => exact absurd rfl hnc
        | «break» => exact ⟨by simp; omega, by simp; omega, by simp⟩
        | timeOut => exact absurd rfl safe
        | _ => exact ⟨by simp; omega, by simp; omega, by simp⟩

theorem parityTwoStepWhile_run (counter limit outCounter : MlS)
    (hne_cl : counter ≠ limit) (hne_co : counter ≠ outCounter) (hne_lo : outCounter ≠ limit)
    (K : BitVec 64) {prefixProg : ProgHOL 64}
    (hpBounded : ProgBounded prefixProg 0)
    (hpAvoidC : avoidsLocal counter prefixProg = true)
    (hpAvoidL : avoidsLocal limit prefixProg = true)
    (hpNoCont : noTopContinue prefixProg = true) :
    ∀ m : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F),
      state.code = originalRuntimeCode →
      ∀ w : BitVec 64, state.locals.lookup counter = some (.val (.word w)) →
      state.locals.lookup limit = some (.val (.word K)) →
      w.toNat % 2 = K.toNat % 2 →
      (w.toNat < K.toNat → (K.toNat - w.toNat) / 2 ≤ m) →
      m ≤ state.clock →
      let body := ProgHOL.seq prefixProg
        (.seq (.assign .local counter (.op .add [.var .local counter, .const 2]))
          (.assign .local outCounter (.op .add [.var .local outCounter, .const 1])))
      let evaluated := evaluateHOLFiniteState state
        (.while (.cmp .lower (.var .local counter) (.var .local limit)) body)
      state.clock ≤ evaluated.2.clock + m ∧
        evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have hcounted : StepCountedBody counter 2
      (.seq prefixProg
        (.seq (.assign .local counter (.op .add [.var .local counter, .const 2]))
          (.assign .local outCounter (.op .add [.var .local outCounter, .const 1])))) 0 := by
    have htail : StepCountedBody counter 2
        (.seq (.assign .local counter (.op .add [.var .local counter, .const 2]))
          (.assign .local outCounter (.op .add [.var .local outCounter, .const 1]))) 0 :=
      StepCountedBody.seqZeroRight (StepCountedBody.incr 2)
        (ProgBounded.straight _ rfl) (by simp [avoidsLocal, Ne.symm hne_co]) rfl
    exact StepCountedBody.seq prefixProg hpBounded hpAvoidC hpNoCont htail
  have havoidL : avoidsLocal limit
      (.seq prefixProg
        (.seq (.assign .local counter (.op .add [.var .local counter, .const 2]))
          (.assign .local outCounter (.op .add [.var .local outCounter, .const 1])))) = true := by
    simp [avoidsLocal, hpAvoidL, hne_cl, hne_lo]
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro F state code w atCounter atLimit hpar hdist budget
    dsimp only
    rw [evaluateHOLFiniteState_while_total]
    by_cases lt : w.toNat < K.toNat
    · have hcond : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
          (.cmp .lower (.var .local counter) (.var .local limit)) = some (.val (.word 1)) := by
        rw [evalHOLFinite_eq_toExact]
        simp [evalHOLExact, atCounter, atLimit, Compiler.Encoders.Asm.wordCmpHOL, lt, BitVec.lt_def]
      rw [hcond]
      simp only [show (1 : BitVec 64) ≠ 0 by decide, if_true, ne_eq, not_false_eq_true]
      have hle2 : w.toNat + 2 ≤ K.toNat := by omega
      have hm_pos : 0 < m := by
        have hd := hdist lt
        omega
      have hclk : state.clock ≠ 0 := by omega
      rw [if_neg hclk, fixClockHOLFinite_evaluateState]
      have stepRun := hcounted.run (decClockHOLFinite state) code w atCounter
        (by change 0 ≤ state.clock - 1; omega)
      let body : ProgHOL 64 := ProgHOL.seq prefixProg
        (.seq (.assign .local counter (.op .add [.var .local counter, .const 2]))
          (.assign .local outCounter (.op .add [.var .local outCounter, .const 1])))
      have hfl := evaluate_avoidsLocal_flowing limit body havoidL (decClockHOLFinite state)
      rcases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with ⟨res, mid⟩
      rw [bodyRun] at stepRun hfl
      dsimp only at stepRun hfl
      obtain ⟨spent, kept, safe, noCont, advance⟩ := stepRun
      change state.clock - 1 ≤ mid.clock + 0 at spent
      change mid.clock ≤ state.clock - 1 at kept
      cases res with
      | none =>
        dsimp only
        obtain ⟨nextCounter, nextCode⟩ := advance rfl
        have hadd : (w + 2).toNat = w.toNat + 2 :=
          BitVec.toNat_add_of_lt (by have := K.isLt; simp; omega)
        have nextLimit : mid.locals.lookup limit = some (.val (.word K)) :=
          (hfl (Or.inl rfl)).trans atLimit
        obtain ⟨t1, t2, t3⟩ := ih (m - 1) (by omega) mid (nextCode.trans code)
          (w + 2) nextCounter nextLimit (by rw [hadd]; omega)
          (fun hlt2 => by have hd := hdist lt; rw [hadd] at hlt2 ⊢; omega)
          (by omega)
        exact ⟨by omega, by omega, t3⟩
      | some r =>
        cases r with
        | «continue» => exact absurd rfl noCont
        | «break» => exact ⟨by simp; omega, by simp; omega, by simp⟩
        | timeOut => exact absurd rfl safe
        | _ => exact ⟨by simp; omega, by simp; omega, by simp⟩
    · have hcond : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
          (.cmp .lower (.var .local counter) (.var .local limit)) = some (.val (.word 0)) := by
        rw [evalHOLFinite_eq_toExact]
        simp [evalHOLExact, atCounter, atLimit, Compiler.Encoders.Asm.wordCmpHOL, lt, BitVec.lt_def]
      rw [hcond]; simp

theorem funBounded_u256_limb : FunBounded (ofString "u256_limb") 0 :=
  funBounded_of_guestAst 43 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_limb 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_bit_length64 : FunBounded (ofString "bit_length64") 0 :=
  funBounded_of_guestAst 77 (by rw [guestAst_len]; decide) Guest.Software.guestFn_bit_length64 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_u256_bit_length : FunBounded (ofString "u256_bit_length") 4 := by
  refine funBounded_of_guestAst 78 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_bit_length 4 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_u256_bit_length,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine ProgBounded.weaken
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
    (by decide)

theorem funBounded_u256_byte_length : FunBounded (ofString "u256_byte_length") 5 := by
  refine funBounded_of_guestAst 79 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_byte_length 5 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_u256_byte_length,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_u256_bit_length _ _ _ (ProgBounded.straight _ rfl))
    (by decide)

theorem funBounded_rlp_fail : FunBounded (ofString "rlp_fail") 0 :=
  funBounded_of_guestAst 105 (by rw [guestAst_len]; decide) Guest.Software.guestFn_rlp_fail 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_udivmod : FunBounded (ofString "udivmod") 65 := by
  refine funBounded_of_guestAst 33 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_udivmod 65 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_udivmod,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine ProgBounded.weaken
    (ProgBounded.seq
      (ProgBounded.iteMax _ (ProgBounded.call funBounded_trap_with none _) (ProgBounded.straight _ rfl))
      (ProgBounded.seq (ProgBounded.straight _ rfl)
        (ProgBounded.dec _ _ _ (ProgBounded.dec _ _ _
          (ProgBounded.downCountedConstDec (ofString "i") .less (Or.inl rfl) 64 (by decide)
            (StepCountedBody.seqZeroRight StepCountedBody.decr (ProgBounded.straight _ rfl) rfl rfl)
            (ProgBounded.straight _ rfl))))))
    (by decide)

theorem funBounded_udiv : FunBounded (ofString "udiv") 66 := by
  refine funBounded_of_guestAst 34 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_udiv 66 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_udiv,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_udivmod _ _ _ (ProgBounded.straight _ rfl))
    (by decide)

theorem funBounded_u256_from_be : FunBounded (ofString "u256_from_be") (2 ^ 64 - 1 + 4) := by
  refine funBounded_of_guestAst 86 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_from_be (2 ^ 64 - 1 + 4) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_u256_from_be,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine ProgBounded.weaken
    (ProgBounded.seq
      (ProgBounded.iteMax _
        (ProgBounded.dec _ _ _
          (ProgBounded.decCall funBounded_bswap64 _ _ _
            (ProgBounded.seq (ProgBounded.straight _ rfl)
              (ProgBounded.decCall funBounded_bswap64 _ _ _
                (ProgBounded.seq (ProgBounded.straight _ rfl)
                  (ProgBounded.decCall funBounded_bswap64 _ _ _
                    (ProgBounded.seq (ProgBounded.straight _ rfl)
                      (ProgBounded.decCall funBounded_bswap64 _ _ _
                        (ProgBounded.straight _ rfl)))))))))
        (ProgBounded.straight _ rfl))
      (ProgBounded.dec _ _ _ (ProgBounded.dec _ _ _ (ProgBounded.dec _ _ _ (ProgBounded.dec _ _ _
        (ProgBounded.expCountedDec (ofString "i") .lower (Or.inr rfl) (.var .local (ofString "n"))
          (StepCountedBody.dec _ _ _ (by decide)
            (StepCountedBody.dec _ _ _ (by decide)
              (StepCountedBody.dec _ _ _ (by decide)
                (StepCountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
                  (StepCountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
                    (StepCountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
                      (StepCountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
                        (StepCountedBody.incr 1))))))))
          (by decide)
          (ProgBounded.straight _ rfl)))))))
    (by decide)

theorem funBounded_u256_to_be_min : FunBounded (ofString "u256_to_be_min") ((2 ^ 64 - 1) * 2 + 6) := by
  refine funBounded_of_guestAst 88 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_to_be_min ((2 ^ 64 - 1) * 2 + 6) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_u256_to_be_min,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine ProgBounded.weaken
    (ProgBounded.decCall funBounded_u256_byte_length _ _ _
      (ProgBounded.expCountedDec (ofString "i") .lower (Or.inr rfl) (.var .local (ofString "len"))
        (StepCountedBody.dec _ _ _ (by decide)
          (StepCountedBody.decCall funBounded_u256_limb _ _ _ (by decide)
            (StepCountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
              (StepCountedBody.incr 1))))
        (by decide)
        (ProgBounded.straight _ rfl)))
    (by decide)

theorem funBounded_rlp_read_length : FunBounded (ofString "rlp_read_length") (2 ^ 64) := by
  refine funBounded_of_guestAst 106 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_rlp_read_length (2 ^ 64) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_rlp_read_length,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine ProgBounded.weaken
    (ProgBounded.seq
      (ProgBounded.iteMax _ (ProgBounded.call funBounded_rlp_fail none _) (ProgBounded.straight _ rfl))
      (ProgBounded.dec _ _ _
        (ProgBounded.expCountedDec (ofString "i") .lower (Or.inr rfl) (.var .local (ofString "n"))
          (StepCountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl (StepCountedBody.incr 1))
          (by decide)
          (ProgBounded.straight _ rfl))))
    (by decide)

theorem funBounded_rlp_be_len : FunBounded (ofString "rlp_be_len") 8 := by
  refine funBounded_of_guestAst 118 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_rlp_be_len 8 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_rlp_be_len,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  intro F state code budget
  apply RunBounded.decConst
  let s0 := setVarHOLFinite (ofString "n") (.val (.word (0#64))) state
  change RunBounded s0 _ _
  have hs0_code : s0.code = originalRuntimeCode := code
  cases hv : s0.locals.lookup (ofString "v") with
  | none =>
    unfold RunBounded
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total]
    have hc : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
        (.cmp .notEqual (.var .local (ofString "v")) (.const (0#64))) = none := by
      rw [evalHOLFinite_eq_toExact]
      simp [evalHOLExact, hv]
    rw [hc]; simp
  | some val =>
    cases val with
    | rStruct fs =>
      unfold RunBounded
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total]
      have hc : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
          (.cmp .notEqual (.var .local (ofString "v")) (.const (0#64))) = none := by
        rw [evalHOLFinite_eq_toExact]
        simp [evalHOLExact, hv]
      rw [hc]; simp
    | nStruct nm fs =>
      unfold RunBounded
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total]
      have hc : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
          (.cmp .notEqual (.var .local (ofString "v")) (.const (0#64))) = none := by
        rw [evalHOLFinite_eq_toExact]
        simp [evalHOLExact, hv]
      rw [hc]; simp
    | val wv =>
      cases wv with
      | word w =>
        have hlt : w.toNat < 256 ^ 8 := by
          have := w.isLt
          have hpow : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
          omega
        have loop := shiftDownWhile_run (ofString "v") (ofString "n") (by decide) 8 s0 hs0_code w hv hlt budget
        exact (RunBounded.seq loop (a := 8) (b := 0) (by change 8 + 0 ≤ state.clock; omega)
          (fun next _ nextCode nextBudget =>
            (ProgBounded.straight (.return (.var .local (ofString "n"))) rfl)
              next (nextCode.trans hs0_code) nextBudget)).weaken (by omega)

theorem funBounded_rlp_put_be : FunBounded (ofString "rlp_put_be") (2 ^ 64 - 1) := by
  refine funBounded_of_guestAst 119 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_rlp_put_be (2 ^ 64 - 1) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_rlp_put_be,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.downCountedVarDec (ofString "i") (ofString "n")
      (StepCountedBody.seqZeroRight StepCountedBody.decr (ProgBounded.straight _ rfl) rfl rfl)
      (ProgBounded.straight _ rfl))
    (by decide)

/-! ## Section 2: Statically Bounded Memory, Keccak, Nibble, and RLP Combinators -/

private theorem progBounded_seq_straight (first : ProgHOL 64) {tail : ProgHOL 64} {cost : Nat}
    (hs : extStraightLine first = true) (hrest : ProgBounded tail cost) :
    ProgBounded (.seq first tail) cost :=
  ProgBounded.weaken (ProgBounded.seq (ProgBounded.straight first hs) hrest) (Nat.zero_add cost).le

private theorem countedBody_seq_straight {counter : MlS} {step : BitVec 64}
    (first : ProgHOL 64) {tail : ProgHOL 64} {cost : Nat}
    (hs : extStraightLine first = true)
    (ha : avoidsLocal counter first = true)
    (hn : noTopContinue first = true)
    (hrest : CountedBody counter step tail cost) :
    CountedBody counter step (.seq first tail) cost :=
  (Nat.zero_add cost) ▸ CountedBody.seq first (ProgBounded.straight first hs) ha hn hrest

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
          rw [pan_three_word_lookup code fn p1 p2 p3 body w1 K w3 hp12 hp13 hp23 hlookup_fn] at hfound
          cases hfound
          simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hp23]

private theorem three_arg_lookup_last
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
          rw [pan_three_word_lookup code fn p1 p2 p3 body w1 w2 K hp12 hp13 hp23 hlookup_fn] at hfound
          cases hfound
          simp [HolFiniteMapExact.lookup_update, FUPDATE]

private theorem lookup_key_to_nibbles :
    originalRuntimeCode.lookup (ofString "key_to_nibbles") =
      some ([(ofString "key", .one), (ofString "n", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_key_to_nibbles, .one) :=
  lookup_of_guestAst_getElem 248 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_key_to_nibbles) rfl

theorem runBounded_key_to_nibbles_body {F : Type}
    (state : PanSemStateFiniteExact 64 F) (K : BitVec 64)
    (hsmall : K.toNat + 4 < 2 ^ 64)
    (hcode : state.code = originalRuntimeCode)
    (atN : state.locals.lookup (ofString "n") = some (.val (.word K)))
    (hbudget : K.toNat / 4 + 3 ≤ state.clock) :
    RunBounded state (sourceFnBody Guest.Software.guestFn_key_to_nibbles) (K.toNat / 4 + 3) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_key_to_nibbles,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply RunBounded.decConst
  let s0 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) state
  have hs0_clk : s0.clock = state.clock := rfl
  have hs0_code : s0.code = originalRuntimeCode := hcode
  have hs0_i : s0.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs0_n : s0.locals.lookup (ofString "n") = some (.val (.word K)) := by
    have hne : ofString "i" ≠ ofString "n" := by decide
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, atN]
  let b4 : ProgHOL 64 :=
    .dec (ofString "b0") .one
      (.loadByte (.op .add [.var .local (ofString "key"), .var .local (ofString "i")]))
      (.seq
        (.storeByte
          (.op .add [.var .local (ofString "out"),
            .panop .mul [.const 2#64, .var .local (ofString "i")]])
          (.shift .lsr (.var .local (ofString "b0")) (.const 4#64)))
        (.seq
          (.storeByte
            (.op .add [.var .local (ofString "out"),
              .panop .mul [.const 2#64, .var .local (ofString "i")], .const 1#64])
            (.op .and [.var .local (ofString "b0"), .const 15#64]))
          (.dec (ofString "b1") .one
            (.loadByte (.op .add
              [.var .local (ofString "key"), .var .local (ofString "i"), .const 1#64]))
            (.seq
              (.storeByte
                (.op .add [.var .local (ofString "out"),
                  .panop .mul [.const 2#64, .var .local (ofString "i")], .const 2#64])
                (.shift .lsr (.var .local (ofString "b1")) (.const 4#64)))
              (.seq
                (.storeByte
                  (.op .add [.var .local (ofString "out"),
                    .panop .mul [.const 2#64, .var .local (ofString "i")], .const 3#64])
                  (.op .and [.var .local (ofString "b1"), .const 15#64]))
                (.dec (ofString "b2") .one
                  (.loadByte (.op .add
                    [.var .local (ofString "key"), .var .local (ofString "i"), .const 2#64]))
                  (.seq
                    (.storeByte
                      (.op .add [.var .local (ofString "out"),
                        .panop .mul [.const 2#64, .var .local (ofString "i")], .const 4#64])
                      (.shift .lsr (.var .local (ofString "b2")) (.const 4#64)))
                    (.seq
                      (.storeByte
                        (.op .add [.var .local (ofString "out"),
                          .panop .mul [.const 2#64, .var .local (ofString "i")], .const 5#64])
                        (.op .and [.var .local (ofString "b2"), .const 15#64]))
                      (.dec (ofString "b3") .one
                        (.loadByte (.op .add
                          [.var .local (ofString "key"), .var .local (ofString "i"), .const 3#64]))
                        (.seq
                          (.storeByte
                            (.op .add [.var .local (ofString "out"),
                              .panop .mul [.const 2#64, .var .local (ofString "i")], .const 6#64])
                            (.shift .lsr (.var .local (ofString "b3")) (.const 4#64)))
                          (.seq
                            (.storeByte
                              (.op .add [.var .local (ofString "out"),
                                .panop .mul [.const 2#64, .var .local (ofString "i")], .const 7#64])
                              (.op .and [.var .local (ofString "b3"), .const 15#64]))
                            (.assign .local (ofString "i")
                              (.op .add [.var .local (ofString "i"), .const 4#64])))))))))))))
  let b1 : ProgHOL 64 :=
    .dec (ofString "b") .one
      (.loadByte (.op .add [.var .local (ofString "key"), .var .local (ofString "i")]))
      (.seq
        (.storeByte
          (.op .add [.var .local (ofString "out"),
            .panop .mul [.const 2#64, .var .local (ofString "i")]])
          (.shift .lsr (.var .local (ofString "b")) (.const 4#64)))
        (.seq
          (.storeByte
            (.op .add [.var .local (ofString "out"),
              .panop .mul [.const 2#64, .var .local (ofString "i")], .const 1#64])
            (.op .and [.var .local (ofString "b"), .const 15#64]))
          (.assign .local (ofString "i")
            (.op .add [.var .local (ofString "i"), .const 1#64]))))
  have hb4 : CountedBody (ofString "i") 4#64 b4 0 := by
    refine CountedBody.dec _ _ _ (by decide) ?_
    refine countedBody_seq_straight _ rfl rfl rfl (countedBody_seq_straight _ rfl rfl rfl ?_)
    refine CountedBody.dec _ _ _ (by decide) ?_
    refine countedBody_seq_straight _ rfl rfl rfl (countedBody_seq_straight _ rfl rfl rfl ?_)
    refine CountedBody.dec _ _ _ (by decide) ?_
    refine countedBody_seq_straight _ rfl rfl rfl (countedBody_seq_straight _ rfl rfl rfl ?_)
    refine CountedBody.dec _ _ _ (by decide) ?_
    refine countedBody_seq_straight _ rfl rfl rfl (countedBody_seq_straight _ rfl rfl rfl ?_)
    exact CountedBody.incr
  have hb1 : CountedBody (ofString "i") 1#64 b1 0 := by
    refine CountedBody.dec _ _ _ (by decide) ?_
    refine countedBody_seq_straight _ rfl rfl rfl (countedBody_seq_straight _ rfl rfl rfl ?_)
    exact CountedBody.incr
  change RunBounded s0 _ (K.toNat / 4 + 3)
  unfold RunBounded
  rw [evaluateHOLFiniteState_seq_line780]
  have h4 := notLowerStrideWhile_run (ofString "i") (ofString "n") K 4#64
    (by simpa using hsmall) (by decide) hb4 rfl rfl
    (K.toNat / 4) s0 hs0_code 0#64 hs0_i hs0_n (by simp) (by simp)
    (by simp only [Nat.zero_add, Nat.mul_one]; change K.toNat / 4 ≤ state.clock; omega)
  rcases hr4 : evaluateHOLFiniteState s0
      (.while (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const 4#64])) b4) with ⟨res4, s1⟩
  rw [hr4] at h4
  dsimp only at h4 ⊢
  cases res4 with
  | some r =>
    dsimp only
    exact ⟨by simp only [Nat.zero_add, Nat.mul_one] at h4; omega, h4.2.1, h4.2.2.1⟩
  | none =>
    dsimp only
    obtain ⟨w1, hs1_i, hs1_n, _, hw1_le, hw1_rem, hs1_code⟩ := h4.2.2.2 rfl
    rw [evaluateHOLFiniteState_seq_line780]
    have hrem3 : K.toNat - w1.toNat ≤ 3 := by
      change K.toNat < w1.toNat + 4 at hw1_rem
      omega
    have h1 := variableCountedWhile_run (ofString "i") (ofString "n") .lower (Or.inr rfl) K
      (fun h => by cases h) hb1 rfl (K.toNat - w1.toNat) s1 (hs1_code.trans hs0_code)
      w1 hs1_i hs1_n hw1_le rfl
      (by simp only [Nat.zero_add, Nat.mul_one] at h4 ⊢; rw [hs0_clk] at h4; omega)
    have h1_meta := PanRunBounded.evaluateHOLFiniteState_metadata s1
      (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) b1)
    rcases hr1 : evaluateHOLFiniteState s1
        (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) b1) with
      ⟨res1, s2⟩
    rw [hr1] at h1 h1_meta
    dsimp only at h1 h1_meta ⊢
    cases res1 with
    | some r =>
      dsimp only
      exact ⟨by simp only [Nat.zero_add, Nat.mul_one] at h4 h1; omega, by omega, h1.2.2⟩
    | none =>
      dsimp only
      have ht := (ProgBounded.straight (.return (.const 0#64)) rfl) s2
        (h1_meta.1.trans (hs1_code.trans hs0_code)) (Nat.zero_le _)
      exact ⟨by simp only [Nat.zero_add, Nat.mul_one] at h4 h1 ht; omega, by omega, ht.2.2⟩

theorem progBounded_key_to_nibbles_const (destination : Option (VarKind × MlS))
    (key out : ExpHOL 64) (K : BitVec 64) (hsmall : K.toNat + 4 < 2 ^ 64) :
    ProgBounded (.call (some (destination, none)) (ofString "key_to_nibbles") [key, .const K, out])
      (K.toNat / 4 + 4) := by
  intro F state hcode hbudget
  cases hargs : evalListHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a)) [key, .const K, out] with
  | none =>
    rw [evaluateHOLFiniteState_call, hargs]
    simp
  | some vs =>
    obtain ⟨v1, v3, rfl⟩ := evalListHOLFinite_three_word2 state key (.const K) out K hargs
      (by rw [evalHOLFinite_eq_toExact]; rfl)
    exact RunBounded.call hargs hbudget (fun body locals rs hfound => by
      rw [hcode] at hfound
      obtain ⟨rfl, hn⟩ := three_arg_lookup_mid originalRuntimeCode.lookup
        (ofString "key_to_nibbles") (ofString "key") (ofString "n") (ofString "out")
        (sourceFnBody Guest.Software.guestFn_key_to_nibbles)
        (by decide) (by decide) (by decide) lookup_key_to_nibbles hfound
      exact runBounded_key_to_nibbles_body (callEntryStateHOLFinite state locals) K hsmall hcode hn
        (by change K.toNat / 4 + 3 ≤ state.clock - 1; omega))

theorem funBounded_keccak_f1600 : FunBounded (ofString "keccak_f1600") 24 := by
  refine funBounded_of_guestAst 101 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_keccak_f1600 24 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_keccak_f1600,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  iterate 25 apply ProgBounded.dec _ _ _
  refine ProgBounded.weaken
    (ProgBounded.countedDec (ofString "r") .less (Or.inl rfl) 24 1 0
      (by decide) (by decide) (by decide) (cost := 0) ?_ (ProgBounded.straight _ (by decide)))
    (by decide)
  iterate 60 (refine CountedBody.dec _ _ _ (by decide) ?_)
  iterate 26 (refine countedBody_seq_straight _ (by decide) (by decide) (by decide) ?_)
  exact CountedBody.incr

theorem funBounded_keccak_absorb_block : FunBounded (ofString "keccak_absorb_block") 161 := by
  refine funBounded_of_guestAst 102 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_keccak_absorb_block 161 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_keccak_absorb_block,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  intro F state hcode hbudget
  apply RunBounded.decConst
  let s0 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) state
  have hs0_code : s0.code = originalRuntimeCode := hcode
  have hs0_i : s0.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have htail : ProgBounded
      (.seq (.call (some (none, none)) (ofString "keccak_f1600") [.var .local (ofString "stp")])
        (.return (.const 0#64))) 25 :=
    ProgBounded.seq (ProgBounded.call funBounded_keccak_f1600 none [.var .local (ofString "stp")])
      (ProgBounded.straight _ (by decide))
  refine RunBounded.seq ?_ (a := 136) (b := 25) (by change 136 + 25 ≤ state.clock; omega)
    (fun next _ nextCode nextBudget => htail next (nextCode.trans hs0_code) nextBudget)
  apply RunBounded.ite
  · unfold RunBounded
    exact countedWhile_from (ofString "i") .less (Or.inl rfl) 136 8 (by decide) (by decide)
      (cost := 0) (countedBody_seq_straight _ (by decide) (by decide) (by decide) CountedBody.incr)
      s0 hs0_code 0#64 hs0_i (by decide) (by change 136 * (0 + 1) ≤ state.clock; omega)
  · unfold RunBounded
    exact countedWhile_from (ofString "i") .less (Or.inl rfl) 136 8 (by decide) (by decide)
      (cost := 0) (countedBody_seq_straight _ (by decide) (by decide) (by decide) CountedBody.incr)
      s0 hs0_code 0#64 hs0_i (by decide) (by change 136 * (0 + 1) ≤ state.clock; omega)

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
      (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "stp"), .const 200#64])
      33 :=
    ProgBounded.weaken
      (progBounded_memzero_const none (.var .local (ofString "stp")) 200#64 (by decide))
      (by decide)
  have hmz200_run := hmz200 s1 hs1_code (by rw [hs1_clk]; omega)
  have hmz200_fn := evaluate_avoidsLocal_flowing (ofString "n")
    (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "stp"), .const 200#64])
    rfl s1
  have hmz200_meta := PanRunBounded.evaluateHOLFiniteState_metadata s1
    (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "stp"), .const 200#64])
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
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 136#64])))) =
        (none, s3) := by
      rw [evaluateHOLFiniteState_while_total]
      have hcond : evalHOLFinite s3 (h := fun a => Classical.propDecidable (s3.memaddrs a))
          (.cmp .notLower (.var .local (ofString "n"))
            (.op .add [.var .local (ofString "i"), .const 136#64])) =
          some (.val (.word 0#64)) := by
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
      simp [evalHOLExact, evalListHOLExact, hs3_n, hs3_i, wordOpHOL, wordOp, valueIsWord, valueWord]
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
          have hrem_k :
              @evalHOLExact 64 F _ s5.toExact
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

theorem progBounded_keccak256_small_const (destination : Option (VarKind × MlS))
    (p out : ExpHOL 64) (K : BitVec 64) (hlt : K.toNat < 136) :
    ProgBounded (.call (some (destination, none)) (ofString "keccak256") [p, .const K, out])
      (K.toNat / 8 + 241) := by
  intro F state hcode hbudget
  cases hargs : evalListHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a)) [p, .const K, out] with
  | none =>
    rw [evaluateHOLFiniteState_call, hargs]
    simp
  | some vs =>
    obtain ⟨v1, v3, rfl⟩ := evalListHOLFinite_three_word2 state p (.const K) out K hargs
      (by rw [evalHOLFinite_eq_toExact]; rfl)
    exact RunBounded.call hargs hbudget (fun body locals rs hfound => by
      rw [hcode] at hfound
      obtain ⟨rfl, hn⟩ := three_arg_lookup_mid originalRuntimeCode.lookup
        (ofString "keccak256") (ofString "p") (ofString "n") (ofString "out")
        (sourceFnBody Guest.Software.guestFn_keccak256)
        (by decide) (by decide) (by decide) lookup_keccak256 hfound
      exact runBounded_keccak256_small_body (callEntryStateHOLFinite state locals) K hlt hcode hn
        (by change K.toNat / 8 + 240 ≤ state.clock - 1; omega))

theorem progBounded_keccak256_small_bounded (destination : Option (VarKind × MlS))
    (p sizeExp out : ExpHOL 64) (M : Nat) (hlt : M < 136)
    (hbnd : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (K : BitVec 64),
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) sizeExp =
        some (.val (.word K)) → K.toNat ≤ M) :
    ProgBounded (.call (some (destination, none)) (ofString "keccak256") [p, sizeExp, out])
      (M / 8 + 241) := by
  intro F state hcode hbudget
  cases hargs : evalListHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a)) [p, sizeExp, out] with
  | none =>
    rw [evaluateHOLFiniteState_call, hargs]
    simp
  | some vs =>
    have hmid : ∃ v1 K v3, vs = [v1, .val (.word K), v3] ∨
        PanSemStateFiniteExact.lookupCodeHOLFinite state.code.lookup (ofString "keccak256") vs =
          none := by
      rw [evalListHOLFinite_eq_toExact] at hargs
      simp only [evalListHOLExact] at hargs
      rcases h1 : @evalHOLExact 64 F _ state.toExact
          (fun a => Classical.propDecidable (state.memaddrs a)) p with _ | v1
      · rw [h1] at hargs; cases hargs
      · rw [h1] at hargs
        rcases h2 : @evalHOLExact 64 F _ state.toExact
            (fun a => Classical.propDecidable (state.memaddrs a)) sizeExp with _ | v2
        · rw [h2] at hargs; cases hargs
        · rw [h2] at hargs
          rcases h3 : @evalHOLExact 64 F _ state.toExact
              (fun a => Classical.propDecidable (state.memaddrs a)) out with _ | v3
          · rw [h3] at hargs; cases hargs
          · rw [h3] at hargs
            cases hargs
            cases v2 with
            | val wv =>
              cases wv with
              | word K =>
                exact ⟨v1, K, v3, Or.inl rfl⟩
            | rStruct _ =>
              refine ⟨v1, 0#64, v3, Or.inr ?_⟩
              rw [hcode]
              unfold PanSemStateFiniteExact.lookupCodeHOLFinite
              split
              · rfl
              · rename_i _ _ _ raw
                simp [lookupCodeHOLExact, lookup_keccak256, shapeOfHOLExact, shapeEqHOL] at raw
            | nStruct _ _ =>
              refine ⟨v1, 0#64, v3, Or.inr ?_⟩
              rw [hcode]
              unfold PanSemStateFiniteExact.lookupCodeHOLFinite
              split
              · rfl
              · rename_i _ _ _ raw
                simp [lookupCodeHOLExact, lookup_keccak256, shapeOfHOLExact, shapeEqHOL] at raw
    obtain ⟨v1, K, v3, hvs⟩ := hmid
    rcases hvs with rfl | hnone
    · have hk_eval : evalHOLFinite state
          (h := fun a => Classical.propDecidable (state.memaddrs a)) sizeExp =
          some (.val (.word K)) := by
        rw [evalListHOLFinite_eq_toExact] at hargs
        rw [evalHOLFinite_eq_toExact]
        simp only [evalListHOLExact] at hargs
        rcases h1 : @evalHOLExact 64 F _ state.toExact
            (fun a => Classical.propDecidable (state.memaddrs a)) p with _ | x1
        · rw [h1] at hargs; cases hargs
        · rw [h1] at hargs
          rcases h2 : @evalHOLExact 64 F _ state.toExact
              (fun a => Classical.propDecidable (state.memaddrs a)) sizeExp with _ | x2
          · rw [h2] at hargs; cases hargs
          · rw [h2] at hargs
            rcases h3 : @evalHOLExact 64 F _ state.toExact
                (fun a => Classical.propDecidable (state.memaddrs a)) out with _ | x3
            · rw [h3] at hargs; cases hargs
            · rw [h3] at hargs
              cases hargs
              rfl
      have hK_le : K.toNat ≤ M := hbnd state K hk_eval
      have hdiv : K.toNat / 8 ≤ M / 8 := Nat.div_le_div_right hK_le
      exact RunBounded.call hargs hbudget (fun body locals rs hfound => by
        rw [hcode] at hfound
        obtain ⟨rfl, hn⟩ := three_arg_lookup_mid originalRuntimeCode.lookup
          (ofString "keccak256") (ofString "p") (ofString "n") (ofString "out")
          (sourceFnBody Guest.Software.guestFn_keccak256)
          (by decide) (by decide) (by decide) lookup_keccak256 hfound
        exact (runBounded_keccak256_small_body (callEntryStateHOLFinite state locals)
          K (by omega) hcode hn
          (by change K.toNat / 8 + 240 ≤ state.clock - 1; omega)).weaken (by omega))
    · rw [evaluateHOLFiniteState_call, hargs]
      dsimp only
      rw [hnone]
      simp

private theorem lookup_memcpy :
    originalRuntimeCode.lookup (ofString "memcpy") =
      some ([(ofString "dst", .one), (ofString "src", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_memcpy, .one) :=
  lookup_of_guestAst_getElem 16 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memcpy) rfl

private theorem runBounded_memcpy_local_body {F : Type}
    (state : PanSemStateFiniteExact 64 F) (K : BitVec 64)
    (hsmall : K.toNat + 32 < 2 ^ 64)
    (hcode : state.code = originalRuntimeCode)
    (atN : state.locals.lookup (ofString "n") = some (.val (.word K)))
    (hbudget : K.toNat / 8 + 7 ≤ state.clock) :
    RunBounded state (sourceFnBody Guest.Software.guestFn_memcpy) (K.toNat / 8 + 7) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_memcpy,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply RunBounded.decConst
  let s0 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) state
  have hs0_clk : s0.clock = state.clock := rfl
  have hs0_code : s0.code = originalRuntimeCode := hcode
  have hs0_i : s0.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs0_n : s0.locals.lookup (ofString "n") = some (.val (.word K)) := by
    have hne : ofString "i" ≠ ofString "n" := by decide
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, atN]
  let b32 : ProgHOL 64 :=
    .seq
      (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
        (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
      (.seq
        (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 8#64])
          (.load .one (.op .add
            [.var .local (ofString "src"), .var .local (ofString "i"), .const 8#64])))
        (.seq
          (.store (.op .add
              [.var .local (ofString "dst"), .var .local (ofString "i"), .const 16#64])
            (.load .one (.op .add
              [.var .local (ofString "src"), .var .local (ofString "i"), .const 16#64])))
          (.seq
            (.store (.op .add
                [.var .local (ofString "dst"), .var .local (ofString "i"), .const 24#64])
              (.load .one (.op .add
                [.var .local (ofString "src"), .var .local (ofString "i"), .const 24#64])))
            (.assign .local (ofString "i")
              (.op .add [.var .local (ofString "i"), .const 32#64])))))
  let b8a : ProgHOL 64 :=
    .seq
      (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
        (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8#64]))
  let b8b : ProgHOL 64 :=
    .seq
      (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
        (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
      (.seq
        (.storeByte (.op .add
            [.var .local (ofString "dst"), .var .local (ofString "i"), .const 1#64])
          (.loadByte (.op .add
            [.var .local (ofString "src"), .var .local (ofString "i"), .const 1#64])))
        (.seq
          (.storeByte (.op .add
              [.var .local (ofString "dst"), .var .local (ofString "i"), .const 2#64])
            (.loadByte (.op .add
              [.var .local (ofString "src"), .var .local (ofString "i"), .const 2#64])))
          (.seq
            (.storeByte (.op .add
                [.var .local (ofString "dst"), .var .local (ofString "i"), .const 3#64])
              (.loadByte (.op .add
                [.var .local (ofString "src"), .var .local (ofString "i"), .const 3#64])))
            (.seq
              (.storeByte (.op .add
                  [.var .local (ofString "dst"), .var .local (ofString "i"), .const 4#64])
                (.loadByte (.op .add
                  [.var .local (ofString "src"), .var .local (ofString "i"), .const 4#64])))
              (.seq
                (.storeByte (.op .add
                    [.var .local (ofString "dst"), .var .local (ofString "i"), .const 5#64])
                  (.loadByte (.op .add
                    [.var .local (ofString "src"), .var .local (ofString "i"), .const 5#64])))
                (.seq
                  (.storeByte (.op .add
                      [.var .local (ofString "dst"), .var .local (ofString "i"), .const 6#64])
                    (.loadByte (.op .add
                      [.var .local (ofString "src"), .var .local (ofString "i"), .const 6#64])))
                  (.seq
                    (.storeByte (.op .add
                        [.var .local (ofString "dst"), .var .local (ofString "i"), .const 7#64])
                      (.loadByte (.op .add
                        [.var .local (ofString "src"), .var .local (ofString "i"), .const 7#64])))
                    (.assign .local (ofString "i")
                      (.op .add [.var .local (ofString "i"), .const 8#64])))))))))
  let b1 : ProgHOL 64 :=
    .seq
      (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
        (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64]))
  have hb32 : CountedBody (ofString "i") 32#64 b32 0 :=
    countedBody_seq_straight _ rfl rfl rfl
      (countedBody_seq_straight _ rfl rfl rfl
        (countedBody_seq_straight _ rfl rfl rfl
          (countedBody_seq_straight _ rfl rfl rfl CountedBody.incr)))
  have hb8a : CountedBody (ofString "i") 8#64 b8a 0 :=
    countedBody_seq_straight _ rfl rfl rfl CountedBody.incr
  have hb8b : CountedBody (ofString "i") 8#64 b8b 0 :=
    countedBody_seq_straight _ rfl rfl rfl
      (countedBody_seq_straight _ rfl rfl rfl
        (countedBody_seq_straight _ rfl rfl rfl
          (countedBody_seq_straight _ rfl rfl rfl
            (countedBody_seq_straight _ rfl rfl rfl
              (countedBody_seq_straight _ rfl rfl rfl
                (countedBody_seq_straight _ rfl rfl rfl
                  (countedBody_seq_straight _ rfl rfl rfl CountedBody.incr)))))))
  have hb1 : CountedBody (ofString "i") 1#64 b1 0 :=
    countedBody_seq_straight _ rfl rfl rfl CountedBody.incr
  let condAlign : ExpHOL 64 :=
    .cmp .equal
      (.op .and
        [.op .or [.var .local (ofString "dst"), .var .local (ofString "src")], .const 7#64])
      (.const 0#64)
  let alignBranch : ProgHOL 64 :=
    .ite condAlign
      (.seq
        (.while (.cmp .notLower (.var .local (ofString "n"))
          (.op .add [.var .local (ofString "i"), .const 32#64])) b32)
        (.while (.cmp .notLower (.var .local (ofString "n"))
          (.op .add [.var .local (ofString "i"), .const 8#64])) b8a))
      .skip
  have halign :
      ∃ c1,
        let r := evaluateHOLFiniteState s0 alignBranch
        s0.clock ≤ r.2.clock + c1 ∧
        r.2.clock ≤ s0.clock ∧ r.1 ≠ some .timeOut ∧
        (r.1 ≠ none → c1 ≤ K.toNat / 8) ∧
        (r.1 = none → ∃ w1,
          r.2.locals.lookup (ofString "i") = some (.val (.word w1)) ∧
          r.2.locals.lookup (ofString "n") = some (.val (.word K)) ∧
          w1.toNat ≤ K.toNat ∧
          c1 + (K.toNat - w1.toNat) / 8 ≤ K.toNat / 8 ∧
          r.2.code = s0.code) := by
    dsimp only [alignBranch]
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · rw [evaluateHOLFiniteState_skip]
        exact ⟨0, by dsimp; omega, le_refl _, by simp, fun h => absurd rfl h,
          fun _ => ⟨0#64, hs0_i, hs0_n, by simp, by simp, rfl⟩⟩
      · rw [evaluateHOLFiniteState_seq_line780]
        have h32 := notLowerStrideWhile_run (ofString "i") (ofString "n") K 32#64
          hsmall (by decide) hb32 rfl rfl (K.toNat / 32) s0 hs0_code 0#64 hs0_i hs0_n
          (by simp) (by simp)
          (by simp only [Nat.zero_add, Nat.mul_one]; rw [hs0_clk]; omega)
        rcases hr32 : evaluateHOLFiniteState s0
            (.while (.cmp .notLower (.var .local (ofString "n"))
              (.op .add [.var .local (ofString "i"), .const 32#64])) b32) with ⟨res32, s1⟩
        rw [hr32] at h32
        dsimp only at h32 ⊢
        cases res32 with
        | some r =>
          dsimp only
          exact ⟨K.toNat / 32, by simp only [Nat.zero_add, Nat.mul_one] at h32; omega,
            h32.2.1, h32.2.2.1, fun _ => by omega, fun h => by cases h⟩
        | none =>
          dsimp only
          obtain ⟨w0, hs1_i, hs1_n, _, hw0_le, hw0_rem, hs1_code⟩ := h32.2.2.2 rfl
          change K.toNat < w0.toNat + 32 at hw0_rem
          have h8a := notLowerStrideWhile_run (ofString "i") (ofString "n") K 8#64
            (by change K.toNat + 8 < 2 ^ 64; omega) (by decide) hb8a rfl rfl
            ((K.toNat - w0.toNat) / 8)
            s1 (hs1_code.trans hs0_code) w0 hs1_i hs1_n hw0_le rfl
            (by simp only [Nat.zero_add, Nat.mul_one] at h32 ⊢; rw [hs0_clk] at h32; omega)
          rcases hr8a : evaluateHOLFiniteState s1
              (.while (.cmp .notLower (.var .local (ofString "n"))
                (.op .add [.var .local (ofString "i"), .const 8#64])) b8a) with ⟨res8a, s2⟩
          rw [hr8a] at h8a
          dsimp only at h8a ⊢
          refine ⟨K.toNat / 32 + (K.toNat - w0.toNat) / 8,
            by simp only [Nat.zero_add, Nat.mul_one] at h32 h8a; omega,
            by omega, h8a.2.2.1, fun _ => by omega, fun hn => ?_⟩
          obtain ⟨w1, hs2_i, hs2_n, _, hw1_le, hw1_rem, hs2_code⟩ := h8a.2.2.2 hn
          change K.toNat < w1.toNat + 8 at hw1_rem
          exact ⟨w1, hs2_i, hs2_n, hw1_le, by omega, hs2_code.trans hs1_code⟩
    · exact ⟨0, by simp, by simp, by simp, fun _ => by omega, fun h => by simp at h⟩
  obtain ⟨c1, hc1_spent, hc1_kept, hc1_safe, hc1_abrupt, hc1_norm⟩ := halign
  change RunBounded s0 (.seq alignBranch
    (.seq (.while (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const 8#64])) b8b)
      (.seq (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) b1)
        (.return (.const 0#64))))) (K.toNat / 8 + 7)
  unfold RunBounded
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hral : evaluateHOLFiniteState s0 alignBranch with ⟨resAl, sa⟩
  rw [hral] at hc1_spent hc1_kept hc1_safe hc1_abrupt hc1_norm
  dsimp only at hc1_spent hc1_kept hc1_safe hc1_abrupt hc1_norm ⊢
  cases resAl with
  | some r =>
    dsimp only
    have hbnd1 := hc1_abrupt (by simp)
    exact ⟨by omega, hc1_kept, hc1_safe⟩
  | none =>
    dsimp only
    obtain ⟨w1, hsa_i, hsa_n, hw1_le, hc1_rem, hsa_code⟩ := hc1_norm rfl
    rw [evaluateHOLFiniteState_seq_line780]
    have h8b := notLowerStrideWhile_run (ofString "i") (ofString "n") K 8#64
      (by change K.toNat + 8 < 2 ^ 64; omega) (by decide) hb8b rfl rfl
      ((K.toNat - w1.toNat) / 8)
      sa (hsa_code.trans hs0_code) w1 hsa_i hsa_n hw1_le rfl
      (by simp only [Nat.zero_add, Nat.mul_one]; rw [hs0_clk] at hc1_spent; omega)
    rcases hr8b : evaluateHOLFiniteState sa
        (.while (.cmp .notLower (.var .local (ofString "n"))
          (.op .add [.var .local (ofString "i"), .const 8#64])) b8b) with ⟨res8b, sb⟩
    rw [hr8b] at h8b
    dsimp only at h8b ⊢
    cases res8b with
    | some r =>
      dsimp only
      exact ⟨by simp only [Nat.zero_add, Nat.mul_one] at h8b; omega, by omega, h8b.2.2.1⟩
    | none =>
      dsimp only
      obtain ⟨w2, hsb_i, hsb_n, _, hw2_le, hw2_rem, hsb_code⟩ := h8b.2.2.2 rfl
      rw [evaluateHOLFiniteState_seq_line780]
      change K.toNat < w2.toNat + 8 at hw2_rem
      have h1 := variableCountedWhile_run (ofString "i") (ofString "n") .lower (Or.inr rfl) K
        (fun h => by cases h) hb1 rfl (K.toNat - w2.toNat)
        sb (hsb_code.trans (hsa_code.trans hs0_code)) w2 hsb_i hsb_n hw2_le rfl
        (by
          simp only [Nat.zero_add, Nat.mul_one] at h8b ⊢
          rw [hs0_clk] at hc1_spent
          omega)
      have h1_meta := PanRunBounded.evaluateHOLFiniteState_metadata sb
        (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) b1)
      rcases hr1 : evaluateHOLFiniteState sb
          (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) b1) with
        ⟨res1, sc⟩
      rw [hr1] at h1 h1_meta
      dsimp only at h1 h1_meta ⊢
      cases res1 with
      | some r =>
        dsimp only
        exact ⟨by simp only [Nat.zero_add, Nat.mul_one] at h8b h1; omega, by omega, h1.2.2⟩
      | none =>
        dsimp only
        have ht := (ProgBounded.straight (.return (.const 0#64)) rfl)
          sc (h1_meta.1.trans (hsb_code.trans (hsa_code.trans hs0_code))) (by omega)
        exact ⟨by simp only [Nat.zero_add, Nat.mul_one] at h8b h1 ht; omega, by omega, ht.2.2⟩

theorem runBounded_memcpy_call {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS))
    (dst src sizeExp : ExpHOL 64) (M : Nat) (hM : M + 32 < 2 ^ 64)
    (hcode : state.code = originalRuntimeCode)
    (hbudget : M / 8 + 8 ≤ state.clock)
    (hbnd : ∀ (K : BitVec 64),
      evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) sizeExp =
        some (.val (.word K)) → K.toNat ≤ M) :
    RunBounded state (.call (some (destination, none)) (ofString "memcpy") [dst, src, sizeExp])
      (M / 8 + 8) := by
  cases hargs : evalListHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a)) [dst, src, sizeExp] with
  | none =>
    unfold RunBounded
    rw [evaluateHOLFiniteState_call, hargs]
    simp
  | some vs =>
    have hlast : ∃ v1 v2,
        (∃ K, vs = [v1, v2, .val (.word K)] ∧
          evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) sizeExp =
            some (.val (.word K))) ∨
        lookupCodeHOLFinite state.code.lookup (ofString "memcpy") vs = none := by
      rw [evalListHOLFinite_eq_toExact] at hargs
      simp only [evalListHOLExact] at hargs
      rcases h1 : @evalHOLExact 64 F _ state.toExact
          (fun a => Classical.propDecidable (state.memaddrs a)) dst with _ | v1
      · rw [h1] at hargs; cases hargs
      · rw [h1] at hargs
        rcases h2 : @evalHOLExact 64 F _ state.toExact
            (fun a => Classical.propDecidable (state.memaddrs a)) src with _ | v2
        · rw [h2] at hargs; cases hargs
        · rw [h2] at hargs
          rcases h3 : @evalHOLExact 64 F _ state.toExact
              (fun a => Classical.propDecidable (state.memaddrs a)) sizeExp with _ | v3
          · rw [h3] at hargs; cases hargs
          · rw [h3] at hargs
            cases hargs
            cases v3 with
            | val wv =>
              cases wv with
              | word K =>
                refine ⟨v1, v2, Or.inl ⟨K, rfl, ?_⟩⟩
                rw [evalHOLFinite_eq_toExact]
                exact h3
            | rStruct _ =>
              refine ⟨v1, v2, Or.inr ?_⟩
              rw [hcode]
              unfold PanSemStateFiniteExact.lookupCodeHOLFinite
              split
              · rfl
              · rename_i _ _ _ raw
                simp [lookupCodeHOLExact, lookup_memcpy, shapeOfHOLExact, shapeEqHOL] at raw
            | nStruct _ _ =>
              refine ⟨v1, v2, Or.inr ?_⟩
              rw [hcode]
              unfold PanSemStateFiniteExact.lookupCodeHOLFinite
              split
              · rfl
              · rename_i _ _ _ raw
                simp [lookupCodeHOLExact, lookup_memcpy, shapeOfHOLExact, shapeEqHOL] at raw
    obtain ⟨v1, v2, hvs⟩ := hlast
    rcases hvs with ⟨K, rfl, hk_eval⟩ | hnone
    · have hK_le : K.toNat ≤ M := hbnd K hk_eval
      have hdiv : K.toNat / 8 ≤ M / 8 := Nat.div_le_div_right hK_le
      exact RunBounded.call hargs hbudget (fun body locals rs hfound => by
        rw [hcode] at hfound
        obtain ⟨rfl, hn⟩ := three_arg_lookup_last originalRuntimeCode.lookup
          (ofString "memcpy") (ofString "dst") (ofString "src") (ofString "n")
          (sourceFnBody Guest.Software.guestFn_memcpy)
          (by decide) (by decide) (by decide) lookup_memcpy hfound
        exact (runBounded_memcpy_local_body (callEntryStateHOLFinite state locals)
          K (by omega) hcode hn
          (by change K.toNat / 8 + 7 ≤ state.clock - 1; omega)).weaken (by omega))
    · unfold RunBounded
      rw [evaluateHOLFiniteState_call, hargs]
      dsimp only
      rw [hnone]
      simp

theorem progBounded_memcpy_bounded (destination : Option (VarKind × MlS))
    (dst src sizeExp : ExpHOL 64) (M : Nat) (hM : M + 32 < 2 ^ 64)
    (hbnd : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (K : BitVec 64),
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) sizeExp =
        some (.val (.word K)) → K.toNat ≤ M) :
    ProgBounded (.call (some (destination, none)) (ofString "memcpy") [dst, src, sizeExp])
      (M / 8 + 8) :=
  fun state hcode hbudget =>
    runBounded_memcpy_call state destination dst src sizeExp M hM hcode hbudget (hbnd state)

theorem funBounded_rlp_write_header : FunBounded (ofString "rlp_write_header") (2 ^ 64 + 9) := by
  refine funBounded_of_guestAst 120 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_rlp_write_header (2 ^ 64 + 9) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_rlp_write_header,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (progBounded_seq_straight _ rfl
      (ProgBounded.decCall funBounded_rlp_be_len _ _ _
        (progBounded_seq_straight _ rfl
          (ProgBounded.seq (ProgBounded.call funBounded_rlp_put_be none _)
            (ProgBounded.straight _ rfl)))))
    (by decide)

theorem funBounded_rlp_header_len : FunBounded (ofString "rlp_header_len") 9 := by
  refine funBounded_of_guestAst 121 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_rlp_header_len 9 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_rlp_header_len,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (progBounded_seq_straight _ rfl
      (ProgBounded.decCall funBounded_rlp_be_len _ _ _ (ProgBounded.straight _ rfl)))
    (by decide)

theorem funBounded_rlp_encode_word : FunBounded (ofString "rlp_encode_word") (2 ^ 64 + 9) := by
  refine funBounded_of_guestAst 123 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_rlp_encode_word (2 ^ 64 + 9) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_rlp_encode_word,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (progBounded_seq_straight _ rfl
      (progBounded_seq_straight _ rfl
        (ProgBounded.decCall funBounded_rlp_be_len _ _ _
          (progBounded_seq_straight _ rfl
            (ProgBounded.seq (ProgBounded.call funBounded_rlp_put_be none _)
              (ProgBounded.straight _ rfl))))))
    (by decide)

theorem funBounded_rlp_encode_list_header :
    FunBounded (ofString "rlp_encode_list_header") (2 ^ 64 + 10) := by
  refine funBounded_of_guestAst 124 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_rlp_encode_list_header (2 ^ 64 + 10) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_rlp_encode_list_header,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.tail funBounded_rlp_write_header _

theorem funBounded_rlp_bytes_encoded_len :
    FunBounded (ofString "rlp_bytes_encoded_len") 10 := by
  refine funBounded_of_guestAst 125 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_rlp_bytes_encoded_len 10 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_rlp_bytes_encoded_len,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (progBounded_seq_straight _ rfl
      (ProgBounded.decCall funBounded_rlp_header_len _ _ _ (ProgBounded.straight _ rfl)))
    (by decide)

theorem funBounded_rlp_list_header_len : FunBounded (ofString "rlp_list_header_len") 10 := by
  refine funBounded_of_guestAst 126 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_rlp_list_header_len 10 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_rlp_list_header_len,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.tail funBounded_rlp_header_len _

theorem funBounded_rlp_value_encoded_len :
    FunBounded (ofString "rlp_value_encoded_len") 11 := by
  refine funBounded_of_guestAst 286 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_rlp_value_encoded_len 11 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_rlp_value_encoded_len,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.dec _ _ _
    (progBounded_seq_straight _ rfl (ProgBounded.tail funBounded_rlp_bytes_encoded_len _))

private theorem lookup_rlp_encode_bytes :
    originalRuntimeCode.lookup (ofString "rlp_encode_bytes") =
      some ([(ofString "dst", .one), (ofString "src", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_encode_bytes, .one) :=
  lookup_of_guestAst_getElem 122 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_encode_bytes) rfl

private theorem runBounded_rlp_encode_bytes_body {F : Type}
    (state : PanSemStateFiniteExact 64 F) (K : BitVec 64)
    (hsmall : K.toNat + 32 < 2 ^ 64)
    (hcode : state.code = originalRuntimeCode)
    (atN : state.locals.lookup (ofString "n") = some (.val (.word K)))
    (hbudget : 2 ^ 64 + 18 + K.toNat / 8 ≤ state.clock) :
    RunBounded state (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes)
      (2 ^ 64 + 18 + K.toNat / 8) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_encode_bytes,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  let pFirst : ProgHOL 64 :=
    .ite (.cmp .equal (.var .local (ofString "n")) (.const 1#64))
      (.dec (ofString "b") .one (.loadByte (.var .local (ofString "src")))
        (.ite (.cmp .lower (.var .local (ofString "b")) (.const 128#64))
          (.seq (.storeByte (.var .local (ofString "dst")) (.var .local (ofString "b")))
            (.return (.const 1#64)))
          .skip))
      .skip
  have hpFirst_av : avoidsLocal (ofString "n") pFirst = true := rfl
  refine (RunBounded.seq (ProgBounded.straight pFirst rfl state hcode (by omega))
    (a := 0) (b := 2 ^ 64 + 18 + K.toNat / 8) (by omega) ?_).weaken (by omega)
  intro s1 hr1 hs1_code hs1_budget
  have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word K)) := by
    have hfl := evaluate_avoidsLocal_flowing (ofString "n") pFirst hpFirst_av state
    rw [hr1] at hfl
    exact (hfl (Or.inl rfl)).trans atN
  have hs1_orig : s1.code = originalRuntimeCode := hs1_code.trans hcode
  cases hargs : evalListHOLFinite s1
      (h := fun a => Classical.propDecidable (s1.memaddrs a))
      [.var .local (ofString "dst"), .const 128#64, .var .local (ofString "n")] with
  | none =>
    unfold RunBounded
    rw [evaluateHOLFiniteState_decCall_args_none s1 _ _ _ _ _ hargs]
    simp
  | some vals =>
    refine (RunBounded.decCall hargs (bodyCost := 2 ^ 64 + 9) (tailCost := K.toNat / 8 + 8)
      (by omega) ?_).weaken (by omega)
    intro body locals rs hfound
    refine ⟨?_, ?_⟩
    · have hb := ProgBounded.bodies_of_fun funBounded_rlp_write_header
        s1 hs1_orig (by omega) vals body locals rs hfound
      exact hb
    · intro val post hran hpost_budget
      have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata
        (callEntryStateHOLFinite s1 locals) body
      rw [hran] at hmeta
      let resumed := setVarHOLFinite (ofString "h") val { post with locals := s1.locals }
      have hres_clk : resumed.clock = post.clock := rfl
      have hres_n : resumed.locals.lookup (ofString "n") = some (.val (.word K)) := by
        have hne : ofString "h" ≠ ofString "n" := by decide
        simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hs1_n]
      have hres_code : resumed.code = originalRuntimeCode := hmeta.1.trans hs1_orig
      have hcp := runBounded_memcpy_call resumed none
        (.op .add [.var .local (ofString "dst"), .var .local (ofString "h")])
        (.var .local (ofString "src"))
        (.var .local (ofString "n"))
        K.toNat hsmall hres_code (by rw [hres_clk]; exact hpost_budget) (by
          intro K' hk'
          rw [evalHOLFinite_eq_toExact] at hk'
          simp only [evalHOLExact] at hk'
          change resumed.locals.lookup (ofString "n") = some (.val (.word K')) at hk'
          rw [hres_n] at hk'
          cases hk'
          exact le_refl _)
      exact (RunBounded.seq hcp (a := K.toNat / 8 + 8) (b := 0)
        (by rw [hres_clk]; omega)
        (fun next _ nextCode nextBudget =>
          (ProgBounded.straight _ rfl) next (nextCode.trans hres_code) nextBudget)).weaken
        (by omega)

theorem runBounded_rlp_encode_bytes_call {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS))
    (dst src sizeExp : ExpHOL 64) (M : Nat) (hM : M + 32 < 2 ^ 64)
    (hcode : state.code = originalRuntimeCode)
    (hbudget : 2 ^ 64 + 19 + M / 8 ≤ state.clock)
    (hbnd : ∀ (K : BitVec 64),
      evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) sizeExp =
        some (.val (.word K)) → K.toNat ≤ M) :
    RunBounded state
      (.call (some (destination, none)) (ofString "rlp_encode_bytes") [dst, src, sizeExp])
      (2 ^ 64 + 19 + M / 8) := by
  cases hargs : evalListHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a)) [dst, src, sizeExp] with
  | none =>
    unfold RunBounded
    rw [evaluateHOLFiniteState_call, hargs]
    simp
  | some vs =>
    have hlast : ∃ v1 v2,
        (∃ K, vs = [v1, v2, .val (.word K)] ∧
          evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) sizeExp =
            some (.val (.word K))) ∨
        lookupCodeHOLFinite state.code.lookup (ofString "rlp_encode_bytes") vs = none := by
      rw [evalListHOLFinite_eq_toExact] at hargs
      simp only [evalListHOLExact] at hargs
      rcases h1 : @evalHOLExact 64 F _ state.toExact
          (fun a => Classical.propDecidable (state.memaddrs a)) dst with _ | v1
      · rw [h1] at hargs; cases hargs
      · rw [h1] at hargs
        rcases h2 : @evalHOLExact 64 F _ state.toExact
            (fun a => Classical.propDecidable (state.memaddrs a)) src with _ | v2
        · rw [h2] at hargs; cases hargs
        · rw [h2] at hargs
          rcases h3 : @evalHOLExact 64 F _ state.toExact
              (fun a => Classical.propDecidable (state.memaddrs a)) sizeExp with _ | v3
          · rw [h3] at hargs; cases hargs
          · rw [h3] at hargs
            cases hargs
            cases v3 with
            | val wv =>
              cases wv with
              | word K =>
                refine ⟨v1, v2, Or.inl ⟨K, rfl, ?_⟩⟩
                rw [evalHOLFinite_eq_toExact]
                exact h3
            | rStruct _ =>
              refine ⟨v1, v2, Or.inr ?_⟩
              rw [hcode]
              unfold PanSemStateFiniteExact.lookupCodeHOLFinite
              split
              · rfl
              · rename_i _ _ _ raw
                simp [lookupCodeHOLExact, lookup_rlp_encode_bytes, shapeOfHOLExact, shapeEqHOL]
                  at raw
            | nStruct _ _ =>
              refine ⟨v1, v2, Or.inr ?_⟩
              rw [hcode]
              unfold PanSemStateFiniteExact.lookupCodeHOLFinite
              split
              · rfl
              · rename_i _ _ _ raw
                simp [lookupCodeHOLExact, lookup_rlp_encode_bytes, shapeOfHOLExact, shapeEqHOL]
                  at raw
    obtain ⟨v1, v2, hvs⟩ := hlast
    rcases hvs with ⟨K, rfl, hk_eval⟩ | hnone
    · have hK_le : K.toNat ≤ M := hbnd K hk_eval
      have hdiv : K.toNat / 8 ≤ M / 8 := Nat.div_le_div_right hK_le
      exact (RunBounded.call hargs (bodyCost := 2 ^ 64 + 18 + M / 8) (by omega)
        (fun body locals rs hfound => by
          rw [hcode] at hfound
          obtain ⟨rfl, hn⟩ := three_arg_lookup_last originalRuntimeCode.lookup
            (ofString "rlp_encode_bytes") (ofString "dst") (ofString "src") (ofString "n")
            (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes)
            (by decide) (by decide) (by decide) lookup_rlp_encode_bytes hfound
          exact (runBounded_rlp_encode_bytes_body (callEntryStateHOLFinite state locals)
            K (by omega) hcode hn
            (by change 2 ^ 64 + 18 + K.toNat / 8 ≤ state.clock - 1; omega)).weaken
            (by omega))).weaken (by omega)
    · unfold RunBounded
      rw [evaluateHOLFiniteState_call, hargs]
      dsimp only
      rw [hnone]
      simp

theorem progBounded_rlp_encode_bytes_bounded (destination : Option (VarKind × MlS))
    (dst src sizeExp : ExpHOL 64) (M : Nat) (hM : M + 32 < 2 ^ 64)
    (hbnd : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (K : BitVec 64),
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) sizeExp =
        some (.val (.word K)) → K.toNat ≤ M) :
    ProgBounded (.call (some (destination, none)) (ofString "rlp_encode_bytes") [dst, src, sizeExp])
      (2 ^ 64 + 19 + M / 8) :=
  fun state hcode hbudget =>
    runBounded_rlp_encode_bytes_call state destination dst src sizeExp M hM
      hcode hbudget (hbnd state)

theorem progBounded_rlp_encode_bytes_const (destination : Option (VarKind × MlS))
    (dst src : ExpHOL 64) (K : BitVec 64) (hsmall : K.toNat + 32 < 2 ^ 64) :
    ProgBounded (.call (some (destination, none)) (ofString "rlp_encode_bytes")
      [dst, src, .const K]) (2 ^ 64 + 19 + K.toNat / 8) :=
  progBounded_rlp_encode_bytes_bounded destination dst src (.const K) K.toNat hsmall
    (fun s K' hk => by
      rw [evalHOLFinite_eq_toExact] at hk
      simp [evalHOLExact] at hk
      cases hk
      exact le_refl _)

theorem runBounded_rlp_encode_bytes_decCall {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (shape : ShapeHOL)
    (dst src sizeExp : ExpHOL 64) {cont : ProgHOL 64} {tailCost : Nat}
    (M : Nat) (hM : M + 32 < 2 ^ 64)
    (hcode : state.code = originalRuntimeCode)
    (hbudget : 2 ^ 64 + 19 + M / 8 + tailCost ≤ state.clock)
    (hbnd : ∀ (K : BitVec 64),
      evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) sizeExp =
        some (.val (.word K)) → K.toNat ≤ M)
    (hcont : ∀ (val : ValueHOL 64) (post : PanSemStateFiniteExact 64 F),
      post.code = originalRuntimeCode → tailCost ≤ post.clock →
      RunBounded (setVarHOLFinite name val { post with locals := state.locals }) cont tailCost) :
    RunBounded state
      (.decCall name shape (ofString "rlp_encode_bytes") [dst, src, sizeExp] cont)
      (2 ^ 64 + 19 + M / 8 + tailCost) := by
  cases hargs : evalListHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a)) [dst, src, sizeExp] with
  | none =>
    unfold RunBounded
    rw [evaluateHOLFiniteState_decCall_args_none state _ _ _ _ _ hargs]
    simp
  | some vs =>
    have hlast : ∃ v1 v2,
        (∃ K, vs = [v1, v2, .val (.word K)] ∧
          evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) sizeExp =
            some (.val (.word K))) ∨
        lookupCodeHOLFinite state.code.lookup (ofString "rlp_encode_bytes") vs = none := by
      rw [evalListHOLFinite_eq_toExact] at hargs
      simp only [evalListHOLExact] at hargs
      rcases h1 : @evalHOLExact 64 F _ state.toExact
          (fun a => Classical.propDecidable (state.memaddrs a)) dst with _ | v1
      · rw [h1] at hargs; cases hargs
      · rw [h1] at hargs
        rcases h2 : @evalHOLExact 64 F _ state.toExact
            (fun a => Classical.propDecidable (state.memaddrs a)) src with _ | v2
        · rw [h2] at hargs; cases hargs
        · rw [h2] at hargs
          rcases h3 : @evalHOLExact 64 F _ state.toExact
              (fun a => Classical.propDecidable (state.memaddrs a)) sizeExp with _ | v3
          · rw [h3] at hargs; cases hargs
          · rw [h3] at hargs
            cases hargs
            cases v3 with
            | val wv =>
              cases wv with
              | word K =>
                refine ⟨v1, v2, Or.inl ⟨K, rfl, ?_⟩⟩
                rw [evalHOLFinite_eq_toExact]
                exact h3
            | rStruct _ =>
              refine ⟨v1, v2, Or.inr ?_⟩
              rw [hcode]
              unfold PanSemStateFiniteExact.lookupCodeHOLFinite
              split
              · rfl
              · rename_i _ _ _ raw
                simp [lookupCodeHOLExact, lookup_rlp_encode_bytes, shapeOfHOLExact, shapeEqHOL]
                  at raw
            | nStruct _ _ =>
              refine ⟨v1, v2, Or.inr ?_⟩
              rw [hcode]
              unfold PanSemStateFiniteExact.lookupCodeHOLFinite
              split
              · rfl
              · rename_i _ _ _ raw
                simp [lookupCodeHOLExact, lookup_rlp_encode_bytes, shapeOfHOLExact, shapeEqHOL]
                  at raw
    obtain ⟨v1, v2, hvs⟩ := hlast
    rcases hvs with ⟨K, rfl, hk_eval⟩ | hnone
    · have hK_le : K.toNat ≤ M := hbnd K hk_eval
      have hdiv : K.toNat / 8 ≤ M / 8 := Nat.div_le_div_right hK_le
      exact (RunBounded.decCall hargs (bodyCost := 2 ^ 64 + 18 + M / 8) (tailCost := tailCost)
        (by omega) (fun body locals rs hfound => by
          rw [hcode] at hfound
          obtain ⟨rfl, hn⟩ := three_arg_lookup_last originalRuntimeCode.lookup
            (ofString "rlp_encode_bytes") (ofString "dst") (ofString "src") (ofString "n")
            (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes)
            (by decide) (by decide) (by decide) lookup_rlp_encode_bytes hfound
          refine ⟨(runBounded_rlp_encode_bytes_body (callEntryStateHOLFinite state locals)
            K (by omega) hcode hn
            (by change 2 ^ 64 + 18 + K.toNat / 8 ≤ state.clock - 1; omega)).weaken (by omega), ?_⟩
          intro val post hran hpost_budget
          have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata
            (callEntryStateHOLFinite state locals)
            (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes)
          rw [hran] at hmeta
          exact hcont val post (hmeta.1.trans hcode) hpost_budget)).weaken (by omega)
    · unfold RunBounded
      rw [evaluateHOLFiniteState_decCall_lookup_none state _ _ _ _ _ vs hargs hnone]
      simp

theorem progBounded_rlp_encode_bytes_decCall_bounded (name : MlS) (shape : ShapeHOL)
    (dst src sizeExp : ExpHOL 64) {cont : ProgHOL 64} {tailCost : Nat}
    (M : Nat) (hM : M + 32 < 2 ^ 64)
    (hbnd : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (K : BitVec 64),
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) sizeExp =
        some (.val (.word K)) → K.toNat ≤ M)
    (hcont : ProgBounded cont tailCost) :
    ProgBounded (.decCall name shape (ofString "rlp_encode_bytes") [dst, src, sizeExp] cont)
      (2 ^ 64 + 19 + M / 8 + tailCost) :=
  fun state hcode hbudget =>
    runBounded_rlp_encode_bytes_decCall state name shape dst src sizeExp M hM
      hcode hbudget (hbnd state) (fun _ _ hp hc => hcont _ hp hc)

theorem progBounded_rlp_encode_bytes_decCall_const (name : MlS) (shape : ShapeHOL)
    (dst src : ExpHOL 64) (K : BitVec 64) (hsmall : K.toNat + 32 < 2 ^ 64)
    {cont : ProgHOL 64} {tailCost : Nat} (hcont : ProgBounded cont tailCost) :
    ProgBounded (.decCall name shape (ofString "rlp_encode_bytes") [dst, src, .const K] cont)
      (2 ^ 64 + 19 + K.toNat / 8 + tailCost) :=
  progBounded_rlp_encode_bytes_decCall_bounded name shape dst src (.const K) K.toNat hsmall
    (fun s K' hk => by
      rw [evalHOLFinite_eq_toExact] at hk
      simp [evalHOLExact] at hk
      cases hk
      exact le_refl _)
    hcont

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

private theorem bit_length64_step {F : Type}
    (s : PanSemStateFiniteExact 64 F) (k : BitVec 64)
    (n x : BitVec 64) (hx : x.toNat < 2 ^ (2 * k.toNat))
    (hk_pos : 0 < k.toNat) (hk_le : k.toNat ≤ 32)
    (hn_le : n.toNat + 2 * k.toNat ≤ 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hx_loc : s.locals.lookup (ofString "x") = some (.val (.word x))) :
    let stepProg : ProgHOL 64 :=
      .ite (.cmp .notEqual (.shift .lsr (.var .local (ofString "x")) (.const k)) (.const 0#64))
        (.seq
          (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const k]))
          (.assign .local (ofString "x") (.shift .lsr (.var .local (ofString "x")) (.const k))))
        .skip
    ∀ s', evaluateHOLFiniteState s stepProg = (none, s') →
      ∃ n' x',
        s'.locals.lookup (ofString "n") = some (.val (.word n')) ∧
        s'.locals.lookup (ofString "x") = some (.val (.word x')) ∧
        x'.toNat < 2 ^ k.toNat ∧
        n'.toNat + k.toNat ≤ 64 := by
  dsimp only
  intro s' hrun
  rw [evaluateHOLFiniteState_ite] at hrun
  have hk_not64 : ¬ (¬ k.toNat = 0 ∧ 64 ≤ k.toNat) := by omega
  have hcond : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notEqual (.shift .lsr (.var .local (ofString "x")) (.const k)) (.const 0#64)) =
      some (.val (.word (if x >>> k.toNat = 0#64 then 0#64 else 1#64))) := by
    simp [evalHOLExact, hx_loc, Compiler.Encoders.Asm.wordCmpHOL, wordShiftHOL, hk_not64]
  rw [hcond] at hrun
  dsimp only at hrun
  by_cases hz : x >>> k.toNat = 0#64
  · rw [if_pos hz] at hrun
    have h0 : (0#64 : BitVec 64) = 0 := rfl
    rw [if_pos h0, evaluateHOLFiniteState_skip] at hrun
    cases hrun
    refine ⟨n, x, hn, hx_loc, ?_, by omega⟩
    have hzt := congrArg BitVec.toNat hz
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at hzt
    simp only [BitVec.toNat_ofNat, Nat.zero_mod] at hzt
    have hpos : 0 < 2 ^ k.toNat := Nat.two_pow_pos k.toNat
    exact (Nat.div_eq_zero_iff_lt hpos).mp hzt
  · rw [if_neg hz] at hrun
    have hnot0 : ¬ ((1#64 : BitVec 64) = 0) := by decide
    rw [if_neg hnot0] at hrun
    rw [evaluateHOLFiniteState_seq_line780] at hrun
    have hasgn_n : evaluateHOLFiniteState s
        (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const k])) =
        (none, setVarHOLFinite (ofString "n") (.val (.word (n + k))) s) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hn,
        wordOpHOL, wordOp, valueIsWord, valueWord,
        lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite, setVarHOLFinite,
        shapeOfHOLExact, shapeEqHOL]
    rw [hasgn_n] at hrun
    dsimp only at hrun
    let s1 := setVarHOLFinite (ofString "n") (.val (.word (n + k))) s
    have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word (n + k))) := by
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hs1_x : s1.locals.lookup (ofString "x") = some (.val (.word x)) := by
      have hne : ofString "n" ≠ ofString "x" := by decide
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hx_loc]
    have hasgn_x : evaluateHOLFiniteState s1
        (.assign .local (ofString "x") (.shift .lsr (.var .local (ofString "x")) (.const k))) =
        (none, setVarHOLFinite (ofString "x") (.val (.word (x >>> k.toNat))) s1) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, hs1_x, wordShiftHOL, hk_not64,
        lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite, setVarHOLFinite,
        shapeOfHOLExact, shapeEqHOL]
    rw [hasgn_x] at hrun
    cases hrun
    refine ⟨n + k, x >>> k.toNat, ?_, ?_, ?_, ?_⟩
    · have hne : ofString "x" ≠ ofString "n" := by decide
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hs1_n]
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      have hpow : 2 ^ (2 * k.toNat) = 2 ^ k.toNat * 2 ^ k.toNat := by
        rw [Nat.two_mul, Nat.pow_add]
      rw [hpow] at hx
      exact Nat.div_lt_of_lt_mul hx
    · have hadd : (n + k).toNat = n.toNat + k.toNat := BitVec.toNat_add_of_lt (by omega)
      omega

private theorem evaluate_bit_length64_le {F : Type}
    (state : PanSemStateFiniteExact 64 F) (x : BitVec 64)
    (hx : state.locals.lookup (ofString "x") = some (.val (.word x))) :
    ∀ w, (evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_bit_length64)).1 =
      some (.returned w) →
      ∃ b : BitVec 64, w = .val (.word b) ∧ b.toNat ≤ 64 := by
  intro w hrun
  have hbody : sourceFnBody Guest.Software.guestFn_bit_length64 =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_bit_length64).body := rfl
  rw [hbody] at hrun
  dsimp only [extractFn, Guest.Software.guestFn_bit_length64,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at hrun
  rw [evaluateHOLFiniteState_dec_total] at hrun
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true] at hrun
  let s0 := setVarHOLFinite (ofString "n") (.val (.word 0#64)) state
  have hs0_n : s0.locals.lookup (ofString "n") = some (.val (.word 0#64)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs0_x : s0.locals.lookup (ofString "x") = some (.val (.word x)) := by
    have hne : ofString "n" ≠ ofString "x" := by decide
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hx]
  have hno_ret_step : ∀ (k : BitVec 64) (st : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState st
        (.ite (.cmp .notEqual (.shift .lsr (.var .local (ofString "x")) (.const k)) (.const 0#64))
          (.seq
            (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const k]))
            (.assign .local (ofString "x") (.shift .lsr (.var .local (ofString "x")) (.const k))))
          .skip)).1 ≠ some (.returned w) := by
    intro k st hc
    rw [evaluateHOLFiniteState_ite] at hc
    split at hc
    · split at hc
      · rw [evaluateHOLFiniteState_skip] at hc; simp at hc
      · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign] at hc
        split at hc
        · simp at hc
        · split at hc
          · dsimp only at hc
            rw [evaluateHOLFiniteState_assign] at hc
            split at hc
            · simp at hc
            · split at hc <;> simp at hc
          · simp at hc
    · simp at hc
  have hstep_seq : ∀ {p1 p2 : ProgHOL 64} {st : PanSemStateFiniteExact 64 F},
      (evaluateHOLFiniteState st (.seq p1 p2)).1 = some (.returned w) →
      (evaluateHOLFiniteState st p1).1 ≠ some (.returned w) →
      ∃ sm, evaluateHOLFiniteState st p1 = (none, sm) ∧
        (evaluateHOLFiniteState sm p2).1 = some (.returned w) := by
    intro p1 p2 st hs hnr
    rw [evaluateHOLFiniteState_seq_line780] at hs
    rcases hr1 : evaluateHOLFiniteState st p1 with ⟨r1, sm⟩
    rw [hr1] at hs hnr
    cases r1 with
    | none => exact ⟨sm, rfl, hs⟩
    | some rv =>
      dsimp only at hs hnr
      exact False.elim (hnr hs)
  obtain ⟨s1, hr1, hrun⟩ := hstep_seq hrun (hno_ret_step 32#64 s0)
  obtain ⟨n1, x1, hn1, hx1, hxb1, hnb1⟩ := bit_length64_step s0 32#64 0#64 x
    (by change x.toNat < 2 ^ 64; exact x.isLt) (by decide) (by decide) (by decide) hs0_n hs0_x s1 hr1
  obtain ⟨s2, hr2, hrun⟩ := hstep_seq hrun (hno_ret_step 16#64 s1)
  obtain ⟨n2, x2, hn2, hx2, hxb2, hnb2⟩ := bit_length64_step s1 16#64 n1 x1
    hxb1 (by decide) (by decide) (by change n1.toNat + 32 ≤ 64; exact hnb1) hn1 hx1 s2 hr2
  obtain ⟨s3, hr3, hrun⟩ := hstep_seq hrun (hno_ret_step 8#64 s2)
  obtain ⟨n3, x3, hn3, hx3, hxb3, hnb3⟩ := bit_length64_step s2 8#64 n2 x2
    hxb2 (by decide) (by decide) (by change n2.toNat + 16 ≤ 64; exact hnb2) hn2 hx2 s3 hr3
  obtain ⟨s4, hr4, hrun⟩ := hstep_seq hrun (hno_ret_step 4#64 s3)
  obtain ⟨n4, x4, hn4, hx4, hxb4, hnb4⟩ := bit_length64_step s3 4#64 n3 x3
    hxb3 (by decide) (by decide) (by change n3.toNat + 8 ≤ 64; exact hnb3) hn3 hx3 s4 hr4
  obtain ⟨s5, hr5, hrun⟩ := hstep_seq hrun (hno_ret_step 2#64 s4)
  obtain ⟨n5, x5, hn5, hx5, hxb5, hnb5⟩ := bit_length64_step s4 2#64 n4 x4
    hxb4 (by decide) (by decide) (by change n4.toNat + 4 ≤ 64; exact hnb4) hn4 hx4 s5 hr5
  obtain ⟨s6, hr6, hrun⟩ := hstep_seq hrun (hno_ret_step 1#64 s5)
  obtain ⟨n6, x6, hn6, hx6, hxb6, hnb6⟩ := bit_length64_step s5 1#64 n5 x5
    hxb5 (by decide) (by decide) (by change n5.toNat + 2 ≤ 64; exact hnb5) hn5 hx5 s6 hr6
  rw [evaluateHOLFiniteState_return] at hrun
  have hev_ret : @evalHOLExact 64 F _ s6.toExact
      (fun a => Classical.propDecidable (s6.memaddrs a))
      (.op .add [.var .local (ofString "n"), .var .local (ofString "x")]) =
      some (.val (.word (n6 + x6))) := by
    simp [evalHOLExact, evalListHOLExact, hn6, hx6, wordOpHOL, wordOp, valueIsWord, valueWord]
  rw [hev_ret] at hrun
  dsimp only at hrun
  split at hrun
  · simp only [Option.some.injEq, PanSemResultExact.returned.injEq] at hrun
    subst hrun
    refine ⟨n6 + x6, rfl, ?_⟩
    change x6.toNat < 2 ^ 1 at hxb6
    change n6.toNat + 1 ≤ 64 at hnb6
    have hadd : (n6 + x6).toNat = n6.toNat + x6.toNat := BitVec.toNat_add_of_lt (by omega)
    omega
  · simp at hrun

private theorem lookupCode_one_word {code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)}
    {fn p1 : MlS} {body foundBody : ProgHOL 64} {rs foundRs : ShapeHOL}
    {v1 : ValueHOL 64} {locals : HolFiniteMapExact MlS (ValueHOL 64)}
    (hlookup : code fn = some ([(p1, .one)], body, rs))
    (hfound : PanSemStateFiniteExact.lookupCodeHOLFinite code fn [v1] =
      some (foundBody, locals, foundRs)) :
    foundBody = body ∧ ∃ w1 : BitVec 64, locals.lookup p1 = some (.val (.word w1)) := by
  have hb := lookupCodeHOLFinite_installed_body code fn _ body foundBody rs foundRs
    [v1] locals hlookup hfound
  refine ⟨hb, ?_⟩
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
  split at hfound
  · cases hfound
  · rename_i exactBody exactLocals exactShape raw
    cases v1 with
    | val wl =>
      cases wl with
      | word w1 =>
        have hraw : lookupCodeHOLExact code fn [ValueHOL.val (HolWordLab.word w1)] =
            some (body,
              (fun current => if current = p1 then some (ValueHOL.val (HolWordLab.word w1)) else none),
              rs) := by
          simp [lookupCodeHOLExact, hlookup, shapeOfHOLExact, shapeEqHOL]
        rw [hraw] at raw
        cases raw
        cases hfound
        exact ⟨w1, by simp⟩
    | rStruct _ =>
      simp [lookupCodeHOLExact, hlookup, shapeOfHOLExact, shapeEqHOL] at raw
    | nStruct _ _ =>
      simp [lookupCodeHOLExact, hlookup, shapeOfHOLExact, shapeEqHOL] at raw

private theorem call_bit_length64_returned_le {F : Type}
    (st post : PanSemStateFiniteExact 64 F) (arg : ExpHOL 64) (w : ValueHOL 64)
    (hcode : st.code = originalRuntimeCode) :
    (∀ vs body callee rs,
      evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a)) [arg] = some vs →
      PanSemStateFiniteExact.lookupCodeHOLFinite st.code.lookup (ofString "bit_length64") vs =
        some (body, callee, rs) →
      evaluateHOLFiniteState (callEntryStateHOLFinite st callee) body = (some (.returned w), post) →
      ∃ b : BitVec 64, w = .val (.word b) ∧ b.toNat ≤ 64) := by
  intro vs body callee rs hargs hfound hran
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact] at hargs
  rcases ha : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) arg with _ | v1
  · rw [ha] at hargs; cases hargs
  · rw [ha] at hargs; cases hargs
    rw [hcode] at hfound
    obtain ⟨rfl, w1, hw1⟩ := lookupCode_one_word lookup_bit_length64 hfound
    exact evaluate_bit_length64_le (callEntryStateHOLFinite st callee) w1 hw1 w
      (by rw [hran])

private theorem decCall_bit_length64_add_le {F : Type}
    (st s' : PanSemStateFiniteExact 64 F) (nm : MlS) (arg : ExpHOL 64)
    (off : BitVec 64) (hoff : off.toNat ≤ 192) (w : ValueHOL 64)
    (hcode : st.code = originalRuntimeCode)
    (hrun : evaluateHOLFiniteState st
      (.decCall nm .one (ofString "bit_length64") [arg]
        (.return (.op .add [.const off, .var .local nm]))) =
      (some (.returned w), s')) :
    ∃ b : BitVec 64, w = .val (.word b) ∧ b.toNat ≤ 256 := by
  rw [evaluateHOLFiniteState_decCall_total] at hrun
  rcases hargs : evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a)) [arg] with _ | vs
  · rw [hargs] at hrun; cases hrun
  · rw [hargs] at hrun
    dsimp only at hrun
    rcases hfound : PanSemStateFiniteExact.lookupCodeHOLFinite st.code.lookup (ofString "bit_length64") vs
      with _ | ⟨body, callee, rs⟩
    · rw [hfound] at hrun; cases hrun
    · rw [hfound] at hrun
      dsimp only at hrun
      split at hrun
      · cases hrun
      · have hle_clk := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite st callee) body
        rcases hran : evaluateHOLFiniteState (callEntryStateHOLFinite st callee) body with ⟨res, post⟩
        rw [hran] at hrun hle_clk
        have hfix : fixClockHOLFinite (callEntryStateHOLFinite st callee) (res, post) = (res, post) := by
          simp [fixClockHOLFinite, Nat.not_lt.mpr hle_clk]
        rw [hfix] at hrun
        dsimp only at hrun
        cases res with
        | none => cases hrun
        | some r =>
          cases r with
          | returned val =>
            obtain ⟨b0, rfl, hb0⟩ := call_bit_length64_returned_le st post arg val hcode vs body callee rs
              hargs hfound hran
            dsimp only at hrun
            split at hrun
            · let resumed := setVarHOLFinite nm (.val (.word b0)) { post with locals := st.locals }
              have hnm : resumed.locals.lookup nm = some (.val (.word b0)) := by
                simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              have hev : @evalHOLExact 64 F _ resumed.toExact
                  (fun a => Classical.propDecidable (resumed.memaddrs a))
                  (.op .add [.const off, .var .local nm]) =
                  some (.val (.word (off + b0))) := by
                simp [evalHOLExact, evalListHOLExact, hnm, wordOpHOL, wordOp, valueIsWord, valueWord]
              have hret_fst : (evaluateHOLFiniteState resumed
                  (.return (.op .add [.const off, .var .local nm]))).1 = some (.returned w) := by
                rcases hc : evaluateHOLFiniteState resumed
                    (.return (.op .add [.const off, .var .local nm])) with ⟨rc, sc⟩
                rw [hc] at hrun
                exact congrArg Prod.fst hrun
              rw [evaluateHOLFiniteState_return, hev] at hret_fst
              dsimp only at hret_fst
              split at hret_fst
              · simp only [Option.some.injEq, PanSemResultExact.returned.injEq] at hret_fst
                subst hret_fst
                refine ⟨off + b0, rfl, ?_⟩
                have hadd : (off + b0).toNat = off.toNat + b0.toNat :=
                  BitVec.toNat_add_of_lt (by omega)
                omega
              · simp at hret_fst
            · cases hrun
          | _ => cases hrun

private theorem evaluate_u256_bit_length_le {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (hcode : state.code = originalRuntimeCode) :
    ∀ w s', evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_u256_bit_length) =
      (some (.returned w), s') →
      ∃ b : BitVec 64, w = .val (.word b) ∧ b.toNat ≤ 256 := by
  intro w s' hrun
  have hbody : sourceFnBody Guest.Software.guestFn_u256_bit_length =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_u256_bit_length).body := rfl
  rw [hbody] at hrun
  dsimp only [extractFn, Guest.Software.guestFn_u256_bit_length,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at hrun
  have hbranch : ∀ {st : PanSemStateFiniteExact 64 F} {cond : ExpHOL 64}
      {nm : MlS} {arg : ExpHOL 64} {off : BitVec 64} {rest : ProgHOL 64},
      st.code = originalRuntimeCode →
      off.toNat ≤ 192 →
      evaluateHOLFiniteState st
        (.seq (.ite cond (.decCall nm .one (ofString "bit_length64") [arg]
            (.return (.op .add [.const off, .var .local nm]))) .skip) rest) =
        (some (.returned w), s') →
      (∃ b : BitVec 64, w = .val (.word b) ∧ b.toNat ≤ 256) ∨
        (∃ sm, sm.code = originalRuntimeCode ∧
          evaluateHOLFiniteState sm rest = (some (.returned w), s')) := by
    intro st cond nm arg off rest hst hoff hs
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hs
    split at hs
    · split at hs
      · rw [evaluateHOLFiniteState_skip] at hs
        exact Or.inr ⟨st, hst, hs⟩
      · rcases hd : evaluateHOLFiniteState st
          (.decCall nm .one (ofString "bit_length64") [arg]
            (.return (.op .add [.const off, .var .local nm]))) with ⟨r1, sm⟩
        rw [hd] at hs
        cases r1 with
        | none =>
          exfalso
          obtain ⟨_, resumed, inner, _, _, contRun, _⟩ := decCall_flowing (Or.inl rfl) hd
          rw [evaluateHOLFiniteState_return] at contRun
          split at contRun
          · cases contRun
          · split at contRun <;> cases contRun
        | some rv =>
          dsimp only at hs
          cases hs
          exact Or.inl (decCall_bit_length64_add_le st s' nm arg off hoff w hst hd)
    · cases hs
  rcases hbranch hcode (by decide) hrun with h | ⟨s1, hc1, hr1⟩
  · exact h
  · rcases hbranch hc1 (by decide) hr1 with h | ⟨s2, hc2, hr2⟩
    · exact h
    · rcases hbranch hc2 (by decide) hr2 with h | ⟨s3, hc3, hr3⟩
      · exact h
      · rw [evaluateHOLFiniteState_call] at hr3
        rcases hargs : evalListHOLFinite s3 (h := fun a => Classical.propDecidable (s3.memaddrs a))
            [.rfield 0 (.var .local (ofString "a"))] with _ | vs
        · rw [hargs] at hr3; cases hr3
        · rw [hargs] at hr3
          dsimp only at hr3
          rcases hfound : PanSemStateFiniteExact.lookupCodeHOLFinite s3.code.lookup
              (ofString "bit_length64") vs with _ | ⟨body, callee, rs⟩
          · rw [hfound] at hr3; cases hr3
          · rw [hfound] at hr3
            dsimp only at hr3
            split at hr3
            · cases hr3
            · rcases hran : evaluateHOLFiniteState (callEntryStateHOLFinite s3 callee) body with ⟨res, post⟩
              rw [hran] at hr3
              cases res with
              | none => cases hr3
              | some r =>
                cases r with
                | returned val =>
                  dsimp only at hr3
                  split at hr3
                  · cases hr3
                    obtain ⟨b0, rfl, hb0⟩ := call_bit_length64_returned_le s3 post
                      (.rfield 0 (.var .local (ofString "a"))) w hc3 vs body callee rs hargs hfound hran
                    exact ⟨b0, rfl, by omega⟩
                  · cases hr3
                | _ => cases hr3

private theorem evaluate_u256_byte_length_le {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (hcode : state.code = originalRuntimeCode) :
    ∀ w s', evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_u256_byte_length) =
      (some (.returned w), s') →
      ∃ b : BitVec 64, w = .val (.word b) ∧ b.toNat ≤ 32 := by
  intro w s' hrun
  have hbody : sourceFnBody Guest.Software.guestFn_u256_byte_length =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_u256_byte_length).body := rfl
  rw [hbody] at hrun
  dsimp only [extractFn, Guest.Software.guestFn_u256_byte_length,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at hrun
  rw [evaluateHOLFiniteState_decCall_total] at hrun
  rcases hargs : evalListHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "a")] with _ | vs
  · rw [hargs] at hrun; cases hrun
  · rw [hargs] at hrun
    dsimp only at hrun
    rcases hfound : PanSemStateFiniteExact.lookupCodeHOLFinite state.code.lookup
        (ofString "u256_bit_length") vs with _ | ⟨body, callee, rs⟩
    · rw [hfound] at hrun; cases hrun
    · rw [hfound] at hrun
      dsimp only at hrun
      split at hrun
      · cases hrun
      · have hle_clk := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
        rcases hran : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with ⟨res, post⟩
        rw [hran] at hrun hle_clk
        have hfix : fixClockHOLFinite (callEntryStateHOLFinite state callee) (res, post) = (res, post) := by
          simp [fixClockHOLFinite, Nat.not_lt.mpr hle_clk]
        rw [hfix] at hrun
        dsimp only at hrun
        cases res with
        | none => cases hrun
        | some r =>
          cases r with
          | returned val =>
            have hfound' := hfound
            rw [hcode] at hfound'
            have hbd := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup
              (ofString "u256_bit_length") _ _ body .one rs vs callee lookup_u256_bit_length hfound'
            subst hbd
            obtain ⟨b0, rfl, hb0⟩ := evaluate_u256_bit_length_le
              (callEntryStateHOLFinite state callee) hcode val post hran
            dsimp only at hrun
            split at hrun
            · let resumed := setVarHOLFinite (ofString "n") (.val (.word b0))
                { post with locals := state.locals }
              have hnm : resumed.locals.lookup (ofString "n") = some (.val (.word b0)) := by
                simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              have hev : @evalHOLExact 64 F _ resumed.toExact
                  (fun a => Classical.propDecidable (resumed.memaddrs a))
                  (.shift .lsr (.op .add [.var .local (ofString "n"), .const 7#64]) (.const 3#64)) =
                  some (.val (.word ((b0 + 7#64) >>> (3 : Nat)))) := by
                simp [evalHOLExact, evalListHOLExact, hnm, wordOpHOL, wordOp, valueIsWord, valueWord,
                  wordShiftHOL]
              have hret_fst : (evaluateHOLFiniteState resumed
                  (.return (.shift .lsr
                    (.op .add [.var .local (ofString "n"), .const 7#64]) (.const 3#64)))).1 =
                  some (.returned w) := by
                rcases hc : evaluateHOLFiniteState resumed
                    (.return (.shift .lsr
                      (.op .add [.var .local (ofString "n"), .const 7#64]) (.const 3#64))) with ⟨rc, sc⟩
                rw [hc] at hrun
                exact congrArg Prod.fst hrun
              rw [evaluateHOLFiniteState_return, hev] at hret_fst
              dsimp only at hret_fst
              split at hret_fst
              · simp only [Option.some.injEq, PanSemResultExact.returned.injEq] at hret_fst
                subst hret_fst
                refine ⟨(b0 + 7#64) >>> (3 : Nat), rfl, ?_⟩
                rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
                have hadd : (b0 + 7#64).toNat = b0.toNat + 7 :=
                  BitVec.toNat_add_of_lt (by change b0.toNat + 7 < 2 ^ 64; omega)
                omega
              · simp at hret_fst
            · cases hrun
          | _ => cases hrun

private def u256ToBeMinLoopBody : ProgHOL 64 :=
  .dec (ofString "pos") .one
    (.op .sub [.op .sub [.var .local (ofString "len"), .const 1#64], .var .local (ofString "i")])
    (.decCall (ofString "l") .one (ofString "u256_limb")
      [.var .local (ofString "a"), .shift .lsr (.var .local (ofString "pos")) (.const 3#64)]
      (.seq
        (.storeByte (.op .add [.var .local (ofString "out"), .var .local (ofString "i")])
          (.op .and
            [.shift .lsr (.var .local (ofString "l"))
              (.panop .mul [.op .and [.var .local (ofString "pos"), .const 7#64], .const 8#64]),
             .const 255#64]))
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64]))))

private theorem u256_to_be_min_loop_no_ret {F : Type}
    (s : PanSemStateFiniteExact 64 F) (w : ValueHOL 64) :
    (evaluateHOLFiniteState s
      (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "len")))
        u256ToBeMinLoopBody)).1 ≠ some (.returned w) := by
  generalize hk : s.clock = k
  induction k using Nat.strongRecOn generalizing s with
  | ind k ih =>
    intro hret
    rw [evaluateHOLFiniteState_while_total] at hret
    split at hret
    · split at hret
      · split at hret
        · simp at hret
        · rename_i hclk
          dsimp only at hret
          rw [fixClockHOLFinite_evaluateState] at hret
          have hle := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) u256ToBeMinLoopBody
          rcases hb : evaluateHOLFiniteState (decClockHOLFinite s) u256ToBeMinLoopBody with ⟨rb, sm⟩
          rw [hb] at hret hle
          cases rb with
          | none =>
            dsimp only at hret
            have hlt : sm.clock < k := by
              change sm.clock ≤ s.clock - 1 at hle
              omega
            exact ih sm.clock hlt sm rfl hret
          | some r =>
            cases r with
            | «continue» =>
              dsimp only at hret
              have hlt : sm.clock < k := by
                change sm.clock ≤ s.clock - 1 at hle
                omega
              exact ih sm.clock hlt sm rfl hret
            | «break» => simp at hret
            | returned v =>
              let dprog : ProgHOL 64 :=
                .decCall (ofString "l") .one (ofString "u256_limb")
                  [.var .local (ofString "a"), .shift .lsr (.var .local (ofString "pos")) (.const 3#64)]
                  (.seq
                    (.storeByte (.op .add [.var .local (ofString "out"), .var .local (ofString "i")])
                      (.op .and
                        [.shift .lsr (.var .local (ofString "l"))
                          (.panop .mul [.op .and [.var .local (ofString "pos"), .const 7#64], .const 8#64]),
                         .const 255#64]))
                    (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64])))
              dsimp only [u256ToBeMinLoopBody] at hb
              rw [evaluateHOLFiniteState_dec_total] at hb
              dsimp only at hb
              split at hb
              · cases hb
              · split at hb
                · rename_i vpos _ _
                  let spos := setVarHOLFinite (ofString "pos") vpos (decClockHOLFinite s)
                  rcases hd : evaluateHOLFiniteState spos dprog with ⟨rd, sd⟩
                  have hrd : rd = some (.returned v) := by
                    rw [hd] at hb
                    exact (Prod.mk.inj hb).1
                  subst hrd
                  dsimp only [dprog] at hd
                  rw [evaluateHOLFiniteState_decCall_total] at hd
                  rcases ha1 : evalListHOLFinite spos
                      (h := fun a => Classical.propDecidable (spos.memaddrs a))
                      [.var .local (ofString "a"),
                       .shift .lsr (.var .local (ofString "pos")) (.const 3#64)] with _ | vs1
                  · rw [ha1] at hd; cases hd
                  · rw [ha1] at hd
                    dsimp only at hd
                    rcases hf1 : PanSemStateFiniteExact.lookupCodeHOLFinite spos.code.lookup
                        (ofString "u256_limb") vs1 with _ | ⟨body1, callee1, rs1⟩
                    · rw [hf1] at hd; cases hd
                    · rw [hf1] at hd
                      dsimp only at hd
                      split at hd
                      · cases hd
                      · have hle1 := evaluateHOLFiniteState_clock_le
                          (callEntryStateHOLFinite spos callee1) body1
                        rcases hc1 : evaluateHOLFiniteState (callEntryStateHOLFinite spos callee1) body1
                          with ⟨rc1, pc1⟩
                        rw [hc1] at hd hle1
                        have hfx1 : fixClockHOLFinite (callEntryStateHOLFinite spos callee1) (rc1, pc1) =
                            (rc1, pc1) := by
                          simp [fixClockHOLFinite, Nat.not_lt.mpr hle1]
                        rw [hfx1] at hd
                        dsimp only at hd
                        cases rc1 with
                        | none => cases hd
                        | some r1 =>
                          cases r1 with
                          | returned v1 =>
                            dsimp only at hd
                            split at hd
                            · let sl1 := setVarHOLFinite (ofString "l") v1
                                { pc1 with locals := spos.locals }
                              let sbProg : ProgHOL 64 :=
                                .storeByte
                                  (.op .add [.var .local (ofString "out"), .var .local (ofString "i")])
                                  (.op .and
                                    [.shift .lsr (.var .local (ofString "l"))
                                      (.panop .mul
                                        [.op .and [.var .local (ofString "pos"), .const 7#64], .const 8#64]),
                                     .const 255#64])
                              let asgnProg : ProgHOL 64 :=
                                .assign .local (ofString "i")
                                  (.op .add [.var .local (ofString "i"), .const 1#64])
                              rcases hsq : evaluateHOLFiniteState sl1 (.seq sbProg asgnProg)
                                with ⟨rsq, ssq⟩
                              have hsq_unf := hsq
                              dsimp only [sl1, sbProg, asgnProg] at hsq_unf
                              have hseq_fst :
                                  (evaluateHOLFiniteState sl1 (.seq sbProg asgnProg)).1 =
                                  some (.returned v) := by
                                rw [hsq]
                                rw [hsq_unf] at hd
                                exact (Prod.mk.inj hd).1
                              rw [evaluateHOLFiniteState_seq_line780] at hseq_fst
                              rcases hsb : evaluateHOLFiniteState sl1 sbProg with ⟨rsb, ssb⟩
                              rw [hsb] at hseq_fst
                              rcases (evaluate_storeByte_control_frame sl1 _ _).1 with h1 | h1
                              · change (evaluateHOLFiniteState sl1 sbProg).1 = none at h1
                                rw [hsb] at h1
                                dsimp only at h1
                                subst h1
                                dsimp only [asgnProg] at hseq_fst
                                rw [evaluateHOLFiniteState_assign] at hseq_fst
                                split at hseq_fst
                                · simp at hseq_fst
                                · split at hseq_fst <;> simp at hseq_fst
                              · change (evaluateHOLFiniteState sl1 sbProg).1 = some .error at h1
                                rw [hsb] at h1
                                dsimp only at h1
                                subst h1
                                simp at hseq_fst
                            · cases hd
                          | _ => cases hd
                · cases hb
            | _ => simp at hret
      · simp at hret
    · simp at hret

private theorem evaluate_u256_to_be_min_le {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (hcode : state.code = originalRuntimeCode) :
    ∀ w s', evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_u256_to_be_min) =
      (some (.returned w), s') →
      ∃ b : BitVec 64, w = .val (.word b) ∧ b.toNat ≤ 32 := by
  intro w s' hrun
  have hbody : sourceFnBody Guest.Software.guestFn_u256_to_be_min =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_u256_to_be_min).body := rfl
  rw [hbody] at hrun
  dsimp only [extractFn, Guest.Software.guestFn_u256_to_be_min,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at hrun
  rw [evaluateHOLFiniteState_decCall_total] at hrun
  rcases hargs : evalListHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "a")] with _ | vs
  · rw [hargs] at hrun; cases hrun
  · rw [hargs] at hrun
    dsimp only at hrun
    rcases hfound : PanSemStateFiniteExact.lookupCodeHOLFinite state.code.lookup
        (ofString "u256_byte_length") vs with _ | ⟨body, callee, rs⟩
    · rw [hfound] at hrun; cases hrun
    · rw [hfound] at hrun
      dsimp only at hrun
      split at hrun
      · cases hrun
      · have hle_clk := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
        rcases hran : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with ⟨res, post⟩
        rw [hran] at hrun hle_clk
        have hfix : fixClockHOLFinite (callEntryStateHOLFinite state callee) (res, post) = (res, post) := by
          simp [fixClockHOLFinite, Nat.not_lt.mpr hle_clk]
        rw [hfix] at hrun
        dsimp only at hrun
        cases res with
        | none => cases hrun
        | some r =>
          cases r with
          | returned val =>
            have hfound' := hfound
            rw [hcode] at hfound'
            have hbd := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup
              (ofString "u256_byte_length") _ _ body .one rs vs callee lookup_u256_byte_length hfound'
            subst hbd
            obtain ⟨b0, rfl, hb0⟩ := evaluate_u256_byte_length_le
              (callEntryStateHOLFinite state callee) hcode val post hran
            dsimp only at hrun
            split at hrun
            · let resumed := setVarHOLFinite (ofString "len") (.val (.word b0))
                { post with locals := state.locals }
              let contProg : ProgHOL 64 :=
                .dec (ofString "i") .one (.const 0#64)
                  (.seq
                    (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "len")))
                      u256ToBeMinLoopBody)
                    (.return (.var .local (ofString "len"))))
              rcases hc : evaluateHOLFiniteState resumed contProg with ⟨rc, sc⟩
              have hc_unf := hc
              dsimp only [resumed, contProg, u256ToBeMinLoopBody] at hc_unf
              have hcont_fst :
                  (evaluateHOLFiniteState resumed contProg).1 = some (.returned w) := by
                rw [hc]
                rw [hc_unf] at hrun
                exact (Prod.mk.inj hrun).1
              dsimp only [contProg] at hcont_fst
              rw [evaluateHOLFiniteState_dec_total] at hcont_fst
              simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true] at hcont_fst
              let s_i := setVarHOLFinite (ofString "i") (.val (.word 0#64)) resumed
              have hsi_len : s_i.locals.lookup (ofString "len") = some (.val (.word b0)) := by
                have hne : ofString "i" ≠ ofString "len" := by decide
                simp [s_i, resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne]
              rw [evaluateHOLFiniteState_seq_line780] at hcont_fst
              have hframe := evaluate_avoidsLocal_flowing (ofString "len")
                (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "len")))
                  u256ToBeMinLoopBody)
                (by decide) s_i
              rcases hloop : evaluateHOLFiniteState s_i
                  (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "len")))
                    u256ToBeMinLoopBody)
                  with ⟨rl, sl⟩
              rw [hloop] at hcont_fst hframe
              cases rl with
              | none =>
                dsimp only at hcont_fst
                have hsl_len : sl.locals.lookup (ofString "len") = some (.val (.word b0)) :=
                  (hframe (Or.inl rfl)).trans hsi_len
                rw [evaluateHOLFiniteState_return] at hcont_fst
                have hev_len : @evalHOLExact 64 F _ sl.toExact
                    (fun a => Classical.propDecidable (sl.memaddrs a))
                    (.var .local (ofString "len")) = some (.val (.word b0)) := hsl_len
                rw [hev_len] at hcont_fst
                dsimp only at hcont_fst
                split at hcont_fst
                · simp only [Option.some.injEq, PanSemResultExact.returned.injEq] at hcont_fst
                  subst hcont_fst
                  exact ⟨b0, rfl, hb0⟩
                · simp at hcont_fst
              | some rloop =>
                dsimp only at hcont_fst
                exfalso
                exact u256_to_be_min_loop_no_ret s_i w (by rw [hloop]; exact hcont_fst)
            · cases hrun
          | _ => cases hrun

theorem progBounded_u256_to_be_min_decCall (name : MlS)
    (a out : ExpHOL 64) {cont : ProgHOL 64} {tailCost : Nat}
    (hcont : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (K : BitVec 64),
      K.toNat ≤ 32 →
      s.code = originalRuntimeCode →
      s.locals.lookup name = some (.val (.word K)) →
      tailCost ≤ s.clock →
      RunBounded s cont tailCost) :
    ProgBounded (.decCall name .one (ofString "u256_to_be_min") [a, out] cont)
      ((2 ^ 64 - 1) * 2 + 7 + tailCost) := by
  intro F state hcode hbudget
  cases hargs : evalListHOLFinite state
      (h := fun ad => Classical.propDecidable (state.memaddrs ad)) [a, out] with
  | none =>
    rw [evaluateHOLFiniteState_decCall_args_none state _ _ _ _ _ hargs]
    simp
  | some vs =>
    refine (RunBounded.decCall hargs
      (bodyCost := (2 ^ 64 - 1) * 2 + 6) (tailCost := tailCost)
      (by omega) ?_).weaken (by omega)
    intro body locals rs hfound
    refine ⟨?_, ?_⟩
    · exact ProgBounded.bodies_of_fun funBounded_u256_to_be_min
        state hcode (by omega) vs body locals rs hfound
    · intro val post hran hpost_budget
      have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata
        (callEntryStateHOLFinite state locals) body
      rw [hran] at hmeta
      have hfound' := hfound
      rw [hcode] at hfound'
      have hbd := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup
        (ofString "u256_to_be_min") _ _ body .one rs vs locals lookup_u256_to_be_min hfound'
      subst hbd
      obtain ⟨K, rfl, hK⟩ := evaluate_u256_to_be_min_le
        (callEntryStateHOLFinite state locals) hcode val post hran
      let resumed := setVarHOLFinite name (.val (.word K)) { post with locals := state.locals }
      have hres_code : resumed.code = originalRuntimeCode := hmeta.1.trans hcode
      have hres_nm : resumed.locals.lookup name = some (.val (.word K)) := by
        simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      exact hcont resumed K hK hres_code hres_nm hpost_budget

theorem funBounded_rlp_put_u256 :
    FunBounded (ofString "rlp_put_u256") ((2 ^ 64 - 1) * 2 + 2 ^ 64 + 34) := by
  refine funBounded_of_guestAst 228 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_rlp_put_u256 ((2 ^ 64 - 1) * 2 + 2 ^ 64 + 34) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_rlp_put_u256,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine ProgBounded.weaken
    (ProgBounded.decCall funBounded_heap_mark _ _ _
      (ProgBounded.decCall funBounded_alloc _ _ _
        (progBounded_u256_to_be_min_decCall (ofString "n")
          (.var .local (ofString "v")) (.var .local (ofString "tmp"))
          (tailCost := 2 ^ 64 + 19 + 32 / 8 + 1) ?_)))
    (by generalize (2 : Nat) ^ 64 - 1 = W; generalize (2 : Nat) ^ 64 = V; omega)
  intro F s K hK hcode hn hbudget
  refine runBounded_rlp_encode_bytes_decCall s (ofString "w") .one
    (.var .local (ofString "dst")) (.var .local (ofString "tmp")) (.var .local (ofString "n"))
    32 (by decide) hcode hbudget ?_ ?_
  · intro K' hk'
    rw [evalHOLFinite_eq_toExact] at hk'
    simp only [evalHOLExact] at hk'
    change s.locals.lookup (ofString "n") = some (.val (.word K')) at hk'
    rw [hn] at hk'
    cases hk'
    exact hK
  · intro val post hpost_code hpost_budget
    exact (ProgBounded.weaken
      (ProgBounded.seq (ProgBounded.call funBounded_heap_release none _)
        (ProgBounded.straight _ rfl)) (by decide))
      (setVarHOLFinite (ofString "w") val { post with locals := s.locals })
      hpost_code hpost_budget

theorem funBounded_tx_put_u256 :
    FunBounded (ofString "tx_put_u256") ((2 ^ 64 - 1) * 2 + 2 ^ 64 + 34) := by
  refine funBounded_of_guestAst 318 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_tx_put_u256 ((2 ^ 64 - 1) * 2 + 2 ^ 64 + 34) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_tx_put_u256,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine ProgBounded.weaken
    (ProgBounded.decCall funBounded_heap_mark _ _ _
      (ProgBounded.decCall funBounded_alloc _ _ _
        (progBounded_u256_to_be_min_decCall (ofString "n")
          (.var .local (ofString "v")) (.var .local (ofString "tmp"))
          (tailCost := 2 ^ 64 + 19 + 32 / 8 + 1) ?_)))
    (by generalize (2 : Nat) ^ 64 - 1 = W; generalize (2 : Nat) ^ 64 = V; omega)
  intro F s K hK hcode hn hbudget
  refine runBounded_rlp_encode_bytes_decCall s (ofString "w") .one
    (.var .local (ofString "dst")) (.var .local (ofString "tmp")) (.var .local (ofString "n"))
    32 (by decide) hcode hbudget ?_ ?_
  · intro K' hk'
    rw [evalHOLFinite_eq_toExact] at hk'
    simp only [evalHOLExact] at hk'
    change s.locals.lookup (ofString "n") = some (.val (.word K')) at hk'
    rw [hn] at hk'
    cases hk'
    exact hK
  · intro val post hpost_code hpost_budget
    exact (ProgBounded.weaken
      (ProgBounded.seq (ProgBounded.call funBounded_heap_release none _)
        (ProgBounded.straight _ rfl)) (by decide))
      (setVarHOLFinite (ofString "w") val { post with locals := s.locals })
      hpost_code hpost_budget

/-! ## Section 3: Pure, Arithmetic, RLP, Transaction, Account, and EVM Helpers -/

theorem funBounded_min : FunBounded (ofString "min") 0 :=
  funBounded_of_guestAst 31 (by rw [guestAst_len]; decide) Guest.Software.guestFn_min 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_max : FunBounded (ofString "max") 0 :=
  funBounded_of_guestAst 32 (by rw [guestAst_len]; decide) Guest.Software.guestFn_max 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_u256_fits_word : FunBounded (ofString "u256_fits_word") 0 :=
  funBounded_of_guestAst 41 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_fits_word 0 rfl (ProgBounded.straight _ rfl)

theorem funBounded_u256_is_zero : FunBounded (ofString "u256_is_zero") 0 :=
  funBounded_of_guestAst 42 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_is_zero 0 rfl (ProgBounded.straight _ rfl)

theorem funBounded_u256_eq : FunBounded (ofString "u256_eq") 0 :=
  funBounded_of_guestAst 45 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_eq 0 rfl (ProgBounded.straight _ rfl)

theorem funBounded_u256_lt : FunBounded (ofString "u256_lt") 0 :=
  funBounded_of_guestAst 46 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_lt 0 rfl (ProgBounded.straight _ rfl)

theorem funBounded_u256_add_carry : FunBounded (ofString "u256_add_carry") 0 :=
  funBounded_of_guestAst 55 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_add_carry 0 rfl (ProgBounded.straight _ rfl)

theorem funBounded_u256_add : FunBounded (ofString "u256_add") 0 :=
  funBounded_of_guestAst 56 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_add 0 rfl (ProgBounded.straight _ rfl)

theorem funBounded_u256_sub : FunBounded (ofString "u256_sub") 0 :=
  funBounded_of_guestAst 57 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_sub 0 rfl (ProgBounded.straight _ rfl)

theorem funBounded_mul64x64 : FunBounded (ofString "mul64x64") 0 :=
  funBounded_of_guestAst 59 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_mul64x64 0 rfl (ProgBounded.straight _ rfl)

theorem funBounded_u256_mul : FunBounded (ofString "u256_mul") 7 := by
  refine funBounded_of_guestAst 60 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_mul 7 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_u256_mul,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine ProgBounded.weaken
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
    (by decide)

theorem funBounded_u256_mul_full : FunBounded (ofString "u256_mul_full") 16 := by
  refine funBounded_of_guestAst 61 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_mul_full 16 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_u256_mul_full,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_mul64x64 _ _ _
      (ProgBounded.decCall funBounded_mul64x64 _ _ _
        (ProgBounded.decCall funBounded_mul64x64 _ _ _
          (ProgBounded.decCall funBounded_mul64x64 _ _ _
            (ProgBounded.decCall funBounded_mul64x64 _ _ _
              (ProgBounded.decCall funBounded_mul64x64 _ _ _
                (ProgBounded.decCall funBounded_mul64x64 _ _ _
                  (ProgBounded.decCall funBounded_mul64x64 _ _ _
                    (ProgBounded.decCall funBounded_mul64x64 _ _ _
                      (ProgBounded.decCall funBounded_mul64x64 _ _ _
                        (ProgBounded.decCall funBounded_mul64x64 _ _ _
                          (ProgBounded.decCall funBounded_mul64x64 _ _ _
                            (ProgBounded.decCall funBounded_mul64x64 _ _ _
                              (ProgBounded.decCall funBounded_mul64x64 _ _ _
                                (ProgBounded.decCall funBounded_mul64x64 _ _ _
                                  (ProgBounded.decCall funBounded_mul64x64 _ _ _
                                    (ProgBounded.straight _ rfl)))))))))))))))))
    (by decide)

theorem funBounded_u256_shr : FunBounded (ofString "u256_shr") 0 :=
  funBounded_of_guestAst 82 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_shr 0 rfl (ProgBounded.straight _ rfl)

theorem funBounded_rlp_word_encoded_len : FunBounded (ofString "rlp_word_encoded_len") 9 := by
  refine funBounded_of_guestAst 127 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_rlp_word_encoded_len 9 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_rlp_word_encoded_len,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (progBounded_seq_straight _ rfl
      (ProgBounded.decCall funBounded_rlp_be_len _ _ _ (ProgBounded.straight _ rfl)))
    (by decide)

theorem funBounded_htab_new : FunBounded (ofString "htab_new") 8 := by
  refine funBounded_of_guestAst 128 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_htab_new 8 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_htab_new,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine ProgBounded.weaken
    (ProgBounded.decCall funBounded_alloc _ _ _
      (ProgBounded.dec _ _ _ (ProgBounded.dec _ _ _
        (progBounded_seq_straight _ rfl
          (progBounded_seq_straight _ rfl
            (progBounded_seq_straight _ rfl
              (progBounded_seq_straight _ rfl
                (progBounded_seq_straight _ rfl
                  (ProgBounded.decCall funBounded_alloc _ _ _
                    (progBounded_seq_straight _ rfl
                      (ProgBounded.decCall funBounded_alloc _ _ _
                        (progBounded_seq_straight _ rfl
                          (ProgBounded.decCall funBounded_alloc _ _ _
                            (ProgBounded.straight _ rfl))))))))))))))
    (by decide)

theorem funBounded_htab_item : FunBounded (ofString "htab_item") 0 :=
  funBounded_of_guestAst 143 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_htab_item 0 rfl (ProgBounded.straight _ rfl)

theorem funBounded_mpt_fail : FunBounded (ofString "mpt_fail") 0 :=
  funBounded_of_guestAst 246 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_mpt_fail 0 rfl (ProgBounded.straight _ rfl)

theorem funBounded_mpt_new : FunBounded (ofString "mpt_new") 2 := by
  refine funBounded_of_guestAst 268 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_mpt_new 2 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_mpt_new,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_alloc _ _ _ (ProgBounded.straight _ rfl))
    (by decide)

theorem funBounded_node_ref_len : FunBounded (ofString "node_ref_len") 1 := by
  refine funBounded_of_guestAst 287 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_node_ref_len 1 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_node_ref_len,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (progBounded_seq_straight _ rfl
      (progBounded_seq_straight _ rfl
        (ProgBounded.seq
          (ProgBounded.iteMax _ (ProgBounded.call funBounded_mpt_fail none _)
            (ProgBounded.straight _ rfl))
          (ProgBounded.straight _ rfl))))
    (by decide)

theorem funBounded_tx_has_access_list : FunBounded (ofString "tx_has_access_list") 0 :=
  funBounded_of_guestAst 315 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_tx_has_access_list 0 rfl (ProgBounded.straight _ rfl)

theorem funBounded_calculate_total_blob_gas :
    FunBounded (ofString "calculate_total_blob_gas") 0 :=
  funBounded_of_guestAst 317 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_calculate_total_blob_gas 0 rfl (ProgBounded.straight _ rfl)

theorem funBounded_tx_u256_encoded_len : FunBounded (ofString "tx_u256_encoded_len") 6 := by
  refine funBounded_of_guestAst 319 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_tx_u256_encoded_len 6 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_tx_u256_encoded_len,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_u256_byte_length _ _ _ (ProgBounded.straight _ rfl))
    (by decide)

theorem RunBounded.tail {F : Type} {state : PanSemStateFiniteExact 64 F} {function : MlS}
    {arguments : List (ExpHOL 64)} {values : List (ValueHOL 64)} {bodyCost : Nat}
    (args : evalListHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments = some values)
    (budget : bodyCost + 1 ≤ state.clock)
    (bodies : ∀ body locals returnShape,
      lookupCodeHOLFinite state.code.lookup function values = some (body, locals, returnShape) →
      RunBounded (callEntryStateHOLFinite state locals) body bodyCost) :
    RunBounded state (.call none function arguments) (bodyCost + 1) := by
  unfold RunBounded
  cases lookup : lookupCodeHOLFinite state.code.lookup function values with
  | none =>
    rw [evaluateHOLFiniteState_call, args]
    dsimp only
    rw [lookup]
    simp
  | some installed =>
    obtain ⟨body, callee, returnShape⟩ := installed
    have bounded := bodies body callee returnShape lookup
    unfold RunBounded at bounded
    have nonzero : state.clock ≠ 0 := by omega
    cases ran : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
    | mk result post =>
      rw [ran] at bounded
      obtain ⟨spent, kept, safe⟩ := bounded
      change state.clock - 1 ≤ post.clock + bodyCost at spent
      change post.clock ≤ state.clock - 1 at kept
      rw [evaluateHOLFiniteState_call, args]
      dsimp only
      rw [lookup]
      dsimp only
      rw [if_neg nonzero, ran]
      rcases result with _ | (_ | _ | _ | _ | _ | _ | _ | _ | _)
      all_goals first
        | (simp at safe; done)
        | (dsimp only; split <;>
            ((try simp only [emptyLocalsHOLFinite]); exact ⟨by omega, by omega, by simp⟩))
        | (dsimp only; (try simp only [emptyLocalsHOLFinite]);
            exact ⟨by omega, by omega, by simp [safe]⟩)

theorem runBounded_rlp_encode_bytes_tail {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (dst src sizeExp : ExpHOL 64) (M : Nat) (hM : M + 32 < 2 ^ 64)
    (hcode : state.code = originalRuntimeCode)
    (hbudget : 2 ^ 64 + 19 + M / 8 ≤ state.clock)
    (hbnd : ∀ (K : BitVec 64),
      evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) sizeExp =
        some (.val (.word K)) → K.toNat ≤ M) :
    RunBounded state
      (.call none (ofString "rlp_encode_bytes") [dst, src, sizeExp])
      (2 ^ 64 + 19 + M / 8) := by
  cases hargs : evalListHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a)) [dst, src, sizeExp] with
  | none =>
    unfold RunBounded
    rw [evaluateHOLFiniteState_call, hargs]
    simp
  | some vs =>
    have hlast : ∃ v1 v2,
        (∃ K, vs = [v1, v2, .val (.word K)] ∧
          evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) sizeExp =
            some (.val (.word K))) ∨
        lookupCodeHOLFinite state.code.lookup (ofString "rlp_encode_bytes") vs = none := by
      rw [evalListHOLFinite_eq_toExact] at hargs
      simp only [evalListHOLExact] at hargs
      rcases h1 : @evalHOLExact 64 F _ state.toExact
          (fun a => Classical.propDecidable (state.memaddrs a)) dst with _ | v1
      · rw [h1] at hargs; cases hargs
      · rw [h1] at hargs
        rcases h2 : @evalHOLExact 64 F _ state.toExact
            (fun a => Classical.propDecidable (state.memaddrs a)) src with _ | v2
        · rw [h2] at hargs; cases hargs
        · rw [h2] at hargs
          rcases h3 : @evalHOLExact 64 F _ state.toExact
              (fun a => Classical.propDecidable (state.memaddrs a)) sizeExp with _ | v3
          · rw [h3] at hargs; cases hargs
          · rw [h3] at hargs
            cases hargs
            cases v3 with
            | val wv =>
              cases wv with
              | word K =>
                refine ⟨v1, v2, Or.inl ⟨K, rfl, ?_⟩⟩
                rw [evalHOLFinite_eq_toExact]
                exact h3
            | rStruct _ =>
              refine ⟨v1, v2, Or.inr ?_⟩
              rw [hcode]
              unfold PanSemStateFiniteExact.lookupCodeHOLFinite
              split
              · rfl
              · rename_i _ _ _ raw
                simp [lookupCodeHOLExact, lookup_rlp_encode_bytes, shapeOfHOLExact, shapeEqHOL]
                  at raw
            | nStruct _ _ =>
              refine ⟨v1, v2, Or.inr ?_⟩
              rw [hcode]
              unfold PanSemStateFiniteExact.lookupCodeHOLFinite
              split
              · rfl
              · rename_i _ _ _ raw
                simp [lookupCodeHOLExact, lookup_rlp_encode_bytes, shapeOfHOLExact, shapeEqHOL]
                  at raw
    obtain ⟨v1, v2, hvs⟩ := hlast
    rcases hvs with ⟨K, rfl, hk_eval⟩ | hnone
    · have hK_le : K.toNat ≤ M := hbnd K hk_eval
      have hdiv : K.toNat / 8 ≤ M / 8 := Nat.div_le_div_right hK_le
      exact (RunBounded.tail hargs (bodyCost := 2 ^ 64 + 18 + M / 8) (by omega)
        (fun body locals rs hfound => by
          rw [hcode] at hfound
          obtain ⟨rfl, hn⟩ := three_arg_lookup_last originalRuntimeCode.lookup
            (ofString "rlp_encode_bytes") (ofString "dst") (ofString "src") (ofString "n")
            (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes)
            (by decide) (by decide) (by decide) lookup_rlp_encode_bytes hfound
          exact (runBounded_rlp_encode_bytes_body (callEntryStateHOLFinite state locals)
            K (by omega) hcode hn
            (by change 2 ^ 64 + 18 + K.toNat / 8 ≤ state.clock - 1; omega)).weaken
            (by omega))).weaken (by omega)
    · unfold RunBounded
      rw [evaluateHOLFiniteState_call, hargs]
      dsimp only
      rw [hnone]
      simp

theorem progBounded_rlp_encode_bytes_tail_const
    (dst src : ExpHOL 64) (K : BitVec 64) (hsmall : K.toNat + 32 < 2 ^ 64) :
    ProgBounded (.call none (ofString "rlp_encode_bytes")
      [dst, src, .const K]) (2 ^ 64 + 19 + K.toNat / 8) :=
  fun state hcode hbudget =>
    runBounded_rlp_encode_bytes_tail state dst src (.const K) K.toNat hsmall
      hcode hbudget (fun K' hk => by
        rw [evalHOLFinite_eq_toExact] at hk
        simp [evalHOLExact] at hk
        cases hk
        exact le_refl _)

theorem funBounded_tx_put_to : FunBounded (ofString "tx_put_to") (2 ^ 64 + 21) := by
  refine funBounded_of_guestAst 320 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_tx_put_to (2 ^ 64 + 21) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_tx_put_to,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine progBounded_seq_straight _ rfl ?_
  refine ProgBounded.weaken
    (progBounded_rlp_encode_bytes_tail_const _ _ 20#64 (by decide)) ?_
  have h20 : (20#64).toNat = 20 := rfl
  rw [h20]

end InitECandidate.Solver.GuestBoundBlockTxBal
