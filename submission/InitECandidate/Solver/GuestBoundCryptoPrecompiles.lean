import InitECandidate.Solver.PanRunBoundedExt

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace InitECandidate.Solver.GuestBoundCryptoPrecompiles

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.PanRunBoundedExt

/-! ## Section 1: Pure Local Limit Invariance & Extended Loop Bodies -/

def isSimpleLimitExp : ExpHOL 64 → Bool
  | .const _ => true
  | .var .local _ => true
  | .op .add [.var .local _, .var .local _] => true
  | .op .sub [.var .local _, .const _] => true
  | _ => false

def progAvoidsLimitExp (p : ProgHOL 64) : ExpHOL 64 → Bool
  | .const _ => true
  | .var .local nm => avoidsLocal nm p
  | .op .add [.var .local n1, .var .local n2] => avoidsLocal n1 p && avoidsLocal n2 p
  | .op .sub [.var .local n1, .const _] => avoidsLocal n1 p
  | _ => false

private theorem evalHOLExact_limit_eq {F : Type}
    (s1 s2 : PanSemStateFiniteExact 64 F) (p : ProgHOL 64) (e : ExpHOL 64)
    (hpure : isSimpleLimitExp e = true)
    (hav : progAvoidsLimitExp p e = true)
    (hagree : ∀ nm, avoidsLocal nm p = true → s1.locals.lookup nm = s2.locals.lookup nm) :
    @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a)) e =
      @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a)) e := by
  cases e with
  | const _ => rfl
  | var vk nm =>
    cases vk with
    | global => simp [isSimpleLimitExp] at hpure
    | «local» =>
      simp only [progAvoidsLimitExp] at hav
      simp only [evalHOLExact]
      exact hagree nm hav
  | op bop es =>
    cases bop with
    | add =>
      rcases es with _ | ⟨e1, _ | ⟨e2, _ | _⟩⟩ <;> (try (simp [isSimpleLimitExp] at hpure; done))
      cases e1 with
      | var vk1 n1 =>
        cases vk1 with
        | global => simp [isSimpleLimitExp] at hpure
        | «local» =>
          cases e2 with
          | var vk2 n2 =>
            cases vk2 with
            | global => simp [isSimpleLimitExp] at hpure
            | «local» =>
              simp only [progAvoidsLimitExp, Bool.and_eq_true] at hav
              simp only [evalHOLExact, evalListHOLExact]
              rw [hagree n1 hav.1, hagree n2 hav.2]
          | _ => simp [isSimpleLimitExp] at hpure
      | _ => simp [isSimpleLimitExp] at hpure
    | sub =>
      rcases es with _ | ⟨e1, _ | ⟨e2, _ | _⟩⟩ <;> (try (simp [isSimpleLimitExp] at hpure; done))
      cases e1 with
      | var vk1 n1 =>
        cases vk1 with
        | global => simp [isSimpleLimitExp] at hpure
        | «local» =>
          cases e2 with
          | const _ =>
            simp only [progAvoidsLimitExp] at hav
            simp only [evalHOLExact, evalListHOLExact]
            rw [hagree n1 hav]
          | _ => simp [isSimpleLimitExp] at hpure
      | _ => simp [isSimpleLimitExp] at hpure
    | _ => simp [isSimpleLimitExp] at hpure
  | _ => simp [isSimpleLimitExp] at hpure

def CalleeBodyBounded (fn : MlS) (args : List (ExpHOL 64)) (ov : Nat) : Prop :=
  ov ≥ 1 ∧
  ∀ {F : Type} (state : PanSemStateFiniteExact 64 F),
    state.code = originalRuntimeCode → ov ≤ state.clock →
    ∀ values body callee retShape,
      evalListHOLFinite state
        (h := fun a => Classical.propDecidable (state.memaddrs a)) args = some values →
      lookupCodeHOLFinite state.code.lookup fn values = some (body, callee, retShape) →
      RunBounded (callEntryStateHOLFinite state callee) body (ov - 1)

theorem calleeBodyBounded_of_funBounded {fn : MlS} {args : List (ExpHOL 64)} {cost : Nat}
    (hfn : FunBounded fn cost) :
    CalleeBodyBounded fn args (cost + 1) := by
  refine ⟨by omega, fun state hcode hbudget values body callee retShape _hargs hlook => ?_⟩
  simp only [Nat.add_sub_cancel]
  exact ProgBounded.bodies_of_fun hfn state hcode hbudget values body callee retShape hlook

theorem progBounded_call_of_calleeBodyBounded
    (dest : Option (VarKind × MlS)) {fn : MlS} {args : List (ExpHOL 64)} {ov : Nat}
    (hcb : CalleeBodyBounded fn args ov) :
    ProgBounded (.call (some (dest, none)) fn args) ov := by
  rcases hcb with ⟨hov, hrun⟩
  intro F state hcode hbudget
  cases hargs : evalListHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a)) args with
  | none =>
    rw [evaluateHOLFiniteState_call, hargs]
    simp
  | some values =>
    have hcall := RunBounded.call (destination := dest) (bodyCost := ov - 1) hargs
      (by omega) (fun body callee retShape hlook =>
        hrun state hcode hbudget values body callee retShape hargs hlook)
    exact hcall.weaken (by omega)

theorem progBounded_tailCall_of_calleeBodyBounded
    {fn : MlS} {args : List (ExpHOL 64)} {ov : Nat}
    (hcb : CalleeBodyBounded fn args ov) :
    ProgBounded (.call none fn args) ov := by
  rcases hcb with ⟨hov, hrun⟩
  intro F state hcode hbudget
  cases hargs : evalListHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a)) args with
  | none =>
    rw [evaluateHOLFiniteState_call, hargs]
    simp
  | some values =>
    cases hlook : lookupCodeHOLFinite state.code.lookup fn values with
    | none =>
      rw [evaluateHOLFiniteState_call, hargs]
      dsimp only
      rw [hlook]
      simp
    | some installed =>
      rcases installed with ⟨body, callee, retShape⟩
      have hb := hrun state hcode hbudget values body callee retShape hargs hlook
      unfold RunBounded at hb
      have nonzero : state.clock ≠ 0 := by omega
      cases ran : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
      | mk result post =>
        rw [ran] at hb
        obtain ⟨spent, kept, safe⟩ := hb
        change state.clock - 1 ≤ post.clock + (ov - 1) at spent
        change post.clock ≤ state.clock - 1 at kept
        rw [evaluateHOLFiniteState_call, hargs]
        dsimp only
        rw [hlook]
        dsimp only
        rw [if_neg nonzero, ran]
        rcases result with _ | (_ | _ | _ | _ | _ | _ | _ | _ | _)
        all_goals first
          | (simp at safe; done)
          | (dsimp only; split <;>
              ((try simp only [emptyLocalsHOLFinite]); exact ⟨by omega, by omega, by simp⟩))
          | (dsimp only; (try simp only [emptyLocalsHOLFinite]);
              exact ⟨by omega, by omega, by simp [safe]⟩)

theorem progBounded_decCall_of_calleeBodyBounded
    (name : MlS) (shape : ShapeHOL) {fn : MlS} {args : List (ExpHOL 64)}
    {cont : ProgHOL 64} {ov tCost : Nat}
    (hcb : CalleeBodyBounded fn args ov)
    (hcont : ProgBounded cont tCost) :
    ProgBounded (.decCall name shape fn args cont) (ov + tCost) := by
  rcases hcb with ⟨hov, hrun⟩
  intro F state hcode hbudget
  cases hargs : evalListHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a)) args with
  | none =>
    rw [evaluateHOLFiniteState_decCall_args_none state name shape fn args cont hargs]
    simp
  | some values =>
    have hdc := RunBounded.decCall (name := name) (shape := shape) (continuation := cont)
      (bodyCost := ov - 1) (tailCost := tCost) hargs (by omega)
      (fun body callee retShape hlook => by
        have hb := hrun state hcode (by omega) values body callee retShape hargs hlook
        have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) body
        refine ⟨hb, fun val post hran hpost_clk => ?_⟩
        rw [hran] at hmeta
        exact hcont _ (hmeta.1.trans hcode) hpost_clk)
    exact hdc.weaken (by omega)

private theorem run_decCall_calleeBody_step {F : Type}
    (state : PanSemStateFiniteExact 64 F) (code : state.code = originalRuntimeCode)
    (counter name fn : MlS) (shape : ShapeHOL) (args : List (ExpHOL 64))
    (cont : ProgHOL 64) (w wNext : BitVec 64) (ov cCost : Nat)
    (distinct : counter ≠ name)
    (atCounter : state.locals.lookup counter = some (.val (.word w)))
    (budget : ov + cCost ≤ state.clock)
    (hcb : CalleeBodyBounded fn args ov)
    (ih : ∀ (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      s.locals.lookup counter = some (.val (.word w)) → cCost ≤ s.clock →
      s.clock ≤ (evaluateHOLFiniteState s cont).2.clock + cCost ∧
        (evaluateHOLFiniteState s cont).2.clock ≤ s.clock ∧
        (evaluateHOLFiniteState s cont).1 ≠ some .timeOut ∧
        (evaluateHOLFiniteState s cont).1 ≠ some .continue ∧
        ((evaluateHOLFiniteState s cont).1 = none →
          (evaluateHOLFiniteState s cont).2.locals.lookup counter = some (.val (.word wNext)) ∧
          (evaluateHOLFiniteState s cont).2.code = s.code)) :
    state.clock ≤ (evaluateHOLFiniteState state (.decCall name shape fn args cont)).2.clock +
        (ov + cCost) ∧
      (evaluateHOLFiniteState state (.decCall name shape fn args cont)).2.clock ≤ state.clock ∧
      (evaluateHOLFiniteState state (.decCall name shape fn args cont)).1 ≠ some .timeOut ∧
      (evaluateHOLFiniteState state (.decCall name shape fn args cont)).1 ≠ some .continue ∧
      ((evaluateHOLFiniteState state (.decCall name shape fn args cont)).1 = none →
        (evaluateHOLFiniteState state (.decCall name shape fn args cont)).2.locals.lookup counter =
          some (.val (.word wNext)) ∧
        (evaluateHOLFiniteState state (.decCall name shape fn args cont)).2.code = state.code) := by
  rcases hcb with ⟨hov, hrun⟩
  cases hargs : evalListHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a)) args with
  | none =>
    rw [evaluateHOLFiniteState_decCall_args_none state name shape fn args cont hargs]
    exact ⟨Nat.le_add_right _ _, le_refl _, by simp, by simp, by simp⟩
  | some values =>
    cases hlook : lookupCodeHOLFinite state.code.lookup fn values with
    | none =>
      rw [evaluateHOLFiniteState_decCall_lookup_none state name shape fn args cont values hargs hlook]
      exact ⟨Nat.le_add_right _ _, le_refl _, by simp, by simp, by simp⟩
    | some installed =>
      rcases installed with ⟨body, callee, retShape⟩
      rw [evaluateHOLFiniteState_decCall_total, hargs]
      dsimp only
      rw [hlook]
      dsimp only
      have nonzero : state.clock ≠ 0 := by omega
      rw [if_neg nonzero]
      let entry := callEntryStateHOLFinite state callee
      have hbody := hrun state code (by omega) values body callee retShape hargs hlook
      unfold RunBounded at hbody
      have metaBody := PanRunBounded.evaluateHOLFiniteState_metadata entry body
      cases bodyRun : evaluateHOLFiniteState entry body with
      | mk r1 post =>
        rw [bodyRun] at hbody metaBody
        dsimp only at hbody metaBody
        obtain ⟨bSpent, bKept, bSafe⟩ := hbody
        change post.clock ≤ entry.clock at bKept
        have fixed : fixClockHOLFinite entry (r1, post) = (r1, post) := by
          simp [fixClockHOLFinite, Nat.not_lt.mpr bKept]
        rw [fixed]
        dsimp only
        change state.clock - 1 ≤ post.clock + (ov - 1) at bSpent
        change post.clock ≤ state.clock - 1 at bKept
        cases r1 with
        | none =>
          dsimp only [emptyLocalsHOLFinite]
          exact ⟨by omega, by omega, by simp, by simp, by simp⟩
        | some res1 =>
          cases res1 with
          | timeOut => exact absurd rfl bSafe
          | returned val =>
            dsimp only
            split
            · let resumed := setVarHOLFinite name val { post with locals := state.locals }
              have rCode : resumed.code = originalRuntimeCode := by
                change post.code = originalRuntimeCode
                exact metaBody.1.trans code
              have rCounter : resumed.locals.lookup counter = some (.val (.word w)) := by
                simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  Ne.symm distinct, atCounter]
              have rBudget : cCost ≤ resumed.clock := by
                change cCost ≤ post.clock
                omega
              obtain ⟨c1, c2, c3, c4, c5⟩ := ih resumed rCode rCounter rBudget
              cases contRun : evaluateHOLFiniteState resumed cont with
              | mk r2 inner =>
                rw [contRun] at c1 c2 c3 c4 c5
                dsimp only at c1 c2 c3 c4 c5 ⊢
                change post.clock ≤ inner.clock + cCost at c1
                change inner.clock ≤ post.clock at c2
                refine ⟨by omega, by omega, c3, c4, fun normal => ?_⟩
                obtain ⟨i1, i2⟩ := c5 normal
                refine ⟨?_, i2.trans metaBody.1⟩
                rw [PanRunBounded.resVarEq_lookup, if_neg distinct]
                exact i1
            · dsimp only [emptyLocalsHOLFinite]
              exact ⟨by omega, by omega, by simp, by simp, by simp⟩
          | _ =>
            dsimp only [emptyLocalsHOLFinite]
            exact ⟨by omega, by omega, by simp, by simp, by simp⟩

inductive CountedBodyExt (counter : MlS) (step : BitVec 64) : ProgHOL 64 → Nat → Prop
  | incr :
      CountedBodyExt counter step
        (.assign .local counter (.op .add [.var .local counter, .const step])) 0
  | seqPre (first : ProgHOL 64) {tail : ProgHOL 64} {a b : Nat}
      (bounded : ProgBounded first a)
      (avoid : avoidsLocal counter first = true)
      (noCont : noTopContinue first = true)
      (rest : CountedBodyExt counter step tail b) :
      CountedBodyExt counter step (.seq first tail) (a + b)
  | seqPost {first : ProgHOL 64} (second : ProgHOL 64) {a b : Nat}
      (firstBody : CountedBodyExt counter step first a)
      (bounded : ProgBounded second b)
      (avoid : avoidsLocal counter second = true)
      (noCont : noTopContinue second = true) :
      CountedBodyExt counter step (.seq first second) (a + b)
  | dec (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL 64) {body : ProgHOL 64} {cost : Nat}
      (distinct : counter ≠ name)
      (rest : CountedBodyExt counter step body cost) :
      CountedBodyExt counter step (.dec name shape initializer body) cost
  | decCall (name : MlS) (shape : ShapeHOL) (fn : MlS) (args : List (ExpHOL 64))
      {cont : ProgHOL 64} {ov cCost : Nat}
      (distinct : counter ≠ name)
      (hcb : CalleeBodyBounded fn args ov)
      (rest : CountedBodyExt counter step cont cCost) :
      CountedBodyExt counter step (.decCall name shape fn args cont) (ov + cCost)

theorem CountedBodyExt.run {counter : MlS} {step : BitVec 64} {body : ProgHOL 64} {cost : Nat}
    (counted : CountedBodyExt counter step body cost) {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode) (w : BitVec 64)
    (atCounter : state.locals.lookup counter = some (.val (.word w))) (budget : cost ≤ state.clock) :
    state.clock ≤ (evaluateHOLFiniteState state body).2.clock + cost ∧
      (evaluateHOLFiniteState state body).2.clock ≤ state.clock ∧
      (evaluateHOLFiniteState state body).1 ≠ some .timeOut ∧
      (evaluateHOLFiniteState state body).1 ≠ some .continue ∧
      ((evaluateHOLFiniteState state body).1 = none →
        (evaluateHOLFiniteState state body).2.locals.lookup counter = some (.val (.word (w + step))) ∧
        (evaluateHOLFiniteState state body).2.code = state.code) := by
  induction counted generalizing state with
  | incr =>
    exact CountedBody.incr.run state code w atCounter budget
  | seqPre first bounded avoid noCont rest ih =>
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
        obtain ⟨t1, t2, t3, t4, t5⟩ := ih middle (meta'.1.trans code)
          (by rw [kept']; exact atCounter) (by omega)
        refine ⟨by omega, by omega, t3, t4, fun normal => ?_⟩
        obtain ⟨i1, i2⟩ := t5 normal
        exact ⟨i1, i2.trans meta'.1⟩
      | some r =>
        dsimp only
        refine ⟨by omega, by omega, safe, noContinue, fun h => by simp at h⟩
  | seqPost second _firstBody bounded avoid noCont ih =>
    rename_i first a b
    have meta1 := PanRunBounded.evaluateHOLFiniteState_metadata state first
    have firstStep := ih state code atCounter (by omega)
    rw [evaluateHOLFiniteState_seq_line780]
    cases firstRun : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [firstRun] at firstStep meta1
      dsimp only at firstStep meta1
      obtain ⟨f1, f2, f3, f4, f5⟩ := firstStep
      cases result with
      | none =>
        dsimp only
        obtain ⟨midCtr, midCode⟩ := f5 rfl
        have secBound := bounded middle (midCode.trans code) (by omega)
        have frame := evaluate_avoidsLocal_flowing counter second avoid middle
        have noContinue := evaluate_noTopContinue second noCont middle
        have meta2 := PanRunBounded.evaluateHOLFiniteState_metadata middle second
        cases secRun : evaluateHOLFiniteState middle second with
        | mk res2 post =>
          rw [secRun] at secBound frame noContinue meta2
          dsimp only at secBound frame noContinue meta2 ⊢
          obtain ⟨s1, s2, s3⟩ := secBound
          refine ⟨by omega, by omega, s3, noContinue, fun normal => ?_⟩
          have keptCtr := frame (by rw [normal]; exact Or.inl rfl)
          exact ⟨keptCtr.trans midCtr, meta2.1.trans midCode⟩
      | some r =>
        dsimp only
        exact ⟨by omega, by omega, f3, f4, fun h => by simp at h⟩
  | dec name shape initializer distinct _rest ih =>
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
  | decCall name shape fn args distinct hcb _rest ih =>
    exact run_decCall_calleeBody_step state code counter name fn shape args _ w (w + step) _ _
      distinct atCounter budget hcb (fun s hs hc hb => ih s hs hc hb)

inductive DecBodyExt (counter : MlS) : ProgHOL 64 → Nat → Prop
  | decr :
      DecBodyExt counter
        (.assign .local counter (.op .sub [.var .local counter, .const 1])) 0
  | seqPre (first : ProgHOL 64) {tail : ProgHOL 64} {a b : Nat}
      (bounded : ProgBounded first a)
      (avoid : avoidsLocal counter first = true)
      (noCont : noTopContinue first = true)
      (rest : DecBodyExt counter tail b) :
      DecBodyExt counter (.seq first tail) (a + b)
  | seqPost {first : ProgHOL 64} (second : ProgHOL 64) {a b : Nat}
      (firstBody : DecBodyExt counter first a)
      (bounded : ProgBounded second b)
      (avoid : avoidsLocal counter second = true)
      (noCont : noTopContinue second = true) :
      DecBodyExt counter (.seq first second) (a + b)
  | dec (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL 64) {body : ProgHOL 64} {cost : Nat}
      (distinct : counter ≠ name)
      (rest : DecBodyExt counter body cost) :
      DecBodyExt counter (.dec name shape initializer body) cost
  | decCall (name : MlS) (shape : ShapeHOL) (fn : MlS) (args : List (ExpHOL 64))
      {cont : ProgHOL 64} {ov cCost : Nat}
      (distinct : counter ≠ name)
      (hcb : CalleeBodyBounded fn args ov)
      (rest : DecBodyExt counter cont cCost) :
      DecBodyExt counter (.decCall name shape fn args cont) (ov + cCost)

theorem DecBodyExt.run {counter : MlS} {body : ProgHOL 64} {cost : Nat}
    (counted : DecBodyExt counter body cost) {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    have run : evaluateHOLFiniteState state
        (.assign .local counter (.op .sub [.var .local counter, .const 1])) =
        (none, setVarHOLFinite counter (.val (.word (w - 1))) state) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, atCounter, wordOpHOL,
        wordOp, valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact,
        setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
    rw [run]
    refine ⟨by simp [setVarHOLFinite], by simp [setVarHOLFinite], by simp, by simp,
      fun _ => ⟨?_, rfl⟩⟩
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  | seqPre first bounded avoid noCont _rest ih =>
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
        obtain ⟨t1, t2, t3, t4, t5⟩ := ih middle (meta'.1.trans code)
          (by rw [kept']; exact atCounter) (by omega)
        refine ⟨by omega, by omega, t3, t4, fun normal => ?_⟩
        obtain ⟨i1, i2⟩ := t5 normal
        exact ⟨i1, i2.trans meta'.1⟩
      | some r =>
        dsimp only
        refine ⟨by omega, by omega, safe, noContinue, fun h => by simp at h⟩
  | seqPost second _firstBody bounded avoid noCont ih =>
    rename_i first a b
    have meta1 := PanRunBounded.evaluateHOLFiniteState_metadata state first
    have firstStep := ih state code atCounter (by omega)
    rw [evaluateHOLFiniteState_seq_line780]
    cases firstRun : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [firstRun] at firstStep meta1
      dsimp only at firstStep meta1
      obtain ⟨f1, f2, f3, f4, f5⟩ := firstStep
      cases result with
      | none =>
        dsimp only
        obtain ⟨midCtr, midCode⟩ := f5 rfl
        have secBound := bounded middle (midCode.trans code) (by omega)
        have frame := evaluate_avoidsLocal_flowing counter second avoid middle
        have noContinue := evaluate_noTopContinue second noCont middle
        have meta2 := PanRunBounded.evaluateHOLFiniteState_metadata middle second
        cases secRun : evaluateHOLFiniteState middle second with
        | mk res2 post =>
          rw [secRun] at secBound frame noContinue meta2
          dsimp only at secBound frame noContinue meta2 ⊢
          obtain ⟨s1, s2, s3⟩ := secBound
          refine ⟨by omega, by omega, s3, noContinue, fun normal => ?_⟩
          have keptCtr := frame (by rw [normal]; exact Or.inl rfl)
          exact ⟨keptCtr.trans midCtr, meta2.1.trans midCode⟩
      | some r =>
        dsimp only
        exact ⟨by omega, by omega, f3, f4, fun h => by simp at h⟩
  | dec name shape initializer distinct _rest ih =>
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
  | decCall name shape fn args distinct hcb _rest ih =>
    exact run_decCall_calleeBody_step state code counter name fn shape args _ w (w - 1) _ _
      distinct atCounter budget hcb (fun s hs hc hb => ih s hs hc hb)

/-! ## Section 2: Loop Theorems (Constant, Downward, Variable-Limit, Shift, Clamped) -/

theorem countedWhileExt_run (counter : MlS) (op : Cmp) (hop : op = .less ∨ op = .lower)
    (K step : BitVec 64) (small : K.toNat + step.toNat < 2 ^ 63) (positive : 0 < step.toNat)
    {body : ProgHOL 64} {cost : Nat} (counted : CountedBodyExt counter step body cost) :
    ∀ n : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F),
      state.code = originalRuntimeCode →
      ∀ w : BitVec 64, state.locals.lookup counter = some (.val (.word w)) →
      w.toNat ≤ K.toNat + step.toNat →
      K.toNat - w.toNat = n → n * (cost + 1) ≤ state.clock →
      state.clock ≤ (evaluateHOLFiniteState state
          (.while (.cmp op (.var .local counter) (.const K)) body)).2.clock + n * (cost + 1) ∧
        (evaluateHOLFiniteState state
          (.while (.cmp op (.var .local counter) (.const K)) body)).2.clock ≤ state.clock ∧
        (evaluateHOLFiniteState state
          (.while (.cmp op (.var .local counter) (.const K)) body)).1 ≠ some .timeOut := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro F state code w atCounter within distance budget
    have condition := eval_counted_condition state counter op hop K w
      (by omega) (by omega) atCounter
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
          have nextRank : K.toNat - (w + step).toNat < n := by rw [natural]; omega
          have decrease : (K.toNat - (w + step).toNat) * (cost + 1) + (cost + 1) ≤
              n * (cost + 1) := by
            rw [← Nat.succ_mul]
            exact Nat.mul_le_mul_right _ (by omega)
          have tail := ih (K.toNat - (w + step).toNat) nextRank middle (nextCode.trans code)
            (w + step) nextCounter (by rw [natural]; omega) rfl (by omega)
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

theorem progBounded_countedDecExt (counter : MlS) (op : Cmp) (hop : op = .less ∨ op = .lower)
    (K step start : BitVec 64)
    (small : K.toNat + step.toNat < 2 ^ 63) (positive : 0 < step.toNat)
    (within : start.toNat ≤ K.toNat)
    {body tail : ProgHOL 64} {bCost tCost : Nat}
    (counted : CountedBodyExt counter step body bCost)
    (htail : ProgBounded tail tCost) :
    ProgBounded (.dec counter .one (.const start)
      (.seq (.while (.cmp op (.var .local counter) (.const K)) body) tail))
      (K.toNat * (bCost + 1) + tCost) := by
  intro F state code budget
  apply RunBounded.decConst
  let s0 := setVarHOLFinite counter (.val (.word start)) state
  have hs0_code : s0.code = originalRuntimeCode := code
  have hs0_ctr : s0.locals.lookup counter = some (.val (.word start)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hceil : (K.toNat - start.toNat) * (bCost + 1) ≤ K.toNat * (bCost + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have hloop := countedWhileExt_run counter op hop K step small positive counted
    (K.toNat - start.toNat) s0 hs0_code start hs0_ctr (by omega) rfl
    (by change (K.toNat - start.toNat) * (bCost + 1) ≤ state.clock; omega)
  have hloop' : RunBounded s0 (.while (.cmp op (.var .local counter) (.const K)) body)
      (K.toNat * (bCost + 1)) := by
    have h1 := hloop.1
    change state.clock ≤ _ + (K.toNat - start.toNat) * (bCost + 1) at h1
    exact ⟨by change state.clock ≤ _ + K.toNat * (bCost + 1); omega, hloop.2.1, hloop.2.2⟩
  exact RunBounded.seq hloop' (by change K.toNat * (bCost + 1) + tCost ≤ state.clock; omega)
    (fun next _ nextCode nextBudget => htail next (nextCode.trans hs0_code) nextBudget)

theorem progBounded_countedAssignExt (counter : MlS) (op : Cmp) (hop : op = .less ∨ op = .lower)
    (K step start : BitVec 64)
    (small : K.toNat + step.toNat < 2 ^ 63) (positive : 0 < step.toNat)
    (within : start.toNat ≤ K.toNat)
    {body tail : ProgHOL 64} {bCost tCost : Nat}
    (counted : CountedBodyExt counter step body bCost)
    (htail : ProgBounded tail tCost) :
    ProgBounded (.seq (.assign .local counter (.const start))
      (.seq (.while (.cmp op (.var .local counter) (.const K)) body) tail))
      (K.toNat * (bCost + 1) + tCost) := by
  intro F state code budget
  by_cases valid : isValidValueHOLExact state.toExact .local counter (.val (.word start)) = true
  · have asgnRun : evaluateHOLFiniteState state (.assign .local counter (.const start)) =
        (none, setKvarHOLFinite .local counter (.val (.word start)) state) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, valid]
    rw [evaluateHOLFiniteState_seq_line780, asgnRun]
    dsimp only
    let s0 := setKvarHOLFinite .local counter (.val (.word start)) state
    have hs0_code : s0.code = originalRuntimeCode := code
    have hs0_ctr : s0.locals.lookup counter = some (.val (.word start)) := by
      simp [s0, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hceil : (K.toNat - start.toNat) * (bCost + 1) ≤ K.toNat * (bCost + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have hloop := countedWhileExt_run counter op hop K step small positive counted
      (K.toNat - start.toNat) s0 hs0_code start hs0_ctr (by omega) rfl
      (by change (K.toNat - start.toNat) * (bCost + 1) ≤ state.clock; omega)
    have hloop' : RunBounded s0 (.while (.cmp op (.var .local counter) (.const K)) body)
        (K.toNat * (bCost + 1)) := by
      have h1 := hloop.1
      change state.clock ≤ _ + (K.toNat - start.toNat) * (bCost + 1) at h1
      exact ⟨by change state.clock ≤ _ + K.toNat * (bCost + 1); omega, hloop.2.1, hloop.2.2⟩
    exact RunBounded.seq hloop' (by change K.toNat * (bCost + 1) + tCost ≤ state.clock; omega)
      (fun next _ nextCode nextBudget => htail next (nextCode.trans hs0_code) nextBudget)
  · have asgnErr : evaluateHOLFiniteState state (.assign .local counter (.const start)) =
        (some .error, state) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, valid]
    rw [evaluateHOLFiniteState_seq_line780, asgnErr]
    simp

theorem downWhileExt_run (counter : MlS) (op : Cmp) (hop : op = .less ∨ op = .lower)
    {body : ProgHOL 64} {cost : Nat} (counted : DecBodyExt counter body cost) :
    ∀ n : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F),
      state.code = originalRuntimeCode →
      ∀ w : BitVec 64, state.locals.lookup counter = some (.val (.word w)) →
      (op = .less → w.toNat < 2 ^ 63) →
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
    intro F state code w atCounter signed within budget
    have condition : evalHOLFinite state
        (h := fun a => Classical.propDecidable (state.memaddrs a))
        (.cmp op (.const 0) (.var .local counter)) =
        some (.val (.word (if 0 < w.toNat then 1 else 0))) := by
      rw [evalHOLFinite_eq_toExact]
      rcases hop with rfl | rfl
      · have hw_lt := signed rfl
        simp only [evalHOLExact, atCounter, Compiler.Encoders.Asm.wordCmpHOL,
          holAsmSignedLess_small 0 w (by decide) hw_lt]
        by_cases lt : 0 < w.toNat <;> simp [lt]
      · simp only [evalHOLExact, atCounter, Compiler.Encoders.Asm.wordCmpHOL]
        by_cases lt : 0 < w.toNat <;> simp [lt, BitVec.lt_def]
    rw [evaluateHOLFiniteState_while_total, condition]
    by_cases lt : 0 < w.toNat
    · rw [if_pos lt]
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
          have one_toNat : (1 : BitVec 64).toNat = 1 := rfl
          have hle : (1 : BitVec 64) ≤ w := by rw [BitVec.le_def, one_toNat]; omega
          have natural : (w - 1).toNat = w.toNat - 1 := by
            rw [BitVec.toNat_sub_of_le hle, one_toNat]
          have hmul : (n - 1) * (cost + 1) + (cost + 1) = n * (cost + 1) := by
            have hsucc : n - 1 + 1 = n := by omega
            calc (n - 1) * (cost + 1) + (cost + 1) = (n - 1 + 1) * (cost + 1) := by
                  rw [Nat.add_mul, Nat.one_mul]
              _ = n * (cost + 1) := by rw [hsucc]
          have tail := ih (n - 1) (by omega) middle (nextCode.trans code) (w - 1) nextCounter
            (fun h => by have := signed h; omega) (by rw [natural]; omega) (by omega)
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

theorem progBounded_downWhileExt (counter : MlS) (op : Cmp) (hop : op = .less ∨ op = .lower)
    {body : ProgHOL 64} {cost : Nat} (counted : DecBodyExt counter body cost) :
    ProgBounded (.while (.cmp op (.const 0) (.var .local counter)) body)
      ((2 ^ 64 - 1) * (cost + 1)) := by
  intro F state code budget
  cases hctr : state.locals.lookup counter with
  | none =>
    rw [evaluateHOLFiniteState_while_total]
    have hguard : evalHOLFinite state
        (h := fun a => Classical.propDecidable (state.memaddrs a))
        (.cmp op (.const 0) (.var .local counter)) = none := by
      rw [evalHOLFinite_eq_toExact]
      simp [evalHOLExact, hctr]
    rw [hguard]
    simp
  | some v =>
    cases v with
    | val wl =>
      cases wl with
      | word w =>
        by_cases hsig : op = .less → w.toNat < 2 ^ 63
        · have hw_max : w.toNat ≤ 2 ^ 64 - 1 := by have := w.isLt; omega
          exact downWhileExt_run counter op hop counted (2 ^ 64 - 1) state code w hctr
            hsig hw_max budget
        · have hop_less : op = .less := by
            rcases hop with rfl | rfl
            · rfl
            · exfalso; exact hsig (fun h => by cases h)
          subst hop_less
          have hneg : ¬ w.toNat < 9223372036854775808 := fun h => hsig (fun _ => h)
          have hguard : evalHOLFinite state
              (h := fun a => Classical.propDecidable (state.memaddrs a))
              (.cmp .less (.const 0) (.var .local counter)) = some (.val (.word 0)) := by
            rw [evalHOLFinite_eq_toExact]
            simp [evalHOLExact, hctr, Compiler.Encoders.Asm.wordCmpHOL,
              Compiler.Encoders.Asm.holAsmSignedLess, hneg]
          rw [evaluateHOLFiniteState_while_total, hguard]
          simp
    | rStruct _ =>
      rw [evaluateHOLFiniteState_while_total]
      have hguard : evalHOLFinite state
          (h := fun a => Classical.propDecidable (state.memaddrs a))
          (.cmp op (.const 0) (.var .local counter)) = none := by
        rw [evalHOLFinite_eq_toExact]
        simp [evalHOLExact, hctr]
      rw [hguard]
      simp
    | nStruct _ _ =>
      rw [evaluateHOLFiniteState_while_total]
      have hguard : evalHOLFinite state
          (h := fun a => Classical.propDecidable (state.memaddrs a))
          (.cmp op (.const 0) (.var .local counter)) = none := by
        rw [evalHOLFinite_eq_toExact]
        simp [evalHOLExact, hctr]
      rw [hguard]
      simp

theorem variableLimitWhileExt_run (counter : MlS) (limitExp : ExpHOL 64) (op : Cmp)
    (hop : op = .less ∨ op = .lower) (K : BitVec 64)
    (signed : op = .less → K.toNat < 2 ^ 63)
    {body : ProgHOL 64} {cost : Nat}
    (hpure : isSimpleLimitExp limitExp = true)
    (hav : progAvoidsLimitExp body limitExp = true)
    (counted : CountedBodyExt counter 1 body cost) :
    ∀ n : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F),
      state.code = originalRuntimeCode →
      ∀ w : BitVec 64, state.locals.lookup counter = some (.val (.word w)) →
      @evalHOLExact 64 F _ state.toExact
        (fun a => Classical.propDecidable (state.memaddrs a)) limitExp = some (.val (.word K)) →
      w.toNat ≤ K.toNat →
      K.toNat - w.toNat = n → n * (cost + 1) ≤ state.clock →
      state.clock ≤ (evaluateHOLFiniteState state
          (.while (.cmp op (.var .local counter) limitExp) body)).2.clock + n * (cost + 1) ∧
        (evaluateHOLFiniteState state
          (.while (.cmp op (.var .local counter) limitExp) body)).2.clock ≤ state.clock ∧
        (evaluateHOLFiniteState state
          (.while (.cmp op (.var .local counter) limitExp) body)).1 ≠ some .timeOut := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro F state code w atCounter atLimit within distance budget
    have condition : evalHOLFinite state
        (h := fun a => Classical.propDecidable (state.memaddrs a))
        (.cmp op (.var .local counter) limitExp) =
        some (.val (.word (if w.toNat < K.toNat then 1 else 0))) := by
      rw [evalHOLFinite_eq_toExact]
      rcases hop with rfl | rfl
      · have small := signed rfl
        simp only [evalHOLExact, atCounter, atLimit, Compiler.Encoders.Asm.wordCmpHOL,
          holAsmSignedLess_small w K (by omega) small]
        by_cases lt : w.toNat < K.toNat <;> simp [lt]
      · simp only [evalHOLExact, atCounter, atLimit, Compiler.Encoders.Asm.wordCmpHOL]
        by_cases lt : w.toNat < K.toNat <;> simp [lt, BitVec.lt_def]
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
          have natural : (w + 1).toNat = w.toNat + 1 := by
            rw [BitVec.toNat_add_of_lt (by have bound := K.isLt; simp; omega)]
            rfl
          have nextRank : K.toNat - (w + 1).toNat < n := by rw [natural]; omega
          have nextLimit : @evalHOLExact 64 F _ middle.toExact
              (fun a => Classical.propDecidable (middle.memaddrs a)) limitExp =
              some (.val (.word K)) := by
            have heq := evalHOLExact_limit_eq middle state body limitExp hpure hav
              (fun nm hnm => by
                have hf := evaluate_avoidsLocal_flowing nm body hnm (decClockHOLFinite state)
                  (by rw [bodyRun]; exact Or.inl rfl)
                rw [bodyRun] at hf
                exact hf)
            exact heq.trans atLimit
          have decrease : (K.toNat - (w + 1).toNat) * (cost + 1) + (cost + 1) ≤
              n * (cost + 1) := by
            rw [← Nat.succ_mul]
            exact Nat.mul_le_mul_right _ (by omega)
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

theorem runBounded_variableLimitWhileExt_zero {F : Type}
    (counter : MlS) (limitExp : ExpHOL 64) (op : Cmp) (hop : op = .less ∨ op = .lower)
    {body : ProgHOL 64} {cost : Nat} (counted : CountedBodyExt counter 1 body cost)
    (hpure : isSimpleLimitExp limitExp = true)
    (hav : progAvoidsLimitExp body limitExp = true)
    (state : PanSemStateFiniteExact 64 F) (code : state.code = originalRuntimeCode)
    (atCounter : state.locals.lookup counter = some (.val (.word 0)))
    (budget : (2 ^ 64 - 1) * (cost + 1) ≤ state.clock) :
    RunBounded state (.while (.cmp op (.var .local counter) limitExp) body)
      ((2 ^ 64 - 1) * (cost + 1)) := by
  unfold RunBounded
  cases hlim : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) limitExp with
  | none =>
    rw [evaluateHOLFiniteState_while_total]
    have hg : evalHOLFinite state
        (h := fun a => Classical.propDecidable (state.memaddrs a))
        (.cmp op (.var .local counter) limitExp) = none := by
      rw [evalHOLFinite_eq_toExact]
      simp [evalHOLExact, atCounter, hlim]
    rw [hg]
    simp
  | some v =>
    cases v with
    | val wl =>
      cases wl with
      | word K =>
        by_cases signed : op = .less → K.toNat < 2 ^ 63
        · have ceiling : K.toNat * (cost + 1) ≤ (2 ^ 64 - 1) * (cost + 1) :=
            Nat.mul_le_mul_right _ (by have bound := K.isLt; omega)
          have hb := variableLimitWhileExt_run counter limitExp op hop K signed hpure hav counted
            K.toNat state code 0 atCounter hlim (by simp) (by simp) (by omega)
          exact ⟨by omega, hb.2.1, hb.2.2⟩
        · have hop_less : op = .less := by
            rcases hop with rfl | rfl
            · rfl
            · exfalso; exact signed (fun h => by cases h)
          subst hop_less
          have hneg : ¬ K.toNat < 9223372036854775808 := fun small => signed (fun _ => small)
          have hg : evalHOLFinite state
              (h := fun a => Classical.propDecidable (state.memaddrs a))
              (.cmp .less (.var .local counter) limitExp) = some (.val (.word 0)) := by
            rw [evalHOLFinite_eq_toExact]
            simp [evalHOLExact, atCounter, hlim, Compiler.Encoders.Asm.wordCmpHOL,
              Compiler.Encoders.Asm.holAsmSignedLess, hneg]
          rw [evaluateHOLFiniteState_while_total, hg]
          simp
    | rStruct _ =>
      rw [evaluateHOLFiniteState_while_total]
      have hg : evalHOLFinite state
          (h := fun a => Classical.propDecidable (state.memaddrs a))
          (.cmp op (.var .local counter) limitExp) = none := by
        rw [evalHOLFinite_eq_toExact]
        simp [evalHOLExact, atCounter, hlim]
      rw [hg]
      simp
    | nStruct _ _ =>
      rw [evaluateHOLFiniteState_while_total]
      have hg : evalHOLFinite state
          (h := fun a => Classical.propDecidable (state.memaddrs a))
          (.cmp op (.var .local counter) limitExp) = none := by
        rw [evalHOLFinite_eq_toExact]
        simp [evalHOLExact, atCounter, hlim]
      rw [hg]
      simp

theorem progBounded_variableDecWhileSeqExt
    (counter : MlS) (limitExp : ExpHOL 64) (op : Cmp) (hop : op = .less ∨ op = .lower)
    {body tail : ProgHOL 64} {bCost tCost : Nat}
    (counted : CountedBodyExt counter 1 body bCost)
    (hpure : isSimpleLimitExp limitExp = true)
    (hav : progAvoidsLimitExp body limitExp = true)
    (htail : ProgBounded tail tCost) :
    ProgBounded (.dec counter .one (.const 0)
      (.seq (.while (.cmp op (.var .local counter) limitExp) body) tail))
      ((2 ^ 64 - 1) * (bCost + 1) + tCost) := by
  intro F state code budget
  apply RunBounded.decConst
  let s0 := setVarHOLFinite counter (.val (.word 0)) state
  have hs0_code : s0.code = originalRuntimeCode := code
  have hs0_ctr : s0.locals.lookup counter = some (.val (.word 0)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hloop := runBounded_variableLimitWhileExt_zero counter limitExp op hop counted hpure hav
    s0 hs0_code hs0_ctr (by change (2 ^ 64 - 1) * (bCost + 1) ≤ state.clock; omega)
  exact RunBounded.seq hloop
    (by change (2 ^ 64 - 1) * (bCost + 1) + tCost ≤ state.clock; omega)
    (fun next _ nextCode nextBudget => htail next (nextCode.trans hs0_code) nextBudget)

theorem progBounded_variableDecWhileOnlyExt
    (counter : MlS) (limitExp : ExpHOL 64) (op : Cmp) (hop : op = .less ∨ op = .lower)
    {body : ProgHOL 64} {bCost : Nat}
    (counted : CountedBodyExt counter 1 body bCost)
    (hpure : isSimpleLimitExp limitExp = true)
    (hav : progAvoidsLimitExp body limitExp = true) :
    ProgBounded (.dec counter .one (.const 0)
      (.while (.cmp op (.var .local counter) limitExp) body))
      ((2 ^ 64 - 1) * (bCost + 1)) := by
  intro F state code budget
  apply RunBounded.decConst
  let s0 := setVarHOLFinite counter (.val (.word 0)) state
  have hs0_code : s0.code = originalRuntimeCode := code
  have hs0_ctr : s0.locals.lookup counter = some (.val (.word 0)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  exact runBounded_variableLimitWhileExt_zero counter limitExp op hop counted hpure hav
    s0 hs0_code hs0_ctr budget

theorem progBounded_countedDecOnlyExt (counter : MlS) (op : Cmp) (hop : op = .less ∨ op = .lower)
    (K step start : BitVec 64)
    (small : K.toNat + step.toNat < 2 ^ 63) (positive : 0 < step.toNat)
    (within : start.toNat ≤ K.toNat)
    {body : ProgHOL 64} {bCost : Nat}
    (counted : CountedBodyExt counter step body bCost) :
    ProgBounded (.dec counter .one (.const start)
      (.while (.cmp op (.var .local counter) (.const K)) body))
      (K.toNat * (bCost + 1)) := by
  intro F state code budget
  apply RunBounded.decConst
  let s0 := setVarHOLFinite counter (.val (.word start)) state
  have hs0_code : s0.code = originalRuntimeCode := code
  have hs0_ctr : s0.locals.lookup counter = some (.val (.word start)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hceil : (K.toNat - start.toNat) * (bCost + 1) ≤ K.toNat * (bCost + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have hloop := countedWhileExt_run counter op hop K step small positive counted
    (K.toNat - start.toNat) s0 hs0_code start hs0_ctr (by omega) rfl
    (by change (K.toNat - start.toNat) * (bCost + 1) ≤ state.clock; omega)
  have h1 := hloop.1
  change state.clock ≤ (s0.evaluateHOLFiniteState
      (.while (.cmp op (.var .local counter) (.const K)) body)).2.clock +
      (K.toNat - start.toNat) * (bCost + 1) at h1
  have h1' : state.clock ≤ (s0.evaluateHOLFiniteState
      (.while (.cmp op (.var .local counter) (.const K)) body)).2.clock + K.toNat * (bCost + 1) := by
    omega
  exact ⟨h1', hloop.2.1, hloop.2.2⟩

private theorem foldl_lookup_preserved {α β : Type} [DecidableEq α]
    (pairs : List (α × β)) (init : α → Option β) (target : α)
    (hnot : ∀ q ∈ pairs, q.1 ≠ target) :
    List.foldl (fun map entry current => if current = entry.1 then some entry.2 else map current)
      init pairs target = init target := by
  induction pairs generalizing init with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun q hq => hnot q (List.mem_cons_of_mem _ hq))]
    have hne : target ≠ hd.1 := Ne.symm (hnot hd (by simp))
    simp [hne]

private theorem zip_fst_ne {α β γ : Type}
    (names : List (α × γ)) (vals : List β) (target : α)
    (hnot : ∀ q ∈ names, q.1 ≠ target) :
    ∀ p ∈ (names.map Prod.fst).zip vals, p.1 ≠ target := by
  induction names generalizing vals with
  | nil => intro p hp; simp at hp
  | cons hd tl ih =>
    cases vals with
    | nil => intro p hp; simp at hp
    | cons v vs =>
      intro p hp
      simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hp
      rcases hp with rfl | hp'
      · exact hnot hd (by simp)
      · exact ih vs (fun q hq => hnot q (List.mem_cons_of_mem _ hq)) p hp'

theorem lookupCodeHOLFinite_param_at {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (fn : MlS) (pre : List (MlS × ShapeHOL)) (pk : MlS) (sk : ShapeHOL)
    (post : List (MlS × ShapeHOL)) (body : ProgHOL width) (rs : ShapeHOL)
    (hafter : ∀ q ∈ post, q.1 ≠ pk)
    (hlookup : code fn = some (pre ++ (pk, sk) :: post, body, rs))
    {vpre : List (ValueHOL width)} {vk : ValueHOL width} {vpost : List (ValueHOL width)}
    (hlen : vpre.length = pre.length)
    {foundBody : ProgHOL width} {locals : HolFiniteMapExact MlS (ValueHOL width)}
    {foundRs : ShapeHOL}
    (hfound : PanSemStateFiniteExact.lookupCodeHOLFinite code fn (vpre ++ vk :: vpost) =
      some (foundBody, locals, foundRs)) :
    foundBody = body ∧ locals.lookup pk = some vk := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
  split at hfound
  · cases hfound
  · rename_i exactBody exactLocals exactShape raw
    have heq := Option.some.inj hfound
    rcases Prod.mk.inj heq with ⟨rfl, hrest⟩
    rcases Prod.mk.inj hrest with ⟨rfl, _⟩
    unfold lookupCodeHOLExact at raw
    rw [hlookup] at raw
    dsimp only at raw
    split at raw
    · have rawEq := Option.some.inj raw
      rcases Prod.mk.inj rawEq with ⟨rfl, hrest2⟩
      rcases Prod.mk.inj hrest2 with ⟨rfl, _⟩
      refine ⟨rfl, ?_⟩
      dsimp only
      have hzip : (List.map Prod.fst (pre ++ (pk, sk) :: post)).zip (vpre ++ vk :: vpost) =
          (pre.map Prod.fst).zip vpre ++ (pk, vk) :: (post.map Prod.fst).zip vpost := by
        rw [List.map_append, List.map_cons, List.zip_append (by simp [hlen]), List.zip_cons_cons]
      rw [hzip, List.foldl_append, List.foldl_cons]
      rw [foldl_lookup_preserved ((post.map Prod.fst).zip vpost) _ pk
        (zip_fst_ne post vpost pk hafter)]
      simp
    · cases raw

theorem evalListHOLFinite_split {F : Type}
    (state : PanSemStateFiniteExact 64 F) (pre : List (ExpHOL 64)) (ek : ExpHOL 64)
    (post : List (ExpHOL 64)) {values : List (ValueHOL 64)}
    (hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      (pre ++ ek :: post) = some values) :
    ∃ vpre vk vpost,
      vpre.length = pre.length ∧
      evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) ek = some vk ∧
      values = vpre ++ vk :: vpost := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  rw [evalHOLFinite_eq_toExact]
  induction pre generalizing values with
  | nil =>
    simp only [List.nil_append, evalListHOLExact] at hargs
    rcases hek : @evalHOLExact 64 F _ state.toExact
        (fun a => Classical.propDecidable (state.memaddrs a)) ek with _ | vk
    · rw [hek] at hargs; cases hargs
    · rw [hek] at hargs
      rcases hpost : @evalListHOLExact 64 F _ state.toExact
          (fun a => Classical.propDecidable (state.memaddrs a)) post with _ | vpost
      · rw [hpost] at hargs; cases hargs
      · rw [hpost] at hargs
        cases hargs
        exact ⟨[], vk, vpost, rfl, rfl, rfl⟩
  | cons e es ih =>
    simp only [List.cons_append, evalListHOLExact] at hargs
    rcases he : @evalHOLExact 64 F _ state.toExact
        (fun a => Classical.propDecidable (state.memaddrs a)) e with _ | ve
    · rw [he] at hargs; cases hargs
    · rw [he] at hargs
      rcases hes : @evalListHOLExact 64 F _ state.toExact
          (fun a => Classical.propDecidable (state.memaddrs a)) (es ++ ek :: post) with _ | vtail
      · rw [hes] at hargs; cases hargs
      · rw [hes] at hargs
        cases hargs
        obtain ⟨vpre, vk, vpost, hlen, heval, rfl⟩ := ih hes
        exact ⟨ve :: vpre, vk, vpost, by simp [hlen], heval, rfl⟩

theorem calleeBodyBounded_of_argAt
    (fn : MlS) (pre : List (MlS × ShapeHOL)) (pk : MlS) (sk : ShapeHOL)
    (post : List (MlS × ShapeHOL)) (body : ProgHOL 64) (rs : ShapeHOL)
    (hafter : ∀ q ∈ post, q.1 ≠ pk)
    (hlookup : originalRuntimeCode.lookup fn = some (pre ++ (pk, sk) :: post, body, rs))
    (epre : List (ExpHOL 64)) (ek : ExpHOL 64) (epost : List (ExpHOL 64))
    (hlen : epre.length = pre.length)
    (P : ValueHOL 64 → Prop) (bodyCost : Nat)
    (hevalP : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (vk : ValueHOL 64),
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) ek = some vk → P vk)
    (hbodyRun : ∀ {F : Type} (entry : PanSemStateFiniteExact 64 F) (vk : ValueHOL 64),
      P vk → entry.code = originalRuntimeCode → entry.locals.lookup pk = some vk →
      bodyCost ≤ entry.clock → RunBounded entry body bodyCost) :
    CalleeBodyBounded fn (epre ++ ek :: epost) (bodyCost + 1) := by
  refine ⟨by omega, ?_⟩
  intro F state hcode hbudget values foundBody callee retShape hargs hfound
  obtain ⟨vpre, vk, vpost, hvlen, hek, rfl⟩ := evalListHOLFinite_split state epre ek epost hargs
  rw [hcode] at hfound
  obtain ⟨rfl, hat⟩ := lookupCodeHOLFinite_param_at originalRuntimeCode.lookup
    fn pre pk sk post body rs hafter hlookup (hvlen.trans hlen) hfound
  have hentry_code : (callEntryStateHOLFinite state callee).code = originalRuntimeCode := hcode
  have hentry_loc : (callEntryStateHOLFinite state callee).locals.lookup pk = some vk := hat
  simpa using hbodyRun (callEntryStateHOLFinite state callee) vk (hevalP state vk hek)
    hentry_code hentry_loc (by change bodyCost ≤ state.clock - 1; omega)

/-! ## Section 3: Special Loop Helpers (`rlp_be_len`, `fq12_mul`, `fq12_sqr`) -/

private theorem lsr8_steps_zero :
    ∀ k : Nat, ∀ w : BitVec 64, w.toNat < 2 ^ (8 * k) →
      ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (nVal : BitVec 64),
        state.locals.lookup (ofString "v") = some (.val (.word w)) →
        state.locals.lookup (ofString "n") = some (.val (.word nVal)) →
        nVal.toNat + k ≤ 8 →
        k ≤ state.clock →
        state.clock ≤ (evaluateHOLFiniteState state
            (.while (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64))
              (.seq
                (.assign .local (ofString "v")
                  (.shift .lsr (.var .local (ofString "v")) (.const 8#64)))
                (.assign .local (ofString "n")
                  (.op .add [.var .local (ofString "n"), .const 1#64]))))).2.clock + k ∧
          (evaluateHOLFiniteState state
            (.while (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64))
              (.seq
                (.assign .local (ofString "v")
                  (.shift .lsr (.var .local (ofString "v")) (.const 8#64)))
                (.assign .local (ofString "n")
                  (.op .add [.var .local (ofString "n"), .const 1#64]))))).2.clock ≤ state.clock ∧
          (evaluateHOLFiniteState state
            (.while (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64))
              (.seq
                (.assign .local (ofString "v")
                  (.shift .lsr (.var .local (ofString "v")) (.const 8#64)))
                (.assign .local (ofString "n")
                  (.op .add [.var .local (ofString "n"), .const 1#64]))))).1 = none ∧
          ∃ nOut : BitVec 64,
            nOut.toNat ≤ 8 ∧
            (evaluateHOLFiniteState state
              (.while (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64))
                (.seq
                  (.assign .local (ofString "v")
                    (.shift .lsr (.var .local (ofString "v")) (.const 8#64)))
                  (.assign .local (ofString "n")
                    (.op .add [.var .local (ofString "n"), .const 1#64]))))).2.locals.lookup
              (ofString "n") = some (.val (.word nOut)) := by
  intro k
  induction k with
  | zero =>
    intro w hw F state nVal hv hn hn_le hclk
    have hw0 : w = 0#64 := by apply BitVec.eq_of_toNat_eq; simp at hw ⊢; omega
    subst hw0
    rw [evaluateHOLFiniteState_while_total]
    have hg : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
        (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64)) = some (.val (.word 0#64)) := by
      rw [evalHOLFinite_eq_toExact]
      simp [evalHOLExact, hv, Compiler.Encoders.Asm.wordCmpHOL]
    rw [hg]
    have hzero : ¬ ((0#64 : BitVec 64) ≠ 0) := by decide
    dsimp only
    rw [if_neg hzero]
    dsimp only
    exact ⟨by omega, le_refl _, rfl, nVal, by omega, hn⟩
  | succ k ih =>
    intro w hw F state nVal hv hn hn_le hclk
    by_cases hwz : w = 0#64
    · subst hwz
      rw [evaluateHOLFiniteState_while_total]
      have hg : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
          (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64)) =
          some (.val (.word 0#64)) := by
        rw [evalHOLFinite_eq_toExact]
        simp [evalHOLExact, hv, Compiler.Encoders.Asm.wordCmpHOL]
      rw [hg]
      have hzero : ¬ ((0#64 : BitVec 64) ≠ 0) := by decide
      dsimp only
      rw [if_neg hzero]
      dsimp only
      exact ⟨by omega, le_refl _, rfl, nVal, by omega, hn⟩
    · rw [evaluateHOLFiniteState_while_total]
      have hg : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
          (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64)) =
          some (.val (.word 1#64)) := by
        rw [evalHOLFinite_eq_toExact]
        simp [evalHOLExact, hv, Compiler.Encoders.Asm.wordCmpHOL, hwz]
      rw [hg]
      simp only [show (1#64 : BitVec 64) ≠ 0 by decide, ↓reduceIte, ne_eq, not_false_eq_true]
      have hnz : state.clock ≠ 0 := by omega
      rw [if_neg hnz, fixClockHOLFinite_evaluateState]
      let sDec := decClockHOLFinite state
      have hasgn1 : evaluateHOLFiniteState sDec
          (.assign .local (ofString "v") (.shift .lsr (.var .local (ofString "v")) (.const 8#64))) =
          (none, setVarHOLFinite (ofString "v") (.val (.word (w >>> 8))) sDec) := by
        simp [evaluateHOLFiniteState_assign, evalHOLExact, sDec, decClockHOLFinite, hv,
          wordShiftHOL, lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
          shapeOfHOLExact, shapeEqHOL]
      let s1 := setVarHOLFinite (ofString "v") (.val (.word (w >>> 8))) sDec
      have hne_vn : ofString "v" ≠ ofString "n" := by decide
      have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word nVal)) := by
        simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          hne_vn, sDec, decClockHOLFinite, hn]
      have hasgn2 : evaluateHOLFiniteState s1
          (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const 1#64])) =
          (none, setVarHOLFinite (ofString "n") (.val (.word (nVal + 1#64))) s1) := by
        simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hs1_n,
          wordOpHOL, wordOp, valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact,
          setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
      rw [evaluateHOLFiniteState_seq_line780, hasgn1]
      dsimp only
      rw [hasgn2]
      dsimp only
      let s2 := setVarHOLFinite (ofString "n") (.val (.word (nVal + 1#64))) s1
      have hs2_v : s2.locals.lookup (ofString "v") = some (.val (.word (w >>> 8))) := by
        simp [s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne_vn]
      have hs2_n : s2.locals.lookup (ofString "n") = some (.val (.word (nVal + 1#64))) := by
        simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hshift : (w >>> 8).toNat < 2 ^ (8 * k) := by
        have h1 : (w >>> 8).toNat = w.toNat / 2 ^ 8 := by
          simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
        have hpow : 2 ^ (8 * (k + 1)) = 2 ^ 8 * 2 ^ (8 * k) := by
          rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]
        rw [h1]
        rw [hpow] at hw
        exact Nat.div_lt_of_lt_mul hw
      have hn_add : (nVal + 1#64).toNat = nVal.toNat + 1 := by
        rw [BitVec.toNat_add_of_lt (by simp; omega)]
        rfl
      have hrec := ih (w >>> 8) hshift s2 (nVal + 1#64) hs2_v hs2_n (by omega)
        (by change k ≤ state.clock - 1; omega)
      rcases htail : evaluateHOLFiniteState s2 _ with ⟨r, post⟩
      rw [htail] at hrec
      dsimp only at hrec ⊢
      obtain ⟨c1, c2, rfl, nOut, hnOut, hloc⟩ := hrec
      change state.clock - 1 ≤ post.clock + k at c1
      change post.clock ≤ state.clock - 1 at c2
      exact ⟨by omega, by omega, rfl, nOut, hnOut, hloc⟩

/-! ## Section 4: Memory & Small-Argument `CalleeBodyBounded` Primitives -/

private theorem runBounded_stride32_8_1 {F : Type}
    (state : PanSemStateFiniteExact 64 F) (K : BitVec 64)
    (hsmall : K.toNat + 32 < 2 ^ 64)
    {b32 b8a b8b b1 : ProgHOL 64}
    (hb32 : CountedBody (ofString "i") 32 b32 0)
    (hb32_lim : avoidsLocal (ofString "n") b32 = true)
    (hb32_nb : noTopBreak b32 = true)
    (hb8a : CountedBody (ofString "i") 8 b8a 0)
    (hb8a_lim : avoidsLocal (ofString "n") b8a = true)
    (hb8a_nb : noTopBreak b8a = true)
    (hb8b : CountedBody (ofString "i") 8 b8b 0)
    (hb8b_lim : avoidsLocal (ofString "n") b8b = true)
    (hb8b_nb : noTopBreak b8b = true)
    (hb1 : CountedBody (ofString "i") 1 b1 0)
    (hb1_lim : avoidsLocal (ofString "n") b1 = true)
    {pre tail : ProgHOL 64}
    (hpre : ProgBounded pre 0)
    (hpre_i : avoidsLocal (ofString "i") pre = true)
    (hpre_n : avoidsLocal (ofString "n") pre = true)
    (htail : ProgBounded tail 0)
    (condAlign : ExpHOL 64)
    (hcode : state.code = originalRuntimeCode)
    (atN : state.locals.lookup (ofString "n") = some (.val (.word K)))
    (hbudget : K.toNat / 8 + 7 ≤ state.clock) :
    RunBounded state
      (.dec (ofString "i") .one (.const 0)
        (.seq
          (.ite condAlign
            (.seq pre
              (.seq
                (.while (.cmp .notLower (.var .local (ofString "n"))
                  (.op .add [.var .local (ofString "i"), .const 32])) b32)
                (.while (.cmp .notLower (.var .local (ofString "n"))
                  (.op .add [.var .local (ofString "i"), .const 8])) b8a)))
            .skip)
          (.seq
            (.while (.cmp .notLower (.var .local (ofString "n"))
              (.op .add [.var .local (ofString "i"), .const 8])) b8b)
            (.seq
              (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) b1)
              tail))))
      (K.toNat / 8 + 7) := by
  apply RunBounded.decConst
  let s0 := setVarHOLFinite (ofString "i") (.val (.word 0)) state
  have hs0_code : s0.code = originalRuntimeCode := hcode
  have hs0_i : s0.locals.lookup (ofString "i") = some (.val (.word 0)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs0_n : s0.locals.lookup (ofString "n") = some (.val (.word K)) := by
    have hne : ofString "i" ≠ ofString "n" := by decide
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, atN]
  have hs0_clk : s0.clock = state.clock := rfl
  let firstBranch :=
    ProgHOL.ite condAlign
      (.seq pre
        (.seq
          (.while (.cmp .notLower (.var .local (ofString "n"))
            (.op .add [.var .local (ofString "i"), .const 32])) b32)
          (.while (.cmp .notLower (.var .local (ofString "n"))
            (.op .add [.var .local (ofString "i"), .const 8])) b8a)))
      .skip
  have hfirst :
      ∃ c1 : Nat,
        s0.clock ≤ (evaluateHOLFiniteState s0 firstBranch).2.clock + c1 ∧
        (evaluateHOLFiniteState s0 firstBranch).2.clock ≤ s0.clock ∧
        (evaluateHOLFiniteState s0 firstBranch).1 ≠ some .timeOut ∧
        ((evaluateHOLFiniteState s0 firstBranch).1 ≠ none → c1 ≤ K.toNat / 8) ∧
        ((evaluateHOLFiniteState s0 firstBranch).1 = none →
          ∃ w1 : BitVec 64,
            (evaluateHOLFiniteState s0 firstBranch).2.locals.lookup (ofString "i") =
              some (.val (.word w1)) ∧
            (evaluateHOLFiniteState s0 firstBranch).2.locals.lookup (ofString "n") =
              some (.val (.word K)) ∧
            w1.toNat ≤ K.toNat ∧
            c1 + (K.toNat - w1.toNat) / 8 ≤ K.toNat / 8 ∧
            (evaluateHOLFiniteState s0 firstBranch).2.code = originalRuntimeCode) := by
    dsimp only [firstBranch]
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · rw [evaluateHOLFiniteState_skip]
        dsimp only
        refine ⟨0, by omega, le_refl _, by simp, fun h => absurd rfl h, fun _ => ?_⟩
        exact ⟨0, hs0_i, hs0_n, by simp, by simp, hs0_code⟩
      · rw [evaluateHOLFiniteState_seq_line780]
        have hpre_run := hpre s0 hs0_code (by omega)
        have hpre_fi := evaluate_avoidsLocal_flowing (ofString "i") pre hpre_i s0
        have hpre_fn := evaluate_avoidsLocal_flowing (ofString "n") pre hpre_n s0
        have hpre_meta := PanRunBounded.evaluateHOLFiniteState_metadata s0 pre
        rcases hp : evaluateHOLFiniteState s0 pre with ⟨rpre, s1⟩
        rw [hp] at hpre_run hpre_fi hpre_fn hpre_meta
        dsimp only at hpre_run hpre_fi hpre_fn hpre_meta ⊢
        cases rpre with
        | some r =>
          dsimp only
          exact ⟨0, hpre_run.1, hpre_run.2.1, hpre_run.2.2, fun _ => by omega, fun h => by simp at h⟩
        | none =>
          dsimp only
          have hs1_i : s1.locals.lookup (ofString "i") = some (.val (.word 0)) :=
            (hpre_fi (Or.inl rfl)).trans hs0_i
          have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word K)) :=
            (hpre_fn (Or.inl rfl)).trans hs0_n
          have hs1_code : s1.code = originalRuntimeCode := hpre_meta.1.trans hs0_code
          rw [evaluateHOLFiniteState_seq_line780]
          have h32 := notLowerStrideWhile_run (ofString "i") (ofString "n") K 32
            (by simpa using hsmall) (by decide) hb32 hb32_lim hb32_nb
            (K.toNat / 32) s1 hs1_code 0 hs1_i hs1_n (by simp) (by simp)
            (by have := hpre_run.1; simp; omega)
          rcases hr32 : evaluateHOLFiniteState s1
              (.while (.cmp .notLower (.var .local (ofString "n"))
                (.op .add [.var .local (ofString "i"), .const 32])) b32)
              with ⟨res32, s2⟩
          rw [hr32] at h32
          dsimp only at h32 ⊢
          cases res32 with
          | some r =>
            dsimp only
            exact ⟨K.toNat / 32, by omega, by omega, h32.2.2.1, fun _ => by omega,
              fun h => by simp at h⟩
          | none =>
            dsimp only
            obtain ⟨w32, hw32_i, hw32_n, _, hw32_le, hw32_rem, hs2_code⟩ := h32.2.2.2 rfl
            have hw32_lt32 : K.toNat - w32.toNat < 32 := by
              change K.toNat < w32.toNat + 32 at hw32_rem
              omega
            have h8a := notLowerStrideWhile_run (ofString "i") (ofString "n") K 8
              (by change K.toNat + 8 < 2 ^ 64; omega) (by decide) hb8a hb8a_lim hb8a_nb
              ((K.toNat - w32.toNat) / 8) s2 (hs2_code.trans hs1_code) w32 hw32_i hw32_n hw32_le
              rfl (by
                have := hpre_run.1
                have := h32.1
                simp only [Nat.zero_add, Nat.mul_one] at *
                omega)
            rcases hr8a : evaluateHOLFiniteState s2
                (.while (.cmp .notLower (.var .local (ofString "n"))
                  (.op .add [.var .local (ofString "i"), .const 8])) b8a)
                with ⟨res8a, s3⟩
            rw [hr8a] at h8a
            dsimp only at h8a ⊢
            refine ⟨K.toNat / 32 + (K.toNat - w32.toNat) / 8,
              by simp only [Nat.zero_add, Nat.mul_one] at h32 h8a; omega,
              by omega, h8a.2.2.1, fun _ => by omega, fun hnorm => ?_⟩
            obtain ⟨w8a, hw8a_i, hw8a_n, _, hw8a_le, hw8a_rem, hs3_code⟩ := h8a.2.2.2 hnorm
            have hw8a_lt8 : K.toNat - w8a.toNat < 8 := by
              change K.toNat < w8a.toNat + 8 at hw8a_rem
              omega
            exact ⟨w8a, hw8a_i, hw8a_n, hw8a_le, by omega,
              hs3_code.trans (hs2_code.trans hs1_code)⟩
    · refine ⟨0, by simp, by simp, by simp, fun _ => by omega, fun h => by simp at h⟩
  obtain ⟨c1, hc1_spent, hc1_kept, hc1_safe, hc1_abrupt, hc1_norm⟩ := hfirst
  change RunBounded s0 _ _
  unfold RunBounded
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hf : evaluateHOLFiniteState s0 firstBranch with ⟨rf, sf⟩
  rw [hf] at hc1_spent hc1_kept hc1_safe hc1_abrupt hc1_norm
  dsimp only at hc1_spent hc1_kept hc1_safe hc1_abrupt hc1_norm ⊢
  cases rf with
  | some r =>
    dsimp only
    have hc1_bound := hc1_abrupt (by simp)
    exact ⟨by omega, hc1_kept, hc1_safe⟩
  | none =>
    dsimp only
    obtain ⟨w1, hsf_i, hsf_n, hw1_le, hc1_rem, hsf_code⟩ := hc1_norm rfl
    rw [evaluateHOLFiniteState_seq_line780]
    have h8b := notLowerStrideWhile_run (ofString "i") (ofString "n") K 8
      (by change K.toNat + 8 < 2 ^ 64; omega) (by decide) hb8b hb8b_lim hb8b_nb
      ((K.toNat - w1.toNat) / 8) sf hsf_code w1 hsf_i hsf_n hw1_le rfl
      (by simp only [Nat.zero_add, Nat.mul_one]; omega)
    rcases hr8b : evaluateHOLFiniteState sf
        (.while (.cmp .notLower (.var .local (ofString "n"))
          (.op .add [.var .local (ofString "i"), .const 8])) b8b)
        with ⟨res8b, sg⟩
    rw [hr8b] at h8b
    dsimp only at h8b ⊢
    cases res8b with
    | some r =>
      dsimp only
      exact ⟨by simp only [Nat.zero_add, Nat.mul_one] at h8b; omega, by omega, h8b.2.2.1⟩
    | none =>
      dsimp only
      obtain ⟨w2, hsg_i, hsg_n, _, hw2_le, hw2_rem, hsg_code⟩ := h8b.2.2.2 rfl
      rw [evaluateHOLFiniteState_seq_line780]
      have hrem7 : K.toNat - w2.toNat ≤ 7 := by
        change K.toNat < w2.toNat + 8 at hw2_rem
        omega
      have h1 := variableCountedWhile_run (ofString "i") (ofString "n") .lower (Or.inr rfl) K
        (fun h => by cases h) hb1 hb1_lim (K.toNat - w2.toNat) sg (hsg_code.trans hsf_code)
        w2 hsg_i hsg_n hw2_le rfl
        (by simp only [Nat.zero_add, Nat.mul_one] at h8b ⊢; omega)
      have h1_meta := PanRunBounded.evaluateHOLFiniteState_metadata sg
        (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) b1)
      rcases hr1 : evaluateHOLFiniteState sg
          (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) b1)
          with ⟨res1, sh⟩
      rw [hr1] at h1 h1_meta
      dsimp only at h1 h1_meta ⊢
      cases res1 with
      | some r =>
        dsimp only
        exact ⟨by simp only [Nat.zero_add, Nat.mul_one] at h8b h1; omega, by omega, h1.2.2⟩
      | none =>
        dsimp only
        have ht := htail sh (h1_meta.1.trans (hsg_code.trans hsf_code)) (by omega)
        exact ⟨by simp only [Nat.zero_add, Nat.mul_one] at h8b h1 ht; omega, by omega, ht.2.2⟩

private theorem runBounded_stride32_8_1_noPre {F : Type}
    (state : PanSemStateFiniteExact 64 F) (K : BitVec 64)
    (hsmall : K.toNat + 32 < 2 ^ 64)
    {b32 b8a b8b b1 : ProgHOL 64}
    (hb32 : CountedBody (ofString "i") 32 b32 0)
    (hb32_lim : avoidsLocal (ofString "n") b32 = true)
    (hb32_nb : noTopBreak b32 = true)
    (hb8a : CountedBody (ofString "i") 8 b8a 0)
    (hb8a_lim : avoidsLocal (ofString "n") b8a = true)
    (hb8a_nb : noTopBreak b8a = true)
    (hb8b : CountedBody (ofString "i") 8 b8b 0)
    (hb8b_lim : avoidsLocal (ofString "n") b8b = true)
    (hb8b_nb : noTopBreak b8b = true)
    (hb1 : CountedBody (ofString "i") 1 b1 0)
    (hb1_lim : avoidsLocal (ofString "n") b1 = true)
    {tail : ProgHOL 64} (htail : ProgBounded tail 0)
    (condAlign : ExpHOL 64)
    (hcode : state.code = originalRuntimeCode)
    (atN : state.locals.lookup (ofString "n") = some (.val (.word K)))
    (hbudget : K.toNat / 8 + 7 ≤ state.clock) :
    RunBounded state
      (.dec (ofString "i") .one (.const 0)
        (.seq
          (.ite condAlign
            (.seq
              (.while (.cmp .notLower (.var .local (ofString "n"))
                (.op .add [.var .local (ofString "i"), .const 32])) b32)
              (.while (.cmp .notLower (.var .local (ofString "n"))
                (.op .add [.var .local (ofString "i"), .const 8])) b8a))
            .skip)
          (.seq
            (.while (.cmp .notLower (.var .local (ofString "n"))
              (.op .add [.var .local (ofString "i"), .const 8])) b8b)
            (.seq
              (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) b1)
              tail))))
      (K.toNat / 8 + 7) := by
  have heq :
      ∀ (s : PanSemStateFiniteExact 64 F) (p : ProgHOL 64),
        evaluateHOLFiniteState s (.seq .skip p) = evaluateHOLFiniteState s p := by
    intro s p
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_skip]
  have hite :
      ∀ (s : PanSemStateFiniteExact 64 F) (p : ProgHOL 64),
        evaluateHOLFiniteState s (.ite condAlign (.seq .skip p) .skip) =
          evaluateHOLFiniteState s (.ite condAlign p .skip) := by
    intro s p
    rw [evaluateHOLFiniteState_ite, evaluateHOLFiniteState_ite]
    split
    · split
      · rfl
      · exact heq s p
    · rfl
  have h := runBounded_stride32_8_1 state K hsmall
    hb32 hb32_lim hb32_nb hb8a hb8a_lim hb8a_nb hb8b hb8b_lim hb8b_nb hb1 hb1_lim
    (ProgBounded.straight .skip rfl) rfl rfl htail condAlign hcode atN hbudget
  unfold RunBounded at h ⊢
  simp only [evaluateHOLFiniteState_dec_total, evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true,
    evaluateHOLFiniteState_seq_line780, hite] at h ⊢
  exact h

theorem runBounded_memzero_le {F : Type}
    (state : PanSemStateFiniteExact 64 F) (K : BitVec 64) (M : Nat)
    (hle : K.toNat ≤ M) (hsmall : M + 32 < 2 ^ 64)
    (hcode : state.code = originalRuntimeCode)
    (atN : state.locals.lookup (ofString "n") = some (.val (.word K)))
    (hbudget : M / 8 + 7 ≤ state.clock) :
    RunBounded state (sourceFnBody Guest.Software.guestFn_memzero) (M / 8 + 7) := by
  have hk_le : K.toNat / 8 + 7 ≤ M / 8 + 7 := by omega
  refine RunBounded.weaken ?_ hk_le
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_memzero,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact runBounded_stride32_8_1_noPre state K (by omega)
    (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
      (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
        (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
          (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr))))
    rfl rfl
    (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr)
    rfl rfl
    (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
      (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
        (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
          (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
            (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
              (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
                (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
                  (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr))))))))
    rfl rfl
    (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr)
    rfl
    (ProgBounded.straight _ rfl) _ hcode atN (by omega)

theorem runBounded_memcpy_le {F : Type}
    (state : PanSemStateFiniteExact 64 F) (K : BitVec 64) (M : Nat)
    (hle : K.toNat ≤ M) (hsmall : M + 32 < 2 ^ 64)
    (hcode : state.code = originalRuntimeCode)
    (atN : state.locals.lookup (ofString "n") = some (.val (.word K)))
    (hbudget : M / 8 + 7 ≤ state.clock) :
    RunBounded state (sourceFnBody Guest.Software.guestFn_memcpy) (M / 8 + 7) := by
  have hk_le : K.toNat / 8 + 7 ≤ M / 8 + 7 := by omega
  refine RunBounded.weaken ?_ hk_le
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_memcpy,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact runBounded_stride32_8_1_noPre state K (by omega)
    (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
      (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
        (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
          (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr))))
    rfl rfl
    (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr)
    rfl rfl
    (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
      (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
        (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
          (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
            (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
              (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
                (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
                  (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr))))))))
    rfl rfl
    (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr)
    rfl
    (ProgBounded.straight _ rfl) _ hcode atN (by omega)

private theorem evaluate_seq_reassoc3' {F : Type}
    (s : PanSemStateFiniteExact 64 F) (p1 p2 p3 rest : ProgHOL 64) :
    evaluateHOLFiniteState s (.seq p1 (.seq p2 (.seq p3 rest))) =
      evaluateHOLFiniteState s (.seq (.seq p1 (.seq p2 p3)) rest) := by
  simp only [evaluateHOLFiniteState_seq_line780]
  rcases evaluateHOLFiniteState s p1 with ⟨_ | _, s1⟩ <;> dsimp only
  · rcases evaluateHOLFiniteState s1 p2 with ⟨_ | _, s2⟩ <;> rfl

private theorem runBounded_seq_ite_reassoc3' {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (cost : Nat)
    (cond : ExpHOL 64) (p1 p2 p3 w32 w8 tailProg : ProgHOL 64)
    (hh : RunBounded s0 (.seq (.ite cond (.seq (.seq p1 (.seq p2 p3)) (.seq w32 w8)) .skip) tailProg) cost) :
    RunBounded s0 (.seq (.ite cond (.seq p1 (.seq p2 (.seq p3 (.seq w32 w8)))) .skip) tailProg) cost := by
  have heq :
      evaluateHOLFiniteState s0 (.ite cond (.seq p1 (.seq p2 (.seq p3 (.seq w32 w8)))) .skip) =
      evaluateHOLFiniteState s0 (.ite cond (.seq (.seq p1 (.seq p2 p3)) (.seq w32 w8)) .skip) := by
    rw [evaluateHOLFiniteState_ite, evaluateHOLFiniteState_ite]
    split
    · split
      · rfl
      · exact evaluate_seq_reassoc3' s0 p1 p2 p3 (.seq w32 w8)
    · rfl
  unfold RunBounded at hh ⊢
  rw [evaluateHOLFiniteState_seq_line780, heq]
  rw [evaluateHOLFiniteState_seq_line780] at hh
  exact hh

private theorem runBounded_decConst_inv' {F : Type}
    (state : PanSemStateFiniteExact 64 F) (name : MlS) (k : BitVec 64) {body : ProgHOL 64} {cost : Nat}
    (h : RunBounded state (.dec name .one (.const k) body) cost) :
    RunBounded (setVarHOLFinite name (.val (.word k)) state) body cost := by
  unfold RunBounded at h ⊢
  rw [evaluateHOLFiniteState_dec_total] at h
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true] at h
  exact h

theorem runBounded_memeq_le {F : Type}
    (state : PanSemStateFiniteExact 64 F) (K : BitVec 64) (M : Nat)
    (hle : K.toNat ≤ M) (hsmall : M + 32 < 2 ^ 64)
    (hcode : state.code = originalRuntimeCode)
    (atN : state.locals.lookup (ofString "n") = some (.val (.word K)))
    (hbudget : M / 8 + 7 ≤ state.clock) :
    RunBounded state (sourceFnBody Guest.Software.guestFn_memeq) (M / 8 + 7) := by
  have hk_le : K.toNat / 8 + 7 ≤ M / 8 + 7 := by omega
  refine RunBounded.weaken ?_ hk_le
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_memeq,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply RunBounded.decConst
  apply runBounded_seq_ite_reassoc3'
  exact runBounded_decConst_inv' state (ofString "i") 0
    (runBounded_stride32_8_1 state K (by omega)
      (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
        (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
          (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
            (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr))))
      rfl rfl
      (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr)
      rfl rfl
      (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
        (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
          (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
            (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
              (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
                (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
                  (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
                    (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr))))))))
      rfl rfl
      (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr)
      rfl
      (ProgBounded.straight _ rfl) rfl rfl (ProgBounded.straight _ rfl) _ hcode atN (by omega))

theorem runBounded_is_zero_bytes_le {F : Type}
    (state : PanSemStateFiniteExact 64 F) (K : BitVec 64) (M : Nat)
    (hle : K.toNat ≤ M)
    (hcode : state.code = originalRuntimeCode)
    (atN : state.locals.lookup (ofString "n") = some (.val (.word K)))
    (hbudget : M ≤ state.clock) :
    RunBounded state (sourceFnBody Guest.Software.guestFn_is_zero_bytes) M := by
  refine RunBounded.weaken ?_ hle
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_is_zero_bytes,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply RunBounded.decConst
  let s0 := setVarHOLFinite (ofString "i") (.val (.word 0)) state
  have hs0_code : s0.code = originalRuntimeCode := hcode
  have hs0_i : s0.locals.lookup (ofString "i") = some (.val (.word 0)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs0_n : s0.locals.lookup (ofString "n") = some (.val (.word K)) := by
    have hne : ofString "i" ≠ ofString "n" := by decide
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, atN]
  have hbody :
      CountedBody (ofString "i") 1
        (.seq
          (.ite (.cmp .notEqual (.loadByte (.op .add [.var .local (ofString "p"), .var .local (ofString "i")])) (.const 0))
            (.return (.const 0))
            .skip)
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))) 0 :=
    CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr
  have hloop := variableCountedWhile_run (ofString "i") (ofString "n") .lower (Or.inr rfl) K
    (fun h => by cases h) hbody rfl K.toNat s0 hs0_code 0 hs0_i hs0_n (by simp) (by simp)
    (by
      have hs0_clk : s0.clock = state.clock := rfl
      rw [hs0_clk]
      simp only [Nat.zero_add, Nat.mul_one]
      omega)
  simp only [Nat.zero_add, Nat.mul_one] at hloop
  exact (RunBounded.seq hloop (a := K.toNat) (b := 0)
    (by
      have hs0_clk : s0.clock = state.clock := rfl
      rw [hs0_clk]
      omega)
    (fun next _ nextCode nextBudget =>
      (ProgBounded.straight (.return (.const 1)) rfl) next (nextCode.trans hs0_code) nextBudget)).weaken (by omega)

theorem calleeBodyBounded_memzero_le (dst sizeExp : ExpHOL 64) (M : Nat)
    (hsmall : M + 32 < 2 ^ 64)
    (hsize : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (vk : ValueHOL 64),
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) sizeExp = some vk →
      ∃ K : BitVec 64, vk = .val (.word K) ∧ K.toNat ≤ M) :
    CalleeBodyBounded (ofString "memzero") [dst, sizeExp] (M / 8 + 8) := by
  simpa using calleeBodyBounded_of_argAt (ofString "memzero") [(ofString "dst", .one)]
    (ofString "n") .one [] (sourceFnBody Guest.Software.guestFn_memzero) .one
    (fun _ h => nomatch h) lookup_memzero [dst] sizeExp [] rfl
    (fun vk => ∃ K : BitVec 64, vk = .val (.word K) ∧ K.toNat ≤ M) (M / 8 + 7)
    (fun s vk hek => hsize s vk hek)
    (fun entry vk hvk hcode hloc hbudget => by
      obtain ⟨K, rfl, hle⟩ := hvk
      exact runBounded_memzero_le entry K M hle hsmall hcode hloc hbudget)

theorem calleeBodyBounded_memcpy_le (dst src sizeExp : ExpHOL 64) (M : Nat)
    (hsmall : M + 32 < 2 ^ 64)
    (hsize : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (vk : ValueHOL 64),
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) sizeExp = some vk →
      ∃ K : BitVec 64, vk = .val (.word K) ∧ K.toNat ≤ M) :
    CalleeBodyBounded (ofString "memcpy") [dst, src, sizeExp] (M / 8 + 8) := by
  simpa using calleeBodyBounded_of_argAt (ofString "memcpy")
    [(ofString "dst", .one), (ofString "src", .one)]
    (ofString "n") .one [] (sourceFnBody Guest.Software.guestFn_memcpy) .one
    (fun _ h => nomatch h) lookup_memcpy [dst, src] sizeExp [] rfl
    (fun vk => ∃ K : BitVec 64, vk = .val (.word K) ∧ K.toNat ≤ M) (M / 8 + 7)
    (fun s vk hek => hsize s vk hek)
    (fun entry vk hvk hcode hloc hbudget => by
      obtain ⟨K, rfl, hle⟩ := hvk
      exact runBounded_memcpy_le entry K M hle hsmall hcode hloc hbudget)

theorem calleeBodyBounded_memeq_le (a b sizeExp : ExpHOL 64) (M : Nat)
    (hsmall : M + 32 < 2 ^ 64)
    (hsize : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (vk : ValueHOL 64),
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) sizeExp = some vk →
      ∃ K : BitVec 64, vk = .val (.word K) ∧ K.toNat ≤ M) :
    CalleeBodyBounded (ofString "memeq") [a, b, sizeExp] (M / 8 + 8) := by
  simpa using calleeBodyBounded_of_argAt (ofString "memeq")
    [(ofString "a", .one), (ofString "b", .one)]
    (ofString "n") .one [] (sourceFnBody Guest.Software.guestFn_memeq) .one
    (fun _ h => nomatch h) lookup_memeq [a, b] sizeExp [] rfl
    (fun vk => ∃ K : BitVec 64, vk = .val (.word K) ∧ K.toNat ≤ M) (M / 8 + 7)
    (fun s vk hek => hsize s vk hek)
    (fun entry vk hvk hcode hloc hbudget => by
      obtain ⟨K, rfl, hle⟩ := hvk
      exact runBounded_memeq_le entry K M hle hsmall hcode hloc hbudget)

theorem calleeBodyBounded_is_zero_bytes_le (p sizeExp : ExpHOL 64) (M : Nat)
    (hsize : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (vk : ValueHOL 64),
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) sizeExp = some vk →
      ∃ K : BitVec 64, vk = .val (.word K) ∧ K.toNat ≤ M) :
    CalleeBodyBounded (ofString "is_zero_bytes") [p, sizeExp] (M + 1) := by
  simpa using calleeBodyBounded_of_argAt (ofString "is_zero_bytes")
    [(ofString "p", .one)]
    (ofString "n") .one [] (sourceFnBody Guest.Software.guestFn_is_zero_bytes) .one
    (fun _ h => nomatch h) lookup_is_zero_bytes [p] sizeExp [] rfl
    (fun vk => ∃ K : BitVec 64, vk = .val (.word K) ∧ K.toNat ≤ M) M
    (fun s vk hek => hsize s vk hek)
    (fun entry vk hvk hcode hloc hbudget => by
      obtain ⟨K, rfl, hle⟩ := hvk
      exact runBounded_is_zero_bytes_le entry K M hle hcode hloc hbudget)

theorem calleeBodyBounded_memzero_const (dst : ExpHOL 64) (K : BitVec 64)
    (hsmall : K.toNat + 32 < 2 ^ 64) :
    CalleeBodyBounded (ofString "memzero") [dst, .const K] (K.toNat / 8 + 8) :=
  calleeBodyBounded_memzero_le dst (.const K) K.toNat hsmall
    (fun s vk hek => by
      rw [evalHOLFinite_eq_toExact] at hek
      cases hek
      exact ⟨K, rfl, le_refl _⟩)

theorem calleeBodyBounded_memzero_mul_const (dst : ExpHOL 64) (a b : BitVec 64)
    (hsmall : (a * b).toNat + 32 < 2 ^ 64) :
    CalleeBodyBounded (ofString "memzero") [dst, .panop .mul [.const a, .const b]]
      ((a * b).toNat / 8 + 8) :=
  calleeBodyBounded_memzero_le dst (.panop .mul [.const a, .const b]) (a * b).toNat hsmall
    (fun s vk hek => by
      rw [evalHOLFinite_eq_toExact] at hek
      simp [evalHOLExact, evalListHOLExact, panOpHOL, valueIsWord, valueWord] at hek
      subst hek
      exact ⟨a * b, rfl, le_refl _⟩)

theorem calleeBodyBounded_memcpy_const (dst src : ExpHOL 64) (K : BitVec 64)
    (hsmall : K.toNat + 32 < 2 ^ 64) :
    CalleeBodyBounded (ofString "memcpy") [dst, src, .const K] (K.toNat / 8 + 8) :=
  calleeBodyBounded_memcpy_le dst src (.const K) K.toNat hsmall
    (fun s vk hek => by
      rw [evalHOLFinite_eq_toExact] at hek
      cases hek
      exact ⟨K, rfl, le_refl _⟩)

theorem calleeBodyBounded_memcpy_mul_const (dst src : ExpHOL 64) (a b : BitVec 64)
    (hsmall : (a * b).toNat + 32 < 2 ^ 64) :
    CalleeBodyBounded (ofString "memcpy") [dst, src, .panop .mul [.const a, .const b]]
      ((a * b).toNat / 8 + 8) :=
  calleeBodyBounded_memcpy_le dst src (.panop .mul [.const a, .const b]) (a * b).toNat hsmall
    (fun s vk hek => by
      rw [evalHOLFinite_eq_toExact] at hek
      simp [evalHOLExact, evalListHOLExact, panOpHOL, valueIsWord, valueWord] at hek
      subst hek
      exact ⟨a * b, rfl, le_refl _⟩)

theorem calleeBodyBounded_memeq_const (a b : ExpHOL 64) (K : BitVec 64)
    (hsmall : K.toNat + 32 < 2 ^ 64) :
    CalleeBodyBounded (ofString "memeq") [a, b, .const K] (K.toNat / 8 + 8) :=
  calleeBodyBounded_memeq_le a b (.const K) K.toNat hsmall
    (fun s vk hek => by
      rw [evalHOLFinite_eq_toExact] at hek
      cases hek
      exact ⟨K, rfl, le_refl _⟩)

theorem calleeBodyBounded_is_zero_bytes_const (p : ExpHOL 64) (K : BitVec 64) :
    CalleeBodyBounded (ofString "is_zero_bytes") [p, .const K] (K.toNat + 1) :=
  calleeBodyBounded_is_zero_bytes_le p (.const K) K.toNat
    (fun s vk hek => by
      rw [evalHOLFinite_eq_toExact] at hek
      cases hek
      exact ⟨K, rfl, le_refl _⟩)

/-! ## Section 5: Return-Word Bounds & Bounded RLP / Buffer / Hash Helpers -/

def FunWordReturnLe (fn : MlS) (cost M : Nat) : Prop :=
  FunBounded fn cost ∧
  ∀ {F : Type} (entry : PanSemStateFiniteExact 64 F) (parameters : List (MlS × ShapeHOL))
    (body : ProgHOL 64) (rs : ShapeHOL) (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F),
    originalRuntimeCode.lookup fn = some (parameters, body, rs) →
    entry.code = originalRuntimeCode →
    cost ≤ entry.clock →
    evaluateHOLFiniteState entry body = (some (.returned v), post) →
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat ≤ M

theorem progBounded_decCall_wordReturnLe {fn : MlS} {cost M : Nat}
    (hfn : FunWordReturnLe fn cost M)
    (name : MlS) (shape : ShapeHOL) (args : List (ExpHOL 64))
    {cont : ProgHOL 64} {tailCost : Nat}
    (hcont : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      w.toNat ≤ M → s.code = originalRuntimeCode → s.locals.lookup name = some (.val (.word w)) →
      tailCost ≤ s.clock → RunBounded s cont tailCost) :
    ProgBounded (.decCall name shape fn args cont) (cost + 1 + tailCost) := by
  obtain ⟨⟨params, fnBody, fnRs, hlookup, hbodyProg⟩, hretLe⟩ := hfn
  intro F state hcode hbudget
  cases hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) args with
  | none =>
    rw [evaluateHOLFiniteState_decCall_args_none state name shape fn args cont hargs]
    simp
  | some values =>
    cases hfound : lookupCodeHOLFinite state.code.lookup fn values with
    | none =>
      rw [evaluateHOLFiniteState_decCall_lookup_none state name shape fn args cont values hargs hfound]
      simp
    | some installed =>
      obtain ⟨body, callee, returnShape⟩ := installed
      have hfound' := hfound
      rw [hcode] at hfound'
      have hbody_eq : body = fnBody := by
        unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound'
        split at hfound'
        · cases hfound'
        · rename_i exactBody exactLocals exactShape raw
          have heq := Option.some.inj hfound'
          rcases Prod.mk.inj heq with ⟨rfl, _⟩
          unfold lookupCodeHOLExact at raw
          rw [hlookup] at raw
          dsimp only at raw
          split at raw
          · exact (Prod.mk.inj (Option.some.inj raw)).1.symm
          · cases raw
      subst hbody_eq
      let entry := callEntryStateHOLFinite state callee
      have hentry_code : entry.code = originalRuntimeCode := hcode
      have hentry_budget : cost ≤ entry.clock := by
        change cost ≤ state.clock - 1
        omega
      have hrun_bound := hbodyProg entry hentry_code hentry_budget
      have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata entry body
      rcases hran : evaluateHOLFiniteState entry body with ⟨res, post⟩
      rw [hran] at hrun_bound hmeta
      obtain ⟨spent, kept, safe⟩ := hrun_bound
      change state.clock - 1 ≤ post.clock + cost at spent
      have hwhole := evaluate_decCall_continuation_bounded state post name fn shape returnShape args
        values body cont callee res (cost + 1) tailCost hargs hfound (by omega) hran kept (by omega)
        safe (by
          intro v hv
          subst hv
          obtain ⟨w, rfl, hw_le⟩ := hretLe entry params body fnRs v post hlookup hentry_code
            hentry_budget hran
          let resumed := setVarHOLFinite name (.val (.word w)) { post with locals := state.locals }
          have hres_code : resumed.code = originalRuntimeCode := hmeta.1.trans hentry_code
          have hres_loc : resumed.locals.lookup name = some (.val (.word w)) := by
            simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          exact hcont resumed w hw_le hres_code hres_loc (by change tailCost ≤ post.clock; omega))
      simpa only [Nat.add_assoc] using hwhole

theorem progBounded_callAssignLocal_wordReturnLe {fn : MlS} {cost M : Nat}
    (hfn : FunWordReturnLe fn cost M)
    (name : MlS) (args : List (ExpHOL 64))
    {cont : ProgHOL 64} {tailCost : Nat}
    (hcont : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      w.toNat ≤ M → s.code = originalRuntimeCode → s.locals.lookup name = some (.val (.word w)) →
      tailCost ≤ s.clock → RunBounded s cont tailCost) :
    ProgBounded (.seq (.call (some (some (.local, name), none)) fn args) cont)
      (cost + 1 + tailCost) := by
  obtain ⟨⟨params, fnBody, fnRs, hlookup, hbodyProg⟩, hretLe⟩ := hfn
  intro F state hcode hbudget
  rw [evaluateHOLFiniteState_seq_line780]
  cases hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) args with
  | none =>
    rw [evaluateHOLFiniteState_call, hargs]
    simp
  | some values =>
    cases hfound : lookupCodeHOLFinite state.code.lookup fn values with
    | none =>
      rw [evaluateHOLFiniteState_call, hargs]
      dsimp only
      rw [hfound]
      simp
    | some installed =>
      obtain ⟨body, callee, returnShape⟩ := installed
      have hfound' := hfound
      rw [hcode] at hfound'
      have hbody_eq : body = fnBody := by
        unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound'
        split at hfound'
        · cases hfound'
        · rename_i exactBody exactLocals exactShape raw
          have heq := Option.some.inj hfound'
          rcases Prod.mk.inj heq with ⟨rfl, _⟩
          unfold lookupCodeHOLExact at raw
          rw [hlookup] at raw
          dsimp only at raw
          split at raw
          · exact (Prod.mk.inj (Option.some.inj raw)).1.symm
          · cases raw
      subst hbody_eq
      let entry := callEntryStateHOLFinite state callee
      have hentry_code : entry.code = originalRuntimeCode := hcode
      have hentry_budget : cost ≤ entry.clock := by
        change cost ≤ state.clock - 1
        omega
      have hrun_bound := hbodyProg entry hentry_code hentry_budget
      have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata entry body
      rcases hran : evaluateHOLFiniteState entry body with ⟨res, post⟩
      rw [hran] at hrun_bound hmeta
      obtain ⟨spent, kept, safe⟩ := hrun_bound
      change state.clock - 1 ≤ post.clock + cost at spent
      change post.clock ≤ state.clock - 1 at kept
      have hnz : state.clock ≠ 0 := by omega
      have hcall :
          (∃ w : BitVec 64,
            evaluateHOLFiniteState state (.call (some (some (.local, name), none)) fn args) =
              (none, setVarHOLFinite name (.val (.word w)) { post with locals := state.locals }) ∧
            w.toNat ≤ M) ∨
          (∃ rErr : PanSemResultExact 64,
            rErr ≠ .timeOut ∧
            (evaluateHOLFiniteState state (.call (some (some (.local, name), none)) fn args)).1 =
              some rErr ∧
            (evaluateHOLFiniteState state (.call (some (some (.local, name), none)) fn args)).2.clock =
              post.clock) := by
        rw [evaluateHOLFiniteState_call, hargs]
        dsimp only
        rw [hfound]
        dsimp only
        rw [if_neg hnz, hran]
        cases res with
        | none =>
          exact Or.inr ⟨.error, by simp, rfl, rfl⟩
        | some r =>
          cases r with
          | timeOut => exact False.elim (safe rfl)
          | error => exact Or.inr ⟨.error, by simp, rfl, rfl⟩
          | «break» => exact Or.inr ⟨.error, by simp, rfl, rfl⟩
          | «continue» => exact Or.inr ⟨.error, by simp, rfl, rfl⟩
          | exception eid ev => exact Or.inr ⟨.exception eid ev, by simp, rfl, rfl⟩
          | finalFfi ffi => exact Or.inr ⟨.finalFfi ffi, by simp, rfl, rfl⟩
          | returned v =>
            dsimp only
            by_cases hs : shapeEqHOL (shapeOfHOLExact v) returnShape = true
            · rw [if_pos hs]
              by_cases hvld : isValidValueHOLExact state.toExact .local name v = true
              · rw [if_pos hvld]
                obtain ⟨w, rfl, hw_le⟩ := hretLe entry params body fnRs v post hlookup hentry_code
                  hentry_budget hran
                exact Or.inl ⟨w, rfl, hw_le⟩
              · rw [if_neg hvld]
                exact Or.inr ⟨.error, by simp, rfl, rfl⟩
            · rw [if_neg hs]
              exact Or.inr ⟨.error, by simp, rfl, rfl⟩
      rcases hcall with ⟨w, hok, hw_le⟩ | ⟨rErr, hne, herr1, herr2⟩
      · rw [hok]
        dsimp only
        let resumed := setVarHOLFinite name (.val (.word w)) { post with locals := state.locals }
        have hres_code : resumed.code = originalRuntimeCode := hmeta.1.trans hentry_code
        have hres_loc : resumed.locals.lookup name = some (.val (.word w)) := by
          simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have ht := hcont resumed w hw_le hres_code hres_loc (by change tailCost ≤ post.clock; omega)
        change post.clock ≤ (evaluateHOLFiniteState resumed cont).2.clock + tailCost ∧
          (evaluateHOLFiniteState resumed cont).2.clock ≤ post.clock ∧
          (evaluateHOLFiniteState resumed cont).1 ≠ some .timeOut at ht
        change state.clock ≤ (evaluateHOLFiniteState resumed cont).2.clock + (cost + 1 + tailCost) ∧
          (evaluateHOLFiniteState resumed cont).2.clock ≤ state.clock ∧
          (evaluateHOLFiniteState resumed cont).1 ≠ some .timeOut
        exact ⟨by omega, by omega, ht.2.2⟩
      · rcases hc : evaluateHOLFiniteState state (.call (some (some (.local, name), none)) fn args) with ⟨rc, sc⟩
        rw [hc] at herr1 herr2
        dsimp only at herr1 herr2
        subst herr1
        dsimp only
        rw [herr2]
        exact ⟨by omega, by omega, by simpa using hne⟩

theorem funWordReturnLe_of_guestAst (i : Nat) (hi : i < Guest.Software.guestAst.length)
    (d : Decl (BitVec 64)) (cost M : Nat)
    (hd : Guest.Software.guestAst[i] = .function (extractFn d))
    (hprog : ProgBounded
      (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body) cost)
    (hret : ∀ {F : Type} (entry post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      entry.code = originalRuntimeCode → cost ≤ entry.clock →
      evaluateHOLFiniteState entry
        (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body) =
        (some (.returned v), post) →
      ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat ≤ M) :
    FunWordReturnLe (ofString (extractFn d).name) cost M := by
  refine ⟨funBounded_of_guestAst i hi d cost hd hprog, ?_⟩
  intro F entry params body rs v post hlookup hcode hbudget hran
  have hlk := lookup_of_guestAst_getElem i hi (extractFn d) hd
  rw [hlk] at hlookup
  have hinj := Option.some.inj hlookup
  rcases Prod.mk.inj hinj with ⟨_, hrest⟩
  rcases Prod.mk.inj hrest with ⟨hbody, _⟩
  subst body
  exact hret entry post v hcode hbudget hran

theorem tailCall_return_bound {fn : MlS} {cost M : Nat}
    (hfn : FunWordReturnLe fn cost M)
    (args : List (ExpHOL 64)) :
    ∀ {F : Type} (state post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      state.code = originalRuntimeCode → cost + 1 ≤ state.clock →
      evaluateHOLFiniteState state (.call none fn args) = (some (.returned v), post) →
      ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat ≤ M := by
  obtain ⟨⟨params, fnBody, fnRs, hlookup, _⟩, hretLe⟩ := hfn
  intro F state post v hcode hbudget hran
  rw [evaluateHOLFiniteState_call] at hran
  rcases hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) args with _ | values
  · rw [hargs] at hran; cases hran
  · rw [hargs] at hran
    dsimp only at hran
    rcases hfound : lookupCodeHOLFinite state.code.lookup fn values with _ | ⟨body, callee, returnShape⟩
    · rw [hfound] at hran; cases hran
    · rw [hfound] at hran
      dsimp only at hran
      have hnz : state.clock ≠ 0 := by omega
      rw [if_neg hnz] at hran
      have hfound' := hfound
      rw [hcode] at hfound'
      have hbody_eq := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup fn params fnBody body
        fnRs returnShape values callee hlookup hfound'
      subst body
      let entry := callEntryStateHOLFinite state callee
      have hentry_code : entry.code = originalRuntimeCode := hcode
      have hentry_budget : cost ≤ entry.clock := by change cost ≤ state.clock - 1; omega
      rcases hbody : evaluateHOLFiniteState entry fnBody with ⟨res, postBody⟩
      rw [hbody] at hran
      cases res with
      | none => cases hran
      | some r =>
        cases r with
        | timeOut => cases hran
        | error => cases hran
        | «break» => cases hran
        | «continue» => cases hran
        | exception eid ev => cases hran
        | finalFfi ffi => cases hran
        | returned v' =>
          dsimp only at hran
          by_cases hs : shapeEqHOL (shapeOfHOLExact v') returnShape = true
          · rw [if_pos hs] at hran
            have hv : v' = v := by
              have h1 := (Prod.mk.inj hran).1
              have h2 := Option.some.inj h1
              cases h2
              rfl
            subst hv
            exact hretLe entry params fnBody fnRs v' postBody hlookup hentry_code hentry_budget hbody
          · rw [if_neg hs] at hran; cases hran

-- ============================================================================
-- Section 5b: Bit-length, RLP, u256_from_be, buffer_read, keccak256<136, sha256=48
-- ============================================================================

private theorem bit_length64_step {F : Type}
    (s : PanSemStateFiniteExact 64 F) (k : BitVec 64) {n0 x0 : BitVec 64} {B : Nat}
    (hk : 0 < k.toNat) (hk64 : k.toNat < 64)
    (hx_bound : B = 2 * k.toNat) (hx_lt : x0.toNat < 2 ^ B)
    (hadd_lt : n0.toNat + B ≤ 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hx : s.locals.lookup (ofString "x") = some (.val (.word x0))) :
    ∃ (s1 : PanSemStateFiniteExact 64 F) (n1 x1 : BitVec 64),
      evaluateHOLFiniteState s
        (.ite (.cmp .notEqual (.shift .lsr (.var .local (ofString "x")) (.const k)) (.const 0#64))
          (.seq
            (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const k]))
            (.assign .local (ofString "x") (.shift .lsr (.var .local (ofString "x")) (.const k))))
          .skip) = (none, s1) ∧
      s1.locals.lookup (ofString "n") = some (.val (.word n1)) ∧
      s1.locals.lookup (ofString "x") = some (.val (.word x1)) ∧
      n1.toNat ≤ n0.toNat + k.toNat ∧
      x1.toNat < 2 ^ k.toNat := by
  have hne_nx : ofString "n" ≠ ofString "x" := by decide
  have hk_ok : ¬ (¬ k.toNat = 0 ∧ 64 ≤ k.toNat) := by omega
  rw [evaluateHOLFiniteState_ite]
  have hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notEqual (.shift .lsr (.var .local (ofString "x")) (.const k)) (.const 0#64)) =
      some (.val (.word (if x0 >>> k.toNat = 0#64 then 0#64 else 1#64))) := by
    simp [evalHOLExact, hx, wordShiftHOL, hk_ok, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcond]
  dsimp only
  by_cases hzero : x0 >>> k.toNat = 0#64
  · rw [if_pos hzero, if_pos (show (0#64 : BitVec 64) = 0 by decide), evaluateHOLFiniteState_skip]
    refine ⟨s, n0, x0, rfl, hn, hx, by omega, ?_⟩
    have hdiv0 : x0.toNat / 2 ^ k.toNat = 0 := by
      have h1 := congrArg BitVec.toNat hzero
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at h1
      exact h1
    have hpos_pow : 0 < 2 ^ k.toNat := Nat.pos_of_ne_zero (by positivity)
    exact (Nat.div_eq_zero_iff_lt hpos_pow).mp hdiv0
  · rw [if_neg hzero, if_neg (show (1#64 : BitVec 64) ≠ 0 by decide)]
    rw [evaluateHOLFiniteState_seq_line780]
    have ha1 : evaluateHOLFiniteState s
        (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const k])) =
        (none, setVarHOLFinite (ofString "n") (.val (.word (n0 + k))) s) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hn,
        wordOpHOL, wordOp, valueIsWord, valueWord, lookupKvarHOLExact,
        isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
    rw [ha1]
    dsimp only
    let smid := setVarHOLFinite (ofString "n") (.val (.word (n0 + k))) s
    have hmid_x : smid.locals.lookup (ofString "x") = some (.val (.word x0)) := by
      simp [smid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne_nx, Ne.symm hne_nx, hx]
    have hmid_n : smid.locals.lookup (ofString "n") = some (.val (.word (n0 + k))) := by
      simp [smid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have ha2 : evaluateHOLFiniteState smid
        (.assign .local (ofString "x") (.shift .lsr (.var .local (ofString "x")) (.const k))) =
        (none, setVarHOLFinite (ofString "x") (.val (.word (x0 >>> k.toNat))) smid) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, hmid_x,
        wordShiftHOL, hk_ok, lookupKvarHOLExact,
        isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
    rw [ha2]
    let s1 := setVarHOLFinite (ofString "x") (.val (.word (x0 >>> k.toNat))) smid
    refine ⟨s1, n0 + k, x0 >>> k.toNat, rfl, ?_, ?_, ?_, ?_⟩
    · simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne_nx, Ne.symm hne_nx, hmid_n]
    · simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    · have hadd : (n0 + k).toNat = n0.toNat + k.toNat := BitVec.toNat_add_of_lt (by omega)
      omega
    · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      subst hx_bound
      have hpow : 2 ^ (2 * k.toNat) = 2 ^ k.toNat * 2 ^ k.toNat := by
        rw [Nat.two_mul, Nat.pow_add]
      rw [hpow] at hx_lt
      exact Nat.div_lt_of_lt_mul hx_lt

theorem funBounded_bit_length64 : FunBounded (ofString "bit_length64") 0 :=
  funBounded_of_guestAst 77 (by rw [guestAst_len]; decide) Guest.Software.guestFn_bit_length64 0 rfl
    (ProgBounded.straight _ rfl)

theorem funWordReturnLe_bit_length64 : FunWordReturnLe (ofString "bit_length64") 0 64 := by
  refine funWordReturnLe_of_guestAst 77 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_bit_length64 0 64 rfl (ProgBounded.straight _ rfl) ?_
  intro F entry post v _ _ hran
  dsimp only [extractFn, Guest.Software.guestFn_bit_length64,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at hran
  have hran1 := congrArg Prod.fst hran
  dsimp only at hran1
  rw [evaluateHOLFiniteState_dec_total] at hran1
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true] at hran1
  let s0 := setVarHOLFinite (ofString "n") (.val (.word 0#64)) entry
  change (evaluateHOLFiniteState s0 _).1 = some (.returned v) at hran1
  have hs0_n : s0.locals.lookup (ofString "n") = some (.val (.word 0#64)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  rcases hx0 : s0.locals.lookup (ofString "x") with _ | vx
  · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hran1
    simp [evalHOLExact, hx0] at hran1
  · cases vx with
    | rStruct _ =>
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hran1
      simp [evalHOLExact, hx0, wordShiftHOL, valueIsWord] at hran1
    | nStruct _ _ =>
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hran1
      simp [evalHOLExact, hx0, wordShiftHOL, valueIsWord] at hran1
    | val wlx =>
      cases wlx with
      | word x0 =>
        obtain ⟨s1, n1, x1, h1, hn1, hx1, hle1, hlt1⟩ :=
          bit_length64_step s0 32#64 (B := 64) (by decide) (by decide) (by decide) x0.isLt (by decide) hs0_n hx0
        rw [evaluateHOLFiniteState_seq_line780, h1] at hran1
        dsimp only at hran1
        obtain ⟨s2, n2, x2, h2, hn2, hx2, hle2, hlt2⟩ :=
          bit_length64_step s1 16#64 (B := 32) (by decide) (by decide) (by decide) hlt1 (by change n1.toNat + 32 ≤ 64; have : (32#64).toNat = 32 := rfl; have : (0#64).toNat = 0 := rfl; omega) hn1 hx1
        rw [evaluateHOLFiniteState_seq_line780, h2] at hran1
        dsimp only at hran1
        obtain ⟨s3, n3, x3, h3, hn3, hx3, hle3, hlt3⟩ :=
          bit_length64_step s2 8#64 (B := 16) (by decide) (by decide) (by decide) hlt2 (by have : (32#64).toNat = 32 := rfl; have : (16#64).toNat = 16 := rfl; have : (0#64).toNat = 0 := rfl; omega) hn2 hx2
        rw [evaluateHOLFiniteState_seq_line780, h3] at hran1
        dsimp only at hran1
        obtain ⟨s4, n4, x4, h4, hn4, hx4, hle4, hlt4⟩ :=
          bit_length64_step s3 4#64 (B := 8) (by decide) (by decide) (by decide) hlt3 (by have : (32#64).toNat = 32 := rfl; have : (16#64).toNat = 16 := rfl; have : (8#64).toNat = 8 := rfl; have : (0#64).toNat = 0 := rfl; omega) hn3 hx3
        rw [evaluateHOLFiniteState_seq_line780, h4] at hran1
        dsimp only at hran1
        obtain ⟨s5, n5, x5, h5, hn5, hx5, hle5, hlt5⟩ :=
          bit_length64_step s4 2#64 (B := 4) (by decide) (by decide) (by decide) hlt4 (by have : (32#64).toNat = 32 := rfl; have : (16#64).toNat = 16 := rfl; have : (8#64).toNat = 8 := rfl; have : (4#64).toNat = 4 := rfl; have : (0#64).toNat = 0 := rfl; omega) hn4 hx4
        rw [evaluateHOLFiniteState_seq_line780, h5] at hran1
        dsimp only at hran1
        obtain ⟨s6, n6, x6, h6, hn6, hx6, hle6, hlt6⟩ :=
          bit_length64_step s5 1#64 (B := 2) (by decide) (by decide) (by decide) hlt5 (by have : (32#64).toNat = 32 := rfl; have : (16#64).toNat = 16 := rfl; have : (8#64).toNat = 8 := rfl; have : (4#64).toNat = 4 := rfl; have : (2#64).toNat = 2 := rfl; have : (0#64).toNat = 0 := rfl; omega) hn5 hx5
        rw [evaluateHOLFiniteState_seq_line780, h6] at hran1
        dsimp only at hran1
        rw [evaluateHOLFiniteState_return] at hran1
        simp [evalHOLExact, evalListHOLExact, hn6, hx6, wordOpHOL, wordOp, valueIsWord, valueWord] at hran1
        split at hran1
        · have hv : ValueHOL.val (HolWordLab.word (n6 + x6)) = v := by
            cases hran1; rfl
          subst hv
          refine ⟨n6 + x6, rfl, ?_⟩
          have h0 : (0#64).toNat = 0 := rfl
          have h32 : (32#64).toNat = 32 := rfl
          have h16 : (16#64).toNat = 16 := rfl
          have h8 : (8#64).toNat = 8 := rfl
          have h4 : (4#64).toNat = 4 := rfl
          have h2v : (2#64).toNat = 2 := rfl
          have h1v : (1#64).toNat = 1 := rfl
          have hp1 : (2 : Nat) ^ (1#64).toNat = 2 := rfl
          rw [hp1] at hlt6
          have hn6_le : n6.toNat ≤ 63 := by omega
          have hadd : (n6 + x6).toNat = n6.toNat + x6.toNat := BitVec.toNat_add_of_lt (by omega)
          omega
        · cases hran1

theorem decCall_return_bound {fn : MlS} {cost M : Nat}
    (hfn : FunWordReturnLe fn cost M)
    (name : MlS) (shape : ShapeHOL) (args : List (ExpHOL 64)) (cont : ProgHOL 64) :
    ∀ {F : Type} (state post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      state.code = originalRuntimeCode → cost + 1 ≤ state.clock →
      evaluateHOLFiniteState state (.decCall name shape fn args cont) = (some (.returned v), post) →
      ∃ (resumed : PanSemStateFiniteExact 64 F) (w : BitVec 64),
        w.toNat ≤ M ∧
        resumed.code = originalRuntimeCode ∧
        resumed.clock ≤ state.clock - 1 ∧
        state.clock - 1 ≤ resumed.clock + cost ∧
        resumed.locals.lookup name = some (.val (.word w)) ∧
        (evaluateHOLFiniteState resumed cont).1 = some (.returned v) := by
  obtain ⟨⟨params, fnBody, fnRs, hlookup, hbodyProg⟩, hretLe⟩ := hfn
  intro F state post v hcode hbudget hran
  rw [evaluateHOLFiniteState_decCall_total] at hran
  rcases hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) args with _ | values
  · rw [hargs] at hran; cases hran
  · rw [hargs] at hran
    dsimp only at hran
    rcases hfound : lookupCodeHOLFinite state.code.lookup fn values with _ | ⟨body, callee, returnShape⟩
    · rw [hfound] at hran; cases hran
    · rw [hfound] at hran
      dsimp only at hran
      have hnz : state.clock ≠ 0 := by omega
      rw [if_neg hnz] at hran
      have hfound' := hfound
      rw [hcode] at hfound'
      have hbody_eq := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup fn params fnBody body
        fnRs returnShape values callee hlookup hfound'
      subst body
      let entry := callEntryStateHOLFinite state callee
      have hentry_code : entry.code = originalRuntimeCode := hcode
      have hentry_budget : cost ≤ entry.clock := by change cost ≤ state.clock - 1; omega
      have hbound := hbodyProg entry hentry_code hentry_budget
      have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata entry fnBody
      rcases hbody : evaluateHOLFiniteState entry fnBody with ⟨res, postBody⟩
      rw [hbody] at hran hbound hmeta
      obtain ⟨spent, kept, safe⟩ := hbound
      have hfix : fixClockHOLFinite entry (res, postBody) = (res, postBody) := by
        simp [fixClockHOLFinite, Nat.not_lt.mpr kept]
      rw [hfix] at hran
      cases res with
      | none => cases hran
      | some r =>
        cases r with
        | timeOut => exact False.elim (safe rfl)
        | error => cases hran
        | «break» => cases hran
        | «continue» => cases hran
        | exception eid ev => cases hran
        | finalFfi ffi => cases hran
        | returned v' =>
          simp only at hran
          split at hran
          · obtain ⟨w, rfl, hw_le⟩ := hretLe entry params fnBody fnRs v' postBody hlookup
              hentry_code hentry_budget hbody
            let resumed := setVarHOLFinite name (.val (.word w)) { postBody with locals := state.locals }
            have hres_code : resumed.code = originalRuntimeCode := hmeta.1.trans hentry_code
            have hres_loc : resumed.locals.lookup name = some (.val (.word w)) := by
              simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            exact ⟨resumed, w, hw_le, hres_code, kept, spent, hres_loc, (Prod.mk.inj hran).1⟩
          · cases hran

private theorem u256_bit_length_body_bounded :
    ProgBounded (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
      (extractFn Guest.Software.guestFn_u256_bit_length).body) 4 := by
  dsimp only [extractFn, Guest.Software.guestFn_u256_bit_length,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.seq
      (ProgBounded.iteMax _ (ProgBounded.decCall funBounded_bit_length64 _ _ _ (ProgBounded.straight _ rfl))
        (ProgBounded.straight _ rfl))
      (ProgBounded.seq
        (ProgBounded.iteMax _ (ProgBounded.decCall funBounded_bit_length64 _ _ _ (ProgBounded.straight _ rfl))
          (ProgBounded.straight _ rfl))
        (ProgBounded.seq
          (ProgBounded.iteMax _ (ProgBounded.decCall funBounded_bit_length64 _ _ _ (ProgBounded.straight _ rfl))
            (ProgBounded.straight _ rfl))
          (ProgBounded.tail funBounded_bit_length64 _))))
    (by decide)

theorem funBounded_u256_bit_length : FunBounded (ofString "u256_bit_length") 4 :=
  funBounded_of_guestAst 78 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_bit_length 4 rfl u256_bit_length_body_bounded

theorem funWordReturnLe_u256_bit_length : FunWordReturnLe (ofString "u256_bit_length") 4 256 := by
  refine funWordReturnLe_of_guestAst 78 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_bit_length 4 256 rfl u256_bit_length_body_bounded ?_
  intro F entry post v hcode hbudget hran
  dsimp only [extractFn, Guest.Software.guestFn_u256_bit_length,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at hran
  have hbranch : ∀ (s : PanSemStateFiniteExact 64 F) (cond : ExpHOL 64) (nm : MlS)
      (arg : ExpHOL 64) (off : BitVec 64) (rest : ProgHOL 64),
      off.toNat ≤ 192 →
      s.code = originalRuntimeCode → 1 ≤ s.clock →
      evaluateHOLFiniteState s
        (.seq (.ite cond (.decCall nm .one (ofString "bit_length64") [arg]
          (.return (.op .add [.const off, .var .local nm]))) .skip) rest) =
        (some (.returned v), post) →
      (∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat ≤ 256) ∨
      evaluateHOLFiniteState s rest = (some (.returned v), post) := by
    intro s cond nm arg off rest hoff hs_code hs_clk hseq
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hseq
    split at hseq
    · split at hseq
      · rw [evaluateHOLFiniteState_skip] at hseq
        exact Or.inr hseq
      · rcases hdc : evaluateHOLFiniteState s
            (.decCall nm .one (ofString "bit_length64") [arg]
              (.return (.op .add [.const off, .var .local nm]))) with ⟨rdc, sdc⟩
        rw [hdc] at hseq
        dsimp only at hseq
        cases rdc with
        | none =>
          exfalso
          have hdc1 := congrArg Prod.fst hdc
          dsimp only at hdc1
          rw [evaluateHOLFiniteState_decCall_total] at hdc1
          rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [arg] with _ | vs
          · rw [hargs] at hdc1; cases hdc1
          · rw [hargs] at hdc1; dsimp only at hdc1
            rcases hlk : lookupCodeHOLFinite s.code.lookup (ofString "bit_length64") vs with _ | ⟨b, cal, rs⟩
            · rw [hlk] at hdc1; cases hdc1
            · rw [hlk] at hdc1; dsimp only at hdc1
              have hnz : s.clock ≠ 0 := by omega
              rw [if_neg hnz] at hdc1
              rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s cal) b with ⟨rb, sb⟩
              rw [hrun] at hdc1
              dsimp only at hdc1
              cases rb with
              | none => cases hdc1
              | some rr =>
                cases rr with
                | «break» => cases hdc1
                | «continue» => cases hdc1
                | error => cases hdc1
                | timeOut => cases hdc1
                | exception _ _ => cases hdc1
                | finalFfi _ => cases hdc1
                | returned vv =>
                  dsimp only at hdc1
                  split at hdc1
                  · dsimp only at hdc1
                    rw [evaluateHOLFiniteState_return] at hdc1
                    split at hdc1
                    · cases hdc1
                    · split at hdc1 <;> cases hdc1
                  · cases hdc1
        | some r =>
          cases r with
          | returned v' =>
            have hv' : v' = v := by
              have h1 := (Prod.mk.inj hseq).1
              have h2 := Option.some.inj h1
              cases h2; rfl
            subst hv'
            obtain ⟨resumed, w, hw_le, _, _, _, hloc, hret⟩ :=
              decCall_return_bound funWordReturnLe_bit_length64 nm .one [arg]
                (.return (.op .add [.const off, .var .local nm])) s sdc v' hs_code hs_clk hdc
            rw [evaluateHOLFiniteState_return] at hret
            simp [evalHOLExact, evalListHOLExact, hloc, wordOpHOL, wordOp, valueIsWord, valueWord] at hret
            split at hret
            · have hv : ValueHOL.val (HolWordLab.word (off + w)) = v' := by
                cases hret; rfl
              subst hv
              refine Or.inl ⟨off + w, rfl, ?_⟩
              have hadd : (off + w).toNat = off.toNat + w.toNat := BitVec.toNat_add_of_lt (by omega)
              omega
            · cases hret
          | _ => cases hseq
    · cases hseq
  rcases hbranch entry _ (ofString "n3") _ 192#64 _ (by decide) hcode (by omega) hran with h | h1
  · exact h
  · rcases hbranch entry _ (ofString "n2") _ 128#64 _ (by decide) hcode (by omega) h1 with h | h2
    · exact h
    · rcases hbranch entry _ (ofString "n1") _ 64#64 _ (by decide) hcode (by omega) h2 with h | h3
      · exact h
      · obtain ⟨w, rfl, hw_le⟩ := tailCall_return_bound funWordReturnLe_bit_length64 _
          entry post v hcode (by omega) h3
        exact ⟨w, rfl, by omega⟩

private theorem u256_byte_length_body_bounded :
    ProgBounded (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
      (extractFn Guest.Software.guestFn_u256_byte_length).body) 5 := by
  dsimp only [extractFn, Guest.Software.guestFn_u256_byte_length,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_u256_bit_length _ _ _ (ProgBounded.straight _ rfl))
    (by decide)

theorem funBounded_u256_byte_length : FunBounded (ofString "u256_byte_length") 5 :=
  funBounded_of_guestAst 79 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_byte_length 5 rfl u256_byte_length_body_bounded

theorem funWordReturnLe_u256_byte_length : FunWordReturnLe (ofString "u256_byte_length") 5 32 := by
  refine funWordReturnLe_of_guestAst 79 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_byte_length 5 32 rfl u256_byte_length_body_bounded ?_
  intro F entry post v hcode hbudget hran
  dsimp only [extractFn, Guest.Software.guestFn_u256_byte_length,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at hran
  obtain ⟨resumed, w, hw_le, _, _, _, hloc, hret⟩ :=
    decCall_return_bound funWordReturnLe_u256_bit_length (ofString "n") .one _ _
      entry post v hcode hbudget hran
  rw [evaluateHOLFiniteState_return] at hret
  simp [evalHOLExact, evalListHOLExact, hloc, wordOpHOL, wordOp, wordShiftHOL,
    valueIsWord, valueWord] at hret
  split at hret
  · have hv : ValueHOL.val (HolWordLab.word ((w + 7#64) >>> 3)) = v := by
      cases hret; rfl
    subst hv
    refine ⟨(w + 7#64) >>> 3, rfl, ?_⟩
    change ((w + 7#64) >>> (3 : Nat)).toNat ≤ 32
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have h7 : (7#64).toNat = 7 := rfl
    have hadd : (w + 7#64).toNat = w.toNat + 7 := by
      rw [BitVec.toNat_add_of_lt (by omega), h7]
    rw [hadd]
    omega
  · cases hret

def noTopReturn : ProgHOL 64 → Bool
  | .return _ => false
  | .call none _ _ => false
  | .seq first second => noTopReturn first && noTopReturn second
  | .ite _ yes no => noTopReturn yes && noTopReturn no
  | .dec _ _ _ body => noTopReturn body
  | .decCall _ _ _ _ continuation => noTopReturn continuation
  | .while _ body => noTopReturn body
  | .skip | .assign _ _ _ | .primitive _ _ _ | .store _ _ | .storeByte _ _ | .store32 _ _
  | .break | .continue | .raise _ _ | .extCall _ _ _ _ _ | .annot _ _ => true
  | .call (some (_, none)) _ _ => true
  | _ => false

theorem evaluate_noTopReturn {F : Type} (program : ProgHOL 64) (supported : noTopReturn program = true)
    (state : PanSemStateFiniteExact 64 F) (v : ValueHOL 64) :
    (evaluateHOLFiniteState state program).1 ≠ some (.returned v) := by
  cases shape : program with
  | «return» _ => simp [shape, noTopReturn] at supported
  | seq first second =>
    have children : noTopReturn first = true ∧ noTopReturn second = true := by
      simpa only [shape, noTopReturn, Bool.and_eq_true] using supported
    have remaining := evaluateHOLFiniteState_clock_le state first
    rw [evaluateHOLFiniteState_seq_line780]
    have one := evaluate_noTopReturn first children.1 state v
    rcases firstRun : evaluateHOLFiniteState state first with ⟨result, middle⟩
    rw [firstRun] at one remaining
    cases result with
    | none => exact evaluate_noTopReturn second children.2 middle v
    | some _ => exact one
  | ite condition yes no =>
    have children : noTopReturn yes = true ∧ noTopReturn no = true := by
      simpa only [shape, noTopReturn, Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noTopReturn no children.2 state v
      · exact evaluate_noTopReturn yes children.1 state v
    · simp
  | dec name kind initializer body =>
    have child : noTopReturn body = true := by simpa only [shape, noTopReturn] using supported
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · simp
    · split
      · exact evaluate_noTopReturn body child _ v
      · simp
  | decCall name shape' function arguments continuation =>
    have child : noTopReturn continuation = true := by simpa only [shape, noTopReturn] using supported
    rw [evaluateHOLFiniteState_decCall_total]
    rcases hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with _ | vs
    · simp
    · dsimp only
      rcases hlk : lookupCodeHOLFinite state.code.lookup function vs with _ | ⟨b, cal, rs⟩
      · simp
      · dsimp only
        split
        · simp
        · rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state cal) b with ⟨rb, sb⟩
          have remaining := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state cal) b
          rw [hrun] at remaining
          have fixed : fixClockHOLFinite (callEntryStateHOLFinite state cal) (rb, sb) = (rb, sb) := by
            simp [fixClockHOLFinite, Nat.not_lt.mpr remaining]
          rw [fixed]
          dsimp only
          cases rb with
          | none => simp
          | some r =>
            cases r with
            | returned w =>
              dsimp only
              split
              · dsimp only
                have smaller : (setVarHOLFinite name w { sb with locals := state.locals }).clock < state.clock := by
                  change sb.clock < state.clock
                  change sb.clock ≤ state.clock - 1 at remaining
                  omega
                exact evaluate_noTopReturn continuation child _ v
              · simp
            | _ => simp
  | skip => simp [evaluateHOLFiniteState_skip]
  | «break» => simp [evaluateHOLFiniteState_break]
  | «continue» => simp [evaluateHOLFiniteState_continue]
  | annot tag text => simp [evaluateHOLFiniteState_annot]
  | raise name value =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> simp
    · simp
  | store destination value =>
    rcases (evaluate_store_control_frame state destination value).1 with h | h <;> rw [h] <;> simp
  | storeByte destination value =>
    rcases (evaluate_storeByte_control_frame state destination value).1 with h | h <;> rw [h] <;> simp
  | store32 address value =>
    rw [evaluateHOLFiniteState_store32]
    repeat' first | split | simp
  | assign kind name value =>
    rw [evaluateHOLFiniteState_assign]
    split
    · simp
    · split <;> simp
  | primitive name operator arguments =>
    rw [evaluateHOLFiniteState_primitive]
    repeat' first | split | simp
  | extCall function a b c d =>
    rw [evaluateHOLFiniteState_extCall_source]
    repeat' first | split | simp
  | call info function arguments =>
    rcases info with _ | ⟨d, _ | h⟩
    · simp [shape, noTopReturn] at supported
    · rw [evaluateHOLFiniteState_call]
      dsimp only
      repeat' first | split | simp | simp_all
    · simp [shape, noTopReturn] at supported
  | «while» condition body =>
    have child : noTopReturn body = true := by simpa only [shape, noTopReturn] using supported
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · simp
        · rename_i nonzero
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body
          have bodyNoRet := evaluate_noTopReturn body child (decClockHOLFinite state) v
          rcases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with ⟨result, middle⟩
          rw [bodyRun] at remaining bodyNoRet
          have smaller : middle.clock < state.clock := by
            change middle.clock ≤ state.clock - 1 at remaining
            omega
          cases result with
          | none => exact evaluate_noTopReturn (.while condition body) (by simp [noTopReturn, child]) middle v
          | some result =>
            cases result with
            | «continue» => exact evaluate_noTopReturn (.while condition body) (by simp [noTopReturn, child]) middle v
            | «returned» v' =>
              dsimp only
              intro heq
              cases Option.some.inj heq
              exact bodyNoRet rfl
            | _ => simp
      · simp
    · simp
  | _ => simp [shape, noTopReturn] at supported
termination_by (state.clock, sizeOf program)
decreasing_by all_goals (simp_all [decClockHOLFinite, setVarHOLFinite]; omega)

private theorem seq_ite_return_const_or_skip {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (cond : ExpHOL 64)
    (pre : ProgHOL 64) (hpre : noTopReturn pre = true)
    (c : BitVec 64) (M : Nat) (hc : c.toNat ≤ M) (rest : ProgHOL 64) {v : ValueHOL 64}
    (hran : evaluateHOLFiniteState s (.seq (.ite cond (.seq pre (.return (.const c))) .skip) rest) =
      (some (.returned v), post)) :
    (∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat ≤ M) ∨
    evaluateHOLFiniteState s rest = (some (.returned v), post) := by
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hran
  split at hran
  · split at hran
    · rw [evaluateHOLFiniteState_skip] at hran
      exact Or.inr hran
    · rw [evaluateHOLFiniteState_seq_line780] at hran
      rcases hp : evaluateHOLFiniteState s pre with ⟨rp, sp⟩
      rw [hp] at hran
      cases rp with
      | some r =>
        dsimp only at hran
        have hr : r = .returned v := Option.some.inj (Prod.mk.inj hran).1
        subst hr
        exact False.elim (evaluate_noTopReturn pre hpre s v (by rw [hp]))
      | none =>
        dsimp only at hran
        rcases hret : evaluateHOLFiniteState sp (.return (.const c)) with ⟨rr, sr⟩
        rw [hret] at hran
        have hret1 := congrArg Prod.fst hret
        dsimp only at hret1
        rw [evaluateHOLFiniteState_return] at hret1
        simp only [evalHOLExact] at hret1
        split at hret1
        · have hrr : rr = some (.returned (.val (.word c))) := hret1.symm
          subst hrr
          dsimp only at hran
          have hv : ValueHOL.val (HolWordLab.word c) = v := by
            cases Option.some.inj (Prod.mk.inj hran).1
            rfl
          subst hv
          exact Or.inl ⟨c, rfl, hc⟩
        · have hrr : rr = some .error := hret1.symm
          subst hrr
          cases hran
  · cases hran

private theorem seq_ite_return_only_const_or_skip {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (cond : ExpHOL 64)
    (c : BitVec 64) (M : Nat) (hc : c.toNat ≤ M) (rest : ProgHOL 64) {v : ValueHOL 64}
    (hran : evaluateHOLFiniteState s (.seq (.ite cond (.return (.const c)) .skip) rest) =
      (some (.returned v), post)) :
    (∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat ≤ M) ∨
    evaluateHOLFiniteState s rest = (some (.returned v), post) := by
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hran
  split at hran
  · split at hran
    · rw [evaluateHOLFiniteState_skip] at hran
      exact Or.inr hran
    · rcases hret : evaluateHOLFiniteState s (.return (.const c)) with ⟨rr, sr⟩
      rw [hret] at hran
      have hret1 := congrArg Prod.fst hret
      dsimp only at hret1
      rw [evaluateHOLFiniteState_return] at hret1
      simp only [evalHOLExact] at hret1
      split at hret1
      · have hrr : rr = some (.returned (.val (.word c))) := hret1.symm
        subst hrr
        dsimp only at hran
        have hv : ValueHOL.val (HolWordLab.word c) = v := by
          have h1 := (Prod.mk.inj hran).1
          cases Option.some.inj h1
          rfl
        subst hv
        exact Or.inl ⟨c, rfl, hc⟩
      · have hrr : rr = some .error := hret1.symm
        subst hrr
        cases hran
  · cases hran

theorem funBounded_u256_limb : FunBounded (ofString "u256_limb") 0 :=
  funBounded_of_guestAst 43 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_limb 0 rfl (ProgBounded.straight _ rfl)

private theorem u256_to_be_min_body_bounded :
    ProgBounded (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
      (extractFn Guest.Software.guestFn_u256_to_be_min).body) 70 := by
  dsimp only [extractFn, Guest.Software.guestFn_u256_to_be_min,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine ProgBounded.weaken
    (progBounded_decCall_wordReturnLe funWordReturnLe_u256_byte_length (ofString "len") .one _
      (tailCost := 64) ?_)
    (by decide)
  intro F s lenW hlen_le hs_code hs_len hs_clk
  apply RunBounded.decConst
  let s0 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) s
  have hs0_code : s0.code = originalRuntimeCode := hs_code
  have hs0_i : s0.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs0_len : s0.locals.lookup (ofString "len") = some (.val (.word lenW)) := by
    have hne : ofString "i" ≠ ofString "len" := by decide
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hs_len]
  have hbody : CountedBodyExt (ofString "i") 1
      (.dec (ofString "pos") .one
        (.op .sub [.op .sub [.var .local (ofString "len"), .const 1#64], .var .local (ofString "i")])
        (.decCall (ofString "l") .one (ofString "u256_limb")
          [.var .local (ofString "a"), .shift .lsr (.var .local (ofString "pos")) (.const 3#64)]
          (.seq
            (.storeByte (.op .add [.var .local (ofString "out"), .var .local (ofString "i")])
              (.op .and
                [.shift .lsr (.var .local (ofString "l"))
                  (.panop .mul [.op .and [.var .local (ofString "pos"), .const 7#64], .const 8#64]),
                 .const 255#64]))
            (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64])))))
      1 := by
    refine CountedBodyExt.dec _ _ _ (by decide) ?_
    exact CountedBodyExt.decCall _ _ _ _ (by decide)
      (calleeBodyBounded_of_funBounded funBounded_u256_limb)
      (CountedBodyExt.seqPre _ (ProgBounded.straight _ rfl) rfl rfl CountedBodyExt.incr)
  have hs0_len_eval : @evalHOLExact 64 F _ s0.toExact
      (fun a => Classical.propDecidable (s0.memaddrs a)) (.var .local (ofString "len")) =
      some (.val (.word lenW)) := by
    simp [evalHOLExact, hs0_len]
  have hloop_raw := variableLimitWhileExt_run (ofString "i") (.var .local (ofString "len"))
    .lower (Or.inr rfl) lenW (fun h => nomatch h) rfl rfl hbody lenW.toNat s0 hs0_code 0#64
    hs0_i hs0_len_eval (by simp) (by simp) (by change lenW.toNat * 2 ≤ s.clock; omega)
  have hloop : RunBounded s0
      (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "len"))) _)
      (lenW.toNat * 2) := hloop_raw
  exact RunBounded.weaken
    (RunBounded.seq hloop (b := 0) (by change lenW.toNat * 2 + 0 ≤ s.clock; omega)
      (fun next _ nextCode nextBudget =>
        (ProgBounded.straight (.return (.var .local (ofString "len"))) rfl)
          next (nextCode.trans hs0_code) nextBudget))
    (by omega)

theorem funBounded_u256_to_be_min : FunBounded (ofString "u256_to_be_min") 70 :=
  funBounded_of_guestAst 88 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_to_be_min 70 rfl u256_to_be_min_body_bounded

theorem funWordReturnLe_u256_to_be_min : FunWordReturnLe (ofString "u256_to_be_min") 70 32 := by
  refine funWordReturnLe_of_guestAst 88 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_to_be_min 70 32 rfl u256_to_be_min_body_bounded ?_
  intro F entry post v hcode hbudget hran
  dsimp only [extractFn, Guest.Software.guestFn_u256_to_be_min,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at hran
  obtain ⟨resumed, lenW, hlen_le, _, _, _, hloc, hret⟩ :=
    decCall_return_bound funWordReturnLe_u256_byte_length (ofString "len") .one _ _
      entry post v hcode (by omega) hran
  rw [evaluateHOLFiniteState_dec_total] at hret
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true] at hret
  let s0 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) resumed
  have hs0_len : s0.locals.lookup (ofString "len") = some (.val (.word lenW)) := by
    have hne : ofString "i" ≠ ofString "len" := by decide
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hloc]
  change (evaluateHOLFiniteState s0 _).1 = some (.returned v) at hret
  rw [evaluateHOLFiniteState_seq_line780] at hret
  let wloop : ProgHOL 64 :=
    .while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "len")))
      (.dec (ofString "pos") .one
        (.op .sub [.op .sub [.var .local (ofString "len"), .const 1#64], .var .local (ofString "i")])
        (.decCall (ofString "l") .one (ofString "u256_limb")
          [.var .local (ofString "a"), .shift .lsr (.var .local (ofString "pos")) (.const 3#64)]
          (.seq
            (.storeByte (.op .add [.var .local (ofString "out"), .var .local (ofString "i")])
              (.op .and
                [.shift .lsr (.var .local (ofString "l"))
                  (.panop .mul [.op .and [.var .local (ofString "pos"), .const 7#64], .const 8#64]),
                 .const 255#64]))
            (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64])))))
  have hkeep := evaluate_avoidsLocal_flowing (ofString "len") wloop rfl s0
  have hnoRet := evaluate_noTopReturn wloop rfl s0 v
  rcases hw : evaluateHOLFiniteState s0 wloop with ⟨rw_res, sw⟩
  rw [hw] at hret hkeep hnoRet
  dsimp only at hkeep hnoRet
  cases rw_res with
  | some r =>
    exfalso
    dsimp only at hret
    exact hnoRet hret
  | none =>
    dsimp only at hret
    have hsw_len : sw.locals.lookup (ofString "len") = some (.val (.word lenW)) :=
      (hkeep (Or.inl rfl)).trans hs0_len
    rw [evaluateHOLFiniteState_return] at hret
    simp only [evalHOLExact, hsw_len] at hret
    split at hret
    · have hv : ValueHOL.val (HolWordLab.word lenW) = v := by
        cases hret; rfl
      subst hv
      exact ⟨lenW, rfl, hlen_le⟩
    · cases hret

private theorem rlp_be_len_body_bounded :
    ProgBounded (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
      (extractFn Guest.Software.guestFn_rlp_be_len).body) 8 := by
  dsimp only [extractFn, Guest.Software.guestFn_rlp_be_len,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  intro F state hcode hbudget
  apply RunBounded.decConst
  let s0 := setVarHOLFinite (ofString "n") (.val (.word 0#64)) state
  have hs0_n : s0.locals.lookup (ofString "n") = some (.val (.word 0#64)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  change RunBounded s0 _ 8
  unfold RunBounded
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hv : s0.locals.lookup (ofString "v") with _ | vv
  · rw [evaluateHOLFiniteState_while_total]
    have hg : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
        (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64)) = none := by
      rw [evalHOLFinite_eq_toExact]
      simp [evalHOLExact, hv]
    rw [hg]
    simp
  · cases vv with
    | rStruct _ =>
      rw [evaluateHOLFiniteState_while_total]
      have hg : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
          (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64)) = none := by
        rw [evalHOLFinite_eq_toExact]
        simp [evalHOLExact, hv]
      rw [hg]; simp
    | nStruct _ _ =>
      rw [evaluateHOLFiniteState_while_total]
      have hg : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
          (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64)) = none := by
        rw [evalHOLFinite_eq_toExact]
        simp [evalHOLExact, hv]
      rw [hg]; simp
    | val wlv =>
      cases wlv with
      | word w0 =>
        let wloop : ProgHOL 64 :=
          .while (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64))
            (.seq (.assign .local (ofString "v") (.shift .lsr (.var .local (ofString "v")) (.const 8#64)))
              (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const 1#64])))
        have hstep := lsr8_steps_zero 8 w0 (by simpa using w0.isLt) s0 0#64 hv hs0_n
          (by decide) (by change 8 ≤ state.clock; omega)
        rcases hw : evaluateHOLFiniteState s0 wloop with ⟨rw_res, sw⟩
        change (let r := evaluateHOLFiniteState s0 wloop; _) at hstep
        rw [hw] at hstep ⊢
        dsimp only at hstep ⊢
        obtain ⟨c1, c2, rfl, nOut, _, hloc_n⟩ := hstep
        dsimp only
        rw [evaluateHOLFiniteState_return]
        simp only [evalHOLExact, hloc_n]
        split <;> exact ⟨by simp [emptyLocalsHOLFinite]; omega,
          by simp [emptyLocalsHOLFinite]; omega, by simp⟩

theorem funBounded_rlp_be_len : FunBounded (ofString "rlp_be_len") 8 :=
  funBounded_of_guestAst 118 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_rlp_be_len 8 rfl rlp_be_len_body_bounded

theorem funWordReturnLe_rlp_be_len : FunWordReturnLe (ofString "rlp_be_len") 8 8 := by
  refine funWordReturnLe_of_guestAst 118 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_rlp_be_len 8 8 rfl rlp_be_len_body_bounded ?_
  intro F entry post v hcode hbudget hran
  dsimp only [extractFn, Guest.Software.guestFn_rlp_be_len,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at hran
  have hran1 := congrArg Prod.fst hran
  dsimp only at hran1
  rw [evaluateHOLFiniteState_dec_total] at hran1
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true] at hran1
  let s0 := setVarHOLFinite (ofString "n") (.val (.word 0#64)) entry
  have hs0_n : s0.locals.lookup (ofString "n") = some (.val (.word 0#64)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  change (evaluateHOLFiniteState s0 _).1 = some (.returned v) at hran1
  rw [evaluateHOLFiniteState_seq_line780] at hran1
  rcases hv : s0.locals.lookup (ofString "v") with _ | vv
  · rw [evaluateHOLFiniteState_while_total] at hran1
    have hg : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
        (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64)) = none := by
      rw [evalHOLFinite_eq_toExact]; simp [evalHOLExact, hv]
    rw [hg] at hran1; cases hran1
  · cases vv with
    | rStruct _ =>
      rw [evaluateHOLFiniteState_while_total] at hran1
      have hg : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
          (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64)) = none := by
        rw [evalHOLFinite_eq_toExact]; simp [evalHOLExact, hv]
      rw [hg] at hran1; cases hran1
    | nStruct _ _ =>
      rw [evaluateHOLFiniteState_while_total] at hran1
      have hg : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
          (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64)) = none := by
        rw [evalHOLFinite_eq_toExact]; simp [evalHOLExact, hv]
      rw [hg] at hran1; cases hran1
    | val wlv =>
      cases wlv with
      | word w0 =>
        let wloop : ProgHOL 64 :=
          .while (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64))
            (.seq (.assign .local (ofString "v") (.shift .lsr (.var .local (ofString "v")) (.const 8#64)))
              (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const 1#64])))
        have hstep := lsr8_steps_zero 8 w0 (by simpa using w0.isLt) s0 0#64 hv hs0_n
          (by decide) (by change 8 ≤ entry.clock; omega)
        rcases hw : evaluateHOLFiniteState s0 wloop with ⟨rw_res, sw⟩
        change (let r := evaluateHOLFiniteState s0 wloop; _) at hstep
        rw [hw] at hstep hran1
        dsimp only at hstep hran1
        obtain ⟨_, _, rfl, nOut, hnOut, hloc_n⟩ := hstep
        dsimp only at hran1
        rw [evaluateHOLFiniteState_return] at hran1
        simp only [evalHOLExact, hloc_n] at hran1
        split at hran1
        · have hveq : ValueHOL.val (HolWordLab.word nOut) = v := by
            cases hran1; rfl
          subst hveq
          exact ⟨nOut, rfl, hnOut⟩
        · cases hran1

private theorem lookup_rlp_put_be :
    originalRuntimeCode.lookup (ofString "rlp_put_be") =
      some ([(ofString "dst", .one), (ofString "v", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_put_be, .one) :=
  lookup_of_guestAst_getElem 119 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_put_be) rfl

theorem runBounded_rlp_put_be_le {F : Type}
    (state : PanSemStateFiniteExact 64 F) (K : BitVec 64) (M : Nat)
    (hle : K.toNat ≤ M)
    (hcode : state.code = originalRuntimeCode)
    (atN : state.locals.lookup (ofString "n") = some (.val (.word K)))
    (hbudget : M ≤ state.clock) :
    RunBounded state (sourceFnBody Guest.Software.guestFn_rlp_put_be) M := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_put_be,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  have heval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) (.var .local (ofString "n")) =
      some (.val (.word K)) := by
    simp [evalHOLExact, atN]
  apply RunBounded.decWord state (ofString "i") (.var .local (ofString "n")) K heval
  let s0 := setVarHOLFinite (ofString "i") (.val (.word K)) state
  have hs0_code : s0.code = originalRuntimeCode := hcode
  have hs0_i : s0.locals.lookup (ofString "i") = some (.val (.word K)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hdec : DecBodyExt (ofString "i")
      (.seq (.assign .local (ofString "i") (.op .sub [.var .local (ofString "i"), .const 1#64]))
        (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
          (.var .local (ofString "v")))
          (.assign .local (ofString "v") (.shift .lsr (.var .local (ofString "v")) (.const 8#64)))))
      0 :=
    DecBodyExt.seqPost _ DecBodyExt.decr (ProgBounded.straight _ rfl) rfl rfl
  have hloop_raw := downWhileExt_run (ofString "i") .lower (Or.inr rfl) hdec M s0 hs0_code K hs0_i
    (fun h => nomatch h) hle (by change M * 1 ≤ state.clock; omega)
  have hloop : RunBounded s0
      (.while (.cmp .lower (.const 0#64) (.var .local (ofString "i"))) _) (M * 1) := hloop_raw
  exact RunBounded.weaken
    (RunBounded.seq hloop (b := 0) (by change M * 1 + 0 ≤ state.clock; omega)
      (fun next _ nextCode nextBudget =>
        (ProgBounded.straight (.return (.const 0#64)) rfl) next (nextCode.trans hs0_code) nextBudget))
    (by omega)

theorem calleeBodyBounded_rlp_put_be_le (dst vExp nExp : ExpHOL 64) (M : Nat)
    (hn : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (vk : ValueHOL 64),
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) nExp = some vk →
      ∃ K : BitVec 64, vk = .val (.word K) ∧ K.toNat ≤ M) :
    CalleeBodyBounded (ofString "rlp_put_be") [dst, vExp, nExp] (M + 1) := by
  simpa using calleeBodyBounded_of_argAt (ofString "rlp_put_be")
    [(ofString "dst", .one), (ofString "v", .one)]
    (ofString "n") .one [] (sourceFnBody Guest.Software.guestFn_rlp_put_be) .one
    (fun _ h => nomatch h) lookup_rlp_put_be [dst, vExp] nExp [] rfl
    (fun vk => ∃ K : BitVec 64, vk = .val (.word K) ∧ K.toNat ≤ M) M
    (fun s vk hek => hn s vk hek)
    (fun entry vk hvk hcode hloc hbudget => by
      obtain ⟨K, rfl, hle⟩ := hvk
      exact runBounded_rlp_put_be_le entry K M hle hcode hloc hbudget)

private theorem rlp_write_header_body_bounded :
    ProgBounded (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
      (extractFn Guest.Software.guestFn_rlp_write_header).body) 18 := by
  dsimp only [extractFn, Guest.Software.guestFn_rlp_write_header,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine ProgBounded.weaken
    (ProgBounded.seq (ProgBounded.straight _ rfl)
      (progBounded_decCall_wordReturnLe funWordReturnLe_rlp_be_len (ofString "ll") .one _
        (tailCost := 9) ?_))
    (by decide)
  intro F s llW hll_le hs_code hs_ll hs_clk
  refine RunBounded.seq (a := 0) (b := 9)
    ((ProgBounded.straight _ rfl) s hs_code (by omega))
    (by omega)
    (fun s1 hs1_flow hs1_code hs1_clk => ?_)
  have hs1_ll : s1.locals.lookup (ofString "ll") = some (.val (.word llW)) := by
    have hkeep := evaluate_avoidsLocal_flowing (ofString "ll")
      (.storeByte (.var .local (ofString "dst"))
        (.op .add [.var .local (ofString "base"), .const 55#64, .var .local (ofString "ll")])) rfl s
    rw [hs1_flow] at hkeep
    exact (hkeep (Or.inl rfl)).trans hs_ll
  have hcall : RunBounded s1
      (.call (some (none, none)) (ofString "rlp_put_be")
        [.op .add [.var .local (ofString "dst"), .const 1#64],
         .var .local (ofString "n"),
         .var .local (ofString "ll")]) 9 := by
    cases hargs : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
        [.op .add [.var .local (ofString "dst"), .const 1#64],
         .var .local (ofString "n"),
         .var .local (ofString "ll")] with
    | none =>
      rw [RunBounded, evaluateHOLFiniteState_call, hargs]; simp
    | some vs =>
      obtain ⟨vpre, vk, vpost, hvlen, hek, rfl⟩ :=
        evalListHOLFinite_split s1
          [.op .add [.var .local (ofString "dst"), .const 1#64], .var .local (ofString "n")]
          (.var .local (ofString "ll")) [] hargs
      have hvk : vk = .val (.word llW) := by
        rw [evalHOLFinite_eq_toExact] at hek
        simp [evalHOLExact, hs1_ll] at hek
        exact hek.symm
      subst hvk
      exact RunBounded.call (destination := none) (bodyCost := 8) hargs (by omega)
        (fun body callee rs hfound => by
          have hs1_c := hs1_code.trans hs_code
          rw [hs1_c] at hfound
          obtain ⟨rfl, hat⟩ := lookupCodeHOLFinite_param_at originalRuntimeCode.lookup
            (ofString "rlp_put_be") [(ofString "dst", .one), (ofString "v", .one)]
            (ofString "n") .one [] (sourceFnBody Guest.Software.guestFn_rlp_put_be) .one
            (fun _ h => nomatch h) lookup_rlp_put_be hvlen hfound
          exact runBounded_rlp_put_be_le (callEntryStateHOLFinite s1 callee) llW 8 hll_le hs1_c hat
            (by change 8 ≤ s1.clock - 1; omega))
  exact RunBounded.seq hcall (b := 0) (by omega)
    (fun s2 _ hs2_code hs2_clk =>
      (ProgBounded.straight _ rfl) s2 (hs2_code.trans (hs1_code.trans hs_code)) hs2_clk)

theorem funBounded_rlp_write_header : FunBounded (ofString "rlp_write_header") 18 :=
  funBounded_of_guestAst 120 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_rlp_write_header 18 rfl rlp_write_header_body_bounded

theorem funWordReturnLe_rlp_write_header : FunWordReturnLe (ofString "rlp_write_header") 18 9 := by
  refine funWordReturnLe_of_guestAst 120 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_rlp_write_header 18 9 rfl rlp_write_header_body_bounded ?_
  intro F entry post v hcode hbudget hran
  dsimp only [extractFn, Guest.Software.guestFn_rlp_write_header,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at hran
  rcases seq_ite_return_const_or_skip entry post _ _ rfl 1#64 9 (by decide) _ hran with h | hrest
  · exact h
  · obtain ⟨resumed, llW, hll_le, _, _, _, hloc, hret⟩ :=
      decCall_return_bound funWordReturnLe_rlp_be_len (ofString "ll") .one _ _
        entry post v hcode (by omega) hrest
    rw [evaluateHOLFiniteState_seq_line780] at hret
    have hk1 := evaluate_avoidsLocal_flowing (ofString "ll")
      (.storeByte (.var .local (ofString "dst"))
        (.op .add [.var .local (ofString "base"), .const 55#64, .var .local (ofString "ll")])) rfl resumed
    have hnr1 := evaluate_noTopReturn
      (.storeByte (.var .local (ofString "dst"))
        (.op .add [.var .local (ofString "base"), .const 55#64, .var .local (ofString "ll")])) rfl resumed v
    rcases hr1 : evaluateHOLFiniteState resumed _ with ⟨res1, s1⟩
    rw [hr1] at hret hk1 hnr1
    cases res1 with
    | some r => exact False.elim (hnr1 hret)
    | none =>
      dsimp only at hret hk1
      have hs1_ll : s1.locals.lookup (ofString "ll") = some (.val (.word llW)) :=
        (hk1 (Or.inl rfl)).trans hloc
      rw [evaluateHOLFiniteState_seq_line780] at hret
      have hk2 := evaluate_avoidsLocal_flowing (ofString "ll")
        (.call (some (none, none)) (ofString "rlp_put_be")
          [.op .add [.var .local (ofString "dst"), .const 1#64],
           .var .local (ofString "n"),
           .var .local (ofString "ll")]) rfl s1
      have hnr2 := evaluate_noTopReturn
        (.call (some (none, none)) (ofString "rlp_put_be")
          [.op .add [.var .local (ofString "dst"), .const 1#64],
           .var .local (ofString "n"),
           .var .local (ofString "ll")]) rfl s1 v
      rcases hr2 : evaluateHOLFiniteState s1 _ with ⟨res2, s2⟩
      rw [hr2] at hret hk2 hnr2
      cases res2 with
      | some r => exact False.elim (hnr2 hret)
      | none =>
        dsimp only at hret hk2
        have hs2_ll : s2.locals.lookup (ofString "ll") = some (.val (.word llW)) :=
          (hk2 (Or.inl rfl)).trans hs1_ll
        rw [evaluateHOLFiniteState_return] at hret
        simp [evalHOLExact, evalListHOLExact, hs2_ll, wordOpHOL, wordOp, valueIsWord, valueWord] at hret
        split at hret
        · have hv : ValueHOL.val (HolWordLab.word (1#64 + llW)) = v := by
            cases hret; rfl
          subst hv
          refine ⟨1#64 + llW, rfl, ?_⟩
          have hadd : (1#64 + llW).toNat = 1 + llW.toNat :=
            BitVec.toNat_add_of_lt (by change 1 + llW.toNat < 2 ^ 64; omega)
          omega
        · cases hret

private theorem rlp_header_len_body_bounded :
    ProgBounded (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
      (extractFn Guest.Software.guestFn_rlp_header_len).body) 9 := by
  dsimp only [extractFn, Guest.Software.guestFn_rlp_header_len,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.seq (ProgBounded.straight _ rfl)
      (ProgBounded.decCall funBounded_rlp_be_len _ _ _ (ProgBounded.straight _ rfl)))
    (by decide)

theorem funBounded_rlp_header_len : FunBounded (ofString "rlp_header_len") 9 :=
  funBounded_of_guestAst 121 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_rlp_header_len 9 rfl rlp_header_len_body_bounded

theorem funWordReturnLe_rlp_header_len : FunWordReturnLe (ofString "rlp_header_len") 9 9 := by
  refine funWordReturnLe_of_guestAst 121 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_rlp_header_len 9 9 rfl rlp_header_len_body_bounded ?_
  intro F entry post v hcode hbudget hran
  dsimp only [extractFn, Guest.Software.guestFn_rlp_header_len,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at hran
  rcases seq_ite_return_only_const_or_skip entry post _ 1#64 9 (by decide) _ hran with h | hrest
  · exact h
  · obtain ⟨resumed, llW, hll_le, _, _, _, hloc, hret⟩ :=
      decCall_return_bound funWordReturnLe_rlp_be_len (ofString "ll") .one _ _
        entry post v hcode (by omega) hrest
    rw [evaluateHOLFiniteState_return] at hret
    simp [evalHOLExact, evalListHOLExact, hloc, wordOpHOL, wordOp, valueIsWord, valueWord] at hret
    split at hret
    · have hv : ValueHOL.val (HolWordLab.word (1#64 + llW)) = v := by
        cases hret; rfl
      subst hv
      refine ⟨1#64 + llW, rfl, ?_⟩
      have hadd : (1#64 + llW).toNat = 1 + llW.toNat :=
        BitVec.toNat_add_of_lt (by change 1 + llW.toNat < 2 ^ 64; omega)
      omega
    · cases hret

private theorem rlp_encode_list_header_body_bounded :
    ProgBounded (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
      (extractFn Guest.Software.guestFn_rlp_encode_list_header).body) 19 := by
  dsimp only [extractFn, Guest.Software.guestFn_rlp_encode_list_header,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.tail funBounded_rlp_write_header _

theorem funBounded_rlp_encode_list_header : FunBounded (ofString "rlp_encode_list_header") 19 :=
  funBounded_of_guestAst 124 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_rlp_encode_list_header 19 rfl rlp_encode_list_header_body_bounded

theorem funWordReturnLe_rlp_encode_list_header : FunWordReturnLe (ofString "rlp_encode_list_header") 19 9 := by
  refine funWordReturnLe_of_guestAst 124 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_rlp_encode_list_header 19 9 rfl rlp_encode_list_header_body_bounded ?_
  intro F entry post v hcode hbudget hran
  dsimp only [extractFn, Guest.Software.guestFn_rlp_encode_list_header,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at hran
  exact tailCall_return_bound funWordReturnLe_rlp_write_header _ entry post v hcode hbudget hran

private theorem rlp_list_header_len_body_bounded :
    ProgBounded (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
      (extractFn Guest.Software.guestFn_rlp_list_header_len).body) 10 := by
  dsimp only [extractFn, Guest.Software.guestFn_rlp_list_header_len,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.tail funBounded_rlp_header_len _

theorem funBounded_rlp_list_header_len : FunBounded (ofString "rlp_list_header_len") 10 :=
  funBounded_of_guestAst 126 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_rlp_list_header_len 10 rfl rlp_list_header_len_body_bounded

theorem funWordReturnLe_rlp_list_header_len : FunWordReturnLe (ofString "rlp_list_header_len") 10 9 := by
  refine funWordReturnLe_of_guestAst 126 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_rlp_list_header_len 10 9 rfl rlp_list_header_len_body_bounded ?_
  intro F entry post v hcode hbudget hran
  dsimp only [extractFn, Guest.Software.guestFn_rlp_list_header_len,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at hran
  exact tailCall_return_bound funWordReturnLe_rlp_header_len _ entry post v hcode hbudget hran

theorem funBounded_rlp_bytes_encoded_len : FunBounded (ofString "rlp_bytes_encoded_len") 10 := by
  refine funBounded_of_guestAst 125 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_rlp_bytes_encoded_len 10 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_rlp_bytes_encoded_len,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.seq (ProgBounded.straight _ rfl)
      (ProgBounded.decCall funBounded_rlp_header_len _ _ _ (ProgBounded.straight _ rfl)))
    (by decide)

private theorem rlp_word_encoded_len_body_bounded :
    ProgBounded (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
      (extractFn Guest.Software.guestFn_rlp_word_encoded_len).body) 9 := by
  dsimp only [extractFn, Guest.Software.guestFn_rlp_word_encoded_len,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.seq (ProgBounded.straight _ rfl)
      (ProgBounded.decCall funBounded_rlp_be_len _ _ _ (ProgBounded.straight _ rfl)))
    (by decide)

theorem funBounded_rlp_word_encoded_len : FunBounded (ofString "rlp_word_encoded_len") 9 :=
  funBounded_of_guestAst 127 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_rlp_word_encoded_len 9 rfl rlp_word_encoded_len_body_bounded

theorem funWordReturnLe_rlp_word_encoded_len : FunWordReturnLe (ofString "rlp_word_encoded_len") 9 9 := by
  refine funWordReturnLe_of_guestAst 127 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_rlp_word_encoded_len 9 9 rfl rlp_word_encoded_len_body_bounded ?_
  intro F entry post v hcode hbudget hran
  dsimp only [extractFn, Guest.Software.guestFn_rlp_word_encoded_len,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at hran
  rcases seq_ite_return_only_const_or_skip entry post _ 1#64 9 (by decide) _ hran with h | hrest
  · exact h
  · obtain ⟨resumed, llW, hll_le, _, _, _, hloc, hret⟩ :=
      decCall_return_bound funWordReturnLe_rlp_be_len (ofString "ll") .one _ _
        entry post v hcode (by omega) hrest
    rw [evaluateHOLFiniteState_return] at hret
    simp [evalHOLExact, evalListHOLExact, hloc, wordOpHOL, wordOp, valueIsWord, valueWord] at hret
    split at hret
    · have hv : ValueHOL.val (HolWordLab.word (1#64 + llW)) = v := by
        cases hret; rfl
      subst hv
      refine ⟨1#64 + llW, rfl, ?_⟩
      have hadd : (1#64 + llW).toNat = 1 + llW.toNat :=
        BitVec.toNat_add_of_lt (by change 1 + llW.toNat < 2 ^ 64; omega)
      omega
    · cases hret

private theorem rlp_encode_word_body_bounded :
    ProgBounded (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
      (extractFn Guest.Software.guestFn_rlp_encode_word).body) 18 := by
  dsimp only [extractFn, Guest.Software.guestFn_rlp_encode_word,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine ProgBounded.weaken
    (ProgBounded.seq (ProgBounded.straight _ rfl)
      (ProgBounded.seq (ProgBounded.straight _ rfl)
        (progBounded_decCall_wordReturnLe funWordReturnLe_rlp_be_len (ofString "ll") .one _
          (tailCost := 9) ?_)))
    (by decide)
  intro F s llW hll_le hs_code hs_ll hs_clk
  refine RunBounded.seq (a := 0) (b := 9)
    ((ProgBounded.straight _ rfl) s hs_code (by omega))
    (by omega)
    (fun s1 hs1_flow hs1_code hs1_clk => ?_)
  have hs1_ll : s1.locals.lookup (ofString "ll") = some (.val (.word llW)) := by
    have hkeep := evaluate_avoidsLocal_flowing (ofString "ll")
      (.storeByte (.var .local (ofString "dst"))
        (.op .add [.const 128#64, .var .local (ofString "ll")])) rfl s
    rw [hs1_flow] at hkeep
    exact (hkeep (Or.inl rfl)).trans hs_ll
  have hcall : RunBounded s1
      (.call (some (none, none)) (ofString "rlp_put_be")
        [.op .add [.var .local (ofString "dst"), .const 1#64],
         .var .local (ofString "w"),
         .var .local (ofString "ll")]) 9 := by
    cases hargs : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
        [.op .add [.var .local (ofString "dst"), .const 1#64],
         .var .local (ofString "w"),
         .var .local (ofString "ll")] with
    | none =>
      rw [RunBounded, evaluateHOLFiniteState_call, hargs]; simp
    | some vs =>
      obtain ⟨vpre, vk, vpost, hvlen, hek, rfl⟩ :=
        evalListHOLFinite_split s1
          [.op .add [.var .local (ofString "dst"), .const 1#64], .var .local (ofString "w")]
          (.var .local (ofString "ll")) [] hargs
      have hvk : vk = .val (.word llW) := by
        rw [evalHOLFinite_eq_toExact] at hek
        simp [evalHOLExact, hs1_ll] at hek
        exact hek.symm
      subst hvk
      exact RunBounded.call (destination := none) (bodyCost := 8) hargs (by omega)
        (fun body callee rs hfound => by
          have hs1_c := hs1_code.trans hs_code
          rw [hs1_c] at hfound
          obtain ⟨rfl, hat⟩ := lookupCodeHOLFinite_param_at originalRuntimeCode.lookup
            (ofString "rlp_put_be") [(ofString "dst", .one), (ofString "v", .one)]
            (ofString "n") .one [] (sourceFnBody Guest.Software.guestFn_rlp_put_be) .one
            (fun _ h => nomatch h) lookup_rlp_put_be hvlen hfound
          exact runBounded_rlp_put_be_le (callEntryStateHOLFinite s1 callee) llW 8 hll_le hs1_c hat
            (by change 8 ≤ s1.clock - 1; omega))
  exact RunBounded.seq hcall (b := 0) (by omega)
    (fun s2 _ hs2_code hs2_clk =>
      (ProgBounded.straight _ rfl) s2 (hs2_code.trans (hs1_code.trans hs_code)) hs2_clk)

theorem funBounded_rlp_encode_word : FunBounded (ofString "rlp_encode_word") 18 :=
  funBounded_of_guestAst 123 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_rlp_encode_word 18 rfl rlp_encode_word_body_bounded

theorem funWordReturnLe_rlp_encode_word : FunWordReturnLe (ofString "rlp_encode_word") 18 9 := by
  refine funWordReturnLe_of_guestAst 123 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_rlp_encode_word 18 9 rfl rlp_encode_word_body_bounded ?_
  intro F entry post v hcode hbudget hran
  dsimp only [extractFn, Guest.Software.guestFn_rlp_encode_word,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at hran
  rcases seq_ite_return_const_or_skip entry post _ _ rfl 1#64 9 (by decide) _ hran with h | h1
  · exact h
  · rcases seq_ite_return_const_or_skip entry post _ _ rfl 1#64 9 (by decide) _ h1 with h | h2
    · exact h
    · obtain ⟨resumed, llW, hll_le, _, _, _, hloc, hret⟩ :=
        decCall_return_bound funWordReturnLe_rlp_be_len (ofString "ll") .one _ _
          entry post v hcode (by omega) h2
      rw [evaluateHOLFiniteState_seq_line780] at hret
      have hk1 := evaluate_avoidsLocal_flowing (ofString "ll")
        (.storeByte (.var .local (ofString "dst"))
          (.op .add [.const 128#64, .var .local (ofString "ll")])) rfl resumed
      have hnr1 := evaluate_noTopReturn
        (.storeByte (.var .local (ofString "dst"))
          (.op .add [.const 128#64, .var .local (ofString "ll")])) rfl resumed v
      rcases hr1 : evaluateHOLFiniteState resumed _ with ⟨res1, s1⟩
      rw [hr1] at hret hk1 hnr1
      cases res1 with
      | some r => exact False.elim (hnr1 hret)
      | none =>
        dsimp only at hret hk1
        have hs1_ll : s1.locals.lookup (ofString "ll") = some (.val (.word llW)) :=
          (hk1 (Or.inl rfl)).trans hloc
        rw [evaluateHOLFiniteState_seq_line780] at hret
        have hk2 := evaluate_avoidsLocal_flowing (ofString "ll")
          (.call (some (none, none)) (ofString "rlp_put_be")
            [.op .add [.var .local (ofString "dst"), .const 1#64],
             .var .local (ofString "w"),
             .var .local (ofString "ll")]) rfl s1
        have hnr2 := evaluate_noTopReturn
          (.call (some (none, none)) (ofString "rlp_put_be")
            [.op .add [.var .local (ofString "dst"), .const 1#64],
             .var .local (ofString "w"),
             .var .local (ofString "ll")]) rfl s1 v
        rcases hr2 : evaluateHOLFiniteState s1 _ with ⟨res2, s2⟩
        rw [hr2] at hret hk2 hnr2
        cases res2 with
        | some r => exact False.elim (hnr2 hret)
        | none =>
          dsimp only at hret hk2
          have hs2_ll : s2.locals.lookup (ofString "ll") = some (.val (.word llW)) :=
            (hk2 (Or.inl rfl)).trans hs1_ll
          rw [evaluateHOLFiniteState_return] at hret
          simp [evalHOLExact, evalListHOLExact, hs2_ll, wordOpHOL, wordOp, valueIsWord, valueWord] at hret
          split at hret
          · have hv : ValueHOL.val (HolWordLab.word (1#64 + llW)) = v := by
              cases hret; rfl
            subst hv
            refine ⟨1#64 + llW, rfl, ?_⟩
            have hadd : (1#64 + llW).toNat = 1 + llW.toNat :=
            BitVec.toNat_add_of_lt (by change 1 + llW.toNat < 2 ^ 64; omega)
            omega
          · cases hret

end InitECandidate.Solver.GuestBoundCryptoPrecompiles
