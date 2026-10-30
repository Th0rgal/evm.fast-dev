import InitECandidate.Solver.UniformSourceClock
import InitECandidate.Solver.PanRunBounded
import InitECandidate.Solver.GuestUniformClockBound
import InitECandidate.Solver.PanRunBoundedExt

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace InitECandidate.Solver.GuestBoundRlpMpt

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.PanRunBoundedExt

theorem funBounded_rlp_fail : FunBounded (ofString "rlp_fail") 0 :=
  funBounded_of_guestAst 105 (by rw [guestAst_len]; decide) Guest.Software.guestFn_rlp_fail 0 rfl
    (ProgBounded.straight _ rfl)

private theorem countedBody_seq_straight {counter : MlS} {step : BitVec 64}
    (first : ProgHOL 64) {tail : ProgHOL 64} {cost : Nat}
    (hs : extStraightLine first = true)
    (ha : avoidsLocal counter first = true)
    (hn : noTopContinue first = true)
    (hrest : CountedBody counter step tail cost) :
    CountedBody counter step (.seq first tail) cost := by
  simpa using CountedBody.seq first (ProgBounded.straight first hs) ha hn hrest

private theorem lookup_rlp_read_length :
    originalRuntimeCode.lookup (ofString "rlp_read_length") =
      some ([(ofString "p", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_read_length, .one) :=
  lookup_of_guestAst_getElem 106 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_read_length) rfl

-- General variable-limit counted loop combinator:
-- bounds `while (.cmp op (.var .local counter) limitExp) body` for any `limitExp`
-- that evaluates to a constant word across loop iterations (e.g. `.var .local l` or `.rfield k (.var .local s)`).
def CountedStep (counter : MlS) (step : BitVec 64) (body : ProgHOL 64) (cost : Nat) : Prop :=
  ∀ {F : Type} (state : PanSemStateFiniteExact 64 F),
    state.code = originalRuntimeCode →
    ∀ w : BitVec 64, state.locals.lookup counter = some (.val (.word w)) →
    cost ≤ state.clock →
    state.clock ≤ (evaluateHOLFiniteState state body).2.clock + cost ∧
      (evaluateHOLFiniteState state body).2.clock ≤ state.clock ∧
      (evaluateHOLFiniteState state body).1 ≠ some .timeOut ∧
      (evaluateHOLFiniteState state body).1 ≠ some .continue ∧
      ((evaluateHOLFiniteState state body).1 = none →
        (evaluateHOLFiniteState state body).2.locals.lookup counter = some (.val (.word (w + step))) ∧
        (evaluateHOLFiniteState state body).2.code = state.code)

theorem countedStep_of_countedBody {counter : MlS} {step : BitVec 64} {body : ProgHOL 64} {cost : Nat}
    (h : CountedBody counter step body cost) : CountedStep counter step body cost :=
  fun state code w atC budget => h.run state code w atC budget

theorem countedStep_incr {counter : MlS} {step : BitVec 64} :
    CountedStep counter step (.assign .local counter (.op .add [.var .local counter, .const step])) 0 :=
  countedStep_of_countedBody CountedBody.incr

theorem countedStep_seq {counter : MlS} {step : BitVec 64} (first : ProgHOL 64) {tail : ProgHOL 64}
    {a b : Nat} (bounded : ProgBounded first a)
    (avoid : avoidsLocal counter first = true) (noCont : noTopContinue first = true)
    (rest : CountedStep counter step tail b) :
    CountedStep counter step (.seq first tail) (a + b) := by
  intro F state code w atC budget
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
      obtain ⟨t1, t2, t3, t4, t5⟩ := rest middle (meta'.1.trans code) w (by rw [kept']; exact atC) (by omega)
      refine ⟨by omega, by omega, t3, t4, fun normal => ?_⟩
      obtain ⟨i1, i2⟩ := t5 normal
      exact ⟨i1, i2.trans meta'.1⟩
    | some r =>
      dsimp only
      refine ⟨by omega, by omega, safe, noContinue, fun h => by simp at h⟩

theorem countedStep_seq_straight {counter : MlS} {step : BitVec 64}
    (first : ProgHOL 64) {tail : ProgHOL 64} {cost : Nat}
    (hs : extStraightLine first = true)
    (ha : avoidsLocal counter first = true)
    (hn : noTopContinue first = true)
    (hrest : CountedStep counter step tail cost) :
    CountedStep counter step (.seq first tail) cost := by
  intro F state code w atC budget
  have h := countedStep_seq first (ProgBounded.straight first hs) ha hn hrest state code w atC (by omega)
  simpa using h

theorem countedStep_dec {counter : MlS} {step : BitVec 64}
    (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL 64) {body : ProgHOL 64} {cost : Nat}
    (distinct : counter ≠ name) (rest : CountedStep counter step body cost) :
    CountedStep counter step (.dec name shape initializer body) cost := by
  intro F state code w atC budget
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · exact ⟨Nat.le_add_right _ _, le_refl _, by simp, by simp, by simp⟩
  · rename_i val _
    split
    · let inner := setVarHOLFinite name val state
      have atInner : inner.locals.lookup counter = some (.val (.word w)) := by
        simp [inner, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm distinct, atC]
      obtain ⟨t1, t2, t3, t4, t5⟩ := rest inner code w atInner budget
      cases run : evaluateHOLFiniteState inner body with
      | mk res post =>
        rw [run] at t1 t2 t3 t4 t5
        dsimp only at t1 t2 t3 t4 t5 ⊢
        refine ⟨t1, t2, t3, t4, fun normal => ?_⟩
        obtain ⟨i1, i2⟩ := t5 normal
        refine ⟨?_, i2⟩
        rw [PanRunBounded.resVarEq_lookup, if_neg distinct]
        exact i1
    · exact ⟨Nat.le_add_right _ _, le_refl _, by simp, by simp, by simp⟩

theorem countedStep_decCall {counter : MlS} {step : BitVec 64}
    (name : MlS) (shape : ShapeHOL) (fn : MlS) (args : List (ExpHOL 64))
    {cont : ProgHOL 64} {fnCost contCost : Nat}
    (distinct : counter ≠ name)
    (hfn : FunBounded fn fnCost)
    (hrest : CountedStep counter step cont contCost) :
    CountedStep counter step (.decCall name shape fn args cont) (fnCost + 1 + contCost) := by
  intro F state code w atC budget
  cases hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) args with
  | none =>
    rw [evaluateHOLFiniteState_decCall_total, hargs]
    exact ⟨by dsimp only; omega, by simp, by simp, by simp, by simp⟩
  | some vs =>
    cases hlookup : lookupCodeHOLFinite state.code.lookup fn vs with
    | none =>
      rw [evaluateHOLFiniteState_decCall_total, hargs]
      dsimp only
      rw [hlookup]
      exact ⟨by dsimp only; omega, by simp, by simp, by simp, by simp⟩
    | some installed =>
      obtain ⟨body, callee, rs⟩ := installed
      have nonzero : state.clock ≠ 0 := by omega
      have hbody := ProgBounded.bodies_of_fun hfn state code (by omega) vs body callee rs hlookup
      change (callEntryStateHOLFinite state callee).clock ≤
          (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).2.clock + fnCost ∧
        (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).2.clock ≤
          (callEntryStateHOLFinite state callee).clock ∧
        (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).1 ≠ some .timeOut at hbody
      have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) body
      cases hran : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
      | mk r1 post =>
        rw [hran] at hbody hmeta
        obtain ⟨spent, kept, safe⟩ := hbody
        have remaining : post.clock ≤ (callEntryStateHOLFinite state callee).clock := kept
        change state.clock - 1 ≤ post.clock + fnCost at spent
        change post.clock ≤ state.clock - 1 at kept
        have postRemaining : post.clock ≤ state.clock := by omega
        rw [evaluateHOLFiniteState_decCall_total, hargs]
        dsimp only
        rw [hlookup]
        dsimp only
        rw [if_neg nonzero, hran]
        have fixed : fixClockHOLFinite (callEntryStateHOLFinite state callee) (r1, post) = (r1, post) := by
          simp [fixClockHOLFinite, Nat.not_lt.mpr remaining]
        rw [fixed]
        dsimp only
        cases r1 with
        | none => exact ⟨by change state.clock ≤ post.clock + (fnCost + 1 + contCost); omega, postRemaining, by simp, by simp, by simp⟩
        | some r =>
          cases r with
          | timeOut => exact False.elim (safe rfl)
          | error => exact ⟨by change state.clock ≤ post.clock + (fnCost + 1 + contCost); omega, postRemaining, by simp, by simp, by simp⟩
          | «break» => exact ⟨by change state.clock ≤ post.clock + (fnCost + 1 + contCost); omega, postRemaining, by simp, by simp, by simp⟩
          | «continue» => exact ⟨by change state.clock ≤ post.clock + (fnCost + 1 + contCost); omega, postRemaining, by simp, by simp, by simp⟩
          | exception _ _ => exact ⟨by change state.clock ≤ post.clock + (fnCost + 1 + contCost); omega, postRemaining, by simp, by simp, by simp⟩
          | finalFfi _ => exact ⟨by change state.clock ≤ post.clock + (fnCost + 1 + contCost); omega, postRemaining, by simp, by simp, by simp⟩
          | returned value =>
            simp only
            split
            · let resumed : PanSemStateFiniteExact 64 F := setVarHOLFinite name value { post with locals := state.locals }
              have hres_code : resumed.code = originalRuntimeCode := hmeta.1.trans code
              have hres_c : resumed.locals.lookup counter = some (.val (.word w)) := by
                simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm distinct, atC]
              have hcont_bnd := hrest resumed hres_code w hres_c (by change contCost ≤ post.clock; omega)
              rcases hcrun : evaluateHOLFiniteState (setVarHOLFinite name value { post with locals := state.locals }) cont with ⟨cres, cpost⟩
              change evaluateHOLFiniteState resumed cont = (cres, cpost) at hcrun
              rw [hcrun] at hcont_bnd
              dsimp only at hcont_bnd ⊢
              obtain ⟨c1, c2, c3, c4, c5⟩ := hcont_bnd
              change post.clock ≤ cpost.clock + contCost at c1
              change cpost.clock ≤ post.clock at c2
              refine ⟨by omega, by omega, c3, c4, fun hnorm => ?_⟩
              obtain ⟨advC, advCode⟩ := c5 hnorm
              refine ⟨?_, advCode.trans hmeta.1⟩
              rw [PanRunBounded.resVarEq_lookup, if_neg distinct]
              exact advC
            · exact ⟨by change state.clock ≤ post.clock + (fnCost + 1 + contCost); omega, postRemaining, by simp, by simp, by simp⟩

theorem progBounded_varCountedDec_exp (counter : MlS) (op : Cmp) (hop : op = .less ∨ op = .lower)
    (limitExp : ExpHOL 64) {body tail : ProgHOL 64} {cost tailCost : Nat}
    (hbody : CountedStep counter 1 body cost)
    (hpreserve : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (K : BitVec 64),
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) limitExp = some (.val (.word K)) →
      Flowing (evaluateHOLFiniteState (decClockHOLFinite s) body).1 →
      evalHOLFinite (evaluateHOLFiniteState (decClockHOLFinite s) body).2
        (h := fun a => Classical.propDecidable ((evaluateHOLFiniteState (decClockHOLFinite s) body).2.memaddrs a))
        limitExp = some (.val (.word K)))
    (htail : ProgBounded tail tailCost) :
    ProgBounded (.dec counter .one (.const 0)
      (.seq (.while (.cmp op (.var .local counter) limitExp) body) tail))
      ((2 ^ 64 - 1) * (cost + 1) + tailCost) := by
  have eval_cond : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (K w : BitVec 64),
      (op = .less → K.toNat < 2 ^ 63) → w.toNat ≤ K.toNat →
      s.locals.lookup counter = some (.val (.word w)) →
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) limitExp = some (.val (.word K)) →
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp op (.var .local counter) limitExp) =
        some (.val (.word (if w.toNat < K.toNat then 1 else 0))) := by
    intro F s K w signed within atC atL
    rw [evalHOLFinite_eq_toExact] at atL ⊢
    rcases hop with rfl | rfl
    · have small := signed rfl
      simp only [evalHOLExact, atC, atL]
      simp only [Compiler.Encoders.Asm.wordCmpHOL, holAsmSignedLess_small w K (by omega) small]
      by_cases lt : w.toNat < K.toNat <;> simp [lt]
    · simp only [evalHOLExact, atC, atL, Compiler.Encoders.Asm.wordCmpHOL]
      by_cases lt : w.toNat < K.toNat <;> simp [lt, BitVec.lt_def]
  have run_from : ∀ (K : BitVec 64), (op = .less → K.toNat < 2 ^ 63) →
      ∀ n : Nat, ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
        s.code = originalRuntimeCode →
        ∀ w : BitVec 64, s.locals.lookup counter = some (.val (.word w)) →
        evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) limitExp = some (.val (.word K)) →
        w.toNat ≤ K.toNat → K.toNat - w.toNat = n → n * (cost + 1) ≤ s.clock →
        let r := evaluateHOLFiniteState s (.while (.cmp op (.var .local counter) limitExp) body)
        s.clock ≤ r.2.clock + n * (cost + 1) ∧ r.2.clock ≤ s.clock ∧ r.1 ≠ some .timeOut := by
    intro K signed n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro F s code w atC atL within dist budget
      have cond := eval_cond s K w signed within atC atL
      dsimp only
      rw [evaluateHOLFiniteState_while_total, cond]
      by_cases lt : w.toNat < K.toNat
      · rw [if_pos lt]
        simp only [show (1 : BitVec 64) ≠ 0 by decide, if_true, ne_eq, not_false_eq_true]
        have posN : 0 < n := by omega
        have oneIter : cost + 1 ≤ n * (cost + 1) := Nat.le_mul_of_pos_left _ posN
        have clk : s.clock ≠ 0 := by omega
        rw [if_neg clk, fixClockHOLFinite_evaluateState]
        have stepRun := hbody (decClockHOLFinite s) code w atC (by change cost ≤ s.clock - 1; omega)
        have pres := hpreserve s K atL
        rcases bodyRun : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨res, mid⟩
        rw [bodyRun] at stepRun pres
        dsimp only at stepRun pres
        obtain ⟨spent, kept, safe, noCont, advance⟩ := stepRun
        change s.clock - 1 ≤ mid.clock + cost at spent
        change mid.clock ≤ s.clock - 1 at kept
        cases res with
        | none =>
          dsimp only
          obtain ⟨nextC, nextCode⟩ := advance rfl
          have nextL := pres (Or.inl rfl)
          have hKlt : K.toNat < 2 ^ 64 := K.isLt
          have hadd : (w + 1).toNat = w.toNat + 1 := BitVec.toNat_add_of_lt (by change w.toNat + 1 < 2 ^ 64; omega)
          have hmul : (n - 1) * (cost + 1) + (cost + 1) = n * (cost + 1) := by
            have hs : n - 1 + 1 = n := by omega
            calc (n - 1) * (cost + 1) + (cost + 1) = (n - 1 + 1) * (cost + 1) := by rw [Nat.add_mul, Nat.one_mul]
              _ = n * (cost + 1) := by rw [hs]
          obtain ⟨t1, t2, t3⟩ := ih (n - 1) (by omega) mid (nextCode.trans code) (w + 1)
            nextC nextL (by rw [hadd]; omega) (by rw [hadd]; omega) (by omega)
          exact ⟨by omega, by omega, t3⟩
        | some r =>
          cases r with
          | «continue» => exact absurd rfl noCont
          | «break» => exact ⟨by simp; omega, by simp; omega, by simp⟩
          | timeOut => exact absurd rfl safe
          | _ => exact ⟨by simp; omega, by simp; omega, by simp⟩
      · rw [if_neg lt]
        simp
  intro F state code budget
  rw [evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true]
  let s0 := setVarHOLFinite counter (.val (.word 0)) state
  have hs0_code : s0.code = originalRuntimeCode := code
  have hs0_c : s0.locals.lookup counter = some (.val (.word 0)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hloop : s0.clock ≤ (evaluateHOLFiniteState s0 (.while (.cmp op (.var .local counter) limitExp) body)).2.clock +
        (2 ^ 64 - 1) * (cost + 1) ∧
      (evaluateHOLFiniteState s0 (.while (.cmp op (.var .local counter) limitExp) body)).2.clock ≤ s0.clock ∧
      (evaluateHOLFiniteState s0 (.while (.cmp op (.var .local counter) limitExp) body)).1 ≠ some .timeOut := by
    cases hlim : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a)) limitExp with
    | none =>
      rw [evaluateHOLFiniteState_while_total]
      have hcond : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
          (.cmp op (.var .local counter) limitExp) = none := by
        rw [evalHOLFinite_eq_toExact] at hlim ⊢
        simp [evalHOLExact, hs0_c, hlim]
      rw [hcond]
      simp
    | some val =>
      cases val with
      | rStruct _ =>
        rw [evaluateHOLFiniteState_while_total]
        have hcond : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
            (.cmp op (.var .local counter) limitExp) = none := by
          rw [evalHOLFinite_eq_toExact] at hlim ⊢
          simp [evalHOLExact, hs0_c, hlim]
        rw [hcond]
        simp
      | nStruct _ _ =>
        rw [evaluateHOLFiniteState_while_total]
        have hcond : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
            (.cmp op (.var .local counter) limitExp) = none := by
          rw [evalHOLFinite_eq_toExact] at hlim ⊢
          simp [evalHOLExact, hs0_c, hlim]
        rw [hcond]
        simp
      | val wl =>
        cases wl with
        | word K =>
          by_cases signed : op = .less → K.toNat < 2 ^ 63
          · have ceil : K.toNat * (cost + 1) ≤ (2 ^ 64 - 1) * (cost + 1) :=
              Nat.mul_le_mul_right _ (by have := K.isLt; omega)
            have bnd := run_from K signed K.toNat s0 hs0_code 0 hs0_c hlim (by simp) (by simp)
              (by change K.toNat * (cost + 1) ≤ state.clock; omega)
            exact ⟨by omega, bnd.2.1, bnd.2.2⟩
          · have hop_eq : op = .less := by
              rcases hop with h | h
              · exact h
              · exfalso; exact signed (fun imp => by cases h.symm.trans imp)
            subst hop_eq
            have neg : ¬ K.toNat < 9223372036854775808 := fun sm => signed (fun _ => sm)
            have hcond : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
                (.cmp .less (.var .local counter) limitExp) = some (.val (.word 0)) := by
              rw [evalHOLFinite_eq_toExact] at hlim ⊢
              simp [evalHOLExact, hs0_c, hlim, Compiler.Encoders.Asm.wordCmpHOL,
                Compiler.Encoders.Asm.holAsmSignedLess, neg]
            rw [evaluateHOLFiniteState_while_total, hcond]
            simp
  have meta' := PanRunBounded.evaluateHOLFiniteState_metadata s0 (.while (.cmp op (.var .local counter) limitExp) body)
  change state.clock ≤ (evaluateHOLFiniteState s0 _).2.clock + _ ∧
    (evaluateHOLFiniteState s0 _).2.clock ≤ state.clock ∧
    (evaluateHOLFiniteState s0 _).1 ≠ some .timeOut
  rw [evaluateHOLFiniteState_seq_line780]
  rcases lr : evaluateHOLFiniteState s0 (.while (.cmp op (.var .local counter) limitExp) body) with ⟨res, mid⟩
  rw [lr] at hloop meta'
  dsimp only at hloop meta'
  obtain ⟨sp, kp, sf⟩ := hloop
  change state.clock ≤ mid.clock + (2 ^ 64 - 1) * (cost + 1) at sp
  change mid.clock ≤ state.clock at kp
  cases res with
  | none =>
    dsimp only
    obtain ⟨t1, t2, t3⟩ := htail mid (meta'.1.trans code) (by omega)
    exact ⟨by omega, by omega, t3⟩
  | some r =>
    dsimp only
    exact ⟨by omega, kp, sf⟩

theorem progBounded_varCountedDec_local (counter limit : MlS) (op : Cmp) (hop : op = .less ∨ op = .lower)
    {body tail : ProgHOL 64} {cost tailCost : Nat}
    (hbody : CountedStep counter 1 body cost)
    (havoid : avoidsLocal limit body = true)
    (htail : ProgBounded tail tailCost) :
    ProgBounded (.dec counter .one (.const 0)
      (.seq (.while (.cmp op (.var .local counter) (.var .local limit)) body) tail))
      ((2 ^ 64 - 1) * (cost + 1) + tailCost) :=
  progBounded_varCountedDec_exp counter op hop (.var .local limit) hbody
    (fun s K hlim hflow => by
      rw [evalHOLFinite_eq_toExact] at hlim ⊢
      have hpres := evaluate_avoidsLocal_flowing limit body havoid (decClockHOLFinite s) hflow
      change (evaluateHOLFiniteState (decClockHOLFinite s) body).2.locals.lookup limit = s.locals.lookup limit at hpres
      simp only [evalHOLExact] at hlim ⊢
      rw [hpres]
      exact hlim)
    htail

theorem progBounded_varCountedDec2_local (counter other limit : MlS) (otherShape : ShapeHOL)
    (otherInit : ExpHOL 64) (op : Cmp) (hop : op = .less ∨ op = .lower)
    {body tail : ProgHOL 64} {cost tailCost : Nat}
    (hdistinct : counter ≠ other)
    (hbody : CountedStep counter 1 body cost)
    (havoid : avoidsLocal limit body = true)
    (htail : ProgBounded tail tailCost) :
    ProgBounded (.dec counter .one (.const 0)
      (.dec other otherShape otherInit
        (.seq (.while (.cmp op (.var .local counter) (.var .local limit)) body) tail)))
      ((2 ^ 64 - 1) * (cost + 1) + tailCost) := by
  intro F state code budget
  rw [evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true]
  let s1 := setVarHOLFinite counter (.val (.word 0)) state
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · simp [setVarHOLFinite]
  · rename_i oval _
    split
    · let s2 := setVarHOLFinite other oval s1
      have hswap : setVarHOLFinite counter (.val (.word 0)) (setVarHOLFinite other oval state) = s2 := by
        cases state
        dsimp only [s1, s2, setVarHOLFinite]
        congr 1
        apply HolFiniteMapExact.ext
        funext k
        by_cases hk1 : k = counter
        · subst hk1
          simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hdistinct]
        · by_cases hk2 : k = other
          · subst hk2
            simp [HolFiniteMapExact.lookup_update, FUPDATE, hdistinct]
          · simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk1, Ne.symm hk2]
      have hrun := progBounded_varCountedDec_local counter limit op hop hbody havoid htail (setVarHOLFinite other oval state) code budget
      rw [evaluateHOLFiniteState_dec_total] at hrun
      simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true] at hrun
      rw [hswap] at hrun
      rcases lr : evaluateHOLFiniteState s2
        (.seq (.while (.cmp op (.var .local counter) (.var .local limit)) body) tail) with ⟨res, post⟩
      rw [lr] at hrun
      dsimp only at hrun ⊢
      exact hrun
    · simp [setVarHOLFinite]

theorem progBounded_varCountedDec_rfield (counter structVar : MlS) (idx : Nat) (op : Cmp)
    (hop : op = .less ∨ op = .lower)
    {body tail : ProgHOL 64} {cost tailCost : Nat}
    (hbody : CountedStep counter 1 body cost)
    (havoid : avoidsLocal structVar body = true)
    (htail : ProgBounded tail tailCost) :
    ProgBounded (.dec counter .one (.const 0)
      (.seq (.while (.cmp op (.var .local counter) (.rfield idx (.var .local structVar))) body) tail))
      ((2 ^ 64 - 1) * (cost + 1) + tailCost) :=
  progBounded_varCountedDec_exp counter op hop (.rfield idx (.var .local structVar)) hbody
    (fun s K hlim hflow => by
      rw [evalHOLFinite_eq_toExact] at hlim ⊢
      have hpres := evaluate_avoidsLocal_flowing structVar body havoid (decClockHOLFinite s) hflow
      change (evaluateHOLFiniteState (decClockHOLFinite s) body).2.locals.lookup structVar = s.locals.lookup structVar at hpres
      simp only [evalHOLExact] at hlim ⊢
      rw [hpres]
      exact hlim)
    htail

private theorem runBounded_rlp_read_length_body {F : Type}
    (state : PanSemStateFiniteExact 64 F) (K : BitVec 64)
    (hcode : state.code = originalRuntimeCode)
    (atN : state.locals.lookup (ofString "n") = some (.val (.word K)))
    (hbudget : K.toNat + 1 ≤ state.clock) :
    RunBounded state (sourceFnBody Guest.Software.guestFn_rlp_read_length) (K.toNat + 1) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_read_length,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  rw [Nat.add_comm K.toNat 1]
  have hstart : 1 + K.toNat ≤ state.clock := by omega
  refine RunBounded.seq (state := state) (a := 1) (b := K.toNat) ?_ hstart ?_
  · exact (ProgBounded.weaken
      (ProgBounded.iteMax _ (ProgBounded.call funBounded_rlp_fail none _) (ProgBounded.straight _ rfl))
      (by decide)) state hcode (by omega)
  · intro next result nextCode nextBudget
    have keepN : ∀ {p : ProgHOL 64}, evaluateHOLFiniteState state p = (none, next) →
        avoidsLocal (ofString "n") p = true →
        next.locals.lookup (ofString "n") = state.locals.lookup (ofString "n") := by
      intro p hr hp
      have h := evaluate_avoidsLocal_flowing (ofString "n") p hp state (by rw [hr]; exact Or.inl rfl)
      rw [hr] at h
      exact h
    have hnext_n : next.locals.lookup (ofString "n") = some (.val (.word K)) :=
      (keepN result rfl).trans atN
    apply RunBounded.decConst
    apply RunBounded.decConst
    have htail : RunBounded (setVarHOLFinite (ofString "i") (.val (.word 0))
          (setVarHOLFinite (ofString "v") (.val (.word 0)) next))
        (.seq
          (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n")))
            (.seq
              (.assign .local (ofString "v")
                (.op .or
                  [.shift .lsl (.var .local (ofString "v")) (.const 8),
                   .loadByte (.op .add [.var .local (ofString "p"), .var .local (ofString "i")])]))
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))))
          (.return (.var .local (ofString "v")))) K.toNat := by
      let s0 := setVarHOLFinite (ofString "i") (.val (.word 0))
        (setVarHOLFinite (ofString "v") (.val (.word 0)) next)
      have hs0_code : s0.code = originalRuntimeCode := nextCode.trans hcode
      have hs0_i : s0.locals.lookup (ofString "i") = some (.val (.word 0)) := by
        simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hs0_n : s0.locals.lookup (ofString "n") = some (.val (.word K)) := by
        simp only [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hnext_n]
        rw [if_neg (by decide), if_neg (by decide)]
      have hbody :
          CountedBody (ofString "i") 1
            (.seq
              (.assign .local (ofString "v")
                (.op .or
                  [.shift .lsl (.var .local (ofString "v")) (.const 8),
                   .loadByte (.op .add [.var .local (ofString "p"), .var .local (ofString "i")])]))
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))) 0 :=
        CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr
      have hloop := variableCountedWhile_run (ofString "i") (ofString "n") .lower (Or.inr rfl) K
        (fun h => by cases h) hbody rfl K.toNat s0 hs0_code 0 hs0_i hs0_n (by simp) (by simp)
        (by simp only [Nat.zero_add, Nat.mul_one]; change K.toNat ≤ next.clock; omega)
      simp only [Nat.zero_add, Nat.mul_one] at hloop
      have hs0_clock : s0.clock = next.clock := rfl
      have hmid : K.toNat + 0 ≤ s0.clock := by rw [hs0_clock]; omega
      exact (RunBounded.seq (state := s0) hloop (a := K.toNat) (b := 0) hmid
        (fun last _ lastCode lastBudget =>
          (ProgBounded.straight (.return (.var .local (ofString "v"))) rfl) last (lastCode.trans hs0_code) lastBudget))
    exact htail.weaken (by omega)

-- ============================================================================
-- Section 1: Base Helpers, U256 Helpers, Keccak256, and Exception Helpers
-- ============================================================================

theorem funBounded_ssz_fail : FunBounded (ofString "ssz_fail") 0 :=
  funBounded_of_guestAst 196 (by rw [guestAst_len]; decide) Guest.Software.guestFn_ssz_fail 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_mpt_fail : FunBounded (ofString "mpt_fail") 0 :=
  funBounded_of_guestAst 246 (by rw [guestAst_len]; decide) Guest.Software.guestFn_mpt_fail 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_min : FunBounded (ofString "min") 0 :=
  funBounded_of_guestAst 31 (by rw [guestAst_len]; decide) Guest.Software.guestFn_min 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_max : FunBounded (ofString "max") 0 :=
  funBounded_of_guestAst 32 (by rw [guestAst_len]; decide) Guest.Software.guestFn_max 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_u256_limb : FunBounded (ofString "u256_limb") 0 :=
  funBounded_of_guestAst 43 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_limb 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_nlz32 : FunBounded (ofString "nlz32") 0 :=
  funBounded_of_guestAst 62 (by rw [guestAst_len]; decide) Guest.Software.guestFn_nlz32 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_bit_length64 : FunBounded (ofString "bit_length64") 0 :=
  funBounded_of_guestAst 77 (by rw [guestAst_len]; decide) Guest.Software.guestFn_bit_length64 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_u256_bit_length : FunBounded (ofString "u256_bit_length") 4 := by
  refine funBounded_of_guestAst 78 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_bit_length 4 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_u256_bit_length,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.seq
      (ProgBounded.iteMax _ (ProgBounded.decCall funBounded_bit_length64 _ _ _ (ProgBounded.straight _ rfl)) (ProgBounded.straight _ rfl))
      (ProgBounded.seq
        (ProgBounded.iteMax _ (ProgBounded.decCall funBounded_bit_length64 _ _ _ (ProgBounded.straight _ rfl)) (ProgBounded.straight _ rfl))
        (ProgBounded.seq
          (ProgBounded.iteMax _ (ProgBounded.decCall funBounded_bit_length64 _ _ _ (ProgBounded.straight _ rfl)) (ProgBounded.straight _ rfl))
          (ProgBounded.tail funBounded_bit_length64 _))))
    (by decide)

theorem funBounded_u256_byte_length : FunBounded (ofString "u256_byte_length") 5 := by
  refine funBounded_of_guestAst 79 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_byte_length 5 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_u256_byte_length,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_u256_bit_length _ _ _ (ProgBounded.straight _ rfl))
    (by decide)

theorem funBounded_u256_from_be : FunBounded (ofString "u256_from_be") (2 ^ 64 + 3) := by
  refine funBounded_of_guestAst 86 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_from_be (2 ^ 64 + 3) rfl ?_
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
      (ProgBounded.dec _ _ _
        (ProgBounded.dec _ _ _
          (ProgBounded.dec _ _ _
            (ProgBounded.dec _ _ _
              (progBounded_varCountedDec_local (ofString "i") (ofString "n") .lower (Or.inr rfl)
                (cost := 0)
                (countedStep_of_countedBody
                  (CountedBody.dec _ _ _ (by decide)
                    (CountedBody.dec _ _ _ (by decide)
                      (CountedBody.dec _ _ _ (by decide)
                        (countedBody_seq_straight _ rfl rfl rfl
                          (countedBody_seq_straight _ rfl rfl rfl
                            (countedBody_seq_straight _ rfl rfl rfl
                              (countedBody_seq_straight _ rfl rfl rfl CountedBody.incr))))))))
                rfl
                (ProgBounded.straight _ rfl)))))))
    (by decide)

theorem funBounded_u256_to_be32 : FunBounded (ofString "u256_to_be32") 20 := by
  refine funBounded_of_guestAst 87 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_to_be32 20 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_u256_to_be32,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.seq
      (ProgBounded.iteMax _
        (ProgBounded.decCall funBounded_bswap64 _ _ _
          (ProgBounded.seq (ProgBounded.straight _ rfl)
            (ProgBounded.seq (ProgBounded.call funBounded_bswap64 _ _)
              (ProgBounded.seq (ProgBounded.straight _ rfl)
                (ProgBounded.seq (ProgBounded.call funBounded_bswap64 _ _)
                  (ProgBounded.seq (ProgBounded.straight _ rfl)
                    (ProgBounded.seq (ProgBounded.call funBounded_bswap64 _ _)
                      (ProgBounded.seq (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl)))))))))
        (ProgBounded.straight _ rfl))
      (ProgBounded.seq (ProgBounded.call funBounded_st_be64 none _)
        (ProgBounded.seq (ProgBounded.call funBounded_st_be64 none _)
          (ProgBounded.seq (ProgBounded.call funBounded_st_be64 none _)
            (ProgBounded.seq (ProgBounded.call funBounded_st_be64 none _)
              (ProgBounded.straight _ rfl))))))
    (by decide)

theorem funBounded_u256_to_be_min : FunBounded (ofString "u256_to_be_min") (2 * 2 ^ 64 + 4) := by
  refine funBounded_of_guestAst 88 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_to_be_min (2 * 2 ^ 64 + 4) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_u256_to_be_min,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine ProgBounded.weaken
    (ProgBounded.decCall funBounded_u256_byte_length _ _ _
      (progBounded_varCountedDec_local (ofString "i") (ofString "len") .lower (Or.inr rfl)
        (cost := 1)
        (countedStep_dec _ _ _ (by decide)
          (countedStep_decCall _ _ _ _ (by decide) funBounded_u256_limb
            (countedStep_seq_straight _ rfl rfl rfl countedStep_incr)))
        rfl
        (ProgBounded.straight _ rfl)))
    (by decide)

private theorem three_arg_lookup_mid (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
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
          simp [HolFiniteMapExact.lookup_update, FUPDATE, hp23, Ne.symm hp23]

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
  · rw [h1] at hargs
    cases hargs
  · rw [h1] at hargs
    rcases h3 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) e3 with _ | v3
    · rw [h3] at hargs
      cases hargs
    · rw [h3] at hargs
      cases hargs
      exact ⟨v1, v3, rfl⟩

private theorem lookup_keccak256 :
    originalRuntimeCode.lookup (ofString "keccak256") =
      some ([(ofString "p", .one), (ofString "n", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_keccak256, .one) :=
  lookup_of_guestAst_getElem 103 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_keccak256) rfl

theorem runBounded_keccak256_body {F : Type}
    (state : PanSemStateFiniteExact 64 F) (K : BitVec 64)
    (hsmall : K.toNat + 136 < 2 ^ 64)
    (hcode : state.code = originalRuntimeCode)
    (atN : state.locals.lookup (ofString "n") = some (.val (.word K)))
    (hbudget : (K.toNat / 136) * 163 + 271 ≤ state.clock) :
    RunBounded state (sourceFnBody Guest.Software.guestFn_keccak256) ((K.toNat / 136) * 163 + 271) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_keccak256,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine RunBounded.dec state (ofString "stp") .one (.var .global (ofString "keccak_st")) (fun vstp _ => ?_)
  let s1 := setVarHOLFinite (ofString "stp") vstp state
  have hs1_code : s1.code = originalRuntimeCode := hcode
  have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word K)) := by
    have hne : ofString "stp" ≠ ofString "n" := by decide
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, atN]
  have hmz1 := progBounded_memzero_const none (.var .local (ofString "stp")) 200 (by decide) s1 hs1_code (by change 33 ≤ state.clock; omega)
  refine (RunBounded.seq (state := s1) (a := 33) (b := (K.toNat / 136) * 163 + 238) hmz1
    (by change 33 + ((K.toNat / 136) * 163 + 238) ≤ state.clock; omega) (fun s2 hr2 hs2_code hs2_clk => ?_)).weaken (by omega)
  have hs2_n : s2.locals.lookup (ofString "n") = some (.val (.word K)) := by
    have hpres := evaluate_avoidsLocal_flowing (ofString "n")
      (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "stp"), .const 200])
      rfl s1 (by rw [hr2]; exact Or.inl rfl)
    rw [hr2] at hpres
    exact hpres.trans hs1_n
  apply RunBounded.decConst
  let s3 := setVarHOLFinite (ofString "i") (.val (.word 0)) s2
  have hs3_code : s3.code = originalRuntimeCode := hs2_code.trans hs1_code
  have hs3_i : s3.locals.lookup (ofString "i") = some (.val (.word 0)) := by
    simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs3_n : s3.locals.lookup (ofString "n") = some (.val (.word K)) := by
    have hne : ofString "i" ≠ ofString "n" := by decide
    simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hs2_n]
  let loopBody : ProgHOL 64 :=
    .seq
      (.call (some (none, none)) (ofString "keccak_absorb_block")
        [.var .local (ofString "stp"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")]])
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 136]))
  have hcb : CountedBody (ofString "i") 136 loopBody 162 := by
    dsimp only [loopBody]
    simpa using CountedBody.seq _ (ProgBounded.call funBounded_keccak_absorb_block none _) rfl rfl CountedBody.incr
  have hstride := notLowerStrideWhile_run (ofString "i") (ofString "n") K 136
    (by simpa using hsmall) (by decide) hcb rfl rfl (K.toNat / 136) s3 hs3_code 0 hs3_i hs3_n
    (by simp) (by simp) (by change (K.toNat / 136) * 163 ≤ s2.clock; omega)
  let loopProg : ProgHOL 64 :=
    .while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 136])) loopBody
  have hloop_rb : RunBounded s3 loopProg ((K.toNat / 136) * 163) := ⟨hstride.1, hstride.2.1, hstride.2.2.1⟩
  refine (RunBounded.seq (state := s3) (a := (K.toNat / 136) * 163) (b := 238) hloop_rb
    (by change (K.toNat / 136) * 163 + 238 ≤ s2.clock; omega) (fun s4 hr4 hs4_code hs4_clk => ?_)).weaken (by omega)
  have hpost := hstride.2.2.2 (by rw [hr4])
  rw [hr4] at hpost
  dsimp only at hpost
  obtain ⟨w', hw'_i, hw'_n, _, hw'_le, hw'_rem, _⟩ := hpost
  have heval_rem : @evalHOLExact 64 F _ s4.toExact (fun a => Classical.propDecidable (s4.memaddrs a))
      (.op .sub [.var .local (ofString "n"), .var .local (ofString "i")]) = some (.val (.word (K - w'))) := by
    simp [evalHOLExact, evalListHOLExact, hw'_n, hw'_i, wordOpHOL, wordOp, valueIsWord, valueWord]
  refine RunBounded.decWord s4 (ofString "rem") _ (K - w') heval_rem ?_
  let s5 := setVarHOLFinite (ofString "rem") (.val (.word (K - w'))) s4
  have hs5_code : s5.code = originalRuntimeCode := hs4_code.trans hs3_code
  have hs5_rem : s5.locals.lookup (ofString "rem") = some (.val (.word (K - w'))) := by
    simp [s5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hle_bv : w' ≤ K := by rw [BitVec.le_def]; exact hw'_le
  have hrem_nat : (K - w').toNat = K.toNat - w'.toNat := BitVec.toNat_sub_of_le hle_bv
  have hrem_lt : (K - w').toNat < 136 := by
    change K.toNat < w'.toNat + 136 at hw'_rem
    omega
  have hrem_small : (K - w').toNat + 32 < 2 ^ 64 := by omega
  have hmz2 := progBounded_memzero_const none (.var .global (ofString "keccak_pad")) 136 (by decide)
    s5 hs5_code (by change 25 ≤ s4.clock; omega)
  refine (RunBounded.seq (state := s5) (a := 25) (b := 213) hmz2
    (by change 25 + 213 ≤ s4.clock; omega) (fun s6 hr6 hs6_code hs6_clk => ?_)).weaken (by omega)
  have hs6_code' : s6.code = originalRuntimeCode := hs6_code.trans hs5_code
  have hs6_rem : s6.locals.lookup (ofString "rem") = some (.val (.word (K - w'))) := by
    have hpres := evaluate_avoidsLocal_flowing (ofString "rem")
      (.call (some (none, none)) (ofString "memzero") [.var .global (ofString "keccak_pad"), .const 136])
      rfl s5 (by rw [hr6]; exact Or.inl rfl)
    rw [hr6] at hpres
    exact hpres.trans hs5_rem
  have hmc_rem : RunBounded s6
      (.call (some (none, none)) (ofString "memcpy")
        [.var .global (ofString "keccak_pad"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")], .var .local (ofString "rem")])
      25 := by
    have heq_call : evaluateHOLFiniteState s6
        (.call (some (none, none)) (ofString "memcpy")
          [.var .global (ofString "keccak_pad"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")], .var .local (ofString "rem")]) =
      evaluateHOLFiniteState s6
        (.call (some (none, none)) (ofString "memcpy")
          [.var .global (ofString "keccak_pad"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")], .const (K - w')]) := by
      have hlist : evalListHOLFinite s6 (h := fun a => Classical.propDecidable (s6.memaddrs a))
          [.var .global (ofString "keccak_pad"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")], .var .local (ofString "rem")] =
        evalListHOLFinite s6 (h := fun a => Classical.propDecidable (s6.memaddrs a))
          [.var .global (ofString "keccak_pad"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")], .const (K - w')] := by
        rw [evalListHOLFinite_eq_toExact, evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, hs6_rem]
      rw [evaluateHOLFiniteState_call, evaluateHOLFiniteState_call, hlist]
    unfold RunBounded
    rw [heq_call]
    exact (ProgBounded.weaken
      (progBounded_memcpy_const none (.var .global (ofString "keccak_pad"))
        (.op .add [.var .local (ofString "p"), .var .local (ofString "i")]) (K - w') hrem_small)
      (by omega)) s6 hs6_code' (by omega)
  have htail_prog : ProgBounded
      (.seq
        (.storeByte (.op .add [.var .global (ofString "keccak_pad"), .var .local (ofString "rem")]) (.const 1))
        (.seq
          (.storeByte (.op .add [.var .global (ofString "keccak_pad"), .const 135])
            (.op .or [.loadByte (.op .add [.var .global (ofString "keccak_pad"), .const 135]), .const 128]))
          (.seq
            (.call (some (none, none)) (ofString "keccak_absorb_block") [.var .local (ofString "stp"), .var .global (ofString "keccak_pad")])
            (.seq
              (.ite (.cmp .equal (.op .and [.var .local (ofString "out"), .const 7]) (.const 0))
                (.seq
                  (.store (.var .local (ofString "out")) (.load .one (.var .local (ofString "stp"))))
                  (.seq
                    (.store (.op .add [.var .local (ofString "out"), .const 8]) (.load .one (.op .add [.var .local (ofString "stp"), .const 8])))
                    (.seq
                      (.store (.op .add [.var .local (ofString "out"), .const 16]) (.load .one (.op .add [.var .local (ofString "stp"), .const 16])))
                      (.store (.op .add [.var .local (ofString "out"), .const 24]) (.load .one (.op .add [.var .local (ofString "stp"), .const 24]))))))
                (.call (some (none, none)) (ofString "memcpy") [.var .local (ofString "out"), .var .local (ofString "stp"), .const 32]))
              (.return (.const 0))))))
      188 :=
    ProgBounded.weaken
      (ProgBounded.seq (ProgBounded.straight _ rfl)
        (ProgBounded.seq (ProgBounded.straight _ rfl)
          (ProgBounded.seq (ProgBounded.call funBounded_keccak_absorb_block none _)
            (ProgBounded.seq
              (ProgBounded.iteMax _ (ProgBounded.straight _ rfl)
                (progBounded_memcpy_const none _ _ 32 (by decide)))
              (ProgBounded.straight _ rfl)))))
      (by decide)
  exact (RunBounded.seq (state := s6) (a := 25) (b := 188) hmc_rem
    (by change 25 + 188 ≤ s6.clock; omega)
    (fun s7 _ hs7_code hs7_clk => htail_prog s7 (hs7_code.trans hs6_code') hs7_clk)).weaken (by omega)

theorem progBounded_keccak256_exp (destination : Option (VarKind × MlS)) (p sizeExp out : ExpHOL 64)
    (K : BitVec 64) (hsmall : K.toNat + 136 < 2 ^ 64)
    (heval : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) sizeExp = some (.val (.word K))) :
    ProgBounded (.call (some (destination, none)) (ofString "keccak256") [p, sizeExp, out])
      ((K.toNat / 136) * 163 + 272) := by
  intro F state hcode hbudget
  cases hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [p, sizeExp, out] with
  | none =>
    rw [evaluateHOLFiniteState_call, hargs]
    simp
  | some vs =>
    obtain ⟨v1, v3, rfl⟩ := evalListHOLFinite_three_word2 state p sizeExp out K hargs (heval state)
    exact RunBounded.call hargs hbudget (fun body locals rs hfound => by
      rw [hcode] at hfound
      obtain ⟨rfl, hn⟩ := three_arg_lookup_mid originalRuntimeCode.lookup
        (ofString "keccak256") (ofString "p") (ofString "n") (ofString "out")
        (sourceFnBody Guest.Software.guestFn_keccak256)
        (by decide) (by decide) (by decide) lookup_keccak256 hfound
      exact runBounded_keccak256_body (callEntryStateHOLFinite state locals) K hsmall hcode hn
        (by change (K.toNat / 136) * 163 + 271 ≤ state.clock - 1; omega))

theorem progBounded_keccak256_const (destination : Option (VarKind × MlS)) (p out : ExpHOL 64)
    (K : BitVec 64) (hsmall : K.toNat + 136 < 2 ^ 64) :
    ProgBounded (.call (some (destination, none)) (ofString "keccak256") [p, .const K, out])
      ((K.toNat / 136) * 163 + 272) :=
  progBounded_keccak256_exp destination p (.const K) out K hsmall
    (fun _ => by rw [evalHOLFinite_eq_toExact]; rfl)

-- ============================================================================
-- Section 2: Cut2 RLP Functions (guestAst[105..127], 228)
-- ============================================================================

theorem progBounded_rlp_read_length_exp (destination : Option (VarKind × MlS)) (p sizeExp : ExpHOL 64)
    (K : BitVec 64)
    (heval : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) sizeExp = some (.val (.word K))) :
    ProgBounded (.call (some (destination, none)) (ofString "rlp_read_length") [p, sizeExp]) (K.toNat + 2) := by
  intro F state hcode hbudget
  cases hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [p, sizeExp] with
  | none =>
    rw [evaluateHOLFiniteState_call, hargs]
    simp
  | some vs =>
    have hk := heval state
    obtain ⟨v1, rfl⟩ : ∃ v1, vs = [v1, .val (.word K)] := by
      rw [evalListHOLFinite_eq_toExact] at hargs
      rw [evalHOLFinite_eq_toExact] at hk
      simp only [evalListHOLExact] at hargs
      rw [hk] at hargs
      rcases h1 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) p with _ | v1
      · rw [h1] at hargs; cases hargs
      · rw [h1] at hargs; cases hargs; exact ⟨v1, rfl⟩
    exact RunBounded.call hargs hbudget (fun body locals rs hfound => by
      rw [hcode] at hfound
      have hbody := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup
        (ofString "rlp_read_length") _ (sourceFnBody Guest.Software.guestFn_rlp_read_length) body .one rs
        [v1, .val (.word K)] locals lookup_rlp_read_length hfound
      subst hbody
      have hn : locals.lookup (ofString "n") = some (.val (.word K)) := by
        cases v1 with
        | rStruct _ =>
          unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
          split at hfound
          · cases hfound
          · rename_i _ _ _ raw
            simp [lookupCodeHOLExact, lookup_rlp_read_length, shapeOfHOLExact, shapeEqHOL] at raw
        | nStruct _ _ =>
          unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
          split at hfound
          · cases hfound
          · rename_i _ _ _ raw
            simp [lookupCodeHOLExact, lookup_rlp_read_length, shapeOfHOLExact, shapeEqHOL] at raw
        | val wl1 =>
          cases wl1 with
          | word w1 =>
            rw [pan_two_word_lookup originalRuntimeCode.lookup (ofString "rlp_read_length") (ofString "p") (ofString "n")
              (sourceFnBody Guest.Software.guestFn_rlp_read_length) w1 K (by decide) lookup_rlp_read_length] at hfound
            cases hfound
            simp [HolFiniteMapExact.lookup_update, FUPDATE]
      exact runBounded_rlp_read_length_body (callEntryStateHOLFinite state locals) K hcode hn
        (by change K.toNat + 1 ≤ state.clock - 1; omega))

theorem funBounded_rlp_read_length : FunBounded (ofString "rlp_read_length") (2 ^ 64) := by
  refine funBounded_of_guestAst 106 (by rw [guestAst_len]; decide) Guest.Software.guestFn_rlp_read_length (2 ^ 64) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_rlp_read_length,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine ProgBounded.weaken
    (ProgBounded.seq
      (ProgBounded.iteMax _ (ProgBounded.call funBounded_rlp_fail none _) (ProgBounded.straight _ rfl))
      (ProgBounded.dec _ _ _
        (progBounded_varCountedDec_local (ofString "i") (ofString "n") .lower (Or.inr rfl)
          (cost := 0)
          (countedStep_seq_straight _ rfl rfl rfl countedStep_incr)
          rfl
          (ProgBounded.straight _ rfl))))
    (by decide)

def mustExitProg : ProgHOL 64 → Bool
  | .return _ | .raise _ _ | .break | .continue => true
  | .seq first second => mustExitProg first || mustExitProg second
  | .ite _ yes no => mustExitProg yes && mustExitProg no
  | .dec _ _ _ body => mustExitProg body
  | .decCall _ _ _ _ cont => mustExitProg cont
  | _ => false

theorem evaluate_mustExitProg_not_none {F : Type} :
    ∀ (p : ProgHOL 64), mustExitProg p = true →
      ∀ (s : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState s p).1 ≠ none
  | .return val, _, s => by
    rw [evaluateHOLFiniteState_return]
    split
    · simp
    · split <;> simp
  | .raise nm val, _, s => by
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> simp
    · simp
  | .break, _, s => by simp [evaluateHOLFiniteState_break]
  | .continue, _, s => by simp [evaluateHOLFiniteState_continue]
  | .seq a b, hp, s => by
    simp only [mustExitProg, Bool.or_eq_true] at hp
    rw [evaluateHOLFiniteState_seq_line780]
    cases hra : evaluateHOLFiniteState s a with
    | mk r1 mid =>
      cases r1 with
      | none =>
        rcases hp with ha | hb
        · exact False.elim (evaluate_mustExitProg_not_none a ha s (by rw [hra]))
        · dsimp only
          exact evaluate_mustExitProg_not_none b hb mid
      | some _ => simp
  | .ite c yes no, hp, s => by
    simp only [mustExitProg, Bool.and_eq_true] at hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_mustExitProg_not_none no hp.2 s
      · exact evaluate_mustExitProg_not_none yes hp.1 s
    · simp
  | .dec nm sh init body, hp, s => by
    simp only [mustExitProg] at hp
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · simp
    · split
      · dsimp only
        exact evaluate_mustExitProg_not_none body hp _
      · simp
  | .decCall nm sh fn args cont, hp, s => by
    simp only [mustExitProg] at hp
    rw [evaluateHOLFiniteState_decCall_total]
    cases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with
    | none => simp
    | some vs =>
      dsimp only
      cases hlk : lookupCodeHOLFinite s.code.lookup fn vs with
      | none => simp
      | some inst =>
        obtain ⟨bbody, blocals, brs⟩ := inst
        dsimp only
        split
        · simp
        · have hrem := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s blocals) bbody
          cases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s blocals) bbody with
          | mk r1 bpost =>
            rw [hb] at hrem
            have hfix : fixClockHOLFinite (callEntryStateHOLFinite s blocals) (r1, bpost) = (r1, bpost) := by
              simp [fixClockHOLFinite, Nat.not_lt.mpr hrem]
            rw [hfix]
            dsimp only
            rcases r1 with _ | (_ | _ | _ | _ | rv | _ | _)
            all_goals try (simp; done)
            simp only []
            split
            · exact evaluate_mustExitProg_not_none cont hp _
            · simp
  | .skip, hp, _ | .assign _ _ _, hp, _ | .storeByte _ _, hp, _ | .store _ _, hp, _
  | .store32 _ _, hp, _ | .shMemLoad _ _ _ _, hp, _ | .shMemStore _ _ _, hp, _
  | .annot _ _, hp, _ | .primitive _ _ _, hp, _ | .extCall _ _ _ _ _, hp, _
  | .tick, hp, _ | .while _ _, hp, _ | .call _ _ _, hp, _ => by
    simp [mustExitProg] at hp

theorem progBounded_ite_exit (cond : ExpHOL 64) {yes tail : ProgHOL 64} {a b : Nat}
    (hexit : mustExitProg yes = true)
    (hyes : ProgBounded yes a)
    (htail : ProgBounded tail b) :
    ProgBounded (.seq (.ite cond yes .skip) tail) (max a b) := by
  intro F state code budget
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
  split
  · split
    · rw [evaluateHOLFiniteState_skip]
      dsimp only
      have ht := htail state code (by omega)
      exact ⟨by have := ht.1; omega, ht.2.1, ht.2.2⟩
    · have hy := hyes state code (by omega)
      have hne := evaluate_mustExitProg_not_none yes hexit state
      rcases hry : evaluateHOLFiniteState state yes with ⟨ry, sy⟩
      rw [hry] at hy hne
      cases ry with
      | none => exact False.elim (hne rfl)
      | some r =>
        dsimp only at hy ⊢
        exact ⟨by have := hy.1; omega, hy.2.1, hy.2.2⟩
  · simp

theorem funBounded_rlp_item_header : FunBounded (ofString "rlp_item_header") (2 ^ 64 + 4) := by
  refine funBounded_of_guestAst 109 (by rw [guestAst_len]; decide) Guest.Software.guestFn_rlp_item_header (2 ^ 64 + 4) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_rlp_item_header,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact @ProgBounded.weaken _ _ (2 ^ 64 + 4)
    (ProgBounded.seq
      (ProgBounded.iteMax _ (ProgBounded.call funBounded_rlp_fail none _) (ProgBounded.straight _ rfl))
      (ProgBounded.dec _ _ _
        (progBounded_ite_exit _ rfl (ProgBounded.straight _ rfl)
          (progBounded_ite_exit _ rfl
            (ProgBounded.dec _ _ _
              (ProgBounded.seq
                (ProgBounded.iteMax _ (ProgBounded.call funBounded_rlp_fail none _) (ProgBounded.straight _ rfl))
                (ProgBounded.seq
                  (ProgBounded.iteMax _
                    (ProgBounded.iteMax _ (ProgBounded.call funBounded_rlp_fail none _) (ProgBounded.straight _ rfl))
                    (ProgBounded.straight _ rfl))
                  (ProgBounded.straight _ rfl))))
            (progBounded_ite_exit _ rfl
              (ProgBounded.dec _ _ _
                (ProgBounded.seq
                  (ProgBounded.iteMax _ (ProgBounded.call funBounded_rlp_fail none _) (ProgBounded.straight _ rfl))
                  (ProgBounded.decCall funBounded_rlp_read_length _ _ _
                    (ProgBounded.seq
                      (ProgBounded.iteMax _ (ProgBounded.call funBounded_rlp_fail none _) (ProgBounded.straight _ rfl))
                      (ProgBounded.seq
                        (ProgBounded.iteMax _ (ProgBounded.call funBounded_rlp_fail none _) (ProgBounded.straight _ rfl))
                        (ProgBounded.straight _ rfl))))))
              (progBounded_ite_exit _ rfl
                (ProgBounded.dec _ _ _
                  (ProgBounded.seq
                    (ProgBounded.iteMax _ (ProgBounded.call funBounded_rlp_fail none _) (ProgBounded.straight _ rfl))
                    (ProgBounded.straight _ rfl)))
                (ProgBounded.dec _ _ _
                  (ProgBounded.seq
                    (ProgBounded.iteMax _ (ProgBounded.call funBounded_rlp_fail none _) (ProgBounded.straight _ rfl))
                    (ProgBounded.decCall funBounded_rlp_read_length _ _ _
                      (ProgBounded.seq
                        (ProgBounded.iteMax _ (ProgBounded.call funBounded_rlp_fail none _) (ProgBounded.straight _ rfl))
                        (ProgBounded.seq
                          (ProgBounded.iteMax _ (ProgBounded.call funBounded_rlp_fail none _) (ProgBounded.straight _ rfl))
                          (ProgBounded.straight _ rfl))))))))))))
    (by decide)

theorem funBounded_rlp_validate_items (K_body : Nat)
    (h_body : FunBounded (ofString "_rlp_validate_items_body") K_body) :
    FunBounded (ofString "rlp_validate_items") (K_body + 4) := by
  refine funBounded_of_guestAst 111 (by rw [guestAst_len]; decide) Guest.Software.guestFn_rlp_validate_items (K_body + 4) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_rlp_validate_items,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_scratch_mark _ _ _
      (ProgBounded.dec _ _ _
        (ProgBounded.seq
          (ProgBounded.handledCall h_body _ _ none _
            (ProgBounded.seq (ProgBounded.call funBounded_scratch_release none _) (ProgBounded.straight _ rfl)))
          (ProgBounded.seq (ProgBounded.call funBounded_scratch_release none _) (ProgBounded.straight _ rfl)))))
    (by omega)

theorem funBounded_rlp_item_total (K_body : Nat)
    (h_body : FunBounded (ofString "_rlp_validate_items_body") K_body) :
    FunBounded (ofString "rlp_item_total") (2 ^ 64 + K_body + 10) := by
  refine funBounded_of_guestAst 112 (by rw [guestAst_len]; decide) Guest.Software.guestFn_rlp_item_total (2 ^ 64 + K_body + 10) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_rlp_item_total,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_rlp_item_header _ _ _
      (ProgBounded.seq
        (ProgBounded.iteMax _
          (ProgBounded.call (funBounded_rlp_validate_items K_body h_body) none _)
          (ProgBounded.straight _ rfl))
        (ProgBounded.straight _ rfl)))
    (by omega)

theorem funBounded_rlp_item (K_lc : Nat)
    (h_lc : FunBounded (ofString "rlp_list_count") K_lc) :
    FunBounded (ofString "rlp_item") (2 ^ 64 + K_lc + 5) := by
  refine funBounded_of_guestAst 107 (by rw [guestAst_len]; decide) Guest.Software.guestFn_rlp_item (2 ^ 64 + K_lc + 5) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_rlp_item,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  have h1 := ProgBounded.iteMax
    (.cmp .equal (.var .local (ofString "len")) (.const 0))
    (ProgBounded.call funBounded_rlp_fail none [.const 1])
    (ProgBounded.straight _ rfl)
  have hb2 := ProgBounded.dec (ofString "pay_len") .one
    (.op .sub [.var .local (ofString "b0"), .const 128])
    (ProgBounded.seq
      (ProgBounded.iteMax _ (ProgBounded.call funBounded_rlp_fail none _) (ProgBounded.straight _ rfl))
      (ProgBounded.seq
        (ProgBounded.iteMax _
          (ProgBounded.iteMax _ (ProgBounded.call funBounded_rlp_fail none _) (ProgBounded.straight _ rfl))
          (ProgBounded.straight _ rfl))
        (ProgBounded.straight _ rfl)))
  have hb3 := ProgBounded.dec (ofString "ll") .one
    (.op .sub [.var .local (ofString "b0"), .const 183])
    (ProgBounded.seq
      (ProgBounded.iteMax _ (ProgBounded.call funBounded_rlp_fail none _) (ProgBounded.straight _ rfl))
      (ProgBounded.decCall funBounded_rlp_read_length _ _ _
        (ProgBounded.seq
          (ProgBounded.iteMax _ (ProgBounded.call funBounded_rlp_fail none _) (ProgBounded.straight _ rfl))
          (ProgBounded.seq
            (ProgBounded.iteMax _ (ProgBounded.call funBounded_rlp_fail none _) (ProgBounded.straight _ rfl))
            (ProgBounded.straight _ rfl)))))
  have hb4 := ProgBounded.dec (ofString "pay_len") .one
    (.op .sub [.var .local (ofString "b0"), .const 192])
    (ProgBounded.seq
      (ProgBounded.iteMax _ (ProgBounded.call funBounded_rlp_fail none _) (ProgBounded.straight _ rfl))
      (ProgBounded.seq (ProgBounded.call h_lc none _) (ProgBounded.straight _ rfl)))
  have hb5 := ProgBounded.dec (ofString "ll") .one
    (.op .sub [.var .local (ofString "b0"), .const 247])
    (ProgBounded.seq
      (ProgBounded.iteMax _ (ProgBounded.call funBounded_rlp_fail none _) (ProgBounded.straight _ rfl))
      (ProgBounded.decCall funBounded_rlp_read_length _ _ _
        (ProgBounded.seq
          (ProgBounded.iteMax _ (ProgBounded.call funBounded_rlp_fail none _) (ProgBounded.straight _ rfl))
          (ProgBounded.seq
            (ProgBounded.iteMax _ (ProgBounded.call funBounded_rlp_fail none _) (ProgBounded.straight _ rfl))
            (ProgBounded.seq (ProgBounded.call h_lc none _) (ProgBounded.straight _ rfl))))))
  exact @ProgBounded.weaken _ _ (2 ^ 64 + K_lc + 5)
    (ProgBounded.seq h1
      (ProgBounded.dec _ _ _
        (progBounded_ite_exit _ rfl (ProgBounded.straight _ rfl)
          (progBounded_ite_exit _ rfl hb2
            (progBounded_ite_exit _ rfl hb3
              (progBounded_ite_exit _ rfl hb4 hb5))))))
    (by omega)

theorem funBounded_rlp_decode_fully (K_lc : Nat)
    (h_lc : FunBounded (ofString "rlp_list_count") K_lc) :
    FunBounded (ofString "rlp_decode_fully") (2 ^ 64 + K_lc + 7) := by
  refine funBounded_of_guestAst 108 (by rw [guestAst_len]; decide) Guest.Software.guestFn_rlp_decode_fully (2 ^ 64 + K_lc + 7) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_rlp_decode_fully,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall (funBounded_rlp_item K_lc h_lc) _ _ _
      (ProgBounded.seq
        (ProgBounded.iteMax _ (ProgBounded.call funBounded_rlp_fail none _) (ProgBounded.straight _ rfl))
        (ProgBounded.straight _ rfl)))
    (by omega)

theorem funBounded_rlp_item_total_unchecked : FunBounded (ofString "rlp_item_total_unchecked") (2 ^ 64 + 1) := by
  refine funBounded_of_guestAst 114 (by rw [guestAst_len]; decide) Guest.Software.guestFn_rlp_item_total_unchecked (2 ^ 64 + 1) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_rlp_item_total_unchecked,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact @ProgBounded.weaken _ _ (2 ^ 64 + 1)
    (ProgBounded.dec _ _ _
      (progBounded_ite_exit _ rfl (ProgBounded.straight _ rfl)
        (progBounded_ite_exit _ rfl (ProgBounded.straight _ rfl)
          (progBounded_ite_exit _ rfl
            (ProgBounded.dec _ _ _
              (ProgBounded.decCall funBounded_rlp_read_length _ _ _ (ProgBounded.straight _ rfl)))
            (progBounded_ite_exit _ rfl (ProgBounded.straight _ rfl)
              (ProgBounded.dec _ _ _
                (ProgBounded.decCall funBounded_rlp_read_length _ _ _ (ProgBounded.straight _ rfl))))))))
    (by decide)

theorem funBounded_rlp_list_to_slices (K_lc : Nat)
    (h_lc : FunBounded (ofString "rlp_list_count") K_lc) :
    FunBounded (ofString "rlp_list_to_slices") (K_lc + 3 + (2 ^ 64 - 1) * (2 ^ 64 + 3)) := by
  refine funBounded_of_guestAst 115 (by rw [guestAst_len]; decide) Guest.Software.guestFn_rlp_list_to_slices
    (K_lc + 3 + (2 ^ 64 - 1) * (2 ^ 64 + 3)) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_rlp_list_to_slices,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine ProgBounded.weaken
    (ProgBounded.decCall h_lc _ _ _
      (ProgBounded.decCall funBounded_alloc _ _ _
        (progBounded_varCountedDec2_local (ofString "i") (ofString "off") (ofString "count") .one (.const 0)
          .lower (Or.inr rfl) (by decide)
          (cost := 2 ^ 64 + 2)
          (countedStep_decCall _ _ _ _ (by decide) funBounded_rlp_item_total_unchecked
            (countedStep_seq_straight _ rfl rfl rfl
              (countedStep_seq_straight _ rfl rfl rfl
                (countedStep_seq_straight _ rfl rfl rfl countedStep_incr))))
          rfl
          (ProgBounded.straight _ rfl))))
    (by omega)

theorem funBounded_rlp_bytes_to_word : FunBounded (ofString "rlp_bytes_to_word") (2 ^ 64 + 3) := by
  refine funBounded_of_guestAst 116 (by rw [guestAst_len]; decide) Guest.Software.guestFn_rlp_bytes_to_word
    (2 ^ 64 + 3) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_rlp_bytes_to_word,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.seq
      (ProgBounded.iteMax _ (ProgBounded.call funBounded_rlp_fail none _) (ProgBounded.straight _ rfl))
      (ProgBounded.seq
        (ProgBounded.iteMax _ (ProgBounded.call funBounded_rlp_fail none _) (ProgBounded.straight _ rfl))
        (ProgBounded.dec _ _ _
          (progBounded_varCountedDec_local (ofString "i") (ofString "n") .lower (Or.inr rfl)
            (cost := 0)
            (countedStep_seq_straight _ rfl rfl rfl countedStep_incr)
            rfl
            (ProgBounded.straight _ rfl)))))
    (by decide)

theorem funBounded_rlp_check_uint_bytes : FunBounded (ofString "rlp_check_uint_bytes") 4 := by
  refine funBounded_of_guestAst 117 (by rw [guestAst_len]; decide) Guest.Software.guestFn_rlp_check_uint_bytes
    4 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_rlp_check_uint_bytes,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.seq
      (ProgBounded.iteMax _ (ProgBounded.call funBounded_rlp_fail none _) (ProgBounded.straight _ rfl))
      (ProgBounded.seq
        (ProgBounded.iteMax _ (ProgBounded.call funBounded_rlp_fail none _) (ProgBounded.straight _ rfl))
        (ProgBounded.straight _ rfl)))
    (by decide)

private def rlpBeLenRank (w : BitVec 64) : Nat :=
  if w = 0 then 0
  else if w.toNat < 2 ^ 8 then 1
  else if w.toNat < 2 ^ 16 then 2
  else if w.toNat < 2 ^ 24 then 3
  else if w.toNat < 2 ^ 32 then 4
  else if w.toNat < 2 ^ 40 then 5
  else if w.toNat < 2 ^ 48 then 6
  else if w.toNat < 2 ^ 56 then 7
  else 8

private theorem rlpBeLenRank_le_eight (w : BitVec 64) : rlpBeLenRank w ≤ 8 := by
  unfold rlpBeLenRank
  repeat' (split; try omega)

private theorem rlpBeLenRank_zero_iff (w : BitVec 64) : rlpBeLenRank w = 0 ↔ w = 0 := by
  unfold rlpBeLenRank
  by_cases h : w = 0
  · simp [h]
  · simp only [h, if_false]
    constructor
    · intro h0
      repeat' (split at h0; try cases h0)
    · intro h0; exact absurd h0 h

private theorem rlpBeLenRank_ushift8 {w : BitVec 64} {k : Nat}
    (hr : rlpBeLenRank w = k + 1) : rlpBeLenRank (w >>> 8) ≤ k := by
  have hw0 : w ≠ 0 := by
    intro h0; subst h0; simp [rlpBeLenRank] at hr
  have hshift : (w >>> 8).toNat = w.toNat / 256 := by
    rw [BitVec.toNat_ushiftRight]
    rfl
  have hwlt : w.toNat < 2 ^ 64 := w.isLt
  unfold rlpBeLenRank at hr ⊢
  rw [if_neg hw0] at hr
  by_cases h1 : w.toNat < 2 ^ 8
  · rw [if_pos h1] at hr
    have hk : k = 0 := by omega
    subst hk
    have hz : w >>> 8 = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [hshift]; simp; omega
    simp [hz]
  · rw [if_neg h1] at hr
    have hnz : w >>> 8 ≠ 0 := by
      intro hz
      have := congrArg BitVec.toNat hz
      rw [hshift] at this
      simp at this
      omega
    rw [if_neg hnz]
    by_cases h2 : w.toNat < 2 ^ 16
    · rw [if_pos h2] at hr
      have hsub : (w >>> 8).toNat < 2 ^ 8 := by rw [hshift]; omega
      rw [if_pos hsub]; omega
    · rw [if_neg h2] at hr
      by_cases h3 : w.toNat < 2 ^ 24
      · rw [if_pos h3] at hr
        have hsub : (w >>> 8).toNat < 2 ^ 16 := by rw [hshift]; omega
        by_cases hs1 : (w >>> 8).toNat < 2 ^ 8 <;> simp [hs1, hsub] <;> omega
      · rw [if_neg h3] at hr
        by_cases h4 : w.toNat < 2 ^ 32
        · rw [if_pos h4] at hr
          have hsub : (w >>> 8).toNat < 2 ^ 24 := by rw [hshift]; omega
          by_cases hs1 : (w >>> 8).toNat < 2 ^ 8
          · simp [hs1]; omega
          · by_cases hs2 : (w >>> 8).toNat < 2 ^ 16 <;> simp [hs1, hs2, hsub] <;> omega
        · rw [if_neg h4] at hr
          by_cases h5 : w.toNat < 2 ^ 40
          · rw [if_pos h5] at hr
            have hsub : (w >>> 8).toNat < 2 ^ 32 := by rw [hshift]; omega
            by_cases hs1 : (w >>> 8).toNat < 2 ^ 8
            · simp [hs1]; omega
            · by_cases hs2 : (w >>> 8).toNat < 2 ^ 16
              · simp [hs1, hs2]; omega
              · by_cases hs3 : (w >>> 8).toNat < 2 ^ 24 <;> simp [hs1, hs2, hs3, hsub] <;> omega
          · rw [if_neg h5] at hr
            by_cases h6 : w.toNat < 2 ^ 48
            · rw [if_pos h6] at hr
              have hsub : (w >>> 8).toNat < 2 ^ 40 := by rw [hshift]; omega
              by_cases hs1 : (w >>> 8).toNat < 2 ^ 8
              · simp [hs1]; omega
              · by_cases hs2 : (w >>> 8).toNat < 2 ^ 16
                · simp [hs1, hs2]; omega
                · by_cases hs3 : (w >>> 8).toNat < 2 ^ 24
                  · simp [hs1, hs2, hs3]; omega
                  · by_cases hs4 : (w >>> 8).toNat < 2 ^ 32 <;> simp [hs1, hs2, hs3, hs4, hsub] <;> omega
            · rw [if_neg h6] at hr
              by_cases h7 : w.toNat < 2 ^ 56
              · rw [if_pos h7] at hr
                have hsub : (w >>> 8).toNat < 2 ^ 48 := by rw [hshift]; omega
                by_cases hs1 : (w >>> 8).toNat < 2 ^ 8
                · simp [hs1]; omega
                · by_cases hs2 : (w >>> 8).toNat < 2 ^ 16
                  · simp [hs1, hs2]; omega
                  · by_cases hs3 : (w >>> 8).toNat < 2 ^ 24
                    · simp [hs1, hs2, hs3]; omega
                    · by_cases hs4 : (w >>> 8).toNat < 2 ^ 32
                      · simp [hs1, hs2, hs3, hs4]; omega
                      · by_cases hs5 : (w >>> 8).toNat < 2 ^ 40 <;> simp [hs1, hs2, hs3, hs4, hs5, hsub] <;> omega
              · rw [if_neg h7] at hr
                have hsub : (w >>> 8).toNat < 2 ^ 56 := by rw [hshift]; omega
                by_cases hs1 : (w >>> 8).toNat < 2 ^ 8
                · simp [hs1]; omega
                · by_cases hs2 : (w >>> 8).toNat < 2 ^ 16
                  · simp [hs1, hs2]; omega
                  · by_cases hs3 : (w >>> 8).toNat < 2 ^ 24
                    · simp [hs1, hs2, hs3]; omega
                    · by_cases hs4 : (w >>> 8).toNat < 2 ^ 32
                      · simp [hs1, hs2, hs3, hs4]; omega
                      · by_cases hs5 : (w >>> 8).toNat < 2 ^ 40
                        · simp [hs1, hs2, hs3, hs4, hs5]; omega
                        · by_cases hs6 : (w >>> 8).toNat < 2 ^ 48 <;> simp [hs1, hs2, hs3, hs4, hs5, hs6, hsub] <;> omega

theorem funBounded_rlp_be_len : FunBounded (ofString "rlp_be_len") 8 := by
  refine funBounded_of_guestAst 118 (by rw [guestAst_len]; decide) Guest.Software.guestFn_rlp_be_len 8 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_rlp_be_len,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  intro F state code budget
  rw [evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true]
  let s0 := setVarHOLFinite (ofString "n") (.val (.word 0)) state
  have hs0_code : s0.code = originalRuntimeCode := code
  let cond : ExpHOL 64 := .cmp .notEqual (.var .local (ofString "v")) (.const 0)
  let body : ProgHOL 64 :=
    .seq (.assign .local (ofString "v") (.shift .lsr (.var .local (ofString "v")) (.const 8)))
         (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const 1]))
  let Rank : ∀ {G : Type}, PanSemStateFiniteExact 64 G → Nat → Prop :=
    fun s r => ∃ vw : BitVec 64, s.locals.lookup (ofString "v") = some (.val (.word vw)) ∧ rlpBeLenRank vw = r
  have hexit : ∀ {G : Type} (s : PanSemStateFiniteExact 64 G), Rank s 0 → ∀ w : BitVec 64,
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) cond = some (.val (.word w)) → w = 0 := by
    intro G s ⟨vw, hvw, hr0⟩ w heval
    have hzero : vw = 0 := (rlpBeLenRank_zero_iff vw).mp hr0
    subst hzero
    rw [evalHOLFinite_eq_toExact] at heval
    simp [cond, evalHOLExact, hvw, Compiler.Encoders.Asm.wordCmpHOL] at heval
    exact heval.symm
  have hstep : ∀ {G : Type} (s : PanSemStateFiniteExact 64 G) (k : Nat) (w : BitVec 64), s.code = originalRuntimeCode →
      Rank s (k + 1) →
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) cond = some (.val (.word w)) →
      w ≠ 0 → 0 + 1 ≤ s.clock →
      s.clock - 1 ≤ (evaluateHOLFiniteState (decClockHOLFinite s) body).2.clock + 0 ∧
        (evaluateHOLFiniteState (decClockHOLFinite s) body).2.clock ≤ s.clock - 1 ∧
        (evaluateHOLFiniteState (decClockHOLFinite s) body).1 ≠ some .timeOut ∧
        ((evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none ∨
            (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = some .continue →
          ∃ m, m ≤ k ∧ Rank (evaluateHOLFiniteState (decClockHOLFinite s) body).2 m ∧
            (evaluateHOLFiniteState (decClockHOLFinite s) body).2.code = s.code) ∧
        ((evaluateHOLFiniteState (decClockHOLFinite s) body).1 = some .break → False ∧
          ∃ m, Rank (evaluateHOLFiniteState (decClockHOLFinite s) body).2 m ∧
            (evaluateHOLFiniteState (decClockHOLFinite s) body).2.code = s.code) := by
    intro G s k w scode ⟨vw, hvw, hrk⟩ _ _ sclk
    have hbody_sl : ProgBounded body 0 := ProgBounded.straight body rfl
    have hbnd := hbody_sl (decClockHOLFinite s) scode (by simp)
    have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata (decClockHOLFinite s) body
    have hv_dec : (decClockHOLFinite s).locals.lookup (ofString "v") = some (.val (.word vw)) := hvw
    have ha1 : evaluateHOLFiniteState (decClockHOLFinite s)
        (.assign .local (ofString "v") (.shift .lsr (.var .local (ofString "v")) (.const 8))) =
        (none, setVarHOLFinite (ofString "v") (.val (.word (vw >>> 8))) (decClockHOLFinite s)) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, hv_dec, isValidValueHOLExact,
        lookupKvarHOLExact, shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, wordShiftHOL]
    rcases hr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨res, post⟩
    rw [hr] at hbnd hmeta
    dsimp only at hbnd hmeta
    obtain ⟨sp, kp, sf⟩ := hbnd
    change s.clock - 1 ≤ post.clock + 0 at sp
    change post.clock ≤ s.clock - 1 at kp
    refine ⟨sp, kp, sf, ?_, ?_⟩
    · intro hflow
      rw [evaluateHOLFiniteState_seq_line780, ha1] at hr
      dsimp only at hr
      let s_mid := setVarHOLFinite (ofString "v") (.val (.word (vw >>> 8))) (decClockHOLFinite s)
      have hpres_v := evaluate_avoidsLocal_flowing (ofString "v")
        (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const 1]))
        (by decide) s_mid
      rw [hr] at hpres_v
      have hflow' : Flowing res := by
        rcases hflow with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inr rfl)
      have hv_post : post.locals.lookup (ofString "v") = some (.val (.word (vw >>> 8))) := by
        rw [hpres_v hflow']
        simp [s_mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      exact ⟨rlpBeLenRank (vw >>> 8), rlpBeLenRank_ushift8 hrk, ⟨vw >>> 8, hv_post, rfl⟩, hmeta.1⟩
    · intro hbrk
      have hnb := evaluate_noTopBreak body rfl (decClockHOLFinite s)
      rw [hr] at hnb
      exact absurd hbrk hnb
  have hloop : s0.clock ≤ (evaluateHOLFiniteState s0 (.while cond body)).2.clock + 8 ∧
      (evaluateHOLFiniteState s0 (.while cond body)).2.clock ≤ s0.clock ∧
      (evaluateHOLFiniteState s0 (.while cond body)).1 ≠ some .timeOut := by
    cases hv0 : s0.locals.lookup (ofString "v") with
    | none =>
      rw [evaluateHOLFiniteState_while_total]
      have hc : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a)) cond = none := by
        rw [evalHOLFinite_eq_toExact]; simp [cond, evalHOLExact, hv0]
      rw [hc]; simp
    | some vval =>
      cases vval with
      | rStruct _ =>
        rw [evaluateHOLFiniteState_while_total]
        have hc : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a)) cond = none := by
          rw [evalHOLFinite_eq_toExact]; simp [cond, evalHOLExact, hv0]
        rw [hc]; simp
      | nStruct _ _ =>
        rw [evaluateHOLFiniteState_while_total]
        have hc : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a)) cond = none := by
          rw [evalHOLFinite_eq_toExact]; simp [cond, evalHOLExact, hv0]
        rw [hc]; simp
      | val wl =>
        cases wl with
        | word vw =>
          have hr_le : rlpBeLenRank vw ≤ 8 := rlpBeLenRank_le_eight vw
          have hout := rankedWhile_run cond body 0 Rank False hexit hstep (rlpBeLenRank vw) s0 hs0_code
            ⟨vw, hv0, rfl⟩ (by change rlpBeLenRank vw * 1 ≤ state.clock; omega)
          exact ⟨by have := hout.1; omega, hout.2.1, hout.2.2.1⟩
  have hmeta0 := PanRunBounded.evaluateHOLFiniteState_metadata s0 (.while cond body)
  change state.clock ≤ (evaluateHOLFiniteState s0 (.seq (.while cond body) (.return (.var .local (ofString "n"))))).2.clock + 8 ∧
    (evaluateHOLFiniteState s0 (.seq (.while cond body) (.return (.var .local (ofString "n"))))).2.clock ≤ state.clock ∧
    (evaluateHOLFiniteState s0 (.seq (.while cond body) (.return (.var .local (ofString "n"))))).1 ≠ some .timeOut
  rw [evaluateHOLFiniteState_seq_line780]
  rcases lr : evaluateHOLFiniteState s0 (.while cond body) with ⟨res, mid⟩
  rw [lr] at hloop hmeta0
  dsimp only at hloop hmeta0
  obtain ⟨sp, kp, sf⟩ := hloop
  change state.clock ≤ mid.clock + 8 at sp
  change mid.clock ≤ state.clock at kp
  cases res with
  | none =>
    dsimp only
    obtain ⟨t1, t2, t3⟩ := (ProgBounded.straight (.return (.var .local (ofString "n"))) rfl) mid
      (hmeta0.1.trans code) (by simp)
    exact ⟨by omega, by omega, t3⟩
  | some r =>
    dsimp only
    exact ⟨sp, kp, sf⟩

-- Downward-counting loop helper for `rlp_put_be`: `while (0 < i) { i := i - 1; ... }`
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

private theorem decStep_decr_seq_straight {counter : MlS} (rest : ProgHOL 64)
    (hs : extStraightLine rest = true)
    (ha : avoidsLocal counter rest = true)
    (hn : noTopContinue rest = true) :
    DecStep counter (.seq (.assign .local counter (.op .sub [.var .local counter, .const 1])) rest) 0 := by
  intro F state code w atC _
  have run1 : evaluateHOLFiniteState state (.assign .local counter (.op .sub [.var .local counter, .const 1])) =
      (none, setVarHOLFinite counter (.val (.word (w - 1))) state) := by
    simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, atC, wordOpHOL, wordOp,
      valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
      shapeOfHOLExact, shapeEqHOL]
  let mid := setVarHOLFinite counter (.val (.word (w - 1))) state
  have hmid_code : mid.code = originalRuntimeCode := code
  have hmid_c : mid.locals.lookup counter = some (.val (.word (w - 1))) := by
    simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hbnd := (ProgBounded.straight rest hs) mid hmid_code (by simp)
  have hframe := evaluate_avoidsLocal_flowing counter rest ha mid
  have hnc := evaluate_noTopContinue rest hn mid
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata mid rest
  rw [evaluateHOLFiniteState_seq_line780, run1]
  dsimp only
  rcases hr : evaluateHOLFiniteState mid rest with ⟨res, post⟩
  rw [hr] at hbnd hframe hnc hmeta
  dsimp only at hbnd hframe hnc hmeta
  obtain ⟨sp, kp, sf⟩ := hbnd
  change state.clock ≤ post.clock + 0 at sp
  change post.clock ≤ state.clock at kp
  refine ⟨sp, kp, sf, hnc, fun normal => ?_⟩
  rw [hframe (by rw [normal]; exact Or.inl rfl)]
  exact ⟨hmid_c, hmeta.1⟩

private theorem downWhile_run_step (counter : MlS) {body : ProgHOL 64} {cost : Nat}
    (counted : DecStep counter body cost) :
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
    have condition : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
        (.cmp .lower (.const 0) (.var .local counter)) =
        some (.val (.word (if 0 < w.toNat then 1 else 0))) := by
      rw [evalHOLFinite_eq_toExact]
      simp only [evalHOLExact, atCounter, Compiler.Encoders.Asm.wordCmpHOL]
      by_cases lt : 0 < w.toNat <;> simp [lt, BitVec.lt_def]
    rw [evaluateHOLFiniteState_while_total, condition]
    by_cases lt : 0 < w.toNat
    · rw [if_pos lt]
      simp only [show (1 : BitVec 64) ≠ 0 by decide, if_true, ne_eq, not_false_eq_true]
      have positiveRank : 0 < n := by omega
      have oneIter : cost + 1 ≤ n * (cost + 1) := Nat.le_mul_of_pos_left _ positiveRank
      have clock : state.clock ≠ 0 := by omega
      rw [if_neg clock, fixClockHOLFinite_evaluateState]
      have stepRun := counted (decClockHOLFinite state) code w atCounter (by change cost ≤ state.clock - 1; omega)
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
          have natural : (w - 1).toNat = w.toNat - 1 := by rw [BitVec.toNat_sub_of_le hle, one_toNat]
          have hmul : (n - 1) * (cost + 1) + (cost + 1) = n * (cost + 1) := by
            have hsucc : n - 1 + 1 = n := by omega
            calc (n - 1) * (cost + 1) + (cost + 1) = (n - 1 + 1) * (cost + 1) := by rw [Nat.add_mul, Nat.one_mul]
              _ = n * (cost + 1) := by rw [hsucc]
          obtain ⟨t1, t2, t3⟩ := ih (n - 1) (by omega) middle (nextCode.trans code) (w - 1) nextCounter
            (by rw [natural]; omega) (by omega)
          exact ⟨by omega, by omega, t3⟩
        | some r =>
          cases r with
          | «continue» => exact absurd rfl noCont
          | «break» => exact ⟨by simp; omega, by simp; omega, by simp⟩
          | timeOut => exact absurd rfl safe
          | _ => exact ⟨by simp; omega, by simp; omega, by simp⟩
    · rw [if_neg lt]
      simp

private theorem lookup_rlp_put_be :
    originalRuntimeCode.lookup (ofString "rlp_put_be") =
      some ([(ofString "dst", .one), (ofString "v", .one), (ofString "n", .one)],
            sourceFnBody Guest.Software.guestFn_rlp_put_be, .one) :=
  lookup_of_guestAst_getElem 119 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_put_be) rfl

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
  refine RunBounded.decWord state (ofString "i") (.var .local (ofString "n")) K
    (by simp [evalHOLExact, atN]) ?_
  let s0 := setVarHOLFinite (ofString "i") (.val (.word K)) state
  have hs0_code : s0.code = originalRuntimeCode := hcode
  have hs0_i : s0.locals.lookup (ofString "i") = some (.val (.word K)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hstep : DecStep (ofString "i")
      (.seq
        (.assign .local (ofString "i") (.op .sub [.var .local (ofString "i"), .const 1]))
        (.seq
          (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) (.var .local (ofString "v")))
          (.assign .local (ofString "v") (.shift .lsr (.var .local (ofString "v")) (.const 8)))))
      0 :=
    decStep_decr_seq_straight _ rfl rfl rfl
  have hloop := downWhile_run_step (ofString "i") hstep K.toNat s0 hs0_code K hs0_i (le_refl _)
    (by simp only [Nat.zero_add, Nat.mul_one]; exact hbudget)
  simp only [Nat.zero_add, Nat.mul_one] at hloop
  exact (RunBounded.seq hloop (a := K.toNat) (b := 0)
    (by change K.toNat + 0 ≤ state.clock; omega)
    (fun next _ nextCode nextBudget =>
      (ProgBounded.straight (.return (.const 0)) rfl) next (nextCode.trans hs0_code) nextBudget)).weaken (by omega)

private theorem three_arg_lookup_last (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
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

private theorem evalListHOLFinite_three_word3_local {F : Type}
    (state : PanSemStateFiniteExact 64 F) (e1 e2 e3 : ExpHOL 64) (K : BitVec 64) {vs : List (ValueHOL 64)}
    (hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [e1, e2, e3] = some vs)
    (hk : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) e3 = some (.val (.word K))) :
    ∃ v1 v2, vs = [v1, v2, .val (.word K)] := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  rw [evalHOLFinite_eq_toExact] at hk
  simp only [evalListHOLExact] at hargs
  rw [hk] at hargs
  rcases h1 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) e1 with _ | v1
  · rw [h1] at hargs; cases hargs
  · rw [h1] at hargs
    rcases h2 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) e2 with _ | v2
    · rw [h2] at hargs; cases hargs
    · rw [h2] at hargs; cases hargs; exact ⟨v1, v2, rfl⟩

theorem progBounded_rlp_put_be_exp (destination : Option (VarKind × MlS)) (dst v sizeExp : ExpHOL 64)
    (K : BitVec 64)
    (heval : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) sizeExp = some (.val (.word K))) :
    ProgBounded (.call (some (destination, none)) (ofString "rlp_put_be") [dst, v, sizeExp]) (K.toNat + 1) := by
  intro F state hcode hbudget
  cases hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [dst, v, sizeExp] with
  | none =>
    rw [evaluateHOLFiniteState_call, hargs]; simp
  | some vs =>
    obtain ⟨v1, v2, rfl⟩ := evalListHOLFinite_three_word3_local state dst v sizeExp K hargs (heval state)
    exact RunBounded.call hargs hbudget (fun body locals rs hfound => by
      rw [hcode] at hfound
      obtain ⟨rfl, hn⟩ := three_arg_lookup_last originalRuntimeCode.lookup
        (ofString "rlp_put_be") (ofString "dst") (ofString "v") (ofString "n")
        (sourceFnBody Guest.Software.guestFn_rlp_put_be)
        (by decide) (by decide) (by decide) lookup_rlp_put_be hfound
      exact runBounded_rlp_put_be_body (callEntryStateHOLFinite state locals) K hcode hn
        (by change K.toNat ≤ state.clock - 1; omega))

theorem funBounded_rlp_put_be : FunBounded (ofString "rlp_put_be") (2 ^ 64 - 1) := by
  refine funBounded_of_guestAst 119 (by rw [guestAst_len]; decide) Guest.Software.guestFn_rlp_put_be (2 ^ 64 - 1) rfl ?_
  intro F state code budget
  cases hn : state.locals.lookup (ofString "n") with
  | none =>
    dsimp only [extractFn, Guest.Software.guestFn_rlp_put_be,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
    rw [evaluateHOLFiniteState_dec_total]
    simp [evalHOLExact, hn]
  | some nval =>
    cases nval with
    | rStruct _ =>
      dsimp only [extractFn, Guest.Software.guestFn_rlp_put_be,
        InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
      rw [evaluateHOLFiniteState_dec_total]
      simp [evalHOLExact, hn, shapeOfHOLExact, shapeEqHOL]
    | nStruct _ _ =>
      dsimp only [extractFn, Guest.Software.guestFn_rlp_put_be,
        InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
      rw [evaluateHOLFiniteState_dec_total]
      simp [evalHOLExact, hn, shapeOfHOLExact, shapeEqHOL]
    | val wl =>
      cases wl with
      | word K =>
        have hklt : K.toNat ≤ 2 ^ 64 - 1 := by have := K.isLt; omega
        exact (runBounded_rlp_put_be_body state K code hn (by omega)).weaken hklt

theorem funBounded_rlp_header_len : FunBounded (ofString "rlp_header_len") 9 := by
  refine funBounded_of_guestAst 121 (by rw [guestAst_len]; decide) Guest.Software.guestFn_rlp_header_len 9 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_rlp_header_len,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.seq
      (ProgBounded.iteMax _ (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl))
      (ProgBounded.decCall funBounded_rlp_be_len _ _ _ (ProgBounded.straight _ rfl)))
    (by decide)

theorem funBounded_rlp_bytes_encoded_len : FunBounded (ofString "rlp_bytes_encoded_len") 10 := by
  refine funBounded_of_guestAst 125 (by rw [guestAst_len]; decide) Guest.Software.guestFn_rlp_bytes_encoded_len 10 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_rlp_bytes_encoded_len,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.seq
      (ProgBounded.iteMax _ (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl))
      (ProgBounded.decCall funBounded_rlp_header_len _ _ _ (ProgBounded.straight _ rfl)))
    (by decide)

theorem funBounded_rlp_list_header_len : FunBounded (ofString "rlp_list_header_len") 10 := by
  refine funBounded_of_guestAst 126 (by rw [guestAst_len]; decide) Guest.Software.guestFn_rlp_list_header_len 10 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_rlp_list_header_len,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.tail funBounded_rlp_header_len _

theorem funBounded_rlp_word_encoded_len : FunBounded (ofString "rlp_word_encoded_len") 9 := by
  refine funBounded_of_guestAst 127 (by rw [guestAst_len]; decide) Guest.Software.guestFn_rlp_word_encoded_len 9 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_rlp_word_encoded_len,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.seq
      (ProgBounded.iteMax _ (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl))
      (ProgBounded.decCall funBounded_rlp_be_len _ _ _ (ProgBounded.straight _ rfl)))
    (by decide)

theorem funBounded_rlp_write_header : FunBounded (ofString "rlp_write_header") (2 ^ 64 + 9) := by
  refine funBounded_of_guestAst 120 (by rw [guestAst_len]; decide) Guest.Software.guestFn_rlp_write_header (2 ^ 64 + 9) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_rlp_write_header,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.seq
      (ProgBounded.iteMax _ (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl))
      (ProgBounded.decCall funBounded_rlp_be_len _ _ _
        (ProgBounded.seq (ProgBounded.straight _ rfl)
          (ProgBounded.seq (ProgBounded.call funBounded_rlp_put_be none _) (ProgBounded.straight _ rfl)))))
    (by decide)

theorem funBounded_rlp_encode_word : FunBounded (ofString "rlp_encode_word") (2 ^ 64 + 9) := by
  refine funBounded_of_guestAst 123 (by rw [guestAst_len]; decide) Guest.Software.guestFn_rlp_encode_word (2 ^ 64 + 9) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_rlp_encode_word,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.seq
      (ProgBounded.iteMax _ (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl))
      (ProgBounded.seq
        (ProgBounded.iteMax _ (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl))
        (ProgBounded.decCall funBounded_rlp_be_len _ _ _
          (ProgBounded.seq (ProgBounded.straight _ rfl)
            (ProgBounded.seq (ProgBounded.call funBounded_rlp_put_be none _) (ProgBounded.straight _ rfl))))))
    (by decide)

theorem funBounded_rlp_encode_list_header : FunBounded (ofString "rlp_encode_list_header") (2 ^ 64 + 10) := by
  refine funBounded_of_guestAst 124 (by rw [guestAst_len]; decide) Guest.Software.guestFn_rlp_encode_list_header (2 ^ 64 + 10) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_rlp_encode_list_header,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.tail funBounded_rlp_write_header _

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
    (hbudget : K.toNat / 8 + 2 ^ 64 + 18 ≤ state.clock) :
    RunBounded state (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes) (K.toNat / 8 + 2 ^ 64 + 18) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_encode_bytes,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  let p_ite : ProgHOL 64 :=
    .ite (.cmp .equal (.var .local (ofString "n")) (.const 1))
      (.dec (ofString "b") .one (.loadByte (.var .local (ofString "src")))
        (.ite (.cmp .lower (.var .local (ofString "b")) (.const 128))
          (.seq (.storeByte (.var .local (ofString "dst")) (.var .local (ofString "b"))) (.return (.const 1)))
          .skip))
      .skip
  have h1 := (ProgBounded.straight p_ite rfl) state hcode (by simp)
  refine (RunBounded.seq (state := state) (a := 0) (b := K.toNat / 8 + 2 ^ 64 + 18) h1
    (by omega) (fun s1 hr1 hs1_code hs1_clk => ?_)).weaken (by omega)
  have hs1_code' : s1.code = originalRuntimeCode := hs1_code.trans hcode
  have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word K)) := by
    have hpres := evaluate_avoidsLocal_flowing (ofString "n") p_ite (by decide) state (by rw [hr1]; exact Or.inl rfl)
    rw [hr1] at hpres
    exact hpres.trans atN
  cases hargs : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
      [.var .local (ofString "dst"), .const 128, .var .local (ofString "n")] with
  | none =>
    unfold RunBounded
    rw [evaluateHOLFiniteState_decCall_args_none s1 _ _ _ _ _ hargs]
    simp
  | some vs =>
    have h := RunBounded.decCall (state := s1) (name := ofString "h") (shape := .one)
      (function := ofString "rlp_write_header")
      (bodyCost := 2 ^ 64 + 9) (tailCost := K.toNat / 8 + 8)
      hargs (by omega)
      (fun body locals rs hfound => by
        have hbnd := ProgBounded.bodies_of_fun funBounded_rlp_write_header s1 hs1_code' (by omega)
          vs body locals rs hfound
        have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s1 locals) body
        refine ⟨hbnd, ?_⟩
        intro value post hran hpost_clk
        rw [hran] at hmeta
        let s2 := setVarHOLFinite (ofString "h") value { post with locals := s1.locals }
        have hs2_code : s2.code = originalRuntimeCode := hmeta.1.trans hs1_code'
        have hs2_n : s2.locals.lookup (ofString "n") = some (.val (.word K)) := by
          have hne : ofString "h" ≠ ofString "n" := by decide
          simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hs1_n]
        have hmc : RunBounded s2
            (.call (some (none, none)) (ofString "memcpy")
              [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
               .var .local (ofString "src"),
               .var .local (ofString "n")])
            (K.toNat / 8 + 8) := by
          have heq_call : evaluateHOLFiniteState s2
              (.call (some (none, none)) (ofString "memcpy")
                [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
                 .var .local (ofString "src"),
                 .var .local (ofString "n")]) =
            evaluateHOLFiniteState s2
              (.call (some (none, none)) (ofString "memcpy")
                [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
                 .var .local (ofString "src"),
                 .const K]) := by
            have hlist : evalListHOLFinite s2 (h := fun a => Classical.propDecidable (s2.memaddrs a))
                [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
                 .var .local (ofString "src"),
                 .var .local (ofString "n")] =
              evalListHOLFinite s2 (h := fun a => Classical.propDecidable (s2.memaddrs a))
                [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
                 .var .local (ofString "src"),
                 .const K] := by
              rw [evalListHOLFinite_eq_toExact, evalListHOLFinite_eq_toExact]
              simp [evalListHOLExact, evalHOLExact, hs2_n]
            rw [evaluateHOLFiniteState_call, evaluateHOLFiniteState_call, hlist]
          unfold RunBounded
          rw [heq_call]
          exact progBounded_memcpy_const none _ _ K hsmall s2 hs2_code hpost_clk
        exact (RunBounded.seq (state := s2) (a := K.toNat / 8 + 8) (b := 0) hmc
          (by change K.toNat / 8 + 8 + 0 ≤ post.clock; omega)
          (fun s3 _ hs3_code hs3_clk =>
            (ProgBounded.straight (.return (.op .add [.var .local (ofString "h"), .var .local (ofString "n")])) rfl)
              s3 (hs3_code.trans hs2_code) hs3_clk)).weaken (by omega))
    exact h.weaken (by omega)

theorem progBounded_rlp_encode_bytes_exp (destination : Option (VarKind × MlS)) (dst src sizeExp : ExpHOL 64)
    (K : BitVec 64) (hsmall : K.toNat + 32 < 2 ^ 64)
    (heval : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) sizeExp = some (.val (.word K))) :
    ProgBounded (.call (some (destination, none)) (ofString "rlp_encode_bytes") [dst, src, sizeExp])
      (K.toNat / 8 + 2 ^ 64 + 19) := by
  intro F state hcode hbudget
  cases hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [dst, src, sizeExp] with
  | none =>
    rw [evaluateHOLFiniteState_call, hargs]; simp
  | some vs =>
    obtain ⟨v1, v2, rfl⟩ := evalListHOLFinite_three_word3_local state dst src sizeExp K hargs (heval state)
    exact RunBounded.call hargs hbudget (fun body locals rs hfound => by
      rw [hcode] at hfound
      obtain ⟨rfl, hn⟩ := three_arg_lookup_last originalRuntimeCode.lookup
        (ofString "rlp_encode_bytes") (ofString "dst") (ofString "src") (ofString "n")
        (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes)
        (by decide) (by decide) (by decide) lookup_rlp_encode_bytes hfound
      exact runBounded_rlp_encode_bytes_body (callEntryStateHOLFinite state locals) K hsmall hcode hn
        (by change K.toNat / 8 + 2 ^ 64 + 18 ≤ state.clock - 1; omega))

theorem progBounded_rlp_encode_bytes_const (destination : Option (VarKind × MlS)) (dst src : ExpHOL 64)
    (K : BitVec 64) (hsmall : K.toNat + 32 < 2 ^ 64) :
    ProgBounded (.call (some (destination, none)) (ofString "rlp_encode_bytes") [dst, src, .const K])
      (K.toNat / 8 + 2 ^ 64 + 19) :=
  progBounded_rlp_encode_bytes_exp destination dst src (.const K) K hsmall
    (fun _ => by rw [evalHOLFinite_eq_toExact]; rfl)

theorem progBounded_rlp_encode_bytes_decCall_exp (name : MlS) (shape : ShapeHOL) (dst src sizeExp : ExpHOL 64)
    (K : BitVec 64) {continuation : ProgHOL 64} {tailCost : Nat}
    (hsmall : K.toNat + 32 < 2 ^ 64)
    (heval : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) sizeExp = some (.val (.word K)))
    (hrest : ProgBounded continuation tailCost) :
    ProgBounded (.decCall name shape (ofString "rlp_encode_bytes") [dst, src, sizeExp] continuation)
      (K.toNat / 8 + 2 ^ 64 + 19 + tailCost) := by
  intro F state hcode hbudget
  cases hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [dst, src, sizeExp] with
  | none =>
    rw [evaluateHOLFiniteState_decCall_args_none state name shape (ofString "rlp_encode_bytes") [dst, src, sizeExp] continuation hargs]
    simp
  | some vs =>
    obtain ⟨v1, v2, rfl⟩ := evalListHOLFinite_three_word3_local state dst src sizeExp K hargs (heval state)
    have h := RunBounded.decCall (name := name) (shape := shape) (continuation := continuation)
      (bodyCost := K.toNat / 8 + 2 ^ 64 + 18) (tailCost := tailCost) hargs (by omega)
      (fun body locals rs hfound => by
        rw [hcode] at hfound
        obtain ⟨rfl, hn⟩ := three_arg_lookup_last originalRuntimeCode.lookup
          (ofString "rlp_encode_bytes") (ofString "dst") (ofString "src") (ofString "n")
          (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes)
          (by decide) (by decide) (by decide) lookup_rlp_encode_bytes hfound
        have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state locals)
          (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes)
        refine ⟨runBounded_rlp_encode_bytes_body (callEntryStateHOLFinite state locals) K hsmall hcode hn
          (by change K.toNat / 8 + 2 ^ 64 + 18 ≤ state.clock - 1; omega), ?_⟩
        intro value post hran hpost_clk
        rw [hran] at hmeta
        exact hrest _ (hmeta.1.trans hcode) hpost_clk)
    exact h.weaken (by omega)

theorem progBounded_rlp_encode_bytes_decCall_const (name : MlS) (shape : ShapeHOL) (dst src : ExpHOL 64)
    (K : BitVec 64) {continuation : ProgHOL 64} {tailCost : Nat}
    (hsmall : K.toNat + 32 < 2 ^ 64)
    (hrest : ProgBounded continuation tailCost) :
    ProgBounded (.decCall name shape (ofString "rlp_encode_bytes") [dst, src, .const K] continuation)
      (K.toNat / 8 + 2 ^ 64 + 19 + tailCost) :=
  progBounded_rlp_encode_bytes_decCall_exp name shape dst src (.const K) K hsmall
    (fun _ => by rw [evalHOLFinite_eq_toExact]; rfl) hrest

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

private def noReturnProg : ProgHOL 64 → Bool
  | .return _ => false
  | .seq first second => noReturnProg first && noReturnProg second
  | .ite _ yes no => noReturnProg yes && noReturnProg no
  | .dec _ _ _ body => noReturnProg body
  | .decCall _ _ _ _ cont => noReturnProg cont
  | .while _ body => noReturnProg body
  | .skip | .assign _ _ _ | .primitive _ _ _ | .store _ _ | .storeByte _ _ | .store32 _ _
  | .break | .continue | .raise _ _ | .annot _ _ | .call (some (_, none)) _ _ => true
  | _ => false

private theorem evaluate_noReturnProg {F : Type} (p : ProgHOL 64) (hp : noReturnProg p = true)
    (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64) :
    (evaluateHOLFiniteState s p).1 ≠ some (.returned v) := by
  cases hshape : p with
  | «return» _ => simp [hshape, noReturnProg] at hp
  | seq a b =>
    have hab : noReturnProg a = true ∧ noReturnProg b = true := by
      simpa only [hshape, noReturnProg, Bool.and_eq_true] using hp
    have hrem := evaluateHOLFiniteState_clock_le s a
    rw [evaluateHOLFiniteState_seq_line780]
    have ha := evaluate_noReturnProg a hab.1 s v
    cases hra : evaluateHOLFiniteState s a with
    | mk r1 mid =>
      rw [hra] at ha hrem
      cases r1 with
      | none => exact evaluate_noReturnProg b hab.2 mid v
      | some _ => exact ha
  | ite c yes no =>
    have hy : noReturnProg yes = true ∧ noReturnProg no = true := by
      simpa only [hshape, noReturnProg, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noReturnProg no hy.2 s v
      · exact evaluate_noReturnProg yes hy.1 s v
    · simp
  | dec nm sh init body =>
    have hb : noReturnProg body = true := by simpa only [hshape, noReturnProg] using hp
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · simp
    · split
      · exact evaluate_noReturnProg body hb _ v
      · simp
  | decCall nm sh fn args cont =>
    have hc : noReturnProg cont = true := by simpa only [hshape, noReturnProg] using hp
    rw [evaluateHOLFiniteState_decCall_total]
    cases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with
    | none => rw [hargs]; simp
    | some vs =>
      rw [hargs]; dsimp only
      cases hlk : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup fn vs with
      | none => rw [hlk]; simp
      | some inst =>
        obtain ⟨bbody, blocals, brs⟩ := inst
        rw [hlk]; dsimp only
        split
        · simp
        · have hrem := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s blocals) bbody
          cases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s blocals) bbody with
          | mk r1 bpost =>
            rw [hb] at hrem ⊢
            have hfix : fixClockHOLFinite (callEntryStateHOLFinite s blocals) (r1, bpost) = (r1, bpost) := by
              simp [fixClockHOLFinite, Nat.not_lt.mpr hrem]
            rw [hfix]
            dsimp only
            rcases r1 with _ | (_ | _ | _ | _ | rv | _ | _)
            all_goals try (simp; done)
            simp only []
            split
            · have hclk_lt : (setVarHOLFinite nm rv {bpost with locals := s.locals}).clock < s.clock := by
                change bpost.clock < s.clock
                change bpost.clock ≤ s.clock - 1 at hrem
                omega
              exact evaluate_noReturnProg cont hc _ v
            · simp
  | «while» cond body =>
    have hb : noReturnProg body = true := by simpa only [hshape, noReturnProg] using hp
    intro hret
    rw [evaluateHOLFiniteState_while_total] at hret
    split at hret
    · split at hret
      · split at hret
        · simp at hret
        · dsimp only at hret
          rw [fixClockHOLFinite_evaluateState] at hret
          have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          cases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with
          | mk r1 mid =>
            rw [hbr] at hret hrem
            have hclk_lt : mid.clock < s.clock := by
              change mid.clock ≤ s.clock - 1 at hrem
              omega
            cases r1 with
            | none => exact evaluate_noReturnProg (.while cond body) (by simpa [noReturnProg] using hb) mid v hret
            | some r1' =>
              cases r1' with
              | «continue» =>
                exact evaluate_noReturnProg (.while cond body) (by simpa [noReturnProg] using hb) mid v hret
              | «break» => simp at hret
              | returned rv =>
                have hno := evaluate_noReturnProg body hb (decClockHOLFinite s) rv
                rw [hbr] at hno
                exact hno rfl
              | _ => simp at hret
      · simp at hret
    · simp at hret
  | skip => simp [evaluateHOLFiniteState_skip]
  | «break» => simp [evaluateHOLFiniteState_break]
  | «continue» => simp [evaluateHOLFiniteState_continue]
  | annot _ _ => simp [evaluateHOLFiniteState_annot]
  | raise _ _ =>
    rw [evaluateHOLFiniteState_raise]; split
    · dsimp only; split <;> simp
    · simp
  | assign _ _ _ => rw [evaluateHOLFiniteState_assign]; repeat' first | split | simp
  | primitive _ _ _ => rw [evaluateHOLFiniteState_primitive]; repeat' first | split | simp
  | store _ _ => rw [(PanRunBounded.evaluate_store_control_frame s _ _).1]; split <;> simp
  | storeByte _ _ => rw [(PanRunBounded.evaluate_storeByte_control_frame s _ _).1]; split <;> simp
  | store32 _ _ => rw [evaluateHOLFiniteState_store32]; repeat' first | split | simp
  | call info fn args =>
    rcases info with _ | ⟨dest, _ | _⟩
    · simp [hshape, noReturnProg] at hp
    · rw [evaluateHOLFiniteState_call]
      repeat' first | split | simp
    · simp [hshape, noReturnProg] at hp
  | _ => simp [hshape, noReturnProg] at hp
termination_by (s.clock, sizeOf p)
decreasing_by all_goals (simp_all [decClockHOLFinite, setVarHOLFinite]; omega)

private theorem u256_byte_length_returned_lt {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (hran : evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_u256_byte_length) =
      (some (.returned v), post)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat < 2 ^ 61 := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_u256_byte_length,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at hran
  rw [evaluateHOLFiniteState_decCall_total] at hran
  cases hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "a")] with
  | none => rw [hargs] at hran; simp at hran
  | some vs =>
    rw [hargs] at hran; dsimp only at hran
    cases hlookup : PanSemStateFiniteExact.lookupCodeHOLFinite state.code.lookup (ofString "u256_bit_length") vs with
    | none => rw [hlookup] at hran; simp at hran
    | some inst =>
      obtain ⟨bbody, blocals, brs⟩ := inst
      rw [hlookup] at hran; dsimp only at hran
      split at hran
      · simp at hran
      · rename_i hclk
        have hrem := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state blocals) bbody
        cases hb : evaluateHOLFiniteState (callEntryStateHOLFinite state blocals) bbody with
        | mk r1 bpost =>
          rw [hb] at hran hrem
          have hfix : fixClockHOLFinite (callEntryStateHOLFinite state blocals) (r1, bpost) = (r1, bpost) := by
            simp [fixClockHOLFinite, Nat.not_lt.mpr hrem]
          rw [hfix] at hran
          dsimp only at hran
          rcases r1 with _ | (_ | _ | _ | _ | nv | _ | _)
          all_goals try (simp at hran; done)
          simp only [] at hran
          split at hran
          · let s1 := setVarHOLFinite (ofString "n") nv {bpost with locals := state.locals}
            have hs1_n : s1.locals.lookup (ofString "n") = some nv := by
              simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            obtain ⟨r2, s2, hret, hr2⟩ : ∃ r2 s2,
                evaluateHOLFiniteState s1
                  (.return (.shift .lsr (.op .add [.var .local (ofString "n"), .const (BitVec.ofNat 64 7)])
                    (.const (BitVec.ofNat 64 3)))) = (r2, s2) ∧ r2 = some (.returned v) := by
              simp only [Prod.mk.injEq] at hran
              exact ⟨_, _, rfl, hran.1⟩
            subst hr2
            rw [evaluateHOLFiniteState_return] at hret
            cases nv with
            | rStruct _ => simp [evalHOLExact, evalListHOLExact, hs1_n, valueIsWord] at hret
            | nStruct _ _ => simp [evalHOLExact, evalListHOLExact, hs1_n, valueIsWord] at hret
            | val wl =>
              cases wl with
              | word nw =>
                have hsh : wordShiftHOL (width := 64) .lsr (nw + 7) (3 : BitVec 64).toNat =
                    some ((nw + 7) >>> 3) := by
                  simp [wordShiftHOL]
                simp only [BitVec.ofNat_eq_ofNat, evalHOLExact, evalListHOLExact, hs1_n, wordOpHOL, wordOp,
                  valueIsWord, valueWord, hsh] at hret
                split at hret
                · cases hret
                  refine ⟨(nw + 7) >>> 3, rfl, ?_⟩
                  rw [BitVec.toNat_ushiftRight]
                  have := (nw + 7).isLt
                  omega
                · simp at hret
          · simp at hran

private theorem call_u256_byte_length_returned_lt {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (args : List (ValueHOL 64))
    (body : ProgHOL 64) (locals : HolFiniteMapExact MlS (ValueHOL 64)) (rs : ShapeHOL) (v : ValueHOL 64)
    (hcode : s.code = originalRuntimeCode)
    (hfound : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup (ofString "u256_byte_length") args =
      some (body, locals, rs))
    (hran : evaluateHOLFiniteState (callEntryStateHOLFinite s locals) body = (some (.returned v), post)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat < 2 ^ 61 := by
  rw [hcode] at hfound
  have hbody := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup
    (ofString "u256_byte_length") _ (sourceFnBody Guest.Software.guestFn_u256_byte_length) body .one rs
    args locals lookup_u256_byte_length hfound
  subst hbody
  exact u256_byte_length_returned_lt (callEntryStateHOLFinite s locals) post v hran

private theorem u256_to_be_min_returned_lt {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (hcode : state.code = originalRuntimeCode)
    (hran : evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_u256_to_be_min) =
      (some (.returned v), post)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat < 2 ^ 61 := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_u256_to_be_min,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at hran
  rw [evaluateHOLFiniteState_decCall_total] at hran
  cases hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "a")] with
  | none => rw [hargs] at hran; simp at hran
  | some vs =>
    rw [hargs] at hran; dsimp only at hran
    cases hlookup : PanSemStateFiniteExact.lookupCodeHOLFinite state.code.lookup (ofString "u256_byte_length") vs with
    | none => rw [hlookup] at hran; simp at hran
    | some inst =>
      obtain ⟨bbody, blocals, brs⟩ := inst
      rw [hlookup] at hran; dsimp only at hran
      split at hran
      · simp at hran
      · rename_i hclk
        have hrem := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state blocals) bbody
        cases hb : evaluateHOLFiniteState (callEntryStateHOLFinite state blocals) bbody with
        | mk r1 bpost =>
          rw [hb] at hran hrem
          have hfix : fixClockHOLFinite (callEntryStateHOLFinite state blocals) (r1, bpost) = (r1, bpost) := by
            simp [fixClockHOLFinite, Nat.not_lt.mpr hrem]
          rw [hfix] at hran
          dsimp only at hran
          rcases r1 with _ | (_ | _ | _ | _ | lenv | _ | _)
          all_goals try (simp at hran; done)
          obtain ⟨lenw, rfl, hlen_lt⟩ := call_u256_byte_length_returned_lt state bpost vs bbody blocals brs
            lenv hcode hlookup hb
          simp only [] at hran
          split at hran
          · let s1 := setVarHOLFinite (ofString "len") (.val (.word lenw)) {bpost with locals := state.locals}
            have hs1_len : s1.locals.lookup (ofString "len") = some (.val (.word lenw)) := by
              simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            obtain ⟨r2, s2, hdec⟩ : ∃ r2 s2,
                evaluateHOLFiniteState s1 _ = (r2, s2) ∧ r2 = some (.returned v) := by
              simp only [Prod.mk.injEq] at hran
              exact ⟨_, _, rfl, hran.1⟩
            rcases hdec with ⟨hdec, rfl⟩
            rw [evaluateHOLFiniteState_dec_total] at hdec
            simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true] at hdec
            let s1i := setVarHOLFinite (ofString "i") (.val (.word 0)) s1
            have hs1i_len : s1i.locals.lookup (ofString "len") = some (.val (.word lenw)) := by
              have hne : ofString "i" ≠ ofString "len" := by decide
              simp [s1i, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hs1_len]
            obtain ⟨r3, s3, hseq, hr3⟩ : ∃ r3 s3,
                evaluateHOLFiniteState s1i _ = (r3, s3) ∧ r3 = some (.returned v) := by
              simp only [Prod.mk.injEq] at hdec
              exact ⟨_, _, rfl, hdec.1⟩
            subst hr3
            rw [evaluateHOLFiniteState_seq_line780] at hseq
            have hno_ret := evaluate_noReturnProg _ (by decide) s1i
            have hpreserve_raw := PanRunBounded.evaluate_avoidsLocal_flowing (ofString "len") _ (by decide) s1i
            cases hwh : evaluateHOLFiniteState s1i _ with
            | mk rw sw =>
              rw [hwh] at hseq hno_ret hpreserve_raw
              dsimp only at hseq hno_ret hpreserve_raw
              cases rw with
              | some rw' =>
                cases rw' with
                | returned rv => exact False.elim (hno_ret rv rfl)
                | _ => simp at hseq
              | none =>
                dsimp only at hseq
                have hsw_len : sw.locals.lookup (ofString "len") = some (.val (.word lenw)) :=
                  (hpreserve_raw (Or.inl rfl)).trans hs1i_len
                rw [evaluateHOLFiniteState_return] at hseq
                simp only [evalHOLExact, hsw_len] at hseq
                split at hseq
                · cases hseq
                  exact ⟨lenw, rfl, hlen_lt⟩
                · simp at hseq
          · simp at hran

theorem call_u256_to_be_min_returned_lt {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (args : List (ValueHOL 64))
    (body : ProgHOL 64) (locals : HolFiniteMapExact MlS (ValueHOL 64)) (rs : ShapeHOL) (v : ValueHOL 64)
    (hcode : s.code = originalRuntimeCode)
    (hfound : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup (ofString "u256_to_be_min") args =
      some (body, locals, rs))
    (hran : evaluateHOLFiniteState (callEntryStateHOLFinite s locals) body = (some (.returned v), post)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat < 2 ^ 61 := by
  rw [hcode] at hfound
  have hbody := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup
    (ofString "u256_to_be_min") _ (sourceFnBody Guest.Software.guestFn_u256_to_be_min) body .one rs
    args locals lookup_u256_to_be_min hfound
  subst hbody
  exact u256_to_be_min_returned_lt (callEntryStateHOLFinite s locals) post v hcode hran

theorem progBounded_u256_to_be_min_encode_decCall
    (dst vExp tmpExp : ExpHOL 64) {continuation : ProgHOL 64} {tailCost : Nat}
    (hrest : ProgBounded continuation tailCost) :
    ProgBounded
      (.decCall (ofString "n") .one (ofString "u256_to_be_min") [vExp, tmpExp]
        (.decCall (ofString "w") .one (ofString "rlp_encode_bytes")
          [dst, tmpExp, .var .local (ofString "n")] continuation))
      (3 * 2 ^ 64 + 2 ^ 58 + 25 + tailCost) := by
  intro F state hcode hbudget
  cases hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [vExp, tmpExp] with
  | none =>
    rw [evaluateHOLFiniteState_decCall_args_none state (ofString "n") .one (ofString "u256_to_be_min") _ _ hargs]
    simp
  | some vs =>
    exact (RunBounded.decCall (bodyCost := 2 * 2 ^ 64 + 4) (tailCost := 2 ^ 64 + 2 ^ 58 + 20 + tailCost)
      hargs (by omega) (fun body locals rs hfound =>
        ⟨ProgBounded.bodies_of_fun funBounded_u256_to_be_min state hcode
          (by omega) vs body locals rs hfound,
         fun val post hran hpost_clk => by
          obtain ⟨nw, rfl, hnw_lt⟩ := call_u256_to_be_min_returned_lt state post vs body locals rs
            val hcode hfound hran
          have hsmall : nw.toNat + 32 < 2 ^ 64 := by omega
          let s1 := setVarHOLFinite (ofString "n") (.val (.word nw)) {post with locals := state.locals}
          have hs1_code : s1.code = originalRuntimeCode := by
            have hm := (PanRunBounded.evaluateHOLFiniteState_metadata
              (callEntryStateHOLFinite state locals) body).1
            rw [hran] at hm
            exact hm.trans hcode
          have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word nw)) := by
            simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          cases hcargs : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
              [dst, tmpExp, .var .local (ofString "n")] with
          | none =>
            unfold RunBounded
            rw [evaluateHOLFiniteState_decCall_args_none s1 (ofString "w") .one (ofString "rlp_encode_bytes") _ _ hcargs]
            simp
          | some cvs =>
            have hen : evalHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
                (.var .local (ofString "n")) = some (.val (.word nw)) := by
              rw [evalHOLFinite_eq_toExact]; simp [evalHOLExact, hs1_n]
            obtain ⟨cv1, cv2, rfl⟩ := evalListHOLFinite_three_word3_local s1
              dst tmpExp (.var .local (ofString "n")) nw hcargs hen
            have hcall := RunBounded.decCall (state := s1)
              (bodyCost := nw.toNat / 8 + 2 ^ 64 + 18) (tailCost := tailCost)
              hcargs (by change nw.toNat / 8 + 2 ^ 64 + 18 + 1 + tailCost ≤ post.clock; omega)
              (fun eb elocals ers hefound => by
                rw [hs1_code] at hefound
                obtain ⟨rfl, heln⟩ := three_arg_lookup_last originalRuntimeCode.lookup
                  (ofString "rlp_encode_bytes") (ofString "dst") (ofString "src") (ofString "n")
                  (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes)
                  (by decide) (by decide) (by decide) lookup_rlp_encode_bytes hefound
                refine ⟨runBounded_rlp_encode_bytes_body (callEntryStateHOLFinite s1 elocals) nw hsmall
                  hs1_code heln (by change nw.toNat / 8 + 2 ^ 64 + 18 ≤ post.clock - 1; omega),
                  fun eval epost heran heclk => ?_⟩
                have hecode : (setVarHOLFinite (ofString "w") eval {epost with locals := s1.locals}).code =
                    originalRuntimeCode := by
                  have hm := (PanRunBounded.evaluateHOLFiniteState_metadata
                    (callEntryStateHOLFinite s1 elocals)
                    (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes)).1
                  rw [heran] at hm
                  exact hm.trans hs1_code
                exact hrest _ hecode heclk)
            exact hcall.weaken (by omega)⟩)).weaken (by omega)

theorem funBounded_rlp_put_u256 :
    FunBounded (ofString "rlp_put_u256") (3 * 2 ^ 64 + 2 ^ 58 + 51) := by
  refine funBounded_of_guestAst 228 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_rlp_put_u256 (3 * 2 ^ 64 + 2 ^ 58 + 51) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_rlp_put_u256,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_heap_mark (ofString "mark") .one []
      (ProgBounded.decCall funBounded_alloc (ofString "tmp") .one [.const 32]
        (progBounded_u256_to_be_min_encode_decCall
          (.var .local (ofString "dst")) (.var .local (ofString "v")) (.var .local (ofString "tmp"))
          (ProgBounded.seq
            (ProgBounded.call funBounded_heap_release none [.var .local (ofString "mark")])
            (ProgBounded.straight _ rfl)))))
    (by decide)

def rlpValidateItemsStepBody : ProgHOL 64 :=
  match sourceFnBody Guest.Software.guestFn__rlp_validate_items_body with
  | .dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.seq (.while _ stepBody) _)))) => stepBody
  | _ => .skip

theorem progBounded_rlp_validate_items_step :
    ProgBounded rlpValidateItemsStepBody (2 ^ 64 + 7) := by
  dsimp only [rlpValidateItemsStepBody, sourceFnBody, sourceFunctionEntry,
    Guest.Software.guestFn__rlp_validate_items_body,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.iteMax _
      (ProgBounded.straight _ rfl)
      (ProgBounded.decCall funBounded_rlp_item_header _ _ _
        (ProgBounded.dec _ _ _
          (ProgBounded.dec _ _ _
            (ProgBounded.iteMax _
              (ProgBounded.decCall funBounded_scratch_alloc _ _ _ (ProgBounded.straight _ rfl))
              (ProgBounded.straight _ rfl))))))
    (by decide)

def rlpListCountStepBody : ProgHOL 64 :=
  match sourceFnBody Guest.Software.guestFn_rlp_list_count with
  | .dec _ _ _ (.dec _ _ _ (.seq (.while _ stepBody) _)) => stepBody
  | _ => .skip

theorem progBounded_rlp_list_count_step (K_body : Nat)
    (h_body : FunBounded (ofString "_rlp_validate_items_body") K_body) :
    ProgBounded rlpListCountStepBody (2 ^ 64 + K_body + 11) := by
  dsimp only [rlpListCountStepBody, sourceFnBody, sourceFunctionEntry,
    Guest.Software.guestFn_rlp_list_count,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall (funBounded_rlp_item_total K_body h_body) _ _ _
      (ProgBounded.straight _ rfl))
    (by omega)

-- ============================================================================
-- Section 3: SSZ decode_bytes_list & Transaction Decoders (206, 296..307)
-- ============================================================================

theorem funBounded_ssz_split_var_list :
    FunBounded (ofString "ssz_split_var_list") (2 ^ 64 * 4 + 10) := by
  refine funBounded_of_guestAst 199 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_ssz_split_var_list (2 ^ 64 * 4 + 10) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_ssz_split_var_list,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.seq
      (ProgBounded.iteMax _ (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl))
      (ProgBounded.seq
        (ProgBounded.iteMax _ (ProgBounded.call funBounded_ssz_fail none _) (ProgBounded.straight _ rfl))
        (ProgBounded.dec _ _ _
          (ProgBounded.seq
            (ProgBounded.iteMax _ (ProgBounded.call funBounded_ssz_fail none _) (ProgBounded.straight _ rfl))
            (ProgBounded.dec _ _ _
              (ProgBounded.seq
                (ProgBounded.iteMax _ (ProgBounded.call funBounded_ssz_fail none _) (ProgBounded.straight _ rfl))
                (ProgBounded.decCall funBounded_alloc _ _ _
                  (progBounded_varCountedDec2_local (ofString "i") (ofString "prev") (ofString "count")
                    .one (.var .local (ofString "first")) .less (Or.inl rfl) (by decide)
                    (cost := max (0 + 1) 0 + 0)
                    (countedStep_dec _ _ _ (by decide)
                      (countedStep_seq
                        (.ite _ (.call (some (none, none)) (ofString "ssz_fail") [.const 23]) .skip)
                        (ProgBounded.iteMax _ (ProgBounded.call funBounded_ssz_fail none _) (ProgBounded.straight _ rfl))
                        rfl rfl
                        (countedStep_seq_straight _ rfl rfl rfl
                          (countedStep_seq_straight _ rfl rfl rfl
                            (countedStep_seq_straight _ rfl rfl rfl countedStep_incr)))))
                    rfl
                    (ProgBounded.straight _ rfl)))))))))
    (by decide)

theorem funBounded_decode_bytes_list :
    FunBounded (ofString "decode_bytes_list") (2 ^ 64 * 7 + 8) := by
  refine funBounded_of_guestAst 206 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_decode_bytes_list (2 ^ 64 * 7 + 8) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_decode_bytes_list,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_ssz_split_var_list _ _ _
      (progBounded_varCountedDec_rfield (ofString "i") (ofString "r") 1 .less (Or.inl rfl)
        (cost := max (0 + 1) 0 + 0)
        (countedStep_seq
          (.ite _ (.call (some (none, none)) (ofString "ssz_fail") [.const 70]) .skip)
          (ProgBounded.iteMax _ (ProgBounded.call funBounded_ssz_fail none _) (ProgBounded.straight _ rfl))
          rfl rfl countedStep_incr)
        rfl
        (ProgBounded.straight _ rfl)))
    (by decide)

theorem funBounded_tx_scalar_item (K_lc : Nat)
    (h_lc : FunBounded (ofString "rlp_list_count") K_lc) :
    FunBounded (ofString "tx_scalar_item") (2 ^ 64 + K_lc + 6) := by
  refine funBounded_of_guestAst 296 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_tx_scalar_item (2 ^ 64 + K_lc + 6) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_tx_scalar_item,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall (funBounded_rlp_item K_lc h_lc) _ _ _ (ProgBounded.straight _ rfl))
    (by omega)

theorem funBounded_tx_scalar_u256 (K_lc : Nat)
    (h_lc : FunBounded (ofString "rlp_list_count") K_lc) :
    FunBounded (ofString "tx_scalar_u256") (2 ^ 64 + K_lc + 36) := by
  refine funBounded_of_guestAst 297 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_tx_scalar_u256 (2 ^ 64 + K_lc + 36) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_tx_scalar_u256,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall (funBounded_tx_scalar_item K_lc h_lc) _ _ _
      (ProgBounded.seq
        (ProgBounded.iteMax _ (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl))
        (ProgBounded.tail funBounded_u256_from_be _)))
    (by omega)

theorem funBounded_tx_scalar_word (K_lc : Nat)
    (h_lc : FunBounded (ofString "rlp_list_count") K_lc) :
    FunBounded (ofString "tx_scalar_word") (2 * 2 ^ 64 + K_lc + 6) := by
  refine funBounded_of_guestAst 298 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_tx_scalar_word (2 * 2 ^ 64 + K_lc + 6) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_tx_scalar_word,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall (funBounded_tx_scalar_item K_lc h_lc) _ _ _
      (ProgBounded.seq
        (ProgBounded.iteMax _ (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl))
        (ProgBounded.dec _ _ _
          (progBounded_varCountedDec_rfield (ofString "j") (ofString "f") 1 .lower (Or.inr rfl)
            (cost := 0)
            (countedStep_seq_straight _ rfl rfl rfl countedStep_incr)
            rfl
            (ProgBounded.straight _ rfl)))))
    (by omega)

theorem funBounded_tx_bytes_item (K_lc : Nat)
    (h_lc : FunBounded (ofString "rlp_list_count") K_lc) :
    FunBounded (ofString "tx_bytes_item") (2 ^ 64 + K_lc + 6) := by
  refine funBounded_of_guestAst 299 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_tx_bytes_item (2 ^ 64 + K_lc + 6) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_tx_bytes_item,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall (funBounded_rlp_item K_lc h_lc) _ _ _ (ProgBounded.straight _ rfl))
    (by omega)

theorem funBounded_tx_fixed_bytes (K_lc : Nat)
    (h_lc : FunBounded (ofString "rlp_list_count") K_lc) :
    FunBounded (ofString "tx_fixed_bytes") (2 ^ 64 + K_lc + 6) := by
  refine funBounded_of_guestAst 300 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_tx_fixed_bytes (2 ^ 64 + K_lc + 6) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_tx_fixed_bytes,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall (funBounded_rlp_item K_lc h_lc) _ _ _ (ProgBounded.straight _ rfl))
    (by omega)

theorem funBounded_tx_to_item (K_lc : Nat)
    (h_lc : FunBounded (ofString "rlp_list_count") K_lc) :
    FunBounded (ofString "tx_to_item") (2 ^ 64 + K_lc + 6) := by
  refine funBounded_of_guestAst 301 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_tx_to_item (2 ^ 64 + K_lc + 6) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_tx_to_item,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall (funBounded_rlp_item K_lc h_lc) _ _ _ (ProgBounded.straight _ rfl))
    (by omega)

theorem funBounded_tx_list_item (K_lc : Nat)
    (h_lc : FunBounded (ofString "rlp_list_count") K_lc) :
    FunBounded (ofString "tx_list_item") (2 ^ 64 + K_lc + 6) := by
  refine funBounded_of_guestAst 302 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_tx_list_item (2 ^ 64 + K_lc + 6) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_tx_list_item,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall (funBounded_rlp_item K_lc h_lc) _ _ _ (ProgBounded.straight _ rfl))
    (by omega)

theorem countedStep_varCountedDec_rfield {outer : MlS} {step : BitVec 64}
    (inner structVar : MlS) (idx : Nat) (op : Cmp) (hop : op = .less ∨ op = .lower)
    {body tail : ProgHOL 64} {cost tailCost : Nat}
    (hdistinct : outer ≠ inner)
    (hbody : CountedStep inner 1 body cost)
    (havoid_struct : avoidsLocal structVar body = true)
    (havoid_outer : avoidsLocal outer body = true)
    (hnoRet : noReturnProg body = true)
    (htail : CountedStep outer step tail tailCost) :
    CountedStep outer step
      (.dec inner .one (.const 0)
        (.seq (.while (.cmp op (.var .local inner) (.rfield idx (.var .local structVar))) body) tail))
      ((2 ^ 64 - 1) * (cost + 1) + tailCost) := by
  intro F state code w atC budget
  have hloop_prog : ProgBounded
      (.dec inner .one (.const 0)
        (.seq (.while (.cmp op (.var .local inner) (.rfield idx (.var .local structVar))) body) .skip))
      ((2 ^ 64 - 1) * (cost + 1)) :=
    ProgBounded.weaken
      (progBounded_varCountedDec_rfield inner structVar idx op hop hbody havoid_struct (ProgBounded.straight .skip rfl))
      (by omega)
  rw [evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true]
  let s0 := setVarHOLFinite inner (.val (.word 0)) state
  have hs0_code : s0.code = originalRuntimeCode := code
  have hs0_outer : s0.locals.lookup outer = some (.val (.word w)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hdistinct, atC]
  have hbnd0 := hloop_prog state code (by omega)
  rw [evaluateHOLFiniteState_dec_total] at hbnd0
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true] at hbnd0
  let wloop : ProgHOL 64 := .while (.cmp op (.var .local inner) (.rfield idx (.var .local structVar))) body
  have hframe := evaluate_avoidsLocal_flowing outer wloop (by simp [wloop, avoidsLocal, havoid_outer]) s0
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata s0 wloop
  have hnr := evaluate_noReturnProg wloop (by simp [wloop, noReturnProg, hnoRet]) s0
  rw [evaluateHOLFiniteState_seq_line780] at hbnd0 ⊢
  rcases hlrun : evaluateHOLFiniteState s0 wloop with ⟨lres, mid⟩
  rw [hlrun] at hbnd0 hframe hmeta hnr
  dsimp only at hbnd0 hframe hmeta hnr
  cases lres with
  | none =>
    simp only [evaluateHOLFiniteState_skip] at hbnd0
    dsimp only at hbnd0 ⊢
    obtain ⟨sp, kp, _⟩ := hbnd0
    have hmid_outer : mid.locals.lookup outer = some (.val (.word w)) := by
      rw [hframe (Or.inl rfl)]
      exact hs0_outer
    obtain ⟨t1, t2, t3, t4, t5⟩ := htail mid (hmeta.1.trans code) w hmid_outer
      (by change tailCost ≤ mid.clock; change state.clock ≤ mid.clock + _ at sp; omega)
    rcases htrun : evaluateHOLFiniteState mid tail with ⟨tres, post⟩
    rw [htrun] at t1 t2 t3 t4 t5
    dsimp only at t1 t2 t3 t4 t5 ⊢
    change mid.clock ≤ post.clock + tailCost at t1
    change post.clock ≤ mid.clock at t2
    change state.clock ≤ mid.clock + (2 ^ 64 - 1) * (cost + 1) at sp
    change mid.clock ≤ state.clock at kp
    refine ⟨by omega, by omega, t3, t4, fun hnorm => ?_⟩
    obtain ⟨advC, advCode⟩ := t5 hnorm
    refine ⟨?_, advCode.trans hmeta.1⟩
    rw [PanRunBounded.resVarEq_lookup, if_neg hdistinct]
    exact advC
  | some r =>
    dsimp only at hbnd0 ⊢
    obtain ⟨sp, kp, sf⟩ := hbnd0
    have hnot_cont : some r ≠ some .continue := by
      intro hc; cases hc
      have hwc := PanRunBounded.evaluate_while_not_break_or_continue s0
        (.cmp op (.var .local inner) (.rfield idx (.var .local structVar))) body
      rw [hlrun] at hwc
      exact hwc.2 rfl
    cases r with
    | returned v => exact False.elim (hnr v rfl)
    | _ => exact ⟨by omega, kp, sf, hnot_cont, by simp⟩

theorem funBounded_decode_access_list (K_lc : Nat)
    (h_lc : FunBounded (ofString "rlp_list_count") K_lc) :
    FunBounded (ofString "decode_access_list")
      (K_lc + 6 + (2 ^ 64 - 1) * (2 ^ 64 + 3) +
        (2 ^ 64 - 1) *
          (5 * K_lc + 3 * 2 ^ 64 + 34 + 2 * ((2 ^ 64 - 1) * (2 ^ 64 + 3)) +
            (2 ^ 64 - 1) * (2 ^ 64 + K_lc + 19))) := by
  refine funBounded_of_guestAst 303 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_decode_access_list _ rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_decode_access_list,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall (funBounded_rlp_list_to_slices K_lc h_lc) _ _ _
      (ProgBounded.decCall funBounded_alloc _ _ _
        (progBounded_varCountedDec_rfield (ofString "i") (ofString "lst") 1 .lower (Or.inr rfl)
          (cost := 5 * K_lc + 3 * 2 ^ 64 + 33 + 2 * ((2 ^ 64 - 1) * (2 ^ 64 + 3)) +
            (2 ^ 64 - 1) * (2 ^ 64 + K_lc + 19))
          (countedStep_decCall _ _ _ _ (by decide) (funBounded_rlp_item K_lc h_lc)
            (countedStep_seq_straight _ rfl rfl rfl
              (countedStep_decCall _ _ _ _ (by decide) (funBounded_rlp_list_to_slices K_lc h_lc)
                (countedStep_seq_straight _ rfl rfl rfl
                  (countedStep_decCall _ _ _ _ (by decide) (funBounded_tx_fixed_bytes K_lc h_lc)
                    (countedStep_decCall _ _ _ _ (by decide) (funBounded_tx_list_item K_lc h_lc)
                      (countedStep_decCall _ _ _ _ (by decide) (funBounded_rlp_list_to_slices K_lc h_lc)
                        (countedStep_decCall _ _ _ _ (by decide) funBounded_alloc
                          (countedStep_varCountedDec_rfield (ofString "j") (ofString "slots") 1 .lower (Or.inr rfl)
                            (by decide)
                            (cost := 2 ^ 64 + K_lc + 18)
                            (countedStep_decCall _ _ _ _ (by decide) (funBounded_tx_fixed_bytes K_lc h_lc)
                              (countedStep_seq _ (progBounded_memcpy_const none _ _ 32 (by decide)) rfl rfl countedStep_incr))
                            rfl rfl rfl
                            (countedStep_dec _ _ _ (by decide)
                              (countedStep_seq_straight _ rfl rfl rfl
                                (countedStep_seq_straight _ rfl rfl rfl
                                  (countedStep_seq_straight _ rfl rfl rfl countedStep_incr)))))))))))))
          rfl
          (ProgBounded.straight _ rfl))))
    (by omega)

theorem funBounded_decode_blob_hashes (K_lc : Nat)
    (h_lc : FunBounded (ofString "rlp_list_count") K_lc) :
    FunBounded (ofString "decode_blob_hashes")
      (K_lc + 6 + (2 ^ 64 - 1) * (2 ^ 64 + 3) + (2 ^ 64 - 1) * (2 ^ 64 + K_lc + 19)) := by
  refine funBounded_of_guestAst 304 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_decode_blob_hashes _ rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_decode_blob_hashes,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall (funBounded_rlp_list_to_slices K_lc h_lc) _ _ _
      (ProgBounded.decCall funBounded_alloc _ _ _
        (progBounded_varCountedDec_rfield (ofString "i") (ofString "lst") 1 .lower (Or.inr rfl)
          (cost := 2 ^ 64 + K_lc + 18)
          (countedStep_decCall _ _ _ _ (by decide) (funBounded_tx_fixed_bytes K_lc h_lc)
            (countedStep_seq _ (progBounded_memcpy_const none _ _ 32 (by decide)) rfl rfl countedStep_incr))
          rfl
          (ProgBounded.straight _ rfl))))
    (by omega)

theorem funBounded_decode_authorizations (K_lc : Nat)
    (h_lc : FunBounded (ofString "rlp_list_count") K_lc) :
    FunBounded (ofString "decode_authorizations")
      (K_lc + 6 + (2 ^ 64 - 1) * (2 ^ 64 + 3) +
        (2 ^ 64 - 1) *
          (8 * K_lc + 9 * 2 ^ 64 + 146 + (2 ^ 64 - 1) * (2 ^ 64 + 3))) := by
  refine funBounded_of_guestAst 305 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_decode_authorizations _ rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_decode_authorizations,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall (funBounded_rlp_list_to_slices K_lc h_lc) _ _ _
      (ProgBounded.decCall funBounded_alloc _ _ _
        (progBounded_varCountedDec_rfield (ofString "i") (ofString "lst") 1 .lower (Or.inr rfl)
          (cost := 8 * K_lc + 9 * 2 ^ 64 + 145 + (2 ^ 64 - 1) * (2 ^ 64 + 3))
          (countedStep_decCall _ _ _ _ (by decide) (funBounded_rlp_item K_lc h_lc)
            (countedStep_seq_straight _ rfl rfl rfl
              (countedStep_decCall _ _ _ _ (by decide) (funBounded_rlp_list_to_slices K_lc h_lc)
                (countedStep_seq_straight _ rfl rfl rfl
                  (countedStep_dec _ _ _ (by decide)
                    (countedStep_decCall _ _ _ _ (by decide) (funBounded_tx_scalar_u256 K_lc h_lc)
                      (countedStep_seq_straight _ rfl rfl rfl
                        (countedStep_decCall _ _ _ _ (by decide) (funBounded_tx_fixed_bytes K_lc h_lc)
                          (countedStep_seq_straight _ rfl rfl rfl
                            (countedStep_decCall _ _ _ _ (by decide) (funBounded_tx_scalar_word K_lc h_lc)
                              (countedStep_seq_straight _ rfl rfl rfl
                                (countedStep_seq _
                                  (ProgBounded.call (funBounded_tx_scalar_word K_lc h_lc) _ _)
                                  rfl rfl
                                  (countedStep_seq_straight _ rfl rfl rfl
                                    (countedStep_decCall _ _ _ _ (by decide) (funBounded_tx_scalar_u256 K_lc h_lc)
                                      (countedStep_seq_straight _ rfl rfl rfl
                                        (countedStep_decCall _ _ _ _ (by decide) (funBounded_tx_scalar_u256 K_lc h_lc)
                                          (countedStep_seq_straight _ rfl rfl rfl countedStep_incr)))))))))))))))))
          rfl
          (ProgBounded.straight _ rfl))))
    (by omega)

theorem funBounded_decode_transaction_rlp (K_lc : Nat)
    (h_lc : FunBounded (ofString "rlp_list_count") K_lc) :
    FunBounded (ofString "decode_transaction_rlp")
      (19 * K_lc + 16 * 2 ^ 64 + 420 + 4 * ((2 ^ 64 - 1) * (2 ^ 64 + 3)) +
        (2 ^ 64 - 1) *
          (5 * K_lc + 3 * 2 ^ 64 + 34 + 2 * ((2 ^ 64 - 1) * (2 ^ 64 + 3)) +
            (2 ^ 64 - 1) * (2 ^ 64 + K_lc + 19)) +
        (2 ^ 64 - 1) * (2 ^ 64 + K_lc + 19) +
        (2 ^ 64 - 1) * (8 * K_lc + 9 * 2 ^ 64 + 146 + (2 ^ 64 - 1) * (2 ^ 64 + 3))) := by
  refine funBounded_of_guestAst 306 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_decode_transaction_rlp _ rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_decode_transaction_rlp,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.seq (ProgBounded.straight _ rfl)
      (ProgBounded.dec _ _ _
        (ProgBounded.decCall funBounded_alloc _ _ _
          (ProgBounded.seq (progBounded_memzero_const none _ 400 (by decide))
            (ProgBounded.seq (ProgBounded.straight _ rfl)
              (ProgBounded.seq (ProgBounded.straight _ rfl)
                (ProgBounded.dec _ _ _
                  (ProgBounded.dec _ _ _
                    (ProgBounded.dec _ _ _
                      (ProgBounded.seq
                        (ProgBounded.iteMax _
                          (ProgBounded.seq (ProgBounded.call (funBounded_rlp_decode_fully K_lc h_lc) _ _)
                            (ProgBounded.straight _ rfl))
                          (ProgBounded.iteMax _
                            (ProgBounded.call (funBounded_rlp_decode_fully K_lc h_lc) _ _)
                            (ProgBounded.straight _ rfl)))
                        (ProgBounded.seq (ProgBounded.straight _ rfl)
                          (ProgBounded.seq (ProgBounded.straight _ rfl)
                            (ProgBounded.decCall (funBounded_rlp_list_to_slices K_lc h_lc) _ _ _
                              (ProgBounded.dec _ _ _
                                (ProgBounded.seq (ProgBounded.straight _ rfl)
                                  (ProgBounded.dec _ _ _
                                    (ProgBounded.dec _ _ _
                                      (ProgBounded.seq
                                        (ProgBounded.iteMax _
                                          (ProgBounded.seq (ProgBounded.call (funBounded_tx_scalar_word K_lc h_lc) _ _)
                                            (ProgBounded.straight _ rfl))
                                          (ProgBounded.straight _ rfl))
                                        (ProgBounded.dec _ _ _
                                          (ProgBounded.seq
                                            (ProgBounded.iteMax _
                                              (ProgBounded.seq (ProgBounded.call (funBounded_tx_scalar_word K_lc h_lc) _ _)
                                                (ProgBounded.straight _ rfl))
                                              (ProgBounded.call (funBounded_tx_scalar_u256 K_lc h_lc) _ _))
                                            (ProgBounded.seq (ProgBounded.straight _ rfl)
                                              (ProgBounded.seq (ProgBounded.straight _ rfl)
                                                (ProgBounded.seq
                                                  (ProgBounded.iteMax _
                                                    (ProgBounded.seq (ProgBounded.call (funBounded_tx_scalar_u256 K_lc h_lc) _ _)
                                                      (ProgBounded.straight _ rfl))
                                                    (ProgBounded.seq (ProgBounded.call (funBounded_tx_scalar_u256 K_lc h_lc) _ _)
                                                      (ProgBounded.seq (ProgBounded.straight _ rfl)
                                                        (ProgBounded.seq (ProgBounded.call (funBounded_tx_scalar_u256 K_lc h_lc) _ _)
                                                          (ProgBounded.straight _ rfl)))))
                                                  (ProgBounded.seq (ProgBounded.call (funBounded_tx_scalar_word K_lc h_lc) _ _)
                                                    (ProgBounded.seq (ProgBounded.straight _ rfl)
                                                      (ProgBounded.seq (ProgBounded.straight _ rfl)
                                                        (ProgBounded.seq
                                                          (ProgBounded.iteMax _
                                                            (ProgBounded.call (funBounded_tx_fixed_bytes K_lc h_lc) _ _)
                                                            (ProgBounded.call (funBounded_tx_to_item K_lc h_lc) _ _))
                                                          (ProgBounded.seq (ProgBounded.straight _ rfl)
                                                            (ProgBounded.seq (ProgBounded.straight _ rfl)
                                                              (ProgBounded.seq (ProgBounded.call (funBounded_tx_scalar_u256 K_lc h_lc) _ _)
                                                                (ProgBounded.seq (ProgBounded.straight _ rfl)
                                                                  (ProgBounded.seq (ProgBounded.straight _ rfl)
                                                                    (ProgBounded.decCall (funBounded_tx_bytes_item K_lc h_lc) _ _ _
                                                                      (ProgBounded.seq (ProgBounded.straight _ rfl)
                                                                        (ProgBounded.seq (ProgBounded.straight _ rfl)
                                                                          (ProgBounded.seq (ProgBounded.straight _ rfl)
                                                                            (ProgBounded.seq
                                                                              (ProgBounded.iteMax _
                                                                                (ProgBounded.decCall (funBounded_tx_list_item K_lc h_lc) _ _ _
                                                                                  (ProgBounded.decCall (funBounded_decode_access_list K_lc h_lc) _ _ _
                                                                                    (ProgBounded.straight _ rfl)))
                                                                                (ProgBounded.straight _ rfl))
                                                                              (ProgBounded.seq
                                                                                (ProgBounded.iteMax _
                                                                                  (ProgBounded.seq (ProgBounded.call (funBounded_tx_scalar_u256 K_lc h_lc) _ _)
                                                                                    (ProgBounded.seq (ProgBounded.straight _ rfl)
                                                                                      (ProgBounded.decCall (funBounded_tx_list_item K_lc h_lc) _ _ _
                                                                                        (ProgBounded.decCall (funBounded_decode_blob_hashes K_lc h_lc) _ _ _
                                                                                          (ProgBounded.straight _ rfl)))))
                                                                                  (ProgBounded.straight _ rfl))
                                                                                (ProgBounded.seq
                                                                                  (ProgBounded.iteMax _
                                                                                    (ProgBounded.decCall (funBounded_tx_list_item K_lc h_lc) _ _ _
                                                                                      (ProgBounded.decCall (funBounded_decode_authorizations K_lc h_lc) _ _ _
                                                                                        (ProgBounded.straight _ rfl)))
                                                                                    (ProgBounded.straight _ rfl))
                                                                                  (ProgBounded.seq (ProgBounded.call (funBounded_tx_scalar_u256 K_lc h_lc) _ _)
                                                                                    (ProgBounded.seq (ProgBounded.straight _ rfl)
                                                                                      (ProgBounded.seq (ProgBounded.call (funBounded_tx_scalar_u256 K_lc h_lc) _ _)
                                                                                        (ProgBounded.seq (ProgBounded.straight _ rfl)
                                                                                          (ProgBounded.seq (ProgBounded.call (funBounded_tx_scalar_u256 K_lc h_lc) _ _)
                                                                                            (ProgBounded.straight _ rfl))))))))))))))))))))))))))))))))))))))
    (by omega)

theorem funBounded_decode_transaction (K_lc : Nat)
    (h_lc : FunBounded (ofString "rlp_list_count") K_lc) :
    FunBounded (ofString "decode_transaction")
      (19 * K_lc + 16 * 2 ^ 64 + 421 + 4 * ((2 ^ 64 - 1) * (2 ^ 64 + 3)) +
        (2 ^ 64 - 1) *
          (5 * K_lc + 3 * 2 ^ 64 + 34 + 2 * ((2 ^ 64 - 1) * (2 ^ 64 + 3)) +
            (2 ^ 64 - 1) * (2 ^ 64 + K_lc + 19)) +
        (2 ^ 64 - 1) * (2 ^ 64 + K_lc + 19) +
        (2 ^ 64 - 1) * (8 * K_lc + 9 * 2 ^ 64 + 146 + (2 ^ 64 - 1) * (2 ^ 64 + 3))) := by
  refine funBounded_of_guestAst 307 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_decode_transaction _ rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_decode_transaction,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.dec _ _ _
      (ProgBounded.dec _ _ _
        (ProgBounded.seq
          (ProgBounded.handledCall (funBounded_decode_transaction_rlp K_lc h_lc) _ _ _ _
            (ProgBounded.straight _ rfl))
          (ProgBounded.straight _ rfl))))
    (by omega)

-- ============================================================================
-- Section 4: MPT & Account Functions (guestAst[247..294])
-- ============================================================================

theorem funBounded_mpt_init : FunBounded (ofString "mpt_init") 559 := by
  refine funBounded_of_guestAst 247 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_mpt_init 559 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_mpt_init,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.seq (ProgBounded.call funBounded_alloc _ _)
      (ProgBounded.seq (ProgBounded.call funBounded_alloc _ _)
        (ProgBounded.seq (ProgBounded.call funBounded_alloc _ _)
          (ProgBounded.seq (ProgBounded.call funBounded_alloc _ _)
            (ProgBounded.seq (ProgBounded.call funBounded_alloc _ _)
              (ProgBounded.seq (ProgBounded.straight _ rfl)
                (ProgBounded.seq (progBounded_keccak256_const none _ _ 1 (by decide))
                  (ProgBounded.seq (progBounded_keccak256_const none _ _ 0 (by decide))
                    (ProgBounded.straight _ rfl)))))))))
    (by decide)

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
  let s1 := setVarHOLFinite (ofString "i") (.val (.word 0)) state
  have hs1_code : s1.code = originalRuntimeCode := hcode
  have hs1_i : s1.locals.lookup (ofString "i") = some (.val (.word 0)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word K)) := by
    have hne : ofString "i" ≠ ofString "n" := by decide
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, atN]
  have hcb4 :
      CountedBody (ofString "i") 4
        (.dec (ofString "b0") .one (.loadByte (.op .add [.var .local (ofString "key"), .var .local (ofString "i")]))
          (.seq
            (.storeByte (.op .add [.var .local (ofString "out"), .panop .mul [.const 2, .var .local (ofString "i")]])
              (.shift .lsr (.var .local (ofString "b0")) (.const 4)))
            (.seq
              (.storeByte (.op .add [.var .local (ofString "out"), .panop .mul [.const 2, .var .local (ofString "i")], .const 1])
                (.op .and [.var .local (ofString "b0"), .const 15]))
              (.dec (ofString "b1") .one (.loadByte (.op .add [.var .local (ofString "key"), .var .local (ofString "i"), .const 1]))
                (.seq
                  (.storeByte (.op .add [.var .local (ofString "out"), .panop .mul [.const 2, .var .local (ofString "i")], .const 2])
                    (.shift .lsr (.var .local (ofString "b1")) (.const 4)))
                  (.seq
                    (.storeByte (.op .add [.var .local (ofString "out"), .panop .mul [.const 2, .var .local (ofString "i")], .const 3])
                      (.op .and [.var .local (ofString "b1"), .const 15]))
                    (.dec (ofString "b2") .one (.loadByte (.op .add [.var .local (ofString "key"), .var .local (ofString "i"), .const 2]))
                      (.seq
                        (.storeByte (.op .add [.var .local (ofString "out"), .panop .mul [.const 2, .var .local (ofString "i")], .const 4])
                          (.shift .lsr (.var .local (ofString "b2")) (.const 4)))
                        (.seq
                          (.storeByte (.op .add [.var .local (ofString "out"), .panop .mul [.const 2, .var .local (ofString "i")], .const 5])
                            (.op .and [.var .local (ofString "b2"), .const 15]))
                          (.dec (ofString "b3") .one (.loadByte (.op .add [.var .local (ofString "key"), .var .local (ofString "i"), .const 3]))
                            (.seq
                              (.storeByte (.op .add [.var .local (ofString "out"), .panop .mul [.const 2, .var .local (ofString "i")], .const 6])
                                (.shift .lsr (.var .local (ofString "b3")) (.const 4)))
                              (.seq
                                (.storeByte (.op .add [.var .local (ofString "out"), .panop .mul [.const 2, .var .local (ofString "i")], .const 7])
                                  (.op .and [.var .local (ofString "b3"), .const 15]))
                                (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 4]))))))))))))))
        0 := by
    simpa using
      CountedBody.dec (ofString "b0") .one _ (by decide)
        (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
          (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
            (CountedBody.dec (ofString "b1") .one _ (by decide)
              (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
                (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
                  (CountedBody.dec (ofString "b2") .one _ (by decide)
                    (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
                      (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
                        (CountedBody.dec (ofString "b3") .one _ (by decide)
                          (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
                            (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
                              CountedBody.incr)))))))))))
  have hstride := notLowerStrideWhile_run (ofString "i") (ofString "n") K 4
    (by simpa using hsmall) (by decide) hcb4 rfl rfl (K.toNat / 4) s1 hs1_code 0 hs1_i hs1_n
    (by simp) (by simp) (by change (K.toNat / 4) * 1 ≤ state.clock; omega)
  have hloop4 : RunBounded s1 _ (K.toNat / 4) := by
    simpa only [Nat.zero_add, Nat.mul_one] using
      (⟨hstride.1, hstride.2.1, hstride.2.2.1⟩ : RunBounded s1 _ ((K.toNat / 4) * (0 + 1)))
  refine (RunBounded.seq (state := s1) (a := K.toNat / 4) (b := 3) hloop4
    (by change K.toNat / 4 + 3 ≤ state.clock; omega) (fun s2 hr2 hs2_code hs2_clk => ?_)).weaken (by omega)
  have hpost := hstride.2.2.2 (by rw [hr2])
  rw [hr2] at hpost
  obtain ⟨w', hw'_i, hw'_n, _, hw'_le, hw'_rem, _⟩ := hpost
  have hs2_code' : s2.code = originalRuntimeCode := hs2_code.trans hs1_code
  have hrem_le3 : K.toNat - w'.toNat ≤ 3 := by
    change K.toNat < w'.toNat + 4 at hw'_rem
    omega
  have hcb1 :
      CountedBody (ofString "i") 1
        (.dec (ofString "b") .one (.loadByte (.op .add [.var .local (ofString "key"), .var .local (ofString "i")]))
          (.seq
            (.storeByte (.op .add [.var .local (ofString "out"), .panop .mul [.const 2, .var .local (ofString "i")]])
              (.shift .lsr (.var .local (ofString "b")) (.const 4)))
            (.seq
              (.storeByte (.op .add [.var .local (ofString "out"), .panop .mul [.const 2, .var .local (ofString "i")], .const 1])
                (.op .and [.var .local (ofString "b"), .const 15]))
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))))
        0 := by
    simpa using
      CountedBody.dec (ofString "b") .one _ (by decide)
        (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
          (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
            CountedBody.incr))
  have hloop1_raw := variableCountedWhile_run (ofString "i") (ofString "n") .lower (Or.inr rfl) K
    (fun h => by cases h) hcb1 rfl (K.toNat - w'.toNat) s2 hs2_code' w' hw'_i hw'_n hw'_le rfl
    (by simp only [Nat.zero_add, Nat.mul_one]; omega)
  simp only [Nat.zero_add, Nat.mul_one] at hloop1_raw
  have hloop1 : RunBounded s2 _ 3 := RunBounded.weaken hloop1_raw hrem_le3
  exact (RunBounded.seq (state := s2) (a := 3) (b := 0) hloop1 (by omega)
    (fun s3 _ hs3_code hs3_clk =>
      (ProgBounded.straight (.return (.const 0)) rfl) s3 (hs3_code.trans hs2_code') hs3_clk)).weaken (by omega)

theorem progBounded_key_to_nibbles_exp (destination : Option (VarKind × MlS)) (key sizeExp out : ExpHOL 64)
    (K : BitVec 64) (hsmall : K.toNat + 4 < 2 ^ 64)
    (heval : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) sizeExp = some (.val (.word K))) :
    ProgBounded (.call (some (destination, none)) (ofString "key_to_nibbles") [key, sizeExp, out])
      (K.toNat / 4 + 4) := by
  intro F state hcode hbudget
  cases hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [key, sizeExp, out] with
  | none =>
    rw [evaluateHOLFiniteState_call, hargs]
    simp
  | some vs =>
    obtain ⟨v1, v3, rfl⟩ := evalListHOLFinite_three_word2 state key sizeExp out K hargs (heval state)
    exact RunBounded.call hargs hbudget (fun body locals rs hfound => by
      rw [hcode] at hfound
      obtain ⟨rfl, hn⟩ := three_arg_lookup_mid originalRuntimeCode.lookup
        (ofString "key_to_nibbles") (ofString "key") (ofString "n") (ofString "out")
        (sourceFnBody Guest.Software.guestFn_key_to_nibbles)
        (by decide) (by decide) (by decide) lookup_key_to_nibbles hfound
      exact runBounded_key_to_nibbles_body (callEntryStateHOLFinite state locals) K hsmall hcode hn
        (by change K.toNat / 4 + 3 ≤ state.clock - 1; omega))

theorem progBounded_key_to_nibbles_const (destination : Option (VarKind × MlS)) (key out : ExpHOL 64)
    (K : BitVec 64) (hsmall : K.toNat + 4 < 2 ^ 64) :
    ProgBounded (.call (some (destination, none)) (ofString "key_to_nibbles") [key, .const K, out])
      (K.toNat / 4 + 4) :=
  progBounded_key_to_nibbles_exp destination key (.const K) out K hsmall
    (fun _ => by rw [evalHOLFinite_eq_toExact]; rfl)

private theorem lookup_mpt_fail :
    originalRuntimeCode.lookup (ofString "mpt_fail") =
      some ([(ofString "code", .one)], sourceFnBody Guest.Software.guestFn_mpt_fail, .one) :=
  lookup_of_guestAst_getElem 246 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_mpt_fail) rfl

private theorem call_mpt_fail_never_none {F : Type}
    (s next : PanSemStateFiniteExact 64 F) (c : BitVec 64)
    (hcode : s.code = originalRuntimeCode) :
    evaluateHOLFiniteState s (.call (some (none, none)) (ofString "mpt_fail") [.const c]) ≠ (none, next) := by
  intro hr
  rw [evaluateHOLFiniteState_call] at hr
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [.const c] =
      some [.val (.word c)] := by
    rw [evalListHOLFinite_eq_toExact]
    rfl
  rw [hargs] at hr
  dsimp only at hr
  rw [hcode, pan_one_word_lookup originalRuntimeCode.lookup (ofString "mpt_fail") (ofString "code")
    (sourceFnBody Guest.Software.guestFn_mpt_fail) c lookup_mpt_fail] at hr
  dsimp only at hr
  split at hr
  · simp at hr
  · dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_mpt_fail,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at hr
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_raise] at hr
    split at hr
    · dsimp only at hr
      split at hr <;> simp at hr
    · simp at hr

private theorem lookup_compact_to_nibbles :
    originalRuntimeCode.lookup (ofString "compact_to_nibbles") =
      some ([(ofString "p", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_compact_to_nibbles, .comb [.one, .one, .one]) :=
  lookup_of_guestAst_getElem 249 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_compact_to_nibbles) rfl

theorem runBounded_compact_to_nibbles_body {F : Type}
    (state : PanSemStateFiniteExact 64 F) (K : BitVec 64)
    (hsmall : K.toNat + 3 < 2 ^ 64)
    (hcode : state.code = originalRuntimeCode)
    (atN : state.locals.lookup (ofString "n") = some (.val (.word K)))
    (hbudget : K.toNat / 4 + 7 ≤ state.clock) :
    RunBounded state (sourceFnBody Guest.Software.guestFn_compact_to_nibbles) (K.toNat / 4 + 7) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_compact_to_nibbles,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  let p_guard : ProgHOL 64 :=
    .ite (.cmp .equal (.var .local (ofString "n")) (.const 0))
      (.call (some (none, none)) (ofString "mpt_fail") [.const 5])
      .skip
  have hguard : RunBounded state p_guard 1 :=
    (ProgBounded.weaken
      (ProgBounded.iteMax _ (ProgBounded.call funBounded_mpt_fail none _) (ProgBounded.straight .skip rfl))
      (by decide : max (0 + 1) 0 ≤ 1)) state hcode (by omega)
  refine (RunBounded.seq (state := state) (a := 1) (b := K.toNat / 4 + 6) hguard
    (by omega) (fun s1 hr1 hs1_code hs1_clk => ?_)).weaken (by omega)
  have hk_ne : K ≠ 0 := by
    intro hk0
    subst hk0
    have hcond : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
        (.cmp .equal (.var .local (ofString "n")) (.const 0)) = some (.val (.word 1)) := by
      simp [evalHOLExact, atN, Compiler.Encoders.Asm.wordCmpHOL]
    change evaluateHOLFiniteState state p_guard = (none, s1) at hr1
    rw [evaluateHOLFiniteState_ite, hcond] at hr1
    simp only [show ¬((1 : BitVec 64) = 0) by decide, if_false] at hr1
    exact call_mpt_fail_never_none state s1 5 hcode hr1
  have hk_pos : 0 < K.toNat := Nat.pos_of_ne_zero (fun h0 => hk_ne (BitVec.eq_of_toNat_eq (by simpa using h0)))
  have hkm1_nat : (K - 1).toNat = K.toNat - 1 := by
    have hle : (1 : BitVec 64) ≤ K := by rw [BitVec.le_def]; change 1 ≤ K.toNat; omega
    exact BitVec.toNat_sub_of_le hle
  have hkm1_small : (K - 1).toNat + 4 < 2 ^ 64 := by omega
  have hs1_code' : s1.code = originalRuntimeCode := hs1_code.trans hcode
  have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word K)) := by
    have hpres := evaluate_avoidsLocal_flowing (ofString "n") p_guard rfl state (by rw [hr1]; exact Or.inl rfl)
    rw [hr1] at hpres
    exact hpres.trans atN
  refine RunBounded.dec s1 (ofString "c0") .one _ (fun vc0 _ => ?_)
  let s2 := setVarHOLFinite (ofString "c0") vc0 s1
  refine RunBounded.dec s2 (ofString "first") .one _ (fun vfirst _ => ?_)
  let s3 := setVarHOLFinite (ofString "first") vfirst s2
  refine RunBounded.dec s3 (ofString "is_leaf") .one _ (fun visleaf _ => ?_)
  let s4 := setVarHOLFinite (ofString "is_leaf") visleaf s3
  refine RunBounded.dec s4 (ofString "odd") .one _ (fun vodd _ => ?_)
  let s5 := setVarHOLFinite (ofString "odd") vodd s4
  have hs5_code : s5.code = originalRuntimeCode := hs1_code'
  have hs5_n : s5.locals.lookup (ofString "n") = some (.val (.word K)) := by
    simp only [s5, s4, s3, s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_n]
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide)]
  cases hargs : evalListHOLFinite s5 (h := fun a => Classical.propDecidable (s5.memaddrs a))
      [.panop .mul [.const 2, .var .local (ofString "n")]] with
  | none =>
    unfold RunBounded
    rw [evaluateHOLFiniteState_decCall_args_none s5 (ofString "out") .one (ofString "alloc") _ _ hargs]
    simp
  | some vs =>
    exact (RunBounded.decCall (state := s5) (name := ofString "out") (shape := .one)
      (function := ofString "alloc") (bodyCost := 1) (tailCost := K.toNat / 4 + 4) hargs
      (by change 1 + 1 + (K.toNat / 4 + 4) ≤ s1.clock; omega)
      (fun body locals rs hfound => by
        refine ⟨ProgBounded.bodies_of_fun funBounded_alloc s5 hs5_code
          (by change 1 + 1 ≤ s1.clock; omega) vs body locals rs hfound, ?_⟩
        intro vout post hran hpost_clk
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s5 locals) body).1
        rw [hran] at hmeta
        let s6 := setVarHOLFinite (ofString "out") vout { post with locals := s5.locals }
        have hs6_code : s6.code = originalRuntimeCode := hmeta.trans hs5_code
        have hs6_n : s6.locals.lookup (ofString "n") = some (.val (.word K)) := by
          have hne : ofString "out" ≠ ofString "n" := by decide
          simp [s6, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hs5_n]
        apply RunBounded.decConst
        let s7 := setVarHOLFinite (ofString "k") (.val (.word 0)) s6
        have hs7_code : s7.code = originalRuntimeCode := hs6_code
        have hs7_n : s7.locals.lookup (ofString "n") = some (.val (.word K)) := by
          have hne : ofString "k" ≠ ofString "n" := by decide
          simp [s7, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hs6_n]
        let p_odd : ProgHOL 64 :=
          .ite (.cmp .notEqual (.var .local (ofString "odd")) (.const 0))
            (.seq
              (.storeByte (.var .local (ofString "out")) (.op .and [.var .local (ofString "c0"), .const 15]))
              (.assign .local (ofString "k") (.const 1)))
            .skip
        have hodd := (ProgBounded.straight p_odd rfl) s7 hs7_code (by simp)
        refine (RunBounded.seq (state := s7) (a := 0) (b := K.toNat / 4 + 4) hodd
          (by change 0 + (K.toNat / 4 + 4) ≤ post.clock; omega) (fun s8 hr8 hs8_code hs8_clk => ?_)).weaken (by omega)
        have hs8_code' : s8.code = originalRuntimeCode := hs8_code.trans hs7_code
        have hs8_n : s8.locals.lookup (ofString "n") = some (.val (.word K)) := by
          have hpres := evaluate_avoidsLocal_flowing (ofString "n") p_odd rfl s7 (by rw [hr8]; exact Or.inl rfl)
          rw [hr8] at hpres
          exact hpres.trans hs7_n
        have hktn : RunBounded s8
            (.call (some (none, none)) (ofString "key_to_nibbles")
              [.op .add [.var .local (ofString "p"), .const 1],
               .op .sub [.var .local (ofString "n"), .const 1],
               .op .add [.var .local (ofString "out"), .var .local (ofString "k")]])
            ((K - 1).toNat / 4 + 4) := by
          have heq_call : evaluateHOLFiniteState s8
              (.call (some (none, none)) (ofString "key_to_nibbles")
                [.op .add [.var .local (ofString "p"), .const 1],
                 .op .sub [.var .local (ofString "n"), .const 1],
                 .op .add [.var .local (ofString "out"), .var .local (ofString "k")]]) =
            evaluateHOLFiniteState s8
              (.call (some (none, none)) (ofString "key_to_nibbles")
                [.op .add [.var .local (ofString "p"), .const 1],
                 .const (K - 1),
                 .op .add [.var .local (ofString "out"), .var .local (ofString "k")]]) := by
            have hlist : evalListHOLFinite s8 (h := fun a => Classical.propDecidable (s8.memaddrs a))
                [.op .add [.var .local (ofString "p"), .const 1],
                 .op .sub [.var .local (ofString "n"), .const 1],
                 .op .add [.var .local (ofString "out"), .var .local (ofString "k")]] =
              evalListHOLFinite s8 (h := fun a => Classical.propDecidable (s8.memaddrs a))
                [.op .add [.var .local (ofString "p"), .const 1],
                 .const (K - 1),
                 .op .add [.var .local (ofString "out"), .var .local (ofString "k")]] := by
              rw [evalListHOLFinite_eq_toExact, evalListHOLFinite_eq_toExact]
              simp [evalListHOLExact, evalHOLExact, hs8_n, Compiler.Encoders.Asm.wordOpHOL, wordOp, valueIsWord, valueWord]
            rw [evaluateHOLFiniteState_call, evaluateHOLFiniteState_call, hlist]
          unfold RunBounded
          rw [heq_call]
          exact progBounded_key_to_nibbles_const none
            (.op .add [.var .local (ofString "p"), .const 1])
            (.op .add [.var .local (ofString "out"), .var .local (ofString "k")])
            (K - 1) hkm1_small s8 hs8_code' (by omega)
        have hle_div : (K - 1).toNat / 4 + 4 ≤ K.toNat / 4 + 4 := by omega
        exact (RunBounded.seq (state := s8) (a := K.toNat / 4 + 4) (b := 0) (hktn.weaken hle_div)
          (by omega) (fun s9 _ hs9_code hs9_clk =>
            (ProgBounded.straight (.return _) rfl) s9 (hs9_code.trans hs8_code') hs9_clk)).weaken (by omega))).weaken (by omega)

theorem progBounded_compact_to_nibbles_decCall_exp (name : MlS) (shape : ShapeHOL) (p sizeExp : ExpHOL 64)
    (K : BitVec 64) {continuation : ProgHOL 64} {tailCost : Nat}
    (hsmall : K.toNat + 3 < 2 ^ 64)
    (heval : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) sizeExp = some (.val (.word K)))
    (hrest : ProgBounded continuation tailCost) :
    ProgBounded (.decCall name shape (ofString "compact_to_nibbles") [p, sizeExp] continuation)
      (K.toNat / 4 + 8 + tailCost) := by
  intro F state hcode hbudget
  cases hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [p, sizeExp] with
  | none =>
    rw [evaluateHOLFiniteState_decCall_args_none state name shape (ofString "compact_to_nibbles") [p, sizeExp] continuation hargs]
    simp
  | some vs =>
    have hk := heval state
    obtain ⟨v1, rfl⟩ : ∃ v1, vs = [v1, .val (.word K)] := by
      rw [evalListHOLFinite_eq_toExact] at hargs
      rw [evalHOLFinite_eq_toExact] at hk
      simp only [evalListHOLExact] at hargs
      rw [hk] at hargs
      rcases h1 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) p with _ | v1
      · rw [h1] at hargs; cases hargs
      · rw [h1] at hargs; cases hargs; exact ⟨v1, rfl⟩
    have h := RunBounded.decCall (name := name) (shape := shape) (continuation := continuation)
      (bodyCost := K.toNat / 4 + 7) (tailCost := tailCost) hargs (by omega)
      (fun body locals rs hfound => by
        rw [hcode] at hfound
        have hbody := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup
          (ofString "compact_to_nibbles") _ (sourceFnBody Guest.Software.guestFn_compact_to_nibbles) body
          (.comb [.one, .one, .one]) rs [v1, .val (.word K)] locals lookup_compact_to_nibbles hfound
        subst hbody
        have hn : locals.lookup (ofString "n") = some (.val (.word K)) := by
          cases v1 with
          | rStruct _ =>
            unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
            split at hfound
            · cases hfound
            · rename_i _ _ _ raw
              simp [lookupCodeHOLExact, lookup_compact_to_nibbles, shapeOfHOLExact, shapeEqHOL] at raw
          | nStruct _ _ =>
            unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
            split at hfound
            · cases hfound
            · rename_i _ _ _ raw
              simp [lookupCodeHOLExact, lookup_compact_to_nibbles, shapeOfHOLExact, shapeEqHOL] at raw
          | val wl1 =>
            cases wl1 with
            | word w1 =>
              have hdiff : ofString "p" ≠ ofString "n" := by decide
              have hraw : lookupCodeHOLExact originalRuntimeCode.lookup (ofString "compact_to_nibbles")
                  [.val (.word w1), .val (.word K)] =
                  some (sourceFnBody Guest.Software.guestFn_compact_to_nibbles,
                    (fun key => if key = ofString "n" then some (.val (.word K))
                      else if key = ofString "p" then some (.val (.word w1)) else none),
                    .comb [.one, .one, .one]) := by
                simp [lookupCodeHOLExact, lookup_compact_to_nibbles, shapeOfHOLExact, shapeEqHOL, hdiff]
              unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
              split at hfound
              · rename_i missing
                rw [hraw] at missing
                cases missing
              · rename_i _ exactLocals _ found
                have equal := Option.some.inj (found.symm.trans hraw)
                obtain ⟨_, rest⟩ := Prod.mk.inj equal
                obtain ⟨rfl, _⟩ := Prod.mk.inj rest
                have heq := Option.some.inj hfound
                obtain ⟨_, hloc2⟩ := Prod.mk.inj heq
                obtain ⟨rfl, _⟩ := Prod.mk.inj hloc2
                rfl
        have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state locals)
          (sourceFnBody Guest.Software.guestFn_compact_to_nibbles)
        refine ⟨runBounded_compact_to_nibbles_body (callEntryStateHOLFinite state locals) K hsmall hcode hn
          (by change K.toNat / 4 + 7 ≤ state.clock - 1; omega), ?_⟩
        intro value post hran hpost_clk
        rw [hran] at hmeta
        exact hrest _ (hmeta.1.trans hcode) hpost_clk)
    exact h.weaken (by omega)

theorem funBounded_nibble_list_to_compact :
    FunBounded (ofString "nibble_list_to_compact") (2 ^ 63) := by
  refine funBounded_of_guestAst 250 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_nibble_list_to_compact (2 ^ 63) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_nibble_list_to_compact,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply ProgBounded.dec
  intro F state hcode hbudget
  apply RunBounded.decConst
  let s1 := setVarHOLFinite (ofString "i") (.val (.word 0)) state
  have hs1_code : s1.code = originalRuntimeCode := hcode
  cases hn0 : state.locals.lookup (ofString "n") with
  | none =>
    change RunBounded s1 _ (2 ^ 63)
    unfold RunBounded
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
    have hnone : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
        (.cmp .equal (.op .and [.var .local (ofString "n"), .const (BitVec.ofNat 64 1)]) (.const (BitVec.ofNat 64 0))) = none := by
      have hs1_n : s1.locals.lookup (ofString "n") = none := by
        have hne : ofString "i" ≠ ofString "n" := by decide
        simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hn0]
      simp [evalHOLExact, evalListHOLExact, hs1_n]
    rw [hnone]
    simp
  | some nval =>
    cases nval with
    | rStruct flds =>
      change RunBounded s1 _ (2 ^ 63)
      unfold RunBounded
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
      have hnone : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
          (.cmp .equal (.op .and [.var .local (ofString "n"), .const (BitVec.ofNat 64 1)]) (.const (BitVec.ofNat 64 0))) = none := by
        have hs1_n : s1.locals.lookup (ofString "n") = some (.rStruct flds) := by
          have hne : ofString "i" ≠ ofString "n" := by decide
          simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hn0]
        simp [evalHOLExact, evalListHOLExact, hs1_n, wordOpHOL, valueIsWord]
      rw [hnone]
      simp
    | nStruct snm flds =>
      change RunBounded s1 _ (2 ^ 63)
      unfold RunBounded
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
      have hnone : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
          (.cmp .equal (.op .and [.var .local (ofString "n"), .const (BitVec.ofNat 64 1)]) (.const (BitVec.ofNat 64 0))) = none := by
        have hs1_n : s1.locals.lookup (ofString "n") = some (.nStruct snm flds) := by
          have hne : ofString "i" ≠ ofString "n" := by decide
          simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hn0]
        simp [evalHOLExact, evalListHOLExact, hs1_n, wordOpHOL, valueIsWord]
      rw [hnone]
      simp
    | val wl =>
      cases wl with
      | word nw =>
        have hs1_i : s1.locals.lookup (ofString "i") = some (.val (.word 0)) := by
          simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word nw)) := by
          have hne : ofString "i" ≠ ofString "n" := by decide
          simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hn0]
        let p_hdr : ProgHOL 64 :=
          .ite (.cmp .equal (.op .and [.var .local (ofString "n"), .const 1]) (.const 0))
            (.storeByte (.var .local (ofString "dst")) (.panop .mul [.const 16, .var .local (ofString "flag")]))
            (.seq
              (.storeByte (.var .local (ofString "dst"))
                (.op .add [.panop .mul [.const 16, .op .add [.var .local (ofString "flag"), .const 1]],
                  .loadByte (.var .local (ofString "nibs"))]))
              (.assign .local (ofString "i") (.const 1)))
        have hhdr : RunBounded s1 p_hdr 0 := (ProgBounded.straight p_hdr rfl) s1 hs1_code (by simp)
        refine (RunBounded.seq (state := s1) (a := 0) (b := 2 ^ 63) hhdr
          (by change 0 + 2 ^ 63 ≤ state.clock; omega) (fun s2 hr2 hs2_code hs2_clk => ?_)).weaken (by omega)
        have hs2_n : s2.locals.lookup (ofString "n") = some (.val (.word nw)) := by
          have hpres := evaluate_avoidsLocal_flowing (ofString "n") p_hdr rfl s1 (by rw [hr2]; exact Or.inl rfl)
          rw [hr2] at hpres
          exact hpres.trans hs1_n
        have hs2_parity : ∃ iw : BitVec 64,
            s2.locals.lookup (ofString "i") = some (.val (.word iw)) ∧ iw.toNat % 2 = nw.toNat % 2 := by
          change evaluateHOLFiniteState s1 p_hdr = (none, s2) at hr2
          have hand_nat : (nw &&& (1 : BitVec 64)).toNat = nw.toNat % 2 := by
            have h1 := @BitVec.toNat_and 64 nw 1
            have hmod : nw.toNat &&& 1 = nw.toNat % 2 := Nat.and_one_is_mod nw.toNat
            simpa [hmod] using h1
          by_cases heven : nw &&& 1 = 0
          · have hmod0 : nw.toNat % 2 = 0 := by
              have hz : (nw &&& 1).toNat = 0 := by rw [heven]; rfl
              omega
            have hcond : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
                (.cmp .equal (.op .and [.var .local (ofString "n"), .const 1]) (.const 0)) =
                some (.val (.word 1)) := by
              have hmask : AndOp.and 1#64 18446744073709551615#64 = 1#64 := by decide
              have heven_op : AndOp.and nw 1#64 = 0#64 := heven
              simp [evalHOLExact, evalListHOLExact, hs1_n, wordOpHOL, wordOp,
                valueIsWord, valueWord, Compiler.Encoders.Asm.wordCmpHOL, hmask, heven_op]
            rw [evaluateHOLFiniteState_ite, hcond] at hr2
            dsimp only at hr2
            simp only [show ¬((1 : BitVec 64) = 0) by decide, if_false] at hr2
            have hpres_i := evaluate_avoidsLocal_flowing (ofString "i")
              (.storeByte (.var .local (ofString "dst")) (.panop .mul [.const 16, .var .local (ofString "flag")]))
              rfl s1 (by rw [hr2]; exact Or.inl rfl)
            rw [hr2] at hpres_i
            exact ⟨0, hpres_i.trans hs1_i, by simp [hmod0]⟩
          · have hmod1 : nw.toNat % 2 = 1 := by
              have hnz : (nw &&& 1).toNat ≠ 0 := fun hz =>
                heven (BitVec.eq_of_toNat_eq (by simpa using hz))
              omega
            have hcond : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
                (.cmp .equal (.op .and [.var .local (ofString "n"), .const 1]) (.const 0)) =
                some (.val (.word 0)) := by
              have hmask : AndOp.and 1#64 18446744073709551615#64 = 1#64 := by decide
              have heven_op : ¬AndOp.and nw 1#64 = 0#64 := heven
              simp [evalHOLExact, evalListHOLExact, hs1_n, wordOpHOL, wordOp,
                valueIsWord, valueWord, Compiler.Encoders.Asm.wordCmpHOL, hmask, heven_op]
            rw [evaluateHOLFiniteState_ite, hcond] at hr2
            dsimp only at hr2
            rw [if_pos rfl, evaluateHOLFiniteState_seq_line780] at hr2
            rcases hsb : evaluateHOLFiniteState s1
                (.storeByte (.var .local (ofString "dst"))
                  (.op .add [.panop .mul [.const 16, .op .add [.var .local (ofString "flag"), .const 1]],
                    .loadByte (.var .local (ofString "nibs"))])) with ⟨rsb, smid⟩
            rw [hsb] at hr2
            cases rsb with
            | some _ => simp at hr2
            | none =>
              dsimp only at hr2
              have hmid_i : smid.locals.lookup (ofString "i") = some (.val (.word 0)) := by
                have hpres_i := evaluate_avoidsLocal_flowing (ofString "i") _ rfl s1 (by rw [hsb]; exact Or.inl rfl)
                rw [hsb] at hpres_i
                exact hpres_i.trans hs1_i
              rw [evaluateHOLFiniteState_assign] at hr2
              simp [evalHOLExact, isValidValueHOLExact, lookupKvarHOLExact, hmid_i,
                shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite] at hr2
              subst hr2
              refine ⟨1, ?_, by simp [hmod1]⟩
              simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        obtain ⟨iw0, hs2_i, hpar0⟩ := hs2_parity
        apply RunBounded.decConst
        let s3 := setVarHOLFinite (ofString "o") (.val (.word 1)) s2
        have hs3_code : s3.code = originalRuntimeCode := hs2_code.trans hs1_code
        have hs3_i : s3.locals.lookup (ofString "i") = some (.val (.word iw0)) := by
          have hne : ofString "o" ≠ ofString "i" := by decide
          simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hs2_i]
        have hs3_n : s3.locals.lookup (ofString "n") = some (.val (.word nw)) := by
          have hne : ofString "o" ≠ ofString "n" := by decide
          simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hs2_n]
        let cond : ExpHOL 64 := .cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))
        let lbody : ProgHOL 64 :=
          .seq
            (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "o")])
              (.op .or
                [.shift .lsl (.loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i")])) (.const 4),
                 .loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i"), .const 1])]))
            (.seq
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 2]))
              (.assign .local (ofString "o") (.op .add [.var .local (ofString "o"), .const 1])))
        let Rank : ∀ {G : Type}, PanSemStateFiniteExact 64 G → Nat → Prop :=
          fun s r => ∃ iw : BitVec 64,
            s.locals.lookup (ofString "i") = some (.val (.word iw)) ∧
            s.locals.lookup (ofString "n") = some (.val (.word nw)) ∧
            (iw.toNat < nw.toNat → iw.toNat % 2 = nw.toNat % 2) ∧
            r = (nw.toNat - iw.toNat) / 2
        have hexit : ∀ {G : Type} (s : PanSemStateFiniteExact 64 G), Rank s 0 → ∀ w : BitVec 64,
            evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) cond = some (.val (.word w)) → w = 0 := by
          intro G s ⟨iw, hi, hn, hpar, hr0⟩ w heval
          rw [evalHOLFinite_eq_toExact] at heval
          by_cases hlt : iw.toNat < nw.toNat
          · have hp := hpar hlt
            omega
          · have hnotlt : ¬(iw < nw) := by rw [BitVec.lt_def]; exact hlt
            simp [cond, evalHOLExact, hi, hn, Compiler.Encoders.Asm.wordCmpHOL, hnotlt] at heval
            exact heval.symm
        have hstep : ∀ {G : Type} (s : PanSemStateFiniteExact 64 G) (k : Nat) (w : BitVec 64), s.code = originalRuntimeCode →
            Rank s (k + 1) →
            evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) cond = some (.val (.word w)) →
            w ≠ 0 → 0 + 1 ≤ s.clock →
            s.clock - 1 ≤ (evaluateHOLFiniteState (decClockHOLFinite s) lbody).2.clock + 0 ∧
              (evaluateHOLFiniteState (decClockHOLFinite s) lbody).2.clock ≤ s.clock - 1 ∧
              (evaluateHOLFiniteState (decClockHOLFinite s) lbody).1 ≠ some .timeOut ∧
              ((evaluateHOLFiniteState (decClockHOLFinite s) lbody).1 = none ∨
                  (evaluateHOLFiniteState (decClockHOLFinite s) lbody).1 = some .continue →
                ∃ m, m ≤ k ∧ Rank (evaluateHOLFiniteState (decClockHOLFinite s) lbody).2 m ∧
                  (evaluateHOLFiniteState (decClockHOLFinite s) lbody).2.code = s.code) ∧
              ((evaluateHOLFiniteState (decClockHOLFinite s) lbody).1 = some .break → False ∧
                ∃ m, Rank (evaluateHOLFiniteState (decClockHOLFinite s) lbody).2 m ∧
                  (evaluateHOLFiniteState (decClockHOLFinite s) lbody).2.code = s.code) := by
          intro G s k w scode ⟨iw, hi, hn, hpar, hrk⟩ heval hw_nz _
          have hlt : iw.toNat < nw.toNat := by
            rw [evalHOLFinite_eq_toExact] at heval
            by_contra hge
            have hnotlt : ¬(iw < nw) := by rw [BitVec.lt_def]; exact hge
            simp [cond, evalHOLExact, hi, hn, Compiler.Encoders.Asm.wordCmpHOL, hnotlt] at heval
            exact hw_nz heval.symm
          have hp := hpar hlt
          have hle2 : iw.toNat + 2 ≤ nw.toNat := by omega
          have hi2_nat : (iw + 2).toNat = iw.toNat + 2 := by
            rw [BitVec.toNat_add_of_lt (by have := nw.isLt; simp; omega)]
            rfl
          have hcb : CountedBody (ofString "i") 2
              (.seq
                (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "o")])
                  (.op .or
                    [.shift .lsl (.loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i")])) (.const 4),
                     .loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i"), .const 1])]))
                (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 2]))) 0 :=
            CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr
          have hbnd := (ProgBounded.straight lbody rfl) (decClockHOLFinite s) scode (by simp)
          have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata (decClockHOLFinite s) lbody
          have hpres_n := evaluate_avoidsLocal_flowing (ofString "n") lbody rfl (decClockHOLFinite s)
          have hno_cont := evaluate_noTopContinue lbody rfl (decClockHOLFinite s)
          have hno_brk := evaluate_noTopBreak lbody rfl (decClockHOLFinite s)
          rcases hr : evaluateHOLFiniteState (decClockHOLFinite s) lbody with ⟨res, post⟩
          rw [hr] at hbnd hmeta hpres_n hno_cont hno_brk
          dsimp only at hbnd hmeta hpres_n hno_cont hno_brk
          obtain ⟨sp, kp, sf⟩ := hbnd
          change s.clock - 1 ≤ post.clock + 0 at sp
          change post.clock ≤ s.clock - 1 at kp
          refine ⟨sp, kp, sf, ?_, fun hbrk => absurd hbrk hno_brk⟩
          intro hflow
          rcases hflow with rfl | hcont
          · have hreassoc : evaluateHOLFiniteState (decClockHOLFinite s) lbody =
                evaluateHOLFiniteState (decClockHOLFinite s)
                  (.seq
                    (.seq
                      (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "o")])
                        (.op .or
                          [.shift .lsl (.loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i")])) (.const 4),
                           .loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i"), .const 1])]))
                      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 2])))
                    (.assign .local (ofString "o") (.op .add [.var .local (ofString "o"), .const 1]))) := by
              simp only [lbody, evaluateHOLFiniteState_seq_line780]
              cases evaluateHOLFiniteState (decClockHOLFinite s)
                (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "o")])
                  (.op .or
                    [.shift .lsl (.loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i")])) (.const 4),
                     .loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i"), .const 1])])) with
              | mk r1 m1 =>
                cases r1 <;> rfl
            rw [hr] at hreassoc
            have hcbrun := hcb.run (decClockHOLFinite s) scode iw hi (by simp)
            rw [evaluateHOLFiniteState_seq_line780] at hreassoc
            rcases h12 : evaluateHOLFiniteState (decClockHOLFinite s)
                (.seq
                  (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "o")])
                    (.op .or
                      [.shift .lsl (.loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i")])) (.const 4),
                       .loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i"), .const 1])]))
                  (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 2]))) with ⟨r12, smid⟩
            rw [h12] at hreassoc hcbrun
            cases r12 with
            | some _ => simp at hreassoc
            | none =>
              dsimp only at hreassoc hcbrun
              have hmid_i : smid.locals.lookup (ofString "i") = some (.val (.word (iw + 2))) := (hcbrun.2.2.2.2 rfl).1
              have hpres_i2 := evaluate_avoidsLocal_flowing (ofString "i")
                (.assign .local (ofString "o") (.op .add [.var .local (ofString "o"), .const 1]))
                rfl smid (by rw [← hreassoc]; exact Or.inl rfl)
              rw [← hreassoc] at hpres_i2
              have hpost_i : post.locals.lookup (ofString "i") = some (.val (.word (iw + 2))) :=
                hpres_i2.trans hmid_i
              have hpost_n : post.locals.lookup (ofString "n") = some (.val (.word nw)) :=
                (hpres_n (Or.inl rfl)).trans hn
              refine ⟨(nw.toNat - (iw + 2).toNat) / 2, by omega, ⟨iw + 2, hpost_i, hpost_n, ?_, rfl⟩, hmeta.1⟩
              intro _
              omega
          · exact absurd hcont hno_cont
        have hr0_le : (nw.toNat - iw0.toNat) / 2 ≤ 2 ^ 63 := by
          have := nw.isLt
          omega
        have hout := rankedWhile_run cond lbody 0 Rank False hexit hstep
          ((nw.toNat - iw0.toNat) / 2) s3 hs3_code
          ⟨iw0, hs3_i, hs3_n, fun _ => hpar0, rfl⟩
          (by change ((nw.toNat - iw0.toNat) / 2) * 1 ≤ s2.clock; omega)
        have hloop_rb : RunBounded s3 (.while cond lbody) (2 ^ 63) :=
          ⟨by change s2.clock ≤ _ + 2 ^ 63; have hsp : s2.clock ≤ _ + ((nw.toNat - iw0.toNat) / 2) * 1 := hout.1; omega,
           hout.2.1, hout.2.2.1⟩
        exact (RunBounded.seq (state := s3) (a := 2 ^ 63) (b := 0) hloop_rb
          (by change 2 ^ 63 + 0 ≤ s2.clock; omega)
          (fun s4 _ hs4_code hs4_clk =>
            (ProgBounded.straight (.return (.var .local (ofString "o"))) rfl) s4 (hs4_code.trans hs3_code) hs4_clk)).weaken (by omega)

theorem funBounded_common_prefix_length :
    FunBounded (ofString "common_prefix_length") (2 ^ 64) := by
  refine funBounded_of_guestAst 251 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_common_prefix_length (2 ^ 64) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_common_prefix_length,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_min (ofString "n") .one _
      (progBounded_varCountedDec_local (ofString "i") (ofString "n") .lower (Or.inr rfl)
        (cost := 0)
        (countedStep_seq_straight _ rfl rfl rfl countedStep_incr)
        rfl
        (ProgBounded.straight _ rfl)))
    (by decide)

private theorem lookup_nibbles_concat :
    originalRuntimeCode.lookup (ofString "nibbles_concat") =
      some ([(ofString "a", .one), (ofString "al", .one), (ofString "b", .one), (ofString "bl", .one)],
        sourceFnBody Guest.Software.guestFn_nibbles_concat, .one) :=
  lookup_of_guestAst_getElem 252 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_nibbles_concat) rfl

theorem runBounded_nibbles_concat_body {F : Type}
    (state : PanSemStateFiniteExact 64 F) (Kal Kbl : BitVec 64)
    (hsmall_al : Kal.toNat + 32 < 2 ^ 64)
    (hsmall_bl : Kbl.toNat + 32 < 2 ^ 64)
    (hcode : state.code = originalRuntimeCode)
    (atAl : state.locals.lookup (ofString "al") = some (.val (.word Kal)))
    (atBl : state.locals.lookup (ofString "bl") = some (.val (.word Kbl)))
    (hbudget : Kal.toNat / 8 + Kbl.toNat / 8 + 18 ≤ state.clock) :
    RunBounded state (sourceFnBody Guest.Software.guestFn_nibbles_concat)
      (Kal.toNat / 8 + Kbl.toNat / 8 + 18) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_nibbles_concat,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  cases hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.op .add [.var .local (ofString "al"), .var .local (ofString "bl")]] with
  | none =>
    unfold RunBounded
    rw [evaluateHOLFiniteState_decCall_args_none state (ofString "out") .one (ofString "alloc") _ _ hargs]
    simp
  | some vs =>
    exact (RunBounded.decCall (state := state) (name := ofString "out") (shape := .one)
      (function := ofString "alloc") (bodyCost := 1)
      (tailCost := Kal.toNat / 8 + Kbl.toNat / 8 + 16) hargs (by omega)
      (fun body locals rs hfound => by
        refine ⟨ProgBounded.bodies_of_fun funBounded_alloc state hcode (by omega) vs body locals rs hfound, ?_⟩
        intro vout post hran hpost_clk
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state locals) body).1
        rw [hran] at hmeta
        let s1 := setVarHOLFinite (ofString "out") vout { post with locals := state.locals }
        have hs1_code : s1.code = originalRuntimeCode := hmeta.trans hcode
        have hs1_al : s1.locals.lookup (ofString "al") = some (.val (.word Kal)) := by
          have hne : ofString "out" ≠ ofString "al" := by decide
          simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, atAl]
        have hs1_bl : s1.locals.lookup (ofString "bl") = some (.val (.word Kbl)) := by
          have hne : ofString "out" ≠ ofString "bl" := by decide
          simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, atBl]
        have hmc1 : RunBounded s1
            (.call (some (none, none)) (ofString "memcpy")
              [.var .local (ofString "out"), .var .local (ofString "a"), .var .local (ofString "al")])
            (Kal.toNat / 8 + 8) := by
          have heq_call : evaluateHOLFiniteState s1
              (.call (some (none, none)) (ofString "memcpy")
                [.var .local (ofString "out"), .var .local (ofString "a"), .var .local (ofString "al")]) =
            evaluateHOLFiniteState s1
              (.call (some (none, none)) (ofString "memcpy")
                [.var .local (ofString "out"), .var .local (ofString "a"), .const Kal]) := by
            have hlist : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
                [.var .local (ofString "out"), .var .local (ofString "a"), .var .local (ofString "al")] =
              evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
                [.var .local (ofString "out"), .var .local (ofString "a"), .const Kal] := by
              rw [evalListHOLFinite_eq_toExact, evalListHOLFinite_eq_toExact]
              simp [evalListHOLExact, evalHOLExact, hs1_al]
            rw [evaluateHOLFiniteState_call, evaluateHOLFiniteState_call, hlist]
          unfold RunBounded
          rw [heq_call]
          exact progBounded_memcpy_const none (.var .local (ofString "out")) (.var .local (ofString "a"))
            Kal hsmall_al s1 hs1_code (by change Kal.toNat / 8 + 8 ≤ post.clock; omega)
        refine (RunBounded.seq (state := s1) (a := Kal.toNat / 8 + 8) (b := Kbl.toNat / 8 + 8) hmc1
          (by change (Kal.toNat / 8 + 8) + (Kbl.toNat / 8 + 8) ≤ post.clock; omega)
          (fun s2 hr2 hs2_code hs2_clk => ?_)).weaken (by omega)
        have hs2_code' : s2.code = originalRuntimeCode := hs2_code.trans hs1_code
        have hs2_bl : s2.locals.lookup (ofString "bl") = some (.val (.word Kbl)) := by
          have hpres := evaluate_avoidsLocal_flowing (ofString "bl")
            (.call (some (none, none)) (ofString "memcpy")
              [.var .local (ofString "out"), .var .local (ofString "a"), .var .local (ofString "al")])
            rfl s1 (by rw [hr2]; exact Or.inl rfl)
          rw [hr2] at hpres
          exact hpres.trans hs1_bl
        have hmc2 : RunBounded s2
            (.call (some (none, none)) (ofString "memcpy")
              [.op .add [.var .local (ofString "out"), .var .local (ofString "al")],
               .var .local (ofString "b"), .var .local (ofString "bl")])
            (Kbl.toNat / 8 + 8) := by
          have heq_call : evaluateHOLFiniteState s2
              (.call (some (none, none)) (ofString "memcpy")
                [.op .add [.var .local (ofString "out"), .var .local (ofString "al")],
                 .var .local (ofString "b"), .var .local (ofString "bl")]) =
            evaluateHOLFiniteState s2
              (.call (some (none, none)) (ofString "memcpy")
                [.op .add [.var .local (ofString "out"), .var .local (ofString "al")],
                 .var .local (ofString "b"), .const Kbl]) := by
            have hlist : evalListHOLFinite s2 (h := fun a => Classical.propDecidable (s2.memaddrs a))
                [.op .add [.var .local (ofString "out"), .var .local (ofString "al")],
                 .var .local (ofString "b"), .var .local (ofString "bl")] =
              evalListHOLFinite s2 (h := fun a => Classical.propDecidable (s2.memaddrs a))
                [.op .add [.var .local (ofString "out"), .var .local (ofString "al")],
                 .var .local (ofString "b"), .const Kbl] := by
              rw [evalListHOLFinite_eq_toExact, evalListHOLFinite_eq_toExact]
              simp [evalListHOLExact, evalHOLExact, hs2_bl]
            rw [evaluateHOLFiniteState_call, evaluateHOLFiniteState_call, hlist]
          unfold RunBounded
          rw [heq_call]
          exact progBounded_memcpy_const none
            (.op .add [.var .local (ofString "out"), .var .local (ofString "al")])
            (.var .local (ofString "b")) Kbl hsmall_bl s2 hs2_code' (by omega)
        exact (RunBounded.seq (state := s2) (a := Kbl.toNat / 8 + 8) (b := 0) hmc2 (by omega)
          (fun s3 _ hs3_code hs3_clk =>
            (ProgBounded.straight (.return (.var .local (ofString "out"))) rfl) s3 (hs3_code.trans hs2_code') hs3_clk)).weaken (by omega))).weaken (by omega)

theorem progBounded_nibbles_concat_decCall_exp (name : MlS) (shape : ShapeHOL)
    (a alExp b blExp : ExpHOL 64) (Kal Kbl : BitVec 64)
    {continuation : ProgHOL 64} {tailCost : Nat}
    (hsmall_al : Kal.toNat + 32 < 2 ^ 64)
    (hsmall_bl : Kbl.toNat + 32 < 2 ^ 64)
    (heval_al : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      evalHOLFinite s (h := fun addr => Classical.propDecidable (s.memaddrs addr)) alExp = some (.val (.word Kal)))
    (heval_bl : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      evalHOLFinite s (h := fun addr => Classical.propDecidable (s.memaddrs addr)) blExp = some (.val (.word Kbl)))
    (hrest : ProgBounded continuation tailCost) :
    ProgBounded (.decCall name shape (ofString "nibbles_concat") [a, alExp, b, blExp] continuation)
      (Kal.toNat / 8 + Kbl.toNat / 8 + 19 + tailCost) := by
  intro F state hcode hbudget
  cases hargs : evalListHOLFinite state (h := fun addr => Classical.propDecidable (state.memaddrs addr))
      [a, alExp, b, blExp] with
  | none =>
    rw [evaluateHOLFiniteState_decCall_args_none state name shape (ofString "nibbles_concat") _ continuation hargs]
    simp
  | some vs =>
    have hal := heval_al state
    have hbl := heval_bl state
    obtain ⟨v1, v3, rfl⟩ : ∃ v1 v3, vs = [v1, .val (.word Kal), v3, .val (.word Kbl)] := by
      rw [evalListHOLFinite_eq_toExact] at hargs
      rw [evalHOLFinite_eq_toExact] at hal hbl
      simp only [evalListHOLExact] at hargs
      rw [hal, hbl] at hargs
      rcases h1 : @evalHOLExact 64 F _ state.toExact (fun addr => Classical.propDecidable (state.memaddrs addr)) a with _ | v1
      · rw [h1] at hargs; cases hargs
      · rw [h1] at hargs
        rcases h3 : @evalHOLExact 64 F _ state.toExact (fun addr => Classical.propDecidable (state.memaddrs addr)) b with _ | v3
        · rw [h3] at hargs; cases hargs
        · rw [h3] at hargs; cases hargs; exact ⟨v1, v3, rfl⟩
    have h := RunBounded.decCall (name := name) (shape := shape) (continuation := continuation)
      (bodyCost := Kal.toNat / 8 + Kbl.toNat / 8 + 18) (tailCost := tailCost) hargs (by omega)
      (fun body locals rs hfound => by
        rw [hcode] at hfound
        have hbody := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup
          (ofString "nibbles_concat") _ (sourceFnBody Guest.Software.guestFn_nibbles_concat) body
          .one rs [v1, .val (.word Kal), v3, .val (.word Kbl)] locals lookup_nibbles_concat hfound
        subst hbody
        have hparams : locals.lookup (ofString "al") = some (.val (.word Kal)) ∧
            locals.lookup (ofString "bl") = some (.val (.word Kbl)) := by
          cases v1 with
          | rStruct _ =>
            unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
            split at hfound
            · cases hfound
            · rename_i _ _ _ raw
              simp [lookupCodeHOLExact, lookup_nibbles_concat, shapeOfHOLExact, shapeEqHOL] at raw
          | nStruct _ _ =>
            unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
            split at hfound
            · cases hfound
            · rename_i _ _ _ raw
              simp [lookupCodeHOLExact, lookup_nibbles_concat, shapeOfHOLExact, shapeEqHOL] at raw
          | val wl1 =>
            cases wl1 with
            | word w1 =>
              cases v3 with
              | rStruct _ =>
                unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
                split at hfound
                · cases hfound
                · rename_i _ _ _ raw
                  simp [lookupCodeHOLExact, lookup_nibbles_concat, shapeOfHOLExact, shapeEqHOL] at raw
              | nStruct _ _ =>
                unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
                split at hfound
                · cases hfound
                · rename_i _ _ _ raw
                  simp [lookupCodeHOLExact, lookup_nibbles_concat, shapeOfHOLExact, shapeEqHOL] at raw
              | val wl3 =>
                cases wl3 with
                | word w3 =>
                  have hd12 : ofString "a" ≠ ofString "al" := by decide
                  have hd13 : ofString "a" ≠ ofString "b" := by decide
                  have hd14 : ofString "a" ≠ ofString "bl" := by decide
                  have hd23 : ofString "al" ≠ ofString "b" := by decide
                  have hd24 : ofString "al" ≠ ofString "bl" := by decide
                  have hd34 : ofString "b" ≠ ofString "bl" := by decide
                  have hraw : lookupCodeHOLExact originalRuntimeCode.lookup (ofString "nibbles_concat")
                      [.val (.word w1), .val (.word Kal), .val (.word w3), .val (.word Kbl)] =
                      some (sourceFnBody Guest.Software.guestFn_nibbles_concat,
                        (fun key => if key = ofString "bl" then some (.val (.word Kbl))
                          else if key = ofString "b" then some (.val (.word w3))
                          else if key = ofString "al" then some (.val (.word Kal))
                          else if key = ofString "a" then some (.val (.word w1)) else none),
                        .one) := by
                    simp [lookupCodeHOLExact, lookup_nibbles_concat, shapeOfHOLExact, shapeEqHOL,
                      hd12, hd13, hd14, hd23, hd24, hd34]
                  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
                  split at hfound
                  · rename_i missing
                    rw [hraw] at missing
                    cases missing
                  · rename_i _ exactLocals _ found
                    have equal := Option.some.inj (found.symm.trans hraw)
                    obtain ⟨_, rest⟩ := Prod.mk.inj equal
                    obtain ⟨rfl, _⟩ := Prod.mk.inj rest
                    have heq := Option.some.inj hfound
                    obtain ⟨_, hloc2⟩ := Prod.mk.inj heq
                    obtain ⟨rfl, _⟩ := Prod.mk.inj hloc2
                    have hne1 : ofString "al" ≠ ofString "bl" := by decide
                    have hne2 : ofString "al" ≠ ofString "b" := by decide
                    exact ⟨by simp [hne1, hne2], rfl⟩
        have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state locals)
          (sourceFnBody Guest.Software.guestFn_nibbles_concat)
        refine ⟨runBounded_nibbles_concat_body (callEntryStateHOLFinite state locals) Kal Kbl
          hsmall_al hsmall_bl hcode hparams.1 hparams.2
          (by change Kal.toNat / 8 + Kbl.toNat / 8 + 18 ≤ state.clock - 1; omega), ?_⟩
        intro value post hran hpost_clk
        rw [hran] at hmeta
        exact hrest _ (hmeta.1.trans hcode) hpost_clk)
    exact h.weaken (by omega)

private def capDoublingAux : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | fuel + 1, target, cap =>
      if cap = 0 ∨ target ≤ cap then 0
      else capDoublingAux fuel target (cap * 2) + 1

private def capDoublingRank (target cap : Nat) : Nat :=
  capDoublingAux 64 target cap

private theorem capDoublingAux_le : ∀ (fuel target cap : Nat),
    capDoublingAux fuel target cap ≤ fuel
  | 0, _, _ => Nat.zero_le _
  | fuel + 1, target, cap => by
      unfold capDoublingAux
      split
      · exact Nat.zero_le _
      · exact Nat.succ_le_succ (capDoublingAux_le fuel target (cap * 2))

private theorem capDoublingRank_le_64 (target cap : Nat) : capDoublingRank target cap ≤ 64 :=
  capDoublingAux_le 64 target cap

private theorem capDoublingRank_zero_imp {target cap : Nat} (hpos : 0 < cap)
    (h0 : capDoublingRank target cap = 0) : target ≤ cap := by
  unfold capDoublingRank capDoublingAux at h0
  split at h0
  · rename_i h
    rcases h with rfl | hle
    · omega
    · exact hle
  · omega

private theorem capDoublingAux_mono_fuel : ∀ (fuel target cap : Nat),
    0 < cap → target ≤ cap * 2 ^ fuel →
    capDoublingAux (fuel + 1) target cap = capDoublingAux fuel target cap
  | 0, target, cap, hpos, hle => by
      have hle' : target ≤ cap := by simpa using hle
      simp [capDoublingAux, hle']
  | fuel + 1, target, cap, hpos, hle => by
      simp only [capDoublingAux]
      split
      · rfl
      · congr 1
        apply capDoublingAux_mono_fuel fuel target (cap * 2) (by omega)
        have heq : (cap * 2) * 2 ^ fuel = cap * 2 ^ (fuel + 1) := by
          rw [Nat.pow_succ, Nat.mul_comm (2 ^ fuel) 2, ← Nat.mul_assoc]
        rw [heq]
        exact hle

private theorem capDoublingRank_step {target cap k : Nat}
    (htarget : target ≤ 2 ^ 63) (hpos : 0 < cap) (hlt : cap < target)
    (hr : capDoublingRank target cap = k + 1) :
    capDoublingRank target (cap * 2) ≤ k := by
  unfold capDoublingRank at hr ⊢
  rw [capDoublingAux, if_neg (by omega)] at hr
  have hk : capDoublingAux 63 target (cap * 2) = k := by omega
  have hle_pow : target ≤ (cap * 2) * 2 ^ 63 := by
    have hc2 : 2 ≤ cap * 2 := by omega
    calc target ≤ 2 ^ 63 := htarget
      _ ≤ 2 * 2 ^ 63 := by omega
      _ ≤ (cap * 2) * 2 ^ 63 := Nat.mul_le_mul_right _ hc2
  rw [capDoublingAux_mono_fuel 63 target (cap * 2) (by omega) hle_pow, hk]

private theorem lookup_nodedb_build :
    originalRuntimeCode.lookup (ofString "nodedb_build") =
      some ([(ofString "slice_arr", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_nodedb_build, .one) :=
  lookup_of_guestAst_getElem 253 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_nodedb_build) rfl

private theorem runBounded_cap_doubling_loop {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (Kn : BitVec 64)
    (hsmall : Kn.toNat < 2 ^ 62)
    (hs0_code : s0.code = originalRuntimeCode)
    (hs0_cap : s0.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 4))))
    (hs0_n : s0.locals.lookup (ofString "n") = some (.val (.word Kn)))
    (hbudget : 64 ≤ s0.clock) :
    RunBounded s0
      (.while
        (.cmp .lower (.var .local (ofString "cap"))
          (.op .add [.panop .mul [.const (BitVec.ofNat 64 2), .var .local (ofString "n")],
            .const (BitVec.ofNat 64 2)]))
        (.assign .local (ofString "cap")
          (.panop .mul [.var .local (ofString "cap"), .const (BitVec.ofNat 64 2)])))
      64 := by
  let target : Nat := 2 * Kn.toNat + 2
  have htarget_le : target ≤ 2 ^ 63 := by omega
  have htarget_bv : (BitVec.ofNat 64 2 * Kn + BitVec.ofNat 64 2).toNat = target := by
    have hmul : (BitVec.ofNat 64 2 * Kn).toNat = 2 * Kn.toNat := by
      rw [BitVec.toNat_mul, show (BitVec.ofNat 64 2).toNat = 2 from rfl,
        Nat.mod_eq_of_lt (by change 2 * Kn.toNat < 2 ^ 64; omega)]
    rw [BitVec.toNat_add, hmul, show (BitVec.ofNat 64 2).toNat = 2 from rfl,
      Nat.mod_eq_of_lt (by change 2 * Kn.toNat + 2 < 2 ^ 64; omega)]
  let cond1 : ExpHOL 64 :=
    .cmp .lower (.var .local (ofString "cap"))
      (.op .add [.panop .mul [.const (BitVec.ofNat 64 2), .var .local (ofString "n")],
        .const (BitVec.ofNat 64 2)])
  let body1 : ProgHOL 64 :=
    .assign .local (ofString "cap")
      (.panop .mul [.var .local (ofString "cap"), .const (BitVec.ofNat 64 2)])
  let Rank1 : ∀ {G : Type}, PanSemStateFiniteExact 64 G → Nat → Prop :=
    fun s r => ∃ cw : BitVec 64,
      s.locals.lookup (ofString "cap") = some (.val (.word cw)) ∧
      s.locals.lookup (ofString "n") = some (.val (.word Kn)) ∧
      0 < cw.toNat ∧ capDoublingRank target cw.toNat = r
  have hexit1 : ∀ {G : Type} (s : PanSemStateFiniteExact 64 G), Rank1 s 0 → ∀ w : BitVec 64,
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) cond1 = some (.val (.word w)) → w = 0 := by
    intro G s ⟨cw, hcw, hnw, hpos, hr0⟩ w heval
    have hge := capDoublingRank_zero_imp hpos hr0
    rw [evalHOLFinite_eq_toExact] at heval
    simp only [cond1, evalHOLExact, evalListHOLExact, hcw, hnw, panOpHOL, wordOpHOL, wordOp,
      valueIsWord, valueWord, Compiler.Encoders.Asm.wordCmpHOL] at heval
    have hnotlt : ¬(cw < BitVec.ofNat 64 2 * Kn + BitVec.ofNat 64 2) := by
      rw [BitVec.lt_def, htarget_bv]
      omega
    have hm : AndOp.and 2#64 18446744073709551615#64 = 2#64 := rfl
    simp only [hm] at heval
    rw [if_neg hnotlt] at heval
    exact (Option.some.inj heval |> ValueHOL.val.inj |> HolWordLab.word.inj).symm
  have hstep1 : ∀ {G : Type} (s : PanSemStateFiniteExact 64 G) (k : Nat) (w : BitVec 64),
      s.code = originalRuntimeCode →
      Rank1 s (k + 1) →
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) cond1 = some (.val (.word w)) →
      w ≠ 0 → 0 + 1 ≤ s.clock →
      s.clock - 1 ≤ (evaluateHOLFiniteState (decClockHOLFinite s) body1).2.clock + 0 ∧
        (evaluateHOLFiniteState (decClockHOLFinite s) body1).2.clock ≤ s.clock - 1 ∧
        (evaluateHOLFiniteState (decClockHOLFinite s) body1).1 ≠ some .timeOut ∧
        ((evaluateHOLFiniteState (decClockHOLFinite s) body1).1 = none ∨
            (evaluateHOLFiniteState (decClockHOLFinite s) body1).1 = some .continue →
          ∃ m, m ≤ k ∧ Rank1 (evaluateHOLFiniteState (decClockHOLFinite s) body1).2 m ∧
            (evaluateHOLFiniteState (decClockHOLFinite s) body1).2.code = s.code) ∧
        ((evaluateHOLFiniteState (decClockHOLFinite s) body1).1 = some .break → False ∧
          ∃ m, Rank1 (evaluateHOLFiniteState (decClockHOLFinite s) body1).2 m ∧
            (evaluateHOLFiniteState (decClockHOLFinite s) body1).2.code = s.code) := by
    intro G s k w _ ⟨cw, hcw, hnw, hpos, hrk⟩ heval hwnz _
    have hlt_cw : cw.toNat < target := by
      rw [evalHOLFinite_eq_toExact] at heval
      simp only [cond1, evalHOLExact, evalListHOLExact, hcw, hnw, panOpHOL, wordOpHOL, wordOp,
        valueIsWord, valueWord, Compiler.Encoders.Asm.wordCmpHOL] at heval
      have hm : AndOp.and 2#64 18446744073709551615#64 = 2#64 := rfl
      simp only [hm] at heval
      by_cases hlt : cw < 2#64 * Kn + 2#64
      · rw [BitVec.lt_def, htarget_bv] at hlt
        exact hlt
      · rw [if_neg hlt] at heval
        have := Option.some.inj heval |> ValueHOL.val.inj |> HolWordLab.word.inj
        exact absurd this.symm hwnz
    have hcw2_nat : (cw * BitVec.ofNat 64 2).toNat = cw.toNat * 2 := by
      rw [BitVec.toNat_mul, show (BitVec.ofNat 64 2).toNat = 2 from rfl,
        Nat.mod_eq_of_lt (by change cw.toNat * 2 < 2 ^ 64; omega)]
    let ds := decClockHOLFinite s
    have hds_cw : ds.locals.lookup (ofString "cap") = some (.val (.word cw)) := hcw
    have heval_body : evaluateHOLFiniteState ds body1 =
        (none, setVarHOLFinite (ofString "cap") (.val (.word (cw * BitVec.ofNat 64 2))) ds) := by
      simp [body1, evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hds_cw,
        panOpHOL, valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact,
        setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
    rw [heval_body]
    refine ⟨by simp [ds, decClockHOLFinite, setVarHOLFinite],
      by simp [ds, decClockHOLFinite, setVarHOLFinite], by simp, ?_, by simp⟩
    intro _
    refine ⟨capDoublingRank target (cw.toNat * 2),
      capDoublingRank_step htarget_le hpos hlt_cw hrk, ?_, rfl⟩
    refine ⟨cw * BitVec.ofNat 64 2, ?_, ?_, by rw [hcw2_nat]; omega, by rw [hcw2_nat]⟩
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    · have hne : ofString "cap" ≠ ofString "n" := by decide
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, ds, decClockHOLFinite, hnw]
  let r0 := capDoublingRank target 4
  have hr0_le : r0 ≤ 64 := capDoublingRank_le_64 target 4
  have hraw := rankedWhile_run cond1 body1 0 Rank1 False hexit1 hstep1 r0
    s0 hs0_code ⟨BitVec.ofNat 64 4, hs0_cap, hs0_n, by decide, rfl⟩
    (by omega)
  exact ⟨by have := hraw.1; omega, hraw.2.1, hraw.2.2.1⟩

theorem runBounded_nodedb_build_body {F : Type}
    (K_hnew K_keccak K_hset : Nat)
    (h_hnew : FunBounded (ofString "htab_new") K_hnew)
    (h_keccak : FunBounded (ofString "keccak256") K_keccak)
    (h_hset : FunBounded (ofString "htab_set") K_hset)
    (state : PanSemStateFiniteExact 64 F) (Kn : BitVec 64)
    (hsmall : Kn.toNat < 2 ^ 62)
    (hcode : state.code = originalRuntimeCode)
    (atN : state.locals.lookup (ofString "n") = some (.val (.word Kn)))
    (hbudget : 65 + K_hnew + 1 + Kn.toNat * (K_keccak + K_hset + 3) ≤ state.clock) :
    RunBounded state (sourceFnBody Guest.Software.guestFn_nodedb_build)
      (65 + K_hnew + 1 + Kn.toNat * (K_keccak + K_hset + 3)) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_nodedb_build,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply RunBounded.decConst
  let s0 := setVarHOLFinite (ofString "cap") (.val (.word (BitVec.ofNat 64 4))) state
  change RunBounded s0 _ (65 + K_hnew + 1 + Kn.toNat * (K_keccak + K_hset + 3))
  have hs0_code : s0.code = originalRuntimeCode := hcode
  have hs0_cap : s0.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 4))) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs0_n : s0.locals.lookup (ofString "n") = some (.val (.word Kn)) := by
    have hne : ofString "cap" ≠ ofString "n" := by decide
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, atN]
  have hloop1 := runBounded_cap_doubling_loop s0 Kn hsmall hs0_code hs0_cap hs0_n
    (by change 64 ≤ state.clock; omega)
  refine (RunBounded.seq (state := s0) (a := 64)
    (b := 1 + K_hnew + 1 + Kn.toNat * (K_keccak + K_hset + 3)) hloop1
    (by change 64 + (1 + K_hnew + 1 + Kn.toNat * (K_keccak + K_hset + 3)) ≤ state.clock; omega)
    (fun s1 hr1 hs1_code hs1_clk => ?_)).weaken (by omega)
  have hs1_code' : s1.code = originalRuntimeCode := hs1_code.trans hs0_code
  have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word Kn)) := by
    have hpres := evaluate_avoidsLocal_flowing (ofString "n") _ rfl s0
      (by rw [hr1]; exact Or.inl rfl)
    rw [hr1] at hpres
    exact hpres.trans hs0_n
  cases hargs : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
      [.const (BitVec.ofNat 64 32), .var .local (ofString "cap")] with
  | none =>
    unfold RunBounded
    rw [evaluateHOLFiniteState_decCall_args_none s1 (ofString "t") .one (ofString "htab_new") _ _ hargs]
    simp
  | some vs =>
    refine (RunBounded.decCall (state := s1) (name := ofString "t") (shape := .one)
      (function := ofString "htab_new") (bodyCost := K_hnew)
      (tailCost := Kn.toNat * (K_keccak + K_hset + 3)) hargs (by omega)
      (fun body locals rs hfound => by
        refine ⟨ProgBounded.bodies_of_fun h_hnew s1 hs1_code' (by omega) vs body locals rs hfound, ?_⟩
        intro vt post hran hpost_clk
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s1 locals) body).1
        rw [hran] at hmeta
        let s2 := setVarHOLFinite (ofString "t") vt { post with locals := s1.locals }
        have hs2_code : s2.code = originalRuntimeCode := hmeta.trans hs1_code'
        have hs2_n : s2.locals.lookup (ofString "n") = some (.val (.word Kn)) := by
          have hne : ofString "t" ≠ ofString "n" := by decide
          simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hs1_n]
        apply RunBounded.decConst
        let s3 := setVarHOLFinite (ofString "i") (.val (.word 0)) s2
        change RunBounded s3 _ (Kn.toNat * (K_keccak + K_hset + 3))
        have hs3_code : s3.code = originalRuntimeCode := hs2_code
        have hs3_i : s3.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 0))) := by
          simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hs3_n : s3.locals.lookup (ofString "n") = some (.val (.word Kn)) := by
          have hne : ofString "i" ≠ ofString "n" := by decide
          simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hs2_n]
        let p_kc : ProgHOL 64 :=
          .call (some (none, none)) (ofString "keccak256")
            [(ExpHOL.op .add [.var .local (ofString "slice_arr"),
                .panop .mul [.var .local (ofString "i"), .const (BitVec.ofNat 64 16)]]).load .one,
             (ExpHOL.op .add [.var .local (ofString "slice_arr"),
                .panop .mul [.var .local (ofString "i"), .const (BitVec.ofNat 64 16)],
                .const (BitVec.ofNat 64 8)]).load .one,
             .var .global (ofString "mpt_hash_scratch")]
        let p_hs : ProgHOL 64 :=
          .call (some (none, none)) (ofString "htab_set")
            [.var .local (ofString "t"),
             .var .global (ofString "mpt_hash_scratch"),
             .op .add [.var .local (ofString "slice_arr"),
               .panop .mul [.var .local (ofString "i"), .const (BitVec.ofNat 64 16)]]]
        have hcounted := CountedBody.seq p_kc
          (ProgBounded.call h_keccak none _) rfl rfl
          (CountedBody.seq p_hs (ProgBounded.call h_hset none _) rfl rfl
            (CountedBody.incr (counter := ofString "i") (step := BitVec.ofNat 64 1)))
        have hloop2 : RunBounded s3
            (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n")))
              (.seq p_kc (.seq p_hs (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)])))))
            (Kn.toNat * (K_keccak + K_hset + 3)) := by
          have hsub : Kn.toNat - (BitVec.ofNat 64 0).toNat = Kn.toNat := by
            change Kn.toNat - 0 = Kn.toNat
            omega
          have hstep_cost : (K_keccak + 1 + (K_hset + 1 + 0)) + 1 = K_keccak + K_hset + 3 := by omega
          have hbud_loop : Kn.toNat * ((K_keccak + 1 + (K_hset + 1 + 0)) + 1) ≤ s3.clock := by
            rw [hstep_cost]
            change Kn.toNat * (K_keccak + K_hset + 3) ≤ post.clock
            omega
          have hraw := variableCountedWhile_run (ofString "i") (ofString "n") .lower
            (Or.inr rfl) Kn (fun h => by cases h) hcounted rfl Kn.toNat s3 hs3_code (BitVec.ofNat 64 0)
            hs3_i hs3_n (Nat.zero_le _) hsub hbud_loop
          exact ⟨by rw [hstep_cost] at hraw; exact hraw.1, hraw.2.1, hraw.2.2⟩
        exact (RunBounded.seq (state := s3)
          (a := Kn.toNat * (K_keccak + K_hset + 3)) (b := 0) hloop2
          (by change Kn.toNat * (K_keccak + K_hset + 3) + 0 ≤ post.clock; omega)
          (fun s4 _ hs4_code hs4_clk =>
            (ProgBounded.straight (.return (.var .local (ofString "t"))) rfl) s4
              (hs4_code.trans hs3_code) hs4_clk)).weaken (by omega))).weaken (by omega)

theorem progBounded_nodedb_build_decCall_exp
    (K_hnew K_keccak K_hset : Nat)
    (h_hnew : FunBounded (ofString "htab_new") K_hnew)
    (h_keccak : FunBounded (ofString "keccak256") K_keccak)
    (h_hset : FunBounded (ofString "htab_set") K_hset)
    (name : MlS) (shape : ShapeHOL) (sliceArr nExp : ExpHOL 64) (Kn : BitVec 64)
    {continuation : ProgHOL 64} {tailCost : Nat}
    (hsmall : Kn.toNat < 2 ^ 62)
    (heval_n : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      evalHOLFinite s (h := fun addr => Classical.propDecidable (s.memaddrs addr)) nExp = some (.val (.word Kn)))
    (hrest : ProgBounded continuation tailCost) :
    ProgBounded (.decCall name shape (ofString "nodedb_build") [sliceArr, nExp] continuation)
      (67 + K_hnew + Kn.toNat * (K_keccak + K_hset + 3) + tailCost) := by
  intro F state hcode hbudget
  cases hargs : evalListHOLFinite state (h := fun addr => Classical.propDecidable (state.memaddrs addr))
      [sliceArr, nExp] with
  | none =>
    rw [evaluateHOLFiniteState_decCall_args_none state name shape (ofString "nodedb_build") _ continuation hargs]
    simp
  | some vs =>
    have hn := heval_n state
    obtain ⟨v1, rfl⟩ : ∃ v1, vs = [v1, .val (.word Kn)] := by
      rw [evalListHOLFinite_eq_toExact] at hargs
      rw [evalHOLFinite_eq_toExact] at hn
      simp only [evalListHOLExact] at hargs
      rw [hn] at hargs
      rcases h1 : @evalHOLExact 64 F _ state.toExact (fun addr => Classical.propDecidable (state.memaddrs addr)) sliceArr with _ | v1
      · rw [h1] at hargs; cases hargs
      · rw [h1] at hargs; cases hargs; exact ⟨v1, rfl⟩
    have h := RunBounded.decCall (name := name) (shape := shape) (continuation := continuation)
      (bodyCost := 65 + K_hnew + 1 + Kn.toNat * (K_keccak + K_hset + 3)) (tailCost := tailCost) hargs (by omega)
      (fun body locals rs hfound => by
        rw [hcode] at hfound
        have hbody := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup
          (ofString "nodedb_build") _ (sourceFnBody Guest.Software.guestFn_nodedb_build) body
          .one rs [v1, .val (.word Kn)] locals lookup_nodedb_build hfound
        subst hbody
        have hparam : locals.lookup (ofString "n") = some (.val (.word Kn)) := by
          cases v1 with
          | rStruct _ =>
            unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
            split at hfound
            · cases hfound
            · rename_i _ _ _ raw
              simp [lookupCodeHOLExact, lookup_nodedb_build, shapeOfHOLExact, shapeEqHOL] at raw
          | nStruct _ _ =>
            unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
            split at hfound
            · cases hfound
            · rename_i _ _ _ raw
              simp [lookupCodeHOLExact, lookup_nodedb_build, shapeOfHOLExact, shapeEqHOL] at raw
          | val wl =>
            cases wl with
            | word w1 =>
              have hlk := pan_two_word_lookup originalRuntimeCode.lookup
                (ofString "nodedb_build") (ofString "slice_arr") (ofString "n")
                (sourceFnBody Guest.Software.guestFn_nodedb_build) w1 Kn (by decide) lookup_nodedb_build
              have heq := Option.some.inj (hfound.symm.trans hlk)
              obtain ⟨_, hloc⟩ := Prod.mk.inj heq
              obtain ⟨rfl, _⟩ := Prod.mk.inj hloc
              simp [HolFiniteMapExact.lookup_update, FUPDATE]
        have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state locals)
          (sourceFnBody Guest.Software.guestFn_nodedb_build)
        refine ⟨runBounded_nodedb_build_body K_hnew K_keccak K_hset h_hnew h_keccak h_hset
          (callEntryStateHOLFinite state locals) Kn hsmall hcode hparam
          (by change 65 + K_hnew + 1 + Kn.toNat * (K_keccak + K_hset + 3) ≤ state.clock - 1; omega), ?_⟩
        intro value post hran hpost_clk
        rw [hran] at hmeta
        exact hrest _ (hmeta.1.trans hcode) hpost_clk)
    exact h.weaken (by omega)

theorem funBounded_nodedb_lookup (K_get : Nat)
    (h_get : FunBounded (ofString "htab_get") K_get) :
    FunBounded (ofString "nodedb_lookup") (K_get + 1) := by
  refine funBounded_of_guestAst 254 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_nodedb_lookup (K_get + 1) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_nodedb_lookup,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall h_get _ _ _ (ProgBounded.straight _ rfl)) (by omega)

theorem funBounded_node_new_hashed : FunBounded (ofString "node_new_hashed") 2 := by
  refine funBounded_of_guestAst 255 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_node_new_hashed 2 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_node_new_hashed,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_alloc _ _ _ (ProgBounded.straight _ rfl)) (by decide)

theorem funBounded_node_new_leaf : FunBounded (ofString "node_new_leaf") 2 := by
  refine funBounded_of_guestAst 256 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_node_new_leaf 2 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_node_new_leaf,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_alloc _ _ _ (ProgBounded.straight _ rfl)) (by decide)

theorem funBounded_node_new_ext : FunBounded (ofString "node_new_ext") 2 := by
  refine funBounded_of_guestAst 257 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_node_new_ext 2 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_node_new_ext,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_alloc _ _ _ (ProgBounded.straight _ rfl)) (by decide)

theorem funBounded_node_new_branch : FunBounded (ofString "node_new_branch") 32 := by
  refine funBounded_of_guestAst 258 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_node_new_branch 32 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_node_new_branch,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_alloc _ _ _
      (ProgBounded.seq
        (progBounded_memzero_const none (.var .local (ofString "nd")) (BitVec.ofNat 64 176) (by decide))
        (ProgBounded.straight _ rfl)))
    (by decide)

theorem funBounded_node_invalidate : FunBounded (ofString "node_invalidate") 0 := by
  refine funBounded_of_guestAst 259 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_node_invalidate 0 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_node_invalidate,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.straight
    (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 8)]) (.const (BitVec.ofNat 64 0)))
    (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 16)]) (.const (BitVec.ofNat 64 0)))
    (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 24)]) (.const (BitVec.ofNat 64 0)))
          (.return (.const (BitVec.ofNat 64 0)))))) rfl

theorem funBounded_resolve_step (K_lc K_get : Nat)
    (h_lc : FunBounded (ofString "rlp_list_count") K_lc)
    (h_get : FunBounded (ofString "htab_get") K_get) :
    FunBounded (ofString "_resolve_step") (2 ^ 64 + K_lc + K_get + 14) := by
  refine funBounded_of_guestAst 260 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn__resolve_step (2 ^ 64 + K_lc + K_get + 14) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn__resolve_step,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.dec _ _ _
      (ProgBounded.dec _ _ _
        (ProgBounded.seq
          (ProgBounded.handledCall (funBounded_rlp_item K_lc h_lc) _ _ _ _
            (ProgBounded.call funBounded_mpt_fail none _))
          (ProgBounded.seq
            (ProgBounded.iteMax _
              (ProgBounded.seq
                (ProgBounded.iteMax _ (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl))
                (ProgBounded.seq
                  (ProgBounded.iteMax _ (ProgBounded.call funBounded_mpt_fail none _) (ProgBounded.straight _ rfl))
                  (ProgBounded.decCall (funBounded_nodedb_lookup K_get h_get) _ _ _
                    (ProgBounded.seq
                      (ProgBounded.iteMax _
                        (ProgBounded.decCall funBounded_node_new_hashed _ _ _ (ProgBounded.straight _ rfl))
                        (ProgBounded.straight _ rfl))
                      (ProgBounded.straight _ rfl)))))
              (ProgBounded.straight _ rfl))
            (ProgBounded.straight _ rfl)))))
    (by omega)

theorem funBounded_decode_step (K_lc K_ctn : Nat)
    (h_lc : FunBounded (ofString "rlp_list_count") K_lc)
    (h_ctn : FunBounded (ofString "compact_to_nibbles") K_ctn) :
    FunBounded (ofString "_decode_step") (2 ^ 128 + 5 * 2 ^ 64 + 4 * K_lc + K_ctn + 68) := by
  refine funBounded_of_guestAst 261 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn__decode_step (2 ^ 128 + 5 * 2 ^ 64 + 4 * K_lc + K_ctn + 68) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn__decode_step,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.dec _ _ _
      (ProgBounded.dec _ _ _
        (ProgBounded.seq
          (ProgBounded.handledCall (funBounded_rlp_decode_fully K_lc h_lc) _ _ _ _
            (ProgBounded.call funBounded_mpt_fail none _))
          (ProgBounded.seq
            (ProgBounded.iteMax _
              (ProgBounded.seq
                (ProgBounded.iteMax _ (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl))
                (ProgBounded.call funBounded_mpt_fail none _))
              (ProgBounded.straight _ rfl))
            (ProgBounded.decCall (funBounded_rlp_list_to_slices K_lc h_lc) _ _ _
              (ProgBounded.dec _ _ _
                (ProgBounded.seq
                  (ProgBounded.iteMax _
                    (ProgBounded.decCall (funBounded_rlp_item K_lc h_lc) _ _ _
                      (ProgBounded.seq
                        (ProgBounded.iteMax _ (ProgBounded.call funBounded_mpt_fail none _) (ProgBounded.straight _ rfl))
                        (ProgBounded.decCall h_ctn _ _ _
                          (ProgBounded.seq
                            (ProgBounded.iteMax _
                              (ProgBounded.decCall (funBounded_rlp_item K_lc h_lc) _ _ _
                                (ProgBounded.seq
                                  (ProgBounded.iteMax _ (ProgBounded.call funBounded_mpt_fail none _) (ProgBounded.straight _ rfl))
                                  (ProgBounded.decCall funBounded_node_new_leaf _ _ _ (ProgBounded.straight _ rfl))))
                              (ProgBounded.straight _ rfl))
                            (ProgBounded.seq
                              (ProgBounded.iteMax _ (ProgBounded.call funBounded_mpt_fail none _) (ProgBounded.straight _ rfl))
                              (ProgBounded.decCall funBounded_scratch_alloc _ _ _ (ProgBounded.straight _ rfl)))))))
                    (ProgBounded.straight _ rfl))
                  (ProgBounded.seq
                    (ProgBounded.iteMax _ (ProgBounded.call funBounded_mpt_fail none _) (ProgBounded.straight _ rfl))
                    (ProgBounded.decCall funBounded_node_new_branch _ _ _
                      (ProgBounded.decCall funBounded_scratch_alloc _ _ _ (ProgBounded.straight _ rfl)))))))))))
    (by omega)

def decodeWitnessNodeBodyLoopStep : ProgHOL 64 :=
  match sourceFnBody Guest.Software.guestFn__decode_witness_node_body with
  | .dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _
      (.seq (.while _ step) _))))))) => step
  | p => p

theorem progBounded_decode_witness_node_body_step (K_lc K_ctn K_get : Nat)
    (h_lc : FunBounded (ofString "rlp_list_count") K_lc)
    (h_ctn : FunBounded (ofString "compact_to_nibbles") K_ctn)
    (h_get : FunBounded (ofString "htab_get") K_get) :
    ProgBounded decodeWitnessNodeBodyLoopStep (2 ^ 128 + 5 * 2 ^ 64 + 4 * K_lc + K_ctn + K_get + 69) := by
  dsimp only [decodeWitnessNodeBodyLoopStep, sourceFnBody, sourceFunctionEntry,
    Guest.Software.guestFn__decode_witness_node_body,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.iteMax _
      (ProgBounded.decCall (funBounded_decode_step K_lc K_ctn h_lc h_ctn) _ _ _ (ProgBounded.straight _ rfl))
      (ProgBounded.iteMax _
        (ProgBounded.dec _ _ _
          (ProgBounded.decCall (funBounded_resolve_step K_lc K_get h_lc h_get) _ _ _ (ProgBounded.straight _ rfl)))
        (ProgBounded.iteMax _
          (ProgBounded.straight _ rfl)
          (ProgBounded.dec _ _ _
            (ProgBounded.seq
              (ProgBounded.straight _ rfl)
              (ProgBounded.iteMax _
                (ProgBounded.seq
                  (ProgBounded.iteMax _ (ProgBounded.call funBounded_mpt_fail none _) (ProgBounded.straight _ rfl))
                  (ProgBounded.dec _ _ _
                    (ProgBounded.seq
                      (ProgBounded.iteMax _ (ProgBounded.call funBounded_mpt_fail none _) (ProgBounded.straight _ rfl))
                      (ProgBounded.decCall funBounded_node_new_ext _ _ _ (ProgBounded.straight _ rfl)))))
                (ProgBounded.dec _ _ _
                  (ProgBounded.dec _ _ _
                    (ProgBounded.seq (ProgBounded.straight _ rfl)
                    (ProgBounded.seq (ProgBounded.straight _ rfl)
                    (ProgBounded.seq (ProgBounded.straight _ rfl)
                      (ProgBounded.iteMax _
                        (ProgBounded.straight _ rfl)
                        (ProgBounded.dec _ _ _
                          (ProgBounded.decCall (funBounded_rlp_item K_lc h_lc) _ _ _
                            (ProgBounded.dec _ _ _
                              (ProgBounded.seq
                                (ProgBounded.straight _ rfl)
                                (ProgBounded.seq
                                  (ProgBounded.iteMax _ (ProgBounded.call funBounded_mpt_fail none _) (ProgBounded.straight _ rfl))
                                  (ProgBounded.straight _ rfl))))))))))))))))))
    (by omega)

theorem funBounded_decode_witness_node_mpt (K_body : Nat)
    (h_body : FunBounded (ofString "_decode_witness_node_body") K_body) :
    FunBounded (ofString "_decode_witness_node_mpt") (K_body + 2) := by
  refine funBounded_of_guestAst 263 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn__decode_witness_node_mpt (K_body + 2) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn__decode_witness_node_mpt,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.dec _ _ _
      (ProgBounded.dec _ _ _
        (ProgBounded.seq
          (ProgBounded.handledCall h_body _ _ _ _
            (ProgBounded.seq (ProgBounded.call funBounded_scratch_release none _)
              (ProgBounded.straight _ rfl)))
          (ProgBounded.straight _ rfl))))
    (by omega)

theorem funBounded_decode_witness_node (K_body : Nat)
    (h_body : FunBounded (ofString "_decode_witness_node_body") K_body) :
    FunBounded (ofString "_decode_witness_node") (K_body + 6) := by
  refine funBounded_of_guestAst 264 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn__decode_witness_node (K_body + 6) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn__decode_witness_node,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_scratch_mark _ _ _
      (ProgBounded.dec _ _ _
        (ProgBounded.dec _ _ _
          (ProgBounded.seq
            (ProgBounded.handledCall (funBounded_decode_witness_node_mpt K_body h_body) _ _ _ _
              (ProgBounded.seq (ProgBounded.call funBounded_scratch_release none _)
                (ProgBounded.straight _ rfl)))
            (ProgBounded.seq
              (ProgBounded.call funBounded_scratch_release none _)
              (ProgBounded.straight _ rfl))))))
    (by omega)

theorem funBounded_decode_witness_to_mpt (K_get K_body : Nat)
    (h_get : FunBounded (ofString "htab_get") K_get)
    (h_body : FunBounded (ofString "_decode_witness_node_body") K_body) :
    FunBounded (ofString "decode_witness_to_mpt") (K_get + K_body + 36) := by
  refine funBounded_of_guestAst 265 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_decode_witness_to_mpt (K_get + K_body + 36) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_decode_witness_to_mpt,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (progBounded_memeq_decCall_const (ofString "is_empty") .one
      (.var .local (ofString "root_hash")) (.var .global (ofString "empty_trie_root"))
      (BitVec.ofNat 64 32) (by decide)
      (ProgBounded.seq
        (ProgBounded.iteMax _ (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl))
        (ProgBounded.decCall (funBounded_nodedb_lookup K_get h_get) _ _ _
          (ProgBounded.seq
            (ProgBounded.iteMax _ (ProgBounded.call funBounded_mpt_fail none _) (ProgBounded.straight _ rfl))
            (ProgBounded.decCall (funBounded_decode_witness_node K_body h_body) _ _ _
              (ProgBounded.seq
                (ProgBounded.iteMax _
                  (ProgBounded.decCall funBounded_alloc _ _ _
                    (ProgBounded.seq
                      (progBounded_memcpy_const none (.var .local (ofString "h"))
                        (.var .local (ofString "root_hash")) (BitVec.ofNat 64 32) (by decide))
                      (ProgBounded.straight _ rfl)))
                  (ProgBounded.straight _ rfl))
                (ProgBounded.straight _ rfl)))))))
    (by
      have h32 : (BitVec.ofNat 64 32).toNat = 32 := rfl
      rw [h32]
      omega)

def trieWalkLoopStep : ProgHOL 64 :=
  match sourceFnBody Guest.Software.guestFn_trie_walk with
  | .dec _ _ _ (.seq (.while _ step) _) => step
  | p => p

theorem progBounded_trie_walk_step (K_meq : Nat)
    (h_meq : FunBounded (ofString "memeq") K_meq) :
    ProgBounded trieWalkLoopStep (2 * K_meq + 3) := by
  dsimp only [trieWalkLoopStep, sourceFnBody, sourceFunctionEntry,
    Guest.Software.guestFn_trie_walk,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.dec _ _ _
      (ProgBounded.seq
        (ProgBounded.iteMax _ (ProgBounded.call funBounded_mpt_fail none _) (ProgBounded.straight _ rfl))
        (ProgBounded.seq
          (ProgBounded.iteMax _
            (ProgBounded.dec _ _ _
              (ProgBounded.seq
                (ProgBounded.iteMax _
                  (ProgBounded.decCall h_meq _ _ _ (ProgBounded.straight _ rfl))
                  (ProgBounded.straight _ rfl))
                (ProgBounded.straight _ rfl)))
            (ProgBounded.straight _ rfl))
          (ProgBounded.iteMax _
            (ProgBounded.dec _ _ _
              (ProgBounded.seq
                (ProgBounded.iteMax _ (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl))
                (ProgBounded.decCall h_meq _ _ _ (ProgBounded.straight _ rfl))))
            (ProgBounded.seq
              (ProgBounded.iteMax _
                (ProgBounded.dec _ _ _ (ProgBounded.straight _ rfl))
                (ProgBounded.straight _ rfl))
              (ProgBounded.straight _ rfl))))))
    (by omega)

theorem funBounded_trie_lookup (K_walk : Nat)
    (h_walk : FunBounded (ofString "trie_walk") K_walk) :
    FunBounded (ofString "trie_lookup") (K_walk + 14) := by
  refine funBounded_of_guestAst 267 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_trie_lookup (K_walk + 14) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_trie_lookup,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.seq
      (progBounded_key_to_nibbles_const none (.var .local (ofString "key_hash32"))
        (.var .global (ofString "mpt_nib_scratch")) (BitVec.ofNat 64 32) (by decide))
      (ProgBounded.tail h_walk _))
    (by
      have h32 : (BitVec.ofNat 64 32).toNat = 32 := rfl
      rw [h32]
      omega)

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

theorem funBounded_mpt_from_witness (K_get K_body : Nat)
    (h_get : FunBounded (ofString "htab_get") K_get)
    (h_body : FunBounded (ofString "_decode_witness_node_body") K_body) :
    FunBounded (ofString "mpt_from_witness") (K_get + K_body + 40) := by
  refine funBounded_of_guestAst 269 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_mpt_from_witness (K_get + K_body + 40) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_mpt_from_witness,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall (funBounded_decode_witness_to_mpt K_get K_body h_get h_body)
      _ _ _ (ProgBounded.tail funBounded_mpt_new _))
    (by omega)

private theorem three_arg_lookup_last_shape (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (fn p1 p2 p3 : MlS) (body : ProgHOL 64) (retShape : ShapeHOL)
    (hp12 : p1 ≠ p2) (hp13 : p1 ≠ p3) (hp23 : p2 ≠ p3)
    (hlookup_fn : code fn = some ([(p1, .one), (p2, .one), (p3, .one)], body, retShape))
    {v1 v2 : ValueHOL 64} {K : BitVec 64}
    {foundBody : ProgHOL 64} {locals : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hfound : PanSemStateFiniteExact.lookupCodeHOLFinite code fn [v1, v2, .val (.word K)] =
      some (foundBody, locals, rs)) :
    foundBody = body ∧ locals.lookup p3 = some (.val (.word K)) := by
  have hbody := lookupCodeHOLFinite_installed_body code fn _ body foundBody retShape rs
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
          have hraw : lookupCodeHOLExact code fn [.val (.word w1), .val (.word w2), .val (.word K)] =
              some (body,
                (fun key => if key = p3 then some (.val (.word K))
                  else if key = p2 then some (.val (.word w2))
                  else if key = p1 then some (.val (.word w1)) else none),
                retShape) := by
            simp [lookupCodeHOLExact, hlookup_fn, shapeOfHOLExact, shapeEqHOL, hp12, hp13, hp23]
          unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
          split at hfound
          · cases hfound
          · rename_i _ _ _ raw
            rw [hraw] at raw
            cases raw
            simp [HolFiniteMapExact.ofExact, HolFiniteMapExact.lookup]

private theorem lookup_mpt_nibble_key :
    originalRuntimeCode.lookup (ofString "mpt_nibble_key") =
      some ([(ofString "m", .one), (ofString "key", .one), (ofString "klen", .one)],
        sourceFnBody Guest.Software.guestFn_mpt_nibble_key, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 270 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_mpt_nibble_key) rfl

theorem runBounded_mpt_nibble_key_body {F : Type}
    (state : PanSemStateFiniteExact 64 F) (K : BitVec 64)
    (hsmall : K.toNat + 136 < 2 ^ 64)
    (hcode : state.code = originalRuntimeCode)
    (hklen : state.locals.lookup (ofString "klen") = some (.val (.word K)))
    (hbudget : (K.toNat / 136) * 163 + K.toNat / 4 + 292 ≤ state.clock) :
    RunBounded state (sourceFnBody Guest.Software.guestFn_mpt_nibble_key)
      ((K.toNat / 136) * 163 + K.toNat / 4 + 292) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_mpt_nibble_key,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  let p_then : ProgHOL 64 :=
    .seq
      (.call (some (none, none)) (ofString "keccak256")
        [.var .local (ofString "key"), .var .local (ofString "klen"), .var .global (ofString "mpt_hash_scratch")])
      (.decCall (ofString "nb") .one (ofString "alloc") [.const (BitVec.ofNat 64 64)]
        (.seq
          (.call (some (none, none)) (ofString "key_to_nibbles")
            [.var .global (ofString "mpt_hash_scratch"), .const (BitVec.ofNat 64 32), .var .local (ofString "nb")])
          (.return (.rstruct [.var .local (ofString "nb"), .const (BitVec.ofNat 64 64)]))))
  let p_ite : ProgHOL 64 :=
    .ite (.cmp .notEqual ((ExpHOL.op .add [.var .local (ofString "m"), .const (BitVec.ofNat 64 8)]).load .one)
        (.const (BitVec.ofNat 64 0)))
      p_then .skip
  have hite : RunBounded state p_ite ((K.toNat / 136) * 163 + 286) := by
    refine RunBounded.ite state
      (.cmp .notEqual ((ExpHOL.op .add [.var .local (ofString "m"), .const (BitVec.ofNat 64 8)]).load .one)
        (.const (BitVec.ofNat 64 0)))
      ?_
      (RunBounded.weaken (RunBounded.ofProg (ProgBounded.straight .skip rfl) hcode (by simp)) (by omega))
    have hkc : RunBounded state
        (.call (some (none, none)) (ofString "keccak256")
          [.var .local (ofString "key"), .var .local (ofString "klen"), .var .global (ofString "mpt_hash_scratch")])
        ((K.toNat / 136) * 163 + 272) := by
      unfold RunBounded
      cases hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
          [.var .local (ofString "key"), .var .local (ofString "klen"), .var .global (ofString "mpt_hash_scratch")] with
      | none =>
        rw [evaluateHOLFiniteState_call, hargs]
        simp
      | some vs =>
        have hk : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
            (.var .local (ofString "klen")) = some (.val (.word K)) := by
          rw [evalHOLFinite_eq_toExact]
          simp [evalHOLExact, hklen]
        obtain ⟨v1, v3, rfl⟩ := evalListHOLFinite_three_word2 state
          (.var .local (ofString "key")) (.var .local (ofString "klen")) (.var .global (ofString "mpt_hash_scratch"))
          K hargs hk
        exact RunBounded.call hargs (by omega) (fun body locals rs hfound => by
          rw [hcode] at hfound
          obtain ⟨rfl, hn⟩ := three_arg_lookup_mid originalRuntimeCode.lookup
            (ofString "keccak256") (ofString "p") (ofString "n") (ofString "out")
            (sourceFnBody Guest.Software.guestFn_keccak256)
            (by decide) (by decide) (by decide) lookup_keccak256 hfound
          exact runBounded_keccak256_body (callEntryStateHOLFinite state locals) K hsmall hcode hn
            (by change (K.toNat / 136) * 163 + 271 ≤ state.clock - 1; omega))
    have hrest_then : ProgBounded
        (.decCall (ofString "nb") .one (ofString "alloc") [.const (BitVec.ofNat 64 64)]
          (.seq
            (.call (some (none, none)) (ofString "key_to_nibbles")
              [.var .global (ofString "mpt_hash_scratch"), .const (BitVec.ofNat 64 32), .var .local (ofString "nb")])
            (.return (.rstruct [.var .local (ofString "nb"), .const (BitVec.ofNat 64 64)])))) 14 := by
      refine ProgBounded.weaken
        (ProgBounded.decCall funBounded_alloc _ _ _
          (ProgBounded.seq
            (progBounded_key_to_nibbles_const none (.var .global (ofString "mpt_hash_scratch"))
              (.var .local (ofString "nb")) (BitVec.ofNat 64 32) (by decide))
            (ProgBounded.straight _ rfl)))
        (by
          have h32 : (BitVec.ofNat 64 32).toNat = 32 := rfl
          omega)
    exact (RunBounded.seq (state := state) (a := (K.toNat / 136) * 163 + 272) (b := 14) hkc
      (by omega) (fun s1 _ hs1_code hs1_clk => hrest_then s1 (hs1_code.trans hcode) hs1_clk)).weaken (by omega)
  refine (RunBounded.seq (state := state) (a := (K.toNat / 136) * 163 + 286) (b := K.toNat / 4 + 6) hite
    (by omega) (fun s1 hr1 hs1_code hs1_clk => ?_)).weaken (by omega)
  have hs1_klen : s1.locals.lookup (ofString "klen") = some (.val (.word K)) := by
    have hpres := evaluate_avoidsLocal_flowing (ofString "klen") p_ite rfl state (by rw [hr1]; exact Or.inl rfl)
    rw [hr1] at hpres
    exact hpres.trans hklen
  cases hargs2 : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
      [ExpHOL.panop .mul [.const (BitVec.ofNat 64 2), .var .local (ofString "klen")]] with
  | none =>
    unfold RunBounded
    rw [evaluateHOLFiniteState_decCall_args_none s1 (ofString "nb2") .one (ofString "alloc") _ _ hargs2]
    simp
  | some vs2 =>
    have hcode1 : s1.code = originalRuntimeCode := hs1_code.trans hcode
    exact (RunBounded.decCall (state := s1) (name := ofString "nb2") (shape := .one)
      (function := ofString "alloc")
      (continuation := .seq
        (.call (some (none, none)) (ofString "key_to_nibbles")
          [.var .local (ofString "key"), .var .local (ofString "klen"), .var .local (ofString "nb2")])
        (.return (.rstruct [.var .local (ofString "nb2"),
          .panop .mul [.const (BitVec.ofNat 64 2), .var .local (ofString "klen")]])))
      (bodyCost := 1) (tailCost := K.toNat / 4 + 4) hargs2 (by omega)
      (fun body locals rs hfound => by
        refine ⟨ProgBounded.bodies_of_fun funBounded_alloc s1 hcode1 (by omega) vs2 body locals rs hfound, ?_⟩
        intro value post hran hpost_clk
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s1 locals) body).1
        rw [hran] at hmeta
        let s2 := setVarHOLFinite (ofString "nb2") value { post with locals := s1.locals }
        have hs2_code : s2.code = originalRuntimeCode := hmeta.trans hcode1
        have hs2_klen : s2.locals.lookup (ofString "klen") = some (.val (.word K)) := by
          have hne : ofString "nb2" ≠ ofString "klen" := by decide
          simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hs1_klen]
        have hktn : RunBounded s2
            (.call (some (none, none)) (ofString "key_to_nibbles")
              [.var .local (ofString "key"), .var .local (ofString "klen"), .var .local (ofString "nb2")])
            (K.toNat / 4 + 4) := by
          unfold RunBounded
          cases hargs3 : evalListHOLFinite s2 (h := fun a => Classical.propDecidable (s2.memaddrs a))
              [.var .local (ofString "key"), .var .local (ofString "klen"), .var .local (ofString "nb2")] with
          | none =>
            rw [evaluateHOLFiniteState_call, hargs3]
            simp
          | some vs3 =>
            have hk3 : evalHOLFinite s2 (h := fun a => Classical.propDecidable (s2.memaddrs a))
                (.var .local (ofString "klen")) = some (.val (.word K)) := by
              rw [evalHOLFinite_eq_toExact]
              simp [evalHOLExact, hs2_klen]
            obtain ⟨u1, u3, rfl⟩ := evalListHOLFinite_three_word2 s2
              (.var .local (ofString "key")) (.var .local (ofString "klen")) (.var .local (ofString "nb2"))
              K hargs3 hk3
            exact RunBounded.call hargs3 (by change K.toNat / 4 + 4 ≤ post.clock; omega)
              (fun b3 l3 rs3 hf3 => by
                rw [hs2_code] at hf3
                obtain ⟨rfl, hn3⟩ := three_arg_lookup_mid originalRuntimeCode.lookup
                  (ofString "key_to_nibbles") (ofString "key") (ofString "n") (ofString "out")
                  (sourceFnBody Guest.Software.guestFn_key_to_nibbles)
                  (by decide) (by decide) (by decide) lookup_key_to_nibbles hf3
                exact runBounded_key_to_nibbles_body (callEntryStateHOLFinite s2 l3) K
                  (by omega) hs2_code hn3
                  (by change K.toNat / 4 + 3 ≤ post.clock - 1; omega))
        exact (RunBounded.seq (state := s2) (a := K.toNat / 4 + 4) (b := 0) hktn
          (by change K.toNat / 4 + 4 + 0 ≤ post.clock; omega)
          (fun s3 _ hs3_code hs3_clk =>
            (ProgBounded.straight _ rfl) s3 (hs3_code.trans hs2_code) hs3_clk)).weaken (by omega))).weaken (by omega)

theorem progBounded_mpt_nibble_key_decCall_exp (name : MlS) (shape : ShapeHOL) (m key sizeExp : ExpHOL 64)
    (K : BitVec 64) {continuation : ProgHOL 64} {tailCost : Nat}
    (hsmall : K.toNat + 136 < 2 ^ 64)
    (heval : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) sizeExp = some (.val (.word K)))
    (hrest : ProgBounded continuation tailCost) :
    ProgBounded (.decCall name shape (ofString "mpt_nibble_key") [m, key, sizeExp] continuation)
      ((K.toNat / 136) * 163 + K.toNat / 4 + 293 + tailCost) := by
  intro F state hcode hbudget
  cases hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [m, key, sizeExp] with
  | none =>
    rw [evaluateHOLFiniteState_decCall_args_none state name shape (ofString "mpt_nibble_key") [m, key, sizeExp] continuation hargs]
    simp
  | some vs =>
    obtain ⟨v1, v2, rfl⟩ := evalListHOLFinite_three_word3_local state m key sizeExp K hargs (heval state)
    have h := RunBounded.decCall (name := name) (shape := shape) (continuation := continuation)
      (bodyCost := (K.toNat / 136) * 163 + K.toNat / 4 + 292) (tailCost := tailCost) hargs (by omega)
      (fun body locals rs hfound => by
        rw [hcode] at hfound
        obtain ⟨rfl, hn⟩ := three_arg_lookup_last_shape originalRuntimeCode.lookup
          (ofString "mpt_nibble_key") (ofString "m") (ofString "key") (ofString "klen")
          (sourceFnBody Guest.Software.guestFn_mpt_nibble_key) (.comb [.one, .one])
          (by decide) (by decide) (by decide) lookup_mpt_nibble_key hfound
        have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state locals)
          (sourceFnBody Guest.Software.guestFn_mpt_nibble_key)
        refine ⟨runBounded_mpt_nibble_key_body (callEntryStateHOLFinite state locals) K hsmall hcode hn
          (by change (K.toNat / 136) * 163 + K.toNat / 4 + 292 ≤ state.clock - 1; omega), ?_⟩
        intro value post hran hpost_clk
        rw [hran] at hmeta
        exact hrest _ (hmeta.1.trans hcode) hpost_clk)
    exact h.weaken (by omega)

theorem funBounded_mpt_get (K_nk K_walk : Nat)
    (h_nk : FunBounded (ofString "mpt_nibble_key") K_nk)
    (h_walk : FunBounded (ofString "trie_walk") K_walk) :
    FunBounded (ofString "mpt_get") (K_nk + K_walk + 5) := by
  refine funBounded_of_guestAst 271 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_mpt_get (K_nk + K_walk + 5) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_mpt_get,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_heap_mark _ _ _
      (ProgBounded.decCall h_nk _ _ _
        (ProgBounded.decCall h_walk _ _ _
          (ProgBounded.seq
            (ProgBounded.call funBounded_heap_release none _)
            (ProgBounded.straight _ rfl)))))
    (by omega)

theorem funBounded_create_branch_from_two_leaves :
    FunBounded (ofString "_create_branch_from_two_leaves") 39 := by
  refine funBounded_of_guestAst 272 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn__create_branch_from_two_leaves 39 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn__create_branch_from_two_leaves,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_node_new_branch _ _ _
      (ProgBounded.seq
        (ProgBounded.iteMax _
          (ProgBounded.straight _ rfl)
          (ProgBounded.decCall funBounded_node_new_leaf _ _ _ (ProgBounded.straight _ rfl)))
        (ProgBounded.seq
          (ProgBounded.iteMax _
            (ProgBounded.straight _ rfl)
            (ProgBounded.decCall funBounded_node_new_leaf _ _ _ (ProgBounded.straight _ rfl)))
          (ProgBounded.straight _ rfl))))
    (by decide)

theorem funBounded_insert_into_leaf (K_meq : Nat)
    (h_meq : FunBounded (ofString "memeq") K_meq) :
    FunBounded (ofString "_insert_into_leaf") (2 ^ 64 + K_meq + 46) := by
  refine funBounded_of_guestAst 273 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn__insert_into_leaf (2 ^ 64 + K_meq + 46) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn__insert_into_leaf,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.dec _ _ _
      (ProgBounded.dec _ _ _
        (ProgBounded.seq
          (ProgBounded.iteMax _
            (ProgBounded.decCall h_meq _ _ _
              (ProgBounded.iteMax _ (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl)))
            (ProgBounded.straight _ rfl))
          (ProgBounded.decCall funBounded_common_prefix_length _ _ _
            (ProgBounded.decCall funBounded_create_branch_from_two_leaves _ _ _
              (ProgBounded.seq
                (ProgBounded.iteMax _
                  (ProgBounded.tail funBounded_node_new_ext _)
                  (ProgBounded.straight _ rfl))
                (ProgBounded.straight _ rfl)))))))
    (by omega)

theorem funBounded_split_extension :
    FunBounded (ofString "_split_extension") 40 := by
  refine funBounded_of_guestAst 274 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn__split_extension 40 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn__split_extension,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.dec _ _ _
      (ProgBounded.dec _ _ _
        (ProgBounded.dec _ _ _
          (ProgBounded.decCall funBounded_node_new_branch _ _ _
            (ProgBounded.dec _ _ _
              (ProgBounded.seq
                (ProgBounded.iteMax _ (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl))
                (ProgBounded.seq
                  (ProgBounded.iteMax _
                    (ProgBounded.decCall funBounded_node_new_ext _ _ _ (ProgBounded.straight _ rfl))
                    (ProgBounded.straight _ rfl))
                  (ProgBounded.dec _ _ _
                    (ProgBounded.seq
                      (ProgBounded.iteMax _
                        (ProgBounded.straight _ rfl)
                        (ProgBounded.dec _ _ _
                          (ProgBounded.seq
                            (ProgBounded.iteMax _
                              (ProgBounded.call funBounded_mpt_fail none _)
                              (ProgBounded.straight _ rfl))
                            (ProgBounded.decCall funBounded_node_new_leaf _ _ _ (ProgBounded.straight _ rfl)))))
                      (ProgBounded.straight _ rfl))))))))))
    (by decide)

def mptInsertNodeLoopStep : ProgHOL 64 :=
  match sourceFnBody Guest.Software.guestFn__mpt_insert_node with
  | .dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.seq (.while _ step) _))) => step
  | p => p

theorem progBounded_mpt_insert_node_step (K_meq : Nat)
    (h_meq : FunBounded (ofString "memeq") K_meq) :
    ProgBounded mptInsertNodeLoopStep (2 ^ 64 + K_meq + 54) := by
  dsimp only [mptInsertNodeLoopStep, sourceFnBody, sourceFunctionEntry,
    Guest.Software.guestFn__mpt_insert_node,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.dec _ _ _
      (ProgBounded.dec _ _ _
        (ProgBounded.dec _ _ _
          (ProgBounded.dec _ _ _
            (ProgBounded.seq
              (ProgBounded.straight _ rfl)
              (ProgBounded.seq
                (ProgBounded.iteMax _
                  (ProgBounded.call funBounded_node_new_leaf (some (.local, ofString "r")) _)
                  (ProgBounded.dec _ _ _
                    (ProgBounded.seq
                      (ProgBounded.iteMax _
                        (ProgBounded.call funBounded_mpt_fail none _)
                        (ProgBounded.straight _ rfl))
                      (ProgBounded.seq
                        (ProgBounded.call funBounded_node_invalidate none _)
                        (ProgBounded.iteMax _
                          (ProgBounded.call (funBounded_insert_into_leaf K_meq h_meq) (some (.local, ofString "r")) _)
                          (ProgBounded.iteMax _
                            (ProgBounded.dec _ _ _
                              (ProgBounded.dec _ _ _
                                (ProgBounded.decCall funBounded_common_prefix_length _ _ _
                                  (ProgBounded.iteMax _
                                    (ProgBounded.straight _ rfl)
                                    (ProgBounded.decCall funBounded_split_extension _ _ _
                                      (ProgBounded.iteMax _
                                        (ProgBounded.call funBounded_node_new_ext (some (.local, ofString "r")) _)
                                        (ProgBounded.straight _ rfl)))))))
                            (ProgBounded.iteMax _
                              (ProgBounded.straight _ rfl)
                              (ProgBounded.dec _ _ _ (ProgBounded.straight _ rfl)))))))))
                (ProgBounded.seq
                  (ProgBounded.iteMax _ (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl))
                  (ProgBounded.straight _ rfl))))))))
    (by omega)

theorem progBounded_cappedCountedDec_const (counter : MlS) (op : Cmp) (K : BitVec 64)
    (hstop : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      s.locals.lookup counter = some (.val (.word K)) →
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp op (.var .local counter) (.const K)) = some (.val (.word 0)))
    {body tail : ProgHOL 64} {cost tailCost : Nat}
    (hbody : CountedBody counter 1 body cost)
    (htail : ProgBounded tail tailCost) :
    ProgBounded (.dec counter .one (.const 0)
      (.seq (.while (.cmp op (.var .local counter) (.const K)) body) tail))
      (K.toNat * (cost + 1) + tailCost) := by
  intro F state code budget
  rw [evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true]
  let s0 := setVarHOLFinite counter (.val (.word 0)) state
  have hs0_code : s0.code = originalRuntimeCode := code
  have hs0_c : s0.locals.lookup counter = some (.val (.word 0)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hwhile := cappedCountedWhile_run counter (.cmp op (.var .local counter) (.const K)) K
    (fun s hc => Or.inr (hstop s hc)) hbody K.toNat s0 hs0_code 0 hs0_c
    (by simp) (by simp) (by change K.toNat * (cost + 1) ≤ state.clock; omega)
  have meta' := PanRunBounded.evaluateHOLFiniteState_metadata s0
    (.while (.cmp op (.var .local counter) (.const K)) body)
  rw [evaluateHOLFiniteState_seq_line780]
  rcases lr : evaluateHOLFiniteState s0 (.while (.cmp op (.var .local counter) (.const K)) body) with ⟨res, mid⟩
  rw [lr] at hwhile meta'
  dsimp only at hwhile meta'
  obtain ⟨sp, kp, sf⟩ := hwhile
  change state.clock ≤ mid.clock + K.toNat * (cost + 1) at sp
  change mid.clock ≤ state.clock at kp
  cases res with
  | none =>
    dsimp only
    obtain ⟨t1, t2, t3⟩ := htail mid (meta'.1.trans code) (by omega)
    exact ⟨by omega, by omega, t3⟩
  | some r =>
    dsimp only
    exact ⟨by omega, kp, sf⟩

theorem funBounded_collapse_branch (K_nc : Nat)
    (h_nc : FunBounded (ofString "nibbles_concat") K_nc) :
    FunBounded (ofString "_collapse_branch") (K_nc + 34) := by
  refine funBounded_of_guestAst 276 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn__collapse_branch (K_nc + 34) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn__collapse_branch,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine ProgBounded.weaken
    (ProgBounded.dec _ _ _
      (ProgBounded.dec _ _ _
        (progBounded_cappedCountedDec_const (ofString "i") .less (BitVec.ofNat 64 16)
          (fun s hc => by
            rw [evalHOLFinite_eq_toExact]
            simp [evalHOLExact, hc, Compiler.Encoders.Asm.wordCmpHOL, Compiler.Encoders.Asm.holAsmSignedLess])
          (countedBody_seq_straight _ rfl rfl rfl CountedBody.incr)
          (ProgBounded.dec _ _ _
            (ProgBounded.seq
              (ProgBounded.iteMax _
                (ProgBounded.seq
                  (ProgBounded.iteMax _
                    (ProgBounded.call funBounded_mpt_fail none _)
                    (ProgBounded.straight _ rfl))
                  (ProgBounded.tail funBounded_node_new_leaf _))
                (ProgBounded.straight _ rfl))
              (ProgBounded.seq
                (ProgBounded.iteMax _
                  (ProgBounded.dec _ _ _
                    (ProgBounded.dec _ _ _
                      (ProgBounded.seq
                        (ProgBounded.iteMax _
                          (ProgBounded.call funBounded_mpt_fail none _)
                          (ProgBounded.straight _ rfl))
                        (ProgBounded.decCall funBounded_alloc _ _ _
    (ProgBounded.seq
      (ProgBounded.iteMax _
        (ProgBounded.seq
          (ProgBounded.straight (.storeByte (.var .local (ofString "dst")) (.const (BitVec.ofNat 64 128))) rfl)
          (ProgBounded.straight (.return (.const (BitVec.ofNat 64 1))) rfl))
        (ProgBounded.straight .skip rfl))
                            (ProgBounded.seq
                              (ProgBounded.iteMax _
                                (ProgBounded.tail funBounded_node_new_ext _)
                                (ProgBounded.straight _ rfl))
                              (ProgBounded.decCall h_nc _ _ _
                                (ProgBounded.seq
                                  (ProgBounded.iteMax _
                                    (ProgBounded.tail funBounded_node_new_leaf _)
                                    (ProgBounded.straight _ rfl))
                                  (ProgBounded.tail funBounded_node_new_ext _)))))))))
                  (ProgBounded.straight _ rfl))
                (ProgBounded.straight _ rfl)))))))
    (by
      have h16 : (BitVec.ofNat 64 16).toNat = 16 := rfl
      omega)

theorem funBounded_delete_ext_finish (K_nc : Nat)
    (h_nc : FunBounded (ofString "nibbles_concat") K_nc) :
    FunBounded (ofString "_delete_ext_finish") (K_nc + 8) := by
  refine funBounded_of_guestAst 277 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn__delete_ext_finish (K_nc + 8) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn__delete_ext_finish,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.seq
      (ProgBounded.iteMax _ (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl))
      (ProgBounded.dec _ _ _
        (ProgBounded.seq
          (ProgBounded.iteMax _ (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl))
          (ProgBounded.seq
            (ProgBounded.iteMax _
              (ProgBounded.call funBounded_mpt_fail none _)
              (ProgBounded.straight _ rfl))
            (ProgBounded.decCall h_nc _ _ _
              (ProgBounded.dec _ _ _
                (ProgBounded.seq
                  (ProgBounded.iteMax _
                    (ProgBounded.tail funBounded_node_new_ext _)
                    (ProgBounded.straight _ rfl))
                  (ProgBounded.tail funBounded_node_new_leaf _))))))))
    (by omega)

def mptDeleteNodeDownStep : ProgHOL 64 :=
  match sourceFnBody Guest.Software.guestFn__mpt_delete_node_body with
  | .dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.seq (.while _ down) _))) => down
  | p => p

def mptDeleteNodeUpStep : ProgHOL 64 :=
  match sourceFnBody Guest.Software.guestFn__mpt_delete_node_body with
  | .dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.seq _ (.seq (.while _ up) _)))) => up
  | p => p

theorem progBounded_mpt_delete_node_down_step (K_meq K_nc : Nat)
    (h_meq : FunBounded (ofString "memeq") K_meq)
    (h_nc : FunBounded (ofString "nibbles_concat") K_nc) :
    ProgBounded mptDeleteNodeDownStep (2 ^ 64 + K_meq + K_nc + 45) := by
  dsimp only [mptDeleteNodeDownStep, sourceFnBody, sourceFunctionEntry,
    Guest.Software.guestFn__mpt_delete_node_body,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.seq
      (ProgBounded.straight _ rfl)
      (ProgBounded.iteMax _
        (ProgBounded.straight _ rfl)
        (ProgBounded.dec _ _ _
          (ProgBounded.seq
            (ProgBounded.iteMax _
              (ProgBounded.call funBounded_mpt_fail none _)
              (ProgBounded.straight _ rfl))
            (ProgBounded.seq
              (ProgBounded.call funBounded_node_invalidate none _)
              (ProgBounded.iteMax _
                (ProgBounded.seq
                  (ProgBounded.straight _ rfl)
                  (ProgBounded.iteMax _
                    (ProgBounded.decCall h_meq _ _ _ (ProgBounded.straight _ rfl))
                    (ProgBounded.straight _ rfl)))
                (ProgBounded.iteMax _
                  (ProgBounded.dec _ _ _
                    (ProgBounded.dec _ _ _
                      (ProgBounded.decCall funBounded_common_prefix_length _ _ _
                        (ProgBounded.iteMax _
                          (ProgBounded.straight _ rfl)
                          (ProgBounded.decCall funBounded_scratch_alloc _ _ _ (ProgBounded.straight _ rfl))))))
                  (ProgBounded.iteMax _
                    (ProgBounded.iteMax _
                      (ProgBounded.straight _ rfl)
                      (ProgBounded.seq
                        (ProgBounded.straight _ rfl)
                        (ProgBounded.seq
                          (ProgBounded.straight _ rfl)
                          (ProgBounded.call (funBounded_collapse_branch K_nc h_nc) (some (.local, ofString "res")) _))))
                    (ProgBounded.dec _ _ _
                      (ProgBounded.decCall funBounded_scratch_alloc _ _ _ (ProgBounded.straight _ rfl)))))))))))
    (by omega)

theorem progBounded_mpt_delete_node_up_step (K_nc : Nat)
    (h_nc : FunBounded (ofString "nibbles_concat") K_nc) :
    ProgBounded mptDeleteNodeUpStep (K_nc + 36) := by
  dsimp only [mptDeleteNodeUpStep, sourceFnBody, sourceFunctionEntry,
    Guest.Software.guestFn__mpt_delete_node_body,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.dec _ _ _
      (ProgBounded.seq
        (ProgBounded.iteMax _
          (ProgBounded.call (funBounded_delete_ext_finish K_nc h_nc) (some (.local, ofString "res")) _)
          (ProgBounded.seq
            (ProgBounded.straight _ rfl)
            (ProgBounded.call (funBounded_collapse_branch K_nc h_nc) (some (.local, ofString "res")) _)))
        (ProgBounded.straight _ rfl)))
    (by omega)

theorem funBounded_mpt_delete_node (K_body : Nat)
    (h_body : FunBounded (ofString "_mpt_delete_node_body") K_body) :
    FunBounded (ofString "_mpt_delete_node") (K_body + 6) := by
  refine funBounded_of_guestAst 279 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn__mpt_delete_node (K_body + 6) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn__mpt_delete_node,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_scratch_mark _ _ _
      (ProgBounded.dec _ _ _
        (ProgBounded.dec _ _ _
          (ProgBounded.seq
            (ProgBounded.handledCall h_body _ _ _ _
              (ProgBounded.seq
                (ProgBounded.call funBounded_scratch_release none _)
                (ProgBounded.straight _ rfl)))
            (ProgBounded.seq
              (ProgBounded.call funBounded_scratch_release none _)
              (ProgBounded.straight _ rfl))))))
    (by omega)

theorem funBounded_mpt_set (K_nk K_del K_ins : Nat)
    (h_nk : FunBounded (ofString "mpt_nibble_key") K_nk)
    (h_del : FunBounded (ofString "_mpt_delete_node") K_del)
    (h_ins : FunBounded (ofString "_mpt_insert_node") K_ins) :
    FunBounded (ofString "mpt_set") (K_nk + K_del + K_ins + 4) := by
  refine funBounded_of_guestAst 280 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_mpt_set (K_nk + K_del + K_ins + 4) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_mpt_set,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall h_nk _ _ _
      (ProgBounded.dec _ _ _
        (ProgBounded.seq
          (ProgBounded.iteMax _
            (ProgBounded.call h_del (some (.local, ofString "root")) _)
            (ProgBounded.call h_ins (some (.local, ofString "root")) _))
          (ProgBounded.straight _ rfl))))
    (by omega)

theorem cappedCountedStepWhile_run (counter : MlS) (cond : ExpHOL 64) (K : BitVec 64)
    (hstop : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      s.locals.lookup counter = some (.val (.word K)) →
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) cond = none ∨
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) cond = some (.val (.word 0)))
    {body : ProgHOL 64} {cost : Nat}
    (hbody : CountedStep counter 1 body cost) :
    ∀ n : Nat, ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      s.code = originalRuntimeCode →
      ∀ w : BitVec 64, s.locals.lookup counter = some (.val (.word w)) →
      w.toNat ≤ K.toNat → K.toNat - w.toNat = n → n * (cost + 1) ≤ s.clock →
      let r := evaluateHOLFiniteState s (.while cond body)
      s.clock ≤ r.2.clock + n * (cost + 1) ∧ r.2.clock ≤ s.clock ∧ r.1 ≠ some .timeOut := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro F s code w atC within dist budget
    dsimp only
    rw [evaluateHOLFiniteState_while_total]
    cases gr : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) cond with
    | none => simp
    | some v =>
      cases v with
      | rStruct _ => simp
      | nStruct _ _ => simp
      | val wl =>
        cases wl with
        | word test =>
          by_cases zero : test = 0
          · simp [zero]
          · dsimp only
            rw [if_pos zero]
            have lt : w.toNat < K.toNat := by
              by_contra nlt
              have same : w = K := BitVec.eq_of_toNat_eq (by omega)
              rcases hstop s (by simpa [same] using atC) with hno | hfin
              · rw [gr] at hno; cases hno
              · rw [gr] at hfin; cases hfin; exact zero rfl
            have posN : 0 < n := by omega
            have oneIter : cost + 1 ≤ n * (cost + 1) := Nat.le_mul_of_pos_left _ posN
            have clk : s.clock ≠ 0 := by omega
            rw [if_neg clk, fixClockHOLFinite_evaluateState]
            have stepRun := hbody (decClockHOLFinite s) code w atC (by change cost ≤ s.clock - 1; omega)
            rcases bodyRun : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨res, mid⟩
            rw [bodyRun] at stepRun
            dsimp only at stepRun
            obtain ⟨spent, kept, safe, noCont, advance⟩ := stepRun
            change s.clock - 1 ≤ mid.clock + cost at spent
            change mid.clock ≤ s.clock - 1 at kept
            cases res with
            | none =>
              dsimp only
              obtain ⟨nextC, nextCode⟩ := advance rfl
              have hadd : (w + 1).toNat = w.toNat + 1 :=
                BitVec.toNat_add_of_lt (by have := K.isLt; change w.toNat + 1 < 2 ^ 64; omega)
              have hmul : (n - 1) * (cost + 1) + (cost + 1) = n * (cost + 1) := by
                have hs : n - 1 + 1 = n := by omega
                calc (n - 1) * (cost + 1) + (cost + 1) = (n - 1 + 1) * (cost + 1) := by rw [Nat.add_mul, Nat.one_mul]
                  _ = n * (cost + 1) := by rw [hs]
              obtain ⟨t1, t2, t3⟩ := ih (n - 1) (by omega) mid (nextCode.trans code) (w + 1)
                nextC (by rw [hadd]; omega) (by rw [hadd]; omega) (by omega)
              exact ⟨by omega, by omega, t3⟩
            | some r =>
              cases r with
              | «continue» => exact absurd rfl noCont
              | «break» => exact ⟨by simp; omega, by simp; omega, by simp⟩
              | timeOut => exact absurd rfl safe
              | _ => exact ⟨by simp; omega, by simp; omega, by simp⟩

theorem progBounded_cappedCountedStep_const (counter : MlS) (cond : ExpHOL 64) (K : BitVec 64)
    (hstop : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      s.locals.lookup counter = some (.val (.word K)) →
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) cond = none ∨
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) cond = some (.val (.word 0)))
    (initExp : ExpHOL 64)
    {body tail : ProgHOL 64} {cost tailCost : Nat}
    (hbody : CountedStep counter 1 body cost)
    (htail : ProgBounded tail tailCost)
    (hinit : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) initExp = none ∨
      ∃ w0 : BitVec 64,
        evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) initExp = some (.val (.word w0)) ∧
        (w0.toNat ≤ K.toNat ∨
          (∀ {G : Type} (s' : PanSemStateFiniteExact 64 G),
            s'.locals.lookup counter = some (.val (.word w0)) →
            evalHOLFinite s' (h := fun a => Classical.propDecidable (s'.memaddrs a)) cond = none ∨
            evalHOLFinite s' (h := fun a => Classical.propDecidable (s'.memaddrs a)) cond = some (.val (.word 0))))) :
    ProgBounded (.dec counter .one initExp
      (.seq (.while cond body) tail))
      (K.toNat * (cost + 1) + tailCost) := by
  intro F state code budget
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  rcases hinit state with hno | ⟨w0, hev, hcases⟩
  · rw [evalHOLFinite_eq_toExact] at hno
    rw [hno]
    simp
  · rw [evalHOLFinite_eq_toExact] at hev
    rw [hev]
    simp only [shapeOfHOLExact, shapeEqHOL, if_true]
    let s0 := setVarHOLFinite counter (.val (.word w0)) state
    have hs0_code : s0.code = originalRuntimeCode := code
    have hs0_c : s0.locals.lookup counter = some (.val (.word w0)) := by
      simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hloop : s0.clock ≤ (evaluateHOLFiniteState s0 (.while cond body)).2.clock + K.toNat * (cost + 1) ∧
        (evaluateHOLFiniteState s0 (.while cond body)).2.clock ≤ s0.clock ∧
        (evaluateHOLFiniteState s0 (.while cond body)).1 ≠ some .timeOut := by
      rcases hcases with hle | hout_cond
      · have ceil : (K.toNat - w0.toNat) * (cost + 1) ≤ K.toNat * (cost + 1) :=
          Nat.mul_le_mul_right _ (by omega)
        obtain ⟨l1, l2, l3⟩ := cappedCountedStepWhile_run counter cond K hstop hbody
          (K.toNat - w0.toNat) s0 hs0_code w0 hs0_c hle rfl
          (by change (K.toNat - w0.toNat) * (cost + 1) ≤ state.clock; omega)
        exact ⟨by omega, l2, l3⟩
      · have hw_out := hout_cond s0 hs0_c
        rw [evaluateHOLFiniteState_while_total]
        rcases hw_out with hno_c | hzero_c
        · rw [hno_c]; simp
        · rw [hzero_c]; simp
    have meta' := PanRunBounded.evaluateHOLFiniteState_metadata s0 (.while cond body)
    rw [evaluateHOLFiniteState_seq_line780]
    rcases lr : evaluateHOLFiniteState s0 (.while cond body) with ⟨res, mid⟩
    rw [lr] at hloop meta'
    dsimp only at hloop meta'
    obtain ⟨sp, kp, sf⟩ := hloop
    change state.clock ≤ mid.clock + K.toNat * (cost + 1) at sp
    change mid.clock ≤ state.clock at kp
    cases res with
    | none =>
      dsimp only
      obtain ⟨t1, t2, t3⟩ := htail mid (meta'.1.trans code) (by omega)
      exact ⟨by omega, by omega, t3⟩
    | some r =>
      dsimp only
      exact ⟨by omega, kp, sf⟩

theorem funBounded_node_needs_rlp : FunBounded (ofString "_node_needs_rlp") 0 := by
  refine funBounded_of_guestAst 283 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn__node_needs_rlp 0 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn__node_needs_rlp,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.seq
      (ProgBounded.iteMax _ (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl))
      (ProgBounded.seq
        (ProgBounded.iteMax _ (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl))
        (ProgBounded.seq
          (ProgBounded.iteMax _ (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl))
          (ProgBounded.straight _ rfl))))
    (by decide)

theorem funBounded_rlp_value_encoded_len : FunBounded (ofString "rlp_value_encoded_len") 11 := by
  refine funBounded_of_guestAst 286 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_rlp_value_encoded_len 11 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_rlp_value_encoded_len,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.dec _ _ _
      (ProgBounded.seq
        (ProgBounded.iteMax _ (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl))
        (ProgBounded.tail funBounded_rlp_bytes_encoded_len _)))
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
    (ProgBounded.seq
      (ProgBounded.iteMax _ (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl))
      (ProgBounded.seq
        (ProgBounded.iteMax _ (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl))
        (ProgBounded.seq
          (ProgBounded.iteMax _
            (ProgBounded.call funBounded_mpt_fail none _)
            (ProgBounded.straight _ rfl))
          (ProgBounded.dec _ _ _
            (ProgBounded.seq
              (ProgBounded.iteMax _ (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl))
              (ProgBounded.straight _ rfl))))))
    (by decide)

theorem funBounded_node_hash_cached (K_keccak : Nat)
    (h_keccak : FunBounded (ofString "keccak256") K_keccak) :
    FunBounded (ofString "node_hash_cached") (K_keccak + 4) := by
  refine funBounded_of_guestAst 288 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_node_hash_cached (K_keccak + 4) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_node_hash_cached,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.dec _ _ _
      (ProgBounded.seq
        (ProgBounded.iteMax _ (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl))
        (ProgBounded.seq
          (ProgBounded.iteMax _
            (ProgBounded.call funBounded_mpt_fail none _)
            (ProgBounded.straight _ rfl))
          (ProgBounded.decCall funBounded_alloc _ _ _
            (ProgBounded.seq
              (ProgBounded.call h_keccak none _)
              (ProgBounded.straight _ rfl))))))
    (by omega)

theorem progBounded_node_write_ref_short :
    ProgBounded
      (.ite (.cmp .lower (.var .local (ofString "rl")) (.const (BitVec.ofNat 64 32)))
        (.seq (.call (some (none, none)) (ofString "memcpy")
          [.var .local (ofString "dst"), .var .local (ofString "rp"), .var .local (ofString "rl")])
          (.return (.var .local (ofString "rl"))))
        .skip)
      11 := by
  intro F s hs_code hs_clk
  change RunBounded s _ 11
  unfold RunBounded
  rw [evaluateHOLFiniteState_ite]
  cases hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .lower (.var .local (ofString "rl")) (.const (BitVec.ofNat 64 32))) with
  | none => simp
  | some cv =>
    cases cv with
    | rStruct _ => simp
    | nStruct _ _ => simp
    | val cwl =>
      cases cwl with
      | word cw =>
        dsimp only
        by_cases hcw0 : cw = 0
        · rw [if_pos hcw0]
          exact (ProgBounded.weaken (ProgBounded.straight .skip rfl) (by omega)) s hs_code hs_clk
        · rw [if_neg hcw0]
          have hrl_lt : ∃ Krl : BitVec 64,
              s.locals.lookup (ofString "rl") = some (.val (.word Krl)) ∧ Krl.toNat < 32 := by
            cases hrl : s.locals.lookup (ofString "rl") with
            | none => simp [evalHOLExact, hrl] at hcond
            | some rv =>
              cases rv with
              | rStruct _ => simp [evalHOLExact, hrl] at hcond
              | nStruct _ _ => simp [evalHOLExact, hrl] at hcond
              | val rwl =>
                cases rwl with
                | word Krl =>
                  refine ⟨Krl, rfl, ?_⟩
                  simp only [evalHOLExact, hrl, Compiler.Encoders.Asm.wordCmpHOL] at hcond
                  injection hcond with hcond
                  injection hcond with hcond
                  injection hcond with hcond
                  by_cases hlt : Krl < BitVec.ofNat 64 32
                  · rw [BitVec.lt_def] at hlt
                    simpa using hlt
                  · simp [hlt] at hcond
                    exact absurd hcond.symm hcw0
          obtain ⟨Krl, hs_rl, hlt32⟩ := hrl_lt
          have hkrl_small : Krl.toNat + 32 < 2 ^ 64 := by omega
          have hmc : RunBounded s
              (.call (some (none, none)) (ofString "memcpy")
                [.var .local (ofString "dst"), .var .local (ofString "rp"), .var .local (ofString "rl")])
              (Krl.toNat / 8 + 8) := by
            have heq_call : evaluateHOLFiniteState s
                (.call (some (none, none)) (ofString "memcpy")
                  [.var .local (ofString "dst"), .var .local (ofString "rp"), .var .local (ofString "rl")]) =
              evaluateHOLFiniteState s
                (.call (some (none, none)) (ofString "memcpy")
                  [.var .local (ofString "dst"), .var .local (ofString "rp"), .const Krl]) := by
              have hlist : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
                  [.var .local (ofString "dst"), .var .local (ofString "rp"), .var .local (ofString "rl")] =
                evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
                  [.var .local (ofString "dst"), .var .local (ofString "rp"), .const Krl] := by
                rw [evalListHOLFinite_eq_toExact, evalListHOLFinite_eq_toExact]
                simp [evalListHOLExact, evalHOLExact, hs_rl]
              rw [evaluateHOLFiniteState_call, evaluateHOLFiniteState_call, hlist]
            unfold RunBounded
            rw [heq_call]
            exact progBounded_memcpy_const none (.var .local (ofString "dst")) (.var .local (ofString "rp"))
              Krl hkrl_small s hs_code (by omega)
          exact (RunBounded.seq (state := s) (a := Krl.toNat / 8 + 8) (b := 0) hmc
            (by omega) (fun s' _ hs'_code hs'_clk =>
              (ProgBounded.straight (.return (.var .local (ofString "rl"))) rfl)
                s' (hs'_code.trans hs_code) hs'_clk)).weaken (by omega)

theorem funBounded_node_write_ref (K_keccak : Nat)
    (h_keccak : FunBounded (ofString "keccak256") K_keccak) :
    FunBounded (ofString "node_write_ref") (K_keccak + 41) := by
  refine funBounded_of_guestAst 289 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_node_write_ref (K_keccak + 41) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_node_write_ref,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  have hmc32_small : (BitVec.ofNat 64 32).toNat + 32 < 2 ^ 64 := by decide
  have hp : ProgBounded
      (.seq
        (.ite (.cmp .equal (.var .local (ofString "child")) (.const (BitVec.ofNat 64 0)))
          (.seq
            (.storeByte (.var .local (ofString "dst")) (.const (BitVec.ofNat 64 128)))
            (.return (.const (BitVec.ofNat 64 1))))
          .skip)
        (.seq
          (.ite (.cmp .equal ((ExpHOL.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 0)]).load .one)
              (.const (BitVec.ofNat 64 0)))
            (.seq
              (.storeByte (.var .local (ofString "dst")) (.const (BitVec.ofNat 64 160)))
              (.seq
                (.call (some (none, none)) (ofString "memcpy")
                  [.op .add [.var .local (ofString "dst"), .const (BitVec.ofNat 64 1)],
                   (ExpHOL.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 24)]).load .one,
                   .const (BitVec.ofNat 64 32)])
                (.return (.const (BitVec.ofNat 64 33)))))
            .skip)
          (.seq
            (.ite (.cmp .equal ((ExpHOL.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 8)]).load .one)
                (.const (BitVec.ofNat 64 0)))
              (.call (some (none, none)) (ofString "mpt_fail") [.const (BitVec.ofNat 64 13)])
              .skip)
            (.dec (ofString "rp") .one ((ExpHOL.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 8)]).load .one)
              (.dec (ofString "rl") .one ((ExpHOL.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 16)]).load .one)
                (.seq
                  (.ite (.cmp .lower (.var .local (ofString "rl")) (.const (BitVec.ofNat 64 32)))
                    (.seq
                      (.call (some (none, none)) (ofString "memcpy")
                        [.var .local (ofString "dst"), .var .local (ofString "rp"), .var .local (ofString "rl")])
                      (.return (.var .local (ofString "rl"))))
                    .skip)
                  (.decCall (ofString "h") .one (ofString "node_hash_cached") [.var .local (ofString "child")]
                    (.seq
                      (.storeByte (.var .local (ofString "dst")) (.const (BitVec.ofNat 64 160)))
                      (.seq
                        (.call (some (none, none)) (ofString "memcpy")
                          [.op .add [.var .local (ofString "dst"), .const (BitVec.ofNat 64 1)],
                           .var .local (ofString "h"),
                           .const (BitVec.ofNat 64 32)])
                        (.return (.const (BitVec.ofNat 64 33))))))))))))
      (0 + (max (0 + ((BitVec.ofNat 64 32).toNat / 8 + 8 + 0)) 0 +
        (max (0 + 1) 0 + (11 + (K_keccak + 4 + 1 + (0 + ((BitVec.ofNat 64 32).toNat / 8 + 8 + 0))))))) :=
    ProgBounded.seq
      (ProgBounded.straight _ rfl)
      (ProgBounded.seq
        (ProgBounded.iteMax _
          (ProgBounded.seq
            (ProgBounded.straight _ rfl)
            (ProgBounded.seq
              (progBounded_memcpy_const none _ _ (BitVec.ofNat 64 32) hmc32_small)
              (ProgBounded.straight _ rfl)))
          (ProgBounded.straight _ rfl))
        (ProgBounded.seq
          (ProgBounded.iteMax _
            (ProgBounded.call funBounded_mpt_fail none _)
            (ProgBounded.straight _ rfl))
          (ProgBounded.dec _ _ _
            (ProgBounded.dec _ _ _
              (ProgBounded.seq
                progBounded_node_write_ref_short
                (ProgBounded.decCall (funBounded_node_hash_cached K_keccak h_keccak) _ _ _
                  (ProgBounded.seq
                    (ProgBounded.straight _ rfl)
                    (ProgBounded.seq
                      (progBounded_memcpy_const none _ _ (BitVec.ofNat 64 32) hmc32_small)
                      (ProgBounded.straight _ rfl)))))))))
  exact @ProgBounded.weaken _ _ (K_keccak + 41) hp (by
    have h32 : (BitVec.ofNat 64 32).toNat / 8 = 4 := rfl
    rw [h32]
    omega)

theorem funBounded_node_rlp_begin : FunBounded (ofString "_node_rlp_begin") (2 ^ 63 + 31) := by
  refine funBounded_of_guestAst 281 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn__node_rlp_begin (2 ^ 63 + 31) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn__node_rlp_begin,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.dec _ _ _
      (ProgBounded.dec _ _ _
        (ProgBounded.dec _ _ _
          (ProgBounded.dec _ _ _
            (ProgBounded.seq
              (ProgBounded.iteMax _
                (ProgBounded.dec _ _ _
                  (ProgBounded.seq
                    (ProgBounded.call funBounded_alloc (some (.local, ofString "cbuf")) _)
                    (ProgBounded.dec _ _ _
                      (ProgBounded.seq
                        (ProgBounded.iteMax _ (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl))
                        (ProgBounded.seq
                          (ProgBounded.call funBounded_nibble_list_to_compact (some (.local, ofString "clen")) _)
                          (ProgBounded.decCall funBounded_rlp_bytes_encoded_len _ _ _
                            (ProgBounded.seq
                              (ProgBounded.straight _ rfl)
                              (ProgBounded.iteMax _
                                (ProgBounded.decCall funBounded_rlp_value_encoded_len _ _ _
                                  (ProgBounded.straight _ rfl))
                                (ProgBounded.straight _ rfl)))))))))
                (ProgBounded.straight _ rfl))
              (ProgBounded.straight _ rfl))))))
    (by decide)

theorem funBounded_node_rlp_finish (K_reb K_keccak : Nat)
    (h_reb : FunBounded (ofString "rlp_encode_bytes") K_reb)
    (h_keccak : FunBounded (ofString "keccak256") K_keccak) :
    FunBounded (ofString "_node_rlp_finish") (2 ^ 64 + 2 * K_reb + 16 * K_keccak + 782) := by
  refine funBounded_of_guestAst 282 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn__node_rlp_finish (2 ^ 64 + 2 * K_reb + 16 * K_keccak + 782) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn__node_rlp_finish,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  have hnwr := funBounded_node_write_ref K_keccak h_keccak
  exact @ProgBounded.weaken _ _ (2 ^ 64 + 2 * K_reb + 16 * K_keccak + 782)
    (ProgBounded.dec _ _ _
      (ProgBounded.dec _ _ _
        (ProgBounded.dec _ _ _
          (ProgBounded.dec _ _ _
            (ProgBounded.seq
              (ProgBounded.iteMax _
                (ProgBounded.decCall funBounded_node_ref_len _ _ _ (ProgBounded.straight _ rfl))
                (ProgBounded.straight _ rfl))
              (ProgBounded.seq
                (ProgBounded.iteMax _
                  (progBounded_cappedCountedStep_const (ofString "i")
                    (.cmp .less (.var .local (ofString "i")) (.const (BitVec.ofNat 64 16)))
                    (BitVec.ofNat 64 16)
                    (fun s hc => Or.inr (by
                      rw [evalHOLFinite_eq_toExact]
                      simp [evalHOLExact, hc, Compiler.Encoders.Asm.wordCmpHOL,
                        Compiler.Encoders.Asm.holAsmSignedLess]))
                    (.const (BitVec.ofNat 64 0))
                    (cost := 2)
                    (countedStep_decCall (ofString "rl2") .one (ofString "node_ref_len") _ (by decide) funBounded_node_ref_len
                      (countedStep_seq_straight _ rfl rfl rfl countedStep_incr))
                    (ProgBounded.decCall funBounded_rlp_value_encoded_len _ _ _
                      (ProgBounded.straight _ rfl))
                    (fun s => Or.inr ⟨0, by rw [evalHOLFinite_eq_toExact]; rfl, Or.inl (by decide)⟩))
                  (ProgBounded.straight _ rfl))
                (ProgBounded.decCall funBounded_rlp_list_header_len _ _ _
                  (ProgBounded.decCall funBounded_alloc _ _ _
                    (ProgBounded.seq
                      (ProgBounded.call funBounded_rlp_encode_list_header none _)
                      (ProgBounded.dec _ _ _
                        (ProgBounded.seq
                          (ProgBounded.iteMax _
                            (ProgBounded.decCall h_reb _ _ _
                              (ProgBounded.seq
                                (ProgBounded.straight _ rfl)
                                (ProgBounded.iteMax _
                                  (ProgBounded.decCall h_reb _ _ _ (ProgBounded.straight _ rfl))
                                  (ProgBounded.decCall hnwr _ _ _ (ProgBounded.straight _ rfl)))))
                            (progBounded_cappedCountedStep_const (ofString "j")
                              (.cmp .less (.var .local (ofString "j")) (.const (BitVec.ofNat 64 16)))
                              (BitVec.ofNat 64 16)
                              (fun s hc => Or.inr (by
                                rw [evalHOLFinite_eq_toExact]
                                simp [evalHOLExact, hc, Compiler.Encoders.Asm.wordCmpHOL,
                                  Compiler.Encoders.Asm.holAsmSignedLess]))
                              (.const (BitVec.ofNat 64 0))
                              (cost := K_keccak + 42)
                              (countedStep_decCall (ofString "w4") .one (ofString "node_write_ref") _ (by decide) hnwr
                                (countedStep_seq_straight _ rfl rfl rfl countedStep_incr))
                              (ProgBounded.decCall h_reb _ _ _ (ProgBounded.straight _ rfl))
                              (fun s => Or.inr ⟨0, by rw [evalHOLFinite_eq_toExact]; rfl, Or.inl (by decide)⟩)))
                          (ProgBounded.straight _ rfl))))))))))))
    (by
      have h16 : (BitVec.ofNat 64 16).toNat = 16 := rfl
      rw [h16]
      omega)

theorem countedStep_tail {counter : MlS} {step : BitVec 64}
    (first : ProgHOL 64) {tail : ProgHOL 64} {cost : Nat}
    (hfirst : CountedStep counter step first 0)
    (htail : ProgBounded tail cost)
    (havoid : avoidsLocal counter tail = true)
    (hnoCont : noTopContinue tail = true) :
    CountedStep counter step (.seq first tail) cost := by
  intro F state code w atC budget
  have h1 := hfirst state code w atC (by omega)
  have meta1 := PanRunBounded.evaluateHOLFiniteState_metadata state first
  rw [evaluateHOLFiniteState_seq_line780]
  rcases r1 : evaluateHOLFiniteState state first with ⟨res1, mid⟩
  rw [r1] at h1 meta1
  dsimp only at h1 meta1
  obtain ⟨sp1, kp1, sf1, nc1, adv1⟩ := h1
  cases res1 with
  | none =>
    dsimp only
    obtain ⟨atMid, codeMid⟩ := adv1 rfl
    have h2 : RunBounded mid tail cost := htail mid (codeMid.trans code) (by omega)
    unfold RunBounded at h2
    have frame := evaluate_avoidsLocal_flowing counter tail havoid mid
    have noCont := evaluate_noTopContinue tail hnoCont mid
    have meta2 := PanRunBounded.evaluateHOLFiniteState_metadata mid tail
    rcases r2 : evaluateHOLFiniteState mid tail with ⟨res2, post⟩
    rw [r2] at h2 frame noCont meta2
    dsimp only at h2 frame noCont meta2 ⊢
    obtain ⟨sp2, kp2, sf2⟩ := h2
    refine ⟨by omega, by omega, sf2, noCont, fun hnorm => ?_⟩
    exact ⟨(frame (Or.inl hnorm)).trans atMid, meta2.1.trans codeMid⟩
  | some r =>
    dsimp only
    exact ⟨by omega, kp1, sf1, nc1, fun h => by simp at h⟩

theorem signedStepWhile_run (counter : MlS) (cond : ExpHOL 64) (K : BitVec 64)
    (hK_pos : K.toNat < 2 ^ 63)
    (hstop : ∀ {F : Type} (w : BitVec 64) (s : PanSemStateFiniteExact 64 F),
      w.toNat < 2 ^ 63 → K.toNat ≤ w.toNat →
      s.locals.lookup counter = some (.val (.word w)) →
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) cond = none ∨
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) cond = some (.val (.word 0)))
    {body : ProgHOL 64} {cost : Nat}
    (hbody : CountedStep counter 1 body cost) :
    ∀ n : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F),
      state.code = originalRuntimeCode →
      ∀ w : BitVec 64, state.locals.lookup counter = some (.val (.word w)) →
      ((w.toNat < 2 ^ 63 ∧ K.toNat - w.toNat ≤ n) ∨
        (2 ^ 63 ≤ w.toNat ∧ 2 ^ 64 - w.toNat + K.toNat ≤ n)) →
      n * (cost + 1) ≤ state.clock →
      let ev := evaluateHOLFiniteState state (.while cond body)
      state.clock ≤ ev.2.clock + n * (cost + 1) ∧
        ev.2.clock ≤ state.clock ∧ ev.1 ≠ some .timeOut := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro F s code w atC hrank budget
    dsimp only
    rw [evaluateHOLFiniteState_while_total]
    cases gr : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) cond with
    | none => simp
    | some v =>
      cases v with
      | rStruct _ => simp
      | nStruct _ _ => simp
      | val wl =>
        cases wl with
        | word test =>
          by_cases zero : test = 0
          · simp [zero]
          · dsimp only
            rw [if_pos zero]
            have hw_lt : (w.toNat < 2 ^ 63 ∧ w.toNat < K.toNat) ∨ 2 ^ 63 ≤ w.toNat := by
              rcases hrank with ⟨hsm, _⟩ | ⟨hneg, _⟩
              · refine Or.inl ⟨hsm, ?_⟩
                by_contra nlt
                rcases hstop w s hsm (by omega) atC with hno | hfin
                · rw [gr] at hno; cases hno
                · rw [gr] at hfin; cases hfin; exact zero rfl
              · exact Or.inr hneg
            have posN : 0 < n := by
              have hw_max := w.isLt
              rcases hrank with ⟨hsm, hle⟩ | ⟨hneg, hle⟩
              · rcases hw_lt with ⟨_, hlt⟩ | hneg' <;> omega
              · omega
            have oneIter : cost + 1 ≤ n * (cost + 1) := Nat.le_mul_of_pos_left _ posN
            have clk : s.clock ≠ 0 := by omega
            rw [if_neg clk, fixClockHOLFinite_evaluateState]
            have stepRun := hbody (decClockHOLFinite s) code w atC (by change cost ≤ s.clock - 1; omega)
            rcases bodyRun : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨res, mid⟩
            rw [bodyRun] at stepRun
            dsimp only at stepRun
            obtain ⟨spent, kept, safe, noCont, advance⟩ := stepRun
            change s.clock - 1 ≤ mid.clock + cost at spent
            change mid.clock ≤ s.clock - 1 at kept
            cases res with
            | none =>
              dsimp only
              obtain ⟨nextC, nextCode⟩ := advance rfl
              have hmul : (n - 1) * (cost + 1) + (cost + 1) = n * (cost + 1) := by
                have hs : n - 1 + 1 = n := by omega
                calc (n - 1) * (cost + 1) + (cost + 1) = (n - 1 + 1) * (cost + 1) := by rw [Nat.add_mul, Nat.one_mul]
                  _ = n * (cost + 1) := by rw [hs]
              have hnext_rank : ((w + 1).toNat < 2 ^ 63 ∧ K.toNat - (w + 1).toNat ≤ n - 1) ∨
                  (2 ^ 63 ≤ (w + 1).toNat ∧ 2 ^ 64 - (w + 1).toNat + K.toNat ≤ n - 1) := by
                have hw_max := w.isLt
                rcases hw_lt with ⟨hsm, hlt⟩ | hneg
                · have hadd : (w + 1).toNat = w.toNat + 1 :=
                    BitVec.toNat_add_of_lt (by change w.toNat + 1 < 2 ^ 64; omega)
                  rcases hrank with ⟨_, hle⟩ | ⟨hneg', _⟩
                  · exact Or.inl ⟨by rw [hadd]; omega, by rw [hadd]; omega⟩
                  · omega
                · rcases hrank with ⟨hsm', _⟩ | ⟨_, hle⟩
                  · omega
                  · by_cases hwrap : w.toNat + 1 = 2 ^ 64
                    · have hadd0 : (w + 1).toNat = 0 := by
                        simp [BitVec.toNat_add, hwrap]
                      exact Or.inl ⟨by rw [hadd0]; omega, by rw [hadd0]; omega⟩
                    · have hadd : (w + 1).toNat = w.toNat + 1 :=
                        BitVec.toNat_add_of_lt (by change w.toNat + 1 < 2 ^ 64; omega)
                      exact Or.inr ⟨by rw [hadd]; omega, by rw [hadd]; omega⟩
              obtain ⟨t1, t2, t3⟩ := ih (n - 1) (by omega) mid (nextCode.trans code) (w + 1)
                nextC hnext_rank (by omega)
              exact ⟨by omega, by omega, t3⟩
            | some r =>
              cases r with
              | «continue» => exact absurd rfl noCont
              | «break» => exact ⟨by simp; omega, by simp; omega, by simp⟩
              | timeOut => exact absurd rfl safe
              | _ => exact ⟨by simp; omega, by simp; omega, by simp⟩

theorem progBounded_signedStep_anyInit (counter : MlS) (cond : ExpHOL 64) (K : BitVec 64)
    (hK_pos : K.toNat < 2 ^ 63)
    (hstop : ∀ {F : Type} (w : BitVec 64) (s : PanSemStateFiniteExact 64 F),
      w.toNat < 2 ^ 63 → K.toNat ≤ w.toNat →
      s.locals.lookup counter = some (.val (.word w)) →
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) cond = none ∨
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) cond = some (.val (.word 0)))
    (initExp : ExpHOL 64)
    {body tail : ProgHOL 64} {cost tailCost : Nat}
    (hbody : CountedStep counter 1 body cost)
    (htail : ProgBounded tail tailCost)
    (hinit : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) initExp = none ∨
      ∃ w0 : BitVec 64,
        evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) initExp = some (.val (.word w0))) :
    ProgBounded (.dec counter .one initExp
      (.seq (.while cond body) tail))
      ((2 ^ 63 + K.toNat) * (cost + 1) + tailCost) := by
  intro F state code budget
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  rcases hinit state with hno | ⟨w0, hev⟩
  · rw [evalHOLFinite_eq_toExact] at hno
    rw [hno]
    simp
  · rw [evalHOLFinite_eq_toExact] at hev
    rw [hev]
    simp only [shapeOfHOLExact, shapeEqHOL, if_true]
    let s0 := setVarHOLFinite counter (.val (.word w0)) state
    have hs0_code : s0.code = originalRuntimeCode := code
    have hs0_c : s0.locals.lookup counter = some (.val (.word w0)) := by
      simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hrank0 : (w0.toNat < 2 ^ 63 ∧ K.toNat - w0.toNat ≤ 2 ^ 63 + K.toNat) ∨
        (2 ^ 63 ≤ w0.toNat ∧ 2 ^ 64 - w0.toNat + K.toNat ≤ 2 ^ 63 + K.toNat) := by
      by_cases hsm : w0.toNat < 2 ^ 63
      · exact Or.inl ⟨hsm, by omega⟩
      · exact Or.inr ⟨by omega, by omega⟩
    have hloop := signedStepWhile_run counter cond K hK_pos hstop hbody
      (2 ^ 63 + K.toNat) s0 hs0_code w0 hs0_c hrank0
      (by change (2 ^ 63 + K.toNat) * (cost + 1) ≤ state.clock; omega)
    have meta' := PanRunBounded.evaluateHOLFiniteState_metadata s0 (.while cond body)
    rw [evaluateHOLFiniteState_seq_line780]
    rcases lr : evaluateHOLFiniteState s0 (.while cond body) with ⟨res, mid⟩
    rw [lr] at hloop meta'
    dsimp only at hloop meta'
    obtain ⟨sp, kp, sf⟩ := hloop
    change state.clock ≤ mid.clock + (2 ^ 63 + K.toNat) * (cost + 1) at sp
    change mid.clock ≤ state.clock at kp
    cases res with
    | none =>
      dsimp only
      obtain ⟨t1, t2, t3⟩ := htail mid (meta'.1.trans code) (by omega)
      exact ⟨by omega, by omega, t3⟩
    | some r =>
      dsimp only
      exact ⟨by omega, kp, sf⟩

def nodeRlpFillLoopStep : ProgHOL 64 :=
  match sourceFnBody Guest.Software.guestFn__node_rlp_fill with
  | .decCall _ _ _ _ (.decCall _ _ _ _ (.seq _ (.seq _ (.seq _ (.seq _ (.dec _ _ _ (.seq (.while _ step) _))))))) => step
  | p => p

theorem progBounded_node_rlp_fill_step (K_reb K_keccak : Nat)
    (h_reb : FunBounded (ofString "rlp_encode_bytes") K_reb)
    (h_keccak : FunBounded (ofString "keccak256") K_keccak) :
    ProgBounded nodeRlpFillLoopStep (2 ^ 65 + 2 ^ 63 + 2 * K_reb + 16 * K_keccak + 818) := by
  dsimp only [nodeRlpFillLoopStep, sourceFnBody, sourceFunctionEntry,
    Guest.Software.guestFn__node_rlp_fill,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  have h16_stop : ∀ {F : Type} (w : BitVec 64) (s : PanSemStateFiniteExact 64 F),
      w.toNat < 2 ^ 63 → (BitVec.ofNat 64 16).toNat ≤ w.toNat →
      s.locals.lookup (ofString "i") = some (.val (.word w)) →
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        (.op .and
          [.cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "i")) (.const 16)),
           .cmp .notEqual (.const 0) (.cmp .equal (.var .local (ofString "found")) (.const 0))]) = none ∨
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        (.op .and
          [.cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "i")) (.const 16)),
           .cmp .notEqual (.const 0) (.cmp .equal (.var .local (ofString "found")) (.const 0))]) = some (.val (.word 0)) := by
    intro F w s hsm hge hc
    rw [evalHOLFinite_eq_toExact]
    have hless_false : Compiler.Encoders.Asm.holAsmSignedLess w (BitVec.ofNat 64 16) = false := by
      rw [holAsmSignedLess_small w (BitVec.ofNat 64 16) hsm (by decide)]
      have h16 : (BitVec.ofNat 64 16).toNat = 16 := rfl
      simp [h16]; omega
    cases hfound : s.locals.lookup (ofString "found") with
    | none =>
      exact Or.inl (by simp [evalHOLExact, evalListHOLExact, hc, hfound,
        Compiler.Encoders.Asm.wordCmpHOL, hless_false])
    | some fv =>
      cases fv with
      | rStruct _ =>
        exact Or.inl (by simp [evalHOLExact, evalListHOLExact, hc, hfound,
          Compiler.Encoders.Asm.wordCmpHOL, hless_false])
      | nStruct _ _ =>
        exact Or.inl (by simp [evalHOLExact, evalListHOLExact, hc, hfound,
          Compiler.Encoders.Asm.wordCmpHOL, hless_false])
      | val fwl =>
        cases fwl with
        | word fw =>
          refine Or.inr ?_
          by_cases hfw : fw = 0#64 <;>
            simp [evalHOLExact, evalListHOLExact, hc, hfound, hfw,
              Compiler.Encoders.Asm.wordCmpHOL, hless_false,
              wordOpHOL, wordOp, valueIsWord, valueWord] <;>
            rfl
  exact @ProgBounded.weaken _ _ (2 ^ 65 + 2 ^ 63 + 2 * K_reb + 16 * K_keccak + 818)
    (ProgBounded.dec _ _ _
      (ProgBounded.dec _ _ _
        (ProgBounded.dec _ _ _
          (ProgBounded.dec _ _ _
            (ProgBounded.seq
              (ProgBounded.iteMax _
                (ProgBounded.iteMax _
                  (ProgBounded.seq (ProgBounded.straight _ rfl)
                    (ProgBounded.seq (ProgBounded.straight _ rfl)
                      (ProgBounded.call funBounded_node_needs_rlp (some (.local, ofString "found")) _)))
                  (ProgBounded.straight _ rfl))
                (ProgBounded.iteMax _
                  (progBounded_signedStep_anyInit (ofString "i") _ (BitVec.ofNat 64 16) (by decide) h16_stop
                    ((ExpHOL.op .add [.var .local (ofString "top"), .const (BitVec.ofNat 64 16)]).load .one)
                    (cost := 1)
                    (countedStep_seq_straight _ rfl rfl rfl
                      (countedStep_tail _ countedStep_incr
                        (ProgBounded.call funBounded_node_needs_rlp (some (.local, ofString "found")) _)
                        rfl rfl))
                    (ProgBounded.straight _ rfl)
                    (fun s => by
                      cases hev : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
                          ((ExpHOL.op .add [.var .local (ofString "top"), .const (BitVec.ofNat 64 16)]).load .one) with
                      | none => exact Or.inl rfl
                      | some iv =>
                        cases iv with
                        | rStruct l =>
                          exfalso
                          rw [evalHOLFinite_eq_toExact] at hev
                          simp only [evalHOLExact] at hev
                          split at hev <;> simp_all [memLoadHOLExact]
                          repeat' first | split at hev | simp_all
                        | nStruct _ _ =>
                          exfalso
                          rw [evalHOLFinite_eq_toExact] at hev
                          simp only [evalHOLExact] at hev
                          split at hev <;> simp_all [memLoadHOLExact]
                          repeat' first | split at hev | simp_all
                        | val iwl =>
                          cases iwl with
                          | word w0 => exact Or.inr ⟨w0, rfl⟩))
                  (ProgBounded.straight _ rfl)))
              (ProgBounded.iteMax _
                (ProgBounded.decCall funBounded_scratch_alloc _ _ _
                  (ProgBounded.seq (ProgBounded.straight _ rfl)
                    (ProgBounded.seq (ProgBounded.straight _ rfl)
                      (ProgBounded.seq (ProgBounded.straight _ rfl)
                        (ProgBounded.seq
                          (ProgBounded.call funBounded_node_rlp_begin none _)
                          (ProgBounded.straight _ rfl))))))
                (ProgBounded.seq
                  (ProgBounded.call (funBounded_node_rlp_finish K_reb K_keccak h_reb h_keccak) none _)
                  (ProgBounded.straight _ rfl))))))))
    (by
      have h16 : (BitVec.ofNat 64 16).toNat = 16 := rfl
      rw [h16]
      omega)

theorem funBounded_node_rlp (K_fill : Nat)
    (h_fill : FunBounded (ofString "_node_rlp_fill") K_fill) :
    FunBounded (ofString "node_rlp") (K_fill + 2) := by
  refine funBounded_of_guestAst 285 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_node_rlp (K_fill + 2) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_node_rlp,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.dec _ _ _
      (ProgBounded.seq
        (ProgBounded.iteMax _ (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl))
        (ProgBounded.seq
          (ProgBounded.iteMax _
            (ProgBounded.call funBounded_mpt_fail none _)
            (ProgBounded.straight _ rfl))
          (ProgBounded.seq
            (ProgBounded.call h_fill none _)
            (ProgBounded.straight _ rfl)))))
    (by omega)

theorem funBounded_node_hash (K_fill K_keccak : Nat)
    (h_fill : FunBounded (ofString "_node_rlp_fill") K_fill)
    (h_keccak : FunBounded (ofString "keccak256") K_keccak) :
    FunBounded (ofString "node_hash") (K_fill + K_keccak + 6) := by
  refine funBounded_of_guestAst 290 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_node_hash (K_fill + K_keccak + 6) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_node_hash,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.dec _ _ _
      (ProgBounded.seq
        (ProgBounded.iteMax _ (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl))
        (ProgBounded.decCall (funBounded_node_rlp K_fill h_fill) _ _ _
          (ProgBounded.decCall funBounded_alloc _ _ _
            (ProgBounded.seq
              (ProgBounded.call h_keccak none _)
              (ProgBounded.straight _ rfl))))))
    (by omega)

theorem funBounded_mpt_root (K_fill K_keccak : Nat)
    (h_fill : FunBounded (ofString "_node_rlp_fill") K_fill)
    (h_keccak : FunBounded (ofString "keccak256") K_keccak) :
    FunBounded (ofString "mpt_root") (K_fill + K_keccak + 31) := by
  refine funBounded_of_guestAst 291 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_mpt_root (K_fill + K_keccak + 31) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_mpt_root,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  have hmc32_small : (BitVec.ofNat 64 32).toNat + 32 < 2 ^ 64 := by decide
  exact @ProgBounded.weaken _ _ (K_fill + K_keccak + 31)
    (ProgBounded.dec _ _ _
      (ProgBounded.seq
        (ProgBounded.iteMax _
          (ProgBounded.seq
            (progBounded_memcpy_const none (.var .local (ofString "out"))
              (.var .global (ofString "empty_trie_root")) (BitVec.ofNat 64 32) hmc32_small)
            (ProgBounded.straight _ rfl))
          (ProgBounded.straight _ rfl))
        (ProgBounded.decCall (funBounded_node_hash K_fill K_keccak h_fill h_keccak) _ _ _
          (ProgBounded.seq
            (progBounded_memcpy_const none (.var .local (ofString "out"))
              (.var .local (ofString "h")) (BitVec.ofNat 64 32) hmc32_small)
            (ProgBounded.straight _ rfl)))))
    (by
      have h32 : (BitVec.ofNat 64 32).toNat / 8 = 4 := rfl
      rw [h32]
      omega)

theorem funBounded_build_mpt_indexed (K_set K_fill K_keccak : Nat)
    (h_set : FunBounded (ofString "mpt_set") K_set)
    (h_fill : FunBounded (ofString "_node_rlp_fill") K_fill)
    (h_keccak : FunBounded (ofString "keccak256") K_keccak) :
    FunBounded (ofString "build_mpt_indexed")
      ((2 ^ 64 - 1) * (2 ^ 64 + K_set + 12) + K_fill + K_keccak + 37) := by
  refine funBounded_of_guestAst 292 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_build_mpt_indexed
    ((2 ^ 64 - 1) * (2 ^ 64 + K_set + 12) + K_fill + K_keccak + 37) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_build_mpt_indexed,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact @ProgBounded.weaken _ _
    ((2 ^ 64 - 1) * (2 ^ 64 + K_set + 12) + K_fill + K_keccak + 37)
    (ProgBounded.decCall funBounded_heap_mark _ _ _
      (ProgBounded.decCall funBounded_mpt_new _ _ _
        (progBounded_varCountedDec_local (ofString "i") (ofString "n") .lower (Or.inr rfl)
          (cost := 2 ^ 64 + 9 + 1 + (K_set + 1 + 0))
          (countedStep_decCall (counter := ofString "i") (ofString "klen") .one (ofString "rlp_encode_word") _ (by decide) funBounded_rlp_encode_word
            (countedStep_seq _ (ProgBounded.call h_set none _) rfl rfl countedStep_incr))
          rfl
          (ProgBounded.seq
            (ProgBounded.call (funBounded_mpt_root K_fill K_keccak h_fill h_keccak) none _)
            (ProgBounded.seq
              (ProgBounded.call funBounded_heap_release none _)
              (ProgBounded.straight _ rfl))))))
    (by omega)

theorem funBounded_decode_account_from_leaf (K_lc : Nat)
    (h_lc : FunBounded (ofString "rlp_list_count") K_lc) :
    FunBounded (ofString "decode_account_from_leaf")
      (6 * K_lc + 5 * 2 ^ 64 + 60 + (2 ^ 64 - 1) * (2 ^ 64 + 12)) := by
  refine funBounded_of_guestAst 293 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_decode_account_from_leaf
    (6 * K_lc + 5 * 2 ^ 64 + 60 + (2 ^ 64 - 1) * (2 ^ 64 + 12)) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_decode_account_from_leaf,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  have hitem := funBounded_rlp_item K_lc h_lc
  have hmz32_small : (BitVec.ofNat 64 32).toNat + 32 < 2 ^ 64 := by decide
  let p_assign : ProgHOL 64 := .assign .local (ofString "i") (.const (BitVec.ofNat 64 0))
  let p_body : ProgHOL 64 :=
    .dec (ofString "pos") .one
      (.op .sub [.op .sub [.rfield 2 (.var .local (ofString "f1")), .const (BitVec.ofNat 64 1)], .var .local (ofString "i")])
      (.dec (ofString "lp") .one
        (.op .add [.var .local (ofString "acct_out"), .const (BitVec.ofNat 64 8),
          .panop .mul [(ExpHOL.var .local (ofString "pos")).shift .lsr (.const (BitVec.ofNat 64 3)), .const (BitVec.ofNat 64 8)]])
        (.seq
          (.store (.var .local (ofString "lp"))
            (.op .or [(ExpHOL.var .local (ofString "lp")).load .one,
              ((ExpHOL.op .add [.rfield 1 (.var .local (ofString "f1")), .var .local (ofString "i")]).loadByte).shift .lsl
                (.panop .mul [.op .and [.var .local (ofString "pos"), .const (BitVec.ofNat 64 7)], .const (BitVec.ofNat 64 8)])]))
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)]))))
  let p_tail : ProgHOL 64 :=
    .seq
      (.ite (.cmp .equal (.rfield 2 (.var .local (ofString "f2"))) (.const (BitVec.ofNat 64 0)))
        (.store (.op .add [.var .local (ofString "acct_out"), .const (BitVec.ofNat 64 40)])
          (.var .global (ofString "empty_trie_root")))
        (.seq
          (.ite (.cmp .notEqual (.rfield 2 (.var .local (ofString "f2"))) (.const (BitVec.ofNat 64 32)))
            (.call (some (none, none)) (ofString "mpt_fail") [.const (BitVec.ofNat 64 23)])
            .skip)
          (.store (.op .add [.var .local (ofString "acct_out"), .const (BitVec.ofNat 64 40)])
            (.rfield 1 (.var .local (ofString "f2"))))))
      (.seq
        (.ite (.cmp .equal (.rfield 2 (.var .local (ofString "f3"))) (.const (BitVec.ofNat 64 0)))
          (.store (.op .add [.var .local (ofString "acct_out"), .const (BitVec.ofNat 64 48)])
            (.var .global (ofString "empty_code_hash")))
          (.seq
            (.ite (.cmp .notEqual (.rfield 2 (.var .local (ofString "f3"))) (.const (BitVec.ofNat 64 32)))
              (.call (some (none, none)) (ofString "mpt_fail") [.const (BitVec.ofNat 64 24)])
              .skip)
            (.store (.op .add [.var .local (ofString "acct_out"), .const (BitVec.ofNat 64 48)])
              (.rfield 1 (.var .local (ofString "f3"))))))
        (.return (.const (BitVec.ofNat 64 0))))
  have hloop_f1 : ProgBounded
      (.seq p_assign (.seq (.while (.cmp .lower (.var .local (ofString "i")) (.rfield 2 (.var .local (ofString "f1")))) p_body) p_tail))
      ((2 ^ 64 - 1) * (0 + 1) + 2) := by
    intro F s hs_code hs_clk
    have htail_bnd : ProgBounded p_tail 2 := @ProgBounded.weaken _ _ 2
      (ProgBounded.seq
        (ProgBounded.iteMax _
          (ProgBounded.straight _ rfl)
          (ProgBounded.seq
            (ProgBounded.iteMax _
              (ProgBounded.call funBounded_mpt_fail none _)
              (ProgBounded.straight _ rfl))
            (ProgBounded.straight _ rfl)))
        (ProgBounded.seq
          (ProgBounded.iteMax _
            (ProgBounded.straight _ rfl)
            (ProgBounded.seq
              (ProgBounded.iteMax _
                (ProgBounded.call funBounded_mpt_fail none _)
                (ProgBounded.straight _ rfl))
              (ProgBounded.straight _ rfl)))
          (ProgBounded.straight _ rfl)))
      (by decide)
    have hdec_bnd : ProgBounded
        (.dec (ofString "i") .one (.const 0)
          (.seq (.while (.cmp .lower (.var .local (ofString "i")) (.rfield 2 (.var .local (ofString "f1")))) p_body) p_tail))
        ((2 ^ 64 - 1) * (0 + 1) + 2) :=
      progBounded_varCountedDec_rfield (ofString "i") (ofString "f1") 2 .lower (Or.inr rfl)
        (cost := 0)
        (countedStep_dec (counter := ofString "i") (ofString "pos") .one _ (by decide)
          (countedStep_dec (counter := ofString "i") (ofString "lp") .one _ (by decide)
            (countedStep_seq_straight _ rfl rfl rfl countedStep_incr)))
        rfl htail_bnd
    change RunBounded s (.seq p_assign (.seq (.while (.cmp .lower (.var .local (ofString "i")) (.rfield 2 (.var .local (ofString "f1")))) p_body) p_tail))
      ((2 ^ 64 - 1) * (0 + 1) + 2)
    unfold RunBounded
    rw [evaluateHOLFiniteState_seq_line780]
    cases hi : s.locals.lookup (ofString "i") with
    | none =>
      simp [p_assign, evaluateHOLFiniteState_assign, evalHOLExact, isValidValueHOLExact, lookupKvarHOLExact, hi]
    | some iv =>
      cases iv with
      | rStruct _ =>
        simp [p_assign, evaluateHOLFiniteState_assign, evalHOLExact, lookupKvarHOLExact, hi,
          isValidValueHOLExact, shapeOfHOLExact, shapeEqHOL]
      | nStruct _ _ =>
        simp [p_assign, evaluateHOLFiniteState_assign, evalHOLExact, lookupKvarHOLExact, hi,
          isValidValueHOLExact, shapeOfHOLExact, shapeEqHOL]
      | val iwl =>
        cases iwl with
        | word iw =>
          have hassign : evaluateHOLFiniteState s p_assign =
              (none, setVarHOLFinite (ofString "i") (.val (.word 0)) s) := by
            simp [p_assign, evaluateHOLFiniteState_assign, evalHOLExact, lookupKvarHOLExact, hi,
              isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
          rw [hassign]
          dsimp only
          have hrun := hdec_bnd s hs_code hs_clk
          unfold RunBounded at hrun
          rw [evaluateHOLFiniteState_dec_total] at hrun
          simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true] at hrun
          rcases lr : evaluateHOLFiniteState (setVarHOLFinite (ofString "i") (.val (.word 0)) s)
            (.seq (.while (.cmp .lower (.var .local (ofString "i")) (.rfield 2 (.var .local (ofString "f1")))) p_body) p_tail) with ⟨res, post⟩
          rw [lr] at hrun
          dsimp only at hrun ⊢
          exact hrun
  exact @ProgBounded.weaken _ _
    (6 * K_lc + 5 * 2 ^ 64 + 60 + (2 ^ 64 - 1) * (2 ^ 64 + 12))
    (ProgBounded.dec _ _ _
      (ProgBounded.dec _ _ _
        (ProgBounded.seq
          (ProgBounded.handledCall (funBounded_rlp_decode_fully K_lc h_lc)
            _ _ (some (.local, ofString "it")) _
            (ProgBounded.call funBounded_mpt_fail none _))
          (ProgBounded.seq
            (ProgBounded.iteMax _
              (ProgBounded.call funBounded_mpt_fail none _)
              (ProgBounded.straight _ rfl))
            (ProgBounded.decCall (funBounded_rlp_list_to_slices K_lc h_lc) _ _ _
              (ProgBounded.seq
                (ProgBounded.iteMax _
                  (ProgBounded.call funBounded_mpt_fail none _)
                  (ProgBounded.straight _ rfl))
                (ProgBounded.dec _ _ _
                  (ProgBounded.decCall hitem _ _ _
                    (ProgBounded.decCall hitem _ _ _
                      (ProgBounded.decCall hitem _ _ _
                        (ProgBounded.decCall hitem _ _ _
                          (ProgBounded.seq
                            (ProgBounded.iteMax _
                              (ProgBounded.call funBounded_mpt_fail none _)
                              (ProgBounded.straight _ rfl))
                            (ProgBounded.seq
                              (ProgBounded.iteMax _
                                (ProgBounded.call funBounded_mpt_fail none _)
                                (ProgBounded.straight _ rfl))
                              (ProgBounded.dec _ _ _
                                (progBounded_varCountedDec_rfield (ofString "i") (ofString "f0") 2
                                  .lower (Or.inr rfl)
                                  (cost := 0)
                                  (countedStep_seq_straight _ rfl rfl rfl countedStep_incr)
                                  rfl
                                  (ProgBounded.seq
                                    (ProgBounded.straight _ rfl)
                                    (ProgBounded.seq
                                      (ProgBounded.iteMax _
                                        (ProgBounded.call funBounded_mpt_fail none _)
                                        (ProgBounded.straight _ rfl))
                                      (ProgBounded.seq
                                        (progBounded_memzero_const none
                                          (.op .add [.var .local (ofString "acct_out"), .const (BitVec.ofNat 64 8)])
                                          (BitVec.ofNat 64 32) hmz32_small)
                                        hloop_f1))))))))))))))))))
    (by
      have h32 : (BitVec.ofNat 64 32).toNat / 8 = 4 := rfl
      rw [h32]
      omega)

theorem runBounded_rlp_encode_bytes_decCall_state {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (shape : ShapeHOL) (dst src sizeExp : ExpHOL 64)
    (K : BitVec 64) {continuation : ProgHOL 64} {tailCost : Nat}
    (hcode : state.code = originalRuntimeCode)
    (hsmall : K.toNat + 32 < 2 ^ 64)
    (heval : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) sizeExp = some (.val (.word K)))
    (hrest : ProgBounded continuation tailCost)
    (hbudget : K.toNat / 8 + 2 ^ 64 + 19 + tailCost ≤ state.clock) :
    RunBounded state (.decCall name shape (ofString "rlp_encode_bytes") [dst, src, sizeExp] continuation)
      (K.toNat / 8 + 2 ^ 64 + 19 + tailCost) := by
  cases hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [dst, src, sizeExp] with
  | none =>
    unfold RunBounded
    rw [evaluateHOLFiniteState_decCall_args_none state name shape (ofString "rlp_encode_bytes") [dst, src, sizeExp] continuation hargs]
    simp
  | some vs =>
    obtain ⟨v1, v2, rfl⟩ := evalListHOLFinite_three_word3_local state dst src sizeExp K hargs heval
    have h := RunBounded.decCall (state := state) (name := name) (shape := shape) (continuation := continuation)
      (bodyCost := K.toNat / 8 + 2 ^ 64 + 18) (tailCost := tailCost) hargs (by omega)
      (fun body locals rs hfound => by
        rw [hcode] at hfound
        obtain ⟨rfl, hn⟩ := three_arg_lookup_last originalRuntimeCode.lookup
          (ofString "rlp_encode_bytes") (ofString "dst") (ofString "src") (ofString "n")
          (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes)
          (by decide) (by decide) (by decide) lookup_rlp_encode_bytes hfound
        have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state locals)
          (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes)
        refine ⟨runBounded_rlp_encode_bytes_body (callEntryStateHOLFinite state locals) K hsmall hcode hn
          (by change K.toNat / 8 + 2 ^ 64 + 18 ≤ state.clock - 1; omega), ?_⟩
        intro value post hran hpost_clk
        rw [hran] at hmeta
        exact hrest _ (hmeta.1.trans hcode) hpost_clk)
    exact h.weaken (by omega)

theorem encode_account_z_loop {F : Type}
    (s0 : PanSemStateFiniteExact 64 F)
    (hs0_code : s0.code = originalRuntimeCode)
    (hs0_z : s0.locals.lookup (ofString "z") = some (.val (.word 0)))
    (hclk : 32 ≤ s0.clock) :
    let loopProg : ProgHOL 64 :=
      .while (.cmp .lower (.var .local (ofString "z")) (.const 32))
        (.seq
          (.ite (.cmp .notEqual ((ExpHOL.op .add [.var .global (ofString "mpt_hash_scratch"), .var .local (ofString "z")]).loadByte) (.const 0))
            .break
            .skip)
          (.assign .local (ofString "z") (.op .add [.var .local (ofString "z"), .const 1])))
    s0.clock ≤ (evaluateHOLFiniteState s0 loopProg).2.clock + 32 ∧
      (evaluateHOLFiniteState s0 loopProg).2.clock ≤ s0.clock ∧
      (evaluateHOLFiniteState s0 loopProg).1 ≠ some .timeOut ∧
      ((evaluateHOLFiniteState s0 loopProg).1 = none →
        (∃ zw : BitVec 64,
          (evaluateHOLFiniteState s0 loopProg).2.locals.lookup (ofString "z") = some (.val (.word zw)) ∧
          zw.toNat ≤ 32) ∧
        (evaluateHOLFiniteState s0 loopProg).2.code = originalRuntimeCode) := by
  let condZ : ExpHOL 64 := .cmp .lower (.var .local (ofString "z")) (.const 32)
  let bodyZ : ProgHOL 64 :=
    .seq
      (.ite (.cmp .notEqual ((ExpHOL.op .add [.var .global (ofString "mpt_hash_scratch"), .var .local (ofString "z")]).loadByte) (.const 0))
        .break
        .skip)
      (.assign .local (ofString "z") (.op .add [.var .local (ofString "z"), .const 1]))
  let RankZ : ∀ {G : Type}, PanSemStateFiniteExact 64 G → Nat → Prop :=
    fun s r => ∃ zw : BitVec 64,
      s.locals.lookup (ofString "z") = some (.val (.word zw)) ∧
      zw.toNat ≤ 32 ∧ 32 - zw.toNat = r
  have hexitZ : ∀ {G : Type} (s : PanSemStateFiniteExact 64 G), RankZ s 0 → ∀ w : BitVec 64,
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) condZ = some (.val (.word w)) → w = 0 := by
    intro G s ⟨zw, hzw, hle, hr0⟩ w hev
    have hzw32 : zw = 32 := BitVec.eq_of_toNat_eq (by have h32 : (32 : BitVec 64).toNat = 32 := rfl; omega)
    subst hzw32
    rw [evalHOLFinite_eq_toExact] at hev
    simp [condZ, evalHOLExact, hzw, Compiler.Encoders.Asm.wordCmpHOL] at hev
    exact hev.symm
  have hstepZ : ∀ {G : Type} (s : PanSemStateFiniteExact 64 G) (n : Nat) (w : BitVec 64),
      s.code = originalRuntimeCode → RankZ s (n + 1) →
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) condZ = some (.val (.word w)) →
      w ≠ 0 → 0 + 1 ≤ s.clock →
      s.clock - 1 ≤ (evaluateHOLFiniteState (decClockHOLFinite s) bodyZ).2.clock + 0 ∧
        (evaluateHOLFiniteState (decClockHOLFinite s) bodyZ).2.clock ≤ s.clock - 1 ∧
        (evaluateHOLFiniteState (decClockHOLFinite s) bodyZ).1 ≠ some .timeOut ∧
        ((evaluateHOLFiniteState (decClockHOLFinite s) bodyZ).1 = none ∨
            (evaluateHOLFiniteState (decClockHOLFinite s) bodyZ).1 = some .continue →
          ∃ m, m ≤ n ∧ RankZ (evaluateHOLFiniteState (decClockHOLFinite s) bodyZ).2 m ∧
            (evaluateHOLFiniteState (decClockHOLFinite s) bodyZ).2.code = s.code) ∧
        ((evaluateHOLFiniteState (decClockHOLFinite s) bodyZ).1 = some .break → True ∧
          ∃ m, RankZ (evaluateHOLFiniteState (decClockHOLFinite s) bodyZ).2 m ∧
            (evaluateHOLFiniteState (decClockHOLFinite s) bodyZ).2.code = s.code) := by
    intro G s n w hsc ⟨zw, hzw, hle, hrk⟩ _ _ _
    let ds := decClockHOLFinite s
    have hds_zw : ds.locals.lookup (ofString "z") = some (.val (.word zw)) := hzw
    have hlt32 : zw.toNat < 32 := by omega
    have hzw1_nat : (zw + 1).toNat = zw.toNat + 1 :=
      BitVec.toNat_add_of_lt (by change zw.toNat + 1 < 2 ^ 64; omega)
    dsimp only [bodyZ]
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
    split
    · split
      · rw [evaluateHOLFiniteState_skip]
        dsimp only
        have hassign : evaluateHOLFiniteState ds
            (.assign .local (ofString "z") (.op .add [.var .local (ofString "z"), .const 1])) =
            (none, setVarHOLFinite (ofString "z") (.val (.word (zw + 1))) ds) := by
          simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hds_zw,
            wordOpHOL, wordOp, valueIsWord, valueWord, lookupKvarHOLExact,
            isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
        rw [hassign]
        refine ⟨by simp [ds, decClockHOLFinite, setVarHOLFinite],
          by simp [ds, decClockHOLFinite, setVarHOLFinite], by simp, ?_, by simp⟩
        intro _
        refine ⟨n, le_refl n, ⟨zw + 1, ?_, by rw [hzw1_nat]; omega, by rw [hzw1_nat]; omega⟩, rfl⟩
        simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      · rw [evaluateHOLFiniteState_break]
        dsimp only
        refine ⟨by simp [ds, decClockHOLFinite], by simp [ds, decClockHOLFinite], by simp, by simp, ?_⟩
        intro _
        exact ⟨trivial, ⟨n + 1, ⟨zw, hds_zw, hle, hrk⟩, rfl⟩⟩
    · simp [ds, decClockHOLFinite]
  have h0_le32 : (0 : BitVec 64).toNat ≤ 32 := by decide
  have hraw := rankedWhile_run condZ bodyZ 0 RankZ True hexitZ hstepZ 32 s0 hs0_code
    ⟨0, hs0_z, h0_le32, rfl⟩ (by omega)
  dsimp only
  refine ⟨by have := hraw.1; omega, hraw.2.1, hraw.2.2.1, ?_⟩
  intro hnone
  obtain ⟨m, ⟨zw, hzw, hle, _⟩, hcode', _⟩ := hraw.2.2.2 hnone
  exact ⟨⟨zw, hzw, hle⟩, hcode'.trans hs0_code⟩

theorem progBounded_encode_account_rest_tail :
    ProgBounded
      (.seq
        (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"), .var .local (ofString "wb")]))
        (.decCall (ofString "wsl") .one (ofString "rlp_encode_bytes")
          [.op .add [.var .local (ofString "out"), .var .local (ofString "off")],
           .var .local (ofString "storage_root"),
           .const 32]
          (.seq
            (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"), .var .local (ofString "wsl")]))
            (.decCall (ofString "wc") .one (ofString "rlp_encode_bytes")
              [.op .add [.var .local (ofString "out"), .var .local (ofString "off")],
               .var .local (ofString "code_hash"),
               .const 32]
              (.seq
                (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"), .var .local (ofString "wc")]))
                (.seq
                  (.storeByte (.var .local (ofString "out")) (.const 248))
                  (.seq
                    (.storeByte (.op .add [.var .local (ofString "out"), .const 1])
                      (.op .sub [.var .local (ofString "off"), .const 2]))
                    (.return (.var .local (ofString "off"))))))))))
      (2 * 2 ^ 64 + 46) := by
  have h32 : (BitVec.ofNat 64 32).toNat = 32 := rfl
  have h32_small : (BitVec.ofNat 64 32).toNat + 32 < 2 ^ 64 := by rw [h32]; omega
  exact @ProgBounded.weaken _ _ (2 * 2 ^ 64 + 46)
    (ProgBounded.seq (ProgBounded.straight _ rfl)
      (progBounded_rlp_encode_bytes_decCall_const (ofString "wsl") .one _ _ 32 h32_small
        (ProgBounded.seq (ProgBounded.straight _ rfl)
          (progBounded_rlp_encode_bytes_decCall_const (ofString "wc") .one _ _ 32 h32_small
            (ProgBounded.straight _ rfl)))))
    (by
      have h32' : (32 : BitVec 64).toNat = 32 := rfl
      omega)

theorem progBounded_encode_account_z_phase :
    ProgBounded
      (.dec (ofString "z") .one (.const 0)
        (.seq
          (.while (.cmp .lower (.var .local (ofString "z")) (.const 32))
            (.seq
              (.ite (.cmp .notEqual ((ExpHOL.op .add [.var .global (ofString "mpt_hash_scratch"), .var .local (ofString "z")]).loadByte) (.const 0))
                .break
                .skip)
              (.assign .local (ofString "z") (.op .add [.var .local (ofString "z"), .const 1]))))
          (.decCall (ofString "wb") .one (ofString "rlp_encode_bytes")
            [.op .add [.var .local (ofString "out"), .var .local (ofString "off")],
             .op .add [.var .global (ofString "mpt_hash_scratch"), .var .local (ofString "z")],
             .op .sub [.const 32, .var .local (ofString "z")]]
            (.seq
              (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"), .var .local (ofString "wb")]))
              (.decCall (ofString "wsl") .one (ofString "rlp_encode_bytes")
                [.op .add [.var .local (ofString "out"), .var .local (ofString "off")],
                 .var .local (ofString "storage_root"),
                 .const 32]
                (.seq
                  (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"), .var .local (ofString "wsl")]))
                  (.decCall (ofString "wc") .one (ofString "rlp_encode_bytes")
                    [.op .add [.var .local (ofString "out"), .var .local (ofString "off")],
                     .var .local (ofString "code_hash"),
                     .const 32]
                    (.seq
                      (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"), .var .local (ofString "wc")]))
                      (.seq
                        (.storeByte (.var .local (ofString "out")) (.const 248))
                        (.seq
                          (.storeByte (.op .add [.var .local (ofString "out"), .const 1])
                            (.op .sub [.var .local (ofString "off"), .const 2]))
                          (.return (.var .local (ofString "off")))))))))))))
      (3 * 2 ^ 64 + 101) := by
  intro F state hcode hbudget
  apply RunBounded.decConst
  let s0 := setVarHOLFinite (ofString "z") (.val (.word 0)) state
  change RunBounded s0 _ (3 * 2 ^ 64 + 101)
  have hs0_clk : s0.clock = state.clock := rfl
  have hs0_code : s0.code = originalRuntimeCode := hcode
  have hs0_z : s0.locals.lookup (ofString "z") = some (.val (.word 0)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hloop := encode_account_z_loop s0 hs0_code hs0_z (by omega)
  dsimp only at hloop
  unfold RunBounded
  rw [evaluateHOLFiniteState_seq_line780]
  rcases lr : evaluateHOLFiniteState s0
      (.while (.cmp .lower (.var .local (ofString "z")) (.const 32))
        (.seq
          (.ite (.cmp .notEqual ((ExpHOL.op .add [.var .global (ofString "mpt_hash_scratch"), .var .local (ofString "z")]).loadByte) (.const 0))
            .break
            .skip)
          (.assign .local (ofString "z") (.op .add [.var .local (ofString "z"), .const 1])))) with ⟨lres, s1⟩
  rw [lr] at hloop
  dsimp only at hloop ⊢
  obtain ⟨sp, kp, sf, hpost⟩ := hloop
  cases lres with
  | some r =>
    dsimp only
    exact ⟨by omega, kp, sf⟩
  | none =>
    dsimp only
    obtain ⟨⟨zw, hs1_z, hzw_le⟩, hs1_code'⟩ := hpost rfl
    let Krem : BitVec 64 := 32 - zw
    have hkrem_le : Krem.toNat ≤ 32 := by
      have h32 : (32 : BitVec 64).toNat = 32 := rfl
      have hle_bv : zw ≤ (32 : BitVec 64) := by rw [BitVec.le_def, h32]; exact hzw_le
      rw [BitVec.toNat_sub_of_le hle_bv, h32]
      omega
    have hkrem_small : Krem.toNat + 32 < 2 ^ 64 := by omega
    have hsub_eval : evalHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
        (.op .sub [.const 32, .var .local (ofString "z")]) = some (.val (.word Krem)) := by
      rw [evalHOLFinite_eq_toExact]
      simp [evalHOLExact, evalListHOLExact, hs1_z, wordOpHOL, wordOp, valueIsWord, valueWord, Krem]
    have hwb := runBounded_rlp_encode_bytes_decCall_state s1 (ofString "wb") .one
      (.op .add [.var .local (ofString "out"), .var .local (ofString "off")])
      (.op .add [.var .global (ofString "mpt_hash_scratch"), .var .local (ofString "z")])
      (.op .sub [.const 32, .var .local (ofString "z")])
      Krem hs1_code' hkrem_small hsub_eval progBounded_encode_account_rest_tail (by omega)
    obtain ⟨d1, d2, d3⟩ := hwb
    exact ⟨by omega, by omega, d3⟩

theorem funBounded_encode_account : FunBounded (ofString "encode_account") (4 * 2 ^ 64 + 127) := by
  refine funBounded_of_guestAst 294 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_encode_account (4 * 2 ^ 64 + 127) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_encode_account,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact @ProgBounded.weaken _ _ (4 * 2 ^ 64 + 127)
    (ProgBounded.dec _ _ _
      (ProgBounded.decCall funBounded_rlp_encode_word _ _ _
        (ProgBounded.seq (ProgBounded.straight _ rfl)
          (ProgBounded.seq (ProgBounded.call funBounded_st_be64 none _)
            (ProgBounded.seq (ProgBounded.call funBounded_st_be64 none _)
              (ProgBounded.seq (ProgBounded.call funBounded_st_be64 none _)
                (ProgBounded.seq (ProgBounded.call funBounded_st_be64 none _)
                  progBounded_encode_account_z_phase)))))))
    (by decide)

end InitECandidate.Solver.GuestBoundRlpMpt
