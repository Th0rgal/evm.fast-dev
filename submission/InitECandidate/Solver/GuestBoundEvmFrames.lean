import InitECandidate.Solver.PanRunBoundedExt

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace InitECandidate.Solver.GuestBoundEvmFrames

def gasPotential (input : Guest.InputBlob) : Nat := Guest.GasLimit.declaredGasLimit input

theorem gasPotential_le_of_declaredGasLimit (input : Guest.InputBlob)
    (hgas : Guest.GasLimit.declaredGasLimit input ≤ 200000000) : gasPotential input ≤ 200000000 :=
  hgas

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.PanRunBoundedExt

private inductive CountedBodyExt (counter : MlS) (step : BitVec 64) : ProgHOL 64 → Nat → Prop
  | incr : CountedBodyExt counter step (.assign .local counter (.op .add [.var .local counter, .const step])) 0
  | seq (first : ProgHOL 64) {tail : ProgHOL 64} {a b : Nat} (bounded : ProgBounded first a)
      (avoid : avoidsLocal counter first = true) (noCont : noTopContinue first = true)
      (rest : CountedBodyExt counter step tail b) : CountedBodyExt counter step (.seq first tail) (a + b)
  | dec (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL 64) {body : ProgHOL 64} {cost : Nat}
      (distinct : counter ≠ name) (rest : CountedBodyExt counter step body cost) :
      CountedBodyExt counter step (.dec name shape initializer body) cost
  | decCall (name : MlS) (shape : ShapeHOL) (fn : MlS) (args : List (ExpHOL 64))
      {cont : ProgHOL 64} {cost cCost : Nat}
      (hpb : ProgBounded (.decCall name shape fn args cont) cost)
      (distinct : counter ≠ name)
      (rest : CountedBodyExt counter step cont cCost) :
      CountedBodyExt counter step (.decCall name shape fn args cont) cost
  | decWhile (name : MlS) (limExp : ExpHOL 64) {lbody tail : ProgHOL 64} {cost tCost : Nat}
      (hpb : ProgBounded (.dec name .one (.const 0) (.seq (.while (.cmp .less (.var .local name) limExp) lbody) tail)) cost)
      (distinct : counter ≠ name)
      (avoidLoop : avoidsLocal counter lbody = true)
      (rest : CountedBodyExt counter step tail tCost) :
      CountedBodyExt counter step
        (.dec name .one (.const 0) (.seq (.while (.cmp .less (.var .local name) limExp) lbody) tail)) cost

private theorem countedBodyExt_progBounded {counter : MlS} {step : BitVec 64} {body : ProgHOL 64} {cost : Nat}
    (counted : CountedBodyExt counter step body cost) : ProgBounded body cost := by
  induction counted with
  | incr => exact ProgBounded.straight _ rfl
  | seq _ bounded _ _ _ ih => exact ProgBounded.seq bounded ih
  | dec name shape initializer _ _ ih => exact ProgBounded.dec name shape initializer ih
  | decCall _ _ _ _ hpb _ _ => exact hpb
  | decWhile _ _ hpb _ _ _ => exact hpb

private theorem countedBodyExt_noCont_advance {counter : MlS} {step : BitVec 64} {body : ProgHOL 64} {cost : Nat}
    (counted : CountedBodyExt counter step body cost) :
    noTopContinue body = true ∧
    ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      state.locals.lookup counter = some (.val (.word w)) →
      (evaluateHOLFiniteState state body).1 = none →
      (evaluateHOLFiniteState state body).2.locals.lookup counter = some (.val (.word (w + step))) := by
  induction counted with
  | incr =>
    refine ⟨rfl, fun state w atCounter hnone => ?_⟩
    have run : evaluateHOLFiniteState state (.assign .local counter (.op .add [.var .local counter, .const step])) =
        (none, setVarHOLFinite counter (.val (.word (w + step))) state) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, atCounter, wordOpHOL, wordOp, valueIsWord,
        valueWord, lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
    rw [run]
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  | seq first _ avoid noCont _ ih =>
    refine ⟨by simp [noTopContinue, noCont, ih.1], fun state w atCounter hnone => ?_⟩
    have frame := evaluate_avoidsLocal_flowing counter first avoid state
    rw [evaluateHOLFiniteState_seq_line780] at hnone ⊢
    cases firstRun : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [firstRun] at frame hnone
      cases result with
      | none =>
        dsimp only at hnone ⊢
        have kept' := frame (Or.inl rfl)
        exact ih.2 middle w (kept'.trans atCounter) hnone
      | some r => simp at hnone
  | dec name shape initializer distinct _ ih =>
    refine ⟨by simp [noTopContinue, ih.1], fun state w atCounter hnone => ?_⟩
    cases run : evaluateHOLFiniteState state (.dec name shape initializer _) with
    | mk res post =>
      rw [run] at hnone
      dsimp only at hnone
      subst hnone
      obtain ⟨val, inner, bodyRun, hlocals⟩ := PanRunBounded.dec_flowing (Or.inl rfl) run
      have atInner : (setVarHOLFinite name val state).locals.lookup counter = some (.val (.word w)) := by
        simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm distinct, atCounter]
      have hsub := ih.2 (setVarHOLFinite name val state) w atInner (by rw [bodyRun])
      rw [bodyRun] at hsub
      change post.locals.lookup counter = _
      rw [hlocals, PanRunBounded.resVarEq_lookup, if_neg distinct]
      exact hsub
  | decCall name shape fn args _ distinct _ ih =>
    refine ⟨by simp [noTopContinue, ih.1], fun state w atCounter hnone => ?_⟩
    cases run : evaluateHOLFiniteState state (.decCall name shape fn args _) with
    | mk res post =>
      rw [run] at hnone
      dsimp only at hnone
      subst hnone
      obtain ⟨_w, resumed, inner, rl, _, contRun, hlocals⟩ := PanRunBounded.decCall_flowing (Or.inl rfl) run
      have atResumed : resumed.locals.lookup counter = some (.val (.word w)) :=
        (rl counter distinct).trans atCounter
      have hsub := ih.2 resumed w atResumed (by rw [contRun])
      rw [contRun] at hsub
      change post.locals.lookup counter = _
      rw [hlocals, PanRunBounded.resVarEq_lookup, if_neg distinct]
      exact hsub
  | decWhile name limExp _ distinct avoidLoop _ ih =>
    rename_i lbody tail _ _
    refine ⟨by simp [noTopContinue, ih.1], fun state w atCounter hnone => ?_⟩
    cases run : evaluateHOLFiniteState state
        (.dec name .one (.const 0) (.seq (.while (.cmp .less (.var .local name) limExp) lbody) tail)) with
    | mk res post =>
      rw [run] at hnone
      dsimp only at hnone
      subst hnone
      obtain ⟨val, inner, seqRun, hlocals⟩ := PanRunBounded.dec_flowing (Or.inl rfl) run
      have atInner : (setVarHOLFinite name val state).locals.lookup counter = some (.val (.word w)) := by
        simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm distinct, atCounter]
      have frame := evaluate_avoidsLocal_flowing counter
        (.while (.cmp .less (.var .local name) limExp) lbody)
        (by simpa [avoidsLocal] using avoidLoop)
        (setVarHOLFinite name val state)
      rw [evaluateHOLFiniteState_seq_line780] at seqRun
      cases loopRun : evaluateHOLFiniteState (setVarHOLFinite name val state)
          (.while (.cmp .less (.var .local name) limExp) lbody) with
      | mk lres mid =>
        rw [loopRun] at seqRun frame
        cases lres with
        | none =>
          dsimp only at seqRun
          have atMid : mid.locals.lookup counter = some (.val (.word w)) :=
            (frame (Or.inl rfl)).trans atInner
          have hsub := ih.2 mid w atMid (by rw [seqRun])
          rw [seqRun] at hsub
          change post.locals.lookup counter = _
          rw [hlocals, PanRunBounded.resVarEq_lookup, if_neg distinct]
          exact hsub
        | some r => simp at seqRun

private theorem countedBodyExt_run {counter : MlS} {step : BitVec 64} {body : ProgHOL 64} {cost : Nat}
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
  have hb := (countedBodyExt_progBounded counted) state code budget
  have ⟨hnc, hadv⟩ := countedBodyExt_noCont_advance counted
  have hnoCont := evaluate_noTopContinue body hnc state
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata state body
  exact ⟨hb.1, hb.2.1, hb.2.2, hnoCont, fun hnone => ⟨hadv state w atCounter hnone, hmeta.1⟩⟩

def pureLimitBound : ExpHOL 64 → Option (Option MlS × Nat)
  | .const K =>
    if decide (K.toNat < 2 ^ 63) then some (none, K.toNat) else none
  | .var .local lim => some (some lim, 2 ^ 63 - 1)
  | .op .add [.var .local lim, .const _] => some (some lim, 2 ^ 63 - 1)
  | _ => none

private theorem pureLimitBound_spec {limExp : ExpHOL 64} {optLim : Option MlS} {maxB : Nat}
    (h : pureLimitBound limExp = some (optLim, maxB)) :
    maxB < 2 ^ 63 ∧
    (∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (∃ v0, optLim = some v0 ∧ s.locals.lookup v0 = none) ∨
      (∃ v0 ns, optLim = some v0 ∧ s.locals.lookup v0 = some (.rStruct ns)) ∨
      (∃ v0 nm ns, optLim = some v0 ∧ s.locals.lookup v0 = some (.nStruct nm ns)) ∨
      (∃ K : BitVec 64,
        (optLim = none ∨ ∃ v0 w0, optLim = some v0 ∧ s.locals.lookup v0 = some (.val (.word w0)) ∧
          ∀ {F' : Type} (s' : PanSemStateFiniteExact 64 F'),
            s'.locals.lookup v0 = some (.val (.word w0)) →
            evalHOLFinite s' (h := fun a => Classical.propDecidable (s'.memaddrs a)) limExp = some (.val (.word K))) ∧
        evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) limExp = some (.val (.word K)) ∧
        (K.toNat < 2 ^ 63 → K.toNat ≤ maxB))) := by
  cases limExp with
  | const K =>
    simp only [pureLimitBound] at h
    by_cases hk : decide (K.toNat < 2 ^ 63) = true
    · rw [if_pos hk] at h
      cases h
      have hk' := of_decide_eq_true hk
      refine ⟨hk', fun s => Or.inr (Or.inr (Or.inr ⟨K, Or.inl rfl, ?_, fun _ => le_refl _⟩))⟩
      rw [evalHOLFinite_eq_toExact]
      rfl
    · rw [if_neg hk] at h; cases h
  | var vk lim =>
    cases vk with
    | global => simp [pureLimitBound] at h
    | «local» =>
      simp only [pureLimitBound] at h
      cases h
      refine ⟨by decide, fun s => ?_⟩
      rcases hl : s.locals.lookup lim with _ | ⟨⟨w0⟩⟩ | ns | ⟨nm, ns⟩
      · exact Or.inl ⟨lim, rfl, hl⟩
      · refine Or.inr (Or.inr (Or.inr ⟨w0, Or.inr ⟨lim, w0, rfl, hl, fun s' hs' => ?_⟩, ?_, fun hlt => by omega⟩))
        · rw [evalHOLFinite_eq_toExact]; simp [evalHOLExact, hs']
        · rw [evalHOLFinite_eq_toExact]; simp [evalHOLExact, hl]
      · exact Or.inr (Or.inl ⟨lim, ns, rfl, hl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨lim, nm, ns, rfl, hl⟩))
  | op bop es =>
    cases bop with
    | add =>
      rcases es with _ | ⟨e1, _ | ⟨e2, _ | _⟩⟩
      · simp [pureLimitBound] at h
      · simp [pureLimitBound] at h
      · cases e1 with
        | var vk lim =>
          cases vk with
          | global => simp [pureLimitBound] at h
          | «local» =>
            cases e2 with
            | const c =>
              simp only [pureLimitBound] at h
              cases h
              refine ⟨by decide, fun s => ?_⟩
              rcases hl : s.locals.lookup lim with _ | ⟨⟨w0⟩⟩ | ns | ⟨nm, ns⟩
              · exact Or.inl ⟨lim, rfl, hl⟩
              · refine Or.inr (Or.inr (Or.inr ⟨w0 + c, Or.inr ⟨lim, w0, rfl, hl, fun s' hs' => ?_⟩, ?_, fun hlt => by omega⟩))
                · rw [evalHOLFinite_eq_toExact]
                  simp [evalHOLExact, evalListHOLExact, hs', wordOpHOL, wordOp, valueIsWord, valueWord]
                · rw [evalHOLFinite_eq_toExact]
                  simp [evalHOLExact, evalListHOLExact, hl, wordOpHOL, wordOp, valueIsWord, valueWord]
              · exact Or.inr (Or.inl ⟨lim, ns, rfl, hl⟩)
              · exact Or.inr (Or.inr (Or.inl ⟨lim, nm, ns, rfl, hl⟩))
            | _ => simp [pureLimitBound] at h
        | _ => simp [pureLimitBound] at h
      · simp [pureLimitBound] at h
    | _ => simp [pureLimitBound] at h
  | _ => simp [pureLimitBound] at h

private theorem pureLimitBound_none_or_nonword {limExp : ExpHOL 64} {v0 : MlS}
    {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hlim : pureLimitBound limExp = some (some v0, 2 ^ 63 - 1))
    (hbad : s.locals.lookup v0 = none ∨ (∃ ns, s.locals.lookup v0 = some (.rStruct ns)) ∨
      (∃ nm ns, s.locals.lookup v0 = some (.nStruct nm ns))) :
    evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) limExp = none ∨
    (∃ ns, evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) limExp = some (.rStruct ns)) ∨
    (∃ nm ns, evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) limExp = some (.nStruct nm ns)) := by
  cases limExp with
  | const K => simp [pureLimitBound] at hlim; split at hlim <;> simp at hlim
  | var vk lim =>
    cases vk <;> simp [pureLimitBound] at hlim
    obtain rfl := hlim
    rw [evalHOLFinite_eq_toExact]
    rcases hbad with hn | ⟨ns, hr⟩ | ⟨nm, ns, hns⟩
    · left; simp [evalHOLExact, hn]
    · right; left; exact ⟨ns, by simp [evalHOLExact, hr]⟩
    · right; right; exact ⟨nm, ns, by simp [evalHOLExact, hns]⟩
  | op bop es =>
    cases bop with
    | add =>
      rcases es with _ | ⟨e1, _ | ⟨e2, _ | _⟩⟩ <;> try (simp [pureLimitBound] at hlim)
      cases e1 with
      | var vk lim =>
        cases vk <;> cases e2 <;> simp [pureLimitBound] at hlim
        obtain rfl := hlim
        left
        rw [evalHOLFinite_eq_toExact]
        rcases hbad with hn | ⟨ns, hr⟩ | ⟨nm, ns, hns⟩
        · simp [evalHOLExact, evalListHOLExact, hn]
        · simp [evalHOLExact, evalListHOLExact, hr, wordOpHOL, valueIsWord]
        · simp [evalHOLExact, evalListHOLExact, hns, wordOpHOL, valueIsWord]
      | _ => simp [pureLimitBound] at hlim
    | _ => simp [pureLimitBound] at hlim
  | _ => simp [pureLimitBound] at hlim

private theorem pureCountedWhile_word_run (counter : MlS) (limExp : ExpHOL 64)
    (K : BitVec 64) (hK : K.toNat < 2 ^ 63)
    {body : ProgHOL 64} {cost : Nat} (counted : CountedBodyExt counter 1 body cost)
    (optVar : Option (MlS × BitVec 64))
    (hpres : ∀ v0 w0, optVar = some (v0, w0) → avoidsLocal v0 body = true)
    (heval : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (∀ v0 w0, optVar = some (v0, w0) → s.locals.lookup v0 = some (.val (.word w0))) →
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) limExp = some (.val (.word K))) :
    ∀ n : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F),
      state.code = originalRuntimeCode →
      ∀ w : BitVec 64, state.locals.lookup counter = some (.val (.word w)) →
      (∀ v0 w0, optVar = some (v0, w0) → state.locals.lookup v0 = some (.val (.word w0))) →
      w.toNat ≤ K.toNat → K.toNat - w.toNat = n → n * (cost + 1) ≤ state.clock →
      let evaluated := evaluateHOLFiniteState state (.while (.cmp .less (.var .local counter) limExp) body)
      state.clock ≤ evaluated.2.clock + n * (cost + 1) ∧
        evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro F state code w atCounter atLim within distance budget
    have hlimVal := heval state atLim
    have hcond : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
        (.cmp .less (.var .local counter) limExp) =
        some (.val (.word (if w.toNat < K.toNat then 1 else 0))) := by
      rw [evalHOLFinite_eq_toExact] at hlimVal ⊢
      simp only [evalHOLExact, atCounter, hlimVal]
      simp only [Compiler.Encoders.Asm.wordCmpHOL, holAsmSignedLess_small w K (by omega) hK]
      by_cases lt : w.toNat < K.toNat <;> simp [lt]
    dsimp only
    rw [evaluateHOLFiniteState_while_total, hcond]
    by_cases lt : w.toNat < K.toNat
    · rw [if_pos lt]
      simp only [show (1 : BitVec 64) ≠ 0 by decide, if_true, ne_eq, not_false_eq_true]
      have positiveRank : 0 < n := by omega
      have oneIteration : cost + 1 ≤ n * (cost + 1) := Nat.le_mul_of_pos_left _ positiveRank
      have clock : state.clock ≠ 0 := by omega
      rw [if_neg clock, fixClockHOLFinite_evaluateState]
      have stepRun := countedBodyExt_run counted (decClockHOLFinite state) code w atCounter
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
            rw [BitVec.toNat_add_of_lt (by simp; omega)]
            rfl
          have nextRank : K.toNat - (w + 1).toNat < n := by rw [natural]; omega
          have nextLim : ∀ v0 w0, optVar = some (v0, w0) → middle.locals.lookup v0 = some (.val (.word w0)) := by
            intro v0 w0 hv
            have hp := hpres v0 w0 hv
            have frame := evaluate_avoidsLocal_flowing v0 body hp (decClockHOLFinite state)
            rw [bodyRun] at frame
            exact (frame (Or.inl rfl)).trans (atLim v0 w0 hv)
          have decrease : (K.toNat - (w + 1).toNat) * (cost + 1) + (cost + 1) ≤ n * (cost + 1) := by
            rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
          obtain ⟨t1, t2, t3⟩ := ih (K.toNat - (w + 1).toNat) nextRank middle (nextCode.trans code)
            (w + 1) nextCounter nextLim (by rw [natural]; omega) rfl (by omega)
          exact ⟨by omega, by omega, t3⟩
        | some r =>
          cases r with
          | «continue» => exact absurd rfl noCont
          | «break» => exact ⟨by simp; omega, by simp; omega, by simp⟩
          | timeOut => exact absurd rfl safe
          | _ => exact ⟨by simp; omega, by simp; omega, by simp⟩
    · rw [if_neg lt]
      simp

private theorem pureCountedWhile_zero_bounded
    (counter : MlS) (limExp : ExpHOL 64) {optLim : Option MlS} {maxB : Nat}
    (hlim : pureLimitBound limExp = some (optLim, maxB))
    {body : ProgHOL 64} {cost : Nat} (counted : CountedBodyExt counter 1 body cost)
    (hpres : match optLim with | none => true | some v0 => avoidsLocal v0 body)
    {F : Type} (state : PanSemStateFiniteExact 64 F) (code : state.code = originalRuntimeCode)
    (atCounter : state.locals.lookup counter = some (.val (.word 0)))
    (budget : maxB * (cost + 1) ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.while (.cmp .less (.var .local counter) limExp) body)
    state.clock ≤ evaluated.2.clock + maxB * (cost + 1) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have ⟨hmaxLt, hcases⟩ := pureLimitBound_spec hlim
  rcases hcases state with ⟨v0, rfl, hnone⟩ | ⟨v0, ns, rfl, hr⟩ | ⟨v0, nm, ns, rfl, hns⟩ |
    ⟨K, hvar, hevalS, hKmax⟩
  · have hmaxEq : maxB = 2 ^ 63 - 1 := by
      cases limExp <;> simp [pureLimitBound] at hlim
      · split at hlim <;> simp at hlim
      · rename_i vk _; cases vk <;> simp [pureLimitBound] at hlim; omega
      · rename_i bop es; cases bop <;> simp [pureLimitBound] at hlim
        rcases es with _ | ⟨e1, _ | ⟨e2, _ | _⟩⟩ <;> simp [pureLimitBound] at hlim
        cases e1 <;> simp [pureLimitBound] at hlim
        rename_i vk _; cases vk <;> cases e2 <;> simp [pureLimitBound] at hlim; omega
    subst hmaxEq
    have hbad := pureLimitBound_none_or_nonword state hlim (Or.inl hnone)
    have hcond : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
        (.cmp .less (.var .local counter) limExp) = none := by
      rw [evalHOLFinite_eq_toExact] at hbad ⊢
      rcases hbad with hb | ⟨ns, hb⟩ | ⟨nm, ns, hb⟩ <;> simp [evalHOLExact, atCounter, hb, Compiler.Encoders.Asm.wordCmpHOL]
    dsimp only; rw [evaluateHOLFiniteState_while_total, hcond]; simp
  · have hmaxEq : maxB = 2 ^ 63 - 1 := by
      cases limExp <;> simp [pureLimitBound] at hlim
      · split at hlim <;> simp at hlim
      · rename_i vk _; cases vk <;> simp [pureLimitBound] at hlim; omega
      · rename_i bop es; cases bop <;> simp [pureLimitBound] at hlim
        rcases es with _ | ⟨e1, _ | ⟨e2, _ | _⟩⟩ <;> simp [pureLimitBound] at hlim
        cases e1 <;> simp [pureLimitBound] at hlim
        rename_i vk _; cases vk <;> cases e2 <;> simp [pureLimitBound] at hlim; omega
    subst hmaxEq
    have hbad := pureLimitBound_none_or_nonword state hlim (Or.inr (Or.inl ⟨ns, hr⟩))
    have hcond : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
        (.cmp .less (.var .local counter) limExp) = none := by
      rw [evalHOLFinite_eq_toExact] at hbad ⊢
      rcases hbad with hb | ⟨ns', hb⟩ | ⟨nm, ns', hb⟩ <;> simp [evalHOLExact, atCounter, hb, Compiler.Encoders.Asm.wordCmpHOL]
    dsimp only; rw [evaluateHOLFiniteState_while_total, hcond]; simp
  · have hmaxEq : maxB = 2 ^ 63 - 1 := by
      cases limExp <;> simp [pureLimitBound] at hlim
      · split at hlim <;> simp at hlim
      · rename_i vk _; cases vk <;> simp [pureLimitBound] at hlim; omega
      · rename_i bop es; cases bop <;> simp [pureLimitBound] at hlim
        rcases es with _ | ⟨e1, _ | ⟨e2, _ | _⟩⟩ <;> simp [pureLimitBound] at hlim
        cases e1 <;> simp [pureLimitBound] at hlim
        rename_i vk _; cases vk <;> cases e2 <;> simp [pureLimitBound] at hlim; omega
    subst hmaxEq
    have hbad := pureLimitBound_none_or_nonword state hlim (Or.inr (Or.inr ⟨nm, ns, hns⟩))
    have hcond : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
        (.cmp .less (.var .local counter) limExp) = none := by
      rw [evalHOLFinite_eq_toExact] at hbad ⊢
      rcases hbad with hb | ⟨ns', hb⟩ | ⟨nm', ns', hb⟩ <;> simp [evalHOLExact, atCounter, hb, Compiler.Encoders.Asm.wordCmpHOL]
    dsimp only; rw [evaluateHOLFiniteState_while_total, hcond]; simp
  · by_cases hKlt : K.toNat < 2 ^ 63
    · have hKle := hKmax hKlt
      have hceil : K.toNat * (cost + 1) ≤ maxB * (cost + 1) := Nat.mul_le_mul_right _ hKle
      rcases hvar with rfl | ⟨v0, w0, rfl, hl0, hevalAll⟩
      · have hconstEval : ∀ {F' : Type} (s' : PanSemStateFiniteExact 64 F'),
            evalHOLFinite s' (h := fun a => Classical.propDecidable (s'.memaddrs a)) limExp = some (.val (.word K)) := by
          intro F' s'
          cases limExp <;> simp [pureLimitBound] at hlim
          · split at hlim <;> simp at hlim
            rcases hlim with ⟨_, hmax⟩
            rw [evalHOLFinite_eq_toExact] at hevalS ⊢
            simpa [evalHOLExact] using hevalS
          · rename_i vk _; cases vk <;> simp [pureLimitBound] at hlim
          · rename_i bop es; cases bop <;> simp [pureLimitBound] at hlim
            rcases es with _ | ⟨e1, _ | ⟨e2, _ | _⟩⟩ <;> simp [pureLimitBound] at hlim
            cases e1 <;> simp [pureLimitBound] at hlim
            rename_i vk _; cases vk <;> cases e2 <;> simp [pureLimitBound] at hlim
        have hrun := pureCountedWhile_word_run counter limExp K hKlt counted none
          (fun _ _ h => by cases h) (fun s' _ => hconstEval s')
          K.toNat state code 0 atCounter (fun _ _ h => by cases h) (by simp) (by simp) (by omega)
        dsimp only at hrun ⊢
        exact ⟨by omega, hrun.2.1, hrun.2.2⟩
      · have hrun := pureCountedWhile_word_run counter limExp K hKlt counted (some (v0, w0))
          (fun v' w' hv => by cases hv; exact hpres)
          (fun s' hs' => hevalAll s' (hs' v0 w0 rfl))
          K.toNat state code 0 atCounter (fun v' w' hv => by cases hv; exact hl0) (by simp) (by simp) (by omega)
        dsimp only at hrun ⊢
        exact ⟨by omega, hrun.2.1, hrun.2.2⟩
    · have hneg : ¬ K.toNat < 9223372036854775808 := hKlt
      have hcond : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
          (.cmp .less (.var .local counter) limExp) = some (.val (.word 0)) := by
        rw [evalHOLFinite_eq_toExact] at hevalS ⊢
        simp [evalHOLExact, atCounter, hevalS, Compiler.Encoders.Asm.wordCmpHOL,
          Compiler.Encoders.Asm.holAsmSignedLess, hneg]
      dsimp only; rw [evaluateHOLFiniteState_while_total, hcond]; simp

private theorem progBounded_pureCountedDec
    (counter : MlS) (limExp : ExpHOL 64) {optLim : Option MlS} {maxB : Nat}
    (hlim : pureLimitBound limExp = some (optLim, maxB))
    {body : ProgHOL 64} {cost : Nat} (counted : CountedBodyExt counter 1 body cost)
    (hpres : match optLim with | none => true | some v0 => !(v0 == counter) && avoidsLocal v0 body) :
    ProgBounded (.dec counter .one (.const 0) (.while (.cmp .less (.var .local counter) limExp) body))
      (maxB * (cost + 1)) := by
  intro F state code budget
  rw [evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true]
  let entered := setVarHOLFinite counter (.val (.word 0)) state
  have atCounter : entered.locals.lookup counter = some (.val (.word 0)) := by
    simp [entered, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hpres' : (match optLim with | none => true | some v0 => avoidsLocal v0 body) = true := by
    cases optLim with
    | none => rfl
    | some v0 => exact ((Bool.and_eq_true _ _).mp hpres).2
  have loop := pureCountedWhile_zero_bounded counter limExp hlim counted hpres' entered code atCounter budget
  cases loopRun : evaluateHOLFiniteState entered (.while (.cmp .less (.var .local counter) limExp) body) with
  | mk result post =>
    rw [loopRun] at loop
    dsimp only at loop ⊢
    exact loop

private theorem progBounded_pureCountedDecSeq
    (counter : MlS) (limExp : ExpHOL 64) {optLim : Option MlS} {maxB : Nat}
    (hlim : pureLimitBound limExp = some (optLim, maxB))
    {body tail : ProgHOL 64} {cost tailCost : Nat} (counted : CountedBodyExt counter 1 body cost)
    (hpres : match optLim with | none => true | some v0 => !(v0 == counter) && avoidsLocal v0 body)
    (rest : ProgBounded tail tailCost) :
    ProgBounded (.dec counter .one (.const 0) (.seq (.while (.cmp .less (.var .local counter) limExp) body) tail))
      (maxB * (cost + 1) + tailCost) := by
  intro F state code budget
  rw [evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true]
  let entered := setVarHOLFinite counter (.val (.word 0)) state
  have atCounter : entered.locals.lookup counter = some (.val (.word 0)) := by
    simp [entered, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hpres' : (match optLim with | none => true | some v0 => avoidsLocal v0 body) = true := by
    cases optLim with
    | none => rfl
    | some v0 => exact ((Bool.and_eq_true _ _).mp hpres).2
  have loop := pureCountedWhile_zero_bounded counter limExp hlim counted hpres' entered code atCounter
    (by change maxB * (cost + 1) ≤ state.clock; omega)
  have meta' := PanRunBounded.evaluateHOLFiniteState_metadata entered (.while (.cmp .less (.var .local counter) limExp) body)
  change state.clock ≤ (evaluateHOLFiniteState entered _).2.clock + _ ∧
    (evaluateHOLFiniteState entered _).2.clock ≤ state.clock ∧ (evaluateHOLFiniteState entered _).1 ≠ some .timeOut
  rw [evaluateHOLFiniteState_seq_line780]
  cases loopRun : evaluateHOLFiniteState entered (.while (.cmp .less (.var .local counter) limExp) body) with
  | mk result middle =>
    rw [loopRun] at loop meta'
    dsimp only at loop meta'
    obtain ⟨spent, kept, safe⟩ := loop
    change state.clock ≤ middle.clock + maxB * (cost + 1) at spent
    change middle.clock ≤ state.clock at kept
    cases result with
    | none =>
      dsimp only
      obtain ⟨t1, t2, t3⟩ := rest middle (meta'.1.trans code) (by omega)
      exact ⟨by omega, by omega, t3⟩
    | some r =>
      dsimp only
      exact ⟨by omega, kept, safe⟩

private theorem progBounded_pureCountedAssignSeq
    (counter : MlS) (limExp : ExpHOL 64) {optLim : Option MlS} {maxB : Nat}
    (hlim : pureLimitBound limExp = some (optLim, maxB))
    {body tail : ProgHOL 64} {cost tailCost : Nat} (counted : CountedBodyExt counter 1 body cost)
    (hpres : match optLim with | none => true | some v0 => !(v0 == counter) && avoidsLocal v0 body)
    (rest : ProgBounded tail tailCost) :
    ProgBounded (.seq (.assign .local counter (.const 0)) (.seq (.while (.cmp .less (.var .local counter) limExp) body) tail))
      (maxB * (cost + 1) + tailCost) := by
  intro F state code budget
  by_cases valid : isValidValueHOLExact state.toExact .local counter (.val (.word 0)) = true
  · have assignRun : evaluateHOLFiniteState state (.assign .local counter (.const 0)) =
        (none, setKvarHOLFinite .local counter (.val (.word 0)) state) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, valid]
    rw [evaluateHOLFiniteState_seq_line780, assignRun]
    dsimp only
    let entered := setKvarHOLFinite .local counter (.val (.word 0)) state
    have atCounter : entered.locals.lookup counter = some (.val (.word 0)) := by
      simp [entered, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hpres' : (match optLim with | none => true | some v0 => avoidsLocal v0 body) = true := by
      cases optLim with
      | none => rfl
      | some v0 => exact ((Bool.and_eq_true _ _).mp hpres).2
    have loop := pureCountedWhile_zero_bounded counter limExp hlim counted hpres' entered code atCounter
      (by change maxB * (cost + 1) ≤ state.clock; omega)
    have meta' := PanRunBounded.evaluateHOLFiniteState_metadata entered (.while (.cmp .less (.var .local counter) limExp) body)
    change state.clock ≤ (evaluateHOLFiniteState entered _).2.clock + _ ∧
      (evaluateHOLFiniteState entered _).2.clock ≤ state.clock ∧ (evaluateHOLFiniteState entered _).1 ≠ some .timeOut
    rw [evaluateHOLFiniteState_seq_line780]
    cases loopRun : evaluateHOLFiniteState entered (.while (.cmp .less (.var .local counter) limExp) body) with
    | mk result middle =>
      rw [loopRun] at loop meta'
      dsimp only at loop meta'
      obtain ⟨spent, kept, safe⟩ := loop
      change state.clock ≤ middle.clock + maxB * (cost + 1) at spent
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

private theorem progBounded_pureCountedAssignOnly
    (counter : MlS) (limExp : ExpHOL 64) {optLim : Option MlS} {maxB : Nat}
    (hlim : pureLimitBound limExp = some (optLim, maxB))
    {body : ProgHOL 64} {cost : Nat} (counted : CountedBodyExt counter 1 body cost)
    (hpres : match optLim with | none => true | some v0 => !(v0 == counter) && avoidsLocal v0 body) :
    ProgBounded (.seq (.assign .local counter (.const 0)) (.while (.cmp .less (.var .local counter) limExp) body))
      (maxB * (cost + 1)) := by
  intro F state code budget
  by_cases valid : isValidValueHOLExact state.toExact .local counter (.val (.word 0)) = true
  · have assignRun : evaluateHOLFiniteState state (.assign .local counter (.const 0)) =
        (none, setKvarHOLFinite .local counter (.val (.word 0)) state) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, valid]
    rw [evaluateHOLFiniteState_seq_line780, assignRun]
    dsimp only
    let entered := setKvarHOLFinite .local counter (.val (.word 0)) state
    have atCounter : entered.locals.lookup counter = some (.val (.word 0)) := by
      simp [entered, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hpres' : (match optLim with | none => true | some v0 => avoidsLocal v0 body) = true := by
      cases optLim with
      | none => rfl
      | some v0 => exact ((Bool.and_eq_true _ _).mp hpres).2
    have loop := pureCountedWhile_zero_bounded counter limExp hlim counted hpres' entered code atCounter budget
    cases loopRun : evaluateHOLFiniteState entered (.while (.cmp .less (.var .local counter) limExp) body) with
    | mk result post =>
      rw [loopRun] at loop
      dsimp only at loop ⊢
      exact loop
  · have assignRun : evaluateHOLFiniteState state (.assign .local counter (.const 0)) = (some .error, state) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, valid]
    rw [evaluateHOLFiniteState_seq_line780, assignRun]
    simp

def isOneZero : ShapeHOL → ExpHOL 64 → Bool
  | .one, .const 0 => true
  | _, _ => false

private theorem isOneZero_eq {shape : ShapeHOL} {init : ExpHOL 64}
    (h : isOneZero shape init = true) : shape = .one ∧ init = .const 0 := by
  cases shape with
  | one =>
    cases init with
    | const c =>
      simp only [isOneZero] at h
      split at h <;> try cases h
      exact ⟨rfl, rfl⟩
    | _ => simp [isOneZero] at h
  | _ => simp [isOneZero] at h

def isAssignLocalZero : ProgHOL 64 → Option MlS
  | .assign .local counter (.const 0) => some counter
  | _ => none

private theorem isAssignLocalZero_eq {p : ProgHOL 64} {counter : MlS}
    (h : isAssignLocalZero p = some counter) :
    p = .assign .local counter (.const 0) := by
  cases p with
  | assign k nm val =>
    cases k with
    | global => simp [isAssignLocalZero] at h
    | «local» =>
      cases val with
      | const c =>
        simp only [isAssignLocalZero] at h
        split at h <;> simp at h
        subst h; rfl
      | _ => simp [isAssignLocalZero] at h
  | _ => simp [isAssignLocalZero] at h

def asWhileLessOnly : ProgHOL 64 → Option (MlS × ExpHOL 64 × ProgHOL 64)
  | .while (.cmp .less (.var .local counter) limExp) lbody =>
    some (counter, limExp, lbody)
  | _ => none

private theorem asWhileLessOnly_eq {p : ProgHOL 64} {counter : MlS} {limExp : ExpHOL 64} {lbody : ProgHOL 64}
    (h : asWhileLessOnly p = some (counter, limExp, lbody)) :
    p = .while (.cmp .less (.var .local counter) limExp) lbody ∧ sizeOf lbody < sizeOf p := by
  cases p with
  | «while» cond lb =>
    cases cond with
    | cmp op e1 e2 =>
      cases op <;> try (simp [asWhileLessOnly] at h)
      cases e1 with
      | var vk nm =>
        cases vk <;> simp [asWhileLessOnly] at h
        rcases h with ⟨rfl, rfl, rfl⟩
        exact ⟨rfl, by simp_wf; omega⟩
      | _ => simp [asWhileLessOnly] at h
    | _ => simp [asWhileLessOnly] at h
  | _ => simp [asWhileLessOnly] at h

def asWhileLessSeq : ProgHOL 64 → Option (MlS × ExpHOL 64 × ProgHOL 64 × ProgHOL 64)
  | .seq (.while (.cmp .less (.var .local counter) limExp) lbody) tail =>
    some (counter, limExp, lbody, tail)
  | _ => none

private theorem asWhileLessSeq_eq {p : ProgHOL 64}
    {counter : MlS} {limExp : ExpHOL 64} {lbody tail : ProgHOL 64}
    (h : asWhileLessSeq p = some (counter, limExp, lbody, tail)) :
    p = .seq (.while (.cmp .less (.var .local counter) limExp) lbody) tail ∧
      sizeOf lbody < sizeOf p ∧ sizeOf tail < sizeOf p := by
  cases p with
  | seq a b =>
    cases a with
    | «while» cond lb =>
      cases cond with
      | cmp op e1 e2 =>
        cases op <;> try (simp [asWhileLessSeq] at h)
        cases e1 with
        | var vk nm =>
          cases vk <;> simp [asWhileLessSeq] at h
          rcases h with ⟨rfl, rfl, rfl, rfl⟩
          refine ⟨rfl, ?_, ?_⟩
          · simp_wf; omega
          · simp_wf
        | _ => simp [asWhileLessSeq] at h
      | _ => simp [asWhileLessSeq] at h
    | _ => simp [asWhileLessSeq] at h
  | _ => simp [asWhileLessSeq] at h

def checkLimitPres (counter : MlS) (optLim : Option MlS) (lbody : ProgHOL 64) : Bool :=
  match optLim with
  | none => true
  | some v0 => !(v0 == counter) && avoidsLocal v0 lbody

mutual

def evalLocalBound (env : StaticEnv) : Nat → ProgHOL 64 → Option Nat
  | 0, _ => none
  | _ + 1, .skip | _ + 1, .assign _ _ _ | _ + 1, .storeByte _ _ | _ + 1, .store _ _ | _ + 1, .store32 _ _
  | _ + 1, .shMemLoad _ _ _ _ | _ + 1, .shMemStore _ _ _ | _ + 1, .break | _ + 1, .continue | _ + 1, .annot _ _
  | _ + 1, .raise _ _ | _ + 1, .return _ | _ + 1, .primitive _ _ _ | _ + 1, .extCall _ _ _ _ _ => some 0
  | _ + 1, .tick | _ + 1, .while _ _ => none
  | fuel + 1, .ite _ yes no =>
    match evalLocalBound env fuel yes, evalLocalBound env fuel no with
    | some a, some b => some (max a b)
    | _, _ => none
  | fuel + 1, .dec name shape init body =>
    if isOneZero shape init then
      match asWhileLessSeq body, asWhileLessOnly body with
      | some (counter, limExp, lbody, tail), _ =>
        if name == counter then
          match pureLimitBound limExp with
          | some (optLim, maxB) =>
            if checkLimitPres counter optLim lbody then
              match evalCountedBodyExt env fuel counter lbody, evalLocalBound env fuel tail with
              | some bCost, some tCost => some (maxB * (bCost + 1) + tCost)
              | _, _ => none
            else none
          | none => none
        else evalLocalBound env fuel body
      | none, some (counter, limExp, lbody) =>
        if name == counter then
          match pureLimitBound limExp with
          | some (optLim, maxB) =>
            if checkLimitPres counter optLim lbody then
              match evalCountedBodyExt env fuel counter lbody with
              | some bCost => some (maxB * (bCost + 1))
              | none => none
            else none
          | none => none
        else evalLocalBound env fuel body
      | none, none => evalLocalBound env fuel body
    else evalLocalBound env fuel body
  | fuel + 1, .seq first second =>
    let fallback :=
      match evalLocalBound env fuel first, evalLocalBound env fuel second with
      | some a, some b => some (a + b)
      | _, _ => none
    match isAssignLocalZero first, asWhileLessSeq second, asWhileLessOnly second with
    | some counter, some (counter2, limExp, lbody, tail), _ =>
      if counter == counter2 then
        match pureLimitBound limExp with
        | some (optLim, maxB) =>
          if checkLimitPres counter optLim lbody then
            match evalCountedBodyExt env fuel counter lbody, evalLocalBound env fuel tail with
            | some bCost, some tCost => some (maxB * (bCost + 1) + tCost)
            | _, _ => none
          else fallback
        | none => fallback
      else fallback
    | some counter, none, some (counter2, limExp, lbody) =>
      if counter == counter2 then
        match pureLimitBound limExp with
        | some (optLim, maxB) =>
          if checkLimitPres counter optLim lbody then
            match evalCountedBodyExt env fuel counter lbody with
            | some bCost => some (maxB * (bCost + 1))
            | none => fallback
          else fallback
        | none => fallback
      else fallback
    | _, _, _ => fallback
  | _ + 1, .call info fn args =>
    match info with
    | none =>
      match lookupStaticCost env fn with
      | some c => some (c + 1)
      | none => none
    | some (_dest, none) =>
      match specialCallCost fn args with
      | some sc => some sc
      | none =>
        match lookupStaticCost env fn with
        | some c => some (c + 1)
        | none => none
    | some (_dest, some (_hid, _hvar, handler)) =>
      match lookupStaticCost env fn, evalLocalBound env 100 handler with
      | some c, some h => some (c + 1 + h)
      | _, _ => none
  | fuel + 1, .decCall _ _ fn args cont =>
    match specialDecCallOverhead fn args with
    | some ov =>
      match evalLocalBound env fuel cont with
      | some t => some (ov + t)
      | none => none
    | none =>
      match lookupStaticCost env fuel cont, lookupStaticCost env fn with
      | _, _ => none

def evalCountedBodyExt (env : StaticEnv) (counter : MlS) : ProgHOL 64 → Option Nat
  | .dec name shape init body =>
    if !(counter == name) then
      if isOneZero shape init then
        match body with
        | .seq (.while (.cmp .less (.var .local counter2) limExp) lbody) tail =>
          if name == counter2 then
            match pureLimitBound limExp with
            | some (optLim, maxB) =>
              if checkLimitPres counter2 optLim lbody && avoidsLocal counter lbody then
                match evalCountedBodyExt env counter2 lbody, evalCountedBodyExt env counter tail with
                | some bCost, some tCost => some (maxB * (bCost + 1) + tCost)
                | _, _ => none
              else none
            | none => none
          else none
        | _ => evalCountedBodyExt env counter body
      else evalCountedBodyExt env counter body
    else none
  | .seq first tail =>
    if avoidsLocal counter first && noTopContinue first then
      match evalLocalBound env first, evalCountedBodyExt env counter tail with
      | some a, some b => some (a + b)
      | _, _ => none
    else none
  | .decCall name _ fn args cont =>
    if !(counter == name) then
      match evalCountedBodyExt env counter cont with
      | some cCost =>
        match specialDecCallOverhead fn args with
        | some ov => some (ov + cCost)
        | none =>
          match lookupStaticCost env fn with
          | some fnCost => some (fnCost + 1 + cCost)
          | none => none
      | none => none
    else none
  | p =>
    if asIncrAssign counter 1 p then some 0 else none

end

mutual

private theorem evalLocalBound_dec_none {env : StaticEnv}
    (name : MlS) (shape : Shape) (init : ExpHOL 64) {body : ProgHOL 64}
    (hz : isOneZero shape init = true)
    (hw1 : asWhileLessSeq body = none)
    (hw2 : asWhileLessOnly body = none) :
    evalLocalBound env (.dec name shape init body) = evalLocalBound env body := by
  cases body with
  | seq a b =>
    cases a with
    | «while» cond lb =>
      cases cond with
      | cmp op e1 e2 =>
        cases op <;> try (simp [evalLocalBound, hz])
        cases e1 with
        | var vk nm =>
          cases vk <;> simp [asWhileLessSeq] at hw1 <;> simp [evalLocalBound, hz]
        | _ => simp [evalLocalBound, hz]
      | _ => simp [evalLocalBound, hz]
    | _ => simp [evalLocalBound, hz]
  | «while» cond lb =>
    cases cond with
    | cmp op e1 e2 =>
      cases op <;> try (simp [evalLocalBound, hz])
      cases e1 with
      | var vk nm =>
        cases vk <;> simp [asWhileLessOnly] at hw2 <;> simp [evalLocalBound, hz]
      | _ => simp [evalLocalBound, hz]
    | _ => simp [evalLocalBound, hz]
  | _ => simp [evalLocalBound, hz]

private theorem evalLocalBound_seq_none {env : StaticEnv}
    {first second : ProgHOL 64} {counter : MlS}
    (h1 : isAssignLocalZero first = some counter)
    (h2 : asWhileLessSeq second = none)
    (h3 : asWhileLessOnly second = none) :
    evalLocalBound env (.seq first second) =
      (match evalLocalBound env first, evalLocalBound env second with
       | some a, some b => some (a + b)
       | _, _ => none) := by
  cases second with
  | seq a b =>
    cases a with
    | «while» cond lb =>
      cases cond with
      | cmp op e1 e2 =>
        cases op <;> try (simp [evalLocalBound, h1])
        cases e1 with
        | var vk nm =>
          cases vk <;> simp [asWhileLessSeq] at h2 <;> simp [evalLocalBound, h1]
        | _ => simp [evalLocalBound, h1]
      | _ => simp [evalLocalBound, h1]
    | _ => simp [evalLocalBound, h1]
  | «while» cond lb =>
    cases cond with
    | cmp op e1 e2 =>
      cases op <;> try (simp [evalLocalBound, h1])
      cases e1 with
      | var vk nm =>
        cases vk <;> simp [asWhileLessOnly] at h3 <;> simp [evalLocalBound, h1]
      | _ => simp [evalLocalBound, h1]
    | _ => simp [evalLocalBound, h1]
  | _ => simp [evalLocalBound, h1]

private theorem evalCountedBodyExt_dec_none {env : StaticEnv}
    {counter name : MlS} {shape : Shape} {init : ExpHOL 64} {body : ProgHOL 64}
    (hne : (!(counter == name)) = true)
    (hz : isOneZero shape init = true)
    (hw : asWhileLessSeq body = none) :
    evalCountedBodyExt env counter (.dec name shape init body) =
      evalCountedBodyExt env counter body := by
  cases body with
  | seq a b =>
    cases a with
    | «while» cond lb =>
      cases cond with
      | cmp op e1 e2 =>
        cases op <;> try (simp [evalCountedBodyExt, hne, hz])
        cases e1 with
        | var vk nm =>
          cases vk <;> simp [asWhileLessSeq] at hw <;> simp [evalCountedBodyExt, hne, hz]
        | _ => simp [evalCountedBodyExt, hne, hz]
      | _ => simp [evalCountedBodyExt, hne, hz]
    | _ => simp [evalCountedBodyExt, hne, hz]
  | _ => simp [evalCountedBodyExt, hne, hz]

end

mutual

private theorem evalLocalBound_sound {env : StaticEnv} (hvalid : EnvValid env) :
    (p : ProgHOL 64) → (cost : Nat) → evalLocalBound env p = some cost →
    ProgBounded p cost
  | .skip, cost, h => by simp only [evalLocalBound] at h; cases h; exact ProgBounded.straight _ rfl
  | .assign _ _ _, cost, h => by simp only [evalLocalBound] at h; cases h; exact ProgBounded.straight _ rfl
  | .storeByte _ _, cost, h => by simp only [evalLocalBound] at h; cases h; exact ProgBounded.straight _ rfl
  | .store _ _, cost, h => by simp only [evalLocalBound] at h; cases h; exact ProgBounded.straight _ rfl
  | .store32 _ _, cost, h => by simp only [evalLocalBound] at h; cases h; exact ProgBounded.straight _ rfl
  | .shMemLoad _ _ _ _, cost, h => by simp only [evalLocalBound] at h; cases h; exact ProgBounded.straight _ rfl
  | .shMemStore _ _ _, cost, h => by simp only [evalLocalBound] at h; cases h; exact ProgBounded.straight _ rfl
  | .break, cost, h => by simp only [evalLocalBound] at h; cases h; exact ProgBounded.straight _ rfl
  | .continue, cost, h => by simp only [evalLocalBound] at h; cases h; exact ProgBounded.straight _ rfl
  | .annot _ _, cost, h => by simp only [evalLocalBound] at h; cases h; exact ProgBounded.straight _ rfl
  | .raise _ _, cost, h => by simp only [evalLocalBound] at h; cases h; exact ProgBounded.straight _ rfl
  | .return _, cost, h => by simp only [evalLocalBound] at h; cases h; exact ProgBounded.straight _ rfl
  | .primitive _ _ _, cost, h => by simp only [evalLocalBound] at h; cases h; exact ProgBounded.straight _ rfl
  | .extCall _ _ _ _ _, cost, h => by simp only [evalLocalBound] at h; cases h; exact ProgBounded.straight _ rfl
  | .tick, _, h => by simp only [evalLocalBound] at h; cases h
  | .while _ _, _, h => by simp only [evalLocalBound] at h; cases h
  | .ite cond yes no, cost, h => by
    simp only [evalLocalBound] at h
    rcases hy : evalLocalBound env yes with _ | a <;>
      rcases hn : evalLocalBound env no with _ | b <;>
      rw [hy, hn] at h <;> cases h
    exact ProgBounded.iteMax cond (evalLocalBound_sound hvalid yes a hy)
      (evalLocalBound_sound hvalid no b hn)
  | .dec name shape init body, cost, h => by
    have hfb : evalLocalBound env body = some cost → ProgBounded (.dec name shape init body) cost :=
      fun hb => ProgBounded.dec name shape init (evalLocalBound_sound hvalid body cost hb)
    by_cases hz : isOneZero shape init = true
    · rcases hw1 : asWhileLessSeq body with _ | ⟨counter, limExp, lbody, tail⟩
      · rcases hw2 : asWhileLessOnly body with _ | ⟨counter, limExp, lbody⟩
        · rw [evalLocalBound_dec_none name shape init hz hw1 hw2] at h
          exact hfb h
        · have ⟨hsh, hinit⟩ := isOneZero_eq hz
          have ⟨hbody, _hsz⟩ := asWhileLessOnly_eq hw2
          rw [hbody] at h
          simp only [evalLocalBound, hz, ↓reduceIte] at h
          by_cases hnc : (name == counter) = true
          · rw [if_pos hnc] at h
            rcases hlim : pureLimitBound limExp with _ | ⟨optLim, maxB⟩
            · rw [hlim] at h; cases h
            · rw [hlim] at h
              dsimp only at h
              by_cases hp : checkLimitPres counter optLim lbody = true
              · rw [if_pos hp] at h
                rcases hb : evalCountedBodyExt env counter lbody with _ | bCost
                · rw [hb] at h; cases h
                · rw [hb] at h
                  cases h
                  have hnc' : name = counter := by simpa using hnc
                  subst hnc'
                  have hcb := evalCountedBodyExt_sound hvalid name lbody bCost hb
                  rw [hsh, hinit, hbody]
                  exact progBounded_pureCountedDec name limExp hlim hcb hp
              · rw [if_neg hp] at h; cases h
          · rw [if_neg hnc] at h; cases h
      · have ⟨hsh, hinit⟩ := isOneZero_eq hz
        have ⟨hbody, _hsz1, _hsz2⟩ := asWhileLessSeq_eq hw1
        rw [hbody] at h
        simp only [evalLocalBound, hz, ↓reduceIte] at h
        by_cases hnc : (name == counter) = true
        · rw [if_pos hnc] at h
          rcases hlim : pureLimitBound limExp with _ | ⟨optLim, maxB⟩
          · rw [hlim] at h; cases h
          · rw [hlim] at h
            dsimp only at h
            by_cases hp : checkLimitPres counter optLim lbody = true
            · rw [if_pos hp] at h
              rcases hb : evalCountedBodyExt env counter lbody with _ | bCost
              · rw [hb] at h; cases h
              · rcases ht : evalLocalBound env tail with _ | tCost
                · rw [hb, ht] at h; cases h
                · rw [hb, ht] at h
                  cases h
                  have hnc' : name = counter := by simpa using hnc
                  subst hnc'
                  have hcb := evalCountedBodyExt_sound hvalid name lbody bCost hb
                  have htb := evalLocalBound_sound hvalid tail tCost ht
                  rw [hsh, hinit, hbody]
                  exact progBounded_pureCountedDecSeq name limExp hlim hcb hp htb
            · rw [if_neg hp] at h; cases h
        · rw [if_neg hnc] at h; cases h
    · simp only [evalLocalBound, hz, Bool.false_eq_true, ↓reduceIte] at h
      exact hfb h
  | .seq first second, cost, h => by
    have hfb : (match evalLocalBound env first, evalLocalBound env second with
        | some a, some b => some (a + b)
        | _, _ => none) = some cost → ProgBounded (.seq first second) cost := by
      intro hc
      rcases hf : evalLocalBound env first with _ | a <;>
        rcases hs : evalLocalBound env second with _ | b <;>
        rw [hf, hs] at hc <;> cases hc
      exact ProgBounded.seq (evalLocalBound_sound hvalid first a hf)
        (evalLocalBound_sound hvalid second b hs)
    rcases h1 : isAssignLocalZero first with _ | counter
    · simp only [evalLocalBound, h1] at h
      exact hfb h
    · rcases h2 : asWhileLessSeq second with _ | ⟨counter2, limExp, lbody, tail⟩
      · rcases h3 : asWhileLessOnly second with _ | ⟨counter2, limExp, lbody⟩
        · rw [evalLocalBound_seq_none h1 h2 h3] at h
          exact hfb h
        · have hfirst := isAssignLocalZero_eq h1
          have ⟨hsec, _hsz⟩ := asWhileLessOnly_eq h3
          rw [hsec] at h
          simp only [evalLocalBound, h1] at h
          by_cases hcc : (counter == counter2) = true
          · rw [if_pos hcc] at h
            rcases hlim : pureLimitBound limExp with _ | ⟨optLim, maxB⟩
            · rw [hlim] at h; cases h
            · rw [hlim] at h
              dsimp only at h
              by_cases hp : checkLimitPres counter optLim lbody = true
              · rw [if_pos hp] at h
                rcases hb : evalCountedBodyExt env counter lbody with _ | bCost
                · rw [hb] at h; cases h
                · rw [hb] at h
                  cases h
                  have hcc' : counter = counter2 := by simpa using hcc
                  subst hcc'
                  have hcb := evalCountedBodyExt_sound hvalid counter lbody bCost hb
                  rw [hfirst, hsec]
                  exact progBounded_pureCountedAssignOnly counter limExp hlim hcb hp
              · rw [if_neg hp] at h; cases h
          · rw [if_neg hcc] at h; cases h
      · have hfirst := isAssignLocalZero_eq h1
        have ⟨hsec, _hsz1, _hsz2⟩ := asWhileLessSeq_eq h2
        rw [hsec] at h
        simp only [evalLocalBound, h1] at h
        by_cases hcc : (counter == counter2) = true
        · rw [if_pos hcc] at h
          rcases hlim : pureLimitBound limExp with _ | ⟨optLim, maxB⟩
          · rw [hlim] at h; cases h
          · rw [hlim] at h
            dsimp only at h
            by_cases hp : checkLimitPres counter optLim lbody = true
            · rw [if_pos hp] at h
              rcases hb : evalCountedBodyExt env counter lbody with _ | bCost
              · rw [hb] at h; cases h
              · rcases ht : evalLocalBound env tail with _ | tCost
                · rw [hb, ht] at h; cases h
                · rw [hb, ht] at h
                  cases h
                  have hcc' : counter = counter2 := by simpa using hcc
                  subst hcc'
                  have hcb := evalCountedBodyExt_sound hvalid counter lbody bCost hb
                  have htb := evalLocalBound_sound hvalid tail tCost ht
                  rw [hfirst, hsec]
                  exact progBounded_pureCountedAssignSeq counter limExp hlim hcb hp htb
            · rw [if_neg hp] at h; cases h
        · rw [if_neg hcc] at h; cases h
  | .call none fn args, cost, h => by
    simp only [evalLocalBound] at h
    rcases hl : lookupStaticCost env fn with _ | c <;> rw [hl] at h <;> cases h
    exact ProgBounded.tail (lookupStaticCost_sound hvalid hl) args
  | .call (some (dest, none)) fn args, cost, h => by
    simp only [evalLocalBound] at h
    rcases hs : specialCallCost fn args with _ | sc
    · rw [hs] at h
      rcases hl : lookupStaticCost env fn with _ | c <;> rw [hl] at h <;> cases h
      exact ProgBounded.call (lookupStaticCost_sound hvalid hl) dest args
    · rw [hs] at h
      cases h
      exact specialCallCost_sound dest fn args hs
  | .call (some (dest, some (hid, hvar, handler))) fn args, cost, h => by
    simp only [evalLocalBound] at h
    rcases hl : lookupStaticCost env fn with _ | c <;>
      rcases hh : evalLocalBound env handler with _ | hc <;>
      rw [hl, hh] at h <;> cases h
    exact ProgBounded.handledCall (lookupStaticCost_sound hvalid hl) hid hvar dest args
      (evalLocalBound_sound hvalid handler hc hh)
  | .decCall name shape fn args cont, cost, h => by
    simp only [evalLocalBound] at h
    rcases hs : specialDecCallOverhead fn args with _ | ov
    · rw [hs] at h
      rcases hl : lookupStaticCost env fn with _ | c <;>
        rcases ht : evalLocalBound env cont with _ | t <;>
        rw [hl, ht] at h <;> cases h
      exact ProgBounded.decCall (lookupStaticCost_sound hvalid hl) name shape args
        (evalLocalBound_sound hvalid cont t ht)
    · rw [hs] at h
      rcases ht : evalLocalBound env cont with _ | t <;> rw [ht] at h <;> cases h
      exact specialDecCallOverhead_sound name shape fn args hs
        (evalLocalBound_sound hvalid cont t ht)
termination_by p _ _ => sizeOf p
decreasing_by
  all_goals
    simp_wf
    try
      first
      | have hsz := (asWhileLessSeq_eq ‹_›).2; omega
      | have hsz := (asWhileLessOnly_eq ‹_›).2; omega
      | omega

private theorem evalCountedBodyExt_sound {env : StaticEnv} (hvalid : EnvValid env)
    (counter : MlS) :
    (p : ProgHOL 64) → (cost : Nat) → evalCountedBodyExt env counter p = some cost →
    CountedBodyExt counter 1 p cost
  | .dec name shape init body, cost, h => by
    by_cases hne : (!(counter == name)) = true
    · have hne' : counter ≠ name := by intro heq; subst heq; simp at hne
      have hfb : evalCountedBodyExt env counter body = some cost →
          CountedBodyExt counter 1 (.dec name shape init body) cost :=
        fun hb => CountedBodyExt.dec name shape init hne'
          (evalCountedBodyExt_sound hvalid counter body cost hb)
      by_cases hz : isOneZero shape init = true
      · rcases hw : asWhileLessSeq body with _ | ⟨counter2, limExp, lbody, tail⟩
        · rw [evalCountedBodyExt_dec_none hne hz hw] at h
          exact hfb h
        · have ⟨hsh, hinit⟩ := isOneZero_eq hz
          have ⟨hbody, _hsz1, _hsz2⟩ := asWhileLessSeq_eq hw
          rw [hbody] at h
          simp only [evalCountedBodyExt, hne, hz, ↓reduceIte] at h
          by_cases hnc : (name == counter2) = true
          · rw [if_pos hnc] at h
            rcases hlim : pureLimitBound limExp with _ | ⟨optLim, maxB⟩
            · rw [hlim] at h; cases h
            · rw [hlim] at h
              dsimp only at h
              by_cases hp : (checkLimitPres counter2 optLim lbody && avoidsLocal counter lbody) = true
              · rw [if_pos hp] at h
                rcases hb : evalCountedBodyExt env counter2 lbody with _ | bCost
                · rw [hb] at h; cases h
                · rcases ht : evalCountedBodyExt env counter tail with _ | tCost
                  · rw [hb, ht] at h; cases h
                  · rw [hb, ht] at h
                    cases h
                    have hnc' : name = counter2 := by simpa using hnc
                    subst hnc'
                    have hp' := (Bool.and_eq_true _ _).mp hp
                    have hcb := evalCountedBodyExt_sound hvalid name lbody bCost hb
                    have htc := evalCountedBodyExt_sound hvalid counter tail tCost ht
                    have htpb := countedBodyExt_progBounded htc
                    rw [hsh, hinit, hbody]
                    exact CountedBodyExt.decWhile name limExp
                      (progBounded_pureCountedDecSeq name limExp hlim hcb hp'.1 htpb)
                      hne' hp'.2 htc
              · rw [if_neg hp] at h; cases h
          · rw [if_neg hnc] at h; cases h
      · simp only [evalCountedBodyExt, hne, hz, Bool.false_eq_true, ↓reduceIte] at h
        exact hfb h
    · simp only [evalCountedBodyExt, hne, Bool.false_eq_true, ↓reduceIte] at h; cases h
  | .seq first tail, cost, h => by
    simp only [evalCountedBodyExt] at h
    by_cases hcond : (avoidsLocal counter first && noTopContinue first) = true
    · rw [if_pos hcond] at h
      rcases hf : evalLocalBound env first with _ | a <;>
        rcases ht : evalCountedBodyExt env counter tail with _ | b <;>
        rw [hf, ht] at h <;> cases h
      have hc := (Bool.and_eq_true _ _).mp hcond
      exact CountedBodyExt.seq first (evalLocalBound_sound hvalid first a hf) hc.1 hc.2
        (evalCountedBodyExt_sound hvalid counter tail b ht)
    · rw [if_neg hcond] at h; cases h
  | .decCall name shape fn args cont, cost, h => by
    simp only [evalCountedBodyExt] at h
    by_cases hne : (!(counter == name)) = true
    · rw [if_pos hne] at h
      have hne' : counter ≠ name := by intro heq; subst heq; simp at hne
      rcases hc : evalCountedBodyExt env counter cont with _ | cCost
      · rw [hc] at h; cases h
      · rw [hc] at h
        dsimp only at h
        have hcb := evalCountedBodyExt_sound hvalid counter cont cCost hc
        have hcontPb := countedBodyExt_progBounded hcb
        rcases hs : specialDecCallOverhead fn args with _ | ov
        · rw [hs] at h
          rcases hl : lookupStaticCost env fn with _ | fnCost
          · rw [hl] at h; cases h
          · rw [hl] at h
            cases h
            exact CountedBodyExt.decCall name shape fn args
              (ProgBounded.decCall (lookupStaticCost_sound hvalid hl) name shape args hcontPb)
              hne' hcb
        · rw [hs] at h
          cases h
          exact CountedBodyExt.decCall name shape fn args
            (specialDecCallOverhead_sound name shape fn args hs hcontPb)
            hne' hcb
    · rw [if_neg hne] at h; cases h
  | .assign kind name val, cost, h => by
    simp only [evalCountedBodyExt] at h
    by_cases hinc : asIncrAssign counter 1 (.assign kind name val) = true
    · rw [if_pos hinc] at h
      cases h
      cases kind with
      | global => simp [asIncrAssign] at hinc
      | «local» =>
        cases val with
        | op bop es =>
          cases bop with
          | add =>
            rcases es with _ | ⟨x1, _ | ⟨x2, _ | _⟩⟩ <;> try (simp [asIncrAssign] at hinc)
            cases x1 with
            | var vk src =>
              cases vk <;> cases x2 <;> simp [asIncrAssign, Bool.and_eq_true, beq_iff_eq] at hinc
              rcases hinc with ⟨⟨rfl, rfl⟩, rfl⟩
              exact CountedBodyExt.incr
            | _ => simp [asIncrAssign] at hinc
          | _ => simp [asIncrAssign] at hinc
        | _ => simp [asIncrAssign] at hinc
    · rw [if_neg hinc] at h; cases h
  | .skip, _, h | .storeByte _ _, _, h | .store _ _, _, h | .store32 _ _, _, h
  | .shMemLoad _ _ _ _, _, h | .shMemStore _ _ _, _, h | .break, _, h | .continue, _, h
  | .annot _ _, _, h | .raise _ _, _, h | .return _, _, h | .primitive _ _ _, _, h
  | .extCall _ _ _ _ _, _, h | .tick, _, h | .while _ _, _, h | .ite _ _ _, _, h
  | .call _ _ _, _, h => by
    simp only [evalCountedBodyExt, asIncrAssign, Bool.false_eq_true, ↓reduceIte] at h
termination_by p _ _ => sizeOf p
decreasing_by
  all_goals
    simp_wf
    try
      first
      | have hsz := (asWhileLessSeq_eq ‹_›).2; omega
      | have hsz := (asWhileLessOnly_eq ‹_›).2; omega
      | omega

end

theorem funBounded_of_localChecker
    {env : StaticEnv} (hvalid : EnvValid env)
    (i : Nat) (hi : i < Guest.Software.guestAst.length)
    (d : Decl (BitVec 64)) (cost : Nat)
    (hd : Guest.Software.guestAst[i] = .function (extractFn d))
    (hcheck : evalLocalBound env
      (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body) = some cost) :
    FunBounded (ofString (extractFn d).name) cost :=
  funBounded_of_guestAst i hi d cost hd (evalLocalBound_sound hvalid _ cost hcheck)

theorem funBounded_of_localChecker_le
    {env : StaticEnv} (hvalid : EnvValid env)
    (i : Nat) (hi : i < Guest.Software.guestAst.length)
    (d : Decl (BitVec 64)) (cost cost' : Nat)
    (hd : Guest.Software.guestAst[i] = .function (extractFn d))
    (hcheck : evalLocalBound env
      (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body) = some cost)
    (hle : cost ≤ cost') :
    FunBounded (ofString (extractFn d).name) cost' :=
  funBounded_of_guestAst i hi d cost' hd
    (ProgBounded.weaken (evalLocalBound_sound hvalid _ cost hcheck) hle)

theorem funBounded_state_snapshot : FunBounded (ofString "state_snapshot") 0 :=
  funBounded_of_guestAst 358 (by rw [guestAst_len]; decide) Guest.Software.guestFn_state_snapshot 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_frame_new (Ka Kz Kf Kj Kl Kh Kc : Nat)
    (ha : FunBounded (ofString "scratch_alloc") Ka)
    (hz : FunBounded (ofString "memzero") Kz)
    (hf : FunBounded (ofString "frame_mem_alloc") Kf)
    (hj : FunBounded (ofString "compute_jumpdests") Kj)
    (hl : FunBounded (ofString "lst_new_scratch") Kl)
    (hh : FunBounded (ofString "htab_new_scratch") Kh)
    (hc : FunBounded (ofString "htab_count") Kc) :
    FunBounded (ofString "frame_new") (2 * Ka + Kz + Kf + Kj + Kl + Kh + 2 * Kc + 11) := by
  refine funBounded_of_guestAst 467 (by rw [guestAst_len]; decide) Guest.Software.guestFn_frame_new
    (2 * Ka + Kz + Kf + Kj + Kl + Kh + 2 * Kc + 11) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_frame_new,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, List.map, Option.map]
  apply ProgBounded.weaken
  · exact
      ProgBounded.decCall funBounded_scratch_mark _ _ _
      (ProgBounded.decCall funBounded_frame_mem_mark _ _ _
      (ProgBounded.decCall ha _ _ _
      (ProgBounded.seq (ProgBounded.call hz _ _)
      (ProgBounded.decCall ha _ _ _
      (ProgBounded.seq (ProgBounded.straight _ rfl)
      (ProgBounded.seq (ProgBounded.straight _ rfl)
      (ProgBounded.seq (ProgBounded.straight _ rfl)
      (ProgBounded.decCall hf _ _ _
      (ProgBounded.seq (ProgBounded.straight _ rfl)
      (ProgBounded.seq (ProgBounded.straight _ rfl)
      (ProgBounded.seq (ProgBounded.straight _ rfl)
      (ProgBounded.seq (ProgBounded.straight _ rfl)
      (ProgBounded.seq (ProgBounded.straight _ rfl)
      (ProgBounded.seq (ProgBounded.straight _ rfl)
      (ProgBounded.seq (ProgBounded.straight _ rfl)
      (ProgBounded.decCall hj _ _ _
      (ProgBounded.seq (ProgBounded.straight _ rfl)
      (ProgBounded.decCall hl _ _ _
      (ProgBounded.seq (ProgBounded.straight _ rfl)
      (ProgBounded.seq (ProgBounded.straight _ rfl)
      (ProgBounded.seq (ProgBounded.straight _ rfl)
      (ProgBounded.decCall hh _ _ _
      (ProgBounded.seq (ProgBounded.straight _ rfl)
      (ProgBounded.seq (ProgBounded.straight _ rfl)
      (ProgBounded.seq (ProgBounded.straight _ rfl)
      (ProgBounded.decCall hc _ _ _
      (ProgBounded.seq (ProgBounded.straight _ rfl)
      (ProgBounded.seq (ProgBounded.call hc _ _)
        (ProgBounded.straight _ rfl)))))))))))))))))))))))))))))
  · omega

theorem funBounded_min : FunBounded (ofString "min") 0 :=
  funBounded_of_guestAst 31 (by rw [guestAst_len]; decide) Guest.Software.guestFn_min 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_max : FunBounded (ofString "max") 0 :=
  funBounded_of_guestAst 32 (by rw [guestAst_len]; decide) Guest.Software.guestFn_max 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_u256_is_zero : FunBounded (ofString "u256_is_zero") 0 :=
  funBounded_of_guestAst 42 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_is_zero 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_u256_eq : FunBounded (ofString "u256_eq") 0 :=
  funBounded_of_guestAst 45 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_eq 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_u256_lt : FunBounded (ofString "u256_lt") 0 :=
  funBounded_of_guestAst 46 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_lt 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_htab_new : FunBounded (ofString "htab_new") 8 :=
  funBounded_of_localChecker (env := [(ofString "alloc", 1)]) ⟨funBounded_alloc, trivial⟩
    128 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htab_new 8 rfl rfl

theorem funBounded_htab_new_scratch : FunBounded (ofString "htab_new_scratch") 8 :=
  funBounded_of_localChecker (env := [(ofString "scratch_alloc", 1)]) ⟨funBounded_scratch_alloc, trivial⟩
    129 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htab_new_scratch 8 rfl rfl

theorem funBounded_state_fresh_tx : FunBounded (ofString "state_fresh_tx") 122 :=
  funBounded_of_localChecker (env := [(ofString "alloc", 1), (ofString "htab_new", 8)])
    ⟨funBounded_alloc, funBounded_htab_new, trivial⟩
    355 (by rw [guestAst_len]; decide) Guest.Software.guestFn_state_fresh_tx 122 rfl rfl

theorem funBounded_track_ancestor_access : FunBounded (ofString "track_ancestor_access") 0 :=
  funBounded_of_guestAst 402 (by rw [guestAst_len]; decide) Guest.Software.guestFn_track_ancestor_access 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_lst_new : FunBounded (ofString "lst_new") 4 :=
  funBounded_of_staticChecker (env := [(ofString "alloc", 1)]) ⟨funBounded_alloc, trivial⟩
    408 (by rw [guestAst_len]; decide) Guest.Software.guestFn_lst_new 4 rfl rfl

theorem funBounded_lst_new_scratch : FunBounded (ofString "lst_new_scratch") 4 :=
  funBounded_of_staticChecker (env := [(ofString "scratch_alloc", 1)]) ⟨funBounded_scratch_alloc, trivial⟩
    409 (by rw [guestAst_len]; decide) Guest.Software.guestFn_lst_new_scratch 4 rfl rfl

theorem funBounded_bal_init : FunBounded (ofString "bal_init") 29 :=
  funBounded_of_staticChecker (env := [(ofString "htab_new", 8), (ofString "alloc", 1)])
    ⟨funBounded_htab_new, funBounded_alloc, trivial⟩
    411 (by rw [guestAst_len]; decide) Guest.Software.guestFn_bal_init 29 rfl rfl

theorem funBounded_sat_word : FunBounded (ofString "sat_word") 0 :=
  funBounded_of_guestAst 440 (by rw [guestAst_len]; decide) Guest.Software.guestFn_sat_word 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_add_sat : FunBounded (ofString "add_sat") 0 :=
  funBounded_of_guestAst 441 (by rw [guestAst_len]; decide) Guest.Software.guestFn_add_sat 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_ceil32 : FunBounded (ofString "ceil32") 1 :=
  funBounded_of_staticChecker (env := [(ofString "add_sat", 0)]) ⟨funBounded_add_sat, trivial⟩
    442 (by rw [guestAst_len]; decide) Guest.Software.guestFn_ceil32 1 rfl rfl

theorem funBounded_words_of : FunBounded (ofString "words_of") 2 :=
  funBounded_of_staticChecker (env := [(ofString "ceil32", 1)]) ⟨funBounded_ceil32, trivial⟩
    443 (by rw [guestAst_len]; decide) Guest.Software.guestFn_words_of 2 rfl rfl

theorem funBounded_check_gas : FunBounded (ofString "check_gas") 0 :=
  funBounded_of_guestAst 447 (by rw [guestAst_len]; decide) Guest.Software.guestFn_check_gas 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_charge_gas : FunBounded (ofString "charge_gas") 0 :=
  funBounded_of_guestAst 448 (by rw [guestAst_len]; decide) Guest.Software.guestFn_charge_gas 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_charge_state_gas : FunBounded (ofString "charge_state_gas") 1 :=
  funBounded_of_staticChecker (env := [(ofString "add_sat", 0)]) ⟨funBounded_add_sat, trivial⟩
    449 (by rw [guestAst_len]; decide) Guest.Software.guestFn_charge_state_gas 1 rfl rfl

theorem funBounded_credit_state_gas_refund : FunBounded (ofString "credit_state_gas_refund") 1 :=
  funBounded_of_staticChecker (env := [(ofString "min", 0)]) ⟨funBounded_min, trivial⟩
    450 (by rw [guestAst_len]; decide) Guest.Software.guestFn_credit_state_gas_refund 1 rfl rfl

theorem funBounded_frame_state_gas_used : FunBounded (ofString "frame_state_gas_used") 0 :=
  funBounded_of_guestAst 451 (by rw [guestAst_len]; decide) Guest.Software.guestFn_frame_state_gas_used 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_refill_frame_state_gas : FunBounded (ofString "refill_frame_state_gas") 0 :=
  funBounded_of_guestAst 452 (by rw [guestAst_len]; decide) Guest.Software.guestFn_refill_frame_state_gas 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_stack_pop : FunBounded (ofString "stack_pop") 0 :=
  funBounded_of_guestAst 453 (by rw [guestAst_len]; decide) Guest.Software.guestFn_stack_pop 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_msg_new : FunBounded (ofString "msg_new") 32 :=
  funBounded_of_staticChecker (env := [(ofString "alloc", 1)]) ⟨funBounded_alloc, trivial⟩
    465 (by rw [guestAst_len]; decide) Guest.Software.guestFn_msg_new 32 rfl rfl

theorem funBounded_msg_new_scratch : FunBounded (ofString "msg_new_scratch") 32 :=
  funBounded_of_staticChecker (env := [(ofString "scratch_alloc", 1)]) ⟨funBounded_scratch_alloc, trivial⟩
    466 (by rw [guestAst_len]; decide) Guest.Software.guestFn_msg_new_scratch 32 rfl rfl

theorem funBounded_pc_add : FunBounded (ofString "pc_add") 0 :=
  funBounded_of_guestAst 468 (by rw [guestAst_len]; decide) Guest.Software.guestFn_pc_add 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_frame_halt : FunBounded (ofString "frame_halt") 0 :=
  funBounded_of_guestAst 586 (by rw [guestAst_len]; decide) Guest.Software.guestFn_frame_halt 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_incorporate_child_on_error : FunBounded (ofString "incorporate_child_on_error") 0 :=
  funBounded_of_guestAst 591 (by rw [guestAst_len]; decide) Guest.Software.guestFn_incorporate_child_on_error 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_child_message : FunBounded (ofString "child_message") 33 :=
  funBounded_of_staticChecker (env := [(ofString "msg_new_scratch", 32)]) ⟨funBounded_msg_new_scratch, trivial⟩
    594 (by rw [guestAst_len]; decide) Guest.Software.guestFn_child_message 33 rfl rfl

theorem funBounded_te_new : FunBounded (ofString "te_new") 35 :=
  funBounded_of_staticChecker (env := [(ofString "alloc", 1)]) ⟨funBounded_alloc, trivial⟩
    869 (by rw [guestAst_len]; decide) Guest.Software.guestFn_te_new 35 rfl rfl

theorem funBounded_frame_open (Kfn : Nat) (hfn : FunBounded (ofString "frame_new") Kfn) :
    FunBounded (ofString "frame_open") (Kfn + 1 + 24) :=
  funBounded_of_localChecker (env := [(ofString "frame_new", Kfn), (ofString "scratch_alloc", 1)])
    ⟨hfn, funBounded_scratch_alloc, trivial⟩
    578 (by rw [guestAst_len]; decide) Guest.Software.guestFn_frame_open (Kfn + 1 + 24) rfl rfl

theorem funBounded_frame_exception : FunBounded (ofString "frame_exception") 2 :=
  funBounded_of_localChecker (env := [(ofString "refill_frame_state_gas", 0), (ofString "frame_halt", 0)])
    ⟨funBounded_refill_frame_state_gas, funBounded_frame_halt, trivial⟩
    579 (by rw [guestAst_len]; decide) Guest.Software.guestFn_frame_exception 2 rfl rfl

theorem funBounded_u256_fits_word : FunBounded (ofString "u256_fits_word") 0 :=
  funBounded_of_localChecker (env := [])
    trivial
    41 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_fits_word 0 rfl rfl

theorem funBounded_u256_limb : FunBounded (ofString "u256_limb") 0 :=
  funBounded_of_localChecker (env := [])
    trivial
    43 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_limb 0 rfl rfl

theorem funBounded_u256_bit : FunBounded (ofString "u256_bit") 1 :=
  funBounded_of_localChecker (env := [(ofString "u256_limb", 0)])
    ⟨funBounded_u256_limb, trivial⟩
    44 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_bit 1 rfl rfl

theorem funBounded_u256_gt : FunBounded (ofString "u256_gt") 1 :=
  funBounded_of_localChecker (env := [(ofString "u256_lt", 0)])
    ⟨funBounded_u256_lt, trivial⟩
    47 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_gt 1 rfl rfl

end InitECandidate.Solver.GuestBoundEvmFrames
