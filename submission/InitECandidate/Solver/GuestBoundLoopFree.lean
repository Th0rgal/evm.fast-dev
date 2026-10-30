import InitECandidate.Solver.UniformSourceClock
import InitECandidate.Solver.PanRunBounded
import InitECandidate.Solver.GuestUniformClockBound
import InitECandidate.Solver.PanRunBoundedExt

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace InitECandidate.Solver.GuestBoundLoopFree

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.PanRunBoundedExt

theorem wordShiftHOL_lsl_one_64 : wordShiftHOL Shift.lsl (1#64) 64 = none := by
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
        simp [evalHOLExact, evalListHOLExact, hd, wordShiftHOL_lsl_one_64, Compiler.Encoders.Asm.wordCmpHOL]
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

private theorem countedBody_seq_straight {counter : MlS} {step : BitVec 64}
    (first : ProgHOL 64) {tail : ProgHOL 64} {cost : Nat}
    (hs : extStraightLine first = true)
    (ha : avoidsLocal counter first = true)
    (hn : noTopContinue first = true)
    (hrest : CountedBody counter step tail cost) :
    CountedBody counter step (.seq first tail) cost := by
  simpa using CountedBody.seq first (ProgBounded.straight first hs) ha hn hrest

private theorem eval_variable_stride_condition {F : Type}
    (state : PanSemStateFiniteExact 64 F) (counter limit : MlS) (op : Cmp)
    (hop : op = .less ∨ op = .lower) (K w : BitVec 64)
    (signed : op = .less → K.toNat < 2 ^ 63 ∧ w.toNat < 2 ^ 63)
    (atCounter : state.locals.lookup counter = some (.val (.word w)))
    (atLimit : state.locals.lookup limit = some (.val (.word K))) :
    evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      (.cmp op (.var .local counter) (.var .local limit)) =
      some (.val (.word (if w.toNat < K.toNat then 1 else 0))) := by
  rw [evalHOLFinite_eq_toExact]
  rcases hop with rfl | rfl
  · obtain ⟨hK, hw⟩ := signed rfl
    simp only [evalHOLExact, atCounter, atLimit, Compiler.Encoders.Asm.wordCmpHOL,
      holAsmSignedLess_small w K hw hK]
    by_cases lt : w.toNat < K.toNat <;> simp [lt]
  · simp only [evalHOLExact, atCounter, atLimit, Compiler.Encoders.Asm.wordCmpHOL]
    by_cases lt : w.toNat < K.toNat <;> simp [lt, BitVec.lt_def]

private theorem variableStrideWhile_run (counter limit : MlS) (op : Cmp)
    (hop : op = .less ∨ op = .lower) (K step : BitVec 64)
    (hsmall : K.toNat + step.toNat < 2 ^ 64)
    (hsigned : op = .less → K.toNat + step.toNat < 2 ^ 63)
    (hpos : 0 < step.toNat)
    {body : ProgHOL 64} {cost : Nat} (counted : CountedBody counter step body cost)
    (preservesLimit : avoidsLocal limit body = true) :
    ∀ n : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F),
      state.code = originalRuntimeCode →
      ∀ w : BitVec 64, state.locals.lookup counter = some (.val (.word w)) →
      state.locals.lookup limit = some (.val (.word K)) →
      w.toNat < K.toNat + step.toNat →
      (K.toNat + step.toNat - 1 - w.toNat) / step.toNat = n →
      n * (cost + 1) ≤ state.clock →
      let evaluated := evaluateHOLFiniteState state
        (.while (.cmp op (.var .local counter) (.var .local limit)) body)
      state.clock ≤ evaluated.2.clock + n * (cost + 1) ∧
        evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro F state code w atCounter atLimit within distance budget
    have condition := eval_variable_stride_condition state counter limit op hop K w
      (fun h => ⟨by have := hsigned h; omega, by have := hsigned h; omega⟩)
      atCounter atLimit
    dsimp only
    rw [evaluateHOLFiniteState_while_total, condition]
    by_cases lt : w.toNat < K.toNat
    · rw [if_pos lt]
      simp only [show (1 : BitVec 64) ≠ 0 by decide, if_true, ne_eq, not_false_eq_true]
      have positiveRank : 0 < n := by
        have h1 : step.toNat ≤ K.toNat + step.toNat - 1 - w.toNat := by omega
        have h2 := Nat.div_pos h1 hpos
        omega
      have oneIteration : cost + 1 ≤ n * (cost + 1) := Nat.le_mul_of_pos_left _ positiveRank
      have clock : state.clock ≠ 0 := by omega
      rw [if_neg clock, fixClockHOLFinite_evaluateState]
      have stepRun := counted.run (decClockHOLFinite state) code w atCounter
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
          have natural : (w + step).toNat = w.toNat + step.toNat :=
            BitVec.toNat_add_of_lt (by omega)
          have hsub_eq :
              (K.toNat + step.toNat - 1 - (w + step).toNat) + step.toNat =
                K.toNat + step.toNat - 1 - w.toNat := by
            rw [natural]; omega
          have hdiv_step :
              (K.toNat + step.toNat - 1 - w.toNat) / step.toNat =
                (K.toNat + step.toNat - 1 - (w + step).toNat) / step.toNat + 1 := by
            rw [← hsub_eq, Nat.add_div_right _ hpos]
          let n' := (K.toNat + step.toNat - 1 - (w + step).toNat) / step.toNat
          have hn' : n' + 1 = n := by omega
          have nextLimit : middle.locals.lookup limit = some (.val (.word K)) := by
            rw [frame (Or.inl rfl)]
            exact atLimit
          have decrease : n' * (cost + 1) + (cost + 1) = n * (cost + 1) := by
            rw [← Nat.succ_mul]; exact congrArg (· * (cost + 1)) hn'
          obtain ⟨t1, t2, t3⟩ := ih n' (by omega) middle (nextCode.trans code)
            (w + step) nextCounter nextLimit (by rw [natural]; omega) rfl (by omega)
          exact ⟨by omega, by omega, t3⟩
        | some r =>
          cases r with
          | «continue» => exact absurd rfl noCont
          | «break» => exact ⟨by simp; omega, by simp; omega, by simp⟩
          | timeOut => exact absurd rfl safe
          | _ => exact ⟨by simp; omega, by simp; omega, by simp⟩
    · rw [if_neg lt]
      simp

private theorem two_arg_lookup_n_local
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (fn p1 : MlS) (body : ProgHOL 64) (hp : p1 ≠ ofString "n")
    (hlookup_fn : code fn = some ([(p1, .one), (ofString "n", .one)], body, .one))
    {v1 : ValueHOL 64} {K : BitVec 64}
    {foundBody : ProgHOL 64} {locals : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hfound : PanSemStateFiniteExact.lookupCodeHOLFinite code fn [v1, .val (.word K)] =
      some (foundBody, locals, rs)) :
    foundBody = body ∧ locals.lookup (ofString "n") = some (.val (.word K)) := by
  have hbody := lookupCodeHOLFinite_installed_body code fn _ body foundBody .one rs
    [v1, .val (.word K)] locals hlookup_fn hfound
  refine ⟨hbody, ?_⟩
  cases v1 with
  | val wl =>
    cases wl with
    | word w1 =>
      rw [pan_two_word_lookup code fn p1 (ofString "n") body w1 K hp hlookup_fn] at hfound
      cases hfound
      simp [HolFiniteMapExact.lookup_update, FUPDATE]
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

private theorem evalListHOLFinite_two_word2_local {F : Type}
    (state : PanSemStateFiniteExact 64 F) (e1 e2 : ExpHOL 64) (K : BitVec 64) {vs : List (ValueHOL 64)}
    (hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [e1, e2] = some vs)
    (hk : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) e2 = some (.val (.word K))) :
    ∃ v1, vs = [v1, .val (.word K)] := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  rw [evalHOLFinite_eq_toExact] at hk
  simp only [evalListHOLExact] at hargs
  rw [hk] at hargs
  rcases h1 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) e1 with _ | v1
  · rw [h1] at hargs; cases hargs
  · rw [h1] at hargs; cases hargs; exact ⟨v1, rfl⟩

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

private theorem three_arg_lookup_n_local
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (fn p1 p2 : MlS) (body : ProgHOL 64)
    (hp12 : p1 ≠ p2) (hp1n : p1 ≠ ofString "n") (hp2n : p2 ≠ ofString "n")
    (hlookup_fn : code fn = some ([(p1, .one), (p2, .one), (ofString "n", .one)], body, .one))
    {v1 v2 : ValueHOL 64} {K : BitVec 64}
    {foundBody : ProgHOL 64} {locals : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hfound : PanSemStateFiniteExact.lookupCodeHOLFinite code fn [v1, v2, .val (.word K)] =
      some (foundBody, locals, rs)) :
    foundBody = body ∧ locals.lookup (ofString "n") = some (.val (.word K)) := by
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
          rw [pan_three_word_lookup code fn p1 p2 (ofString "n") body w1 w2 K hp12 hp1n hp2n hlookup_fn] at hfound
          cases hfound
          simp [HolFiniteMapExact.lookup_update, FUPDATE]

private theorem runBounded_notLowerStride_and_lowerTail_local {F : Type}
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
    {pre tail : ProgHOL 64} {preCost : Nat}
    (hpre : ProgBounded pre preCost)
    (hpre_i : avoidsLocal (ofString "i") pre = true)
    (hpre_n : avoidsLocal (ofString "n") pre = true)
    (htail : ProgBounded tail 0)
    (condAlign : ExpHOL 64)
    (hcode : state.code = originalRuntimeCode)
    (atN : state.locals.lookup (ofString "n") = some (.val (.word K)))
    (hbudget : preCost + K.toNat / 8 + 7 ≤ state.clock) :
    RunBounded state
      (.dec (ofString "i") .one (.const 0)
        (.seq
          (.ite condAlign
            (.seq pre
              (.seq
                (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 32])) b32)
                (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8])) b8a)))
            .skip)
          (.seq
            (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8])) b8b)
            (.seq
              (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) b1)
              tail))))
      (preCost + K.toNat / 8 + 7) := by
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
          (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 32])) b32)
          (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8])) b8a)))
      .skip
  have hfirst :
      ∃ c1 : Nat,
        s0.clock ≤ (evaluateHOLFiniteState s0 firstBranch).2.clock + c1 ∧
        (evaluateHOLFiniteState s0 firstBranch).2.clock ≤ s0.clock ∧
        (evaluateHOLFiniteState s0 firstBranch).1 ≠ some .timeOut ∧
        ((evaluateHOLFiniteState s0 firstBranch).1 ≠ none → c1 ≤ preCost + K.toNat / 8) ∧
        ((evaluateHOLFiniteState s0 firstBranch).1 = none →
          ∃ w1 : BitVec 64,
            (evaluateHOLFiniteState s0 firstBranch).2.locals.lookup (ofString "i") = some (.val (.word w1)) ∧
            (evaluateHOLFiniteState s0 firstBranch).2.locals.lookup (ofString "n") = some (.val (.word K)) ∧
            w1.toNat ≤ K.toNat ∧
            c1 + (K.toNat - w1.toNat) / 8 ≤ preCost + K.toNat / 8 ∧
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
          exact ⟨preCost, hpre_run.1, hpre_run.2.1, hpre_run.2.2, fun _ => by omega, fun h => by simp at h⟩
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
              (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 32])) b32)
              with ⟨res32, s2⟩
          rw [hr32] at h32
          dsimp only at h32 ⊢
          cases res32 with
          | some r =>
            dsimp only
            exact ⟨preCost + K.toNat / 32, by omega, by omega, h32.2.2.1, fun _ => by omega, fun h => by simp at h⟩
          | none =>
            dsimp only
            obtain ⟨w32, hw32_i, hw32_n, _, hw32_le, hw32_rem, hs2_code⟩ := h32.2.2.2 rfl
            have hw32_lt32 : K.toNat - w32.toNat < 32 := by
              change K.toNat < w32.toNat + 32 at hw32_rem
              omega
            have h8a := notLowerStrideWhile_run (ofString "i") (ofString "n") K 8
              (by change K.toNat + 8 < 2 ^ 64; omega) (by decide) hb8a hb8a_lim hb8a_nb
              ((K.toNat - w32.toNat) / 8) s2 (hs2_code.trans hs1_code) w32 hw32_i hw32_n hw32_le rfl
              (by
                have := hpre_run.1
                have := h32.1
                simp only [Nat.zero_add, Nat.mul_one] at *
                omega)
            rcases hr8a : evaluateHOLFiniteState s2
                (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8])) b8a)
                with ⟨res8a, s3⟩
            rw [hr8a] at h8a
            dsimp only at h8a ⊢
            have hc1_le : preCost + K.toNat / 32 + (K.toNat - w32.toNat) / 8 ≤ preCost + K.toNat / 8 := by
              omega
            refine ⟨preCost + K.toNat / 32 + (K.toNat - w32.toNat) / 8,
              by simp only [Nat.zero_add, Nat.mul_one] at h32 h8a; omega,
              by omega, h8a.2.2.1, fun _ => hc1_le, fun hnorm => ?_⟩
            obtain ⟨w8a, hw8a_i, hw8a_n, _, hw8a_le, hw8a_rem, hs3_code⟩ := h8a.2.2.2 hnorm
            have hw8a_lt8 : K.toNat - w8a.toNat < 8 := by
              change K.toNat < w8a.toNat + 8 at hw8a_rem
              omega
            exact ⟨w8a, hw8a_i, hw8a_n, hw8a_le, by omega, hs3_code.trans (hs2_code.trans hs1_code)⟩
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
        (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8])) b8b)
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
        (by
          simp only [Nat.zero_add, Nat.mul_one] at h8b ⊢
          omega)
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

private theorem runBounded_notLowerStride_noPre_local {F : Type}
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
              (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 32])) b32)
              (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8])) b8a))
            .skip)
          (.seq
            (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8])) b8b)
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
  have h := runBounded_notLowerStride_and_lowerTail_local state K hsmall
    hb32 hb32_lim hb32_nb hb8a hb8a_lim hb8a_nb hb8b hb8b_lim hb8b_nb hb1 hb1_lim
    (ProgBounded.straight .skip rfl) rfl rfl htail condAlign hcode atN
    (by simp only [Nat.zero_add]; exact hbudget)
  unfold RunBounded at h ⊢
  simp only [evaluateHOLFiniteState_dec_total, evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true,
    evaluateHOLFiniteState_seq_line780, hite, Nat.zero_add] at h ⊢
  exact h

private theorem evaluate_seq_reassoc3_local {F : Type}
    (s : PanSemStateFiniteExact 64 F) (p1 p2 p3 rest : ProgHOL 64) :
    evaluateHOLFiniteState s (.seq p1 (.seq p2 (.seq p3 rest))) =
      evaluateHOLFiniteState s (.seq (.seq p1 (.seq p2 p3)) rest) := by
  simp only [evaluateHOLFiniteState_seq_line780]
  rcases evaluateHOLFiniteState s p1 with ⟨_ | _, s1⟩ <;> dsimp only
  · rcases evaluateHOLFiniteState s1 p2 with ⟨_ | _, s2⟩ <;> rfl

private theorem runBounded_seq_ite_reassoc3_local {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (cost : Nat)
    (cond : ExpHOL 64) (p1 p2 p3 w32 w8 tailProg : ProgHOL 64)
    (hh : RunBounded s0 (.seq (.ite cond (.seq (.seq p1 (.seq p2 p3)) (.seq w32 w8)) .skip) tailProg) (0 + cost)) :
    RunBounded s0 (.seq (.ite cond (.seq p1 (.seq p2 (.seq p3 (.seq w32 w8)))) .skip) tailProg) cost := by
  have heq :
      evaluateHOLFiniteState s0 (.ite cond (.seq p1 (.seq p2 (.seq p3 (.seq w32 w8)))) .skip) =
      evaluateHOLFiniteState s0 (.ite cond (.seq (.seq p1 (.seq p2 p3)) (.seq w32 w8)) .skip) := by
    rw [evaluateHOLFiniteState_ite, evaluateHOLFiniteState_ite]
    split
    · split
      · rfl
      · exact evaluate_seq_reassoc3_local s0 p1 p2 p3 (.seq w32 w8)
    · rfl
  unfold RunBounded at hh ⊢
  rw [evaluateHOLFiniteState_seq_line780, heq]
  rw [evaluateHOLFiniteState_seq_line780, Nat.zero_add] at hh
  exact hh

private theorem runBounded_decConst_inv_local {F : Type}
    (state : PanSemStateFiniteExact 64 F) (name : MlS) (k : BitVec 64) {body : ProgHOL 64} {cost : Nat}
    (h : RunBounded state (.dec name .one (.const k) body) cost) :
    RunBounded (setVarHOLFinite name (.val (.word k)) state) body cost := by
  unfold RunBounded at h ⊢
  rw [evaluateHOLFiniteState_dec_total] at h
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true] at h
  exact h

theorem runBounded_memcpy {F : Type}
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
  exact runBounded_notLowerStride_noPre_local state K hsmall
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
    (ProgBounded.straight _ rfl) _ hcode atN hbudget

theorem progBounded_memcpy (destination : Option (VarKind × MlS)) (dst src sizeExp : ExpHOL 64)
    (M : Nat) (hsmall : M + 32 < 2 ^ 64)
    (heval : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      ∀ v, evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) sizeExp = some v →
        ∃ K : BitVec 64, v = .val (.word K) ∧ K.toNat ≤ M) :
    ProgBounded (.call (some (destination, none)) (ofString "memcpy") [dst, src, sizeExp]) (M / 8 + 8) := by
  intro F state hcode hbudget
  cases hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [dst, src, sizeExp] with
  | none =>
    rw [evaluateHOLFiniteState_call, hargs]
    simp
  | some vs =>
    have hex : ∃ v, evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) sizeExp = some v := by
      rw [evalListHOLFinite_eq_toExact] at hargs
      rw [evalHOLFinite_eq_toExact]
      rcases h1 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) dst with _ | v1
      · simp [evalListHOLExact, h1] at hargs
      · rcases h2 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) src with _ | v2
        · simp [evalListHOLExact, h1, h2] at hargs
        · rcases h3 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) sizeExp with _ | v3
          · simp [evalListHOLExact, h1, h2, h3] at hargs
          · exact ⟨v3, rfl⟩
    obtain ⟨v3, hv3⟩ := hex
    obtain ⟨K, rfl, hK_le⟩ := heval state v3 hv3
    have hK_div : K.toNat / 8 ≤ M / 8 := Nat.div_le_div_right hK_le
    obtain ⟨v1, v2, rfl⟩ := evalListHOLFinite_three_word3_local state dst src sizeExp K hargs hv3
    have h := RunBounded.call (destination := destination) (bodyCost := K.toNat / 8 + 7) hargs (by omega)
      (fun body locals rs hfound => by
        rw [hcode] at hfound
        obtain ⟨rfl, hn⟩ := three_arg_lookup_n_local originalRuntimeCode.lookup
          (ofString "memcpy") (ofString "dst") (ofString "src") (sourceFnBody Guest.Software.guestFn_memcpy)
          (by decide) (by decide) (by decide) lookup_memcpy hfound
        exact runBounded_memcpy (callEntryStateHOLFinite state locals) K (by omega) hcode hn
          (by change K.toNat / 8 + 7 ≤ state.clock - 1; omega))
    exact h.weaken (by omega)

theorem runBounded_memzero {F : Type}
    (state : PanSemStateFiniteExact 64 F) (K : BitVec 64)
    (hsmall : K.toNat + 32 < 2 ^ 64)
    (hcode : state.code = originalRuntimeCode)
    (atN : state.locals.lookup (ofString "n") = some (.val (.word K)))
    (hbudget : K.toNat / 8 + 7 ≤ state.clock) :
    RunBounded state (sourceFnBody Guest.Software.guestFn_memzero) (K.toNat / 8 + 7) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_memzero,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact runBounded_notLowerStride_noPre_local state K hsmall
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
    (ProgBounded.straight _ rfl) _ hcode atN hbudget

theorem progBounded_memzero (destination : Option (VarKind × MlS)) (dst sizeExp : ExpHOL 64)
    (M : Nat) (hsmall : M + 32 < 2 ^ 64)
    (heval : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      ∀ v, evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) sizeExp = some v →
        ∃ K : BitVec 64, v = .val (.word K) ∧ K.toNat ≤ M) :
    ProgBounded (.call (some (destination, none)) (ofString "memzero") [dst, sizeExp]) (M / 8 + 8) := by
  intro F state hcode hbudget
  cases hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [dst, sizeExp] with
  | none =>
    rw [evaluateHOLFiniteState_call, hargs]
    simp
  | some vs =>
    have hex : ∃ v, evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) sizeExp = some v := by
      rw [evalListHOLFinite_eq_toExact] at hargs
      rw [evalHOLFinite_eq_toExact]
      rcases h1 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) dst with _ | v1
      · simp [evalListHOLExact, h1] at hargs
      · rcases h2 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) sizeExp with _ | v2
        · simp [evalListHOLExact, h1, h2] at hargs
        · exact ⟨v2, rfl⟩
    obtain ⟨v2, hv2⟩ := hex
    obtain ⟨K, rfl, hK_le⟩ := heval state v2 hv2
    have hK_div : K.toNat / 8 ≤ M / 8 := Nat.div_le_div_right hK_le
    obtain ⟨v1, rfl⟩ := evalListHOLFinite_two_word2_local state dst sizeExp K hargs hv2
    have h := RunBounded.call (destination := destination) (bodyCost := K.toNat / 8 + 7) hargs (by omega)
      (fun body locals rs hfound => by
        rw [hcode] at hfound
        obtain ⟨rfl, hn⟩ := two_arg_lookup_n_local originalRuntimeCode.lookup
          (ofString "memzero") (ofString "dst") (sourceFnBody Guest.Software.guestFn_memzero)
          (by decide) lookup_memzero hfound
        exact runBounded_memzero (callEntryStateHOLFinite state locals) K (by omega) hcode hn
          (by change K.toNat / 8 + 7 ≤ state.clock - 1; omega))
    exact h.weaken (by omega)

theorem runBounded_memeq {F : Type}
    (state : PanSemStateFiniteExact 64 F) (K : BitVec 64)
    (hsmall : K.toNat + 32 < 2 ^ 64)
    (hcode : state.code = originalRuntimeCode)
    (atN : state.locals.lookup (ofString "n") = some (.val (.word K)))
    (hbudget : K.toNat / 8 + 7 ≤ state.clock) :
    RunBounded state (sourceFnBody Guest.Software.guestFn_memeq) (K.toNat / 8 + 7) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_memeq,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply RunBounded.decConst
  apply runBounded_seq_ite_reassoc3_local
  exact runBounded_decConst_inv_local state (ofString "i") 0
    (runBounded_notLowerStride_and_lowerTail_local state K hsmall
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
      (ProgBounded.straight _ rfl) rfl rfl (ProgBounded.straight _ rfl) _ hcode atN
      (by simp only [Nat.zero_add]; exact hbudget))

theorem progBounded_memeq (destination : Option (VarKind × MlS)) (a b sizeExp : ExpHOL 64)
    (M : Nat) (hsmall : M + 32 < 2 ^ 64)
    (heval : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      ∀ v, evalHOLFinite s (h := fun addr => Classical.propDecidable (s.memaddrs addr)) sizeExp = some v →
        ∃ K : BitVec 64, v = .val (.word K) ∧ K.toNat ≤ M) :
    ProgBounded (.call (some (destination, none)) (ofString "memeq") [a, b, sizeExp]) (M / 8 + 8) := by
  intro F state hcode hbudget
  cases hargs : evalListHOLFinite state (h := fun addr => Classical.propDecidable (state.memaddrs addr)) [a, b, sizeExp] with
  | none =>
    rw [evaluateHOLFiniteState_call, hargs]
    simp
  | some vs =>
    have hex : ∃ v, evalHOLFinite state (h := fun addr => Classical.propDecidable (state.memaddrs addr)) sizeExp = some v := by
      rw [evalListHOLFinite_eq_toExact] at hargs
      rw [evalHOLFinite_eq_toExact]
      rcases h1 : @evalHOLExact 64 F _ state.toExact (fun addr => Classical.propDecidable (state.memaddrs addr)) a with _ | v1
      · simp [evalListHOLExact, h1] at hargs
      · rcases h2 : @evalHOLExact 64 F _ state.toExact (fun addr => Classical.propDecidable (state.memaddrs addr)) b with _ | v2
        · simp [evalListHOLExact, h1, h2] at hargs
        · rcases h3 : @evalHOLExact 64 F _ state.toExact (fun addr => Classical.propDecidable (state.memaddrs addr)) sizeExp with _ | v3
          · simp [evalListHOLExact, h1, h2, h3] at hargs
          · exact ⟨v3, rfl⟩
    obtain ⟨v3, hv3⟩ := hex
    obtain ⟨K, rfl, hK_le⟩ := heval state v3 hv3
    have hK_div : K.toNat / 8 ≤ M / 8 := Nat.div_le_div_right hK_le
    obtain ⟨v1, v2, rfl⟩ := evalListHOLFinite_three_word3_local state a b sizeExp K hargs hv3
    have h := RunBounded.call (destination := destination) (bodyCost := K.toNat / 8 + 7) hargs (by omega)
      (fun body locals rs hfound => by
        rw [hcode] at hfound
        obtain ⟨rfl, hn⟩ := three_arg_lookup_n_local originalRuntimeCode.lookup
          (ofString "memeq") (ofString "a") (ofString "b") (sourceFnBody Guest.Software.guestFn_memeq)
          (by decide) (by decide) (by decide) lookup_memeq hfound
        exact runBounded_memeq (callEntryStateHOLFinite state locals) K (by omega) hcode hn
          (by change K.toNat / 8 + 7 ≤ state.clock - 1; omega))
    exact h.weaken (by omega)

private theorem shMemStore_locals_flowing {F : Type}
    (state : PanSemStateFiniteExact 64 F) (operator : OpSize)
    (address value : ExpHOL 64)
    (hnone : (evaluateHOLFiniteState state (.shMemStore operator address value)).1 = none) :
    (evaluateHOLFiniteState state (.shMemStore operator address value)).2.locals = state.locals := by
  classical
  rw [evaluateHOLFiniteState_shMemStore_total] at hnone ⊢
  dsimp only at hnone ⊢
  split at hnone ⊢
  · change (shMemStoreHOLExact state.toExact _ _ (nbOpHOL operator)).2.locals = state.locals
    change (shMemStoreHOLExact state.toExact _ _ (nbOpHOL operator)).1 = none at hnone
    unfold shMemStoreHOLExact at hnone ⊢
    split at hnone ⊢ <;> split at hnone ⊢
    all_goals first | rfl | simp at hnone | (split at hnone ⊢ <;> first | rfl | simp at hnone)
  · simp at hnone

private theorem shMemLoad_local_other_locals {F : Type}
    (state : PanSemStateFiniteExact 64 F) (operator : OpSize)
    (name : MlS) (address : ExpHOL 64) (key : MlS) (hne : name ≠ key)
    (hnone : (evaluateHOLFiniteState state (.shMemLoad operator .local name address)).1 = none) :
    (evaluateHOLFiniteState state (.shMemLoad operator .local name address)).2.locals.lookup key =
      state.locals.lookup key := by
  classical
  rw [evaluateHOLFiniteState_shMemLoad_source] at hnone ⊢
  split at hnone ⊢
  · split at hnone ⊢
    · unfold shMemLoadHOLFiniteExact at hnone ⊢
      dsimp only at hnone ⊢
      split at hnone ⊢
      · split at hnone ⊢
        · split at hnone ⊢
          · simp [setKvarFfiHOLFinite, setKvarHOLFinite, setVarHOLFinite,
              HolFiniteMapExact.lookup_update, FUPDATE, hne]
          · simp at hnone
        · simp at hnone
      · simp at hnone
    · simp at hnone
  · simp at hnone

private theorem shMemLoad_no_break {F : Type}
    (state : PanSemStateFiniteExact 64 F) (operator : OpSize)
    (vk : VarKind) (name : MlS) (address : ExpHOL 64) :
    (evaluateHOLFiniteState state (.shMemLoad operator vk name address)).1 ≠ some .break := by
  classical
  cases vk with
  | «local» =>
    rw [evaluateHOLFiniteState_shMemLoad_source]
    split
    · split
      · unfold shMemLoadHOLFiniteExact; dsimp only
        split
        · split
          · split <;> simp
          · simp
        · simp
      · simp
    · simp
  | global =>
    rw [evaluateHOLFiniteState_shMemLoad_source]
    split
    · split
      · unfold shMemLoadHOLFiniteExact; dsimp only
        split
        · split
          · split <;> simp
          · simp
        · simp
      · simp
    · simp

private theorem shMemStore_no_break {F : Type}
    (state : PanSemStateFiniteExact 64 F) (operator : OpSize)
    (address value : ExpHOL 64) :
    (evaluateHOLFiniteState state (.shMemStore operator address value)).1 ≠ some .break := by
  classical
  rw [evaluateHOLFiniteState_shMemStore_total]
  dsimp only
  split
  · change (shMemStoreHOLExact state.toExact _ _ (nbOpHOL operator)).1 ≠ some .break
    unfold shMemStoreHOLExact
    split <;> split
    all_goals first | simp | (split <;> simp)
  · simp

theorem funBounded_input_blob : FunBounded (ofString "input_blob") 134217728 := by
  refine funBounded_of_guestAst 29 (by rw [guestAst_len]; decide) Guest.Software.guestFn_input_blob 134217728 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_input_blob,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  intro F state hcode hbudget
  apply RunBounded.decConst
  set s0 := setVarHOLFinite (ofString "len") (.val (.word 0)) state
  have hs0_code : s0.code = originalRuntimeCode := hcode
  have hs0_clk : s0.clock = state.clock := rfl
  refine (RunBounded.seq (state := s0) (a := 0) (b := 134217728)
    ((ProgBounded.straight _ rfl) s0 hs0_code (Nat.zero_le _)) (by omega) ?_).weaken (by omega)
  intro s1 _ hs1_code hs1_clk
  have hs1_code' : s1.code = originalRuntimeCode := hs1_code.trans hs0_code
  unfold RunBounded
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
  split
  · rename_i wcond hcond
    split
    · rename_i hwz
      rw [evaluateHOLFiniteState_skip]
      dsimp only
      have hlen_val : ∃ K : BitVec 64,
          s1.locals.lookup (ofString "len") = some (.val (.word K)) ∧ K.toNat ≤ 1073741808 := by
        simp only [evalHOLExact] at hcond
        cases hlook : s1.locals.lookup (ofString "len") with
        | none => simp [hlook, Compiler.Encoders.Asm.wordCmpHOL] at hcond
        | some lv =>
          cases lv with
          | rStruct _ => simp [hlook, Compiler.Encoders.Asm.wordCmpHOL] at hcond
          | nStruct _ _ => simp [hlook, Compiler.Encoders.Asm.wordCmpHOL] at hcond
          | val lwl =>
            cases lwl with
            | word K =>
              refine ⟨K, rfl, ?_⟩
              simp only [hlook, Compiler.Encoders.Asm.wordCmpHOL] at hcond
              injection hcond with hv
              injection hv with hwl
              injection hwl with hwc
              subst hwc
              by_cases hlt : (1073741808#64) < K
              · simp [hlt] at hwz
              · simp only [BitVec.lt_def, Nat.not_lt] at hlt
                simpa using hlt
      obtain ⟨K, hs1_len, hK_le⟩ := hlen_val
      have hargs : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
          [.op .add [.var .local (ofString "len"), .const 8]] = some [.val (.word (K + 8))] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, hs1_len, valueIsWord, valueWord,
          wordOpHOL, wordOp, BitVec.add_zero]
      have hdec := RunBounded.decCall (state := s1) (name := ofString "p") (shape := .one)
        (function := ofString "alloc") (bodyCost := 1) (tailCost := 134217726) hargs (by omega)
        (fun body locals rs hfound => by
          have hbodies := ProgBounded.bodies_of_fun funBounded_alloc s1 hs1_code' (by omega)
            [.val (.word (K + 8))] body locals rs hfound
          have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s1 locals) body
          refine ⟨hbodies, ?_⟩
          intro pval post hran hpost_clk
          rw [hran] at hmeta
          have hpost_code : (setVarHOLFinite (ofString "p") pval { post with locals := s1.locals }).code =
              originalRuntimeCode := hmeta.1.trans hs1_code'
          apply RunBounded.decConst
          apply RunBounded.decConst
          let sw := setVarHOLFinite (ofString "w") (.val (.word (0#64)))
            (setVarHOLFinite (ofString "i") (.val (.word (0#64)))
              (setVarHOLFinite (ofString "p") pval { post with locals := s1.locals }))
          change RunBounded sw _ _
          have hsw_clk : sw.clock = post.clock := rfl
          have hsw_code : sw.code = originalRuntimeCode := hpost_code
          have hsw_i : sw.locals.lookup (ofString "i") = some (.val (.word 0)) := by
            simp [sw, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hsw_len : sw.locals.lookup (ofString "len") = some (.val (.word K)) := by
            have hne1 : ofString "w" ≠ ofString "len" := by decide
            have hne2 : ofString "i" ≠ ofString "len" := by decide
            have hne3 : ofString "p" ≠ ofString "len" := by decide
            simp [sw, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne1, hne2, hne3, hs1_len]
          let Rank : ∀ {G : Type}, PanSemStateFiniteExact 64 G → Nat → Prop :=
            fun s n => ∃ w : BitVec 64,
              s.locals.lookup (ofString "i") = some (.val (.word w)) ∧
              s.locals.lookup (ofString "len") = some (.val (.word K)) ∧
              w.toNat < K.toNat + 8 ∧
              (K.toNat + 7 - w.toNat) / 8 = n
          let loopBody : ProgHOL 64 :=
            .seq
              (.shMemLoad .opW .local (ofString "w") (.op .add [.const 1073741840#64, .var .local (ofString "i")]))
              (.seq
                (.store (.op .add [.var .local (ofString "p"), .var .local (ofString "i")]) (.var .local (ofString "w")))
                (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8#64])))
          have hexit : ∀ {G : Type} (s : PanSemStateFiniteExact 64 G), Rank s 0 → ∀ wc : BitVec 64,
              evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
                (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "len"))) = some (.val (.word wc)) →
              wc = 0 := by
            intro G s ⟨w, hwi, hwlen, _, hdiv⟩ wc hev
            have hcond_ev := eval_variable_stride_condition s (ofString "i") (ofString "len") .lower
              (Or.inr rfl) K w (fun h => by cases h) hwi hwlen
            rw [hcond_ev] at hev
            injection hev with hv
            injection hv with hwl
            injection hwl with hwc
            subst hwc
            have hge : ¬ w.toNat < K.toNat := by
              intro hlt
              have hpos8 : 0 < 8 := by decide
              have hge8 : 8 ≤ K.toNat + 7 - w.toNat := by omega
              have := Nat.div_pos hge8 hpos8
              omega
            simp [hge]
          have hstep : ∀ {G : Type} (s : PanSemStateFiniteExact 64 G) (n : Nat) (wc : BitVec 64),
              s.code = originalRuntimeCode → Rank s (n + 1) →
              evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
                (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "len"))) = some (.val (.word wc)) →
              wc ≠ 0 → 0 + 1 ≤ s.clock →
              s.clock - 1 ≤ (evaluateHOLFiniteState (decClockHOLFinite s) loopBody).2.clock + 0 ∧
                (evaluateHOLFiniteState (decClockHOLFinite s) loopBody).2.clock ≤ s.clock - 1 ∧
                (evaluateHOLFiniteState (decClockHOLFinite s) loopBody).1 ≠ some .timeOut ∧
                ((evaluateHOLFiniteState (decClockHOLFinite s) loopBody).1 = none ∨
                    (evaluateHOLFiniteState (decClockHOLFinite s) loopBody).1 = some .continue →
                  ∃ m, m ≤ n ∧ Rank (evaluateHOLFiniteState (decClockHOLFinite s) loopBody).2 m ∧
                    (evaluateHOLFiniteState (decClockHOLFinite s) loopBody).2.code = s.code) ∧
                ((evaluateHOLFiniteState (decClockHOLFinite s) loopBody).1 = some .break → False ∧
                  ∃ m, Rank (evaluateHOLFiniteState (decClockHOLFinite s) loopBody).2 m ∧
                    (evaluateHOLFiniteState (decClockHOLFinite s) loopBody).2.code = s.code) := by
            intro G s n wc hs_code ⟨w, hwi, hwlen, hw_lt, hdiv⟩ hev hwc_nz hclk1
            have hcond_ev := eval_variable_stride_condition s (ofString "i") (ofString "len") .lower
              (Or.inr rfl) K w (fun h => by cases h) hwi hwlen
            rw [hcond_ev] at hev
            have hlt : w.toNat < K.toNat := by
              by_cases h : w.toNat < K.toNat
              · exact h
              · simp [h] at hev; exact absurd hev.symm hwc_nz
            have hb_run := (ProgBounded.straight loopBody rfl) (decClockHOLFinite s) hs_code (Nat.zero_le _)
            have hb_nc := evaluate_noTopContinue loopBody rfl (decClockHOLFinite s)
            have hb_nb : (evaluateHOLFiniteState (decClockHOLFinite s) loopBody).1 ≠ some .break := by
              dsimp only [loopBody]
              rw [evaluateHOLFiniteState_seq_line780]
              have hnb1 := shMemLoad_no_break (decClockHOLFinite s) .opW .local (ofString "w")
                (.op .add [.const 1073741840#64, .var .local (ofString "i")])
              rcases h1 : evaluateHOLFiniteState (decClockHOLFinite s)
                  (.shMemLoad .opW .local (ofString "w") (.op .add [.const 1073741840#64, .var .local (ofString "i")]))
                  with ⟨r1, s_mid⟩
              rw [h1] at hnb1
              cases r1 with
              | none => exact evaluate_noTopBreak _ rfl s_mid
              | some _ => exact hnb1
            have hb_meta := PanRunBounded.evaluateHOLFiniteState_metadata (decClockHOLFinite s) loopBody
            refine ⟨hb_run.1, hb_run.2.1, hb_run.2.2, ?_, fun hbr => absurd hbr hb_nb⟩
            intro hflow
            have hnorm : (evaluateHOLFiniteState (decClockHOLFinite s) loopBody).1 = none := by
              rcases hflow with h | h
              · exact h
              · exact absurd h hb_nc
            dsimp only [loopBody] at hnorm hb_meta ⊢
            rw [evaluateHOLFiniteState_seq_line780] at hnorm ⊢
            rcases hld : evaluateHOLFiniteState (decClockHOLFinite s)
                (.shMemLoad .opW .local (ofString "w") (.op .add [.const 1073741840#64, .var .local (ofString "i")]))
                with ⟨rld, sld⟩
            have hsld_i := shMemLoad_local_other_locals (decClockHOLFinite s) .opW (ofString "w")
              (.op .add [.const 1073741840#64, .var .local (ofString "i")]) (ofString "i") (by decide)
            have hsld_len := shMemLoad_local_other_locals (decClockHOLFinite s) .opW (ofString "w")
              (.op .add [.const 1073741840#64, .var .local (ofString "i")]) (ofString "len") (by decide)
            have hsld_meta := PanRunBounded.evaluateHOLFiniteState_metadata (decClockHOLFinite s)
              (.shMemLoad .opW .local (ofString "w") (.op .add [.const 1073741840#64, .var .local (ofString "i")]))
            rw [hld] at hnorm hsld_i hsld_len hsld_meta
            cases rld with
            | some r => simp at hnorm
            | none =>
              dsimp only at hnorm hsld_i hsld_len hsld_meta ⊢
              have hsld_i' : sld.locals.lookup (ofString "i") = some (.val (.word w)) :=
                (hsld_i rfl).trans hwi
              have hsld_len' : sld.locals.lookup (ofString "len") = some (.val (.word K)) :=
                (hsld_len rfl).trans hwlen
              have hcb_tail : CountedBody (ofString "i") 8
                  (.seq
                    (.store (.op .add [.var .local (ofString "p"), .var .local (ofString "i")]) (.var .local (ofString "w")))
                    (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8#64]))) 0 :=
                countedBody_seq_straight _ rfl rfl rfl CountedBody.incr
              have htail_run := hcb_tail.run sld (hsld_meta.1.trans hs_code) w hsld_i' (Nat.zero_le _)
              have htail_len := evaluate_avoidsLocal_flowing (ofString "len") _
                (rfl : avoidsLocal (ofString "len")
                  (.seq
                    (.store (.op .add [.var .local (ofString "p"), .var .local (ofString "i")]) (.var .local (ofString "w")))
                    (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8#64]))) = true) sld
              obtain ⟨hnext_i, hnext_code⟩ := htail_run.2.2.2.2 hnorm
              have hnext_len : (evaluateHOLFiniteState sld _).2.locals.lookup (ofString "len") =
                  some (.val (.word K)) := (htail_len (Or.inl hnorm)).trans hsld_len'
              have hnat : (w + 8#64).toNat = w.toNat + 8 := BitVec.toNat_add_of_lt (by change w.toNat + 8 < 2 ^ 64; omega)
              have hsub_eq : (K.toNat + 7 - (w + 8#64).toNat) + 8 = K.toNat + 7 - w.toNat := by
                rw [hnat]; omega
              have hdiv_step : (K.toNat + 7 - w.toNat) / 8 = (K.toNat + 7 - (w + 8#64).toNat) / 8 + 1 := by
                rw [← hsub_eq, Nat.add_div_right _ (by decide)]
              exact ⟨n, le_refl _, ⟨w + 8#64, hnext_i, hnext_len, by rw [hnat]; omega, by omega⟩,
                hnext_code.trans hsld_meta.1⟩
          have hn0_le : (K.toNat + 7 - 0) / 8 ≤ 134217726 := by omega
          have hrank0 : Rank sw ((K.toNat + 7 - 0) / 8) :=
            ⟨0, hsw_i, hsw_len, by change 0 < K.toNat + 8; omega, rfl⟩
          have hw_run := rankedWhile_run
            (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "len")))
            loopBody 0 Rank False hexit hstep ((K.toNat + 7 - 0) / 8) sw hsw_code hrank0
            (by simp only [Nat.zero_add, Nat.mul_one]; omega)
          refine (RunBounded.seq (state := sw) (a := (K.toNat + 7 - 0) / 8) (b := 0)
            (tail := .return (.rstruct [.var .local (ofString "p"), .var .local (ofString "len")]))
            ⟨by simpa using hw_run.1, hw_run.2.1, hw_run.2.2.1⟩ (by omega) ?_).weaken (by omega)
          intro s_end _ hs_end_code _
          exact (ProgBounded.straight _ rfl) s_end (hs_end_code.trans hsw_code) (Nat.zero_le _))
      exact hdec
    · have hcall := ProgBounded.call funBounded_trap_with none [.const 8#64] s1 hs1_code' (by omega)
      have hnonone := evaluate_call_trap_with_no_none s1 (8#64) hs1_code'
      rcases hrun : evaluateHOLFiniteState s1 (.call (some (none, none)) (ofString "trap_with") [.const 8#64]) with ⟨res, post⟩
      rw [hrun] at hcall hnonone
      cases res with
      | none => exact absurd rfl hnonone
      | some r =>
        dsimp only at hcall ⊢
        exact ⟨by omega, hcall.2.1, hcall.2.2⟩
  · simp

theorem funBounded_output_write : FunBounded (ofString "output_write") (2 ^ 64 - 1) := by
  refine funBounded_of_guestAst 30 (by rw [guestAst_len]; decide) Guest.Software.guestFn_output_write (2 ^ 64 - 1) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_output_write,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  intro F state hcode hbudget
  apply RunBounded.decConst
  let s0 := setVarHOLFinite (ofString "i") (.val (.word (0#64))) state
  change RunBounded s0 _ _
  have hs0_code : s0.code = originalRuntimeCode := hcode
  have hs0_clk : s0.clock = state.clock := rfl
  have hs0_i : s0.locals.lookup (ofString "i") = some (.val (.word 0)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  cases hn : s0.locals.lookup (ofString "n") with
  | none =>
    unfold RunBounded
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total]
    have hcond : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) = none := by
      rw [evalHOLFinite_eq_toExact]
      simp [evalHOLExact, hs0_i, hn]
    rw [hcond]
    simp
  | some vn =>
    cases vn with
    | rStruct _ =>
      unfold RunBounded
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total]
      have hcond : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
          (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) = none := by
        rw [evalHOLFinite_eq_toExact]
        simp [evalHOLExact, hs0_i, hn]
      rw [hcond]
      simp
    | nStruct _ _ =>
      unfold RunBounded
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total]
      have hcond : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
          (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) = none := by
        rw [evalHOLFinite_eq_toExact]
        simp [evalHOLExact, hs0_i, hn]
      rw [hcond]
      simp
    | val wl =>
      cases wl with
      | word K =>
        let Rank : ∀ {G : Type}, PanSemStateFiniteExact 64 G → Nat → Prop :=
          fun s n => ∃ w : BitVec 64,
            s.locals.lookup (ofString "i") = some (.val (.word w)) ∧
            s.locals.lookup (ofString "n") = some (.val (.word K)) ∧
            w.toNat ≤ K.toNat ∧
            K.toNat - w.toNat = n
        let loopBody : ProgHOL 64 :=
          .seq
            (.shMemStore .op8 (.op .add [.const 2688614400#64, .var .local (ofString "i")])
              (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
            (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64]))
        have hexit : ∀ {G : Type} (s : PanSemStateFiniteExact 64 G), Rank s 0 → ∀ wc : BitVec 64,
            evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
              (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) = some (.val (.word wc)) →
            wc = 0 := by
          intro G s ⟨w, hwi, hwn, _, hsub⟩ wc hev
          have hcond_ev := eval_variable_stride_condition s (ofString "i") (ofString "n") .lower
            (Or.inr rfl) K w (fun h => by cases h) hwi hwn
          rw [hcond_ev] at hev
          injection hev with hv
          injection hv with hwl
          injection hwl with hwc
          subst hwc
          have hge : ¬ w.toNat < K.toNat := by omega
          simp [hge]
        have hstep : ∀ {G : Type} (s : PanSemStateFiniteExact 64 G) (n : Nat) (wc : BitVec 64),
            s.code = originalRuntimeCode → Rank s (n + 1) →
            evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
              (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) = some (.val (.word wc)) →
            wc ≠ 0 → 0 + 1 ≤ s.clock →
            s.clock - 1 ≤ (evaluateHOLFiniteState (decClockHOLFinite s) loopBody).2.clock + 0 ∧
              (evaluateHOLFiniteState (decClockHOLFinite s) loopBody).2.clock ≤ s.clock - 1 ∧
              (evaluateHOLFiniteState (decClockHOLFinite s) loopBody).1 ≠ some .timeOut ∧
              ((evaluateHOLFiniteState (decClockHOLFinite s) loopBody).1 = none ∨
                  (evaluateHOLFiniteState (decClockHOLFinite s) loopBody).1 = some .continue →
                ∃ m, m ≤ n ∧ Rank (evaluateHOLFiniteState (decClockHOLFinite s) loopBody).2 m ∧
                  (evaluateHOLFiniteState (decClockHOLFinite s) loopBody).2.code = s.code) ∧
              ((evaluateHOLFiniteState (decClockHOLFinite s) loopBody).1 = some .break → False ∧
                ∃ m, Rank (evaluateHOLFiniteState (decClockHOLFinite s) loopBody).2 m ∧
                  (evaluateHOLFiniteState (decClockHOLFinite s) loopBody).2.code = s.code) := by
          intro G s n wc hs_code ⟨w, hwi, hwn, _, hsub⟩ hev hwc_nz _
          have hcond_ev := eval_variable_stride_condition s (ofString "i") (ofString "n") .lower
            (Or.inr rfl) K w (fun h => by cases h) hwi hwn
          rw [hcond_ev] at hev
          have hlt : w.toNat < K.toNat := by
            by_cases h : w.toNat < K.toNat
            · exact h
            · simp [h] at hev; exact absurd hev.symm hwc_nz
          have hb_run := (ProgBounded.straight loopBody rfl) (decClockHOLFinite s) hs_code (Nat.zero_le _)
          have hb_nc := evaluate_noTopContinue loopBody rfl (decClockHOLFinite s)
          have hb_nb : (evaluateHOLFiniteState (decClockHOLFinite s) loopBody).1 ≠ some .break := by
            dsimp only [loopBody]
            rw [evaluateHOLFiniteState_seq_line780]
            have hnb1 := shMemStore_no_break (decClockHOLFinite s) .op8
              (.op .add [.const 2688614400#64, .var .local (ofString "i")])
              (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")]))
            rcases h1 : evaluateHOLFiniteState (decClockHOLFinite s)
                (.shMemStore .op8 (.op .add [.const 2688614400#64, .var .local (ofString "i")])
                  (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
                with ⟨r1, s_mid⟩
            rw [h1] at hnb1
            cases r1 with
            | none => exact evaluate_noTopBreak _ rfl s_mid
            | some _ => exact hnb1
          refine ⟨hb_run.1, hb_run.2.1, hb_run.2.2, ?_, fun hbr => absurd hbr hb_nb⟩
          intro hflow
          have hnorm : (evaluateHOLFiniteState (decClockHOLFinite s) loopBody).1 = none := by
            rcases hflow with h | h
            · exact h
            · exact absurd h hb_nc
          dsimp only [loopBody] at hnorm ⊢
          rw [evaluateHOLFiniteState_seq_line780] at hnorm ⊢
          rcases hst : evaluateHOLFiniteState (decClockHOLFinite s)
              (.shMemStore .op8 (.op .add [.const 2688614400#64, .var .local (ofString "i")])
                (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
              with ⟨rst, sst⟩
          have hsst_loc := shMemStore_locals_flowing (decClockHOLFinite s) .op8
            (.op .add [.const 2688614400#64, .var .local (ofString "i")])
            (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")]))
          have hsst_meta := PanRunBounded.evaluateHOLFiniteState_metadata (decClockHOLFinite s)
            (.shMemStore .op8 (.op .add [.const 2688614400#64, .var .local (ofString "i")])
              (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
          rw [hst] at hnorm hsst_loc hsst_meta
          cases rst with
          | some r => simp at hnorm
          | none =>
            dsimp only at hnorm hsst_loc hsst_meta ⊢
            have hsst_loc' := hsst_loc rfl
            have hsst_i : sst.locals.lookup (ofString "i") = some (.val (.word w)) := by
              rw [hsst_loc']; exact hwi
            have hsst_n : sst.locals.lookup (ofString "n") = some (.val (.word K)) := by
              rw [hsst_loc']; exact hwn
            have hcb_inc : CountedBody (ofString "i") 1
                (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64])) 0 :=
              CountedBody.incr
            have hinc_run := hcb_inc.run sst (hsst_meta.1.trans hs_code) w hsst_i (Nat.zero_le _)
            have hinc_n := evaluate_avoidsLocal_flowing (ofString "n")
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64])) rfl sst
            obtain ⟨hnext_i, hnext_code⟩ := hinc_run.2.2.2.2 hnorm
            have hnext_n : (evaluateHOLFiniteState sst _).2.locals.lookup (ofString "n") =
                some (.val (.word K)) := (hinc_n (Or.inl hnorm)).trans hsst_n
            have hK_bound := K.isLt
            have hnat : (w + 1#64).toNat = w.toNat + 1 := BitVec.toNat_add_of_lt (by change w.toNat + 1 < 2 ^ 64; omega)
            exact ⟨n, le_refl _, ⟨w + 1#64, hnext_i, hnext_n, by rw [hnat]; omega, by rw [hnat]; omega⟩,
              hnext_code.trans hsst_meta.1⟩
        have hK_le : K.toNat ≤ 2 ^ 64 - 1 := by have := K.isLt; omega
        have hrank0 : Rank s0 K.toNat := ⟨0, hs0_i, hn, by simp, by simp⟩
        have hw := rankedWhile_run
          (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n")))
          loopBody 0 Rank False hexit hstep K.toNat s0 hs0_code hrank0
          (by simp only [Nat.zero_add, Nat.mul_one]; omega)
        refine (RunBounded.seq (state := s0) (a := K.toNat) (b := 0)
          (tail := .return (.const 0#64))
          ⟨by simpa using hw.1, hw.2.1, hw.2.2.1⟩ (by omega) ?_).weaken (by omega)
        intro s_end _ hs_end_code _
        exact (ProgBounded.straight _ rfl) s_end (hs_end_code.trans hs0_code) (Nat.zero_le _)

private theorem eval_zero_lt_condition {F : Type} (state : PanSemStateFiniteExact 64 F) (counter : MlS)
    (w : BitVec 64) (atCounter : state.locals.lookup counter = some (.val (.word w))) :
    evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      (.cmp .lower (.const 0) (.var .local counter)) =
      some (.val (.word (if 0 < w.toNat then 1 else 0))) := by
  rw [evalHOLFinite_eq_toExact]
  simp only [evalHOLExact, atCounter, Compiler.Encoders.Asm.wordCmpHOL]
  by_cases lt : 0 < w.toNat <;> simp [lt, BitVec.lt_def]

private theorem downWhile_seq_decr_run (counter : MlS) {first : ProgHOL 64} {cost : Nat}
    (hfirst : ProgBounded first cost)
    (havoid : avoidsLocal counter first = true)
    (hnoCont : noTopContinue first = true) :
    ∀ n : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.code = originalRuntimeCode →
      ∀ w : BitVec 64, state.locals.lookup counter = some (.val (.word w)) →
      w.toNat ≤ n → n * (cost + 1) ≤ state.clock →
      let loop := ProgHOL.while (.cmp .lower (.const 0) (.var .local counter))
        (.seq first (.assign .local counter (.op .sub [.var .local counter, .const 1])))
      state.clock ≤ (evaluateHOLFiniteState state loop).2.clock + n * (cost + 1) ∧
        (evaluateHOLFiniteState state loop).2.clock ≤ state.clock ∧
        (evaluateHOLFiniteState state loop).1 ≠ some .timeOut := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro F state code w atCounter within budget
    have condition := eval_zero_lt_condition state counter w atCounter
    dsimp only
    rw [evaluateHOLFiniteState_while_total, condition]
    by_cases lt : 0 < w.toNat
    · rw [if_pos lt]
      simp only [show (1 : BitVec 64) ≠ 0 by decide, if_true, ne_eq, not_false_eq_true]
      have positiveRank : 0 < n := by omega
      have oneIteration : cost + 1 ≤ n * (cost + 1) := Nat.le_mul_of_pos_left _ positiveRank
      have clock : state.clock ≠ 0 := by omega
      rw [if_neg clock, fixClockHOLFinite_evaluateState]
      let s1 := decClockHOLFinite state
      have hfirst_run := hfirst s1 code (by change cost ≤ state.clock - 1; omega)
      have hframe := evaluate_avoidsLocal_flowing counter first havoid s1
      have hnc := evaluate_noTopContinue first hnoCont s1
      have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata s1 first
      rw [evaluateHOLFiniteState_seq_line780]
      cases firstRun : evaluateHOLFiniteState s1 first with
      | mk result middle =>
        rw [firstRun] at hfirst_run hframe hnc hmeta
        dsimp only at hfirst_run hframe hnc hmeta
        obtain ⟨spent, kept, safe⟩ := hfirst_run
        change state.clock - 1 ≤ middle.clock + cost at spent
        change middle.clock ≤ state.clock - 1 at kept
        cases result with
        | none =>
          dsimp only
          have hmid_cnt : middle.locals.lookup counter = some (.val (.word w)) :=
            (hframe (Or.inl rfl)).trans atCounter
          have hdecr : evaluateHOLFiniteState middle
              (.assign .local counter (.op .sub [.var .local counter, .const 1])) =
              (none, setVarHOLFinite counter (.val (.word (w - 1))) middle) := by
            simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hmid_cnt,
              wordOpHOL, wordOp, valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact,
              setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
          rw [hdecr]
          dsimp only
          let s2 := setVarHOLFinite counter (.val (.word (w - 1))) middle
          have hs2_cnt : s2.locals.lookup counter = some (.val (.word (w - 1))) := by
            simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have one_toNat : (1 : BitVec 64).toNat = 1 := rfl
          have hle : (1 : BitVec 64) ≤ w := by rw [BitVec.le_def, one_toNat]; omega
          have natural : (w - 1).toNat = w.toNat - 1 := by
            rw [BitVec.toNat_sub_of_le hle, one_toNat]
          have hmul : (n - 1) * (cost + 1) + (cost + 1) = n * (cost + 1) := by
            calc (n - 1) * (cost + 1) + (cost + 1) = (n - 1 + 1) * (cost + 1) := by
                  rw [Nat.add_mul, Nat.one_mul]
              _ = n * (cost + 1) := by rw [show n - 1 + 1 = n by omega]
          have tail := ih (n - 1) (by omega) s2 (hmeta.1.trans code)
            (w - 1) hs2_cnt (by rw [natural]; omega) (by change (n - 1) * (cost + 1) ≤ middle.clock; omega)
          obtain ⟨t1, t2, t3⟩ := tail
          exact ⟨by omega, by omega, t3⟩
        | some r =>
          cases r with
          | «continue» => exact absurd rfl hnc
          | «break» => exact ⟨by simp; omega, by simp; omega, by simp⟩
          | timeOut => exact absurd rfl safe
          | _ => exact ⟨by simp; omega, by simp; omega, by simp⟩
    · rw [if_neg lt]
      simp

private theorem eval_zero_less_condition {F : Type}
    (state : PanSemStateFiniteExact 64 F) (counter : MlS)
    (w : BitVec 64) (hw : w.toNat < 2 ^ 63)
    (atCounter : state.locals.lookup counter = some (.val (.word w))) :
    evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      (.cmp .less (.const 0) (.var .local counter)) =
      some (.val (.word (if 0 < w.toNat then 1 else 0))) := by
  rw [evalHOLFinite_eq_toExact]
  simp only [evalHOLExact, atCounter, Compiler.Encoders.Asm.wordCmpHOL,
    holAsmSignedLess_small 0 w (by decide) hw]
  by_cases lt : 0 < w.toNat <;> simp [lt]

private theorem downLessWhile_decrFirst_run (counter : MlS) {rest : ProgHOL 64} {cost : Nat}
    (hrest : ProgBounded rest cost)
    (havoid : avoidsLocal counter rest = true)
    (hnoCont : noTopContinue rest = true) :
    ∀ n : Nat, n < 2 ^ 63 →
      ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.code = originalRuntimeCode →
      ∀ w : BitVec 64, state.locals.lookup counter = some (.val (.word w)) →
      w.toNat ≤ n → n * (cost + 1) ≤ state.clock →
      let loop := ProgHOL.while (.cmp .less (.const 0) (.var .local counter))
        (.seq (.assign .local counter (.op .sub [.var .local counter, .const 1])) rest)
      state.clock ≤ (evaluateHOLFiniteState state loop).2.clock + n * (cost + 1) ∧
        (evaluateHOLFiniteState state loop).2.clock ≤ state.clock ∧
        (evaluateHOLFiniteState state loop).1 ≠ some .timeOut := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn_lt F state code w atCounter within budget
    have condition := eval_zero_less_condition state counter w (by omega) atCounter
    dsimp only
    rw [evaluateHOLFiniteState_while_total, condition]
    by_cases lt : 0 < w.toNat
    · rw [if_pos lt]
      simp only [show (1 : BitVec 64) ≠ 0 by decide, if_true, ne_eq, not_false_eq_true]
      have positiveRank : 0 < n := by omega
      have oneIteration : cost + 1 ≤ n * (cost + 1) := Nat.le_mul_of_pos_left _ positiveRank
      have clock : state.clock ≠ 0 := by omega
      rw [if_neg clock, fixClockHOLFinite_evaluateState]
      let s1 := decClockHOLFinite state
      have hs1_decr : evaluateHOLFiniteState s1
          (.assign .local counter (.op .sub [.var .local counter, .const 1])) =
          (none, setVarHOLFinite counter (.val (.word (w - 1))) s1) := by
        simp [s1, evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, atCounter,
          wordOpHOL, wordOp, valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact,
          setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
      rw [evaluateHOLFiniteState_seq_line780, hs1_decr]
      dsimp only
      let s2 := setVarHOLFinite counter (.val (.word (w - 1))) s1
      have hs2_code : s2.code = originalRuntimeCode := code
      have hs2_cnt : s2.locals.lookup counter = some (.val (.word (w - 1))) := by
        simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hrest_run := hrest s2 hs2_code (by change cost ≤ state.clock - 1; omega)
      have hframe := evaluate_avoidsLocal_flowing counter rest havoid s2
      have hnc := evaluate_noTopContinue rest hnoCont s2
      have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata s2 rest
      cases restRun : evaluateHOLFiniteState s2 rest with
      | mk result middle =>
        rw [restRun] at hrest_run hframe hnc hmeta
        dsimp only at hrest_run hframe hnc hmeta
        obtain ⟨spent, kept, safe⟩ := hrest_run
        change state.clock - 1 ≤ middle.clock + cost at spent
        change middle.clock ≤ state.clock - 1 at kept
        cases result with
        | none =>
          dsimp only
          have hmid_cnt : middle.locals.lookup counter = some (.val (.word (w - 1))) :=
            (hframe (Or.inl rfl)).trans hs2_cnt
          have one_toNat : (1 : BitVec 64).toNat = 1 := rfl
          have hle : (1 : BitVec 64) ≤ w := by rw [BitVec.le_def, one_toNat]; omega
          have natural : (w - 1).toNat = w.toNat - 1 := by
            rw [BitVec.toNat_sub_of_le hle, one_toNat]
          have hmul : (n - 1) * (cost + 1) + (cost + 1) = n * (cost + 1) := by
            calc (n - 1) * (cost + 1) + (cost + 1) = (n - 1 + 1) * (cost + 1) := by
                  rw [Nat.add_mul, Nat.one_mul]
              _ = n * (cost + 1) := by rw [show n - 1 + 1 = n by omega]
          have tail := ih (n - 1) (by omega) (by omega) middle (hmeta.1.trans code)
            (w - 1) hmid_cnt (by rw [natural]; omega) (by omega)
          obtain ⟨t1, t2, t3⟩ := tail
          exact ⟨by omega, by omega, t3⟩
        | some r =>
          cases r with
          | «continue» => exact absurd rfl hnc
          | «break» => exact ⟨by simp; omega, by simp; omega, by simp⟩
          | timeOut => exact absurd rfl safe
          | _ => exact ⟨by simp; omega, by simp; omega, by simp⟩
    · rw [if_neg lt]
      simp

private theorem downLowerWhile_decrFirst_run (counter : MlS) {rest : ProgHOL 64} {cost : Nat}
    (hrest : ProgBounded rest cost)
    (havoid : avoidsLocal counter rest = true)
    (hnoCont : noTopContinue rest = true) :
    ∀ n : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.code = originalRuntimeCode →
      ∀ w : BitVec 64, state.locals.lookup counter = some (.val (.word w)) →
      w.toNat ≤ n → n * (cost + 1) ≤ state.clock →
      let loop := ProgHOL.while (.cmp .lower (.const 0) (.var .local counter))
        (.seq (.assign .local counter (.op .sub [.var .local counter, .const 1])) rest)
      state.clock ≤ (evaluateHOLFiniteState state loop).2.clock + n * (cost + 1) ∧
        (evaluateHOLFiniteState state loop).2.clock ≤ state.clock ∧
        (evaluateHOLFiniteState state loop).1 ≠ some .timeOut := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro F state code w atCounter within budget
    have condition := eval_zero_lt_condition state counter w atCounter
    dsimp only
    rw [evaluateHOLFiniteState_while_total, condition]
    by_cases lt : 0 < w.toNat
    · rw [if_pos lt]
      simp only [show (1 : BitVec 64) ≠ 0 by decide, if_true, ne_eq, not_false_eq_true]
      have positiveRank : 0 < n := by omega
      have oneIteration : cost + 1 ≤ n * (cost + 1) := Nat.le_mul_of_pos_left _ positiveRank
      have clock : state.clock ≠ 0 := by omega
      rw [if_neg clock, fixClockHOLFinite_evaluateState]
      let s1 := decClockHOLFinite state
      have hs1_decr : evaluateHOLFiniteState s1
          (.assign .local counter (.op .sub [.var .local counter, .const 1])) =
          (none, setVarHOLFinite counter (.val (.word (w - 1))) s1) := by
        simp [s1, evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, atCounter,
          wordOpHOL, wordOp, valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact,
          setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
      rw [evaluateHOLFiniteState_seq_line780, hs1_decr]
      dsimp only
      let s2 := setVarHOLFinite counter (.val (.word (w - 1))) s1
      have hs2_code : s2.code = originalRuntimeCode := code
      have hs2_cnt : s2.locals.lookup counter = some (.val (.word (w - 1))) := by
        simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hrest_run := hrest s2 hs2_code (by change cost ≤ state.clock - 1; omega)
      have hframe := evaluate_avoidsLocal_flowing counter rest havoid s2
      have hnc := evaluate_noTopContinue rest hnoCont s2
      have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata s2 rest
      cases restRun : evaluateHOLFiniteState s2 rest with
      | mk result middle =>
        rw [restRun] at hrest_run hframe hnc hmeta
        dsimp only at hrest_run hframe hnc hmeta
        obtain ⟨spent, kept, safe⟩ := hrest_run
        change state.clock - 1 ≤ middle.clock + cost at spent
        change middle.clock ≤ state.clock - 1 at kept
        cases result with
        | none =>
          dsimp only
          have hmid_cnt : middle.locals.lookup counter = some (.val (.word (w - 1))) :=
            (hframe (Or.inl rfl)).trans hs2_cnt
          have one_toNat : (1 : BitVec 64).toNat = 1 := rfl
          have hle : (1 : BitVec 64) ≤ w := by rw [BitVec.le_def, one_toNat]; omega
          have natural : (w - 1).toNat = w.toNat - 1 := by
            rw [BitVec.toNat_sub_of_le hle, one_toNat]
          have hmul : (n - 1) * (cost + 1) + (cost + 1) = n * (cost + 1) := by
            calc (n - 1) * (cost + 1) + (cost + 1) = (n - 1 + 1) * (cost + 1) := by
                  rw [Nat.add_mul, Nat.one_mul]
              _ = n * (cost + 1) := by rw [show n - 1 + 1 = n by omega]
          have tail := ih (n - 1) (by omega) middle (hmeta.1.trans code)
            (w - 1) hmid_cnt (by rw [natural]; omega) (by omega)
          obtain ⟨t1, t2, t3⟩ := tail
          exact ⟨by omega, by omega, t3⟩
        | some r =>
          cases r with
          | «continue» => exact absurd rfl hnc
          | «break» => exact ⟨by simp; omega, by simp; omega, by simp⟩
          | timeOut => exact absurd rfl safe
          | _ => exact ⟨by simp; omega, by simp; omega, by simp⟩
    · rw [if_neg lt]
      simp

theorem funBounded_udivmod : FunBounded (ofString "udivmod") 64 := by
  refine funBounded_of_guestAst 33 (by rw [guestAst_len]; decide) Guest.Software.guestFn_udivmod 64 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_udivmod,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  intro F state hcode hbudget
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
  split
  · split
    · rw [evaluateHOLFiniteState_skip]
      dsimp only
      refine (RunBounded.seq (state := state) (a := 0) (b := 64)
        ((ProgBounded.straight _ rfl) state hcode (Nat.zero_le _)) (by omega) ?_).weaken (by omega)
      intro s1 _ hs1_code hs1_clk
      have hs1_code' : s1.code = originalRuntimeCode := hs1_code.trans hcode
      apply RunBounded.decConst
      apply RunBounded.decConst
      apply RunBounded.decConst
      let s2 := setVarHOLFinite (ofString "i") (.val (.word 64))
        (setVarHOLFinite (ofString "r") (.val (.word 0))
          (setVarHOLFinite (ofString "q") (.val (.word 0)) s1))
      have hs2_code : s2.code = originalRuntimeCode := hs1_code'
      have hs2_i : s2.locals.lookup (ofString "i") = some (.val (.word 64)) := by
        simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hs2_clk : s2.clock = s1.clock := rfl
      let restBody : ProgHOL 64 :=
        .seq
          (.assign .local (ofString "r")
            (.op .or
              [.shift .lsl (.var .local (ofString "r")) (.const 1#64),
               .op .and [.shift .lsr (.var .local (ofString "a")) (.var .local (ofString "i")), .const 1#64]]))
          (.ite (.cmp .notLower (.var .local (ofString "r")) (.var .local (ofString "b")))
            (.seq
              (.assign .local (ofString "r") (.op .sub [.var .local (ofString "r"), .var .local (ofString "b")]))
              (.assign .local (ofString "q")
                (.op .or [.var .local (ofString "q"), .shift .lsl (.const 1#64) (.var .local (ofString "i"))])))
            .skip)
      have hloop := downLessWhile_decrFirst_run (ofString "i") (rest := restBody)
        (ProgBounded.straight restBody rfl) rfl rfl
        64 (by decide) s2 hs2_code 64 hs2_i (by decide)
        (by simp only [Nat.zero_add, Nat.mul_one]; rw [hs2_clk]; omega)
      simp only [Nat.zero_add, Nat.mul_one] at hloop
      refine (RunBounded.seq (state := s2) (a := 64) (b := 0) hloop (by rw [hs2_clk]; omega) ?_).weaken (by omega)
      intro s3 _ hs3_code _
      exact (ProgBounded.straight _ rfl) s3 (hs3_code.trans hs2_code) (Nat.zero_le _)
    · have hcall := ProgBounded.call funBounded_trap_with none [.const (2#64)] state hcode (by omega)
      have hnonone := evaluate_call_trap_with_no_none state (2#64) hcode
      rcases hrun : evaluateHOLFiniteState state
          (.call (some (none, none)) (ofString "trap_with") [.const (2#64)]) with ⟨res, post⟩
      rw [hrun] at hcall hnonone
      cases res with
      | none => exact absurd rfl hnonone
      | some _ =>
        dsimp only at hcall ⊢
        exact ⟨by omega, hcall.2.1, hcall.2.2⟩
  · dsimp only
    exact ⟨by omega, le_refl _, by simp⟩

theorem lookup_digits_len :
    originalRuntimeCode.lookup (ofString "digits_len") =
      some ([(ofString "p", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_digits_len, .one) :=
  lookup_of_guestAst_getElem 66 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_digits_len) rfl

theorem runBounded_digits_len {F : Type}
    (state : PanSemStateFiniteExact 64 F) (K : BitVec 64)
    (hcode : state.code = originalRuntimeCode)
    (atN : state.locals.lookup (ofString "n") = some (.val (.word K)))
    (hbudget : K.toNat ≤ state.clock) :
    RunBounded state (sourceFnBody Guest.Software.guestFn_digits_len) K.toNat := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_digits_len,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  have hloop := downWhile_seq_decr_run (ofString "n")
    (first := .ite (.cmp .notEqual
        (.load .one (.op .add [.var .local (ofString "p"),
          .panop .mul [.op .sub [.var .local (ofString "n"), .const 1], .const 8]]))
        (.const 0))
      (.return (.var .local (ofString "n")))
      .skip)
    (ProgBounded.straight _ rfl) rfl rfl K.toNat state hcode K atN (le_refl _)
    (by simp only [Nat.zero_add, Nat.mul_one]; exact hbudget)
  simp only [Nat.zero_add, Nat.mul_one] at hloop
  refine (RunBounded.seq (state := state) (a := K.toNat) (b := 0) hloop (by omega) ?_).weaken (by omega)
  intro s_end _ hs_end_code _
  exact (ProgBounded.straight _ rfl) s_end (hs_end_code.trans hcode) (Nat.zero_le _)

theorem funBounded_digits_len : FunBounded (ofString "digits_len") (2 ^ 64 - 1) := by
  refine ⟨[(ofString "p", .one), (ofString "n", .one)],
    sourceFnBody Guest.Software.guestFn_digits_len, .one, lookup_digits_len, ?_⟩
  intro F state hcode hbudget
  rcases hn : state.locals.lookup (ofString "n") with _ | val
  · dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_digits_len,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total]
    have hc : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
        (.cmp .lower (.const 0#64) (.var .local (ofString "n"))) = none := by
      rw [evalHOLFinite_eq_toExact]
      simp [evalHOLExact, hn]
    rw [hc]
    simp
  · rcases val with ⟨⟨K⟩⟩ | fs | ⟨nm, fs⟩
    · exact (runBounded_digits_len state K hcode hn (by have := K.isLt; omega)).weaken
        (by have := K.isLt; omega)
    · dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_digits_len,
        InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total]
      have hc : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
          (.cmp .lower (.const 0#64) (.var .local (ofString "n"))) = none := by
        rw [evalHOLFinite_eq_toExact]
        simp [evalHOLExact, hn]
      rw [hc]
      simp
    · dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_digits_len,
        InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total]
      have hc : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
          (.cmp .lower (.const 0#64) (.var .local (ofString "n"))) = none := by
        rw [evalHOLFinite_eq_toExact]
        simp [evalHOLExact, hn]
      rw [hc]
      simp

private def mustTerminate : ProgHOL 64 → Bool
  | .return _ | .raise _ _ | .break | .continue => true
  | .call none _ _ => true
  | .seq p1 p2 => mustTerminate p1 || mustTerminate p2
  | .ite _ p1 p2 => mustTerminate p1 && mustTerminate p2
  | .dec _ _ _ b => mustTerminate b
  | .decCall _ _ _ _ cont => mustTerminate cont
  | _ => false

private theorem evaluate_mustTerminate {F : Type} (p : ProgHOL 64)
    (hm : mustTerminate p = true) (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s p).1 ≠ none := by
  induction p generalizing s with
  | «return» e =>
    rw [evaluateHOLFiniteState_return]
    split <;> (try split) <;> simp
  | raise nm e =>
    rw [evaluateHOLFiniteState_raise]
    split <;> [ (dsimp only; split <;> simp); simp ]
  | «break» => simp [evaluateHOLFiniteState_break]
  | «continue» => simp [evaluateHOLFiniteState_continue]
  | call info fn args =>
    cases info with
    | none =>
      rw [evaluateHOLFiniteState_tailCall]
      cases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with
      | none => simp
      | some vs =>
        dsimp only
        cases lookupCodeHOLFinite s.code.lookup fn vs with
        | none => simp
        | some entry =>
          rcases entry with ⟨body, callee, rsh⟩
          dsimp only
          split
          · simp
          · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r1, post1⟩
            dsimp only [fixClockHOLFinite]
            rcases r1 with _ | (_ | _ | _ | _ | w | _ | _) <;> try simp
            dsimp only
            split <;> simp
    | some _ => simp [mustTerminate] at hm
  | seq p1 p2 ih1 ih2 =>
    simp only [mustTerminate, Bool.or_eq_true] at hm
    rw [evaluateHOLFiniteState_seq_line780]
    rcases h1 : evaluateHOLFiniteState s p1 with ⟨r1, s1⟩
    cases r1 with
    | none =>
      rcases hm with hm1 | hm2
      · exact absurd (congrArg Prod.fst h1) (ih1 hm1 s)
      · exact ih2 hm2 s1
    | some _ => simp
  | ite cond p1 p2 ih1 ih2 =>
    simp only [mustTerminate, Bool.and_eq_true] at hm
    rw [evaluateHOLFiniteState_ite]
    split
    · split <;> [exact ih2 hm.2 s; exact ih1 hm.1 s]
    · simp
  | dec nm sh init b ih =>
    simp only [mustTerminate] at hm
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · simp
    · split <;> [exact ih hm _; simp]
  | decCall nm sh fn args cont ih =>
    simp only [mustTerminate] at hm
    rw [evaluateHOLFiniteState_decCall_total]
    cases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with
    | none => simp
    | some vs =>
      dsimp only
      cases lookupCodeHOLFinite s.code.lookup fn vs with
      | none => simp
      | some entry =>
        rcases entry with ⟨body, callee, rsh⟩
        dsimp only
        split
        · simp
        · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r1, post1⟩
          dsimp only [fixClockHOLFinite]
          rcases r1 with _ | (_ | _ | _ | _ | w | _ | _) <;> try simp
          dsimp only
          split
          · exact ih hm _
          · simp
  | _ => simp [mustTerminate] at hm

private theorem progBounded_seq_ite_terminating {cond : ExpHOL 64} {yes tail : ProgHOL 64} {a b : Nat}
    (hyes : ProgBounded yes a) (hm : mustTerminate yes = true) (htail : ProgBounded tail b) :
    ProgBounded (.seq (.ite cond yes .skip) tail) (max a b) := by
  intro F state hcode hbudget
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
  split
  · split
    · rw [evaluateHOLFiniteState_skip]
      dsimp only
      exact (htail state hcode (by omega)).weaken (by omega)
    · have hy := hyes state hcode (by omega)
      have hnn := evaluate_mustTerminate yes hm state
      rcases hr : evaluateHOLFiniteState state yes with ⟨res, post⟩
      rw [hr] at hy
      cases res with
      | none => exact absurd (congrArg Prod.fst hr) hnn
      | some _ =>
        dsimp only at hy ⊢
        exact ⟨by omega, hy.2.1, hy.2.2⟩
  · dsimp only
    exact ⟨by omega, le_refl _, by simp⟩

theorem funBounded_u256_to_be32 : FunBounded (ofString "u256_to_be32") 16 := by
  refine funBounded_of_guestAst 87 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_to_be32 16 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_u256_to_be32,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine ProgBounded.weaken
    (progBounded_seq_ite_terminating
      (ProgBounded.decCall funBounded_bswap64 _ _ _
        (ProgBounded.seq (ProgBounded.straight _ rfl)
          (ProgBounded.seq (ProgBounded.call funBounded_bswap64 _ _)
            (ProgBounded.seq (ProgBounded.straight _ rfl)
              (ProgBounded.seq (ProgBounded.call funBounded_bswap64 _ _)
                (ProgBounded.seq (ProgBounded.straight _ rfl)
                  (ProgBounded.seq (ProgBounded.call funBounded_bswap64 _ _)
                    (ProgBounded.seq (ProgBounded.straight _ rfl)
                      (ProgBounded.straight _ rfl)))))))))
      rfl
      (ProgBounded.seq (ProgBounded.call funBounded_st_be64 none _)
        (ProgBounded.seq (ProgBounded.call funBounded_st_be64 none _)
          (ProgBounded.seq (ProgBounded.call funBounded_st_be64 none _)
            (ProgBounded.seq (ProgBounded.call funBounded_st_be64 none _)
              (ProgBounded.straight _ rfl))))))
    (by decide)

theorem funBounded_u256_limb : FunBounded (ofString "u256_limb") 0 :=
  funBounded_of_guestAst 43 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_limb 0 rfl
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
          (ProgBounded.tailCall funBounded_bit_length64 _))))
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

private theorem runBounded_seq_ite_terminating {F : Type}
    (state : PanSemStateFiniteExact 64 F) {cond : ExpHOL 64} {yes tail : ProgHOL 64} {a b : Nat}
    (hyes : RunBounded state yes a) (hm : mustTerminate yes = true)
    (htail : RunBounded state tail b) :
    RunBounded state (.seq (.ite cond yes .skip) tail) (max a b) := by
  unfold RunBounded at *
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
  split
  · split
    · rw [evaluateHOLFiniteState_skip]
      dsimp only
      exact ⟨by omega, htail.2.1, htail.2.2⟩
    · have hnn := evaluate_mustTerminate yes hm state
      rcases hr : evaluateHOLFiniteState state yes with ⟨res, post⟩
      rw [hr] at hyes
      cases res with
      | none => exact absurd (congrArg Prod.fst hr) hnn
      | some _ =>
        dsimp only at hyes ⊢
        exact ⟨by omega, hyes.2.1, hyes.2.2⟩
  · dsimp only
    exact ⟨by omega, le_refl _, by simp⟩

private theorem variableCountedWhile_step {counter limit : MlS} (op : Cmp)
    (hop : op = .less ∨ op = .lower) (K : BitVec 64)
    (signed : op = .less → K.toNat < 2 ^ 63)
    {body : ProgHOL 64} {cost : Nat}
    (stepBody : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      s.code = originalRuntimeCode →
      ∀ w : BitVec 64, s.locals.lookup counter = some (.val (.word w)) →
      cost ≤ s.clock →
      s.clock ≤ (evaluateHOLFiniteState s body).2.clock + cost ∧
        (evaluateHOLFiniteState s body).2.clock ≤ s.clock ∧
        (evaluateHOLFiniteState s body).1 ≠ some .timeOut ∧
        (evaluateHOLFiniteState s body).1 ≠ some .continue ∧
        ((evaluateHOLFiniteState s body).1 = none →
          (evaluateHOLFiniteState s body).2.locals.lookup counter = some (.val (.word (w + 1))) ∧
          (evaluateHOLFiniteState s body).2.code = s.code))
    (preservesLimit : avoidsLocal limit body = true) :
    ∀ n : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F),
      state.code = originalRuntimeCode →
      ∀ w : BitVec 64, state.locals.lookup counter = some (.val (.word w)) →
      state.locals.lookup limit = some (.val (.word K)) → w.toNat ≤ K.toNat →
      K.toNat - w.toNat = n → n * (cost + 1) ≤ state.clock →
      let evaluated := evaluateHOLFiniteState state
        (.while (.cmp op (.var .local counter) (.var .local limit)) body)
      state.clock ≤ evaluated.2.clock + n * (cost + 1) ∧
        evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro F state code w atCounter atLimit within distance budget
    have condition := eval_variable_counted_condition state counter limit op hop K w
      signed within atCounter atLimit
    dsimp only
    rw [evaluateHOLFiniteState_while_total, condition]
    by_cases lt : w.toNat < K.toNat
    · rw [if_pos lt]
      simp only [show (1 : BitVec 64) ≠ 0 by decide, if_true, ne_eq, not_false_eq_true]
      have positiveRank : 0 < n := by omega
      have oneIteration : cost + 1 ≤ n * (cost + 1) := Nat.le_mul_of_pos_left _ positiveRank
      have clock : state.clock ≠ 0 := by omega
      rw [if_neg clock, fixClockHOLFinite_evaluateState]
      have stepRun := stepBody (decClockHOLFinite state) code w atCounter
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
          obtain ⟨t1, t2, t3⟩ := ih (K.toNat - (w + 1).toNat) nextRank middle (nextCode.trans code)
            (w + 1) nextCounter nextLimit (by rw [natural]; omega) rfl (by omega)
          exact ⟨by omega, by omega, t3⟩
        | some r =>
          cases r with
          | «continue» => exact absurd rfl noCont
          | «break» => exact ⟨by simp; omega, by simp; omega, by simp⟩
          | timeOut => exact absurd rfl safe
          | _ => exact ⟨by simp; omega, by simp; omega, by simp⟩
    · rw [if_neg lt]
      simp

private theorem decCall_step_incr {F : Type}
    (s : PanSemStateFiniteExact 64 F) {counter name function : MlS}
    {shape : ShapeHOL} {args : List (ExpHOL 64)} {tail : ProgHOL 64} {a b : Nat}
    (hfn : FunBounded function a) (hdist : counter ≠ name)
    (hrest : CountedBody counter 1 tail b)
    (hcode : s.code = originalRuntimeCode) (w : BitVec 64)
    (atCounter : s.locals.lookup counter = some (.val (.word w)))
    (hbudget : (a + 1) + b ≤ s.clock) :
    s.clock ≤ (evaluateHOLFiniteState s (.decCall name shape function args tail)).2.clock + ((a + 1) + b) ∧
      (evaluateHOLFiniteState s (.decCall name shape function args tail)).2.clock ≤ s.clock ∧
      (evaluateHOLFiniteState s (.decCall name shape function args tail)).1 ≠ some .timeOut ∧
      (evaluateHOLFiniteState s (.decCall name shape function args tail)).1 ≠ some .continue ∧
      ((evaluateHOLFiniteState s (.decCall name shape function args tail)).1 = none →
        (evaluateHOLFiniteState s (.decCall name shape function args tail)).2.locals.lookup counter =
          some (.val (.word (w + 1))) ∧
        (evaluateHOLFiniteState s (.decCall name shape function args tail)).2.code = s.code) := by
  rw [evaluateHOLFiniteState_decCall_total]
  cases hargs : evalListHOLFinite s (h := fun ad => Classical.propDecidable (s.memaddrs ad)) args with
  | none =>
    simp
  | some values =>
    dsimp only
    cases hlookup : lookupCodeHOLFinite s.code.lookup function values with
    | none =>
      simp
    | some entry =>
      rcases entry with ⟨fbody, callee, rsh⟩
      dsimp only
      have hclk : s.clock ≠ 0 := by omega
      rw [if_neg hclk]
      have hcallee := hfn s values fbody callee rsh hcode hlookup (by change a ≤ s.clock - 1; omega)
      have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) fbody
      have hrem := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s callee) fbody
      rcases hcal : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) fbody with ⟨r1, post1⟩
      rw [hcal] at hcallee hmeta hrem
      dsimp only at hcallee hmeta hrem
      have hfix : fixClockHOLFinite (callEntryStateHOLFinite s callee) (r1, post1) = (r1, post1) := by
        simp [fixClockHOLFinite, Nat.not_lt.mpr hrem]
      rw [hfix]
      dsimp only
      change s.clock - 1 ≤ post1.clock + a at hcallee
      change post1.clock ≤ s.clock - 1 at hrem
      rcases r1 with _ | (_ | _ | _ | _ | v | _ | _)
      · exact ⟨by omega, by omega, by simp, by simp, by simp⟩
      · exact ⟨by omega, by omega, by simp, by simp, by simp⟩
      · exact absurd rfl hcallee.2.2
      · exact ⟨by omega, by omega, by simp, by simp, by simp⟩
      · exact ⟨by omega, by omega, by simp, by simp, by simp⟩
      · dsimp only
        split
        · let resumed := setVarHOLFinite name v { post1 with locals := s.locals }
          have hres_code : resumed.code = originalRuntimeCode := hmeta.1.trans hcode
          have hres_cnt : resumed.locals.lookup counter = some (.val (.word w)) := by
            simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hdist, atCounter]
          have htail := hrest.run resumed hres_code w hres_cnt (by change b ≤ post1.clock; omega)
          rcases htr : evaluateHOLFiniteState resumed tail with ⟨rt, post2⟩
          rw [htr] at htail
          dsimp only at htail ⊢
          refine ⟨by change s.clock ≤ post2.clock + _; change post1.clock ≤ post2.clock + b at htail; omega,
            by change post2.clock ≤ s.clock; change post2.clock ≤ post1.clock at htail; omega,
            htail.2.2.1, htail.2.2.2.1, fun hnorm => ?_⟩
          obtain ⟨hcnt2, hcode2⟩ := htail.2.2.2.2 hnorm
          refine ⟨?_, hcode2.trans hmeta.1⟩
          rw [resVarEq_lookup, if_neg hdist]
          exact hcnt2
        · exact ⟨by omega, by omega, by simp, by simp, by simp⟩
      · exact ⟨by omega, by omega, by simp, by simp, by simp⟩
      · exact ⟨by omega, by omega, by simp, by simp, by simp⟩

theorem lookup_u256_from_be :
    originalRuntimeCode.lookup (ofString "u256_from_be") =
      some ([(ofString "p", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_u256_from_be, .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 86 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_from_be) rfl

theorem runBounded_u256_from_be {F : Type}
    (state : PanSemStateFiniteExact 64 F) (K : BitVec 64)
    (hcode : state.code = originalRuntimeCode)
    (atN : state.locals.lookup (ofString "n") = some (.val (.word K)))
    (hbudget : max 4 K.toNat ≤ state.clock) :
    RunBounded state (sourceFnBody Guest.Software.guestFn_u256_from_be) (max 4 K.toNat) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_u256_from_be,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine runBounded_seq_ite_terminating state
    ((ProgBounded.weaken
      (ProgBounded.dec _ _ _
        (ProgBounded.decCall funBounded_bswap64 _ _ _
          (ProgBounded.seq (ProgBounded.straight _ rfl)
            (ProgBounded.decCall funBounded_bswap64 _ _ _
              (ProgBounded.seq (ProgBounded.straight _ rfl)
                (ProgBounded.decCall funBounded_bswap64 _ _ _
                  (ProgBounded.seq (ProgBounded.straight _ rfl)
                    (ProgBounded.decCall funBounded_bswap64 _ _ _
                      (ProgBounded.straight _ rfl)))))))))
      (by decide)) state hcode (by omega))
    rfl ?_
  apply RunBounded.decConst
  apply RunBounded.decConst
  apply RunBounded.decConst
  apply RunBounded.decConst
  apply RunBounded.decConst
  let s0 := setVarHOLFinite (ofString "i") (.val (.word 0))
    (setVarHOLFinite (ofString "l3") (.val (.word 0))
      (setVarHOLFinite (ofString "l2") (.val (.word 0))
        (setVarHOLFinite (ofString "l1") (.val (.word 0))
          (setVarHOLFinite (ofString "l0") (.val (.word 0)) state))))
  have hs0_code : s0.code = originalRuntimeCode := hcode
  have hs0_i : s0.locals.lookup (ofString "i") = some (.val (.word 0)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs0_n : s0.locals.lookup (ofString "n") = some (.val (.word K)) := by
    simp only [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, atN]
    repeat rw [if_neg (by decide)]
  have hs0_clk : s0.clock = state.clock := rfl
  refine (RunBounded.seq (state := s0) (a := K.toNat * (0 + 1)) (b := 0) ?_
    (by rw [hs0_clk]; omega) ?_).weaken (by omega)
  · unfold RunBounded
    exact variableCountedWhile_run (ofString "i") (ofString "n") .lower (Or.inr rfl) K
      (fun h => by cases h)
      (CountedBody.dec _ _ _ (by decide)
        (CountedBody.dec _ _ _ (by decide)
          (CountedBody.dec _ _ _ (by decide)
            (countedBody_seq_straight _ (by decide) (by decide) (by decide)
              (countedBody_seq_straight _ (by decide) (by decide) (by decide)
                (countedBody_seq_straight _ (by decide) (by decide) (by decide)
                  (countedBody_seq_straight _ (by decide) (by decide) (by decide) CountedBody.incr)))))))
      (by decide) K.toNat s0 hs0_code 0 hs0_i hs0_n (by simp) (by simp)
      (by simp only [Nat.zero_add, Nat.mul_one]; rw [hs0_clk]; omega)
  · intro s_end _ hs_end_code _
    exact (ProgBounded.straight _ rfl) s_end (hs_end_code.trans hs0_code) (Nat.zero_le _)

theorem funBounded_u256_from_be : FunBounded (ofString "u256_from_be") (2 ^ 64 - 1) := by
  refine ⟨[(ofString "p", .one), (ofString "n", .one)],
    sourceFnBody Guest.Software.guestFn_u256_from_be, .comb [.one, .one, .one, .one],
    lookup_u256_from_be, ?_⟩
  intro F state hcode hbudget
  rcases hn : state.locals.lookup (ofString "n") with _ | val
  · dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_u256_from_be,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
    simp [evalHOLExact, evalListHOLExact, hn]
  · rcases val with ⟨⟨K⟩⟩ | fs | ⟨nm, fs⟩
    · exact (runBounded_u256_from_be state K hcode hn (by have := K.isLt; omega)).weaken
        (by have := K.isLt; omega)
    · dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_u256_from_be,
        InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
      simp [evalHOLExact, evalListHOLExact, hn]
    · dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_u256_from_be,
        InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
      simp [evalHOLExact, evalListHOLExact, hn]

theorem lookup_rlp_put_be :
    originalRuntimeCode.lookup (ofString "rlp_put_be") =
      some ([(ofString "dst", .one), (ofString "v", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_put_be, .one) :=
  lookup_of_guestAst_getElem 119 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_put_be) rfl

theorem runBounded_rlp_put_be {F : Type}
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
  apply RunBounded.decWord state (ofString "i") (.var .local (ofString "n")) K
    (by simp [evalHOLExact, atN])
  let s0 := setVarHOLFinite (ofString "i") (.val (.word K)) state
  have hs0_code : s0.code = originalRuntimeCode := hcode
  have hs0_i : s0.locals.lookup (ofString "i") = some (.val (.word K)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs0_clk : s0.clock = state.clock := rfl
  let restBody : ProgHOL 64 :=
    .seq
      (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) (.var .local (ofString "v")))
      (.assign .local (ofString "v") (.shift .lsr (.var .local (ofString "v")) (.const 8#64)))
  have hloop := downLowerWhile_decrFirst_run (ofString "i") (rest := restBody)
    (ProgBounded.straight restBody rfl) rfl rfl
    K.toNat s0 hs0_code K hs0_i (le_refl _)
    (by simp only [Nat.zero_add, Nat.mul_one]; rw [hs0_clk]; exact hbudget)
  simp only [Nat.zero_add, Nat.mul_one] at hloop
  refine (RunBounded.seq (state := s0) (a := K.toNat) (b := 0) hloop (by rw [hs0_clk]; omega) ?_).weaken (by omega)
  intro s_end _ hs_end_code _
  exact (ProgBounded.straight _ rfl) s_end (hs_end_code.trans hs0_code) (Nat.zero_le _)

theorem funBounded_rlp_put_be : FunBounded (ofString "rlp_put_be") (2 ^ 64 - 1) := by
  refine ⟨[(ofString "dst", .one), (ofString "v", .one), (ofString "n", .one)],
    sourceFnBody Guest.Software.guestFn_rlp_put_be, .one, lookup_rlp_put_be, ?_⟩
  intro F state hcode hbudget
  rcases hn : state.locals.lookup (ofString "n") with _ | val
  · dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_put_be,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
    rw [evaluateHOLFiniteState_dec_total]
    simp [evalHOLExact, hn]
  · rcases val with ⟨⟨K⟩⟩ | fs | ⟨nm, fs⟩
    · exact (runBounded_rlp_put_be state K hcode hn (by have := K.isLt; omega)).weaken
        (by have := K.isLt; omega)
    · dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_put_be,
        InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
      rw [evaluateHOLFiniteState_dec_total]
      simp [evalHOLExact, hn, shapeOfHOLExact, shapeEqHOL]
    · dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_put_be,
        InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
      rw [evaluateHOLFiniteState_dec_total]
      simp [evalHOLExact, hn, shapeOfHOLExact, shapeEqHOL]

private theorem variableCountedWhile_step_zero_bounded {F : Type}
    (counter limit : MlS) (op : Cmp) (hop : op = .less ∨ op = .lower)
    {body : ProgHOL 64} {cost : Nat}
    (stepBody : ∀ {G : Type} (s : PanSemStateFiniteExact 64 G),
      s.code = originalRuntimeCode →
      ∀ w : BitVec 64, s.locals.lookup counter = some (.val (.word w)) →
      cost ≤ s.clock →
      s.clock ≤ (evaluateHOLFiniteState s body).2.clock + cost ∧
        (evaluateHOLFiniteState s body).2.clock ≤ s.clock ∧
        (evaluateHOLFiniteState s body).1 ≠ some .timeOut ∧
        (evaluateHOLFiniteState s body).1 ≠ some .continue ∧
        ((evaluateHOLFiniteState s body).1 = none →
          (evaluateHOLFiniteState s body).2.locals.lookup counter = some (.val (.word (w + 1))) ∧
          (evaluateHOLFiniteState s body).2.code = s.code))
    (preservesLimit : avoidsLocal limit body = true)
    (state : PanSemStateFiniteExact 64 F) (code : state.code = originalRuntimeCode)
    (K : BitVec 64)
    (atCounter : state.locals.lookup counter = some (.val (.word 0)))
    (atLimit : state.locals.lookup limit = some (.val (.word K)))
    (budget : (2 ^ 64 - 1) * (cost + 1) ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state
      (.while (.cmp op (.var .local counter) (.var .local limit)) body)
    state.clock ≤ evaluated.2.clock + (2 ^ 64 - 1) * (cost + 1) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  by_cases signed : op = .less → K.toNat < 2 ^ 63
  · have ceiling : K.toNat * (cost + 1) ≤ (2 ^ 64 - 1) * (cost + 1) :=
      Nat.mul_le_mul_right _ (by have bound := K.isLt; omega)
    have bounded := variableCountedWhile_step op hop K signed stepBody preservesLimit
      K.toNat state code 0 atCounter atLimit (by simp) (by simp) (by omega)
    dsimp only at bounded ⊢
    exact ⟨by omega, bounded.2.1, bounded.2.2⟩
  · have comparison : op = .less := by
      rcases hop with eq | eq
      · exact eq
      · exfalso; apply signed; intro impossible; cases eq.symm.trans impossible
    have negative : ¬ K.toNat < 9223372036854775808 := fun small => signed (fun _ => small)
    subst op
    have condition : evalHOLFinite state
        (h := fun a => Classical.propDecidable (state.memaddrs a))
        (.cmp .less (.var .local counter) (.var .local limit)) = some (.val (.word 0)) := by
      rw [evalHOLFinite_eq_toExact]
      simp [evalHOLExact, atCounter, atLimit, Compiler.Encoders.Asm.wordCmpHOL,
        Compiler.Encoders.Asm.holAsmSignedLess, negative]
    dsimp only
    rw [evaluateHOLFiniteState_while_total, condition]
    simp

private theorem progBounded_decCall_one {function : MlS} {fnCost : Nat}
    (hfn : FunBounded function fnCost) (name : MlS) (args : List (ExpHOL 64))
    {cont : ProgHOL 64} {tailCost : Nat}
    (hcont : ∀ (K : BitVec 64) {F : Type} (s : PanSemStateFiniteExact 64 F),
      s.code = originalRuntimeCode →
      s.locals.lookup name = some (.val (.word K)) →
      tailCost ≤ s.clock →
      RunBounded s cont tailCost) :
    ProgBounded (.decCall name .one function args cont) (fnCost + 1 + tailCost) := by
  intro F state hcode hbudget
  rw [evaluateHOLFiniteState_decCall_total]
  cases hargs : evalListHOLFinite state (h := fun ad => Classical.propDecidable (state.memaddrs ad)) args with
  | none => simp
  | some values =>
    dsimp only
    cases hlookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => simp
    | some entry =>
      rcases entry with ⟨fbody, callee, rsh⟩
      dsimp only
      have hclk : state.clock ≠ 0 := by omega
      rw [if_neg hclk]
      have hcallee := hfn state values fbody callee rsh hcode hlookup (by change fnCost ≤ state.clock - 1; omega)
      have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) fbody
      have hrem := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) fbody
      rcases hcal : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) fbody with ⟨r1, post1⟩
      rw [hcal] at hcallee hmeta hrem
      dsimp only at hcallee hmeta hrem
      have hfix : fixClockHOLFinite (callEntryStateHOLFinite state callee) (r1, post1) = (r1, post1) := by
        simp [fixClockHOLFinite, Nat.not_lt.mpr hrem]
      rw [hfix]
      dsimp only
      change state.clock - 1 ≤ post1.clock + fnCost at hcallee
      change post1.clock ≤ state.clock - 1 at hrem
      rcases r1 with _ | (_ | _ | _ | _ | v | _ | _)
      · exact ⟨by omega, by omega, by simp⟩
      · exact ⟨by omega, by omega, by simp⟩
      · exact absurd rfl hcallee.2.2
      · exact ⟨by omega, by omega, by simp⟩
      · exact ⟨by omega, by omega, by simp⟩
      · dsimp only
        split
        · rename_i hshape
          have hv : ∃ K : BitVec 64, v = .val (.word K) := by
            rcases v with ⟨⟨K⟩⟩ | fs | ⟨nm, fs⟩
            · exact ⟨K, rfl⟩
            · simp [shapeOfHOLExact, shapeEqHOL] at hshape
            · simp [shapeOfHOLExact, shapeEqHOL] at hshape
          obtain ⟨K, rfl⟩ := hv
          let resumed := setVarHOLFinite name (.val (.word K)) { post1 with locals := state.locals }
          have hres_code : resumed.code = originalRuntimeCode := hmeta.1.trans hcode
          have hres_nm : resumed.locals.lookup name = some (.val (.word K)) := by
            simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have htail := hcont K resumed hres_code hres_nm (by change tailCost ≤ post1.clock; omega)
          rcases htr : evaluateHOLFiniteState resumed cont with ⟨rt, post2⟩
          rw [htr] at htail
          dsimp only at htail ⊢
          exact ⟨by change state.clock ≤ post2.clock + _; change post1.clock ≤ post2.clock + tailCost at htail; omega,
            by change post2.clock ≤ state.clock; change post2.clock ≤ post1.clock at htail; omega,
            htail.2.2⟩
        · exact ⟨by omega, by omega, by simp⟩
      · exact ⟨by omega, by omega, by simp⟩
      · exact ⟨by omega, by omega, by simp⟩

private theorem dec_step_incr {F : Type}
    (s : PanSemStateFiniteExact 64 F) {counter name : MlS}
    {shape : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64} {cost : Nat}
    (hdist : counter ≠ name)
    (hbody : ∀ {G : Type} (u : PanSemStateFiniteExact 64 G),
      u.code = originalRuntimeCode →
      ∀ w : BitVec 64, u.locals.lookup counter = some (.val (.word w)) →
      cost ≤ u.clock →
      u.clock ≤ (evaluateHOLFiniteState u body).2.clock + cost ∧
        (evaluateHOLFiniteState u body).2.clock ≤ u.clock ∧
        (evaluateHOLFiniteState u body).1 ≠ some .timeOut ∧
        (evaluateHOLFiniteState u body).1 ≠ some .continue ∧
        ((evaluateHOLFiniteState u body).1 = none →
          (evaluateHOLFiniteState u body).2.locals.lookup counter = some (.val (.word (w + 1))) ∧
          (evaluateHOLFiniteState u body).2.code = u.code))
    (hcode : s.code = originalRuntimeCode) (w : BitVec 64)
    (atCounter : s.locals.lookup counter = some (.val (.word w)))
    (hbudget : cost ≤ s.clock) :
    s.clock ≤ (evaluateHOLFiniteState s (.dec name shape init body)).2.clock + cost ∧
      (evaluateHOLFiniteState s (.dec name shape init body)).2.clock ≤ s.clock ∧
      (evaluateHOLFiniteState s (.dec name shape init body)).1 ≠ some .timeOut ∧
      (evaluateHOLFiniteState s (.dec name shape init body)).1 ≠ some .continue ∧
      ((evaluateHOLFiniteState s (.dec name shape init body)).1 = none →
        (evaluateHOLFiniteState s (.dec name shape init body)).2.locals.lookup counter =
          some (.val (.word (w + 1))) ∧
        (evaluateHOLFiniteState s (.dec name shape init body)).2.code = s.code) := by
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · exact ⟨by omega, le_refl _, by simp, by simp, by simp⟩
  · rename_i val _
    split
    · let inner := setVarHOLFinite name val s
      have hcnt : inner.locals.lookup counter = some (.val (.word w)) := by
        simp [inner, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hdist, atCounter]
      have hb := hbody inner hcode w hcnt hbudget
      rcases hrun : evaluateHOLFiniteState inner body with ⟨res, post⟩
      rw [hrun] at hb
      dsimp only at hb ⊢
      refine ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, fun hnorm => ?_⟩
      obtain ⟨hc1, hc2⟩ := hb.2.2.2.2 hnorm
      refine ⟨?_, hc2⟩
      rw [resVarEq_lookup, if_neg hdist]
      exact hc1
    · exact ⟨by omega, le_refl _, by simp, by simp, by simp⟩

theorem funBounded_u256_to_be_min :
    FunBounded (ofString "u256_to_be_min") (6 + (2 ^ 64 - 1) * 2) := by
  refine funBounded_of_guestAst 88 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_to_be_min
    (6 + (2 ^ 64 - 1) * 2) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_u256_to_be_min,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine ProgBounded.weaken
    (progBounded_decCall_one funBounded_u256_byte_length (ofString "len") _
      (tailCost := (2 ^ 64 - 1) * 2) ?_)
    (by omega)
  intro K F s hs_code hs_len hs_budget
  apply RunBounded.decConst
  let s0 := setVarHOLFinite (ofString "i") (.val (.word 0)) s
  have hs0_code : s0.code = originalRuntimeCode := hs_code
  have hs0_i : s0.locals.lookup (ofString "i") = some (.val (.word 0)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs0_len : s0.locals.lookup (ofString "len") = some (.val (.word K)) := by
    simp only [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs_len]
    rw [if_neg (by decide)]
  have hs0_clk : s0.clock = s.clock := rfl
  refine (RunBounded.seq (state := s0) (a := (2 ^ 64 - 1) * 2) (b := 0) ?_
    (by rw [hs0_clk]; omega) ?_).weaken (by omega)
  · exact variableCountedWhile_step_zero_bounded (ofString "i") (ofString "len")
      .lower (Or.inr rfl) (cost := 1)
      (fun u hu_code w hu_i hu_b =>
        dec_step_incr u (by decide)
          (fun u' hu'_code w' hu'_i hu'_b =>
            decCall_step_incr u' funBounded_u256_limb (by decide)
              (countedBody_seq_straight _ (by decide) (by decide) (by decide) CountedBody.incr)
              hu'_code w' hu'_i hu'_b)
          hu_code w hu_i hu_b)
      (by decide) s0 hs0_code K hs0_i hs0_len (by rw [hs0_clk]; exact hs_budget)
  · intro s_end _ hs_end_code _
    exact (ProgBounded.straight _ rfl) s_end (hs_end_code.trans hs0_code) (Nat.zero_le _)

private theorem byteShiftWhile_run (varName : MlS)
    {rest : ProgHOL 64} {cost : Nat}
    (hrest : ProgBounded rest cost)
    (havoid : avoidsLocal varName rest = true)
    (hnoCont : noTopContinue rest = true) :
    ∀ n : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F),
      state.code = originalRuntimeCode →
      ∀ w : BitVec 64, state.locals.lookup varName = some (.val (.word w)) →
      w.toNat < 2 ^ (8 * n) →
      n * (cost + 1) ≤ state.clock →
      let evaluated := evaluateHOLFiniteState state
        (.while (.cmp .notEqual (.var .local varName) (.const 0#64))
          (.seq (.assign .local varName (.shift .lsr (.var .local varName) (.const 8#64))) rest))
      state.clock ≤ evaluated.2.clock + n * (cost + 1) ∧
        evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  intro n
  induction n with
  | zero =>
    intro F state _ w atVar hw _
    have hw0 : w = 0#64 := BitVec.eq_of_toNat_eq (by simp at hw ⊢; omega)
    subst hw0
    have hcond : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
        (.cmp .notEqual (.var .local varName) (.const 0#64)) = some (.val (.word 0#64)) := by
      rw [evalHOLFinite_eq_toExact]
      simp [evalHOLExact, atVar, Compiler.Encoders.Asm.wordCmpHOL]
    dsimp only
    rw [evaluateHOLFiniteState_while_total, hcond]
    simp
  | succ k ih =>
    intro F state hcode w atVar hw hbudget
    have hcond : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
        (.cmp .notEqual (.var .local varName) (.const 0#64)) =
        some (.val (.word (if w = 0#64 then 0#64 else 1#64))) := by
      rw [evalHOLFinite_eq_toExact]
      by_cases hz : w = 0#64 <;> simp [evalHOLExact, atVar, Compiler.Encoders.Asm.wordCmpHOL, hz]
    dsimp only
    rw [evaluateHOLFiniteState_while_total, hcond]
    by_cases hz : w = 0#64
    · rw [if_pos hz]
      simp
    · rw [if_neg hz]
      simp only [show (1#64 : BitVec 64) ≠ 0 by decide, if_true, ne_eq, not_false_eq_true]
      have hclk : state.clock ≠ 0 := by
        have : cost + 1 ≤ (k + 1) * (cost + 1) := Nat.le_mul_of_pos_left _ (by omega)
        omega
      rw [if_neg hclk, fixClockHOLFinite_evaluateState, evaluateHOLFiniteState_seq_line780]
      have hassign : evaluateHOLFiniteState (decClockHOLFinite state)
          (.assign .local varName (.shift .lsr (.var .local varName) (.const 8#64))) =
          (none, setVarHOLFinite varName (.val (.word (w >>> 8))) (decClockHOLFinite state)) := by
        simp [evaluateHOLFiniteState_assign, evalHOLExact, decClockHOLFinite, atVar, wordShiftHOL,
          lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
      rw [hassign]
      dsimp only
      let s1 := setVarHOLFinite varName (.val (.word (w >>> 8))) (decClockHOLFinite state)
      have hs1_code : s1.code = originalRuntimeCode := hcode
      have hs1_var : s1.locals.lookup varName = some (.val (.word (w >>> 8))) := by
        simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hs1_clk : s1.clock = state.clock - 1 := rfl
      have hrest_run := hrest s1 hs1_code (by rw [hs1_clk]; have : (k + 1) * (cost + 1) = k * (cost + 1) + (cost + 1) := Nat.succ_mul _ _; omega)
      have hframe := evaluate_avoidsLocal_flowing varName rest havoid s1
      have hnc := evaluate_noTopContinue rest hnoCont s1
      have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata s1 rest
      rcases hrr : evaluateHOLFiniteState s1 rest with ⟨r1, s2⟩
      rw [hrr] at hrest_run hframe hnc hmeta
      dsimp only at hrest_run hframe hnc hmeta ⊢
      obtain ⟨hspent, hkept, hsafe⟩ := hrest_run
      rw [hs1_clk] at hspent hkept
      have hexp : (k + 1) * (cost + 1) = k * (cost + 1) + (cost + 1) := Nat.succ_mul _ _
      cases r1 with
      | none =>
        dsimp only
        have hs2_var : s2.locals.lookup varName = some (.val (.word (w >>> 8))) :=
          (hframe (Or.inl rfl)).trans hs1_var
        have hshr : (w >>> 8).toNat < 2 ^ (8 * k) := by
          rw [BitVec.toNat_ushiftRight]
          have hpow : 2 ^ (8 * (k + 1)) = 2 ^ (8 * k) * 256 := by
            rw [Nat.mul_succ, Nat.pow_add]
          rw [Nat.shiftRight_eq_div_pow]
          change w.toNat / 256 < 2 ^ (8 * k)
          omega
        obtain ⟨t1, t2, t3⟩ := ih s2 (hmeta.1.trans hs1_code) (w >>> 8) hs2_var hshr (by omega)
        exact ⟨by omega, by omega, t3⟩
      | some r =>
        cases r with
        | «continue» => exact absurd rfl hnc
        | «break» => exact ⟨by simp; omega, by simp; omega, by simp⟩
        | timeOut => exact absurd rfl hsafe
        | _ => exact ⟨by simp; omega, by simp; omega, by simp⟩

theorem funBounded_rlp_be_len : FunBounded (ofString "rlp_be_len") 8 := by
  refine funBounded_of_guestAst 118 (by rw [guestAst_len]; decide) Guest.Software.guestFn_rlp_be_len 8 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_rlp_be_len,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  intro F state hcode hbudget
  apply RunBounded.decConst
  generalize hs0 : setVarHOLFinite (ofString "n") (.val (.word 0)) state = s0
  have hs0_code : s0.code = originalRuntimeCode := by rw [← hs0]; exact hcode
  have hs0_clk : s0.clock = state.clock := by rw [← hs0]; rfl
  rcases hv : s0.locals.lookup (ofString "v") with _ | val
  · unfold RunBounded
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total]
    have hc : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
        (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64)) = none := by
      rw [evalHOLFinite_eq_toExact]
      simp [evalHOLExact, hv]
    rw [hc]
    simp
  · rcases val with ⟨⟨w⟩⟩ | fs | ⟨nm, fs⟩
    · have hloop := byteShiftWhile_run (ofString "v")
        (rest := .assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const 1#64]))
        (ProgBounded.straight _ rfl) rfl rfl
        8 s0 hs0_code w hv (by simpa using w.isLt)
        (by simp only [Nat.zero_add, Nat.mul_one]; rw [hs0_clk]; exact hbudget)
      simp only [Nat.zero_add, Nat.mul_one] at hloop
      refine (RunBounded.seq (state := s0) (a := 8) (b := 0) hloop (by rw [hs0_clk]; omega) ?_).weaken (by omega)
      intro s_end _ hs_end_code _
      exact (ProgBounded.straight _ rfl) s_end (hs_end_code.trans hs0_code) (Nat.zero_le _)
    · unfold RunBounded
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total]
      have hc : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
          (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64)) = none := by
        rw [evalHOLFinite_eq_toExact]
        simp [evalHOLExact, hv]
      rw [hc]
      simp
    · unfold RunBounded
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total]
      have hc : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
          (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64)) = none := by
        rw [evalHOLFinite_eq_toExact]
        simp [evalHOLExact, hv]
      rw [hc]
      simp

theorem funBounded_u256_to_digits : FunBounded (ofString "u256_to_digits") 0 :=
  funBounded_of_guestAst 64 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_to_digits 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_digits_to_u256 : FunBounded (ofString "digits_to_u256") 0 :=
  funBounded_of_guestAst 65 (by rw [guestAst_len]; decide) Guest.Software.guestFn_digits_to_u256 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_digits_divmod (Kd : Nat)
    (hdiv : FunBounded (ofString "divmnu") Kd) :
    FunBounded (ofString "digits_divmod") (1 + (2 ^ 64 - 1 + 1) + (2 ^ 64 - 1 + 1) + 16 + 1 + 8 + (Kd + 1) + 1) := by
  refine funBounded_of_guestAst 68 (by rw [guestAst_len]; decide) Guest.Software.guestFn_digits_divmod _ rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_digits_divmod,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine ProgBounded.weaken
    (ProgBounded.dec _ _ _
      (ProgBounded.dec _ _ _
        (ProgBounded.dec _ _ _
          (ProgBounded.seq (ProgBounded.call funBounded_u256_to_digits none _)
            (ProgBounded.decCall funBounded_digits_len _ _ _
              (ProgBounded.decCall funBounded_digits_len _ _ _
                (ProgBounded.countedDec (ofString "i") .lower (Or.inr rfl) 16 1 0
                  (by decide) (by decide) (by decide)
                  (countedBody_seq_straight _ (by decide) (by decide) (by decide) CountedBody.incr)
                  (ProgBounded.seq
                    (ProgBounded.iteMax _
                      (ProgBounded.tail funBounded_digits_to_u256 _)
                      (ProgBounded.straight _ rfl))
                    (ProgBounded.countedAssign (ofString "i") .lower (Or.inr rfl) 8 1 0
                      (by decide) (by decide) (by decide)
                      (countedBody_seq_straight _ (by decide) (by decide) (by decide) CountedBody.incr)
                      (ProgBounded.seq
                        (ProgBounded.call hdiv _ _)
                        (ProgBounded.tail funBounded_digits_to_u256 _)))))))))))
    (by
      have h16 : (16 : BitVec 64).toNat = 16 := rfl
      have h8 : (8 : BitVec 64).toNat = 8 := rfl
      rw [h16, h8]
      omega)

theorem funBounded_rlp_fail : FunBounded (ofString "rlp_fail") 0 :=
  funBounded_of_guestAst 105 (by rw [guestAst_len]; decide) Guest.Software.guestFn_rlp_fail 0 rfl
    (ProgBounded.straight _ rfl)

theorem lookup_rlp_fail :
    originalRuntimeCode.lookup (ofString "rlp_fail") =
      some ([(ofString "code", .one)], sourceFnBody Guest.Software.guestFn_rlp_fail, .one) :=
  lookup_of_guestAst_getElem 105 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_fail) rfl

private theorem evaluate_rlp_fail_body_outcomes {F : Type} (state : PanSemStateFiniteExact 64 F) :
    let out := evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_rlp_fail)
    out.1 ≠ none ∧ (∀ v, out.1 ≠ some (.returned v)) := by
  classical
  have hbody : sourceFnBody Guest.Software.guestFn_rlp_fail =
      .seq (.raise (ofString "RlpErr") (.var .local (ofString "code"))) (.return (.const 0#64)) := rfl
  dsimp only
  rw [hbody, evaluateHOLFiniteState_seq_line780]
  have hraise :
      let r := (evaluateHOLFiniteState state (.raise (ofString "RlpErr") (.var .local (ofString "code")))).1
      r = some .error ∨ ∃ v, r = some (.exception (ofString "RlpErr") v) := by
    dsimp only
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only
      split <;> simp
    · simp
  rcases h1 : evaluateHOLFiniteState state (.raise (ofString "RlpErr") (.var .local (ofString "code"))) with ⟨r1, st1⟩
  rw [h1] at hraise
  rcases hraise with rfl | ⟨v, rfl⟩
  · exact ⟨by simp, fun _ => by simp⟩
  · exact ⟨by simp, fun _ => by simp⟩

private theorem evaluate_call_rlp_fail_no_none {F : Type}
    (state : PanSemStateFiniteExact 64 F) (codeVal : BitVec 64)
    (hcode : state.code = originalRuntimeCode) :
    (evaluateHOLFiniteState state
      (.call (some (none, none)) (ofString "rlp_fail") [.const codeVal])).1 ≠ none := by
  rw [evaluateHOLFiniteState_call]
  have hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [.const codeVal] =
      some [.val (.word codeVal)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
  have hlookup := pan_one_word_lookup state.code.lookup (ofString "rlp_fail") (ofString "code")
    (sourceFnBody Guest.Software.guestFn_rlp_fail) codeVal (by rw [hcode]; exact lookup_rlp_fail)
  rw [hargs]
  dsimp only
  rw [hlookup]
  dsimp only
  split
  · simp
  · have hout := evaluate_rlp_fail_body_outcomes
      (callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "code", .val (.word codeVal))))
    rcases hbody : evaluateHOLFiniteState
      (callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "code", .val (.word codeVal))))
      (sourceFnBody Guest.Software.guestFn_rlp_fail) with ⟨res, st⟩
    rw [hbody] at hout
    cases res with
    | none => exact absurd rfl hout.1
    | some r =>
      cases r with
      | returned v => exact absurd rfl (hout.2 v)
      | «break» | «continue» | error | timeOut | finalFfi _ | exception _ _ => simp

theorem lookup_rlp_read_length :
    originalRuntimeCode.lookup (ofString "rlp_read_length") =
      some ([(ofString "p", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_read_length, .one) :=
  lookup_of_guestAst_getElem 106 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_read_length) rfl

theorem runBounded_rlp_read_length {F : Type}
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
      (keepN result (by decide)).trans atN
    apply RunBounded.decConst
    apply RunBounded.decConst
    let s0 := setVarHOLFinite (ofString "i") (.val (.word 0))
      (setVarHOLFinite (ofString "v") (.val (.word 0)) next)
    have hs0_code : s0.code = originalRuntimeCode := nextCode.trans hcode
    have hs0_i : s0.locals.lookup (ofString "i") = some (.val (.word 0)) := by
      simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hs0_n : s0.locals.lookup (ofString "n") = some (.val (.word K)) := by
      simp only [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hnext_n]
      rw [if_neg (by decide), if_neg (by decide)]
    have hs0_clk : s0.clock = next.clock := rfl
    refine (RunBounded.seq (state := s0) (a := K.toNat * (0 + 1)) (b := 0) ?_
      (by rw [hs0_clk]; omega) ?_).weaken (by omega)
    · unfold RunBounded
      exact variableCountedWhile_run (ofString "i") (ofString "n") .lower (Or.inr rfl) K
        (fun h => by cases h)
        (countedBody_seq_straight _ (by decide) (by decide) (by decide) CountedBody.incr)
        (by decide) K.toNat s0 hs0_code 0 hs0_i hs0_n (by simp) (by simp)
        (by simp only [Nat.zero_add, Nat.mul_one]; rw [hs0_clk]; omega)
    · intro last _ lastCode _
      exact (ProgBounded.straight _ rfl) last (lastCode.trans hs0_code) (Nat.zero_le _)

private theorem progBounded_decCall_rlp_read_length
    (name : MlS) (pExp sizeExp : ExpHOL 64) {cont : ProgHOL 64} {tailCost : Nat}
    (M : Nat)
    (heval : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      ∀ v, evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) sizeExp = some v →
        ∃ K : BitVec 64, v = .val (.word K) ∧ K.toNat ≤ M)
    (hcont : ProgBounded cont tailCost) :
    ProgBounded (.decCall name .one (ofString "rlp_read_length") [pExp, sizeExp] cont)
      ((M + 1) + 1 + tailCost) := by
  intro F state hcode hbudget
  cases hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [pExp, sizeExp] with
  | none =>
    rw [evaluateHOLFiniteState_decCall_args_none state name .one (ofString "rlp_read_length") [pExp, sizeExp] cont hargs]
    simp
  | some vs =>
    have hex : ∃ v2, evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) sizeExp = some v2 := by
      rw [evalListHOLFinite_eq_toExact] at hargs
      rw [evalHOLFinite_eq_toExact]
      rcases h1 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) pExp with _ | v1
      · simp [evalListHOLExact, h1] at hargs
      · rcases h2 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) sizeExp with _ | v2
        · simp [evalListHOLExact, h1, h2] at hargs
        · exact ⟨v2, rfl⟩
    obtain ⟨v2, hv2⟩ := hex
    obtain ⟨K, rfl, hK_le⟩ := heval state v2 hv2
    obtain ⟨v1, rfl⟩ := evalListHOLFinite_two_word2_local state pExp sizeExp K hargs hv2
    have h := RunBounded.decCall (state := state) (shape := .one) (bodyCost := K.toNat + 1) (tailCost := tailCost)
      hargs (by omega)
      (fun body locals rs hfound => by
        rw [hcode] at hfound
        obtain ⟨rfl, hn⟩ := two_arg_lookup_n_local originalRuntimeCode.lookup
          (ofString "rlp_read_length") (ofString "p") (sourceFnBody Guest.Software.guestFn_rlp_read_length)
          (by decide) lookup_rlp_read_length hfound
        refine ⟨runBounded_rlp_read_length (callEntryStateHOLFinite state locals) K hcode hn
          (by change K.toNat + 1 ≤ state.clock - 1; omega), ?_⟩
        intro value post hran hpost_bud
        have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state locals)
          (sourceFnBody Guest.Software.guestFn_rlp_read_length)
        rw [hran] at hmeta
        exact hcont (setVarHOLFinite name value { post with locals := state.locals })
          (hmeta.1.trans hcode) hpost_bud)
    exact h.weaken (by omega)

theorem funBounded_rlp_read_length : FunBounded (ofString "rlp_read_length") (2 ^ 64) := by
  refine ⟨[(ofString "p", .one), (ofString "n", .one)],
    sourceFnBody Guest.Software.guestFn_rlp_read_length, .one,
    lookup_rlp_read_length, ?_⟩
  intro F state hcode hbudget
  rcases hn : state.locals.lookup (ofString "n") with _ | val
  · dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_read_length,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
    simp [evalHOLExact, evalListHOLExact, hn]
  · rcases val with ⟨⟨K⟩⟩ | fs | ⟨nm, fs⟩
    · exact (runBounded_rlp_read_length state K hcode hn (by have := K.isLt; omega)).weaken
        (by have := K.isLt; omega)
    · dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_read_length,
        InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
      simp [evalHOLExact, evalListHOLExact, hn]
    · dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_read_length,
        InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
      simp [evalHOLExact, evalListHOLExact, hn]

theorem funBounded_rlp_item_total_unchecked : FunBounded (ofString "rlp_item_total_unchecked") (2 ^ 64 + 1) := by
  refine funBounded_of_guestAst 114 (by rw [guestAst_len]; decide) Guest.Software.guestFn_rlp_item_total_unchecked (2 ^ 64 + 1) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_rlp_item_total_unchecked,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.dec _ _ _
      (progBounded_seq_ite_terminating
        (ProgBounded.straight _ rfl) rfl
        (progBounded_seq_ite_terminating
          (ProgBounded.straight _ rfl) rfl
          (progBounded_seq_ite_terminating
            (ProgBounded.dec _ _ _
              (ProgBounded.decCall funBounded_rlp_read_length _ _ _ (ProgBounded.straight _ rfl)))
            rfl
            (progBounded_seq_ite_terminating
              (ProgBounded.straight _ rfl) rfl
              (ProgBounded.dec _ _ _
                (ProgBounded.decCall funBounded_rlp_read_length _ _ _ (ProgBounded.straight _ rfl))))))))
    (by decide)

theorem funBounded_rlp_item_header : FunBounded (ofString "rlp_item_header") (2 ^ 64 + 5) := by
  refine funBounded_of_guestAst 109 (by rw [guestAst_len]; decide) Guest.Software.guestFn_rlp_item_header _ rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_rlp_item_header,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.seq
      (ProgBounded.iteMax _ (ProgBounded.call funBounded_rlp_fail none _) (ProgBounded.straight _ rfl))
      (ProgBounded.dec _ _ _
        (progBounded_seq_ite_terminating
          (ProgBounded.straight _ rfl) rfl
          (progBounded_seq_ite_terminating
            (ProgBounded.dec _ _ _
              (ProgBounded.seq
                (ProgBounded.iteMax _ (ProgBounded.call funBounded_rlp_fail none _) (ProgBounded.straight _ rfl))
                (ProgBounded.seq
                  (ProgBounded.iteMax _
                    (ProgBounded.iteMax _ (ProgBounded.call funBounded_rlp_fail none _) (ProgBounded.straight _ rfl))
                    (ProgBounded.straight _ rfl))
                  (ProgBounded.straight _ rfl))))
            rfl
            (progBounded_seq_ite_terminating
              (ProgBounded.dec _ _ _
                (ProgBounded.seq
                  (ProgBounded.iteMax _ (ProgBounded.call funBounded_rlp_fail none _) (ProgBounded.straight _ rfl))
                  (ProgBounded.decCall funBounded_rlp_read_length _ _ _
                    (ProgBounded.seq
                      (ProgBounded.iteMax _ (ProgBounded.call funBounded_rlp_fail none _) (ProgBounded.straight _ rfl))
                      (ProgBounded.seq
                        (ProgBounded.iteMax _ (ProgBounded.call funBounded_rlp_fail none _) (ProgBounded.straight _ rfl))
                        (ProgBounded.straight _ rfl))))))
              rfl
              (progBounded_seq_ite_terminating
                (ProgBounded.dec _ _ _
                  (ProgBounded.seq
                    (ProgBounded.iteMax _ (ProgBounded.call funBounded_rlp_fail none _) (ProgBounded.straight _ rfl))
                    (ProgBounded.straight _ rfl)))
                rfl
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

theorem funBounded_rlp_validate_items (Kv : Nat)
    (hv : FunBounded (ofString "_rlp_validate_items_body") Kv) :
    FunBounded (ofString "rlp_validate_items") (1 + (Kv + 1 + 1) + 1) := by
  refine funBounded_of_guestAst 111 (by rw [guestAst_len]; decide) Guest.Software.guestFn_rlp_validate_items _ rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_rlp_validate_items,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_scratch_mark _ _ _
      (ProgBounded.dec _ _ _
        (ProgBounded.seq
          (ProgBounded.handledCall hv _ _ none _
            (ProgBounded.seq
              (ProgBounded.call funBounded_scratch_release none _)
              (ProgBounded.straight _ rfl)))
          (ProgBounded.seq
            (ProgBounded.call funBounded_scratch_release none _)
            (ProgBounded.straight _ rfl)))))
    (by omega)

theorem funBounded_rlp_item_total (Kv : Nat)
    (hv : FunBounded (ofString "_rlp_validate_items_body") Kv) :
    FunBounded (ofString "rlp_item_total") ((2 ^ 64 + 5) + 1 + ((1 + (Kv + 1 + 1) + 1) + 1)) := by
  refine funBounded_of_guestAst 112 (by rw [guestAst_len]; decide) Guest.Software.guestFn_rlp_item_total _ rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_rlp_item_total,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_rlp_item_header _ _ _
      (ProgBounded.seq
        (ProgBounded.iteMax _
          (ProgBounded.call (funBounded_rlp_validate_items Kv hv) none _)
          (ProgBounded.straight _ rfl))
        (ProgBounded.straight _ rfl)))
    (by omega)

private theorem seq_returned_inv {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {p1 p2 : ProgHOL 64} {retVal : ValueHOL 64}
    (h : evaluateHOLFiniteState s (.seq p1 p2) = (some (.returned retVal), post)) :
    evaluateHOLFiniteState s p1 = (some (.returned retVal), post) ∨
      ∃ mid, evaluateHOLFiniteState s p1 = (none, mid) ∧
        evaluateHOLFiniteState mid p2 = (some (.returned retVal), post) := by
  rw [evaluateHOLFiniteState_seq_line780] at h
  rcases h1 : evaluateHOLFiniteState s p1 with ⟨r1, mid⟩
  rw [h1] at h
  cases r1 with
  | none => exact Or.inr ⟨mid, rfl, h⟩
  | some _ => exact Or.inl h

private theorem seq_fail_guard_returned_inv {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {cond : ExpHOL 64} {codeVal : BitVec 64} {tail : ProgHOL 64} {retVal : ValueHOL 64}
    (hcode : s.code = originalRuntimeCode)
    (h : evaluateHOLFiniteState s (.seq (.ite cond (.call (some (none, none)) (ofString "rlp_fail") [.const codeVal]) .skip) tail) =
      (some (.returned retVal), post)) :
    ∃ cw : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond = some (.val (.word cw)) ∧
      cw = 0 ∧
      evaluateHOLFiniteState s tail = (some (.returned retVal), post) := by
  have hcall_no_ret : ∀ w,
      (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "rlp_fail") [.const codeVal])).1 ≠ some (.returned w) := by
    intro w
    rw [evaluateHOLFiniteState_call]
    have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [.const codeVal] =
        some [.val (.word codeVal)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
    have hlk := pan_one_word_lookup s.code.lookup (ofString "rlp_fail") (ofString "code")
      (sourceFnBody Guest.Software.guestFn_rlp_fail) codeVal (by rw [hcode]; exact lookup_rlp_fail)
    rw [hargs]; dsimp only; rw [hlk]; dsimp only
    split
    · simp
    · have hout := evaluate_rlp_fail_body_outcomes
        (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "code", .val (.word codeVal))))
      rcases hb : evaluateHOLFiniteState _ (sourceFnBody Guest.Software.guestFn_rlp_fail) with ⟨res, st⟩
      rw [hb] at hout
      cases res with
      | none => exact absurd rfl hout.1
      | some r =>
        cases r with
        | returned v => exact absurd rfl (hout.2 v)
        | «break» | «continue» | error | timeOut | finalFfi _ | exception _ _ => simp
  have hcall_no_none := evaluate_call_rlp_fail_no_none s codeVal hcode
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at h
  rcases hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond with _ | cv
  · simp [hcond] at h
  · rcases cv with ⟨⟨cw⟩⟩ | _ | _
    · rw [hcond] at h
      by_cases hcz : cw = 0
      · subst hcz
        simp only [ ↓reduceIte, evaluateHOLFiniteState_skip] at h
        exact ⟨0, rfl, rfl, h⟩
      · simp only [hcz, ↓reduceIte] at h
        rcases hc : evaluateHOLFiniteState s (.call (some (none, none)) (ofString "rlp_fail") [.const codeVal]) with ⟨rc, sc⟩
        rw [hc] at h hcall_no_none hcall_no_ret
        cases rc with
        | none => exact absurd rfl hcall_no_none
        | some r' => exact absurd (congrArg Prod.fst h) (hcall_no_ret retVal)
    · simp [hcond] at h
    · simp [hcond] at h

private theorem dec_returned_inv {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {name : MlS} {sh : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64} {retVal : ValueHOL 64}
    (h : evaluateHOLFiniteState s (.dec name sh init body) = (some (.returned retVal), post)) :
    ∃ val inner,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) init = some val ∧
      shapeEqHOL sh (shapeOfHOLExact val) = true ∧
      evaluateHOLFiniteState (setVarHOLFinite name val s) body = (some (.returned retVal), inner) ∧
      post = { inner with locals := HolFiniteMapExact.resVarEq inner.locals (name, s.locals.lookup name) } := by
  rw [evaluateHOLFiniteState_dec_total] at h
  dsimp only at h
  rcases hi : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) init with _ | val
  · rw [hi] at h; simp at h
  · rw [hi] at h; dsimp only at h
    by_cases hsh : shapeEqHOL sh (shapeOfHOLExact val) = true
    · rw [if_pos hsh] at h
      rcases hb : evaluateHOLFiniteState (setVarHOLFinite name val s) body with ⟨rb, inner⟩
      rw [hb] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact ⟨val, inner, rfl, hsh, hb, rfl⟩
    · rw [if_neg hsh] at h; simp at h

private theorem decCall_returned_inv {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {name fn : MlS} {sh : ShapeHOL} {args : List (ExpHOL 64)} {cont : ProgHOL 64} {retVal : ValueHOL 64}
    (h : evaluateHOLFiniteState s (.decCall name sh fn args cont) = (some (.returned retVal), post)) :
    ∃ values fbody callee rsh retCallee post1 inner,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values ∧
      lookupCodeHOLFinite s.code.lookup fn values = some (fbody, callee, rsh) ∧
      s.clock ≠ 0 ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) fbody = (some (.returned retCallee), post1) ∧
      shapeEqHOL (shapeOfHOLExact retCallee) sh = true ∧
      shapeEqHOL (shapeOfHOLExact retCallee) rsh = true ∧
      evaluateHOLFiniteState (setVarHOLFinite name retCallee { post1 with locals := s.locals }) cont =
        (some (.returned retVal), inner) := by
  rw [evaluateHOLFiniteState_decCall_total] at h
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · rw [hargs] at h; simp at h
  · rw [hargs] at h; dsimp only at h
    rcases hlk : lookupCodeHOLFinite s.code.lookup fn values with _ | ⟨fbody, callee, rsh⟩
    · rw [hlk] at h; simp at h
    · rw [hlk] at h; dsimp only at h
      by_cases hclk : s.clock = 0
      · rw [if_pos hclk] at h; simp at h
      · rw [if_neg hclk] at h
        have hrem := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s callee) fbody
        rcases hcal : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) fbody with ⟨r1, post1⟩
        rw [hcal] at h hrem
        have hfix : fixClockHOLFinite (callEntryStateHOLFinite s callee) (r1, post1) = (r1, post1) := by
          simp [fixClockHOLFinite, Nat.not_lt.mpr hrem]
        rw [hfix] at h
        dsimp only at h
        rcases r1 with _ | (_ | _ | _ | _ | retCallee | _ | _)
        all_goals try (simp at h)
        by_cases hsh2 : shapeEqHOL (shapeOfHOLExact retCallee) sh = true ∧ shapeEqHOL (shapeOfHOLExact retCallee) rsh = true
        · rw [if_pos hsh2] at h
          rcases hcont : evaluateHOLFiniteState (setVarHOLFinite name retCallee { post1 with locals := s.locals }) cont with ⟨rc, inner⟩
          rw [hcont] at h
          obtain ⟨rfl, _⟩ := Prod.mk.inj h
          exact ⟨values, fbody, callee, rsh, retCallee, post1, inner, rfl, hlk, hclk, hcal, hsh2.1, hsh2.2, hcont⟩
        · rw [if_neg hsh2] at h; simp at h

private theorem return_returned_inv {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {e : ExpHOL 64} {retVal : ValueHOL 64}
    (h : evaluateHOLFiniteState s (.return e) = (some (.returned retVal), post)) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e = some retVal := by
  rw [evaluateHOLFiniteState_return] at h
  rcases he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | v
  · rw [he] at h; simp at h
  · rw [he] at h; dsimp only at h
    split at h
    · simp at h; obtain ⟨rfl, _⟩ := h; rfl
    · simp at h

private theorem pan_two_word_lookup_any {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name first second : MlS) (body : ProgHOL width) (rs : ShapeHOL) (left right : BitVec width)
    (different : first ≠ second)
    (lookup : code name = some ([(first, .one), (second, .one)], body, rs)) :
    PanSemStateFiniteExact.lookupCodeHOLFinite code name [.val (.word left), .val (.word right)] =
      some (body, (HolFiniteMapExact.empty.update (first, .val (.word left))).update (second, .val (.word right)), rs) := by
  have raw : lookupCodeHOLExact code name [.val (.word left), .val (.word right)] =
      some (body, (fun key => if key = second then some (.val (.word right)) else if key = first then some (.val (.word left)) else none), rs) := by
    simp [lookupCodeHOLExact, lookup, shapeOfHOLExact, shapeEqHOL, different]
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
    by_cases one : key = first
    · subst key
      simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY, different, Ne.symm different]
    · have backOne : first ≠ key := Ne.symm one
      by_cases two : key = second
      · subst key
        simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY]
      · have backTwo : second ≠ key := Ne.symm two
        simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY, one, two, backOne, backTwo]

theorem lookup_rlp_item_header :
    originalRuntimeCode.lookup (ofString "rlp_item_header") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_item_header,
        .comb [.one, .one, .one]) :=
  lookup_of_guestAst_getElem 109 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_item_header) rfl

theorem lookup_rlp_item_total :
    originalRuntimeCode.lookup (ofString "rlp_item_total") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_item_total,
        .one) :=
  lookup_of_guestAst_getElem 112 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_item_total) rfl

private theorem seq_ite_terminating_returned_inv {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {cond : ExpHOL 64} {yes tail : ProgHOL 64} {retVal : ValueHOL 64}
    (hm : mustTerminate yes = true)
    (h : evaluateHOLFiniteState s (.seq (.ite cond yes .skip) tail) = (some (.returned retVal), post)) :
    (∃ cw : BitVec 64,
        @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond = some (.val (.word cw)) ∧
        cw ≠ 0 ∧
        evaluateHOLFiniteState s yes = (some (.returned retVal), post)) ∨
      (∃ cw : BitVec 64,
        @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond = some (.val (.word cw)) ∧
        cw = 0 ∧
        evaluateHOLFiniteState s tail = (some (.returned retVal), post)) := by
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at h
  rcases hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond with _ | cv
  · simp [hcond] at h
  · rcases cv with ⟨⟨cw⟩⟩ | _ | _
    · rw [hcond] at h
      by_cases hcz : cw = 0
      · subst hcz
        simp only [↓reduceIte, evaluateHOLFiniteState_skip] at h
        exact Or.inr ⟨0, rfl, rfl, h⟩
      · simp only [hcz, ↓reduceIte] at h
        have hnn := evaluate_mustTerminate yes hm s
        rcases hy : evaluateHOLFiniteState s yes with ⟨ry, mid⟩
        rw [hy] at h
        cases ry with
        | none => exact absurd (congrArg Prod.fst hy) hnn
        | some _ => exact Or.inl ⟨cw, rfl, hcz, h⟩
    · simp [hcond] at h
    · simp [hcond] at h

private theorem shapeEq_one_word {v : ValueHOL 64}
    (h : shapeEqHOL .one (shapeOfHOLExact v) = true ∨ shapeEqHOL (shapeOfHOLExact v) .one = true) :
    ∃ w : BitVec 64, v = .val (.word w) := by
  cases v with
  | val wl => cases wl with | word w => exact ⟨w, rfl⟩
  | rStruct _ => rcases h with h | h <;> simp [shapeOfHOLExact, shapeEqHOL] at h
  | nStruct _ _ => rcases h with h | h <;> simp [shapeOfHOLExact, shapeEqHOL] at h

private theorem fail_guard_lower_returned_inv {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {e1 e2 : ExpHOL 64} {w1 w2 codeVal : BitVec 64} {tail : ProgHOL 64} {retVal : ValueHOL 64}
    (hcode : s.code = originalRuntimeCode)
    (he1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 = some (.val (.word w1)))
    (he2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e2 = some (.val (.word w2)))
    (h : evaluateHOLFiniteState s (.seq (.ite (.cmp .lower e1 e2) (.call (some (none, none)) (ofString "rlp_fail") [.const codeVal]) .skip) tail) =
      (some (.returned retVal), post)) :
    w2.toNat ≤ w1.toNat ∧ evaluateHOLFiniteState s tail = (some (.returned retVal), post) := by
  obtain ⟨cw, hcond, hcw_z, htail⟩ := seq_fail_guard_returned_inv hcode h
  refine ⟨?_, htail⟩
  simp only [evalHOLExact, he1, he2, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq] at hcond
  injection hcond with hv; injection hv with hwl; injection hwl with hcw
  by_cases hlt : w1.toNat < w2.toNat
  · rw [if_pos hlt] at hcw; exact absurd (hcw.trans hcw_z) (by decide)
  · omega

private theorem nested_fail_guard_returned_inv {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {c1 c2 : ExpHOL 64} {codeVal : BitVec 64} {tail : ProgHOL 64} {retVal : ValueHOL 64}
    (hcode : s.code = originalRuntimeCode)
    (h : evaluateHOLFiniteState s
      (.seq (.ite c1 (.ite c2 (.call (some (none, none)) (ofString "rlp_fail") [.const codeVal]) .skip) .skip) tail) =
      (some (.returned retVal), post)) :
    evaluateHOLFiniteState s tail = (some (.returned retVal), post) := by
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at h
  rcases hc1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) c1 with _ | v1
  · simp [hc1] at h
  · rcases v1 with ⟨⟨w1⟩⟩ | _ | _
    · rw [hc1] at h
      by_cases hw1 : w1 = 0
      · subst hw1; simp only [↓reduceIte, evaluateHOLFiniteState_skip] at h; exact h
      · simp only [hw1, ↓reduceIte] at h
        have h2 : evaluateHOLFiniteState s (.seq (.ite c2 (.call (some (none, none)) (ofString "rlp_fail") [.const codeVal]) .skip) tail) =
            (some (.returned retVal), post) := by
          rw [evaluateHOLFiniteState_seq_line780]; exact h
        exact (seq_fail_guard_returned_inv hcode h2).2.2
    · simp [hc1] at h
    · simp [hc1] at h

private theorem eval_var_local {F : Type} (s : PanSemStateFiniteExact 64 F) {x : MlS} {v : ValueHOL 64}
    (hx : s.locals.lookup x = some v) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.var .local x) = some v := by
  simp [evalHOLExact, hx]

private theorem eval_const_word {F : Type} (s : PanSemStateFiniteExact 64 F) (c : BitVec 64) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.const c) = some (.val (.word c)) := rfl

private theorem eval_sub_word_local {F : Type} (s : PanSemStateFiniteExact 64 F)
    {e1 e2 : ExpHOL 64} {w1 w2 : BitVec 64}
    (h1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 = some (.val (.word w1)))
    (h2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e2 = some (.val (.word w2))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.op .sub [e1, e2]) =
      some (.val (.word (w1 - w2))) := by
  simp [evalHOLExact, evalListHOLExact, h1, h2, wordOpHOL, wordOp, valueIsWord, valueWord]

private theorem rlp_item_header_returned_bounds {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {len : BitVec 64} {retVal : ValueHOL 64}
    (hcode : s.code = originalRuntimeCode)
    (hlen : s.locals.lookup (ofString "len") = some (.val (.word len)))
    (h : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_item_header) =
      (some (.returned retVal), post)) :
    ∃ hlen_w n_w k_w : BitVec 64,
      retVal = .rStruct [.val (.word hlen_w), .val (.word n_w), .val (.word k_w)] ∧
      1 ≤ (hlen_w + n_w).toNat ∧
      (hlen_w + n_w).toNat ≤ len.toNat := by
  have hlen_lt : len.toNat < 2 ^ 64 := len.isLt
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_item_header,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at h
  obtain ⟨cw0, hcond0, hcw0_z, h1⟩ := seq_fail_guard_returned_inv hcode h
  have hlen_pos : 0 < len.toNat := by
    simp only [evalHOLExact, hlen, Compiler.Encoders.Asm.wordCmpHOL, beq_iff_eq] at hcond0
    injection hcond0 with hv; injection hv with hwl; injection hwl with hcw
    by_cases hz : len.toNat = 0
    · have hzeq : len = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hz)
      rw [if_pos hzeq] at hcw; exact absurd (hcw.trans hcw0_z) (by decide)
    · omega
  have hlen_m1 : (len - 1#64).toNat = len.toNat - 1 :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; change 1 ≤ len.toNat; omega)
  obtain ⟨bVal, _, _, hsh_b, h2, _⟩ := dec_returned_inv h1
  obtain ⟨b, rfl⟩ := shapeEq_one_word (Or.inl hsh_b)
  let s_b := setVarHOLFinite (ofString "b") (.val (.word b)) s
  have hsb_code : s_b.code = originalRuntimeCode := hcode
  have hsb_len : s_b.locals.lookup (ofString "len") = some (.val (.word len)) := by
    simp [s_b, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlen, show ofString "b" ≠ ofString "len" by decide]
  change evaluateHOLFiniteState s_b _ = _ at h2
  rcases seq_ite_terminating_returned_inv rfl h2 with ⟨_, _, _, hbr1⟩ | ⟨_, _, _, h3⟩
  · have hret := return_returned_inv hbr1
    simp only [evalHOLExact, evalListHOLExact, Option.map] at hret
    injection hret with hrv; subst hrv
    refine ⟨0#64, 1#64, 0#64, rfl, by decide, ?_⟩
    have : (0#64 + 1#64).toNat = 1 := by decide
    omega
  · rcases seq_ite_terminating_returned_inv rfl h3 with ⟨_, _, _, hbr2⟩ | ⟨_, _, _, h4⟩
    · obtain ⟨nVal, _, _, hsh_n, hb2_1, _⟩ := dec_returned_inv hbr2
      obtain ⟨n_w, rfl⟩ := shapeEq_one_word (Or.inl hsh_n)
      let s_n := setVarHOLFinite (ofString "n") (.val (.word n_w)) s_b
      have hsn_code : s_n.code = originalRuntimeCode := hsb_code
      have hsn_n : s_n.locals.lookup (ofString "n") = some (.val (.word n_w)) := by
        simp [s_n, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hsn_len : s_n.locals.lookup (ofString "len") = some (.val (.word len)) := by
        simp [s_n, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsb_len, show ofString "n" ≠ ofString "len" by decide]
      change evaluateHOLFiniteState s_n _ = _ at hb2_1
      obtain ⟨hn_le, hb2_2⟩ := fail_guard_lower_returned_inv hsn_code
        (eval_sub_word_local s_n (eval_var_local s_n hsn_len) (eval_const_word s_n 1#64)) (eval_var_local s_n hsn_n) hb2_1
      have hb2_3 := nested_fail_guard_returned_inv hsn_code hb2_2
      have hret := return_returned_inv hb2_3
      simp only [evalHOLExact, evalListHOLExact, hsn_n, Option.map] at hret
      injection hret with hrv; subst hrv
      have hadd : (1#64 + n_w).toNat = 1 + n_w.toNat := by
        rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by change 1 + n_w.toNat < 2 ^ 64; omega)]; rfl
      exact ⟨1#64, n_w, 0#64, rfl, by omega, by omega⟩
    · rcases seq_ite_terminating_returned_inv rfl h4 with ⟨_, _, _, hbr3⟩ | ⟨_, _, _, h5⟩
      · obtain ⟨llVal, _, _, hsh_ll, hb3_1, _⟩ := dec_returned_inv hbr3
        obtain ⟨ll_w, rfl⟩ := shapeEq_one_word (Or.inl hsh_ll)
        let s_ll := setVarHOLFinite (ofString "ll") (.val (.word ll_w)) s_b
        have hsll_code : s_ll.code = originalRuntimeCode := hsb_code
        have hsll_ll : s_ll.locals.lookup (ofString "ll") = some (.val (.word ll_w)) := by
          simp [s_ll, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hsll_len : s_ll.locals.lookup (ofString "len") = some (.val (.word len)) := by
          simp [s_ll, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsb_len, show ofString "ll" ≠ ofString "len" by decide]
        change evaluateHOLFiniteState s_ll _ = _ at hb3_1
        obtain ⟨hll_le, hb3_2⟩ := fail_guard_lower_returned_inv hsll_code
          (eval_sub_word_local s_ll (eval_var_local s_ll hsll_len) (eval_const_word s_ll 1#64)) (eval_var_local s_ll hsll_ll) hb3_1
        obtain ⟨_, fbodyN, calleeN, _, retN, postN, _, _, _, _, hcalN, hshN, _, hb3_3⟩ := decCall_returned_inv hb3_2
        obtain ⟨n_w, rfl⟩ := shapeEq_one_word (Or.inr hshN)
        let s_n := setVarHOLFinite (ofString "n") (.val (.word n_w)) { postN with locals := s_ll.locals }
        have hsn_code : s_n.code = originalRuntimeCode := by
          have hm := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s_ll calleeN) fbodyN).1
          rw [hcalN] at hm; exact hm.trans hsll_code
        have hsn_n : s_n.locals.lookup (ofString "n") = some (.val (.word n_w)) := by
          simp [s_n, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hsn_ll : s_n.locals.lookup (ofString "ll") = some (.val (.word ll_w)) := by
          simp [s_n, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsll_ll, show ofString "n" ≠ ofString "ll" by decide]
        have hsn_len : s_n.locals.lookup (ofString "len") = some (.val (.word len)) := by
          simp [s_n, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsll_len, show ofString "n" ≠ ofString "len" by decide]
        obtain ⟨_, _, _, hb3_4⟩ := seq_fail_guard_returned_inv hsn_code hb3_3
        obtain ⟨hn_le, hb3_5⟩ := fail_guard_lower_returned_inv hsn_code
          (eval_sub_word_local s_n (eval_sub_word_local s_n (eval_var_local s_n hsn_len) (eval_const_word s_n 1#64)) (eval_var_local s_n hsn_ll))
          (eval_var_local s_n hsn_n) hb3_4
        have hsub_ll : ((len - 1#64) - ll_w).toNat = len.toNat - 1 - ll_w.toNat := by
          rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega), hlen_m1]
        have hret := return_returned_inv hb3_5
        simp only [evalHOLExact, evalListHOLExact, hsn_ll, hsn_n, wordOpHOL, wordOp, valueIsWord, valueWord,
          List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr] at hret
        injection hret with hrv; subst hrv
        have hz0 : ll_w + (0 : BitVec 64) = ll_w := BitVec.add_zero ll_w
        rw [hz0]
        have h1ll : (1#64 + ll_w).toNat = 1 + ll_w.toNat := by
          rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by change 1 + ll_w.toNat < 2 ^ 64; omega)]; rfl
        have htot : ((1#64 + ll_w) + n_w).toNat = (1#64 + ll_w).toNat + n_w.toNat := by
          rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
        exact ⟨1#64 + ll_w, n_w, 0#64, rfl, by omega, by omega⟩
      · rcases seq_ite_terminating_returned_inv rfl h5 with ⟨_, _, _, hbr4⟩ | ⟨_, _, _, h6⟩
        · obtain ⟨nVal, _, _, hsh_n, hb4_1, _⟩ := dec_returned_inv hbr4
          obtain ⟨n_w, rfl⟩ := shapeEq_one_word (Or.inl hsh_n)
          let s_n := setVarHOLFinite (ofString "n") (.val (.word n_w)) s_b
          have hsn_code : s_n.code = originalRuntimeCode := hsb_code
          have hsn_n : s_n.locals.lookup (ofString "n") = some (.val (.word n_w)) := by
            simp [s_n, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hsn_len : s_n.locals.lookup (ofString "len") = some (.val (.word len)) := by
            simp [s_n, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsb_len, show ofString "n" ≠ ofString "len" by decide]
          change evaluateHOLFiniteState s_n _ = _ at hb4_1
          obtain ⟨hn_le, hb4_2⟩ := fail_guard_lower_returned_inv hsn_code
            (eval_sub_word_local s_n (eval_var_local s_n hsn_len) (eval_const_word s_n 1#64)) (eval_var_local s_n hsn_n) hb4_1
          have hret := return_returned_inv hb4_2
          simp only [evalHOLExact, evalListHOLExact, hsn_n, Option.map] at hret
          injection hret with hrv; subst hrv
          have hadd : (1#64 + n_w).toNat = 1 + n_w.toNat := by
            rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by change 1 + n_w.toNat < 2 ^ 64; omega)]; rfl
          exact ⟨1#64, n_w, 1#64, rfl, by omega, by omega⟩
        · obtain ⟨llVal, _, _, hsh_ll, hb5_1, _⟩ := dec_returned_inv h6
          obtain ⟨ll_w, rfl⟩ := shapeEq_one_word (Or.inl hsh_ll)
          let s_ll := setVarHOLFinite (ofString "ll") (.val (.word ll_w)) s_b
          have hsll_code : s_ll.code = originalRuntimeCode := hsb_code
          have hsll_ll : s_ll.locals.lookup (ofString "ll") = some (.val (.word ll_w)) := by
            simp [s_ll, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hsll_len : s_ll.locals.lookup (ofString "len") = some (.val (.word len)) := by
            simp [s_ll, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsb_len, show ofString "ll" ≠ ofString "len" by decide]
          change evaluateHOLFiniteState s_ll _ = _ at hb5_1
          obtain ⟨hll_le, hb5_2⟩ := fail_guard_lower_returned_inv hsll_code
            (eval_sub_word_local s_ll (eval_var_local s_ll hsll_len) (eval_const_word s_ll 1#64)) (eval_var_local s_ll hsll_ll) hb5_1
          obtain ⟨_, fbodyN, calleeN, _, retN, postN, _, _, _, _, hcalN, hshN, _, hb5_3⟩ := decCall_returned_inv hb5_2
          obtain ⟨n_w, rfl⟩ := shapeEq_one_word (Or.inr hshN)
          let s_n := setVarHOLFinite (ofString "n") (.val (.word n_w)) { postN with locals := s_ll.locals }
          have hsn_code : s_n.code = originalRuntimeCode := by
            have hm := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s_ll calleeN) fbodyN).1
            rw [hcalN] at hm; exact hm.trans hsll_code
          have hsn_n : s_n.locals.lookup (ofString "n") = some (.val (.word n_w)) := by
            simp [s_n, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hsn_ll : s_n.locals.lookup (ofString "ll") = some (.val (.word ll_w)) := by
            simp [s_n, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsll_ll, show ofString "n" ≠ ofString "ll" by decide]
          have hsn_len : s_n.locals.lookup (ofString "len") = some (.val (.word len)) := by
            simp [s_n, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsll_len, show ofString "n" ≠ ofString "len" by decide]
          obtain ⟨_, _, _, hb5_4⟩ := seq_fail_guard_returned_inv hsn_code hb5_3
          obtain ⟨hn_le, hb5_5⟩ := fail_guard_lower_returned_inv hsn_code
            (eval_sub_word_local s_n (eval_sub_word_local s_n (eval_var_local s_n hsn_len) (eval_const_word s_n 1#64)) (eval_var_local s_n hsn_ll))
            (eval_var_local s_n hsn_n) hb5_4
          have hsub_ll : ((len - 1#64) - ll_w).toNat = len.toNat - 1 - ll_w.toNat := by
            rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega), hlen_m1]
          have hret := return_returned_inv hb5_5
          simp only [evalHOLExact, evalListHOLExact, hsn_ll, hsn_n, wordOpHOL, wordOp, valueIsWord, valueWord,
            List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr] at hret
          injection hret with hrv; subst hrv
          have hz0 : ll_w + (0 : BitVec 64) = ll_w := BitVec.add_zero ll_w
          rw [hz0]
          have h1ll : (1#64 + ll_w).toNat = 1 + ll_w.toNat := by
            rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by change 1 + ll_w.toNat < 2 ^ 64; omega)]; rfl
          have htot : ((1#64 + ll_w) + n_w).toNat = (1#64 + ll_w).toNat + n_w.toNat := by
            rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
          exact ⟨1#64 + ll_w, n_w, 1#64, rfl, by omega, by omega⟩

private theorem rlp_item_total_returned_bounds {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {p len : BitVec 64} {retVal : ValueHOL 64}
    (hcode : s.code = originalRuntimeCode)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word p)))
    (hlen : s.locals.lookup (ofString "len") = some (.val (.word len)))
    (h : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_item_total) =
      (some (.returned retVal), post)) :
    ∃ total_w : BitVec 64,
      retVal = .val (.word total_w) ∧
      1 ≤ total_w.toNat ∧
      total_w.toNat ≤ len.toNat := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_item_total,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at h
  obtain ⟨values, fbody, callee, rsh, retH, postH, _, hargs, hlk, _, hcalH, _, _, hcont⟩ :=
    decCall_returned_inv h
  have hvals : values = [.val (.word p), .val (.word len)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hp, hlen] at hargs
    exact hargs.symm
  subst hvals
  have hlk_exact := pan_two_word_lookup_any s.code.lookup (ofString "rlp_item_header")
    (ofString "p") (ofString "len") (sourceFnBody Guest.Software.guestFn_rlp_item_header)
    (.comb [.one, .one, .one]) p len (by decide) (by rw [hcode]; exact lookup_rlp_item_header)
  rw [hlk_exact] at hlk
  injection hlk with heq
  obtain ⟨rfl, heq2⟩ := Prod.mk.inj heq
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq2
  have hentry_code : (callEntryStateHOLFinite s
      ((HolFiniteMapExact.empty.update (ofString "p", .val (.word p))).update
        (ofString "len", .val (.word len)))).code = originalRuntimeCode := hcode
  have hentry_len : (callEntryStateHOLFinite s
      ((HolFiniteMapExact.empty.update (ofString "p", .val (.word p))).update
        (ofString "len", .val (.word len)))).locals.lookup (ofString "len") = some (.val (.word len)) := by
    simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  obtain ⟨hlen_w, n_w, k_w, rfl, hge1, hle_len⟩ :=
    rlp_item_header_returned_bounds hentry_code hentry_len hcalH
  let sh := setVarHOLFinite (ofString "h")
    (.rStruct [.val (.word hlen_w), .val (.word n_w), .val (.word k_w)])
    { postH with locals := s.locals }
  have hsh_h : sh.locals.lookup (ofString "h") =
      some (.rStruct [.val (.word hlen_w), .val (.word n_w), .val (.word k_w)]) := by
    simp [sh, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  let iteValProg : ProgHOL 64 :=
    .ite (.cmp .notEqual (.rfield 2 (.var .local (ofString "h"))) (.const 0#64))
      (.call (some (none, none)) (ofString "rlp_validate_items")
        [.op .add [.var .local (ofString "p"), .rfield 0 (.var .local (ofString "h"))],
         .rfield 1 (.var .local (ofString "h"))])
      .skip
  change evaluateHOLFiniteState sh (.seq iteValProg _) = _ at hcont
  rcases seq_returned_inv hcont with hite_ret | ⟨mid, hite_none, hret_run⟩
  · exfalso
    dsimp only [iteValProg] at hite_ret
    rw [evaluateHOLFiniteState_ite] at hite_ret
    split at hite_ret
    · split at hite_ret
      · rw [evaluateHOLFiniteState_skip] at hite_ret; simp at hite_ret
      · rw [evaluateHOLFiniteState_call] at hite_ret
        cases hargs_v : evalListHOLFinite sh (h := fun a => Classical.propDecidable (sh.memaddrs a))
            [.op .add [.var .local (ofString "p"), .rfield 0 (.var .local (ofString "h"))],
             .rfield 1 (.var .local (ofString "h"))] with
        | none => rw [hargs_v] at hite_ret; simp at hite_ret
        | some vs =>
          rw [hargs_v] at hite_ret; dsimp only at hite_ret
          cases hlk_v : PanSemStateFiniteExact.lookupCodeHOLFinite sh.code.lookup (ofString "rlp_validate_items") vs with
          | none => rw [hlk_v] at hite_ret; simp at hite_ret
          | some entry_v =>
            obtain ⟨b_v, c_v, rs_v⟩ := entry_v
            rw [hlk_v] at hite_ret; dsimp only at hite_ret
            by_cases hclk_v : sh.clock = 0
            · rw [if_pos hclk_v] at hite_ret; simp at hite_ret
            · rw [if_neg hclk_v] at hite_ret
              rcases hrun_v : evaluateHOLFiniteState (callEntryStateHOLFinite sh c_v) b_v with ⟨rv_v, st_v⟩
              rw [hrun_v] at hite_ret
              rcases rv_v with _ | (_ | _ | _ | _ | ret_v | ⟨eid_v, ev_v⟩ | _)
              all_goals simp at hite_ret
              split at hite_ret <;> simp at hite_ret
    · simp at hite_ret
  · have hmid_h : mid.locals.lookup (ofString "h") =
        some (.rStruct [.val (.word hlen_w), .val (.word n_w), .val (.word k_w)]) := by
      have hav := evaluate_avoidsLocal_flowing (ofString "h") iteValProg (by decide) sh (by rw [hite_none]; exact Or.inl rfl)
      rw [hite_none] at hav; exact hav.trans hsh_h
    have hret := return_returned_inv hret_run
    have hret_ev : @evalHOLExact 64 F _ mid.toExact (fun a => Classical.propDecidable (mid.memaddrs a))
        (.op .add [.rfield 0 (.var .local (ofString "h")), .rfield 1 (.var .local (ofString "h"))]) =
        some (.val (.word (hlen_w + n_w))) := by
      simp [evalHOLExact, evalListHOLExact, hmid_h, wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero]
    rw [hret_ev] at hret
    injection hret with hrv; subst hrv
    exact ⟨hlen_w + n_w, rfl, hge1, hle_len⟩

private def RlpListCountRank (len : BitVec 64) {F : Type} (s : PanSemStateFiniteExact 64 F) (n : Nat) : Prop :=
  ∃ off : BitVec 64,
    s.locals.lookup (ofString "off") = some (.val (.word off)) ∧
    s.locals.lookup (ofString "len") = some (.val (.word len)) ∧
    off.toNat ≤ len.toNat ∧
    len.toNat - off.toNat = n

theorem funBounded_rlp_list_count (Kv : Nat)
    (hval : FunBounded (ofString "_rlp_validate_items_body") Kv) :
    FunBounded (ofString "rlp_list_count") ((2 ^ 64 - 1) * (((2 ^ 64 + 11 + Kv) + 1) + 1)) := by
  have htot_fn : FunBounded (ofString "rlp_item_total") (2 ^ 64 + 11 + Kv) :=
    let ⟨p, b, r, hlk, hpb⟩ := funBounded_rlp_item_total Kv hval
    ⟨p, b, r, hlk, ProgBounded.weaken hpb (by omega)⟩
  refine ⟨[(ofString "p", .one), (ofString "len", .one)],
    sourceFnBody Guest.Software.guestFn_rlp_list_count, .one,
    lookup_of_guestAst_getElem 113 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_rlp_list_count) rfl, ?_⟩
  intro F state hcode hbudget
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_list_count,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply RunBounded.decConst
  apply RunBounded.decConst
  set s0 := setVarHOLFinite (ofString "off") (.val (.word 0#64))
    (setVarHOLFinite (ofString "count") (.val (.word 0#64)) state) with hs0_def
  have hs0_code : s0.code = originalRuntimeCode := hcode
  have hs0_off : s0.locals.lookup (ofString "off") = some (.val (.word 0#64)) := by
    simp [hs0_def, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs0_clk : s0.clock = state.clock := rfl
  rcases hlen_lk : s0.locals.lookup (ofString "len") with _ | lenVal
  · unfold RunBounded
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total]
    have hc : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
        (.cmp .lower (.var .local (ofString "off")) (.var .local (ofString "len"))) = none := by
      rw [evalHOLFinite_eq_toExact]; simp [evalHOLExact, hs0_off, hlen_lk]
    rw [hc]; simp
  · rcases lenVal with ⟨⟨len⟩⟩ | _ | _
    · let loopBody : ProgHOL 64 :=
        .decCall (ofString "total") .one (ofString "rlp_item_total")
          [.op .add [.var .local (ofString "p"), .var .local (ofString "off")],
           .op .sub [.var .local (ofString "len"), .var .local (ofString "off")]]
          (.seq
            (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"), .var .local (ofString "total")]))
            (.assign .local (ofString "count") (.op .add [.var .local (ofString "count"), .const 1#64])))
      let itemCost : Nat := (2 ^ 64 + 11 + Kv) + 1
      have hceil : len.toNat * (itemCost + 1) ≤ (2 ^ 64 - 1) * (itemCost + 1) :=
        Nat.mul_le_mul_right _ (by have := len.isLt; omega)
      have hranked := rankedWhile_run
        (.cmp .lower (.var .local (ofString "off")) (.var .local (ofString "len")))
        loopBody itemCost (RlpListCountRank len) False
        (by
          intro F' s hrk w hcond
          obtain ⟨off, hoff, hlen', hle, hdiff⟩ := hrk
          have heq : off.toNat = len.toNat := by omega
          rw [evalHOLFinite_eq_toExact] at hcond
          simp only [evalHOLExact, hoff, hlen', Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, heq, lt_irrefl, decide_false, Bool.false_eq_true, ↓reduceIte] at hcond
          injection hcond with hv; injection hv with hwl; injection hwl with hcw; exact hcw.symm)
        (by
          intro F' s n w hs_code hrk hcond hwnz hs_clk
          obtain ⟨off, hoff, hlen', hle, hdiff⟩ := hrk
          have hoff_lt_len : off.toNat < len.toNat := by omega
          set sd := decClockHOLFinite s
          have hsd_code : sd.code = originalRuntimeCode := hs_code
          have hsd_off : sd.locals.lookup (ofString "off") = some (.val (.word off)) := hoff
          have hsd_len : sd.locals.lookup (ofString "len") = some (.val (.word len)) := hlen'
          have hsd_clk : itemCost ≤ sd.clock := by change itemCost ≤ s.clock - 1; omega
          have hsd_eq : sd.clock = s.clock - 1 := rfl
          dsimp only [loopBody]
          rw [evaluateHOLFiniteState_decCall_total]
          rcases hp_lk : sd.locals.lookup (ofString "p") with _ | pVal
          · have hargs_none : evalListHOLFinite sd (h := fun a => Classical.propDecidable (sd.memaddrs a))
                [.op .add [.var .local (ofString "p"), .var .local (ofString "off")],
                 .op .sub [.var .local (ofString "len"), .var .local (ofString "off")]] = none := by
              simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hp_lk, hsd_off]
            rw [hargs_none]
            dsimp only
            exact ⟨by omega, by omega, by simp, by simp, by simp⟩
          · rcases pVal with ⟨⟨p_w⟩⟩ | _ | _
            · have hargs_some : evalListHOLFinite sd (h := fun a => Classical.propDecidable (sd.memaddrs a))
                  [.op .add [.var .local (ofString "p"), .var .local (ofString "off")],
                   .op .sub [.var .local (ofString "len"), .var .local (ofString "off")]] =
                  some [.val (.word (p_w + off)), .val (.word (len - off))] := by
                simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hp_lk, hsd_off, hsd_len,
                  wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero]
              rw [hargs_some]
              dsimp only
              have hlk_tot := pan_two_word_lookup_any sd.code.lookup (ofString "rlp_item_total")
                (ofString "p") (ofString "len") (sourceFnBody Guest.Software.guestFn_rlp_item_total) .one
                (p_w + off) (len - off) (by decide) (by rw [hsd_code]; exact lookup_rlp_item_total)
              rw [hlk_tot]
              dsimp only
              have hsd_nz : sd.clock ≠ 0 := by omega
              rw [if_neg hsd_nz]
              let calleeMap : HolFiniteMapExact MlS (ValueHOL 64) :=
                (HolFiniteMapExact.empty.update (ofString "p", .val (.word (p_w + off)))).update
                  (ofString "len", .val (.word (len - off)))
              have hcallee_bound := ProgBounded.bodies_of_fun htot_fn sd hsd_code
                (by omega)
                [.val (.word (p_w + off)), .val (.word (len - off))]
                (sourceFnBody Guest.Software.guestFn_rlp_item_total) calleeMap .one hlk_tot
              dsimp only at hcallee_bound
              have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite sd calleeMap)
                (sourceFnBody Guest.Software.guestFn_rlp_item_total)
              have hrem := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite sd calleeMap)
                (sourceFnBody Guest.Software.guestFn_rlp_item_total)
              rcases hcal : evaluateHOLFiniteState (callEntryStateHOLFinite sd calleeMap)
                  (sourceFnBody Guest.Software.guestFn_rlp_item_total) with ⟨r1, post1⟩
              rw [hcal] at hcallee_bound hmeta hrem
              dsimp only at hcallee_bound hmeta hrem
              have hfix : fixClockHOLFinite (callEntryStateHOLFinite sd calleeMap) (r1, post1) = (r1, post1) := by
                simp [fixClockHOLFinite, Nat.not_lt.mpr hrem]
              rw [hfix]
              dsimp only
              change sd.clock - 1 ≤ post1.clock + (2 ^ 64 + 11 + Kv) ∧ _ at hcallee_bound
              change post1.clock ≤ sd.clock - 1 at hrem
              have hsd_eq : sd.clock = s.clock - 1 := rfl
              rcases r1 with _ | (_ | _ | _ | _ | retV | _ | _)
              · exact ⟨by simp [emptyLocalsHOLFinite]; omega, by simp [emptyLocalsHOLFinite]; omega, by simp, by simp, by simp⟩
              · exact ⟨by simp [emptyLocalsHOLFinite]; omega, by simp [emptyLocalsHOLFinite]; omega, by simp, by simp, by simp⟩
              · exact absurd rfl hcallee_bound.2.2
              · exact ⟨by simp [emptyLocalsHOLFinite]; omega, by simp [emptyLocalsHOLFinite]; omega, by simp, by simp, by simp⟩
              · exact ⟨by simp [emptyLocalsHOLFinite]; omega, by simp [emptyLocalsHOLFinite]; omega, by simp, by simp, by simp⟩
              · have hentry_code : (callEntryStateHOLFinite sd calleeMap).code = originalRuntimeCode := hsd_code
                have hentry_p : (callEntryStateHOLFinite sd calleeMap).locals.lookup (ofString "p") =
                    some (.val (.word (p_w + off))) := by
                  simp [callEntryStateHOLFinite, calleeMap, HolFiniteMapExact.lookup_update, FUPDATE,
                    show ofString "len" ≠ ofString "p" by decide]
                have hentry_len : (callEntryStateHOLFinite sd calleeMap).locals.lookup (ofString "len") =
                    some (.val (.word (len - off))) := by
                  simp [callEntryStateHOLFinite, calleeMap, HolFiniteMapExact.lookup_update, FUPDATE]
                obtain ⟨tot_w, rfl, htot_ge1, htot_le_rem⟩ :=
                  rlp_item_total_returned_bounds hentry_code hentry_p hentry_len hcal
                dsimp only
                have hsh_ok : (shapeEqHOL (shapeOfHOLExact (.val (.word tot_w))) .one &&
                    shapeEqHOL (shapeOfHOLExact (.val (.word tot_w))) .one) = true := by
                  simp [shapeOfHOLExact, shapeEqHOL]
                rw [if_pos hsh_ok]
                let resumed := setVarHOLFinite (ofString "total") (.val (.word tot_w)) { post1 with locals := sd.locals }
                let tailProg : ProgHOL 64 :=
                  .seq
                    (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"), .var .local (ofString "total")]))
                    (.assign .local (ofString "count") (.op .add [.var .local (ofString "count"), .const 1#64]))
                have htail_clk := clockPreserving_of_extStraightLine tailProg rfl resumed
                have htail_safe := evaluate_extStraightLine_no_timeout tailProg rfl resumed
                have htail_nc := evaluate_noTopContinue tailProg rfl resumed
                have htail_meta := PanRunBounded.evaluateHOLFiniteState_metadata resumed tailProg
                have hassign1 : evaluateHOLFiniteState resumed
                    (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"), .var .local (ofString "total")])) =
                    (none, setVarHOLFinite (ofString "off") (.val (.word (off + tot_w))) resumed) := by
                  have hres_off : resumed.locals.lookup (ofString "off") = some (.val (.word off)) := by
                    simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsd_off,
                      show ofString "total" ≠ ofString "off" by decide]
                  have hres_tot : resumed.locals.lookup (ofString "total") = some (.val (.word tot_w)) := by
                    simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                  simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hres_off, hres_tot,
                    wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero, lookupKvarHOLExact,
                    isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
                rcases htr : evaluateHOLFiniteState resumed tailProg with ⟨rt, post2⟩
                rw [htr] at htail_clk htail_safe htail_nc htail_meta
                have hres_clk : resumed.clock = post1.clock := rfl
                dsimp only at htail_clk htail_safe htail_nc htail_meta ⊢
                refine ⟨by omega, by omega, htail_safe, fun hflow => ?_, fun hbrk => ?_⟩
                · rcases hflow with rfl | hcont_eq
                  · have htr_exp := htr
                    dsimp only [tailProg] at htr_exp
                    rw [evaluateHOLFiniteState_seq_line780, hassign1] at htr_exp
                    dsimp only at htr_exp
                    let midOff := setVarHOLFinite (ofString "off") (.val (.word (off + tot_w))) resumed
                    have hpost2_off : post2.locals.lookup (ofString "off") = some (.val (.word (off + tot_w))) := by
                      have hav := evaluate_avoidsLocal_flowing (ofString "off")
                        (.assign .local (ofString "count") (.op .add [.var .local (ofString "count"), .const 1#64]))
                        (by decide) midOff (by rw [htr_exp]; exact Or.inl rfl)
                      rw [htr_exp] at hav
                      refine hav.trans ?_
                      simp [midOff, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                    have hpost2_len : post2.locals.lookup (ofString "len") = some (.val (.word len)) := by
                      have hav := evaluate_avoidsLocal_flowing (ofString "len") tailProg (by decide) resumed
                        (by rw [htr]; exact Or.inl rfl)
                      rw [htr] at hav
                      refine hav.trans ?_
                      simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsd_len,
                        show ofString "total" ≠ ofString "len" by decide]
                    have hrem_nat : (len - off).toNat = len.toNat - off.toNat :=
                      BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hle)
                    have hoff_add : (off + tot_w).toNat = off.toNat + tot_w.toNat := by
                      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
                    refine ⟨len.toNat - (off + tot_w).toNat, by omega, ?_, htail_meta.1.trans hmeta.1⟩
                    refine ⟨off + tot_w, ?_, ?_, by omega, rfl⟩
                    · rw [PanRunBounded.resVarEq_lookup, if_neg (by decide : ofString "off" ≠ ofString "total")]
                      exact hpost2_off
                    · rw [PanRunBounded.resVarEq_lookup, if_neg (by decide : ofString "len" ≠ ofString "total")]
                      exact hpost2_len
                  · exact absurd hcont_eq htail_nc
                · exfalso
                  have htr_exp := htr
                  dsimp only [tailProg] at htr_exp
                  rw [evaluateHOLFiniteState_seq_line780, hassign1] at htr_exp
                  dsimp only at htr_exp
                  rw [evaluateHOLFiniteState_assign] at htr_exp
                  split at htr_exp
                  · simp [hbrk] at htr_exp
                  · split at htr_exp <;> simp [hbrk] at htr_exp
              · exact ⟨by simp [emptyLocalsHOLFinite]; omega, by simp [emptyLocalsHOLFinite]; omega, by simp, by simp, by simp⟩
              · exact ⟨by simp [emptyLocalsHOLFinite]; omega, by simp [emptyLocalsHOLFinite]; omega, by simp, by simp, by simp⟩
            · have hargs_none : evalListHOLFinite sd (h := fun a => Classical.propDecidable (sd.memaddrs a))
                  [.op .add [.var .local (ofString "p"), .var .local (ofString "off")],
                   .op .sub [.var .local (ofString "len"), .var .local (ofString "off")]] = none := by
                simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hp_lk, hsd_off,
                  wordOpHOL, valueIsWord]
              rw [hargs_none]
              dsimp only
              exact ⟨by omega, by omega, by simp, by simp, by simp⟩
            · have hargs_none : evalListHOLFinite sd (h := fun a => Classical.propDecidable (sd.memaddrs a))
                  [.op .add [.var .local (ofString "p"), .var .local (ofString "off")],
                   .op .sub [.var .local (ofString "len"), .var .local (ofString "off")]] = none := by
                simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hp_lk, hsd_off,
                  wordOpHOL, valueIsWord]
              rw [hargs_none]
              dsimp only
              exact ⟨by omega, by omega, by simp, by simp, by simp⟩)
        len.toNat s0 hs0_code ⟨0#64, hs0_off, hlen_lk, by simp, by simp⟩
        (by rw [hs0_clk]; omega)
      have hloop_rb : RunBounded s0 (.while (.cmp .lower (.var .local (ofString "off")) (.var .local (ofString "len"))) loopBody)
          (len.toNat * (itemCost + 1)) :=
        ⟨hranked.1, hranked.2.1, hranked.2.2.1⟩
      refine (RunBounded.seq (state := s0) (a := len.toNat * (itemCost + 1)) (b := 0) hloop_rb
        (by rw [hs0_clk]; omega) ?_).weaken (by omega)
      intro s_end _ hs_end_code _
      exact (ProgBounded.straight _ rfl) s_end (hs_end_code.trans hs0_code) (Nat.zero_le _)
    · unfold RunBounded
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total]
      have hc : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
          (.cmp .lower (.var .local (ofString "off")) (.var .local (ofString "len"))) = none := by
        rw [evalHOLFinite_eq_toExact]; simp [evalHOLExact, hs0_off, hlen_lk]
      rw [hc]; simp
    · unfold RunBounded
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total]
      have hc : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
          (.cmp .lower (.var .local (ofString "off")) (.var .local (ofString "len"))) = none := by
        rw [evalHOLFinite_eq_toExact]; simp [evalHOLExact, hs0_off, hlen_lk]
      rw [hc]; simp

private theorem progBounded_rlp_list_slices_after_alloc : ProgBounded
    (.dec (ofString "i") .one (.const 0#64)
      (.dec (ofString "off") .one (.const 0#64)
        (.seq
          (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "count")))
            (.decCall (ofString "total") .one (ofString "rlp_item_total_unchecked")
              [.op .add [.var .local (ofString "p"), .var .local (ofString "off")]]
              (.seq
                (.store (.op .add [.var .local (ofString "arr"), .panop .mul [.var .local (ofString "i"), .const 16#64]])
                  (.op .add [.var .local (ofString "p"), .var .local (ofString "off")]))
                (.seq
                  (.store (.op .add [.var .local (ofString "arr"), .panop .mul [.var .local (ofString "i"), .const 16#64], .const 8#64])
                    (.var .local (ofString "total")))
                  (.seq
                    (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"), .var .local (ofString "total")]))
                    (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64])))))))
          (.return (.rstruct [.var .local (ofString "arr"), .var .local (ofString "count")])))))
    ((2 ^ 64 - 1) * (((2 ^ 64 + 1) + 1) + 1)) := by
  intro F' state hcode hbudget
  apply RunBounded.decConst
  apply RunBounded.decConst
  set s0 := setVarHOLFinite (ofString "off") (.val (.word 0#64))
    (setVarHOLFinite (ofString "i") (.val (.word 0#64)) state) with hs0_def
  have hs0_code : s0.code = originalRuntimeCode := hcode
  have hs0_i : s0.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
    simp [hs0_def, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "off" ≠ ofString "i" by decide]
  have hs0_clk : s0.clock = state.clock := rfl
  rcases hcnt : s0.locals.lookup (ofString "count") with _ | cntVal
  · unfold RunBounded
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total]
    have hc : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "count"))) = none := by
      rw [evalHOLFinite_eq_toExact]; simp [evalHOLExact, hs0_i, hcnt]
    rw [hc]; simp
  · rcases cntVal with ⟨⟨K'⟩⟩ | _ | _
    · refine (RunBounded.seq (state := s0) (a := (2 ^ 64 - 1) * ((((2 ^ 64 + 1) + 1) + 0) + 1)) (b := 0) ?_
        (by rw [hs0_clk]; omega) ?_).weaken (by omega)
      · exact variableCountedWhile_step_zero_bounded (ofString "i") (ofString "count")
          .lower (Or.inr rfl) (cost := ((2 ^ 64 + 1) + 1) + 0)
          (fun u hu_code w hu_i hu_b =>
            decCall_step_incr u funBounded_rlp_item_total_unchecked (by decide)
              (countedBody_seq_straight _ (by decide) (by decide) (by decide)
                (countedBody_seq_straight _ (by decide) (by decide) (by decide)
                  (countedBody_seq_straight _ (by decide) (by decide) (by decide) CountedBody.incr)))
              hu_code w hu_i hu_b)
          (by decide) s0 hs0_code K' hs0_i hcnt (by rw [hs0_clk]; omega)
      · intro s_end _ hs_end_code _
        exact (ProgBounded.straight _ rfl) s_end (hs_end_code.trans hs0_code) (Nat.zero_le _)
    · unfold RunBounded
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total]
      have hc : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
          (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "count"))) = none := by
        rw [evalHOLFinite_eq_toExact]; simp [evalHOLExact, hs0_i, hcnt]
      rw [hc]; simp
    · unfold RunBounded
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total]
      have hc : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
          (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "count"))) = none := by
        rw [evalHOLFinite_eq_toExact]; simp [evalHOLExact, hs0_i, hcnt]
      rw [hc]; simp

theorem funBounded_rlp_list_to_slices (Kv : Nat)
    (hval : FunBounded (ofString "_rlp_validate_items_body") Kv) :
    FunBounded (ofString "rlp_list_to_slices")
      (((2 ^ 64 - 1) * (((2 ^ 64 + 11 + Kv) + 1) + 1)) + 1 + (1 + 1 + (2 ^ 64 - 1) * (((2 ^ 64 + 1) + 1) + 1))) := by
  have hcnt_fn := funBounded_rlp_list_count Kv hval
  refine funBounded_of_guestAst 115 (by rw [guestAst_len]; decide) Guest.Software.guestFn_rlp_list_to_slices
    (((2 ^ 64 - 1) * (((2 ^ 64 + 11 + Kv) + 1) + 1)) + 1 + (1 + 1 + (2 ^ 64 - 1) * (((2 ^ 64 + 1) + 1) + 1))) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_rlp_list_to_slices,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.decCall hcnt_fn _ _ _
    (ProgBounded.decCall funBounded_alloc _ _ _ progBounded_rlp_list_slices_after_alloc)

theorem funBounded_sha256_state_init : FunBounded (ofString "sha256_state_init") 0 :=
  funBounded_of_guestAst 92 (by rw [guestAst_len]; decide) Guest.Software.guestFn_sha256_state_init 0 rfl
    (ProgBounded.straight _ (by decide))

theorem funBounded_sha256_block : FunBounded (ofString "sha256_block") 0 :=
  funBounded_of_guestAst 93 (by rw [guestAst_len]; decide) Guest.Software.guestFn_sha256_block 0 rfl
    (ProgBounded.straight _ (by decide))

theorem funBounded_sha256_finish : FunBounded (ofString "sha256_finish") 16 := by
  refine funBounded_of_guestAst 94 (by rw [guestAst_len]; decide) Guest.Software.guestFn_sha256_finish 16 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_sha256_finish,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.countedDec (ofString "i") .less (Or.inl rfl) 8 1 0
      (by decide) (by decide) (by decide) (cost := 1 + 0)
      (CountedBody.seq _ (ProgBounded.call funBounded_st_be32 none _) (by decide) (by decide) CountedBody.incr)
      (ProgBounded.straight _ (by decide)))
    (by decide)

theorem funBounded_sha256_pair : FunBounded (ofString "sha256_pair") 0 :=
  funBounded_of_guestAst 96 (by rw [guestAst_len]; decide) Guest.Software.guestFn_sha256_pair 0 rfl
    (ProgBounded.straight _ (by decide))

private theorem progBounded_variableDecWhile (counter limit : MlS) (op : Cmp)
    (hop : op = .less ∨ op = .lower) {body tail : ProgHOL 64} {cost tailCost : Nat}
    (counted : CountedBody counter 1 body cost)
    (preservesLimit : avoidsLocal limit body = true)
    (rest : ProgBounded tail tailCost) :
    ProgBounded (.dec counter .one (.const 0)
      (.seq (.while (.cmp op (.var .local counter) (.var .local limit)) body) tail))
      ((2 ^ 64 - 1) * (cost + 1) + tailCost) := by
  intro F state hcode hbudget
  apply RunBounded.decConst
  set s0 := setVarHOLFinite counter (.val (.word 0#64)) state with hs0_def
  have hs0_code : s0.code = originalRuntimeCode := hcode
  have hs0_i : s0.locals.lookup counter = some (.val (.word 0#64)) := by
    simp [hs0_def, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs0_clk : s0.clock = state.clock := rfl
  rcases hlim : s0.locals.lookup limit with _ | limVal
  · unfold RunBounded
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total]
    have hc : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
        (.cmp op (.var .local counter) (.var .local limit)) = none := by
      rw [evalHOLFinite_eq_toExact]
      by_cases heq : counter = limit
      · subst heq; rw [hs0_i] at hlim; cases hlim
      · simp [evalHOLExact, hs0_i, hlim]
    rw [hc]; simp
  · rcases limVal with ⟨⟨K⟩⟩ | _ | _
    · exact RunBounded.seq (state := s0) (a := (2 ^ 64 - 1) * (cost + 1)) (b := tailCost)
        (variableCountedWhile_zero_bounded counter limit op hop counted preservesLimit
          s0 hs0_code K hs0_i hlim (by rw [hs0_clk]; omega))
        (by rw [hs0_clk]; omega)
        (fun s_end _ hs_end_code hb => rest s_end (hs_end_code.trans hs0_code) hb)
    · unfold RunBounded
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total]
      have hc : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
          (.cmp op (.var .local counter) (.var .local limit)) = none := by
        rw [evalHOLFinite_eq_toExact]
        by_cases heq : counter = limit
        · subst heq; rw [hs0_i] at hlim; cases hlim
        · simp [evalHOLExact, hs0_i, hlim]
      rw [hc]; simp
    · unfold RunBounded
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total]
      have hc : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
          (.cmp op (.var .local counter) (.var .local limit)) = none := by
        rw [evalHOLFinite_eq_toExact]
        by_cases heq : counter = limit
        · subst heq; rw [hs0_i] at hlim; cases hlim
        · simp [evalHOLExact, hs0_i, hlim]
      rw [hc]; simp

private theorem progBounded_variableAssignWhile (counter limit : MlS) (op : Cmp)
    (hop : op = .less ∨ op = .lower) {body tail : ProgHOL 64} {cost tailCost : Nat}
    (counted : CountedBody counter 1 body cost)
    (preservesLimit : avoidsLocal limit body = true)
    (rest : ProgBounded tail tailCost) :
    ProgBounded (.seq (.assign .local counter (.const 0))
      (.seq (.while (.cmp op (.var .local counter) (.var .local limit)) body) tail))
      ((2 ^ 64 - 1) * (cost + 1) + tailCost) := by
  intro F state hcode hbudget
  by_cases hvalid : isValidValueHOLFinite state.locals .local counter (.val (.word 0#64))
  · have hassign : evaluateHOLFiniteState state (.assign .local counter (.const 0)) =
        (none, setVarHOLFinite counter (.val (.word 0#64)) state) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, hvalid, setKvarHOLFinite]
    rw [evaluateHOLFiniteState_seq_line780, hassign]
    dsimp only
    set s0 := setVarHOLFinite counter (.val (.word 0#64)) state with hs0_def
    have hs0_code : s0.code = originalRuntimeCode := hcode
    have hs0_i : s0.locals.lookup counter = some (.val (.word 0#64)) := by
      simp [hs0_def, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hs0_clk : s0.clock = state.clock := rfl
    rcases hlim : s0.locals.lookup limit with _ | limVal
    · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total]
      have hc : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
          (.cmp op (.var .local counter) (.var .local limit)) = none := by
        rw [evalHOLFinite_eq_toExact]
        by_cases heq : counter = limit
        · subst heq; rw [hs0_i] at hlim; cases hlim
        · simp [evalHOLExact, hs0_i, hlim]
      rw [hc]; simp
    · rcases limVal with ⟨⟨K⟩⟩ | _ | _
      · exact RunBounded.seq (state := s0) (a := (2 ^ 64 - 1) * (cost + 1)) (b := tailCost)
          (variableCountedWhile_zero_bounded counter limit op hop counted preservesLimit
            s0 hs0_code K hs0_i hlim (by rw [hs0_clk]; omega))
          (by rw [hs0_clk]; omega)
          (fun s_end _ hs_end_code hb => rest s_end (hs_end_code.trans hs0_code) hb)
      · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total]
        have hc : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
            (.cmp op (.var .local counter) (.var .local limit)) = none := by
          rw [evalHOLFinite_eq_toExact]
          by_cases heq : counter = limit
          · subst heq; rw [hs0_i] at hlim; cases hlim
          · simp [evalHOLExact, hs0_i, hlim]
        rw [hc]; simp
      · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total]
        have hc : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
            (.cmp op (.var .local counter) (.var .local limit)) = none := by
          rw [evalHOLFinite_eq_toExact]
          by_cases heq : counter = limit
          · subst heq; rw [hs0_i] at hlim; cases hlim
          · simp [evalHOLExact, hs0_i, hlim]
        rw [hc]; simp
  · have hassign : evaluateHOLFiniteState state (.assign .local counter (.const 0)) = (some .error, state) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, hvalid]
    rw [evaluateHOLFiniteState_seq_line780, hassign]
    simp

theorem lookup_sha256 :
    originalRuntimeCode.lookup (ofString "sha256") =
      some ([(ofString "p", .one), (ofString "len", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_sha256, .one) :=
  lookup_of_guestAst_getElem 95 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_sha256) rfl

private theorem lookup_sha256_len
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (hlookup_fn : code (ofString "sha256") =
      some ([(ofString "p", .one), (ofString "len", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_sha256, .one))
    {v1 v3 : ValueHOL 64} {K : BitVec 64}
    {foundBody : ProgHOL 64} {locals : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hfound : PanSemStateFiniteExact.lookupCodeHOLFinite code (ofString "sha256") [v1, .val (.word K), v3] =
      some (foundBody, locals, rs)) :
    foundBody = sourceFnBody Guest.Software.guestFn_sha256 ∧
      locals.lookup (ofString "len") = some (.val (.word K)) := by
  have hbody := lookupCodeHOLFinite_installed_body code (ofString "sha256") _
    (sourceFnBody Guest.Software.guestFn_sha256) foundBody .one rs
    [v1, .val (.word K), v3] locals hlookup_fn hfound
  refine ⟨hbody, ?_⟩
  rcases v1 with ⟨⟨w1⟩⟩ | _ | _
  · rcases v3 with ⟨⟨w3⟩⟩ | _ | _
    · rw [pan_three_word_lookup code (ofString "sha256") (ofString "p") (ofString "len") (ofString "out")
        (sourceFnBody Guest.Software.guestFn_sha256) w1 K w3 (by decide) (by decide) (by decide) hlookup_fn] at hfound
      cases hfound
      simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "out" ≠ ofString "len" by decide]
    · unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
      split at hfound
      · cases hfound
      · rename_i _ _ _ raw; simp [lookupCodeHOLExact, hlookup_fn, shapeOfHOLExact, shapeEqHOL] at raw
    · unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
      split at hfound
      · cases hfound
      · rename_i _ _ _ raw; simp [lookupCodeHOLExact, hlookup_fn, shapeOfHOLExact, shapeEqHOL] at raw
  · unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
    split at hfound
    · cases hfound
    · rename_i _ _ _ raw; simp [lookupCodeHOLExact, hlookup_fn, shapeOfHOLExact, shapeEqHOL] at raw
  · unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
    split at hfound
    · cases hfound
    · rename_i _ _ _ raw; simp [lookupCodeHOLExact, hlookup_fn, shapeOfHOLExact, shapeEqHOL] at raw

theorem runBounded_sha256 {F : Type}
    (state : PanSemStateFiniteExact 64 F) (K : BitVec 64)
    (hsmall : K.toNat + 64 < 2 ^ 64)
    (hcode : state.code = originalRuntimeCode)
    (atLen : state.locals.lookup (ofString "len") = some (.val (.word K)))
    (hbudget : K.toNat / 64 * 2 + 63 ≤ state.clock) :
    RunBounded state (sourceFnBody Guest.Software.guestFn_sha256) (K.toNat / 64 * 2 + 63) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_sha256,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  have hinit_avoids : avoidsLocal (ofString "len")
      (.call (some (none, none)) (ofString "sha256_state_init") [.var .global (ofString "sha_st")]) = true := rfl
  refine RunBounded.seq (a := 1) (b := K.toNat / 64 * 2 + 62)
    (ProgBounded.call funBounded_sha256_state_init none _ state hcode (by omega))
    (by omega) ?_
  intro s1 hs1_eq hs1_code hs1_bud
  have hs1_len : s1.locals.lookup (ofString "len") = some (.val (.word K)) := by
    have hfl := evaluate_avoidsLocal_flowing (ofString "len") _ hinit_avoids state
      (by rw [hs1_eq]; exact Or.inl rfl)
    rw [hs1_eq] at hfl
    exact hfl.trans atLen
  apply RunBounded.decConst
  set s2 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) s1 with hs2_def
  have hs2_code : s2.code = originalRuntimeCode := hs1_code.trans hcode
  have hs2_i : s2.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
    simp [hs2_def, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs2_len : s2.locals.lookup (ofString "len") = some (.val (.word K)) := by
    simp [hs2_def, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "i" ≠ ofString "len" by decide, hs1_len]
  have hs2_clk : s2.clock = s1.clock := rfl
  have hloop := notLowerStrideWhile_run (ofString "i") (ofString "len") K 64#64
    (by simpa using hsmall) (by decide) (cost := 1 + 0)
    (CountedBody.seq _
      (ProgBounded.call funBounded_sha256_block none
        [.var .global (ofString "sha_st"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")]])
      (by decide) (by decide) CountedBody.incr)
    (by decide) (by decide)
    (K.toNat / 64) s2 hs2_code 0#64 hs2_i hs2_len (by simp) (by simp) (by rw [hs2_clk]; omega)
  dsimp only at hloop
  refine RunBounded.seq (state := s2) (a := K.toNat / 64 * 2) (b := 62)
    ⟨hloop.1, hloop.2.1, hloop.2.2.1⟩ (by rw [hs2_clk]; omega) ?_
  intro s3 hs3_eq hs3_code hs3_bud
  have hpost := hloop.2.2.2 (by rw [hs3_eq])
  rw [hs3_eq] at hpost
  dsimp only at hpost
  obtain ⟨w', hw'_i, hw'_len, _, hw'_le, hw'_lt, _⟩ := hpost
  have hrem_eval : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
      (.op .sub [.var .local (ofString "len"), .var .local (ofString "i")]) = some (.val (.word (K - w'))) := by
    simp [evalHOLExact, evalListHOLExact, hw'_len, hw'_i, valueIsWord, valueWord, wordOpHOL, wordOp]
  have hrem_lt : (K - w').toNat ≤ 63 := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hw'_le)]
    change K.toNat < w'.toNat + 64 at hw'_lt
    omega
  apply RunBounded.decWord s3 (ofString "rem") _ (K - w') hrem_eval
  set s4 := setVarHOLFinite (ofString "rem") (.val (.word (K - w'))) s3 with hs4_def
  have hs4_code : s4.code = originalRuntimeCode := hs3_code.trans hs2_code
  have hs4_rem : s4.locals.lookup (ofString "rem") = some (.val (.word (K - w'))) := by
    simp [hs4_def, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs4_clk : s4.clock = s3.clock := rfl
  have hmz_avoids : avoidsLocal (ofString "rem")
      (.call (some (none, none)) (ofString "memzero") [.var .global (ofString "sha_pad"), .const 128#64]) = true := rfl
  refine RunBounded.seq (state := s4) (a := 24) (b := 38)
    ((ProgBounded.weaken (progBounded_memzero_const none _ 128#64 (by decide))
      (by decide : (128#64).toNat / 8 + 8 ≤ 24)) s4 hs4_code (by rw [hs4_clk]; omega))
    (by rw [hs4_clk]; omega) ?_
  intro s5 hs5_eq hs5_code hs5_bud
  have hs5_rem : s5.locals.lookup (ofString "rem") = some (.val (.word (K - w'))) := by
    have hfl := evaluate_avoidsLocal_flowing (ofString "rem") _ hmz_avoids s4
      (by rw [hs5_eq]; exact Or.inl rfl)
    rw [hs5_eq] at hfl
    exact hfl.trans hs4_rem
  have hs5_code' : s5.code = originalRuntimeCode := hs5_code.trans hs4_code
  have hmc : RunBounded s5
      (.call (some (none, none)) (ofString "memcpy")
        [.var .global (ofString "sha_pad"),
         .op .add [.var .local (ofString "p"), .var .local (ofString "i")],
         .var .local (ofString "rem")]) 15 := by
    cases hargs : evalListHOLFinite s5 (h := fun a => Classical.propDecidable (s5.memaddrs a))
        [.var .global (ofString "sha_pad"),
         .op .add [.var .local (ofString "p"), .var .local (ofString "i")],
         .var .local (ofString "rem")] with
    | none =>
      unfold RunBounded
      rw [evaluateHOLFiniteState_call, hargs]; simp
    | some vs =>
      have hv3 : evalHOLFinite s5 (h := fun a => Classical.propDecidable (s5.memaddrs a))
          (.var .local (ofString "rem")) = some (.val (.word (K - w'))) := by
        rw [evalHOLFinite_eq_toExact]; simp [evalHOLExact, hs5_rem]
      obtain ⟨v1, v2, rfl⟩ := evalListHOLFinite_three_word3_local s5 _ _ _ (K - w') hargs hv3
      have hcall := RunBounded.call (destination := none) (bodyCost := (K - w').toNat / 8 + 7) hargs (by omega)
        (fun body locals rs hfound => by
          rw [hs5_code'] at hfound
          obtain ⟨rfl, hn⟩ := three_arg_lookup_n_local originalRuntimeCode.lookup
            (ofString "memcpy") (ofString "dst") (ofString "src") (sourceFnBody Guest.Software.guestFn_memcpy)
            (by decide) (by decide) (by decide) lookup_memcpy hfound
          exact runBounded_memcpy (callEntryStateHOLFinite s5 locals) (K - w') (by omega) hs5_code' hn
            (by change (K - w').toNat / 8 + 7 ≤ s5.clock - 1; omega))
      exact hcall.weaken (by omega)
  have htail : ProgBounded
      (.seq (.storeByte (.op .add [.var .global (ofString "sha_pad"), .var .local (ofString "rem")]) (.const 128#64))
        (.dec (ofString "total") .one (.const 64#64)
          (.seq
            (.ite (.cmp .notLower (.var .local (ofString "rem")) (.const 56#64))
              (.assign .local (ofString "total") (.const 128#64)) .skip)
            (.seq
              (.call (some (none, none)) (ofString "st_be64")
                [.op .sub [.op .add [.var .global (ofString "sha_pad"), .var .local (ofString "total")], .const 8#64],
                 .shift .lsl (.var .local (ofString "len")) (.const 3#64)])
              (.seq
                (.call (some (none, none)) (ofString "sha256_block")
                  [.var .global (ofString "sha_st"), .var .global (ofString "sha_pad")])
                (.seq
                  (.ite (.cmp .equal (.var .local (ofString "total")) (.const 128#64))
                    (.call (some (none, none)) (ofString "sha256_block")
                      [.var .global (ofString "sha_st"), .op .add [.var .global (ofString "sha_pad"), .const 64#64]])
                    .skip)
                  (.seq
                    (.call (some (none, none)) (ofString "sha256_finish")
                      [.var .global (ofString "sha_st"), .var .local (ofString "out")])
                    (.return (.const 0#64))))))))) 23 :=
    ProgBounded.weaken
      (ProgBounded.seq (ProgBounded.straight _ rfl)
        (ProgBounded.dec _ _ _
          (ProgBounded.seq (ProgBounded.straight _ rfl)
            (ProgBounded.seq (ProgBounded.call funBounded_st_be64 none _)
              (ProgBounded.seq (ProgBounded.call funBounded_sha256_block none _)
                (ProgBounded.seq
                  (ProgBounded.iteMax _ (ProgBounded.call funBounded_sha256_block none _) (ProgBounded.straight _ rfl))
                  (ProgBounded.seq (ProgBounded.call funBounded_sha256_finish none _)
                    (ProgBounded.straight _ rfl))))))))
      (by decide)
  exact RunBounded.seq (state := s5) (a := 15) (b := 23) hmc hs5_bud
    (fun s6 _ hs6_code hb => htail s6 (hs6_code.trans hs5_code') hb)

theorem progBounded_sha256 (destination : Option (VarKind × MlS)) (p lenExp out : ExpHOL 64)
    (M : Nat) (hsmall : M + 64 < 2 ^ 64)
    (heval : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      ∀ v, evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) lenExp = some v →
        ∃ K : BitVec 64, v = .val (.word K) ∧ K.toNat ≤ M) :
    ProgBounded (.call (some (destination, none)) (ofString "sha256") [p, lenExp, out])
      (M / 64 * 2 + 64) := by
  intro F state hcode hbudget
  cases hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [p, lenExp, out] with
  | none =>
    rw [evaluateHOLFiniteState_call, hargs]; simp
  | some vs =>
    have hex : ∃ v1 v2 v3, vs = [v1, v2, v3] ∧
        evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) lenExp = some v2 := by
      rw [evalListHOLFinite_eq_toExact] at hargs
      rw [evalHOLFinite_eq_toExact]
      rcases h1 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) p with _ | v1
      · simp [evalListHOLExact, h1] at hargs
      · rcases h2 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) lenExp with _ | v2
        · simp [evalListHOLExact, h1, h2] at hargs
        · rcases h3 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) out with _ | v3
          · simp [evalListHOLExact, h1, h2, h3] at hargs
          · simp [evalListHOLExact, h1, h2, h3] at hargs
            exact ⟨v1, v2, v3, hargs.symm, rfl⟩
    obtain ⟨v1, v2, v3, rfl, hv2⟩ := hex
    obtain ⟨K, rfl, hK_le⟩ := heval state v2 hv2
    have hK_div : K.toNat / 64 ≤ M / 64 := Nat.div_le_div_right hK_le
    have hcall := RunBounded.call (destination := destination) (bodyCost := K.toNat / 64 * 2 + 63) hargs (by omega)
      (fun body locals rs hfound => by
        rw [hcode] at hfound
        obtain ⟨rfl, hlen⟩ := lookup_sha256_len originalRuntimeCode.lookup lookup_sha256 hfound
        exact runBounded_sha256 (callEntryStateHOLFinite state locals) K (by omega) hcode hlen
          (by change K.toNat / 64 * 2 + 63 ≤ state.clock - 1; omega))
    exact hcall.weaken (by omega)

theorem progBounded_sha256_const (destination : Option (VarKind × MlS)) (p out : ExpHOL 64)
    (K : BitVec 64) (hsmall : K.toNat + 64 < 2 ^ 64) :
    ProgBounded (.call (some (destination, none)) (ofString "sha256") [p, .const K, out])
      (K.toNat / 64 * 2 + 64) :=
  progBounded_sha256 destination p (.const K) out K.toNat hsmall
    (fun _ _ hv => by
      rw [evalHOLFinite_eq_toExact] at hv
      cases hv
      exact ⟨K, rfl, le_refl _⟩)

theorem funBounded_ssz_fail : FunBounded (ofString "ssz_fail") 0 :=
  funBounded_of_guestAst 196 (by rw [guestAst_len]; decide) Guest.Software.guestFn_ssz_fail 0 rfl
    (ProgBounded.straight _ (by decide))

theorem funBounded_htr_u64_at : FunBounded (ofString "htr_u64_at") 21 := by
  refine funBounded_of_guestAst 195 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htr_u64_at 21 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_htr_u64_at,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.seq (progBounded_memzero_const none _ 32 (by decide))
      (ProgBounded.seq (progBounded_memcpy_const none _ _ 8 (by decide))
        (ProgBounded.straight _ rfl)))
    (by decide)

theorem funBounded_htr_pcontainer (Kmp : Nat)
    (hmp : FunBounded (ofString "merkleize_progressive") Kmp) :
    FunBounded (ofString "htr_pcontainer") (Kmp + 19 + (2 ^ 64 - 1)) := by
  refine funBounded_of_guestAst 191 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htr_pcontainer
    (Kmp + 19 + (2 ^ 64 - 1)) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_htr_pcontainer,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_heap_mark _ _ _
      (ProgBounded.decCall funBounded_alloc _ _ _
        (ProgBounded.seq (ProgBounded.call hmp none _)
          (ProgBounded.dec _ _ _
            (ProgBounded.seq (ProgBounded.weaken (progBounded_memzero_const none _ 32#64 (by decide)) (by decide : (32#64).toNat / 8 + 8 ≤ 12))
              (progBounded_variableDecWhile (ofString "i") (ofString "n") .less (Or.inl rfl)
                (cost := 0 + 0)
                (CountedBody.seq _ (ProgBounded.straight _ rfl) (by decide) (by decide) CountedBody.incr)
                (by decide)
                (ProgBounded.seq (ProgBounded.call funBounded_sha256_pair none _)
                  (ProgBounded.seq (ProgBounded.call funBounded_heap_release none _)
                    (ProgBounded.straight _ rfl)))))))))
    (by omega)

theorem funBounded_ssz_check_offsets :
    FunBounded (ofString "ssz_check_offsets") ((2 ^ 64 - 1) * 3 + 1) := by
  refine funBounded_of_guestAst 201 (by rw [guestAst_len]; decide) Guest.Software.guestFn_ssz_check_offsets
    ((2 ^ 64 - 1) * 3 + 1) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_ssz_check_offsets,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.seq (ProgBounded.straight _ rfl)
      (progBounded_variableDecWhile (ofString "i") (ofString "n") .less (Or.inl rfl)
        (cost := 1 + (1 + 0))
        (CountedBody.dec _ _ _ (by decide)
          (CountedBody.seq _
            (ProgBounded.iteMax _ (ProgBounded.call funBounded_ssz_fail none _) (ProgBounded.straight _ rfl))
            (by decide) (by decide)
            (CountedBody.seq _
              (ProgBounded.iteMax _
                (ProgBounded.iteMax _ (ProgBounded.call funBounded_ssz_fail none _) (ProgBounded.straight _ rfl))
                (ProgBounded.straight _ rfl))
              (by decide) (by decide)
              CountedBody.incr)))
        (by decide)
        (ProgBounded.seq
          (ProgBounded.iteMax _ (ProgBounded.call funBounded_ssz_fail none _) (ProgBounded.straight _ rfl))
          (ProgBounded.straight _ rfl))))
    (by decide)

private theorem progBounded_variableDec2While (counter v2 limit : MlS) (s2 : ShapeHOL) (init2 : ExpHOL 64)
    (hne : v2 ≠ counter) (op : Cmp) (hop : op = .less ∨ op = .lower)
    {body tail : ProgHOL 64} {cost tailCost : Nat}
    (counted : CountedBody counter 1 body cost)
    (preservesLimit : avoidsLocal limit body = true)
    (rest : ProgBounded tail tailCost) :
    ProgBounded (.dec counter .one (.const 0)
      (.dec v2 s2 init2 (.seq (.while (.cmp op (.var .local counter) (.var .local limit)) body) tail)))
      ((2 ^ 64 - 1) * (cost + 1) + tailCost) := by
  intro F state hcode hbudget
  apply RunBounded.decConst
  apply RunBounded.dec
  intro val _
  set s0 := setVarHOLFinite v2 val (setVarHOLFinite counter (.val (.word 0#64)) state) with hs0_def
  have hs0_code : s0.code = originalRuntimeCode := hcode
  have hs0_i : s0.locals.lookup counter = some (.val (.word 0#64)) := by
    simp [hs0_def, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne]
  have hs0_clk : s0.clock = state.clock := rfl
  rcases hlim : s0.locals.lookup limit with _ | limVal
  · unfold RunBounded
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total]
    have hc : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
        (.cmp op (.var .local counter) (.var .local limit)) = none := by
      rw [evalHOLFinite_eq_toExact]
      by_cases heq : counter = limit
      · subst heq; rw [hs0_i] at hlim; cases hlim
      · simp [evalHOLExact, hs0_i, hlim]
    rw [hc]; simp
  · rcases limVal with ⟨⟨K⟩⟩ | _ | _
    · exact RunBounded.seq (state := s0) (a := (2 ^ 64 - 1) * (cost + 1)) (b := tailCost)
        (variableCountedWhile_zero_bounded counter limit op hop counted preservesLimit
          s0 hs0_code K hs0_i hlim (by rw [hs0_clk]; omega))
        (by rw [hs0_clk]; omega)
        (fun s_end _ hs_end_code hb => rest s_end (hs_end_code.trans hs0_code) hb)
    · unfold RunBounded
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total]
      have hc : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
          (.cmp op (.var .local counter) (.var .local limit)) = none := by
        rw [evalHOLFinite_eq_toExact]
        by_cases heq : counter = limit
        · subst heq; rw [hs0_i] at hlim; cases hlim
        · simp [evalHOLExact, hs0_i, hlim]
      rw [hc]; simp
    · unfold RunBounded
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total]
      have hc : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
          (.cmp op (.var .local counter) (.var .local limit)) = none := by
        rw [evalHOLFinite_eq_toExact]
        by_cases heq : counter = limit
        · subst heq; rw [hs0_i] at hlim; cases hlim
        · simp [evalHOLExact, hs0_i, hlim]
      rw [hc]; simp

theorem funBounded_ssz_split_var_list :
    FunBounded (ofString "ssz_split_var_list") ((2 ^ 64 - 1) * 2 + 5) := by
  refine funBounded_of_guestAst 202 (by rw [guestAst_len]; decide) Guest.Software.guestFn_ssz_split_var_list
    ((2 ^ 64 - 1) * 2 + 5) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_ssz_split_var_list,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.seq (ProgBounded.straight _ rfl)
      (ProgBounded.seq
        (ProgBounded.iteMax _ (ProgBounded.call funBounded_ssz_fail none _) (ProgBounded.straight _ rfl))
        (ProgBounded.dec _ _ _
          (ProgBounded.seq
            (ProgBounded.iteMax _ (ProgBounded.call funBounded_ssz_fail none _) (ProgBounded.straight _ rfl))
            (ProgBounded.dec _ _ _
              (ProgBounded.seq
                (ProgBounded.iteMax _ (ProgBounded.call funBounded_ssz_fail none _) (ProgBounded.straight _ rfl))
                (ProgBounded.decCall funBounded_alloc _ _ _
                  (progBounded_variableDec2While (ofString "i") (ofString "prev") (ofString "count")
                    .one (.var .local (ofString "first")) (by decide) .less (Or.inl rfl)
                    (cost := 1 + (0 + (0 + (0 + 0))))
                    (CountedBody.dec _ _ _ (by decide)
                      (CountedBody.seq _
                        (ProgBounded.iteMax _ (ProgBounded.call funBounded_ssz_fail none _) (ProgBounded.straight _ rfl))
                        (by decide) (by decide)
                        (CountedBody.seq _ (ProgBounded.straight _ rfl) (by decide) (by decide)
                          (CountedBody.seq _ (ProgBounded.straight _ rfl) (by decide) (by decide)
                            (CountedBody.seq _ (ProgBounded.straight _ rfl) (by decide) (by decide)
                              CountedBody.incr)))))
                    (by decide)
                    (ProgBounded.straight _ rfl)))))))))
    (by decide)

theorem funBounded_htr_bytes_vector (Kpk Kmk : Nat)
    (hpk : FunBounded (ofString "pack_bytes") Kpk)
    (hmk : FunBounded (ofString "merkleize") Kmk) :
    FunBounded (ofString "htr_bytes_vector") (max 24 (Kpk + Kmk + 4)) := by
  refine funBounded_of_guestAst 193 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htr_bytes_vector
    (max 24 (Kpk + Kmk + 4)) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_htr_bytes_vector,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  intro F state hcode hbudget
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
  cases hcond : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      (.cmp .notLower (.const 32) (.var .local (ofString "n"))) with
  | none => simp
  | some cv =>
    rcases cv with ⟨⟨cw⟩⟩ | _ | _
    · by_cases hzero : cw = 0
      · simp only [hzero, if_true]
        rw [evaluateHOLFiniteState_skip]
        dsimp only
        have helse : ProgBounded
            (.decCall (ofString "mark") .one (ofString "heap_mark") []
              (.decCall (ofString "pk") (.comb [.one, .one]) (ofString "pack_bytes")
                [.var .local (ofString "p"), .var .local (ofString "n")]
                (.seq
                  (.call (some (none, none)) (ofString "merkleize")
                    [.rfield 0 (.var .local (ofString "pk")), .rfield 1 (.var .local (ofString "pk")),
                     .rfield 1 (.var .local (ofString "pk")), .var .local (ofString "out")])
                  (.seq (.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")])
                    (.return (.const 0))))))
            (Kpk + Kmk + 4) := by
          refine ProgBounded.weaken ?_ (by omega)
          exact ProgBounded.decCall funBounded_heap_mark _ _ _
            (ProgBounded.decCall hpk _ _ _
              (ProgBounded.seq (ProgBounded.call hmk none _)
                (ProgBounded.seq (ProgBounded.call funBounded_heap_release none _)
                  (ProgBounded.straight _ rfl))))
        exact (helse state hcode (by omega)).weaken (by omega)
      · simp only [hzero, if_false]
        have hn_bound : ∃ K : BitVec 64, state.locals.lookup (ofString "n") = some (.val (.word K)) ∧ K.toNat ≤ 32 := by
          rw [evalHOLFinite_eq_toExact] at hcond
          rcases hn : state.locals.lookup (ofString "n") with _ | nv
          · simp [evalHOLExact, hn] at hcond
          · rcases nv with ⟨⟨K⟩⟩ | _ | _
            · simp [evalHOLExact, hn, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def] at hcond
              by_cases hgt : 32 < K.toNat
              · simp [hgt] at hcond
                exact absurd hcond.symm hzero
              · exact ⟨K, rfl, by omega⟩
            · simp [evalHOLExact, hn] at hcond
            · simp [evalHOLExact, hn] at hcond
        obtain ⟨K, hn_eq, hK_le⟩ := hn_bound
        have hmz_avoids : avoidsLocal (ofString "n")
            (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "out"), .const 32]) = true := rfl
        have hyes : RunBounded state
            (.seq (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "out"), .const 32])
              (.seq (.call (some (none, none)) (ofString "memcpy")
                  [.var .local (ofString "out"), .var .local (ofString "p"), .var .local (ofString "n")])
                (.return (.const 0)))) 24 := by
          refine RunBounded.seq (a := 12) (b := 12)
            (progBounded_memzero_const none _ 32 (by decide) state hcode (by omega))
            (by omega) ?_
          intro s1 hs1_eq hs1_code hs1_bud
          have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word K)) := by
            have hfl := evaluate_avoidsLocal_flowing (ofString "n") _ hmz_avoids state
              (by rw [hs1_eq]; exact Or.inl rfl)
            rw [hs1_eq] at hfl
            exact hfl.trans hn_eq
          have hs1_code' : s1.code = originalRuntimeCode := hs1_code.trans hcode
          have hmc : RunBounded s1
              (.call (some (none, none)) (ofString "memcpy")
                [.var .local (ofString "out"), .var .local (ofString "p"), .var .local (ofString "n")]) 12 := by
            cases hargs : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
                [.var .local (ofString "out"), .var .local (ofString "p"), .var .local (ofString "n")] with
            | none =>
              unfold RunBounded; rw [evaluateHOLFiniteState_call, hargs]; simp
            | some vs =>
              have hv3 : evalHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
                  (.var .local (ofString "n")) = some (.val (.word K)) := by
                rw [evalHOLFinite_eq_toExact]; simp [evalHOLExact, hs1_n]
              obtain ⟨v1, v2, rfl⟩ := evalListHOLFinite_three_word3_local s1 _ _ _ K hargs hv3
              have hcall := RunBounded.call (destination := none) (bodyCost := K.toNat / 8 + 7) hargs (by omega)
                (fun body locals rs hfound => by
                  rw [hs1_code'] at hfound
                  obtain ⟨rfl, hn⟩ := three_arg_lookup_n_local originalRuntimeCode.lookup
                    (ofString "memcpy") (ofString "dst") (ofString "src") (sourceFnBody Guest.Software.guestFn_memcpy)
                    (by decide) (by decide) (by decide) lookup_memcpy hfound
                  exact runBounded_memcpy (callEntryStateHOLFinite s1 locals) K (by omega) hs1_code' hn
                    (by change K.toNat / 8 + 7 ≤ s1.clock - 1; omega))
              exact hcall.weaken (by omega)
          exact RunBounded.seq (state := s1) (a := 12) (b := 0) hmc hs1_bud
            (fun s2 _ hs2_code hb => (ProgBounded.straight _ rfl) s2 (hs2_code.trans hs1_code') hb)
        have hm : mustTerminate
            (.seq (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "out"), .const 32])
              (.seq (.call (some (none, none)) (ofString "memcpy")
                  [.var .local (ofString "out"), .var .local (ofString "p"), .var .local (ofString "n")])
                (.return (.const 0)))) = true := rfl
        have hnn := evaluate_mustTerminate _ hm state
        rcases hr : evaluateHOLFiniteState state _ with ⟨res, post⟩
        rw [hr] at hyes
        cases res with
        | none => exact absurd (congrArg Prod.fst hr) hnn
        | some _ =>
          dsimp only at hyes ⊢
          exact ⟨by omega, hyes.2.1, hyes.2.2⟩
    · simp
    · simp

theorem funBounded_htr_deposit (Kpk Kmk : Nat)
    (hpk : FunBounded (ofString "pack_bytes") Kpk)
    (hmk : FunBounded (ofString "merkleize") Kmk) :
    FunBounded (ofString "htr_deposit") (2 * max 24 (Kpk + Kmk + 4) + Kmk + 63) := by
  have hbv := funBounded_htr_bytes_vector Kpk Kmk hpk hmk
  refine funBounded_of_guestAst 211 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htr_deposit
    (2 * max 24 (Kpk + Kmk + 4) + Kmk + 63) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_htr_deposit,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_heap_mark _ _ _
      (ProgBounded.decCall funBounded_alloc _ _ _
        (ProgBounded.seq (ProgBounded.call hbv none _)
          (ProgBounded.seq (ProgBounded.weaken (progBounded_memcpy_const none _ _ 32#64 (by decide)) (by decide : (32#64).toNat / 8 + 8 ≤ 12))
            (ProgBounded.seq (ProgBounded.call funBounded_htr_u64_at none _)
              (ProgBounded.seq (ProgBounded.call hbv none _)
                (ProgBounded.seq (ProgBounded.call funBounded_htr_u64_at none _)
                  (ProgBounded.seq (ProgBounded.call hmk none _)
                    (ProgBounded.seq (ProgBounded.call funBounded_heap_release none _)
                      (ProgBounded.straight _ rfl))))))))))
    (by omega)

theorem funBounded_htr_wdreq (Kpk Kmk : Nat)
    (hpk : FunBounded (ofString "pack_bytes") Kpk)
    (hmk : FunBounded (ofString "merkleize") Kmk) :
    FunBounded (ofString "htr_wdreq") (2 * max 24 (Kpk + Kmk + 4) + Kmk + 28) := by
  have hbv := funBounded_htr_bytes_vector Kpk Kmk hpk hmk
  refine funBounded_of_guestAst 212 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htr_wdreq
    (2 * max 24 (Kpk + Kmk + 4) + Kmk + 28) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_htr_wdreq,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_heap_mark _ _ _
      (ProgBounded.decCall funBounded_alloc _ _ _
        (ProgBounded.seq (ProgBounded.call hbv none _)
          (ProgBounded.seq (ProgBounded.call hbv none _)
            (ProgBounded.seq (ProgBounded.call funBounded_htr_u64_at none _)
              (ProgBounded.seq (ProgBounded.call hmk none _)
                (ProgBounded.seq (ProgBounded.call funBounded_heap_release none _)
                  (ProgBounded.straight _ rfl))))))))
    (by omega)

theorem funBounded_htr_cons (Kpk Kmk : Nat)
    (hpk : FunBounded (ofString "pack_bytes") Kpk)
    (hmk : FunBounded (ofString "merkleize") Kmk) :
    FunBounded (ofString "htr_cons") (3 * max 24 (Kpk + Kmk + 4) + Kmk + 7) := by
  have hbv := funBounded_htr_bytes_vector Kpk Kmk hpk hmk
  refine funBounded_of_guestAst 213 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htr_cons
    (3 * max 24 (Kpk + Kmk + 4) + Kmk + 7) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_htr_cons,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_heap_mark _ _ _
      (ProgBounded.decCall funBounded_alloc _ _ _
        (ProgBounded.seq (ProgBounded.call hbv none _)
          (ProgBounded.seq (ProgBounded.call hbv none _)
            (ProgBounded.seq (ProgBounded.call hbv none _)
              (ProgBounded.seq (ProgBounded.call hmk none _)
                (ProgBounded.seq (ProgBounded.call funBounded_heap_release none _)
                  (ProgBounded.straight _ rfl))))))))
    (by omega)

theorem funBounded_htr_bdep (Kpk Kmk : Nat)
    (hpk : FunBounded (ofString "pack_bytes") Kpk)
    (hmk : FunBounded (ofString "merkleize") Kmk) :
    FunBounded (ofString "htr_bdep") (2 * max 24 (Kpk + Kmk + 4) + Kmk + 41) := by
  have hbv := funBounded_htr_bytes_vector Kpk Kmk hpk hmk
  refine funBounded_of_guestAst 214 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htr_bdep
    (2 * max 24 (Kpk + Kmk + 4) + Kmk + 41) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_htr_bdep,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_heap_mark _ _ _
      (ProgBounded.decCall funBounded_alloc _ _ _
        (ProgBounded.seq (ProgBounded.call hbv none _)
          (ProgBounded.seq (ProgBounded.weaken (progBounded_memcpy_const none _ _ 32#64 (by decide)) (by decide : (32#64).toNat / 8 + 8 ≤ 12))
            (ProgBounded.seq (ProgBounded.call funBounded_htr_u64_at none _)
              (ProgBounded.seq (ProgBounded.call hbv none _)
                (ProgBounded.seq (ProgBounded.call hmk none _)
                  (ProgBounded.seq (ProgBounded.call funBounded_heap_release none _)
                    (ProgBounded.straight _ rfl)))))))))
    (by omega)

theorem funBounded_htr_bexit (Kpk Kmk : Nat)
    (hpk : FunBounded (ofString "pack_bytes") Kpk)
    (hmk : FunBounded (ofString "merkleize") Kmk) :
    FunBounded (ofString "htr_bexit") (2 * max 24 (Kpk + Kmk + 4) + Kmk + 6) := by
  have hbv := funBounded_htr_bytes_vector Kpk Kmk hpk hmk
  refine funBounded_of_guestAst 215 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htr_bexit
    (2 * max 24 (Kpk + Kmk + 4) + Kmk + 6) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_htr_bexit,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_heap_mark _ _ _
      (ProgBounded.decCall funBounded_alloc _ _ _
        (ProgBounded.seq (ProgBounded.call hbv none _)
          (ProgBounded.seq (ProgBounded.call hbv none _)
            (ProgBounded.seq (ProgBounded.call hmk none _)
              (ProgBounded.seq (ProgBounded.call funBounded_heap_release none _)
                (ProgBounded.straight _ rfl)))))))
    (by omega)

theorem funBounded_htr_request_list (Kpk Kmk Kpl : Nat)
    (hpk : FunBounded (ofString "pack_bytes") Kpk)
    (hmk : FunBounded (ofString "merkleize") Kmk)
    (hpl : FunBounded (ofString "htr_plist_chunks") Kpl) :
    FunBounded (ofString "htr_request_list")
      ((2 ^ 64 - 1) * (11 * max 24 (Kpk + Kmk + 4) + 5 * Kmk + 151) + Kpl + 5) := by
  have hd := funBounded_htr_deposit Kpk Kmk hpk hmk
  have hw := funBounded_htr_wdreq Kpk Kmk hpk hmk
  have hc := funBounded_htr_cons Kpk Kmk hpk hmk
  have hbd := funBounded_htr_bdep Kpk Kmk hpk hmk
  have hbe := funBounded_htr_bexit Kpk Kmk hpk hmk
  refine funBounded_of_guestAst 216 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htr_request_list
    ((2 ^ 64 - 1) * (11 * max 24 (Kpk + Kmk + 4) + 5 * Kmk + 151) + Kpl + 5) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_htr_request_list,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_heap_mark _ _ _
      (ProgBounded.decCall funBounded_alloc _ _ _
        (progBounded_variableDecWhile (ofString "i") (ofString "n") .less (Or.inl rfl)
          (CountedBody.seq _
            (ProgBounded.iteMax _ (ProgBounded.call hd none _) (ProgBounded.straight _ rfl))
            (by decide) (by decide)
            (CountedBody.seq _
              (ProgBounded.iteMax _ (ProgBounded.call hw none _) (ProgBounded.straight _ rfl))
              (by decide) (by decide)
              (CountedBody.seq _
                (ProgBounded.iteMax _ (ProgBounded.call hc none _) (ProgBounded.straight _ rfl))
                (by decide) (by decide)
                (CountedBody.seq _
                  (ProgBounded.iteMax _ (ProgBounded.call hbd none _) (ProgBounded.straight _ rfl))
                  (by decide) (by decide)
                  (CountedBody.seq _
                    (ProgBounded.iteMax _ (ProgBounded.call hbe none _) (ProgBounded.straight _ rfl))
                    (by decide) (by decide)
                    CountedBody.incr)))))
          (by decide)
          (ProgBounded.seq (ProgBounded.call hpl none _)
            (ProgBounded.seq (ProgBounded.call funBounded_heap_release none _)
              (ProgBounded.straight _ rfl))))))
    (by
      have hsub :
          max (2 * max 24 (Kpk + Kmk + 4) + Kmk + 63 + 1) 0 +
          (max (2 * max 24 (Kpk + Kmk + 4) + Kmk + 28 + 1) 0 +
          (max (3 * max 24 (Kpk + Kmk + 4) + Kmk + 7 + 1) 0 +
          (max (2 * max 24 (Kpk + Kmk + 4) + Kmk + 41 + 1) 0 +
          (max (2 * max 24 (Kpk + Kmk + 4) + Kmk + 6 + 1) 0 + 0)))) + 1 =
          11 * max 24 (Kpk + Kmk + 4) + 5 * Kmk + 151 := by omega
      rw [hsub]; omega)

theorem funBounded_mix_in_length : FunBounded (ofString "mix_in_length") 16 := by
  refine funBounded_of_guestAst 188 (by rw [guestAst_len]; decide) Guest.Software.guestFn_mix_in_length 16 rfl ?_
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

theorem funBounded_htr_bytes_list (Kpk Kmk : Nat)
    (hpk : FunBounded (ofString "pack_bytes") Kpk)
    (hmk : FunBounded (ofString "merkleize") Kmk) :
    FunBounded (ofString "htr_bytes_list") (Kpk + Kmk + 22) := by
  refine funBounded_of_guestAst 194 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htr_bytes_list
    (Kpk + Kmk + 22) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_htr_bytes_list,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_heap_mark _ _ _
      (ProgBounded.decCall hpk _ _ _
        (ProgBounded.seq (ProgBounded.call hmk none _)
          (ProgBounded.seq (ProgBounded.call funBounded_heap_release none _)
            (ProgBounded.seq (ProgBounded.call funBounded_mix_in_length none _)
              (ProgBounded.straight _ rfl))))))
    (by omega)

theorem funBounded_htr_pbytes (Kpk Kpl : Nat)
    (hpk : FunBounded (ofString "pack_bytes") Kpk)
    (hpl : FunBounded (ofString "htr_plist_chunks") Kpl) :
    FunBounded (ofString "htr_pbytes") (Kpk + Kpl + 4) := by
  refine funBounded_of_guestAst 190 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htr_pbytes
    (Kpk + Kpl + 4) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_htr_pbytes,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_heap_mark _ _ _
      (ProgBounded.decCall hpk _ _ _
        (ProgBounded.seq (ProgBounded.call hpl none _)
          (ProgBounded.seq (ProgBounded.call funBounded_heap_release none _)
            (ProgBounded.straight _ rfl)))))
    (by omega)

theorem funBounded_htr_withdrawal (Kpk Kmk : Nat)
    (hpk : FunBounded (ofString "pack_bytes") Kpk)
    (hmk : FunBounded (ofString "merkleize") Kmk) :
    FunBounded (ofString "htr_withdrawal") (max 24 (Kpk + Kmk + 4) + Kmk + 71) := by
  have hbv := funBounded_htr_bytes_vector Kpk Kmk hpk hmk
  refine funBounded_of_guestAst 208 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htr_withdrawal
    (max 24 (Kpk + Kmk + 4) + Kmk + 71) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_htr_withdrawal,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_heap_mark _ _ _
      (ProgBounded.decCall funBounded_alloc _ _ _
        (ProgBounded.seq (ProgBounded.call funBounded_htr_u64_at none _)
          (ProgBounded.seq (ProgBounded.call funBounded_htr_u64_at none _)
            (ProgBounded.seq (ProgBounded.call hbv none _)
              (ProgBounded.seq (ProgBounded.call funBounded_htr_u64_at none _)
                (ProgBounded.seq (ProgBounded.call hmk none _)
                  (ProgBounded.seq (ProgBounded.call funBounded_heap_release none _)
                    (ProgBounded.straight _ rfl)))))))))
    (by omega)

theorem funBounded_htr_payload (Kpk Kmk Kpl Kmp : Nat)
    (hpk : FunBounded (ofString "pack_bytes") Kpk)
    (hmk : FunBounded (ofString "merkleize") Kmk)
    (hpl : FunBounded (ofString "htr_plist_chunks") Kpl)
    (hmp : FunBounded (ofString "merkleize_progressive") Kmp) :
    FunBounded (ofString "htr_payload")
      (3 * max 24 (Kpk + Kmk + 4) + Kpk + 2 * Kmk + 4 * Kpl + Kmp + 294 + (2 ^ 64 - 1) +
        (2 ^ 64 - 1) * (Kpk + Kpl + 6) +
        (2 ^ 64 - 1) * (max 24 (Kpk + Kmk + 4) + Kmk + 73)) := by
  have hbv := funBounded_htr_bytes_vector Kpk Kmk hpk hmk
  have hbl := funBounded_htr_bytes_list Kpk Kmk hpk hmk
  have hpb := funBounded_htr_pbytes Kpk Kpl hpk hpl
  have hwd := funBounded_htr_withdrawal Kpk Kmk hpk hmk
  have hpc := funBounded_htr_pcontainer Kmp hmp
  have hmc32 : ∀ dst src, ProgBounded (.call (some (none, none)) (ofString "memcpy") [dst, src, .const 32]) 12 :=
    fun dst src => ProgBounded.weaken (progBounded_memcpy_const none dst src 32#64 (by decide)) (by decide : (32#64).toNat / 8 + 8 ≤ 12)
  refine funBounded_of_guestAst 210 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htr_payload
    (3 * max 24 (Kpk + Kmk + 4) + Kpk + 2 * Kmk + 4 * Kpl + Kmp + 294 + (2 ^ 64 - 1) +
      (2 ^ 64 - 1) * (Kpk + Kpl + 6) +
      (2 ^ 64 - 1) * (max 24 (Kpk + Kmk + 4) + Kmk + 73)) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_htr_payload,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.dec _ _ _
      (ProgBounded.decCall funBounded_heap_mark _ _ _
        (ProgBounded.decCall funBounded_alloc _ _ _
          (ProgBounded.seq (hmc32 _ _)
            (ProgBounded.seq (ProgBounded.call hbv none _)
              (ProgBounded.seq (hmc32 _ _)
                (ProgBounded.seq (hmc32 _ _)
                  (ProgBounded.seq (ProgBounded.call hbv none _)
                    (ProgBounded.seq (hmc32 _ _)
                      (ProgBounded.seq (ProgBounded.call funBounded_htr_u64_at none _)
                        (ProgBounded.seq (ProgBounded.call funBounded_htr_u64_at none _)
                          (ProgBounded.seq (ProgBounded.call funBounded_htr_u64_at none _)
                            (ProgBounded.seq (ProgBounded.call funBounded_htr_u64_at none _)
                              (ProgBounded.seq (ProgBounded.call hbl none _)
                                (ProgBounded.seq (hmc32 _ _)
                                  (ProgBounded.seq (hmc32 _ _)
                                    (ProgBounded.dec _ _ _
                                      (ProgBounded.dec _ _ _
                                        (ProgBounded.decCall funBounded_heap_mark _ _ _
                                          (ProgBounded.decCall funBounded_alloc _ _ _
                                            (progBounded_variableDecWhile (ofString "i") (ofString "ntx") .less (Or.inl rfl)
                                              (CountedBody.seq _ (ProgBounded.call hpb none _) (by decide) (by decide) CountedBody.incr)
                                              (by decide)
                                              (ProgBounded.seq (ProgBounded.call hpl none _)
                                                (ProgBounded.seq (ProgBounded.call funBounded_heap_release none _)
                                                  (ProgBounded.dec _ _ _
                                                    (ProgBounded.dec _ _ _
                                                      (ProgBounded.seq (ProgBounded.call funBounded_alloc (some (.local, ofString "roots")) _)
                                                        (progBounded_variableAssignWhile (ofString "i") (ofString "nwd") .less (Or.inl rfl)
                                                          (CountedBody.seq _ (ProgBounded.call hwd none _) (by decide) (by decide) CountedBody.incr)
                                                          (by decide)
                                                          (ProgBounded.seq (ProgBounded.call hpl none _)
                                                            (ProgBounded.seq (ProgBounded.call funBounded_heap_release none _)
                                                              (ProgBounded.seq (ProgBounded.call funBounded_htr_u64_at none _)
                                                                (ProgBounded.seq (ProgBounded.call funBounded_htr_u64_at none _)
                                                                  (ProgBounded.seq (ProgBounded.call hpb none _)
                                                                    (ProgBounded.seq (ProgBounded.call funBounded_htr_u64_at none _)
                                                                      (ProgBounded.seq (ProgBounded.call hpc none _)
                                                                        (ProgBounded.seq (ProgBounded.call funBounded_heap_release none _)
                                                                          (ProgBounded.straight _ rfl))))))))))))))))))))))))))))))))))))
    (by
      have h1 : (Kpk + Kpl + 4 + 1 + 0 + 1) = Kpk + Kpl + 6 := by omega
      have h2 : (max 24 (Kpk + Kmk + 4) + Kmk + 71 + 1 + 0 + 1) = max 24 (Kpk + Kmk + 4) + Kmk + 73 := by omega
      rw [h1, h2]; omega)

theorem funBounded_mpt_fail : FunBounded (ofString "mpt_fail") 0 :=
  funBounded_of_guestAst 246 (by rw [guestAst_len]; decide) Guest.Software.guestFn_mpt_fail 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_node_new_leaf : FunBounded (ofString "node_new_leaf") 2 := by
  refine funBounded_of_guestAst 256 (by rw [guestAst_len]; decide) Guest.Software.guestFn_node_new_leaf 2 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_node_new_leaf,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_alloc _ _ _ (ProgBounded.straight _ rfl))
    (by decide)

theorem funBounded_node_new_ext : FunBounded (ofString "node_new_ext") 2 := by
  refine funBounded_of_guestAst 257 (by rw [guestAst_len]; decide) Guest.Software.guestFn_node_new_ext 2 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_node_new_ext,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_alloc _ _ _ (ProgBounded.straight _ rfl))
    (by decide)

private theorem lookup_key_to_nibbles :
    originalRuntimeCode.lookup (ofString "key_to_nibbles") =
      some ([(ofString "key", .one), (ofString "n", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_key_to_nibbles, .one) :=
  lookup_of_guestAst_getElem 248 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_key_to_nibbles) rfl

private theorem lookup_key_to_nibbles_n
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (hlookup_fn : code (ofString "key_to_nibbles") =
      some ([(ofString "key", .one), (ofString "n", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_key_to_nibbles, .one))
    {v1 v3 : ValueHOL 64} {K : BitVec 64}
    {foundBody : ProgHOL 64} {locals : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hfound : PanSemStateFiniteExact.lookupCodeHOLFinite code (ofString "key_to_nibbles") [v1, .val (.word K), v3] =
      some (foundBody, locals, rs)) :
    foundBody = sourceFnBody Guest.Software.guestFn_key_to_nibbles ∧
      locals.lookup (ofString "n") = some (.val (.word K)) := by
  have hbody := lookupCodeHOLFinite_installed_body code (ofString "key_to_nibbles") _
    (sourceFnBody Guest.Software.guestFn_key_to_nibbles) foundBody .one rs
    [v1, .val (.word K), v3] locals hlookup_fn hfound
  refine ⟨hbody, ?_⟩
  rcases v1 with ⟨⟨w1⟩⟩ | _ | _
  · rcases v3 with ⟨⟨w3⟩⟩ | _ | _
    · rw [pan_three_word_lookup code (ofString "key_to_nibbles") (ofString "key") (ofString "n") (ofString "out")
        (sourceFnBody Guest.Software.guestFn_key_to_nibbles) w1 K w3 (by decide) (by decide) (by decide) hlookup_fn] at hfound
      cases hfound
      simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "out" ≠ ofString "n" by decide]
    · unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
      split at hfound
      · cases hfound
      · rename_i _ _ _ raw
        simp [lookupCodeHOLExact, hlookup_fn, shapeOfHOLExact, shapeEqHOL] at raw
    · unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
      split at hfound
      · cases hfound
      · rename_i _ _ _ raw
        simp [lookupCodeHOLExact, hlookup_fn, shapeOfHOLExact, shapeEqHOL] at raw
  · unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
    split at hfound
    · cases hfound
    · rename_i _ _ _ raw
      simp [lookupCodeHOLExact, hlookup_fn, shapeOfHOLExact, shapeEqHOL] at raw
  · unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
    split at hfound
    · cases hfound
    · rename_i _ _ _ raw
      simp [lookupCodeHOLExact, hlookup_fn, shapeOfHOLExact, shapeEqHOL] at raw

theorem runBounded_key_to_nibbles {F : Type}
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
  set s0 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) state with hs0_def
  have hs0_code : s0.code = originalRuntimeCode := hcode
  have hs0_i : s0.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
    simp [hs0_def, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs0_n : s0.locals.lookup (ofString "n") = some (.val (.word K)) := by
    simp [hs0_def, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "i" ≠ ofString "n" by decide, atN]
  have hs0_clk : s0.clock = state.clock := rfl
  have hb4 : CountedBody (ofString "i") 4#64
      (.dec (ofString "b0") .one (.loadByte (.op .add [.var .local (ofString "key"), .var .local (ofString "i")]))
        (.seq
          (.storeByte (.op .add [.var .local (ofString "out"), .panop .mul [.const 2#64, .var .local (ofString "i")]])
            (.shift .lsr (.var .local (ofString "b0")) (.const 4#64)))
          (.seq
            (.storeByte (.op .add [.var .local (ofString "out"), .panop .mul [.const 2#64, .var .local (ofString "i")], .const 1#64])
              (.op .and [.var .local (ofString "b0"), .const 15#64]))
            (.dec (ofString "b1") .one (.loadByte (.op .add [.var .local (ofString "key"), .var .local (ofString "i"), .const 1#64]))
              (.seq
                (.storeByte (.op .add [.var .local (ofString "out"), .panop .mul [.const 2#64, .var .local (ofString "i")], .const 2#64])
                  (.shift .lsr (.var .local (ofString "b1")) (.const 4#64)))
                (.seq
                  (.storeByte (.op .add [.var .local (ofString "out"), .panop .mul [.const 2#64, .var .local (ofString "i")], .const 3#64])
                    (.op .and [.var .local (ofString "b1"), .const 15#64]))
                  (.dec (ofString "b2") .one (.loadByte (.op .add [.var .local (ofString "key"), .var .local (ofString "i"), .const 2#64]))
                    (.seq
                      (.storeByte (.op .add [.var .local (ofString "out"), .panop .mul [.const 2#64, .var .local (ofString "i")], .const 4#64])
                        (.shift .lsr (.var .local (ofString "b2")) (.const 4#64)))
                      (.seq
                        (.storeByte (.op .add [.var .local (ofString "out"), .panop .mul [.const 2#64, .var .local (ofString "i")], .const 5#64])
                          (.op .and [.var .local (ofString "b2"), .const 15#64]))
                        (.dec (ofString "b3") .one (.loadByte (.op .add [.var .local (ofString "key"), .var .local (ofString "i"), .const 3#64]))
                          (.seq
                            (.storeByte (.op .add [.var .local (ofString "out"), .panop .mul [.const 2#64, .var .local (ofString "i")], .const 6#64])
                              (.shift .lsr (.var .local (ofString "b3")) (.const 4#64)))
                            (.seq
                              (.storeByte (.op .add [.var .local (ofString "out"), .panop .mul [.const 2#64, .var .local (ofString "i")], .const 7#64])
                                (.op .and [.var .local (ofString "b3"), .const 15#64]))
                              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 4#64])))))))))))))) 0 :=
    CountedBody.dec _ _ _ (by decide)
      (countedBody_seq_straight _ (by decide) (by decide) (by decide)
        (countedBody_seq_straight _ (by decide) (by decide) (by decide)
          (CountedBody.dec _ _ _ (by decide)
            (countedBody_seq_straight _ (by decide) (by decide) (by decide)
              (countedBody_seq_straight _ (by decide) (by decide) (by decide)
                (CountedBody.dec _ _ _ (by decide)
                  (countedBody_seq_straight _ (by decide) (by decide) (by decide)
                    (countedBody_seq_straight _ (by decide) (by decide) (by decide)
                      (CountedBody.dec _ _ _ (by decide)
                        (countedBody_seq_straight _ (by decide) (by decide) (by decide)
                          (countedBody_seq_straight _ (by decide) (by decide) (by decide)
                            CountedBody.incr)))))))))))
  have h4 := notLowerStrideWhile_run (ofString "i") (ofString "n") K 4#64
    (by simpa using hsmall) (by decide) hb4 (by decide) (by decide)
    (K.toNat / 4) s0 hs0_code 0#64 hs0_i hs0_n (by simp) (by simp) (by rw [hs0_clk]; omega)
  dsimp only at h4
  refine RunBounded.seq (state := s0) (a := K.toNat / 4) (b := 3)
    ⟨by simpa using h4.1, h4.2.1, h4.2.2.1⟩ (by rw [hs0_clk]; omega) ?_
  intro s1 hs1_eq hs1_code hs1_bud
  have hpost := h4.2.2.2 (by rw [hs1_eq])
  rw [hs1_eq] at hpost
  dsimp only at hpost
  obtain ⟨w', hw'_i, hw'_n, _, hw'_le, hw'_rem, _⟩ := hpost
  have hrem3 : K.toNat - w'.toNat ≤ 3 := by
    change K.toNat < w'.toNat + 4 at hw'_rem
    omega
  have hb1 : CountedBody (ofString "i") 1#64
      (.dec (ofString "b") .one (.loadByte (.op .add [.var .local (ofString "key"), .var .local (ofString "i")]))
        (.seq
          (.storeByte (.op .add [.var .local (ofString "out"), .panop .mul [.const 2#64, .var .local (ofString "i")]])
            (.shift .lsr (.var .local (ofString "b")) (.const 4#64)))
          (.seq
            (.storeByte (.op .add [.var .local (ofString "out"), .panop .mul [.const 2#64, .var .local (ofString "i")], .const 1#64])
              (.op .and [.var .local (ofString "b"), .const 15#64]))
            (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64]))))) 0 :=
    CountedBody.dec _ _ _ (by decide)
      (countedBody_seq_straight _ (by decide) (by decide) (by decide)
        (countedBody_seq_straight _ (by decide) (by decide) (by decide)
          CountedBody.incr))
  have hs1_code' : s1.code = originalRuntimeCode := hs1_code.trans hs0_code
  have h1 := variableCountedWhile_run (ofString "i") (ofString "n") .lower (Or.inr rfl) K
    (fun h => by cases h) hb1 (by decide) (K.toNat - w'.toNat) s1 hs1_code'
    w' hw'_i hw'_n hw'_le rfl (by simp only [Nat.zero_add, Nat.mul_one]; omega)
  dsimp only at h1
  exact RunBounded.seq (state := s1) (a := 3) (b := 0)
    ⟨by simp only [Nat.zero_add, Nat.mul_one] at h1; omega, h1.2.1, h1.2.2⟩
    hs1_bud
    (fun s2 _ hs2_code hb => (ProgBounded.straight _ rfl) s2 (hs2_code.trans hs1_code') hb)

theorem progBounded_key_to_nibbles (destination : Option (VarKind × MlS)) (key nExp out : ExpHOL 64)
    (M : Nat) (hsmall : M + 4 < 2 ^ 64)
    (heval : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      ∀ v, evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) nExp = some v →
        ∃ K : BitVec 64, v = .val (.word K) ∧ K.toNat ≤ M) :
    ProgBounded (.call (some (destination, none)) (ofString "key_to_nibbles") [key, nExp, out])
      (M / 4 + 4) := by
  intro F state hcode hbudget
  cases hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [key, nExp, out] with
  | none =>
    rw [evaluateHOLFiniteState_call, hargs]; simp
  | some vs =>
    have hex : ∃ v1 v2 v3, vs = [v1, v2, v3] ∧
        evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) nExp = some v2 := by
      rw [evalListHOLFinite_eq_toExact] at hargs
      rw [evalHOLFinite_eq_toExact]
      rcases h1 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) key with _ | v1
      · simp [evalListHOLExact, h1] at hargs
      · rcases h2 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) nExp with _ | v2
        · simp [evalListHOLExact, h1, h2] at hargs
        · rcases h3 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) out with _ | v3
          · simp [evalListHOLExact, h1, h2, h3] at hargs
          · simp [evalListHOLExact, h1, h2, h3] at hargs
            exact ⟨v1, v2, v3, hargs.symm, rfl⟩
    obtain ⟨v1, v2, v3, rfl, hv2⟩ := hex
    obtain ⟨K, rfl, hK_le⟩ := heval state v2 hv2
    have hK_div : K.toNat / 4 ≤ M / 4 := Nat.div_le_div_right hK_le
    have hcall := RunBounded.call (destination := destination) (bodyCost := K.toNat / 4 + 3) hargs (by omega)
      (fun body locals rs hfound => by
        rw [hcode] at hfound
        obtain ⟨rfl, hn⟩ := lookup_key_to_nibbles_n originalRuntimeCode.lookup lookup_key_to_nibbles hfound
        exact runBounded_key_to_nibbles (callEntryStateHOLFinite state locals) K (by omega) hcode hn
          (by change K.toNat / 4 + 3 ≤ state.clock - 1; omega))
    exact hcall.weaken (by omega)

theorem progBounded_key_to_nibbles_const (destination : Option (VarKind × MlS)) (key out : ExpHOL 64)
    (K : BitVec 64) (hsmall : K.toNat + 4 < 2 ^ 64) :
    ProgBounded (.call (some (destination, none)) (ofString "key_to_nibbles") [key, .const K, out])
      (K.toNat / 4 + 4) :=
  progBounded_key_to_nibbles destination key (.const K) out K.toNat hsmall
    (fun _ _ hv => by
      rw [evalHOLFinite_eq_toExact] at hv
      cases hv
      exact ⟨K, rfl, le_refl _⟩)

theorem funBounded_min : FunBounded (ofString "min") 0 :=
  funBounded_of_guestAst 31 (by rw [guestAst_len]; decide) Guest.Software.guestFn_min 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_common_prefix_length :
    FunBounded (ofString "common_prefix_length") (2 ^ 64) := by
  refine funBounded_of_guestAst 251 (by rw [guestAst_len]; decide) Guest.Software.guestFn_common_prefix_length
    (2 ^ 64) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_common_prefix_length,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_min _ _ _
      (progBounded_variableDecWhile (ofString "i") (ofString "n") .lower (Or.inr rfl)
        (cost := 0)
        (countedBody_seq_straight _ (by decide) (by decide) (by decide) CountedBody.incr)
        (by decide)
        (ProgBounded.straight _ rfl)))
    (by decide)

set_option linter.style.nameCheck false in
theorem funBounded__collapse_branch (Knc : Nat)
    (hnc : FunBounded (ofString "nibbles_concat") Knc) :
    FunBounded (ofString "_collapse_branch") (Knc + 32) := by
  refine funBounded_of_guestAst 276 (by rw [guestAst_len]; decide) Guest.Software.guestFn__collapse_branch
    (Knc + 32) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn__collapse_branch,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.dec _ _ _
      (ProgBounded.dec _ _ _
        (ProgBounded.countedDec (ofString "i") .less (Or.inl rfl) 16 1 0
          (by decide) (by decide) (by decide)
          (countedBody_seq_straight _ (by decide) (by decide) (by decide) CountedBody.incr)
          (ProgBounded.dec _ _ _
            (ProgBounded.seq
              (ProgBounded.iteMax _
                (ProgBounded.seq
                  (ProgBounded.iteMax _ (ProgBounded.call funBounded_mpt_fail none _) (ProgBounded.straight _ rfl))
                  (ProgBounded.tail funBounded_node_new_leaf _))
                (ProgBounded.straight _ rfl))
              (ProgBounded.seq
                (ProgBounded.iteMax _
                  (ProgBounded.dec _ _ _
                    (ProgBounded.dec _ _ _
                      (ProgBounded.seq
                        (ProgBounded.iteMax _ (ProgBounded.call funBounded_mpt_fail none _) (ProgBounded.straight _ rfl))
                        (ProgBounded.decCall funBounded_alloc _ _ _
                          (ProgBounded.seq (ProgBounded.straight _ rfl)
                            (ProgBounded.seq
                              (ProgBounded.iteMax _ (ProgBounded.tail funBounded_node_new_ext _) (ProgBounded.straight _ rfl))
                              (ProgBounded.decCall hnc _ _ _
                                (ProgBounded.seq
                                  (ProgBounded.iteMax _ (ProgBounded.tail funBounded_node_new_leaf _) (ProgBounded.straight _ rfl))
                                  (ProgBounded.tail funBounded_node_new_ext _)))))))))
                  (ProgBounded.straight _ rfl))
                (ProgBounded.straight _ rfl)))))))
    (by
      have h16 : (16 : BitVec 64).toNat = 16 := rfl
      have h8 : (8 : BitVec 64).toNat = 8 := rfl
      rw [h16]; omega)

private theorem eval_rField_counted_condition {F : Type}
    (state : PanSemStateFiniteExact 64 F) (counter base : MlS) (idx : Nat) (op : Cmp)
    (hop : op = .less ∨ op = .lower) (bv : ValueHOL 64) (K w : BitVec 64)
    (signed : op = .less → K.toNat < 2 ^ 63) (within : w.toNat ≤ K.toNat)
    (atCounter : state.locals.lookup counter = some (.val (.word w)))
    (atBase : state.locals.lookup base = some bv)
    (hfield : ∃ fields, bv = .rStruct fields ∧ fields[idx]? = some (.val (.word K))) :
    evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      (.cmp op (.var .local counter) (.rfield idx (.var .local base))) =
      some (.val (.word (if w.toNat < K.toNat then 1 else 0))) := by
  obtain ⟨fields, rfl, hf_idx⟩ := hfield
  rw [evalHOLFinite_eq_toExact]
  rcases hop with rfl | rfl
  · have hpos := signed rfl
    have hw_pos : w.toNat < 2 ^ 63 := by omega
    simp [evalHOLExact, atCounter, atBase, hf_idx, Compiler.Encoders.Asm.wordCmpHOL,
      Compiler.Encoders.Asm.holAsmSignedLess, hpos, hw_pos]
  · simp [evalHOLExact, atCounter, atBase, hf_idx, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]

private theorem rFieldCountedWhile_run (counter base : MlS) (idx : Nat) (op : Cmp)
    (hop : op = .less ∨ op = .lower) (bv : ValueHOL 64) (K : BitVec 64)
    (signed : op = .less → K.toNat < 2 ^ 63)
    (hfield : ∃ fields, bv = .rStruct fields ∧ fields[idx]? = some (.val (.word K)))
    {body : ProgHOL 64} {cost : Nat} (counted : CountedBody counter 1 body cost)
    (preservesBase : avoidsLocal base body = true) :
    ∀ n : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F),
      state.code = originalRuntimeCode →
      ∀ w : BitVec 64, state.locals.lookup counter = some (.val (.word w)) →
      state.locals.lookup base = some bv → w.toNat ≤ K.toNat →
      K.toNat - w.toNat = n → n * (cost + 1) ≤ state.clock →
      let evaluated := evaluateHOLFiniteState state
        (.while (.cmp op (.var .local counter) (.rfield idx (.var .local base))) body)
      state.clock ≤ evaluated.2.clock + n * (cost + 1) ∧
        evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro F state code w atCounter atBase within distance budget
    have condition := eval_rField_counted_condition state counter base idx op hop bv K w
      signed within atCounter atBase hfield
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
      have frame := evaluate_avoidsLocal_flowing base body preservesBase (decClockHOLFinite state)
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
          have nextBase : middle.locals.lookup base = some bv := by
            rw [frame (Or.inl rfl)]
            exact atBase
          have decrease : (K.toNat - (w + 1).toNat) * (cost + 1) + (cost + 1) ≤ n * (cost + 1) := by
            rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
          obtain ⟨t1, t2, t3⟩ := ih (K.toNat - (w + 1).toNat) nextRank middle (nextCode.trans code)
            (w + 1) nextCounter nextBase (by rw [natural]; omega) rfl (by omega)
          exact ⟨by omega, by omega, t3⟩
        | some r =>
          cases r with
          | «continue» => exact absurd rfl noCont
          | «break» => exact ⟨by simp; omega, by simp; omega, by simp⟩
          | timeOut => exact absurd rfl safe
          | _ => exact ⟨by simp; omega, by simp; omega, by simp⟩
    · rw [if_neg lt]
      simp

private theorem rFieldCountedWhile_zero_bounded {F : Type}
    (counter base : MlS) (idx : Nat) (op : Cmp) (hop : op = .less ∨ op = .lower)
    {body : ProgHOL 64} {cost : Nat} (counted : CountedBody counter 1 body cost)
    (preservesBase : avoidsLocal base body = true)
    (state : PanSemStateFiniteExact 64 F) (code : state.code = originalRuntimeCode)
    (atCounter : state.locals.lookup counter = some (.val (.word 0#64)))
    (budget : (2 ^ 64 - 1) * (cost + 1) ≤ state.clock) :
    RunBounded state
      (.while (.cmp op (.var .local counter) (.rfield idx (.var .local base))) body)
      ((2 ^ 64 - 1) * (cost + 1)) := by
  rcases hb : state.locals.lookup base with _ | bv
  · unfold RunBounded
    rw [evaluateHOLFiniteState_while_total]
    have hc : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
        (.cmp op (.var .local counter) (.rfield idx (.var .local base))) = none := by
      rw [evalHOLFinite_eq_toExact]; simp [evalHOLExact, atCounter, hb]
    rw [hc]; simp
  · rcases bv with _ | fields | _
    · unfold RunBounded
      rw [evaluateHOLFiniteState_while_total]
      have hc : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
          (.cmp op (.var .local counter) (.rfield idx (.var .local base))) = none := by
        rw [evalHOLFinite_eq_toExact]; simp [evalHOLExact, atCounter, hb]
      rw [hc]; simp
    · rcases hf : fields[idx]? with _ | fv
      · unfold RunBounded
        rw [evaluateHOLFiniteState_while_total]
        have hc : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
            (.cmp op (.var .local counter) (.rfield idx (.var .local base))) = none := by
          rw [evalHOLFinite_eq_toExact]; simp [evalHOLExact, atCounter, hb, hf]
        rw [hc]; simp
      · rcases fv with ⟨⟨K⟩⟩ | _ | _
        · by_cases signed : op = .less → K.toNat < 2 ^ 63
          · have ceiling : K.toNat * (cost + 1) ≤ (2 ^ 64 - 1) * (cost + 1) :=
              Nat.mul_le_mul_right _ (by have bound := K.isLt; omega)
            have bounded := rFieldCountedWhile_run counter base idx op hop (.rStruct fields) K
              signed ⟨fields, rfl, hf⟩ counted preservesBase K.toNat state code 0#64 atCounter hb
              (by simp) (by simp) (by omega)
            dsimp only at bounded
            exact ⟨by omega, bounded.2.1, bounded.2.2⟩
          · have comparison : op = .less := by
              rcases hop with eq | eq
              · exact eq
              · exfalso; apply signed; intro imp; cases eq.symm.trans imp
            have negative : ¬ K.toNat < 9223372036854775808 := fun small => signed (fun _ => small)
            subst op
            unfold RunBounded
            rw [evaluateHOLFiniteState_while_total]
            have hc : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
                (.cmp .less (.var .local counter) (.rfield idx (.var .local base))) = some (.val (.word 0)) := by
              rw [evalHOLFinite_eq_toExact]
              simp [evalHOLExact, atCounter, hb, hf, Compiler.Encoders.Asm.wordCmpHOL,
                Compiler.Encoders.Asm.holAsmSignedLess, negative]
            rw [hc]; simp
        · unfold RunBounded
          rw [evaluateHOLFiniteState_while_total]
          have hc : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
              (.cmp op (.var .local counter) (.rfield idx (.var .local base))) = none := by
            rw [evalHOLFinite_eq_toExact]; simp [evalHOLExact, atCounter, hb, hf]
          rw [hc]; simp
        · unfold RunBounded
          rw [evaluateHOLFiniteState_while_total]
          have hc : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
              (.cmp op (.var .local counter) (.rfield idx (.var .local base))) = none := by
            rw [evalHOLFinite_eq_toExact]; simp [evalHOLExact, atCounter, hb, hf]
          rw [hc]; simp
    · unfold RunBounded
      rw [evaluateHOLFiniteState_while_total]
      have hc : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
          (.cmp op (.var .local counter) (.rfield idx (.var .local base))) = none := by
        rw [evalHOLFinite_eq_toExact]; simp [evalHOLExact, atCounter, hb]
      rw [hc]; simp

private theorem progBounded_rFieldDecWhile (counter base : MlS) (idx : Nat) (op : Cmp)
    (hop : op = .less ∨ op = .lower) {body tail : ProgHOL 64} {cost tailCost : Nat}
    (counted : CountedBody counter 1 body cost)
    (preservesBase : avoidsLocal base body = true)
    (rest : ProgBounded tail tailCost) :
    ProgBounded (.dec counter .one (.const 0)
      (.seq (.while (.cmp op (.var .local counter) (.rfield idx (.var .local base))) body) tail))
      ((2 ^ 64 - 1) * (cost + 1) + tailCost) := by
  intro F state hcode hbudget
  apply RunBounded.decConst
  set s0 := setVarHOLFinite counter (.val (.word 0#64)) state with hs0_def
  have hs0_code : s0.code = originalRuntimeCode := hcode
  have hs0_i : s0.locals.lookup counter = some (.val (.word 0#64)) := by
    simp [hs0_def, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs0_clk : s0.clock = state.clock := rfl
  exact RunBounded.seq (state := s0) (a := (2 ^ 64 - 1) * (cost + 1)) (b := tailCost)
    (rFieldCountedWhile_zero_bounded counter base idx op hop counted preservesBase
      s0 hs0_code hs0_i (by rw [hs0_clk]; omega))
    (by rw [hs0_clk]; omega)
    (fun s_end _ hs_end_code hb => rest s_end (hs_end_code.trans hs0_code) hb)

private theorem progBounded_rFieldAssignWhile (counter base : MlS) (idx : Nat) (op : Cmp)
    (hop : op = .less ∨ op = .lower) {body tail : ProgHOL 64} {cost tailCost : Nat}
    (counted : CountedBody counter 1 body cost)
    (preservesBase : avoidsLocal base body = true)
    (rest : ProgBounded tail tailCost) :
    ProgBounded (.seq (.assign .local counter (.const 0))
      (.seq (.while (.cmp op (.var .local counter) (.rfield idx (.var .local base))) body) tail))
      ((2 ^ 64 - 1) * (cost + 1) + tailCost) := by
  intro F state hcode hbudget
  by_cases hvalid : isValidValueHOLFinite state.locals .local counter (.val (.word 0#64))
  · have hassign : evaluateHOLFiniteState state (.assign .local counter (.const 0)) =
        (none, setVarHOLFinite counter (.val (.word 0#64)) state) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, hvalid, setKvarHOLFinite]
    unfold RunBounded
    rw [evaluateHOLFiniteState_seq_line780, hassign]
    dsimp only
    set s0 := setVarHOLFinite counter (.val (.word 0#64)) state with hs0_def
    have hs0_code : s0.code = originalRuntimeCode := hcode
    have hs0_i : s0.locals.lookup counter = some (.val (.word 0#64)) := by
      simp [hs0_def, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hs0_clk : s0.clock = state.clock := rfl
    exact RunBounded.seq (state := s0) (a := (2 ^ 64 - 1) * (cost + 1)) (b := tailCost)
      (rFieldCountedWhile_zero_bounded counter base idx op hop counted preservesBase
        s0 hs0_code hs0_i (by rw [hs0_clk]; omega))
      (by rw [hs0_clk]; omega)
      (fun s_end _ hs_end_code hb => rest s_end (hs_end_code.trans hs0_code) hb)
  · unfold RunBounded
    rw [evaluateHOLFiniteState_seq_line780]
    simp [evaluateHOLFiniteState_assign, evalHOLExact, hvalid]

theorem funBounded_decode_account_from_leaf (Kdf Kls Krit : Nat)
    (hdf : FunBounded (ofString "rlp_decode_fully") Kdf)
    (hls : FunBounded (ofString "rlp_list_to_slices") Kls)
    (hrit : FunBounded (ofString "rlp_item") Krit) :
    FunBounded (ofString "decode_account_from_leaf")
      (Kdf + Kls + 4 * Krit + 2 * (2 ^ 64 - 1) + 27) := by
  refine funBounded_of_guestAst 293 (by rw [guestAst_len]; decide) Guest.Software.guestFn_decode_account_from_leaf
    (Kdf + Kls + 4 * Krit + 2 * (2 ^ 64 - 1) + 27) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_decode_account_from_leaf,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.dec _ _ _
      (ProgBounded.dec _ _ _
        (ProgBounded.seq
          (ProgBounded.handledCall hdf _ _ _ _ (ProgBounded.call funBounded_mpt_fail none _))
          (ProgBounded.seq
            (ProgBounded.iteMax _ (ProgBounded.call funBounded_mpt_fail none _) (ProgBounded.straight _ rfl))
            (ProgBounded.decCall hls _ _ _
              (ProgBounded.seq
                (ProgBounded.iteMax _ (ProgBounded.call funBounded_mpt_fail none _) (ProgBounded.straight _ rfl))
                (ProgBounded.dec _ _ _
                  (ProgBounded.decCall hrit _ _ _
                    (ProgBounded.decCall hrit _ _ _
                      (ProgBounded.decCall hrit _ _ _
                        (ProgBounded.decCall hrit _ _ _
                          (ProgBounded.seq
                            (ProgBounded.iteMax _ (ProgBounded.call funBounded_mpt_fail none _) (ProgBounded.straight _ rfl))
                            (ProgBounded.seq
                              (ProgBounded.iteMax _ (ProgBounded.call funBounded_mpt_fail none _) (ProgBounded.straight _ rfl))
                              (ProgBounded.dec _ _ _
                                (progBounded_rFieldDecWhile (ofString "i") (ofString "f0") 2 .lower (Or.inr rfl)
                                  (cost := 0)
                                  (countedBody_seq_straight _ (by decide) (by decide) (by decide) CountedBody.incr)
                                  (by decide)
                                  (ProgBounded.seq (ProgBounded.straight _ rfl)
                                    (ProgBounded.seq
                                      (ProgBounded.iteMax _ (ProgBounded.call funBounded_mpt_fail none _) (ProgBounded.straight _ rfl))
                                      (ProgBounded.seq
                                        (ProgBounded.weaken (progBounded_memzero_const none _ 32#64 (by decide))
                                          (by decide : (32#64).toNat / 8 + 8 ≤ 12))
                                        (progBounded_rFieldAssignWhile (ofString "i") (ofString "f1") 2 .lower (Or.inr rfl)
                                          (cost := 0)
                                          (CountedBody.dec _ _ _ (by decide)
                                            (CountedBody.dec _ _ _ (by decide)
                                              (countedBody_seq_straight _ (by decide) (by decide) (by decide) CountedBody.incr)))
                                          (by decide)
                                          (ProgBounded.seq
                                            (ProgBounded.iteMax _
                                              (ProgBounded.straight _ rfl)
                                              (ProgBounded.seq
                                                (ProgBounded.iteMax _ (ProgBounded.call funBounded_mpt_fail none _) (ProgBounded.straight _ rfl))
                                                (ProgBounded.straight _ rfl)))
                                            (ProgBounded.seq
                                              (ProgBounded.iteMax _
                                                (ProgBounded.straight _ rfl)
                                                (ProgBounded.seq
                                                  (ProgBounded.iteMax _ (ProgBounded.call funBounded_mpt_fail none _) (ProgBounded.straight _ rfl))
                                                  (ProgBounded.straight _ rfl)))
                                              (ProgBounded.straight _ rfl))))))))))))))))))))))
    (by omega)



end InitECandidate.Solver.GuestBoundLoopFree
