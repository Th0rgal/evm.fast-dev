import InitECandidate.Solver.UniformSourceClock
import InitECandidate.Solver.PanRunBounded
import InitECandidate.Solver.GuestUniformClockBound
import InitECandidate.Solver.HeapPotential

/-! Verbatim extract of the 0-sorry parts of `InitECandidate.Solver.GuestBoundHtab` (lines 1-719 and
1189-1292) that still elaborate on Lean 4.33.1; the file as a whole fails (lines 923, 1761, ...). -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace InitECandidate.Solver.Wave8GuestInv.Htab.Old

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.HeapPotential

private theorem countedBody_seq_straight {counter : MlS} {step : BitVec 64}
    (first : ProgHOL 64) {tail : ProgHOL 64} {cost : Nat}
    (hs : extStraightLine first = true)
    (ha : avoidsLocal counter first = true)
    (hn : noTopContinue first = true)
    (hrest : CountedBody counter step tail cost) :
    CountedBody counter step (.seq first tail) cost := by
  simpa using CountedBody.seq first (ProgBounded.straight first hs) ha hn hrest

private theorem countedBody_decCall_run {counter name function : MlS} {step : BitVec 64}
    {shape : ShapeHOL} {arguments : List (ExpHOL 64)} {continuation : ProgHOL 64}
    {fnCost contCost : Nat} (hne : counter ≠ name)
    (hfn : FunBounded function fnCost)
    (hcont : CountedBody counter step continuation contCost)
    {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode) (w : BitVec 64)
    (atCounter : state.locals.lookup counter = some (.val (.word w)))
    (budget : fnCost + 1 + contCost ≤ state.clock) :
    let prog : ProgHOL 64 := .decCall name shape function arguments continuation
    state.clock ≤ (evaluateHOLFiniteState state prog).2.clock + (fnCost + 1 + contCost) ∧
      (evaluateHOLFiniteState state prog).2.clock ≤ state.clock ∧
      (evaluateHOLFiniteState state prog).1 ≠ some .timeOut ∧
      (evaluateHOLFiniteState state prog).1 ≠ some .continue ∧
      ((evaluateHOLFiniteState state prog).1 = none →
        (evaluateHOLFiniteState state prog).2.locals.lookup counter = some (.val (.word (w + step))) ∧
        (evaluateHOLFiniteState state prog).2.code = state.code) := by
  dsimp only
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none =>
    rw [evaluateHOLFiniteState_decCall_args_none state name shape function arguments continuation args]
    simp
  | some values =>
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none =>
      rw [evaluateHOLFiniteState_decCall_lookup_none state name shape function arguments continuation values args lookup]
      simp
    | some installed =>
      obtain ⟨body, callee, returnShape⟩ := installed
      have bounded := ProgBounded.bodies_of_fun hfn state code (by omega) values body callee returnShape lookup
      change (callEntryStateHOLFinite state callee).clock ≤
          (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).2.clock + fnCost ∧
        (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).2.clock ≤
          (callEntryStateHOLFinite state callee).clock ∧
        (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).1 ≠ some .timeOut at bounded
      have meta' := PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) body
      cases ran : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
      | mk result post =>
        rw [ran] at bounded meta'
        obtain ⟨spent, kept, safe⟩ := bounded
        have kept_entry : post.clock ≤ (callEntryStateHOLFinite state callee).clock := kept
        change state.clock - 1 ≤ post.clock + fnCost at spent
        change post.clock ≤ state.clock - 1 at kept
        have hpost_code : post.code = originalRuntimeCode := meta'.1.trans code
        have nonzero : state.clock ≠ 0 := by omega
        rw [evaluateHOLFiniteState_decCall_total, args]
        dsimp only
        rw [lookup]
        dsimp only
        rw [if_neg nonzero, ran]
        have fixed : fixClockHOLFinite (callEntryStateHOLFinite state callee) (result, post) = (result, post) := by
          simp [fixClockHOLFinite, Nat.not_lt.mpr kept_entry]
        rw [fixed]
        dsimp only
        cases result with
        | none => dsimp only; exact ⟨by omega, by omega, by simp, by simp, by simp⟩
        | some res =>
          cases res with
          | returned value =>
            dsimp only
            split
            · let resumed := setVarHOLFinite name value { post with locals := state.locals }
              have hres_code : resumed.code = originalRuntimeCode := hpost_code
              have hres_cnt : resumed.locals.lookup counter = some (.val (.word w)) := by
                simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne, atCounter]
              have hres_bud : contCost ≤ resumed.clock := by
                change contCost ≤ post.clock; omega
              obtain ⟨c1, c2, c3, c4, c5⟩ := hcont.run resumed hres_code w hres_cnt hres_bud
              cases crun : evaluateHOLFiniteState resumed continuation with
              | mk cres cpost =>
                rw [crun] at c1 c2 c3 c4 c5
                dsimp only at c1 c2 c3 c4 c5 ⊢
                change post.clock ≤ cpost.clock + contCost at c1
                change cpost.clock ≤ post.clock at c2
                refine ⟨by omega, by omega, c3, c4, fun hnorm => ?_⟩
                obtain ⟨hi, hcd⟩ := c5 hnorm
                refine ⟨?_, (hcd.trans hpost_code).trans code.symm⟩
                rw [PanRunBounded.resVarEq_lookup, if_neg hne]
                exact hi
            · dsimp only [emptyLocalsHOLFinite]; exact ⟨by omega, by omega, by simp, by simp, by simp⟩
          | timeOut => exact False.elim (safe rfl)
          | error => dsimp only [emptyLocalsHOLFinite]; exact ⟨by omega, by omega, by simp, by simp, by simp⟩
          | «break» => dsimp only [emptyLocalsHOLFinite]; exact ⟨by omega, by omega, by simp, by simp, by simp⟩
          | «continue» => dsimp only [emptyLocalsHOLFinite]; exact ⟨by omega, by omega, by simp, by simp, by simp⟩
          | exception _ _ => dsimp only [emptyLocalsHOLFinite]; exact ⟨by omega, by omega, by simp, by simp, by simp⟩
          | finalFfi _ => dsimp only [emptyLocalsHOLFinite]; exact ⟨by omega, by omega, by simp, by simp, by simp⟩

theorem progBounded_variableCountedDec (counter limit : MlS) (op : Cmp)
    (hop : op = .less ∨ op = .lower) (hne : counter ≠ limit)
    {body tail : ProgHOL 64} {cost tailCost : Nat}
    (counted : CountedBody counter 1 body cost)
    (preservesLimit : avoidsLocal limit body = true)
    (rest : ProgBounded tail tailCost) :
    ProgBounded
      (.dec counter .one (.const 0)
        (.seq (.while (.cmp op (.var .local counter) (.var .local limit)) body) tail))
      ((2 ^ 64 - 1) * (cost + 1) + tailCost) := by
  intro F state code budget
  apply RunBounded.decConst
  let s0 := setVarHOLFinite counter (.val (.word 0)) state
  have hs0_code : s0.code = originalRuntimeCode := code
  have hs0_cnt : s0.locals.lookup counter = some (.val (.word 0)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs0_clk : s0.clock = state.clock := rfl
  have hs0_lim_eq : s0.locals.lookup limit = state.locals.lookup limit := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne]
  cases hlim : state.locals.lookup limit with
  | none =>
    have hguard : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
        (.cmp op (.var .local counter) (.var .local limit)) = none := by
      rw [evalHOLFinite_eq_toExact]
      simp [evalHOLExact, hs0_cnt, hs0_lim_eq, hlim]
    change RunBounded s0 _ _
    unfold RunBounded
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total, hguard]
    simp
  | some v =>
    cases v with
    | rStruct _ =>
      have hguard : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
          (.cmp op (.var .local counter) (.var .local limit)) = none := by
        rw [evalHOLFinite_eq_toExact]
        simp [evalHOLExact, hs0_cnt, hs0_lim_eq, hlim]
      change RunBounded s0 _ _
      unfold RunBounded
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total, hguard]
      simp
    | nStruct _ _ =>
      have hguard : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
          (.cmp op (.var .local counter) (.var .local limit)) = none := by
        rw [evalHOLFinite_eq_toExact]
        simp [evalHOLExact, hs0_cnt, hs0_lim_eq, hlim]
      change RunBounded s0 _ _
      unfold RunBounded
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total, hguard]
      simp
    | val wl =>
      cases wl with
      | word K =>
        have hs0_lim : s0.locals.lookup limit = some (.val (.word K)) := hs0_lim_eq.trans hlim
        have hloop := variableCountedWhile_zero_bounded counter limit op hop counted preservesLimit
          s0 hs0_code K hs0_cnt hs0_lim (by rw [hs0_clk]; omega)
        exact RunBounded.seq hloop (by rw [hs0_clk]; omega)
          (fun next _ nextCode nextBudget => rest next (nextCode.trans hs0_code) nextBudget)

theorem funBounded_htab_count : FunBounded (ofString "htab_count") 0 :=
  funBounded_of_guestAst 141 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htab_count 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_htab_cap : FunBounded (ofString "htab_cap") 0 :=
  funBounded_of_guestAst 142 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htab_cap 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_htab_item : FunBounded (ofString "htab_item") 0 :=
  funBounded_of_guestAst 143 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htab_item 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_node_invalidate : FunBounded (ofString "node_invalidate") 0 :=
  funBounded_of_guestAst 259 (by rw [guestAst_len]; decide) Guest.Software.guestFn_node_invalidate 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_node_new_hashed : FunBounded (ofString "node_new_hashed") 2 := by
  refine funBounded_of_guestAst 255 (by rw [guestAst_len]; decide) Guest.Software.guestFn_node_new_hashed 2 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_node_new_hashed,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_alloc _ _ _ (ProgBounded.straight _ rfl))
    (by decide)

theorem funBounded_node_new_leaf : FunBounded (ofString "node_new_leaf") 2 := by
  refine funBounded_of_guestAst 256 (by rw [guestAst_len]; decide) Guest.Software.guestFn_node_new_leaf 2 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_node_new_leaf,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_alloc _ _ _ (ProgBounded.straight _ rfl))
    (by decide)

theorem funBounded_node_new_ext : FunBounded (ofString "node_new_ext") 2 := by
  refine funBounded_of_guestAst 257 (by rw [guestAst_len]; decide) Guest.Software.guestFn_node_new_ext 2 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_node_new_ext,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_alloc _ _ _ (ProgBounded.straight _ rfl))
    (by decide)

theorem funBounded_node_new_branch : FunBounded (ofString "node_new_branch") 32 := by
  refine funBounded_of_guestAst 258 (by rw [guestAst_len]; decide) Guest.Software.guestFn_node_new_branch 32 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_node_new_branch,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_alloc _ _ _
      (ProgBounded.seq (progBounded_memzero_const none _ 176 (by decide))
        (ProgBounded.straight _ rfl)))
    (by decide)

theorem funBounded_htab_new : FunBounded (ofString "htab_new") 8 := by
  refine funBounded_of_guestAst 128 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htab_new 8 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_htab_new,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_alloc _ _ _
      (ProgBounded.dec _ _ _
        (ProgBounded.dec _ _ _
          (ProgBounded.seq (ProgBounded.straight _ rfl)
            (ProgBounded.seq (ProgBounded.straight _ rfl)
              (ProgBounded.seq (ProgBounded.straight _ rfl)
                (ProgBounded.seq (ProgBounded.straight _ rfl)
                  (ProgBounded.seq (ProgBounded.straight _ rfl)
                    (ProgBounded.decCall funBounded_alloc _ _ _
                      (ProgBounded.seq (ProgBounded.straight _ rfl)
                        (ProgBounded.decCall funBounded_alloc _ _ _
                          (ProgBounded.seq (ProgBounded.straight _ rfl)
                            (ProgBounded.decCall funBounded_alloc _ _ _
                              (ProgBounded.straight _ rfl))))))))))))))
    (by decide)

theorem funBounded_htab_new_scratch : FunBounded (ofString "htab_new_scratch") 8 := by
  refine funBounded_of_guestAst 129 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htab_new_scratch 8 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_htab_new_scratch,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_scratch_alloc _ _ _
      (ProgBounded.dec _ _ _
        (ProgBounded.dec _ _ _
          (ProgBounded.seq (ProgBounded.straight _ rfl)
            (ProgBounded.seq (ProgBounded.straight _ rfl)
              (ProgBounded.seq (ProgBounded.straight _ rfl)
                (ProgBounded.seq (ProgBounded.straight _ rfl)
                  (ProgBounded.seq (ProgBounded.straight _ rfl)
                    (ProgBounded.decCall funBounded_scratch_alloc _ _ _
                      (ProgBounded.seq (ProgBounded.straight _ rfl)
                        (ProgBounded.decCall funBounded_scratch_alloc _ _ _
                          (ProgBounded.seq (ProgBounded.straight _ rfl)
                            (ProgBounded.decCall funBounded_scratch_alloc _ _ _
                              (ProgBounded.straight _ rfl))))))))))))))
    (by decide)

theorem funBounded_htab_first_diff :
    FunBounded (ofString "htab_first_diff") ((2 ^ 64 - 1) * 9) := by
  refine funBounded_of_guestAst 130 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_htab_first_diff ((2 ^ 64 - 1) * 9) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_htab_first_diff,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  have hinner :
      ProgBounded
        (.dec (ofString "j") .one (.const 0)
          (.while (.cmp .less (.var .local (ofString "j")) (.const 8))
            (.seq
              (.ite
                (.cmp .notEqual
                  (.op .and
                    [.shift .lsr (.var .local (ofString "x"))
                      (.op .sub [.const 7, .var .local (ofString "j")]), .const 1])
                  (.const 0))
                (.return (.op .add [.panop .mul [.var .local (ofString "i"), .const 8],
                  .var .local (ofString "j")]))
                .skip)
              (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1])))))
        8 := by
    intro F state hcode hbudget
    apply RunBounded.decConst
    let s0 := setVarHOLFinite (ofString "j") (.val (.word 0)) state
    have hs0_j : s0.locals.lookup (ofString "j") = some (.val (.word 0)) := by
      simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    exact countedWhile_from (ofString "j") .less (Or.inl rfl) 8 1 (by decide) (by decide)
      (cost := 0) (countedBody_seq_straight _ (by decide) (by decide) (by decide) CountedBody.incr)
      s0 hcode 0 hs0_j (by decide) (by change 8 * (0 + 1) ≤ state.clock; omega)
  apply ProgBounded.weaken (cost := (2 ^ 64 - 1) * (max 8 0 + 0 + 1) + 0)
  · refine progBounded_variableCountedDec (ofString "i") (ofString "key_len") .lower (Or.inr rfl)
      (by decide) ?_ ?_ (ProgBounded.straight _ rfl)
    · refine CountedBody.dec (ofString "x") .one _ (by decide) ?_
      exact CountedBody.seq _ (ProgBounded.iteMax _ hinner (ProgBounded.straight .skip rfl))
        (by decide) (by decide) CountedBody.incr
    · decide
  · decide

-- Parameterized caller wrappers for functions calling htab_find_leaf / memeq / memcpy / htab_set

theorem funBounded_htab_get (Kf Km : Nat)
    (hf : FunBounded (ofString "htab_find_leaf") Kf)
    (hm : FunBounded (ofString "memeq") Km) :
    FunBounded (ofString "htab_get") (Kf + Km + 2) := by
  refine funBounded_of_guestAst 132 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_htab_get (Kf + Km + 2) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_htab_get,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply ProgBounded.weaken
  · exact ProgBounded.decCall hf _ _ _
      (ProgBounded.seq (ProgBounded.straight _ rfl)
        (ProgBounded.dec _ _ _
          (ProgBounded.dec _ _ _
            (ProgBounded.dec _ _ _
              (ProgBounded.decCall hm _ _ _ (ProgBounded.straight _ rfl))))))
  · omega

theorem funBounded_htab_has (Kf Km : Nat)
    (hf : FunBounded (ofString "htab_find_leaf") Kf)
    (hm : FunBounded (ofString "memeq") Km) :
    FunBounded (ofString "htab_has") (Kf + Km + 2) := by
  refine funBounded_of_guestAst 133 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_htab_has (Kf + Km + 2) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_htab_has,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply ProgBounded.weaken
  · exact ProgBounded.decCall hf _ _ _
      (ProgBounded.seq (ProgBounded.straight _ rfl)
        (ProgBounded.dec _ _ _
          (ProgBounded.dec _ _ _
            (ProgBounded.dec _ _ _
              (ProgBounded.decCall hm _ _ _ (ProgBounded.straight _ rfl))))))
  · omega

theorem funBounded_nodedb_lookup (Kg : Nat)
    (hg : FunBounded (ofString "htab_get") Kg) :
    FunBounded (ofString "nodedb_lookup") (Kg + 1) := by
  refine funBounded_of_guestAst 254 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_nodedb_lookup (Kg + 1) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_nodedb_lookup,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply ProgBounded.weaken
  · exact ProgBounded.decCall hg _ _ _ (ProgBounded.straight _ rfl)
  · omega

theorem funBounded_htab_del (Kf Km : Nat)
    (hf : FunBounded (ofString "htab_find_leaf") Kf)
    (hm : FunBounded (ofString "memeq") Km) :
    FunBounded (ofString "htab_del") (Kf + Km + 2) := by
  refine funBounded_of_guestAst 139 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_htab_del (Kf + Km + 2) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_htab_del,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply ProgBounded.weaken
  · exact ProgBounded.dec _ _ _
      (ProgBounded.dec _ _ _
        (ProgBounded.decCall hf _ _ _
          (ProgBounded.seq (ProgBounded.straight _ rfl)
            (ProgBounded.dec _ _ _
              (ProgBounded.decCall hm _ _ _ (ProgBounded.straight _ rfl))))))
  · omega

theorem funBounded_htab_grow_of_memcpy (Km : Nat)
    (hm : FunBounded (ofString "memcpy") Km) :
    FunBounded (ofString "htab_grow") (3 * Km + 9) := by
  refine funBounded_of_guestAst 137 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_htab_grow (3 * Km + 9) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_htab_grow,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply ProgBounded.weaken
  · exact ProgBounded.dec _ _ _
      (ProgBounded.dec _ _ _
        (ProgBounded.dec _ _ _
          (ProgBounded.decCall funBounded_alloc _ _ _
            (ProgBounded.seq (ProgBounded.call hm none _)
              (ProgBounded.seq (ProgBounded.straight _ rfl)
                (ProgBounded.decCall funBounded_alloc _ _ _
                  (ProgBounded.seq (ProgBounded.call hm none _)
                    (ProgBounded.seq (ProgBounded.straight _ rfl)
                      (ProgBounded.decCall funBounded_alloc _ _ _
                        (ProgBounded.seq (ProgBounded.call hm none _)
                          (ProgBounded.straight _ rfl)))))))))))
  · omega

theorem funBounded_htab_new_node_of_grow (Kg : Nat)
    (hg : FunBounded (ofString "htab_grow") Kg) :
    FunBounded (ofString "htab_new_node") (Kg + 1) := by
  refine funBounded_of_guestAst 134 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_htab_new_node (Kg + 1) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_htab_new_node,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply ProgBounded.weaken
  · exact ProgBounded.dec _ _ _
      (ProgBounded.seq (ProgBounded.straight _ rfl)
        (ProgBounded.dec _ _ _
          (ProgBounded.seq
            (ProgBounded.iteMax _ (ProgBounded.call hg none _) (ProgBounded.straight _ rfl))
            (ProgBounded.straight _ rfl))))
  · omega

theorem funBounded_htab_new_leaf_of (Kn Km : Nat)
    (hn : FunBounded (ofString "htab_new_node") Kn)
    (hm : FunBounded (ofString "memcpy") Km) :
    FunBounded (ofString "htab_new_leaf") (Kn + Km + 2) := by
  refine funBounded_of_guestAst 135 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_htab_new_leaf (Kn + Km + 2) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_htab_new_leaf,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply ProgBounded.weaken
  · exact ProgBounded.decCall hn _ _ _
      (ProgBounded.dec _ _ _
        (ProgBounded.dec _ _ _
          (ProgBounded.seq (ProgBounded.call hm none _)
            (ProgBounded.straight _ rfl))))
  · omega

theorem funBounded_htab_new_internal_of (Kn : Nat)
    (hn : FunBounded (ofString "htab_new_node") Kn) :
    FunBounded (ofString "htab_new_internal") (Kn + 1) := by
  refine funBounded_of_guestAst 136 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_htab_new_internal (Kn + 1) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_htab_new_internal,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply ProgBounded.weaken
  · exact ProgBounded.decCall hn _ _ _ (ProgBounded.straight _ rfl)
  · omega

theorem funBounded_htab_keys_of_memcpy (Km : Nat)
    (hm : FunBounded (ofString "memcpy") Km) :
    FunBounded (ofString "htab_keys") (2 + (2 ^ 64 - 1) * (Km + 2)) := by
  refine funBounded_of_guestAst 144 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_htab_keys (2 + (2 ^ 64 - 1) * (Km + 2)) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_htab_keys,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply ProgBounded.weaken (cost := 1 + 1 + ((2 ^ 64 - 1) * (((Km + 1) + 0) + 1) + 0))
  · refine ProgBounded.dec _ _ _
      (ProgBounded.dec _ _ _
        (ProgBounded.decCall funBounded_alloc _ _ _
          (ProgBounded.dec _ _ _
            (ProgBounded.dec _ _ _ ?_))))
    refine progBounded_variableCountedDec (ofString "i") (ofString "n") .less (Or.inl rfl)
      (by decide) (cost := (Km + 1) + 0) (tailCost := 0) ?_ ?_ (ProgBounded.straight _ rfl)
    · refine CountedBody.dec (ofString "leaf") .one _ (by decide) ?_
      exact CountedBody.seq _ (ProgBounded.call hm none _) (by decide) (by decide) CountedBody.incr
    · decide
  · have h264 : (2 ^ 64 - 1 : Nat) = 18446744073709551615 := by decide
    omega

theorem funBounded_htab_copy_of_memcpy (Km : Nat)
    (hm : FunBounded (ofString "memcpy") Km) :
    FunBounded (ofString "htab_copy") (3 * Km + 35) := by
  refine funBounded_of_guestAst 145 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_htab_copy (3 * Km + 35) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_htab_copy,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply ProgBounded.weaken
  · exact ProgBounded.dec _ _ _
      (ProgBounded.dec _ _ _
        (ProgBounded.decCall funBounded_alloc _ _ _
          (ProgBounded.seq (progBounded_memcpy_const none _ _ 88 (by decide))
            (ProgBounded.decCall funBounded_alloc _ _ _
              (ProgBounded.seq (ProgBounded.call hm none _)
                (ProgBounded.seq (ProgBounded.straight _ rfl)
                  (ProgBounded.decCall funBounded_alloc _ _ _
                    (ProgBounded.seq (ProgBounded.call hm none _)
                      (ProgBounded.seq (ProgBounded.straight _ rfl)
                        (ProgBounded.decCall funBounded_alloc _ _ _
                          (ProgBounded.seq (ProgBounded.call hm none _)
                            (ProgBounded.straight _ rfl))))))))))))
  · have h88 : (88 : BitVec 64).toNat = 88 := by decide
    omega

theorem funBounded_htab_copy_scratch_of_memcpy (Km : Nat)
    (hm : FunBounded (ofString "memcpy") Km) :
    FunBounded (ofString "htab_copy_scratch") (3 * Km + 35) := by
  refine funBounded_of_guestAst 146 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_htab_copy_scratch (3 * Km + 35) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_htab_copy_scratch,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply ProgBounded.weaken
  · exact ProgBounded.dec _ _ _
      (ProgBounded.dec _ _ _
        (ProgBounded.decCall funBounded_scratch_alloc _ _ _
          (ProgBounded.seq (progBounded_memcpy_const none _ _ 88 (by decide))
            (ProgBounded.decCall funBounded_scratch_alloc _ _ _
              (ProgBounded.seq (ProgBounded.call hm none _)
                (ProgBounded.seq (ProgBounded.straight _ rfl)
                  (ProgBounded.decCall funBounded_scratch_alloc _ _ _
                    (ProgBounded.seq (ProgBounded.call hm none _)
                      (ProgBounded.seq (ProgBounded.straight _ rfl)
                        (ProgBounded.decCall funBounded_scratch_alloc _ _ _
                          (ProgBounded.seq (ProgBounded.call hm none _)
                            (ProgBounded.straight _ rfl))))))))))))
  · have h88 : (88 : BitVec 64).toNat = 88 := by decide
    omega

theorem funBounded_htab_union_into (Ks : Nat)
    (hs : FunBounded (ofString "htab_set") Ks) :
    FunBounded (ofString "htab_union_into") ((2 ^ 64 - 1) * (Ks + 3)) := by
  refine funBounded_of_guestAst 400 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_htab_union_into ((2 ^ 64 - 1) * (Ks + 3)) rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_htab_union_into,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  refine ProgBounded.dec _ _ _ ?_
  intro F state code budget
  apply RunBounded.decConst
  let s0 := setVarHOLFinite (ofString "i") (.val (.word 0)) state
  have hs0_code : s0.code = originalRuntimeCode := code
  have hs0_cnt : s0.locals.lookup (ofString "i") = some (.val (.word 0)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs0_cap_eq : s0.locals.lookup (ofString "cap") = state.locals.lookup (ofString "cap") := by
    have hne : ofString "i" ≠ ofString "cap" := by decide
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne]
  cases hcap : state.locals.lookup (ofString "cap") with
  | none =>
    have hg : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
        (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "cap"))) = none := by
      rw [evalHOLFinite_eq_toExact]; simp [evalHOLExact, hs0_cnt, hs0_cap_eq, hcap]
    change RunBounded s0 _ _; unfold RunBounded
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total, hg]; simp
  | some vcap =>
    have hs0_cap : s0.locals.lookup (ofString "cap") = some vcap := hs0_cap_eq.trans hcap
    cases vcap with
    | rStruct _ =>
      have hg : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
          (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "cap"))) = none := by
        rw [evalHOLFinite_eq_toExact]; simp [evalHOLExact, hs0_cnt, hs0_cap]
      change RunBounded s0 _ _; unfold RunBounded
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total, hg]; simp
    | nStruct _ _ =>
      have hg : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
          (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "cap"))) = none := by
        rw [evalHOLFinite_eq_toExact]; simp [evalHOLExact, hs0_cnt, hs0_cap]
      change RunBounded s0 _ _; unfold RunBounded
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total, hg]; simp
    | val wv =>
      cases wv with
      | word K =>
        let lbody : ProgHOL 64 :=
          .decCall (ofString "s") (.comb [.one, .one, .one]) (ofString "htab_item")
            [.var .local (ofString "src"), .var .local (ofString "i")]
            (.seq
              (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "s"))) (.const 0))
                (.call (some (none, none)) (ofString "htab_set")
                  [.var .local (ofString "dst"), .rfield 1 (.var .local (ofString "s")),
                   .rfield 2 (.var .local (ofString "s"))])
                .skip)
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
        let cond : ExpHOL 64 := .cmp .less (.var .local (ofString "i")) (.var .local (ofString "cap"))
        have hcb_cont : CountedBody (ofString "i") 1
            (.seq
              (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "s"))) (.const 0))
                (.call (some (none, none)) (ofString "htab_set")
                  [.var .local (ofString "dst"), .rfield 1 (.var .local (ofString "s")),
                   .rfield 2 (.var .local (ofString "s"))])
                .skip)
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
            (Ks + 1) := by
          have hite_b : ProgBounded
              (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "s"))) (.const 0))
                (.call (some (none, none)) (ofString "htab_set")
                  [.var .local (ofString "dst"), .rfield 1 (.var .local (ofString "s")),
                   .rfield 2 (.var .local (ofString "s"))])
                .skip)
              (Ks + 1) :=
            ProgBounded.weaken
              (ProgBounded.iteMax _ (ProgBounded.call hs none _) (ProgBounded.straight .skip rfl))
              (Nat.max_le.mpr ⟨le_refl _, Nat.zero_le _⟩)
          have hcb0 := CountedBody.seq _ hite_b (by decide) (by decide)
            (CountedBody.incr (counter := ofString "i") (step := 1))
          rw [Nat.add_zero] at hcb0
          exact hcb0
        have hloop_run : ∀ n : Nat, ∀ {G : Type} (st : PanSemStateFiniteExact 64 G),
            st.code = originalRuntimeCode →
            ∀ w : BitVec 64, st.locals.lookup (ofString "i") = some (.val (.word w)) →
            st.locals.lookup (ofString "cap") = some (.val (.word K)) →
            K.toNat < 2 ^ 63 → w.toNat ≤ K.toNat → K.toNat - w.toNat = n →
            n * (Ks + 3) ≤ st.clock →
            RunBounded st (.while cond lbody) (n * (Ks + 3)) := by
          intro n
          induction n using Nat.strongRecOn with
          | ind n ih =>
            intro G st hst_code w hwi hwc hKsign hwle hrn hclk
            have h263 : (2 ^ 63 : Nat) = 9223372036854775808 := by decide
            have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by decide
            have hw2 : w.toNat < 2 ^ 63 := Nat.lt_of_le_of_lt hwle hKsign
            have hcond : evalHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a)) cond =
                some (.val (.word (if w.toNat < K.toNat then 1 else 0))) := by
              rw [evalHOLFinite_eq_toExact]
              simp only [cond, evalHOLExact, hwi, hwc, Compiler.Encoders.Asm.wordCmpHOL,
                holAsmSignedLess_small w K hw2 hKsign]
              by_cases hlt : w.toNat < K.toNat <;> simp [hlt]
            unfold RunBounded
            rw [evaluateHOLFiniteState_while_total, hcond]
            by_cases hlt : w.toNat < K.toNat
            · rw [if_pos hlt]
              simp only [show (1 : BitVec 64) ≠ 0 by decide, if_true, ne_eq, not_false_eq_true]
              have hpos : 0 < n := by omega
              have hone : Ks + 3 ≤ n * (Ks + 3) := Nat.le_mul_of_pos_left _ hpos
              have hnz : st.clock ≠ 0 := by omega
              rw [if_neg hnz, fixClockHOLFinite_evaluateState]
              have hstep := countedBody_decCall_run (name := ofString "s")
                (shape := .comb [.one, .one, .one])
                (arguments := [.var .local (ofString "src"), .var .local (ofString "i")])
                (by decide) funBounded_htab_item hcb_cont (decClockHOLFinite st) hst_code w hwi
                (by change 0 + 1 + (Ks + 1) ≤ st.clock - 1; omega)
              have havoid_cap : avoidsLocal (ofString "cap") lbody = true := by decide
              have hcap_fr := evaluate_avoidsLocal_flowing (ofString "cap") lbody havoid_cap (decClockHOLFinite st)
              dsimp only at hstep
              cases hlb : evaluateHOLFiniteState (decClockHOLFinite st) lbody with
              | mk res mid =>
                rw [hlb] at hstep hcap_fr
                dsimp only at hstep hcap_fr ⊢
                obtain ⟨b1, b2, b3, b4, b5⟩ := hstep
                change st.clock - 1 ≤ mid.clock + (0 + 1 + (Ks + 1)) at b1
                change mid.clock ≤ st.clock - 1 at b2
                cases res with
                | none =>
                  dsimp only
                  obtain ⟨hi_next, hcd_next⟩ := b5 rfl
                  have hcap_next : mid.locals.lookup (ofString "cap") = some (.val (.word K)) := by
                    rw [hcap_fr (Or.inl rfl)]; exact hwc
                  have hw1_lt : w.toNat + 1 < 2 ^ 64 := by omega
                  have hnat : (w + 1).toNat = w.toNat + 1 := by
                    rw [BitVec.toNat_add_of_lt (by simpa using hw1_lt)]
                    rfl
                  have hrem_le : (K.toNat - (w + 1).toNat) * (Ks + 3) + (Ks + 3) ≤ n * (Ks + 3) := by
                    have hle1 : (K.toNat - (w + 1).toNat) + 1 ≤ n := by omega
                    calc (K.toNat - (w + 1).toNat) * (Ks + 3) + (Ks + 3)
                        = ((K.toNat - (w + 1).toNat) + 1) * (Ks + 3) := (Nat.succ_mul _ _).symm
                      _ ≤ n * (Ks + 3) := Nat.mul_le_mul_right _ hle1
                  obtain ⟨t1, t2, t3⟩ := ih (K.toNat - (w + 1).toNat) (by omega) mid
                    (hcd_next.trans hst_code) (w + 1) hi_next hcap_next hKsign (by omega) rfl (by omega)
                  exact ⟨by omega, by omega, t3⟩
                | some r =>
                  cases r with
                  | «continue» => exact absurd rfl b4
                  | «break» => exact ⟨by simp; omega, by simp; omega, by simp⟩
                  | timeOut => exact absurd rfl b3
                  | _ => exact ⟨by simp; omega, by simp; omega, by simp⟩
            · rw [if_neg hlt]; simp
        have hwhile : RunBounded s0 (.while cond lbody) ((2 ^ 64 - 1) * (Ks + 3)) := by
          by_cases hsign : K.toNat < 2 ^ 63
          · have h264m1 : K.toNat ≤ 2 ^ 64 - 1 := Nat.le_sub_one_of_lt K.isLt
            have hceil : K.toNat * (Ks + 3) ≤ (2 ^ 64 - 1) * (Ks + 3) :=
              Nat.mul_le_mul_right _ h264m1
            have hs0_bud : K.toNat * (Ks + 3) ≤ s0.clock := le_trans hceil budget
            exact RunBounded.weaken
              (hloop_run K.toNat s0 hs0_code 0 hs0_cnt hs0_cap hsign (Nat.zero_le _) (Nat.sub_zero _) hs0_bud)
              hceil
          · have hneg : ¬ K.toNat < 9223372036854775808 := hsign
            have hcond0 : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a)) cond =
                some (.val (.word 0)) := by
              rw [evalHOLFinite_eq_toExact]
              simp [cond, evalHOLExact, hs0_cnt, hs0_cap, Compiler.Encoders.Asm.wordCmpHOL,
                Compiler.Encoders.Asm.holAsmSignedLess, hneg]
            unfold RunBounded
            rw [evaluateHOLFiniteState_while_total, hcond0]; simp
        have hret : ProgBounded (.return (.const 0)) 0 := ProgBounded.straight _ rfl
        have hseq_bud : (2 ^ 64 - 1) * (Ks + 3) + 0 ≤ s0.clock := by rw [Nat.add_zero]; exact budget
        have hseq := RunBounded.seq hwhile hseq_bud
          (fun next _ hnc hnb => hret next (hnc.trans hs0_code) hnb)
        rw [Nat.add_zero] at hseq
        exact hseq

-- ============================================================================
-- Stage 3a: Runtime-length memeq/memcpy helpers, pureMemLocal, keccak256, and cap loop
-- ============================================================================

theorem lookup_htab_new :
    originalRuntimeCode.lookup (ofString "htab_new") =
      some ([(ofString "key_len", .one), (ofString "cap", .one)],
        sourceFnBody Guest.Software.guestFn_htab_new, .one) :=
  lookup_of_guestAst_getElem 128 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_new) rfl

theorem lookup_htab_new_scratch :
    originalRuntimeCode.lookup (ofString "htab_new_scratch") =
      some ([(ofString "key_len", .one), (ofString "cap", .one)],
        sourceFnBody Guest.Software.guestFn_htab_new_scratch, .one) :=
  lookup_of_guestAst_getElem 129 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_new_scratch) rfl

theorem lookup_htab_first_diff :
    originalRuntimeCode.lookup (ofString "htab_first_diff") =
      some ([(ofString "a", .one), (ofString "b", .one), (ofString "key_len", .one)],
        sourceFnBody Guest.Software.guestFn_htab_first_diff, .one) :=
  lookup_of_guestAst_getElem 130 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_first_diff) rfl

theorem lookup_htab_find_leaf :
    originalRuntimeCode.lookup (ofString "htab_find_leaf") =
      some ([(ofString "t", .one), (ofString "key", .one)],
        sourceFnBody Guest.Software.guestFn_htab_find_leaf, .one) :=
  lookup_of_guestAst_getElem 131 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_find_leaf) rfl

theorem lookup_htab_get :
    originalRuntimeCode.lookup (ofString "htab_get") =
      some ([(ofString "t", .one), (ofString "key", .one)],
        sourceFnBody Guest.Software.guestFn_htab_get, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 132 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_get) rfl

theorem lookup_htab_has :
    originalRuntimeCode.lookup (ofString "htab_has") =
      some ([(ofString "t", .one), (ofString "key", .one)],
        sourceFnBody Guest.Software.guestFn_htab_has, .one) :=
  lookup_of_guestAst_getElem 133 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_has) rfl

theorem lookup_htab_new_node :
    originalRuntimeCode.lookup (ofString "htab_new_node") =
      some ([(ofString "t", .one)],
        sourceFnBody Guest.Software.guestFn_htab_new_node, .one) :=
  lookup_of_guestAst_getElem 134 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_new_node) rfl

theorem lookup_htab_new_leaf :
    originalRuntimeCode.lookup (ofString "htab_new_leaf") =
      some ([(ofString "t", .one), (ofString "key", .one), (ofString "value", .one)],
        sourceFnBody Guest.Software.guestFn_htab_new_leaf, .one) :=
  lookup_of_guestAst_getElem 135 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_new_leaf) rfl

theorem lookup_htab_new_internal :
    originalRuntimeCode.lookup (ofString "htab_new_internal") =
      some ([(ofString "t", .one), (ofString "bit", .one)],
        sourceFnBody Guest.Software.guestFn_htab_new_internal, .one) :=
  lookup_of_guestAst_getElem 136 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_new_internal) rfl

theorem lookup_htab_grow :
    originalRuntimeCode.lookup (ofString "htab_grow") =
      some ([(ofString "t", .one)],
        sourceFnBody Guest.Software.guestFn_htab_grow, .one) :=
  lookup_of_guestAst_getElem 137 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_grow) rfl

theorem lookup_htab_set :
    originalRuntimeCode.lookup (ofString "htab_set") =
      some ([(ofString "t", .one), (ofString "key", .one), (ofString "value", .one)],
        sourceFnBody Guest.Software.guestFn_htab_set, .one) :=
  lookup_of_guestAst_getElem 138 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_set) rfl

theorem lookup_htab_del :
    originalRuntimeCode.lookup (ofString "htab_del") =
      some ([(ofString "t", .one), (ofString "key", .one)],
        sourceFnBody Guest.Software.guestFn_htab_del, .one) :=
  lookup_of_guestAst_getElem 139 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_del) rfl

theorem lookup_htab_truncate :
    originalRuntimeCode.lookup (ofString "htab_truncate") =
      some ([(ofString "t", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_htab_truncate, .one) :=
  lookup_of_guestAst_getElem 140 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_truncate) rfl

theorem lookup_nodedb_build :
    originalRuntimeCode.lookup (ofString "nodedb_build") =
      some ([(ofString "slice_arr", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_nodedb_build, .one) :=
  lookup_of_guestAst_getElem 253 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_nodedb_build) rfl

theorem lookup_nodedb_lookup :
    originalRuntimeCode.lookup (ofString "nodedb_lookup") =
      some ([(ofString "db", .one), (ofString "hash", .one)],
        sourceFnBody Guest.Software.guestFn_nodedb_lookup, .comb [.one, .one, .one]) :=
  lookup_of_guestAst_getElem 254 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_nodedb_lookup) rfl
end InitECandidate.Solver.Wave8GuestInv.Htab.Old
