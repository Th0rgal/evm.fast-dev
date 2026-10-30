import InitECandidate.Solver.UniformSourceClock
import InitECandidate.Solver.PanRunBounded
import InitECandidate.Solver.GuestUniformClockBound
import InitECandidate.Solver.HeapPotential

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace InitECandidate.Solver.GuestBoundHtab

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

def pureMemLocal : ProgHOL 64 → Bool
  | .dec _ _ _ body => pureMemLocal body
  | .seq first second => pureMemLocal first && pureMemLocal second
  | .ite _ yes no => pureMemLocal yes && pureMemLocal no
  | .while _ body => pureMemLocal body
  | .assign .local _ _ => true
  | .skip | .break | .continue | .annot _ _ | .raise _ _ | .return _ => true
  | .primitive _ _ _ => true
  | _ => false

theorem evaluate_pureMemLocal {F : Type} (p : ProgHOL 64) (hp : pureMemLocal p = true)
    (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state p).2.memory = state.memory ∧
    (evaluateHOLFiniteState state p).2.globals = state.globals := by
  cases shape : p with
  | skip => rw [evaluateHOLFiniteState_skip]; exact ⟨rfl, rfl⟩
  | «break» => rw [evaluateHOLFiniteState_break]; exact ⟨rfl, rfl⟩
  | «continue» => rw [evaluateHOLFiniteState_continue]; exact ⟨rfl, rfl⟩
  | annot _ _ => rw [evaluateHOLFiniteState_annot]; exact ⟨rfl, rfl⟩
  | raise _ _ =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  | «return» _ =>
    rw [evaluateHOLFiniteState_return]
    split
    · exact ⟨rfl, rfl⟩
    · split <;> exact ⟨rfl, rfl⟩
  | primitive _ _ _ =>
    rw [evaluateHOLFiniteState_primitive]
    split
    · exact ⟨rfl, rfl⟩
    · split
      · exact ⟨rfl, rfl⟩
      · split <;> exact ⟨rfl, rfl⟩
  | assign kind name expr =>
    cases kind with
    | global => simp [shape, pureMemLocal] at hp
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · exact ⟨rfl, rfl⟩
      · split <;> exact ⟨rfl, rfl⟩
  | dec name sh init body =>
    have hb : pureMemLocal body = true := by simpa [shape, pureMemLocal] using hp
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · exact ⟨rfl, rfl⟩
    · rename_i val _
      split
      · have ih := evaluate_pureMemLocal body hb (setVarHOLFinite name val state)
        rcases hbr : evaluateHOLFiniteState (setVarHOLFinite name val state) body with ⟨r, s'⟩
        rw [hbr] at ih
        exact ih
      · exact ⟨rfl, rfl⟩
  | seq first second =>
    have h12 : pureMemLocal first = true ∧ pureMemLocal second = true := by
      simpa [shape, pureMemLocal, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_seq_line780]
    have ih1 := evaluate_pureMemLocal first h12.1 state
    rcases hr1 : evaluateHOLFiniteState state first with ⟨r1, mid⟩
    rw [hr1] at ih1
    dsimp only at ih1 ⊢
    have hle1 : mid.clock ≤ state.clock := by
      have := evaluateHOLFiniteState_clock_le state first
      rw [hr1] at this
      exact this
    cases r1 with
    | none =>
      dsimp only
      have ih2 := evaluate_pureMemLocal second h12.2 mid
      exact ⟨ih2.1.trans ih1.1, ih2.2.trans ih1.2⟩
    | some _ => exact ih1
  | ite cond yes no =>
    have h12 : pureMemLocal yes = true ∧ pureMemLocal no = true := by
      simpa [shape, pureMemLocal, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_pureMemLocal no h12.2 state
      · exact evaluate_pureMemLocal yes h12.1 state
    · exact ⟨rfl, rfl⟩
  | «while» cond body =>
    have hb : pureMemLocal body = true := by simpa [shape, pureMemLocal] using hp
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · exact ⟨rfl, rfl⟩
        · rename_i nonzero
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have ih1 := evaluate_pureMemLocal body hb (decClockHOLFinite state)
          have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite state) body with ⟨r1, mid⟩
          rw [hbr] at ih1 hrem
          dsimp only at ih1 hrem
          have hlt : mid.clock < state.clock := by
            change mid.clock ≤ state.clock - 1 at hrem; omega
          cases r1 with
          | none =>
            have ih2 := evaluate_pureMemLocal (.while cond body) (by simpa [pureMemLocal] using hb) mid
            exact ⟨ih2.1.trans ih1.1, ih2.2.trans ih1.2⟩
          | some res =>
            cases res with
            | «continue» =>
              have ih2 := evaluate_pureMemLocal (.while cond body) (by simpa [pureMemLocal] using hb) mid
              exact ⟨ih2.1.trans ih1.1, ih2.2.trans ih1.2⟩
            | _ => exact ih1
      · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  | _ => simp [shape, pureMemLocal] at hp
termination_by (state.clock, sizeOf p)
decreasing_by
  all_goals
    subst shape
    simp_wf
    try simp only [decClockHOLFinite, setVarHOLFinite]
    omega

theorem evaluateHOLFiniteState_structs {F : Type} (state : PanSemStateFiniteExact 64 F) (program : ProgHOL 64) :
    (evaluateHOLFiniteState state program).2.structs = state.structs := by
  have inv := evaluateInvariantsHOLFinite program
    (PanPropsEvalStateFiniteExact.ofPanSemFinite state)
    (evaluateHOLFiniteState state program).1
    (PanPropsEvalStateFiniteExact.ofPanSemFinite (evaluateHOLFiniteState state program).2)
    (by simp only [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
          PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite])
  exact inv.2.2.2.2.2.1

theorem runBounded_call_memcpy_at {F : Type}
    (state : PanSemStateFiniteExact 64 F) (destination : Option (VarKind × MlS))
    (dst src sizeExp : ExpHOL 64) (K : BitVec 64)
    (hsmall : K.toNat + 32 < 2 ^ 64)
    (hcode : state.code = originalRuntimeCode)
    (hk : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) sizeExp = some (.val (.word K)))
    (hbudget : K.toNat / 8 + 8 ≤ state.clock) :
    RunBounded state (.call (some (destination, none)) (ofString "memcpy") [dst, src, sizeExp]) (K.toNat / 8 + 8) := by
  have hc := progBounded_memcpy_const destination dst src K hsmall state hcode hbudget
  unfold RunBounded at hc ⊢
  rw [evaluateHOLFiniteState_call] at hc
  rw [evaluateHOLFiniteState_call]
  have heq : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [dst, src, sizeExp] =
      evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [dst, src, .const K] := by
    rw [evalListHOLFinite_eq_toExact, evalListHOLFinite_eq_toExact]
    rw [evalHOLFinite_eq_toExact] at hk
    simp only [evalListHOLExact, evalHOLExact, hk]
  rw [heq]
  exact hc

theorem runBounded_call_memeq_at {F : Type}
    (state : PanSemStateFiniteExact 64 F) (destination : Option (VarKind × MlS))
    (a b sizeExp : ExpHOL 64) (K : BitVec 64)
    (hsmall : K.toNat + 32 < 2 ^ 64)
    (hcode : state.code = originalRuntimeCode)
    (hk : evalHOLFinite state (h := fun addr => Classical.propDecidable (state.memaddrs addr)) sizeExp = some (.val (.word K)))
    (hbudget : K.toNat / 8 + 8 ≤ state.clock) :
    RunBounded state (.call (some (destination, none)) (ofString "memeq") [a, b, sizeExp]) (K.toNat / 8 + 8) := by
  have hc := progBounded_memeq_const destination a b K hsmall state hcode hbudget
  unfold RunBounded at hc ⊢
  rw [evaluateHOLFiniteState_call] at hc
  rw [evaluateHOLFiniteState_call]
  have heq : evalListHOLFinite state (h := fun addr => Classical.propDecidable (state.memaddrs addr)) [a, b, sizeExp] =
      evalListHOLFinite state (h := fun addr => Classical.propDecidable (state.memaddrs addr)) [a, b, .const K] := by
    rw [evalListHOLFinite_eq_toExact, evalListHOLFinite_eq_toExact]
    rw [evalHOLFinite_eq_toExact] at hk
    simp only [evalListHOLExact, evalHOLExact, hk]
  rw [heq]
  exact hc

theorem runBounded_decCall_memeq_at {F : Type}
    (state : PanSemStateFiniteExact 64 F) (name : MlS) (shape : ShapeHOL)
    (a b sizeExp : ExpHOL 64) (K : BitVec 64) {continuation : ProgHOL 64} {tailCost : Nat}
    (hsmall : K.toNat + 32 < 2 ^ 64)
    (hcode : state.code = originalRuntimeCode)
    (hk : evalHOLFinite state (h := fun addr => Classical.propDecidable (state.memaddrs addr)) sizeExp = some (.val (.word K)))
    (hbudget : K.toNat / 8 + 8 + tailCost ≤ state.clock)
    (htail : ∀ (value : ValueHOL 64) (post : PanSemStateFiniteExact 64 F),
      post.code = originalRuntimeCode →
      post.memory = state.memory →
      post.memaddrs = state.memaddrs →
      post.globals = state.globals →
      post.structs = state.structs →
      tailCost ≤ post.clock →
      RunBounded (setVarHOLFinite name value { post with locals := state.locals }) continuation tailCost) :
    RunBounded state (.decCall name shape (ofString "memeq") [a, b, sizeExp] continuation)
      (K.toNat / 8 + 8 + tailCost) := by
  have heq : evalListHOLFinite state (h := fun addr => Classical.propDecidable (state.memaddrs addr)) [a, b, sizeExp] =
      evalListHOLFinite state (h := fun addr => Classical.propDecidable (state.memaddrs addr)) [a, b, .const K] := by
    rw [evalListHOLFinite_eq_toExact, evalListHOLFinite_eq_toExact]
    rw [evalHOLFinite_eq_toExact] at hk
    simp only [evalListHOLExact, evalHOLExact, hk]
  cases hargs : evalListHOLFinite state (h := fun addr => Classical.propDecidable (state.memaddrs addr)) [a, b, sizeExp] with
  | none =>
    unfold RunBounded
    rw [evaluateHOLFiniteState_decCall_args_none state name shape (ofString "memeq") [a, b, sizeExp] continuation hargs]
    simp
  | some vs =>
    have hargs_c : evalListHOLFinite state (h := fun addr => Classical.propDecidable (state.memaddrs addr)) [a, b, .const K] = some vs :=
      heq.symm.trans hargs
    have hc_call := progBounded_memeq_const none a b K hsmall state hcode (by omega)
    unfold RunBounded at hc_call
    rw [evaluateHOLFiniteState_call, hargs_c] at hc_call
    dsimp only at hc_call
    refine RunBounded.decCall (name := name) (shape := shape) (continuation := continuation)
      (bodyCost := K.toNat / 8 + 7) (tailCost := tailCost) hargs (by omega)
      (fun body locals rs hfound => ?_) |>.weaken (by omega)
    rw [hfound] at hc_call
    dsimp only at hc_call
    have hnz : state.clock ≠ 0 := by omega
    rw [if_neg hnz] at hc_call
    have hbody_eq : body = sourceFnBody Guest.Software.guestFn_memeq := by
      rw [hcode] at hfound
      exact lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup
        (ofString "memeq") _ _ body _ rs vs locals lookup_memeq hfound
    have hpure_memeq : pureMemLocal (sourceFnBody Guest.Software.guestFn_memeq) = true := by decide
    have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state locals) body
    have hstr := evaluateHOLFiniteState_structs (callEntryStateHOLFinite state locals) body
    have hpure := evaluate_pureMemLocal body (by rw [hbody_eq]; exact hpure_memeq) (callEntryStateHOLFinite state locals)
    have hb_body : RunBounded (callEntryStateHOLFinite state locals) body (K.toNat / 8 + 7) := by
      unfold RunBounded
      have hle_raw := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state locals) body
      rcases hran : evaluateHOLFiniteState (callEntryStateHOLFinite state locals) body with ⟨res, post⟩
      rw [hran] at hle_raw hc_call
      dsimp only at hle_raw ⊢
      have hle : post.clock ≤ state.clock - 1 := hle_raw
      change state.clock - 1 ≤ post.clock + (K.toNat / 8 + 7) ∧ post.clock ≤ state.clock - 1 ∧ res ≠ some .timeOut
      cases res with
      | none => dsimp only at hc_call; exact ⟨by omega, hle, by simp⟩
      | some r =>
        cases r with
        | returned val =>
          dsimp only at hc_call
          split at hc_call <;> (dsimp only at hc_call; exact ⟨by omega, hle, by simp⟩)
        | timeOut => dsimp only [emptyLocalsHOLFinite] at hc_call; exact absurd rfl hc_call.2.2
        | error | «break» | «continue» | exception _ _ | finalFfi _ =>
          dsimp only [emptyLocalsHOLFinite] at hc_call
          exact ⟨by omega, hle, by simp⟩
    refine ⟨hb_body, ?_⟩
    intro value post hran hpost_clk
    rw [hran] at hmeta hstr hpure
    exact htail value post (hmeta.1.trans hcode) hpure.1 hmeta.2.1 hpure.2 hstr hpost_clk

private theorem evalListHOLFinite_three_word2' {F : Type}
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
    · rw [h3] at hargs; cases hargs; exact ⟨v1, v3, rfl⟩

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
          simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hnp3]

theorem lookup_keccak256 :
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
    (hbudget : (K.toNat / 136) * 163 + 258 ≤ state.clock) :
    RunBounded state (sourceFnBody Guest.Software.guestFn_keccak256) ((K.toNat / 136) * 163 + 258) := by
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
  have hs1_code : s1.code = originalRuntimeCode := hcode
  have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word K)) := by
    have hne : ofString "stp" ≠ ofString "n" := by decide
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, atN]
  have hs1_clk : s1.clock = state.clock := rfl
  have hm200 : ProgBounded
      (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "stp"), .const 200]) 33 :=
    progBounded_memzero_const none (.var .local (ofString "stp")) 200 (by decide)
  refine RunBounded.seq (state := s1) (a := 33) (b := (K.toNat / 136) * 163 + 225)
    (hm200 s1 hs1_code (by rw [hs1_clk]; omega)) (by rw [hs1_clk]; omega) ?_ |>.weaken (by omega)
  intro s2 hr2 hs2_code hs2_bud
  have hs2_n : s2.locals.lookup (ofString "n") = some (.val (.word K)) := by
    have hfr := evaluate_avoidsLocal_flowing (ofString "n")
      (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "stp"), .const 200])
      (by decide) s1 (by rw [hr2]; exact Or.inl rfl)
    rw [hr2] at hfr
    exact hfr.trans hs1_n
  apply RunBounded.decConst
  let s3 := setVarHOLFinite (ofString "i") (.val (.word 0)) s2
  have hs3_code : s3.code = originalRuntimeCode := hs2_code.trans hs1_code
  have hs3_i : s3.locals.lookup (ofString "i") = some (.val (.word 0)) := by
    simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs3_n : s3.locals.lookup (ofString "n") = some (.val (.word K)) := by
    have hne : ofString "i" ≠ ofString "n" := by decide
    simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hs2_n]
  have hs3_clk : s3.clock = s2.clock := rfl
  have hbody136 : CountedBody (ofString "i") (BitVec.ofNat 64 136)
      (.seq
        (.call (some (none, none)) (ofString "keccak_absorb_block")
          [.var .local (ofString "stp"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")]])
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 136)]))) 162 :=
    CountedBody.seq _ (ProgBounded.call funBounded_keccak_absorb_block none _) (by decide) (by decide)
      CountedBody.incr
  have h136 : (BitVec.ofNat 64 136).toNat = 136 := by decide
  have h0 : (BitVec.ofNat 64 0).toNat = 0 := by decide
  have hloop := notLowerStrideWhile_run (ofString "i") (ofString "n") K (BitVec.ofNat 64 136)
    (by rw [h136]; exact hsmall)
    (by decide) hbody136 (by decide) (by decide)
    (K.toNat / 136) s3 hs3_code (BitVec.ofNat 64 0) hs3_i hs3_n (by rw [h0]; exact Nat.zero_le _)
    (by rw [h0, h136, Nat.sub_zero])
    (by rw [hs3_clk]; omega)
  dsimp only at hloop
  change RunBounded s3 _ _
  unfold RunBounded
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hlr : evaluateHOLFiniteState s3
      (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 136)])) _)
      with ⟨lres, s4⟩
  rw [hlr] at hloop
  dsimp only at hloop ⊢
  cases lres with
  | some r =>
    dsimp only
    exact ⟨by omega, hloop.2.1, hloop.2.2.1⟩
  | none =>
    dsimp only
    obtain ⟨w', hs4_i, hs4_n, _, hw'_le, hw'_rem, hs4_code⟩ := hloop.2.2.2 rfl
    have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by decide
    rw [h136] at hw'_rem
    let rem : BitVec 64 := K - w'
    have hrem_nat : rem.toNat = K.toNat - w'.toNat := by
      simp [rem, BitVec.toNat_sub_of_le (BitVec.le_def.mpr hw'_le)]
    have hrem_lt : rem.toNat < 136 := by omega
    have hrem_small : rem.toNat + 32 < 2 ^ 64 := by omega
    have hrem_div : rem.toNat / 8 + 8 ≤ 25 := by omega
    have heval_rem : @evalHOLExact 64 F _ s4.toExact (fun a => Classical.propDecidable (s4.memaddrs a))
        (.op .sub [.var .local (ofString "n"), .var .local (ofString "i")]) = some (.val (.word rem)) := by
      simp [evalHOLExact, evalListHOLExact, hs4_n, hs4_i, wordOpHOL, wordOp, valueIsWord, valueWord, rem]
    suffices hs4_run : RunBounded s4 _ 225 by
      unfold RunBounded at hs4_run
      exact ⟨by omega, le_trans hs4_run.2.1 hloop.2.1, hs4_run.2.2⟩
    refine RunBounded.decWord s4 (ofString "rem") _ rem heval_rem ?_
    let s5 := setVarHOLFinite (ofString "rem") (.val (.word rem)) s4
    have hs5_code : s5.code = originalRuntimeCode := hs4_code.trans hs3_code
    have hs5_rem : s5.locals.lookup (ofString "rem") = some (.val (.word rem)) := by
      simp [s5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hs5_clk : s5.clock = s4.clock := rfl
    have hm136 : ProgBounded
        (.call (some (none, none)) (ofString "memzero") [.var .global (ofString "keccak_pad"), .const 136]) 25 :=
      progBounded_memzero_const none (.var .global (ofString "keccak_pad")) 136 (by decide)
    refine RunBounded.seq (state := s5) (a := 25) (b := 200)
      (hm136 s5 hs5_code (by rw [hs5_clk]; omega)) (by rw [hs5_clk]; omega) ?_ |>.weaken (by omega)
    intro s6 hr6 hs6_code hs6_bud
    have hs6_rem : s6.locals.lookup (ofString "rem") = some (.val (.word rem)) := by
      have hfr := evaluate_avoidsLocal_flowing (ofString "rem")
        (.call (some (none, none)) (ofString "memzero") [.var .global (ofString "keccak_pad"), .const 136])
        (by decide) s5 (by rw [hr6]; exact Or.inl rfl)
      rw [hr6] at hfr
      exact hfr.trans hs5_rem
    have hev6_rem : evalHOLFinite s6 (h := fun a => Classical.propDecidable (s6.memaddrs a))
        (.var .local (ofString "rem")) = some (.val (.word rem)) := by
      rw [evalHOLFinite_eq_toExact]; exact hs6_rem
    have hmcpy := (runBounded_call_memcpy_at s6 none
      (.var .global (ofString "keccak_pad"))
      (.op .add [.var .local (ofString "p"), .var .local (ofString "i")])
      (.var .local (ofString "rem")) rem hrem_small (hs6_code.trans hs5_code) hev6_rem
      (by omega)).weaken hrem_div
    refine (RunBounded.seq (state := s6) (a := 25) (b := 175) hmcpy (by omega) ?_).weaken (by omega)
    intro s7 _ hs7_code hs7_bud
    refine ProgBounded.weaken
      (ProgBounded.seq (ProgBounded.straight _ (by decide))
        (ProgBounded.seq (ProgBounded.straight _ (by decide))
          (ProgBounded.seq (ProgBounded.call funBounded_keccak_absorb_block none _)
            (ProgBounded.seq
              (ProgBounded.iteMax _ (ProgBounded.straight _ (by decide))
                (progBounded_memcpy_const none (.var .local (ofString "out")) (.var .local (ofString "stp"))
                  32 (by decide)))
              (ProgBounded.straight _ (by decide))))))
      (by decide) s7 (hs7_code.trans (hs6_code.trans hs5_code)) hs7_bud

theorem runBounded_call_keccak256_at {F : Type}
    (state : PanSemStateFiniteExact 64 F) (destination : Option (VarKind × MlS))
    (p sizeExp out : ExpHOL 64) (K : BitVec 64)
    (hsmall : K.toNat + 136 < 2 ^ 64)
    (hcode : state.code = originalRuntimeCode)
    (hk : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) sizeExp = some (.val (.word K)))
    (hbudget : (K.toNat / 136) * 163 + 259 ≤ state.clock) :
    RunBounded state (.call (some (destination, none)) (ofString "keccak256") [p, sizeExp, out])
      ((K.toNat / 136) * 163 + 259) := by
  cases hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [p, sizeExp, out] with
  | none =>
    unfold RunBounded
    rw [evaluateHOLFiniteState_call, hargs]
    simp
  | some vs =>
    obtain ⟨v1, v3, rfl⟩ := evalListHOLFinite_three_word2' state p sizeExp out K hargs hk
    exact RunBounded.call hargs hbudget (fun body locals rs hfound => by
      rw [hcode] at hfound
      obtain ⟨rfl, hn⟩ := three_arg_lookup_mid_n originalRuntimeCode.lookup
        (ofString "keccak256") (ofString "p") (ofString "out")
        (sourceFnBody Guest.Software.guestFn_keccak256)
        (by decide) (by decide) (by decide) lookup_keccak256 hfound
      exact runBounded_keccak256_body (callEntryStateHOLFinite state locals) K hsmall hcode hn
        (by change (K.toNat / 136) * 163 + 258 ≤ state.clock - 1; omega))

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

theorem runBounded_nodedb_cap_while :
    ∀ k : Nat, k ≤ 62 →
      ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (N : BitVec 64),
        2 * N.toNat + 2 < 2 ^ 63 →
        state.code = originalRuntimeCode →
        state.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 (2 ^ (63 - k))))) →
        state.locals.lookup (ofString "n") = some (.val (.word N)) →
        k ≤ state.clock →
        let cond : ExpHOL 64 :=
          .cmp .lower (.var .local (ofString "cap"))
            (.op .add [.panop .mul [.const (BitVec.ofNat 64 2), .var .local (ofString "n")],
              .const (BitVec.ofNat 64 2)])
        let body : ProgHOL 64 :=
          .assign .local (ofString "cap")
            (.panop .mul [.var .local (ofString "cap"), .const (BitVec.ofNat 64 2)])
        let r := evaluateHOLFiniteState state (.while cond body)
        state.clock ≤ r.2.clock + k ∧ r.2.clock ≤ state.clock ∧ r.1 ≠ some .timeOut ∧
          (r.1 = none →
            ∃ m : Nat, m ≤ k ∧
              r.2.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 (2 ^ (63 - m))))) ∧
              2 * N.toNat + 2 ≤ 2 ^ (63 - m) ∧
              r.2.locals.lookup (ofString "n") = some (.val (.word N)) ∧
              r.2.locals.lookup (ofString "slice_arr") = state.locals.lookup (ofString "slice_arr") ∧
              r.2.memory = state.memory ∧
              r.2.globals = state.globals ∧
              r.2.memaddrs = state.memaddrs ∧
              r.2.structs = state.structs ∧
              r.2.code = state.code) := by
  intro k
  induction k with
  | zero =>
    intro _ F state N hN hcode hcap hn _
    dsimp only
    have h263 : (2 ^ 63 : Nat) = 9223372036854775808 := by decide
    have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by decide
    have hcap_nat : (BitVec.ofNat 64 (2 ^ 63)).toNat = 2 ^ 63 := by decide
    have hlim_nat : (BitVec.ofNat 64 2 * N + BitVec.ofNat 64 2).toNat = 2 * N.toNat + 2 := by
      have hmul : (BitVec.ofNat 64 2 * N).toNat = 2 * N.toNat := by
        rw [BitVec.toNat_mul, show (BitVec.ofNat 64 2).toNat = 2 by decide]
        exact Nat.mod_eq_of_lt (by omega)
      rw [BitVec.toNat_add, hmul, show (BitVec.ofNat 64 2).toNat = 2 by decide]
      exact Nat.mod_eq_of_lt (by omega)
    have hnot_lt : ¬ (BitVec.ofNat 64 (2 ^ (63 - 0))).toNat <
        (BitVec.ofNat 64 2 * N + (BitVec.ofNat 64 2 + 0)).toNat := by
      have hz : BitVec.ofNat 64 2 + (0 : BitVec 64) = BitVec.ofNat 64 2 := by decide
      rw [Nat.sub_zero, hz, hcap_nat, hlim_nat]
      omega
    have hev : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
        (.cmp .lower (.var .local (ofString "cap"))
          (.op .add [.panop .mul [.const (BitVec.ofNat 64 2), .var .local (ofString "n")],
            .const (BitVec.ofNat 64 2)])) = some (.val (.word 0)) := by
      rw [evalHOLFinite_eq_toExact]
      simp only [evalHOLExact, evalListHOLExact, hcap, hn, valueIsWord, valueWord, panOpHOL,
        wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr, Bool.and_self, if_true,
        Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq, if_neg hnot_lt]
    rw [evaluateHOLFiniteState_while_total, hev]
    dsimp only
    have h0_not_ne : ¬ ((0 : BitVec 64) ≠ 0) := by decide
    rw [if_neg h0_not_ne]
    refine ⟨Nat.le_add_right _ _, le_refl _, by simp, fun _ => ?_⟩
    exact ⟨0, le_refl _, hcap, by omega, hn, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ k ih =>
    intro hk F state N hN hcode hcap hn hclk
    dsimp only
    have h263 : (2 ^ 63 : Nat) = 9223372036854775808 := by decide
    have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by decide
    have hpow_le : 2 ^ (63 - (k + 1)) ≤ 2 ^ 62 :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have h262 : (2 ^ 62 : Nat) = 4611686018427387904 := by decide
    have hcap_nat : (BitVec.ofNat 64 (2 ^ (63 - (k + 1)))).toNat = 2 ^ (63 - (k + 1)) := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    have hlim_nat : (BitVec.ofNat 64 2 * N + (BitVec.ofNat 64 2 + 0)).toNat = 2 * N.toNat + 2 := by
      have hz : BitVec.ofNat 64 2 + (0 : BitVec 64) = BitVec.ofNat 64 2 := by decide
      rw [hz]
      have hmul : (BitVec.ofNat 64 2 * N).toNat = 2 * N.toNat := by
        rw [BitVec.toNat_mul, show (BitVec.ofNat 64 2).toNat = 2 by decide]
        exact Nat.mod_eq_of_lt (by omega)
      rw [BitVec.toNat_add, hmul, show (BitVec.ofNat 64 2).toNat = 2 by decide]
      exact Nat.mod_eq_of_lt (by omega)
    have hev : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
        (.cmp .lower (.var .local (ofString "cap"))
          (.op .add [.panop .mul [.const (BitVec.ofNat 64 2), .var .local (ofString "n")],
            .const (BitVec.ofNat 64 2)])) =
        some (.val (.word (if 2 ^ (63 - (k + 1)) < 2 * N.toNat + 2 then 1 else 0))) := by
      rw [evalHOLFinite_eq_toExact]
      simp only [evalHOLExact, evalListHOLExact, hcap, hn, valueIsWord, valueWord, panOpHOL,
        wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr, Bool.and_self, if_true,
        Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq, hcap_nat, hlim_nat]
    rw [evaluateHOLFiniteState_while_total, hev]
    dsimp only
    by_cases hlt : 2 ^ (63 - (k + 1)) < 2 * N.toNat + 2
    · rw [if_pos hlt]
      have h1_ne : (1 : BitVec 64) ≠ 0 := by decide
      rw [if_pos h1_ne]
      have hnz : state.clock ≠ 0 := by omega
      rw [if_neg hnz]
      rw [fixClockHOLFinite_evaluateState]
      have hmul2 : BitVec.ofNat 64 (2 ^ (63 - (k + 1))) * BitVec.ofNat 64 2 =
          BitVec.ofNat 64 (2 ^ (63 - k)) := by
        apply BitVec.eq_of_toNat_eq
        have heq_exp : 63 - k = (63 - (k + 1)) + 1 := by omega
        have hp : 2 ^ (63 - k) = 2 ^ (63 - (k + 1)) * 2 := by
          rw [heq_exp, Nat.pow_succ]
        rw [BitVec.toNat_mul, hcap_nat, show (BitVec.ofNat 64 2).toNat = 2 by decide,
          BitVec.toNat_ofNat, hp]
      have hbody_eq :
          evaluateHOLFiniteState (decClockHOLFinite state)
            (.assign .local (ofString "cap")
              (.panop .mul [.var .local (ofString "cap"), .const (BitVec.ofNat 64 2)])) =
          (none, setVarHOLFinite (ofString "cap") (.val (.word (BitVec.ofNat 64 (2 ^ (63 - k)))))
            (decClockHOLFinite state)) := by
        rw [evaluateHOLFiniteState_assign]
        have hcap_dec : (decClockHOLFinite state).locals.lookup (ofString "cap") =
            some (.val (.word (BitVec.ofNat 64 (2 ^ (63 - (k + 1)))))) := hcap
        simp only [evalHOLExact, evalListHOLExact, hcap_dec, valueIsWord, valueWord, panOpHOL,
          List.all, List.map, Option.map, Bool.and_self, if_true, hmul2,
          isValidValueHOLFinite, lookupKvarHOLFinite, shapeOfHOLExact, shapeEqHOL,
          setKvarHOLFinite]
      rw [hbody_eq]
      dsimp only
      set mid := setVarHOLFinite (ofString "cap") (.val (.word (BitVec.ofNat 64 (2 ^ (63 - k)))))
        (decClockHOLFinite state)
      have hmid_code : mid.code = originalRuntimeCode := hcode
      have hmid_cap : mid.locals.lookup (ofString "cap") =
          some (.val (.word (BitVec.ofNat 64 (2 ^ (63 - k))))) := by
        simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hmid_n : mid.locals.lookup (ofString "n") = some (.val (.word N)) := by
        have hne : ofString "cap" ≠ ofString "n" := by decide
        simp [mid, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hn]
      have hmid_sa : mid.locals.lookup (ofString "slice_arr") = state.locals.lookup (ofString "slice_arr") := by
        have hne : ofString "cap" ≠ ofString "slice_arr" := by decide
        simp [mid, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne]
      have hmid_clk : mid.clock = state.clock - 1 := rfl
      have hrec := ih (by omega) mid N hN hmid_code hmid_cap hmid_n (by rw [hmid_clk]; omega)
      dsimp only at hrec
      obtain ⟨r1, r2, r3, r4⟩ := hrec
      rw [hmid_clk] at r1 r2
      refine ⟨by omega, by omega, r3, fun hnorm => ?_⟩
      obtain ⟨m, hm_le, hm_cap, hm_ge, hm_n, hm_sa, hm_mem, hm_glob, hm_ma, hm_str, hm_cd⟩ := r4 hnorm
      exact ⟨m, by omega, hm_cap, hm_ge, hm_n, hm_sa.trans hmid_sa, hm_mem, hm_glob, hm_ma, hm_str, hm_cd⟩
    · rw [if_neg hlt]
      have h0_not_ne : ¬ ((0 : BitVec 64) ≠ 0) := by decide
      rw [if_neg h0_not_ne]
      refine ⟨Nat.le_add_right _ _, le_refl _, by simp, fun _ => ?_⟩
      exact ⟨k + 1, le_refl _, hcap, by omega, hn, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Stage 3b: Memory, byte-slice, and allocator lemmas -/

def WordMemRange {F : Type} (state : PanSemStateFiniteExact 64 F) (base : Nat) (bytes : Nat) : Prop :=
  base % 8 = 0 ∧ base + bytes < 2 ^ 64 ∧
  ∀ off : Nat, off < bytes → off % 8 = 0 →
    state.memaddrs (BitVec.ofNat 64 (base + off))

def ByteReadable {F : Type} (state : PanSemStateFiniteExact 64 F) (base : Nat) (bytes : Nat) : Prop :=
  base + bytes < 2 ^ 64 ∧
  ∀ i : Nat, i < bytes →
    state.memaddrs (panByteAlignHOL (BitVec.ofNat 64 (base + i)))

def memWordAt (mem : BitVec 64 → HolWordLab 64) (addr : BitVec 64) : BitVec 64 :=
  match mem addr with
  | .word w => w

def memByteAt (mem : BitVec 64 → HolWordLab 64) (be : Bool) (addr : BitVec 64) : UInt8 :=
  panGetByteHOL addr (memWordAt mem (panByteAlignHOL addr)) be

def bitInByteMSB (b : UInt8) (j : Nat) : Nat :=
  (b.toNat >>> (7 - j)) % 2

def memBitAt (mem : BitVec 64 → HolWordLab 64) (be : Bool) (base : BitVec 64) (bit : Nat) : Nat :=
  bitInByteMSB (memByteAt mem be (base + BitVec.ofNat 64 (bit / 8))) (bit % 8)

theorem wordMemRange_byteReadable {F : Type} (state : PanSemStateFiniteExact 64 F)
    {base bytes : Nat} (hw : WordMemRange state base bytes) (hb : bytes % 8 = 0) :
    ByteReadable state base bytes := by
  have hb8 : base % 8 = 0 := hw.1
  have hlt : base + bytes < 2 ^ 64 := hw.2.1
  refine ⟨hlt, fun i hi => ?_⟩
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by decide
  have hbi_lt : base + i < 2 ^ 64 := by omega
  have hdiv : (base + i) / 8 * 8 = base + (i / 8 * 8) := by omega
  have hal_eq : panByteAlignHOL (BitVec.ofNat 64 (base + i)) = BitVec.ofNat 64 (base + (i / 8 * 8)) := by
    apply BitVec.eq_of_toNat_eq
    rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbi_lt,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hdiv]
  rw [hal_eq]
  exact hw.2.2 (i / 8 * 8) (by omega) (by omega)

theorem wordMemRange_subrange {F : Type} {state : PanSemStateFiniteExact 64 F}
    {base bytes subBase subBytes : Nat}
    (hw : WordMemRange state base bytes)
    (hal : subBase % 8 = 0)
    (hlo : base ≤ subBase)
    (hhi : subBase + subBytes ≤ base + bytes) :
    WordMemRange state subBase subBytes := by
  have hb8 : base % 8 = 0 := hw.1
  have hlt : base + bytes < 2 ^ 64 := hw.2.1
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by decide
  refine ⟨hal, by omega, fun off hoff hoff8 => ?_⟩
  have heq : subBase + off = base + ((subBase - base) + off) := by omega
  rw [heq]
  exact hw.2.2 ((subBase - base) + off) (by omega) (by omega)

theorem wordMemRange_of_memaddrs_eq {F₁ F₂ : Type}
    {s₁ : PanSemStateFiniteExact 64 F₁} {s₂ : PanSemStateFiniteExact 64 F₂}
    {base bytes : Nat}
    (hw : WordMemRange s₁ base bytes)
    (hma : s₂.memaddrs = s₁.memaddrs) :
    WordMemRange s₂ base bytes := by
  refine ⟨hw.1, hw.2.1, fun off hoff hoff8 => ?_⟩
  rw [hma]
  exact hw.2.2 off hoff hoff8

theorem panMemLoadByte_eq_memByteAt {mem : BitVec 64 → HolWordLab 64}
    {dom : BitVec 64 → Prop} [DecidablePred dom] {be : Bool} {addr : BitVec 64}
    (hdom : dom (panByteAlignHOL addr)) :
    panMemLoadByteHOL mem dom be addr = some (memByteAt mem be addr) := by
  cases hcell : mem (panByteAlignHOL addr) with
  | word w => simp [panMemLoadByteHOL, memByteAt, memWordAt, hcell, hdom]

theorem panMemStore_eq_some {mem : BitVec 64 → HolWordLab 64}
    {dom : BitVec 64 → Prop} [DecidablePred dom] {addr val : BitVec 64}
    (hdom : dom addr) :
    panMemStoreHOL addr (.word val) dom mem =
      some (fun current => if current = addr then .word val else mem current) := by
  simp [panMemStoreHOL, hdom]

theorem panMemStore_getByte_disjoint {mem : BitVec 64 → HolWordLab 64}
    {be : Bool} {addr val addr' : BitVec 64}
    (hne : panByteAlignHOL addr' ≠ addr) :
    memByteAt (fun current => if current = addr then .word val else mem current) be addr' =
      memByteAt mem be addr' := by
  simp [memByteAt, memWordAt, hne]

theorem panMemStoreByte_getByte_same {mem : BitVec 64 → HolWordLab 64}
    {dom : BitVec 64 → Prop} [DecidablePred dom] {be : Bool}
    {addr : BitVec 64} {b : UInt8} {mem' : BitVec 64 → HolWordLab 64}
    (hst : panMemStoreByteWord8HOL mem dom be addr (BitVec.ofNat 8 b.toNat) = some mem') :
    memByteAt mem' be addr = b ∧
    ∀ addr' : BitVec 64, addr' ≠ addr → memByteAt mem' be addr' = memByteAt mem be addr' := by
  unfold panMemStoreByteWord8HOL at hst
  dsimp only at hst
  cases hcell : mem (panByteAlignHOL addr) with
  | word cell =>
    rw [hcell] at hst
    split at hst
    · injection hst with hmem
      subst hmem
      have hb8 : b.toNat < 256 := b.toNat_lt_size
      have hb_mod : (BitVec.ofNat 8 b.toNat).toNat = b.toNat := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hb8
      have hset_nat := panSetByteHOL_toNat (width := 64) (by decide) addr cell b be
      have hK_le : byteBitIndex addr be + 8 ≤ 64 := by
        cases be <;> simp only [byteBitIndex, Bool.false_eq_true, if_true, if_false] <;> omega
      have hpow_div : ∀ (x y z K : Nat), y < 256 → z < 2 ^ K →
          (x * 2 ^ (K + 8) + y * 2 ^ K + z) / 2 ^ K % 256 = y := by
        intro x y z K hy hz
        have hpK : 0 < 2 ^ K := Nat.two_pow_pos K
        have h1 : x * 2 ^ (K + 8) + y * 2 ^ K + z = z + (y + x * 256) * 2 ^ K := by
          rw [Nat.pow_add, show (2 ^ 8 : Nat) = 256 by decide, Nat.add_mul,
            Nat.mul_assoc x 256 (2 ^ K), Nat.mul_comm 256 (2 ^ K), ← Nat.mul_assoc]
          omega
        rw [h1, Nat.add_mul_div_right _ _ hpK, Nat.div_eq_of_lt hz, Nat.zero_add]
        omega
      have hpow_div_low : ∀ (x y z K J : Nat), y < 256 → z < 2 ^ K → J + 8 ≤ K →
          (x * 2 ^ (K + 8) + y * 2 ^ K + z) / 2 ^ J % 256 = z / 2 ^ J % 256 := by
        intro x y z K J _ _ hJK
        have hpJ : 0 < 2 ^ J := Nat.two_pow_pos J
        have hdK : 2 ^ K = 2 ^ (K - J - 8) * (256 * 2 ^ J) := by
          have hk_eq : K = (K - J - 8) + 8 + J := by omega
          conv_lhs => rw [hk_eq]
          rw [Nat.pow_add, Nat.pow_add, show (2 ^ 8 : Nat) = 256 by decide, Nat.mul_assoc]
        have hdK8 : 2 ^ (K + 8) = 2 ^ (K - J) * (256 * 2 ^ J) := by
          have hk_eq : K + 8 = (K - J) + 8 + J := by omega
          conv_lhs => rw [hk_eq]
          rw [Nat.pow_add, Nat.pow_add, show (2 ^ 8 : Nat) = 256 by decide, Nat.mul_assoc]
        have h1 : x * 2 ^ (K + 8) + y * 2 ^ K + z =
            z + ((x * 2 ^ (K - J) + y * 2 ^ (K - J - 8)) * 256) * 2 ^ J := by
          rw [hdK, hdK8, ← Nat.mul_assoc x, ← Nat.mul_assoc y, ← Nat.add_mul, ← Nat.mul_assoc]
          omega
        rw [h1, Nat.add_mul_div_right _ _ hpJ]
        omega
      have hpow_div_high : ∀ (x y z K J : Nat), y < 256 → z < 2 ^ K → K + 8 ≤ J →
          (x * 2 ^ (K + 8) + y * 2 ^ K + z) / 2 ^ J % 256 =
            (x * 2 ^ (K + 8)) / 2 ^ J % 256 := by
        intro x y z K J hy hz hKJ
        have hyz : y * 2 ^ K + z < 2 ^ (K + 8) := by
          have : y * 2 ^ K ≤ 255 * 2 ^ K := Nat.mul_le_mul_right _ (by omega)
          have h2 : 255 * 2 ^ K + 2 ^ K = 2 ^ (K + 8) := by
            rw [Nat.pow_add, show (2 ^ 8 : Nat) = 256 by decide]; omega
          omega
        have hdJ : 2 ^ J = 2 ^ (K + 8) * 2 ^ (J - (K + 8)) := by
          have hj_eq : J = (K + 8) + (J - (K + 8)) := by omega
          conv_lhs => rw [hj_eq]
          rw [Nat.pow_add]
        have hpK8 : 0 < 2 ^ (K + 8) := Nat.two_pow_pos _
        have hsum : x * 2 ^ (K + 8) + y * 2 ^ K + z = (y * 2 ^ K + z) + x * 2 ^ (K + 8) := by omega
        rw [hsum, hdJ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
          Nat.add_mul_div_right _ _ hpK8, Nat.div_eq_of_lt hyz, Nat.zero_add,
          Nat.mul_div_cancel _ hpK8]
      have hcell_high : ∀ J : Nat, byteBitIndex addr be + 8 ≤ J →
          ((cell.toNat / 2 ^ (byteBitIndex addr be + 8)) * 2 ^ (byteBitIndex addr be + 8)) / 2 ^ J =
            cell.toNat / 2 ^ J := by
        intro J hKJ
        have hdJ : 2 ^ J = 2 ^ (byteBitIndex addr be + 8) * 2 ^ (J - (byteBitIndex addr be + 8)) := by
          have hj_eq : J = (byteBitIndex addr be + 8) + (J - (byteBitIndex addr be + 8)) := by omega
          conv_lhs => rw [hj_eq]
          rw [Nat.pow_add]
        have hpK8 : 0 < 2 ^ (byteBitIndex addr be + 8) := Nat.two_pow_pos _
        rw [hdJ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ hpK8]
      have h256_pow : ∀ a : BitVec 64,
          (256 : Nat) ^ (if be then 8 - 1 - a.toNat % 8 else a.toNat % 8) = 2 ^ byteBitIndex a be := by
        intro a
        rw [pow256_eq_two_pow_mul]
        cases be <;> simp [byteBitIndex]
      constructor
      · simp only [memByteAt, memWordAt, ↓reduceIte, hb_mod, panGetByteHOL]
        have heq_nat : (panSetByteHOL addr (BitVec.ofNat 64 b.toNat) cell be).toNat /
            256 ^ (if be then 64 / 8 - 1 - addr.toNat % (64 / 8) else addr.toNat % (64 / 8)) % 256 =
            b.toNat := by
          change (panSetByteHOL addr (BitVec.ofNat 64 b.toNat) cell be).toNat /
              256 ^ (if be then 8 - 1 - addr.toNat % 8 else addr.toNat % 8) % 256 =
            b.toNat
          rw [hset_nat, h256_pow addr]
          exact hpow_div _ _ _ _ hb8 (Nat.mod_lt _ (Nat.two_pow_pos _))
        rw [heq_nat, UInt8.ofNat_toNat]
      · intro addr' hne
        by_cases hal : panByteAlignHOL addr' = panByteAlignHOL addr
        · simp only [memByteAt, memWordAt, hal, ↓reduceIte, hb_mod, hcell, panGetByteHOL]
          have hmod_ne : addr'.toNat % 8 ≠ addr.toNat % 8 := by
            intro hmeq
            apply hne
            apply BitVec.eq_of_toNat_eq
            have ha1 := panByteAlign_toNat64 addr'
            have ha2 := panByteAlign_toNat64 addr
            rw [hal] at ha1
            omega
          have hidx_ne : byteBitIndex addr' be ≠ byteBitIndex addr be := by
            have hm1 : addr'.toNat % 8 < 8 := by omega
            have hm2 : addr.toNat % 8 < 8 := by omega
            cases be <;> simp only [byteBitIndex, Bool.false_eq_true, if_true, if_false] <;> omega
          have hidx_sep : byteBitIndex addr' be + 8 ≤ byteBitIndex addr be ∨
              byteBitIndex addr be + 8 ≤ byteBitIndex addr' be := by
            have hm1 : addr'.toNat % 8 < 8 := by omega
            have hm2 : addr.toNat % 8 < 8 := by omega
            cases be <;> simp only [byteBitIndex, Bool.false_eq_true, if_true, if_false] at hidx_ne ⊢ <;> omega
          apply congrArg UInt8.ofNat
          change (panSetByteHOL addr (BitVec.ofNat 64 b.toNat) cell be).toNat /
              256 ^ (if be then 8 - 1 - addr'.toNat % 8 else addr'.toNat % 8) % 256 =
            cell.toNat / 256 ^ (if be then 8 - 1 - addr'.toNat % 8 else addr'.toNat % 8) % 256
          rw [hset_nat, h256_pow addr']
          rcases hidx_sep with hlow | hhigh
          · rw [hpow_div_low _ _ _ _ _ hb8 (Nat.mod_lt _ (Nat.two_pow_pos _)) hlow]
            have hc_eq : 2 ^ byteBitIndex addr be =
                (2 ^ (byteBitIndex addr be - (byteBitIndex addr' be + 8)) * 256) *
                  2 ^ byteBitIndex addr' be := by
              have hk_eq : byteBitIndex addr be =
                  (byteBitIndex addr be - (byteBitIndex addr' be + 8)) + 8 + byteBitIndex addr' be := by omega
              conv_lhs => rw [hk_eq]
              rw [Nat.pow_add, Nat.pow_add, show (2 ^ 8 : Nat) = 256 by decide]
            have hcell_eq : cell.toNat =
                cell.toNat % 2 ^ byteBitIndex addr be +
                (((cell.toNat / 2 ^ byteBitIndex addr be) *
                  2 ^ (byteBitIndex addr be - (byteBitIndex addr' be + 8))) * 256) *
                  2 ^ byteBitIndex addr' be := by
              have hdm := (Nat.div_add_mod cell.toNat (2 ^ byteBitIndex addr be)).symm
              rw [Nat.mul_comm (2 ^ byteBitIndex addr be)] at hdm
              have hmul : (cell.toNat / 2 ^ byteBitIndex addr be) * 2 ^ byteBitIndex addr be =
                  (((cell.toNat / 2 ^ byteBitIndex addr be) *
                    2 ^ (byteBitIndex addr be - (byteBitIndex addr' be + 8))) * 256) *
                    2 ^ byteBitIndex addr' be := by
                have hq : ∀ q : Nat, q * 2 ^ byteBitIndex addr be =
                    ((q * 2 ^ (byteBitIndex addr be - (byteBitIndex addr' be + 8))) * 256) *
                      2 ^ byteBitIndex addr' be := by
                  intro q
                  rw [hc_eq, ← Nat.mul_assoc, ← Nat.mul_assoc]
                exact hq (cell.toNat / 2 ^ byteBitIndex addr be)
              rw [hmul] at hdm
              omega
            conv_rhs => rw [hcell_eq]
            rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos _)]
            omega
          · rw [hpow_div_high _ _ _ _ _ hb8 (Nat.mod_lt _ (Nat.two_pow_pos _)) hhigh,
              hcell_high _ hhigh]
        · simp only [memByteAt, memWordAt, hal, ↓reduceIte]
    · cases hst

theorem nat_eq_of_digits_256_8 {u v : Nat} (hu : u < 2 ^ 64) (hv : v < 2 ^ 64)
    (hd : ∀ r : Nat, r < 8 → u / 256 ^ r % 256 = v / 256 ^ r % 256) : u = v := by
  have hstep : ∀ k : Nat, k ≤ 8 → u % 256 ^ k = v % 256 ^ k := by
    intro k hk
    induction k with
    | zero => omega
    | succ k ih =>
      have hklt : k < 8 := by omega
      have hprev := ih (by omega)
      have hdk := hd k hklt
      have hp1 : 256 ^ (k + 1) = 256 ^ k * 256 := Nat.pow_succ 256 k
      have hdecomp : ∀ x : Nat, x % 256 ^ (k + 1) = (x / 256 ^ k % 256) * 256 ^ k + x % 256 ^ k := by
        intro x
        rw [hp1]
        have hp_pos : 0 < 256 ^ k := Nat.pos_of_ne_zero (by positivity)
        have hlt_rem : (x / 256 ^ k % 256) * 256 ^ k + x % 256 ^ k < 256 ^ k * 256 := by
          have h1 : x / 256 ^ k % 256 ≤ 255 := by omega
          have h2 : (x / 256 ^ k % 256) * 256 ^ k ≤ 255 * 256 ^ k := Nat.mul_le_mul_right _ h1
          have h3 : x % 256 ^ k < 256 ^ k := Nat.mod_lt _ hp_pos
          omega
        have hx_eq : x = ((x / 256 ^ k % 256) * 256 ^ k + x % 256 ^ k) +
            (x / 256 ^ k / 256) * (256 ^ k * 256) := by
          calc x
            _ = 256 ^ k * (x / 256 ^ k) + x % 256 ^ k := (Nat.div_add_mod x (256 ^ k)).symm
            _ = 256 ^ k * (256 * (x / 256 ^ k / 256) + x / 256 ^ k % 256) + x % 256 ^ k := by
                rw [Nat.div_add_mod (x / 256 ^ k) 256]
            _ = ((x / 256 ^ k % 256) * 256 ^ k + x % 256 ^ k) +
                (x / 256 ^ k / 256) * (256 ^ k * 256) := by
                rw [Nat.left_distrib, Nat.mul_comm (256 ^ k) (x / 256 ^ k % 256),
                  ← Nat.mul_assoc, Nat.mul_comm (256 ^ k * 256) (x / 256 ^ k / 256)]
                omega
        conv_lhs => rw [hx_eq]
        rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt_rem]
      rw [hdecomp u, hdecomp v, hdk, hprev]
  have h8 := hstep 8 (le_refl 8)
  have hp8 : (256 ^ 8 : Nat) = 2 ^ 64 := by decide
  rw [hp8, Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hv] at h8
  exact h8

theorem memWordAt_eq_iff_bytes {mem₁ mem₂ : BitVec 64 → HolWordLab 64}
    {be : Bool} {addr₁ addr₂ : BitVec 64}
    (hal₁ : addr₁.toNat % 8 = 0) (hal₂ : addr₂.toNat % 8 = 0)
    (h1 : addr₁.toNat + 8 < 2 ^ 64) (h2 : addr₂.toNat + 8 < 2 ^ 64) :
    memWordAt mem₁ addr₁ = memWordAt mem₂ addr₂ ↔
      ∀ r : Nat, r < 8 →
        memByteAt mem₁ be (addr₁ + BitVec.ofNat 64 r) =
          memByteAt mem₂ be (addr₂ + BitVec.ofNat 64 r) := by
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by decide
  have hal_self₁ : panByteAlignHOL addr₁ = addr₁ := by
    apply BitVec.eq_of_toNat_eq; rw [panByteAlign_toNat64]; omega
  have hal_self₂ : panByteAlignHOL addr₂ = addr₂ := by
    apply BitVec.eq_of_toNat_eq; rw [panByteAlign_toNat64]; omega
  have hal_off : ∀ (a : BitVec 64) (r : Nat), a.toNat % 8 = 0 → a.toNat + 8 < 2 ^ 64 → r < 8 →
      panByteAlignHOL (a + BitVec.ofNat 64 r) = a ∧ (a + BitVec.ofNat 64 r).toNat % 8 = r := by
    intro a r ha8 ha_lt hr
    have har : (a + BitVec.ofNat 64 r).toNat = a.toNat + r := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      have : r % 2 ^ 64 = r := Nat.mod_eq_of_lt (by omega)
      rw [this]
      exact Nat.mod_eq_of_lt (by omega)
    refine ⟨?_, by omega⟩
    apply BitVec.eq_of_toNat_eq
    rw [panByteAlign_toNat64, har]
    omega
  constructor
  · intro hweq r hr
    obtain ⟨hp₁, hm₁⟩ := hal_off addr₁ r hal₁ h1 hr
    obtain ⟨hp₂, hm₂⟩ := hal_off addr₂ r hal₂ h2 hr
    simp only [memByteAt, hp₁, hp₂, hweq, panGetByteHOL]
    change UInt8.ofNat ((memWordAt mem₂ addr₂).toNat /
        256 ^ (if be then 8 - 1 - (addr₁ + BitVec.ofNat 64 r).toNat % 8 else (addr₁ + BitVec.ofNat 64 r).toNat % 8) % 256) =
      UInt8.ofNat ((memWordAt mem₂ addr₂).toNat /
        256 ^ (if be then 8 - 1 - (addr₂ + BitVec.ofNat 64 r).toNat % 8 else (addr₂ + BitVec.ofNat 64 r).toNat % 8) % 256)
    rw [hm₁, hm₂]
  · intro hbytes
    apply BitVec.eq_of_toNat_eq
    apply nat_eq_of_digits_256_8 (memWordAt mem₁ addr₁).isLt (memWordAt mem₂ addr₂).isLt
    intro k hk
    let r := if be then 7 - k else k
    have hr : r < 8 := by cases be <;> dsimp [r] <;> omega
    have hidx : (if be then 8 - 1 - r else r) = k := by cases be <;> dsimp [r] <;> omega
    have hb := congrArg UInt8.toNat (hbytes r hr)
    obtain ⟨hp₁, hm₁⟩ := hal_off addr₁ r hal₁ h1 hr
    obtain ⟨hp₂, hm₂⟩ := hal_off addr₂ r hal₂ h2 hr
    simp only [memByteAt, hp₁, hp₂, panGetByteHOL] at hb
    change (UInt8.ofNat ((memWordAt mem₁ addr₁).toNat /
        256 ^ (if be then 8 - 1 - (addr₁ + BitVec.ofNat 64 r).toNat % 8 else (addr₁ + BitVec.ofNat 64 r).toNat % 8) % 256)).toNat =
      (UInt8.ofNat ((memWordAt mem₂ addr₂).toNat /
        256 ^ (if be then 8 - 1 - (addr₂ + BitVec.ofNat 64 r).toNat % 8 else (addr₂ + BitVec.ofNat 64 r).toNat % 8) % 256)).toNat at hb
    rw [hm₁, hm₂, hidx, UInt8.toNat_ofNat', UInt8.toNat_ofNat',
      Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide)),
      Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))] at hb
    exact hb

theorem panMemStore_bytes_same {mem : BitVec 64 → HolWordLab 64}
    {be : Bool} {dst src : BitVec 64}
    (hd8 : dst.toNat % 8 = 0) (hs8 : src.toNat % 8 = 0)
    (hd_lt : dst.toNat + 8 < 2 ^ 64) (hs_lt : src.toNat + 8 < 2 ^ 64) :
    let mem' := fun current => if current = dst then .word (memWordAt mem src) else mem current
    (∀ r : Nat, r < 8 →
      memByteAt mem' be (dst + BitVec.ofNat 64 r) = memByteAt mem be (src + BitVec.ofNat 64 r)) ∧
    (∀ addr' : BitVec 64, panByteAlignHOL addr' ≠ dst → memByteAt mem' be addr' = memByteAt mem be addr') := by
  dsimp only
  have hself : memWordAt (fun current => if current = dst then .word (memWordAt mem src) else mem current) dst =
      memWordAt mem src := by
    simp [memWordAt]
  refine ⟨(memWordAt_eq_iff_bytes hd8 hs8 hd_lt hs_lt).mp hself, fun addr' hne => ?_⟩
  exact panMemStore_getByte_disjoint hne

theorem eval_load_one_word {F : Type} {state : PanSemStateFiniteExact 64 F}
    {addrExp : ExpHOL 64} {addr : BitVec 64}
    (heval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) addrExp = some (.val (.word addr)))
    (hdom : state.memaddrs addr) :
    @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) (.load .one addrExp) =
      some (.val (.word (memWordAt state.memory addr))) := by
  simp only [evalHOLExact, isWfShapeExactHOL, ↓reduceIte, heval, memLoadHOLExact, hdom]
  cases hm : state.memory addr with
  | word w => simp [memWordAt, hm]

theorem eval_loadByte_word {F : Type} {state : PanSemStateFiniteExact 64 F}
    {addrExp : ExpHOL 64} {addr : BitVec 64}
    (heval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) addrExp = some (.val (.word addr)))
    (hdom : state.memaddrs (panByteAlignHOL addr)) :
    @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) (.loadByte addrExp) =
      some (.val (.word (BitVec.ofNat 64 (memByteAt state.memory state.be addr).toNat))) := by
  have hload := @panMemLoadByte_eq_memByteAt state.memory state.memaddrs
    (fun a => Classical.propDecidable (state.memaddrs a)) state.be addr hdom
  simp only [evalHOLExact, heval, Option.map]
  rw [hload]

/-! ### Stage 3c: Allocator, memcpy, memeq, keccak256, and htab_first_diff post-state lemmas -/

theorem alloc_bounds_general (p n : BitVec 64)
    (hp_le : p.toNat ≤ cMax.toNat)
    (hcmp1 : ¬ ((cMax - p).toNat < n.toNat))
    (hcmp2 : ¬ (cMax.toNat < ((p + (n + 7)) &&& ((0 : BitVec 64) - 8)).toNat)) :
    let q := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    p.toNat + n.toNat ≤ q.toNat ∧ q.toNat ≤ cMax.toNat ∧ q.toNat % 8 = 0 := by
  intro q
  have hcMax : cMax.toNat = 2952790016 := rfl
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by decide
  have hp_lt_264 : p.toNat < 2 ^ 64 := p.isLt
  have hn_lt_264 : n.toNat < 2 ^ 64 := n.isLt
  have hq_eq : q.toNat = (p + (n + 7)).toNat / 8 * 8 := and_neg8_toNat (p + (n + 7))
  have hq_le : q.toNat ≤ cMax.toNat := Nat.le_of_not_lt hcmp2
  have hq_mod : q.toNat % 8 = 0 := by omega
  have hsub : (cMax - p).toNat = cMax.toNat - p.toNat := by
    rw [BitVec.toNat_sub]; omega
  have hn_le : n.toNat ≤ cMax.toNat - p.toNat := by omega
  have h7 : (7 : BitVec 64).toNat = 7 := rfl
  have hn7 : (n + 7).toNat = n.toNat + 7 := by rw [BitVec.toNat_add, h7]; omega
  have hsum : (p + (n + 7)).toNat = p.toNat + n.toNat + 7 := by rw [BitVec.toNat_add, hn7]; omega
  exact ⟨by omega, hq_le, hq_mod⟩

theorem evaluate_alloc_body_general {F : Type}
    (state : PanSemStateFiniteExact 64 F) (p n : BitVec 64)
    (hcode : state.code = originalRuntimeCode)
    (hp_le : p.toNat ≤ cMax.toNat)
    (hp_lookup : state.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n))) :
    let out := evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_alloc)
    let q := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    ∀ retVal : ValueHOL 64, out.1 = some (.returned retVal) →
      retVal = .val (.word p) ∧
      out.2.globals = state.globals.update (ofString "heap_ptr", .val (.word q)) ∧
      out.2.memory = state.memory ∧
      p.toNat + n.toNat ≤ q.toNat ∧ q.toNat ≤ cMax.toNat ∧ q.toNat % 8 = 0 := by
  dsimp only
  have hbody_eq : sourceFnBody Guest.Software.guestFn_alloc =
      .dec (ofString "p") .one (.var .global (ofString "heap_ptr"))
        (.seq
          (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
              (.var .local (ofString "n")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1])
            .skip)
          (.dec (ofString "q") .one
            (.op .and [.op .add [.var .local (ofString "p"), .var .local (ofString "n"), .const 7],
              .op .sub [.const 0, .const 8]])
            (.seq
              (.ite (.cmp .lower (.const cMax) (.var .local (ofString "q")))
                (.call (some (none, none)) (ofString "trap_with") [.const 1])
                .skip)
              (.seq
                (.assign .global (ofString "heap_ptr") (.var .local (ofString "q")))
                (.return (.var .local (ofString "p"))))))) := rfl
  rw [hbody_eq, evaluateHOLFiniteState_dec_total]
  have hp_eval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a))
      (.var .global (ofString "heap_ptr")) = some (.val (.word p)) := hp_lookup
  dsimp only
  rw [hp_eval]
  have hsh_p : shapeEqHOL .one (shapeOfHOLExact (.val (.word p))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  dsimp only
  rw [if_pos hsh_p]
  dsimp only
  set pState := setVarHOLFinite (ofString "p") (.val (.word p)) state
  have hp_loc : pState.locals.lookup (ofString "p") = some (.val (.word p)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hn_loc : pState.locals.lookup (ofString "n") = some (.val (.word n)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn,
      show ofString "p" ≠ ofString "n" by decide]
  have hcode_p : pState.code = originalRuntimeCode := hcode
  rw [evaluateHOLFiniteState_seq_line780]
  have hev1 : @evalHOLExact 64 F _ pState.toExact
      (fun a => Classical.propDecidable (pState.memaddrs a))
      (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
        (.var .local (ofString "n"))) =
      some (.val (.word (if (cMax - p).toNat < n.toNat then 1 else 0))) := by
    simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
      Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
    rfl
  by_cases hcmp1 : (cMax - p).toNat < n.toNat
  · have hite1 : evaluateHOLFiniteState pState
        (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const 1])
          .skip) =
        evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 1]) := by
      rw [evaluateHOLFiniteState_ite, hev1, if_pos hcmp1]; simp
    rw [hite1]
    have hno_none := evaluate_call_trap_with_no_none pState 1 hcode_p
    have hno_ret := fun w => evaluate_call_trap_with_no_return pState 1 w hcode_p
    rcases htr : evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r1, s1⟩
    rw [htr] at hno_none hno_ret
    cases r1 with
    | none => exact absurd rfl hno_none
    | some r1' =>
      intro retVal hret
      exact False.elim (hno_ret retVal hret)
  · have hite1 : evaluateHOLFiniteState pState
        (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const 1])
          .skip) = (none, pState) := by
      rw [evaluateHOLFiniteState_ite, hev1, if_neg hcmp1]; simp [evaluateHOLFiniteState_skip]
    rw [hite1]
    dsimp only
    rw [evaluateHOLFiniteState_dec_total]
    let q : BitVec 64 := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    have hq_eval : @evalHOLExact 64 F _ pState.toExact
        (fun a => Classical.propDecidable (pState.memaddrs a))
        (.op .and [.op .add [.var .local (ofString "p"), .var .local (ofString "n"), .const 7],
          .op .sub [.const 0, .const 8]]) = some (.val (.word q)) := by
      simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
        wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
      exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word w))) (alloc_q_word_eq p n)
    dsimp only
    rw [hq_eval]
    have hsh_q : shapeEqHOL .one (shapeOfHOLExact (.val (.word q))) = true := by
      simp [shapeEqHOL, shapeOfHOLExact]
    dsimp only
    rw [if_pos hsh_q]
    dsimp only
    set qState := setVarHOLFinite (ofString "q") (.val (.word q)) pState
    have hq_loc : qState.locals.lookup (ofString "q") = some (.val (.word q)) := by
      simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hp_loc_q : qState.locals.lookup (ofString "p") = some (.val (.word p)) := by
      simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp_loc,
        show ofString "q" ≠ ofString "p" by decide]
    have hcode_q : qState.code = originalRuntimeCode := hcode
    rw [evaluateHOLFiniteState_seq_line780]
    have hev2 : @evalHOLExact 64 F _ qState.toExact
        (fun a => Classical.propDecidable (qState.memaddrs a))
        (.cmp .lower (.const cMax) (.var .local (ofString "q"))) =
        some (.val (.word (if cMax.toNat < q.toNat then 1 else 0))) := by
      simp only [evalHOLExact, hq_loc, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
    by_cases hcmp2 : cMax.toNat < q.toNat
    · have hite2 : evaluateHOLFiniteState qState
          (.ite (.cmp .lower (.const cMax) (.var .local (ofString "q")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1])
            .skip) =
          evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 1]) := by
        rw [evaluateHOLFiniteState_ite, hev2, if_pos hcmp2]; simp
      rw [hite2]
      have hno_none := evaluate_call_trap_with_no_none qState 1 hcode_q
      have hno_ret := fun w => evaluate_call_trap_with_no_return qState 1 w hcode_q
      rcases htr : evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r2, s2⟩
      rw [htr] at hno_none hno_ret
      cases r2 with
      | none => exact absurd rfl hno_none
      | some r2' =>
        intro retVal hret
        exact False.elim (hno_ret retVal hret)
    · have hite2 : evaluateHOLFiniteState qState
          (.ite (.cmp .lower (.const cMax) (.var .local (ofString "q")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1])
            .skip) = (none, qState) := by
        rw [evaluateHOLFiniteState_ite, hev2, if_neg hcmp2]; simp [evaluateHOLFiniteState_skip]
      rw [hite2]
      dsimp only
      have hp_g : qState.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) := hp_lookup
      have heval_end : evaluateHOLFiniteState qState
          (.seq (.assign .global (ofString "heap_ptr") (.var .local (ofString "q")))
            (.return (.var .local (ofString "p")))) =
          (some (.returned (.val (.word p))),
            emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word q)) qState)) := by
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
        simp [evalHOLExact, hq_loc, hp_loc_q, isValidValueHOLFinite, isValidValueHOLExact,
          lookupKvarHOLFinite, lookupKvarHOLExact, hp_g,
          shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite,
          evaluateHOLFiniteState_return, sizeOfShapeWithContextHOL]
      rw [heval_end]
      have hb := alloc_bounds_general p n hp_le hcmp1 hcmp2
      intro retVal hret
      injection hret with hr
      injection hr with hr'
      exact ⟨hr'.symm, rfl, rfl, hb⟩

theorem scratch_alloc_bounds_general (ptr frame size : BitVec 64)
    (hlo : frame.toNat ≤ ptr.toNat)
    (hcmp1 : ¬ ((ptr - frame).toNat < size.toNat))
    (hcmp2 : ¬ (((ptr - size) &&& ((0 : BitVec 64) - 8)).toNat < frame.toNat)) :
    let q := (ptr - size) &&& ((0 : BitVec 64) - 8)
    frame.toNat ≤ q.toNat ∧ q.toNat + size.toNat ≤ ptr.toNat ∧ q.toNat % 8 = 0 := by
  intro q
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by decide
  have hp : ptr.toNat < 2 ^ 64 := ptr.isLt
  have hf : frame.toNat < 2 ^ 64 := frame.isLt
  have hs : size.toNat < 2 ^ 64 := size.isLt
  have hsub_pf : (ptr - frame).toNat = ptr.toNat - frame.toNat := by
    rw [BitVec.toNat_sub]; omega
  have hsize_le : size.toNat ≤ ptr.toNat - frame.toNat := by omega
  have hsub_ps : (ptr - size).toNat = ptr.toNat - size.toNat := by
    rw [BitVec.toNat_sub]; omega
  have hq_eq : q.toNat = (ptr - size).toNat / 8 * 8 := and_neg8_toNat (ptr - size)
  exact ⟨Nat.le_of_not_lt hcmp2, by omega, by omega⟩

theorem evaluate_scratch_alloc_body_general {F : Type}
    (state : PanSemStateFiniteExact 64 F) (p frame n : BitVec 64)
    (hcode : state.code = originalRuntimeCode)
    (hlo : frame.toNat ≤ p.toNat)
    (hp_lookup : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word p)))
    (hf_lookup : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n))) :
    let out := evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_scratch_alloc)
    let q := (p - n) &&& ((0 : BitVec 64) - 8)
    ∀ retVal : ValueHOL 64, out.1 = some (.returned retVal) →
      retVal = .val (.word q) ∧
      out.2.globals = state.globals.update (ofString "scratch_ptr", .val (.word q)) ∧
      out.2.memory = state.memory ∧
      frame.toNat ≤ q.toNat ∧ q.toNat + n.toNat ≤ p.toNat ∧ q.toNat % 8 = 0 := by
  dsimp only
  have hbody_eq : sourceFnBody Guest.Software.guestFn_scratch_alloc =
      .dec (ofString "p") .one (.var .global (ofString "scratch_ptr"))
        (.seq
          (.ite (.cmp .lower (.op .sub [.var .local (ofString "p"), .var .global (ofString "frame_mem_ptr")])
              (.var .local (ofString "n")))
            (.call (some (none, none)) (ofString "trap_with") [.const (BitVec.ofNat 64 7)])
            .skip)
          (.dec (ofString "q") .one
            (.op .and [.op .sub [.var .local (ofString "p"), .var .local (ofString "n")],
              .op .sub [.const (BitVec.ofNat 64 0), .const (BitVec.ofNat 64 8)]])
            (.seq
              (.ite (.cmp .lower (.var .local (ofString "q")) (.var .global (ofString "frame_mem_ptr")))
                (.call (some (none, none)) (ofString "trap_with") [.const (BitVec.ofNat 64 7)])
                .skip)
              (.seq
                (.assign .global (ofString "scratch_ptr") (.var .local (ofString "q")))
                (.return (.var .local (ofString "q"))))))) := rfl
  rw [hbody_eq, evaluateHOLFiniteState_dec_total]
  have hp_eval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a))
      (.var .global (ofString "scratch_ptr")) = some (.val (.word p)) := hp_lookup
  dsimp only
  rw [hp_eval]
  have hsh_p : shapeEqHOL .one (shapeOfHOLExact (.val (.word p))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  dsimp only
  rw [if_pos hsh_p]
  dsimp only
  set pState := setVarHOLFinite (ofString "p") (.val (.word p)) state
  have hp_loc : pState.locals.lookup (ofString "p") = some (.val (.word p)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hn_loc : pState.locals.lookup (ofString "n") = some (.val (.word n)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn,
      show ofString "p" ≠ ofString "n" by decide]
  have hf_g : pState.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := hf_lookup
  have hcode_p : pState.code = originalRuntimeCode := hcode
  rw [evaluateHOLFiniteState_seq_line780]
  have hev1 : @evalHOLExact 64 F _ pState.toExact
      (fun a => Classical.propDecidable (pState.memaddrs a))
      (.cmp .lower (.op .sub [.var .local (ofString "p"), .var .global (ofString "frame_mem_ptr")])
        (.var .local (ofString "n"))) =
      some (.val (.word (if (p - frame).toNat < n.toNat then 1 else 0))) := by
    simp only [evalHOLExact, evalListHOLExact, hp_loc, hf_g, hn_loc,
      wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte,
      Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
  by_cases hcmp1 : (p - frame).toNat < n.toNat
  · have hite1 : evaluateHOLFiniteState pState
        (.ite (.cmp .lower (.op .sub [.var .local (ofString "p"), .var .global (ofString "frame_mem_ptr")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const (BitVec.ofNat 64 7)])
          .skip) =
        evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const (BitVec.ofNat 64 7)]) := by
      rw [evaluateHOLFiniteState_ite, hev1, if_pos hcmp1]; simp
    rw [hite1]
    have hno_none := evaluate_call_trap_with_no_none pState (BitVec.ofNat 64 7) hcode_p
    have hno_ret := fun w => evaluate_call_trap_with_no_return pState (BitVec.ofNat 64 7) w hcode_p
    rcases htr : evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const (BitVec.ofNat 64 7)]) with ⟨r1, s1⟩
    rw [htr] at hno_none hno_ret
    cases r1 with
    | none => exact absurd rfl hno_none
    | some r1' =>
      intro retVal hret
      exact False.elim (hno_ret retVal hret)
  · have hite1 : evaluateHOLFiniteState pState
        (.ite (.cmp .lower (.op .sub [.var .local (ofString "p"), .var .global (ofString "frame_mem_ptr")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const (BitVec.ofNat 64 7)])
          .skip) = (none, pState) := by
      rw [evaluateHOLFiniteState_ite, hev1, if_neg hcmp1]; simp [evaluateHOLFiniteState_skip]
    rw [hite1]
    dsimp only
    rw [evaluateHOLFiniteState_dec_total]
    let q : BitVec 64 := (p - n) &&& ((0 : BitVec 64) - 8)
    have hq_word : (p - n) &&& (BitVec.ofNat 64 0 - BitVec.ofNat 64 8 &&& ~~~0#64) = q := by
      have : (BitVec.ofNat 64 0 - BitVec.ofNat 64 8 &&& ~~~0#64) = ((0 : BitVec 64) - 8) := by decide
      rw [this]
    have hq_eval : @evalHOLExact 64 F _ pState.toExact
        (fun a => Classical.propDecidable (pState.memaddrs a))
        (.op .and [.op .sub [.var .local (ofString "p"), .var .local (ofString "n")],
          .op .sub [.const (BitVec.ofNat 64 0), .const (BitVec.ofNat 64 8)]]) = some (.val (.word q)) := by
      simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
        wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
      exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word w))) hq_word
    dsimp only
    rw [hq_eval]
    have hsh_q : shapeEqHOL .one (shapeOfHOLExact (.val (.word q))) = true := by
      simp [shapeEqHOL, shapeOfHOLExact]
    dsimp only
    rw [if_pos hsh_q]
    dsimp only
    set qState := setVarHOLFinite (ofString "q") (.val (.word q)) pState
    have hq_loc : qState.locals.lookup (ofString "q") = some (.val (.word q)) := by
      simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hf_g_q : qState.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := hf_lookup
    have hcode_q : qState.code = originalRuntimeCode := hcode
    rw [evaluateHOLFiniteState_seq_line780]
    have hev2 : @evalHOLExact 64 F _ qState.toExact
        (fun a => Classical.propDecidable (qState.memaddrs a))
        (.cmp .lower (.var .local (ofString "q")) (.var .global (ofString "frame_mem_ptr"))) =
        some (.val (.word (if q.toNat < frame.toNat then 1 else 0))) := by
      simp only [evalHOLExact, hq_loc, hf_g_q, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
    by_cases hcmp2 : q.toNat < frame.toNat
    · have hite2 : evaluateHOLFiniteState qState
          (.ite (.cmp .lower (.var .local (ofString "q")) (.var .global (ofString "frame_mem_ptr")))
            (.call (some (none, none)) (ofString "trap_with") [.const (BitVec.ofNat 64 7)])
            .skip) =
          evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const (BitVec.ofNat 64 7)]) := by
        rw [evaluateHOLFiniteState_ite, hev2, if_pos hcmp2]; simp
      rw [hite2]
      have hno_none := evaluate_call_trap_with_no_none qState (BitVec.ofNat 64 7) hcode_q
      have hno_ret := fun w => evaluate_call_trap_with_no_return qState (BitVec.ofNat 64 7) w hcode_q
      rcases htr : evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const (BitVec.ofNat 64 7)]) with ⟨r2, s2⟩
      rw [htr] at hno_none hno_ret
      cases r2 with
      | none => exact absurd rfl hno_none
      | some r2' =>
        intro retVal hret
        exact False.elim (hno_ret retVal hret)
    · have hite2 : evaluateHOLFiniteState qState
          (.ite (.cmp .lower (.var .local (ofString "q")) (.var .global (ofString "frame_mem_ptr")))
            (.call (some (none, none)) (ofString "trap_with") [.const (BitVec.ofNat 64 7)])
            .skip) = (none, qState) := by
        rw [evaluateHOLFiniteState_ite, hev2, if_neg hcmp2]; simp [evaluateHOLFiniteState_skip]
      rw [hite2]
      dsimp only
      have hp_g : qState.globals.lookup (ofString "scratch_ptr") = some (.val (.word p)) := hp_lookup
      have heval_end : evaluateHOLFiniteState qState
          (.seq (.assign .global (ofString "scratch_ptr") (.var .local (ofString "q")))
            (.return (.var .local (ofString "q")))) =
          (some (.returned (.val (.word q))),
            emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "scratch_ptr") (.val (.word q)) qState)) := by
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
        simp [evalHOLExact, hq_loc, isValidValueHOLFinite, isValidValueHOLExact,
          lookupKvarHOLFinite, lookupKvarHOLExact, hp_g,
          shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite,
          evaluateHOLFiniteState_return, sizeOfShapeWithContextHOL]
      rw [heval_end]
      have hb := scratch_alloc_bounds_general p frame n hlo hcmp1 hcmp2
      intro retVal hret
      injection hret with hr
      injection hr with hr'
      exact ⟨hr'.symm, rfl, rfl, hb⟩

theorem evaluate_store_word {F : Type} {state : PanSemStateFiniteExact 64 F}
    {dstExp srcExp : ExpHOL 64} {addr val : BitVec 64}
    (hdst : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) dstExp = some (.val (.word addr)))
    (hsrc : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) srcExp = some (.val (.word val)))
    (hdom : state.memaddrs addr) :
    evaluateHOLFiniteState state (.store dstExp srcExp) =
      (none, { state with memory := fun current => if current = addr then .word val else state.memory current }) := by
  rw [evaluateHOLFiniteState_store]
  simp only [hdst, hsrc, flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom, ↓reduceIte]

theorem evaluate_storeByte_word {F : Type} {state : PanSemStateFiniteExact 64 F}
    {dstExp srcExp : ExpHOL 64} {addr val : BitVec 64}
    (hdst : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) dstExp = some (.val (.word addr)))
    (hsrc : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) srcExp = some (.val (.word val)))
    (hdom : state.memaddrs (panByteAlignHOL addr)) :
    ∃ mem',
      evaluateHOLFiniteState state (.storeByte dstExp srcExp) = (none, { state with memory := mem' }) ∧
      memByteAt mem' state.be addr = UInt8.ofNat (val.toNat % 256) ∧
      (∀ addr' : BitVec 64, addr' ≠ addr → memByteAt mem' state.be addr' = memByteAt state.memory state.be addr') ∧
      (∀ c : BitVec 64, c ≠ panByteAlignHOL addr → mem' c = state.memory c) := by
  rw [evaluateHOLFiniteState_storeByte]
  simp only [hdst, hsrc]
  cases hcell : state.memory (panByteAlignHOL addr) with
  | word cell =>
    have hst : @panMemStoreByteWord8HOL 64 _ state.memory state.memaddrs
        (fun a => Classical.propDecidable (state.memaddrs a)) state.be addr
        (BitVec.ofNat 8 val.toNat) =
        some (fun current => if current = panByteAlignHOL addr
          then .word (panSetByteHOL addr (BitVec.ofNat 64 (BitVec.ofNat 8 val.toNat).toNat) cell state.be)
          else state.memory current) := by
      simp [panMemStoreByteWord8HOL, hcell, hdom]
    have hb_eq : BitVec.ofNat 8 val.toNat = BitVec.ofNat 8 (UInt8.ofNat (val.toNat % 256)).toNat := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_ofNat, UInt8.toNat_ofNat']
    have hst' : @panMemStoreByteWord8HOL 64 _ state.memory state.memaddrs
        (fun a => Classical.propDecidable (state.memaddrs a)) state.be addr
        (BitVec.ofNat 8 (UInt8.ofNat (val.toNat % 256)).toNat) =
        some (fun current => if current = panByteAlignHOL addr
          then .word (panSetByteHOL addr (BitVec.ofNat 64 (BitVec.ofNat 8 val.toNat).toNat) cell state.be)
          else state.memory current) := by
      rw [← hb_eq]
      exact hst
    obtain ⟨hsame, hdiff⟩ := @panMemStoreByte_getByte_same state.memory state.memaddrs
      (fun a => Classical.propDecidable (state.memaddrs a)) state.be addr
      (UInt8.ofNat (val.toNat % 256)) _ hst'
    refine ⟨_, ?_, hsame, hdiff, fun c hc => if_neg hc⟩
    rw [hst]

def localOnlyNoCalls : ProgHOL 64 → Bool
  | .dec _ _ _ body => localOnlyNoCalls body
  | .seq first second => localOnlyNoCalls first && localOnlyNoCalls second
  | .ite _ yes no => localOnlyNoCalls yes && localOnlyNoCalls no
  | .while _ body => localOnlyNoCalls body
  | .assign .local _ _ => true
  | .store _ _ | .storeByte _ _ => true
  | .skip | .break | .continue | .annot _ _ | .raise _ _ | .return _ => true
  | .primitive _ _ _ => true
  | _ => false

theorem evaluate_localOnlyNoCalls_globals {F : Type} (p : ProgHOL 64)
    (hp : localOnlyNoCalls p = true) (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state p).2.globals = state.globals := by
  cases shape : p with
  | skip => rw [evaluateHOLFiniteState_skip]
  | «break» => rw [evaluateHOLFiniteState_break]
  | «continue» => rw [evaluateHOLFiniteState_continue]
  | annot _ _ => rw [evaluateHOLFiniteState_annot]
  | raise _ _ =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> rfl
    · rfl
  | «return» _ =>
    rw [evaluateHOLFiniteState_return]
    split
    · rfl
    · split <;> rfl
  | primitive _ _ _ =>
    rw [evaluateHOLFiniteState_primitive]
    split
    · rfl
    · split
      · rfl
      · split <;> rfl
  | assign kind name expr =>
    cases kind with
    | global => simp [shape, localOnlyNoCalls] at hp
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · rfl
      · split <;> rfl
  | store _ _ =>
    rw [evaluateHOLFiniteState_store]
    split
    · split
      · split <;> rfl
      · rfl
    · rfl
  | storeByte _ _ =>
    rw [evaluateHOLFiniteState_storeByte]
    split
    · split
      · split <;> rfl
      · rfl
    · rfl
  | dec name sh init body =>
    have hb : localOnlyNoCalls body = true := by simpa [shape, localOnlyNoCalls] using hp
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · rfl
    · rename_i val _
      split
      · have ih := evaluate_localOnlyNoCalls_globals body hb (setVarHOLFinite name val state)
        rcases hbr : evaluateHOLFiniteState (setVarHOLFinite name val state) body with ⟨r, s'⟩
        rw [hbr] at ih
        exact ih
      · rfl
  | seq first second =>
    have h12 : localOnlyNoCalls first = true ∧ localOnlyNoCalls second = true := by
      simpa [shape, localOnlyNoCalls, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_seq_line780]
    have ih1 := evaluate_localOnlyNoCalls_globals first h12.1 state
    rcases hr1 : evaluateHOLFiniteState state first with ⟨r1, mid⟩
    rw [hr1] at ih1
    dsimp only at ih1 ⊢
    have hle1 : mid.clock ≤ state.clock := by
      have := evaluateHOLFiniteState_clock_le state first
      rw [hr1] at this
      exact this
    cases r1 with
    | none =>
      dsimp only
      have ih2 := evaluate_localOnlyNoCalls_globals second h12.2 mid
      exact ih2.trans ih1
    | some _ => exact ih1
  | ite cond yes no =>
    have h12 : localOnlyNoCalls yes = true ∧ localOnlyNoCalls no = true := by
      simpa [shape, localOnlyNoCalls, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_localOnlyNoCalls_globals no h12.2 state
      · exact evaluate_localOnlyNoCalls_globals yes h12.1 state
    · rfl
  | «while» cond body =>
    have hb : localOnlyNoCalls body = true := by simpa [shape, localOnlyNoCalls] using hp
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · rfl
        · rename_i nonzero
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have ih1 := evaluate_localOnlyNoCalls_globals body hb (decClockHOLFinite state)
          have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite state) body with ⟨r1, mid⟩
          rw [hbr] at ih1 hrem
          dsimp only at ih1 hrem
          have hlt : mid.clock < state.clock := by
            change mid.clock ≤ state.clock - 1 at hrem; omega
          cases r1 with
          | none =>
            have ih2 := evaluate_localOnlyNoCalls_globals (.while cond body) (by simpa [localOnlyNoCalls] using hb) mid
            exact ih2.trans ih1
          | some res =>
            cases res with
            | «continue» =>
              have ih2 := evaluate_localOnlyNoCalls_globals (.while cond body) (by simpa [localOnlyNoCalls] using hb) mid
              exact ih2.trans ih1
            | _ => exact ih1
      · rfl
    · rfl
  | _ => simp [shape, localOnlyNoCalls] at hp
termination_by (state.clock, sizeOf p)
decreasing_by
  all_goals
    subst shape
    simp_wf
    try simp only [decClockHOLFinite, setVarHOLFinite]
    omega

theorem evaluate_call_pure_globals {F : Type}
    (state : PanSemStateFiniteExact 64 F) (fn : MlS) (args : List (ExpHOL 64))
    {params : List (MlS × ShapeHOL)} {body : ProgHOL 64} {retSh : ShapeHOL}
    (hcode : state.code = originalRuntimeCode)
    (hlookup : originalRuntimeCode.lookup fn = some (params, body, retSh))
    (hpure : localOnlyNoCalls body = true) :
    (evaluateHOLFiniteState state (.call (some (none, none)) fn args)).2.globals = state.globals := by
  rw [evaluateHOLFiniteState_call]
  split
  · rfl
  · rename_i vs _
    split
    · rfl
    · rename_i fBody callee rs hfound
      split
      · rfl
      · have hbody_eq : fBody = body := by
          rw [hcode] at hfound
          exact lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup fn _ _ fBody _ rs vs callee hlookup hfound
        have hg := evaluate_localOnlyNoCalls_globals fBody (by rw [hbody_eq]; exact hpure)
          (callEntryStateHOLFinite state callee)
        rcases hran : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) fBody with ⟨res, post⟩
        rw [hran] at hg
        dsimp only at hg ⊢
        cases res with
        | none => exact hg
        | some r =>
          cases r with
          | returned val =>
            dsimp only
            split <;> exact hg
          | _ => exact hg

theorem lookup_keccak_f1600 :
    originalRuntimeCode.lookup (ofString "keccak_f1600") =
      some ([(ofString "stp", .one)],
        sourceFnBody Guest.Software.guestFn_keccak_f1600, .one) :=
  lookup_of_guestAst_getElem 101 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_keccak_f1600) rfl

theorem lookup_keccak_absorb_block :
    originalRuntimeCode.lookup (ofString "keccak_absorb_block") =
      some ([(ofString "stp", .one), (ofString "blk", .one)],
        sourceFnBody Guest.Software.guestFn_keccak_absorb_block, .one) :=
  lookup_of_guestAst_getElem 102 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_keccak_absorb_block) rfl

def ByteRangeDisjoint (a : BitVec 64) (na : Nat) (b : BitVec 64) (nb : Nat) : Prop :=
  a.toNat + na ≤ b.toNat ∨ b.toNat + nb ≤ a.toNat

def MemOutsideUnchanged (mem' mem : BitVec 64 → HolWordLab 64) (dst : BitVec 64) (len : Nat) : Prop :=
  ∀ c : BitVec 64, c.toNat % 8 = 0 →
    (c.toNat + 8 ≤ dst.toNat ∨ dst.toNat + len ≤ c.toNat) → mem' c = mem c

theorem memOutsideUnchanged_refl (mem : BitVec 64 → HolWordLab 64) (dst : BitVec 64) (len : Nat) :
    MemOutsideUnchanged mem mem dst len :=
  fun _ _ _ => rfl

theorem memOutsideUnchanged_trans {m1 m2 m3 : BitVec 64 → HolWordLab 64} {dst : BitVec 64} {len : Nat}
    (h12 : MemOutsideUnchanged m2 m1 dst len) (h23 : MemOutsideUnchanged m3 m2 dst len) :
    MemOutsideUnchanged m3 m1 dst len :=
  fun c hc hdisj => (h23 c hc hdisj).trans (h12 c hc hdisj)

theorem memOutsideUnchanged_mono {m1 m2 : BitVec 64 → HolWordLab 64}
    {dst1 dst2 : BitVec 64} {len1 len2 : Nat}
    (h12 : MemOutsideUnchanged m2 m1 dst1 len1)
    (hlo : dst2.toNat ≤ dst1.toNat) (hhi : dst1.toNat + len1 ≤ dst2.toNat + len2) :
    MemOutsideUnchanged m2 m1 dst2 len2 := by
  intro c hc hdisj
  apply h12 c hc
  rcases hdisj with h | h <;> omega

theorem memOutsideUnchanged_byte {m2 m1 : BitVec 64 → HolWordLab 64}
    {be : Bool} {dst : BitVec 64} {len : Nat} {addr : BitVec 64}
    (hout : MemOutsideUnchanged m2 m1 dst len)
    (hal : dst.toNat % 8 = 0 ∨ (addr.toNat + 8 ≤ dst.toNat ∨ dst.toNat + len + 8 ≤ addr.toNat))
    (hdisj : addr.toNat < dst.toNat ∨ dst.toNat + len ≤ addr.toNat) :
    memByteAt m2 be addr = memByteAt m1 be addr := by
  have hp_mod : (panByteAlignHOL addr).toNat % 8 = 0 := by
    rw [panByteAlign_toNat64]; omega
  have hp_eq : (panByteAlignHOL addr).toNat = addr.toNat / 8 * 8 := panByteAlign_toNat64 addr
  have hcell : m2 (panByteAlignHOL addr) = m1 (panByteAlignHOL addr) := by
    apply hout _ hp_mod
    rcases hal with hd8 | hfar
    · rcases hdisj with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    · rcases hfar with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
  simp [memByteAt, memWordAt, hcell]

theorem memOutsideUnchanged_aligned_byte {m2 m1 : BitVec 64 → HolWordLab 64}
    {be : Bool} {dst : BitVec 64} {len : Nat} {addr : BitVec 64}
    (hout : MemOutsideUnchanged m2 m1 dst len)
    (hd8 : dst.toNat % 8 = 0) (hlen8 : len % 8 = 0)
    (hdisj : addr.toNat < dst.toNat ∨ dst.toNat + len ≤ addr.toNat) :
    memByteAt m2 be addr = memByteAt m1 be addr := by
  have hp_mod : (panByteAlignHOL addr).toNat % 8 = 0 := by
    rw [panByteAlign_toNat64]; omega
  have hp_eq : (panByteAlignHOL addr).toNat = addr.toNat / 8 * 8 := panByteAlign_toNat64 addr
  have hcell : m2 (panByteAlignHOL addr) = m1 (panByteAlignHOL addr) := by
    apply hout _ hp_mod
    rcases hdisj with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  simp [memByteAt, memWordAt, hcell]

theorem writesOnlyRange_word {F : Type} {state : PanSemStateFiniteExact 64 F}
    {dstExp srcExp : ExpHOL 64} {dst addr : BitVec 64} {len : Nat}
    (hdst : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) dstExp = some (.val (.word addr)))
    (hin : dst.toNat ≤ addr.toNat ∧ addr.toNat + 8 ≤ dst.toNat + len) :
    let out := evaluateHOLFiniteState state (.store dstExp srcExp)
    MemOutsideUnchanged out.2.memory state.memory dst len ∧ out.2.globals = state.globals := by
  dsimp only
  rw [evaluateHOLFiniteState_store, hdst]
  dsimp only
  split
  · split
    · rename_i mem' hst
      refine ⟨fun c _ hdisj => ?_, rfl⟩
      simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL] at hst
      split at hst
      · injection hst with hm
        subst hm
        have hne : c ≠ addr := by intro heq; subst heq; omega
        exact if_neg hne
      · cases hst
    · exact ⟨memOutsideUnchanged_refl _ _ _, rfl⟩
  · exact ⟨memOutsideUnchanged_refl _ _ _, rfl⟩

theorem writesOnlyRange_byte {F : Type} {state : PanSemStateFiniteExact 64 F}
    {dstExp srcExp : ExpHOL 64} {dst addr : BitVec 64} {len : Nat}
    (hdst : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) dstExp = some (.val (.word addr)))
    (hin : dst.toNat ≤ addr.toNat ∧ addr.toNat < dst.toNat + len) :
    let out := evaluateHOLFiniteState state (.storeByte dstExp srcExp)
    MemOutsideUnchanged out.2.memory state.memory dst len ∧ out.2.globals = state.globals := by
  dsimp only
  rw [evaluateHOLFiniteState_storeByte, hdst]
  dsimp only
  split
  · split
    · rename_i mem' hst
      refine ⟨fun c hc hdisj => ?_, rfl⟩
      unfold panMemStoreByteWord8HOL at hst
      dsimp only at hst
      split at hst
      · injection hst with hm
        subst hm
        have hp_eq : (panByteAlignHOL addr).toNat = addr.toNat / 8 * 8 := panByteAlign_toNat64 addr
        have hne : c ≠ panByteAlignHOL addr := by
          intro heq; subst heq; omega
        exact if_neg hne
      · cases hst
    · exact ⟨memOutsideUnchanged_refl _ _ _, rfl⟩
  · exact ⟨memOutsideUnchanged_refl _ _ _, rfl⟩

def MemPreservesPred (P : BitVec 64 → Bool) (mem' mem : BitVec 64 → HolWordLab 64) : Prop :=
  ∀ c : BitVec 64, P c = true → mem' c = mem c

theorem memPreservesPred_refl (P : BitVec 64 → Bool) (mem : BitVec 64 → HolWordLab 64) :
    MemPreservesPred P mem mem :=
  fun _ _ => rfl

theorem memPreservesPred_trans {P : BitVec 64 → Bool} {m1 m2 m3 : BitVec 64 → HolWordLab 64}
    (h12 : MemPreservesPred P m2 m1) (h23 : MemPreservesPred P m3 m2) :
    MemPreservesPred P m3 m1 :=
  fun c hc => (h23 c hc).trans (h12 c hc)

private theorem writesOnlyRange_seq {F : Type} {state : PanSemStateFiniteExact 64 F}
    {p1 p2 : ProgHOL 64} {dst : BitVec 64} {len : Nat}
    (h1 : MemOutsideUnchanged (evaluateHOLFiniteState state p1).2.memory state.memory dst len ∧
          (evaluateHOLFiniteState state p1).2.globals = state.globals)
    (h2 : ∀ mid, evaluateHOLFiniteState state p1 = (none, mid) →
          MemOutsideUnchanged (evaluateHOLFiniteState mid p2).2.memory mid.memory dst len ∧
          (evaluateHOLFiniteState mid p2).2.globals = mid.globals) :
    let out := evaluateHOLFiniteState state (.seq p1 p2)
    MemOutsideUnchanged out.2.memory state.memory dst len ∧ out.2.globals = state.globals := by
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hr1 : evaluateHOLFiniteState state p1 with ⟨r1, mid⟩
  rw [hr1] at h1
  dsimp only at h1 ⊢
  cases r1 with
  | none =>
    dsimp only
    obtain ⟨hm2, hg2⟩ := h2 mid hr1
    exact ⟨memOutsideUnchanged_trans h1.1 hm2, hg2.trans h1.2⟩
  | some _ => exact h1

private def storeAddrBoundedConst (dstVar : MlS) (bound : Nat) (e : ExpHOL 64) (off : Nat) : Bool :=
  match e with
  | .var vk v =>
    match vk with
    | .local => (v == dstVar) && decide (off ≤ bound)
    | .global => false
  | .op bop es =>
    match bop with
    | .add =>
      match es with
      | e1 :: e2 :: [] =>
        match e1, e2 with
        | .var .local v, .const k => (v == dstVar) && decide (k.toNat + off ≤ bound)
        | _, _ => false
      | _ => false
    | _ => false
  | _ => false

private def checkConstStores (dstVar : MlS) (bound : Nat) : ProgHOL 64 → Bool
  | .skip | .return _ | .raise _ _ | .break | .continue | .annot _ _
  | .primitive _ _ _ => true
  | .assign vk _ _ =>
    match vk with
    | .local => true
    | .global => false
  | .store addr _ => storeAddrBoundedConst dstVar bound addr 8
  | .storeByte addr _ => storeAddrBoundedConst dstVar bound addr 1
  | .seq p1 p2 | .ite _ p1 p2 => checkConstStores dstVar bound p1 && checkConstStores dstVar bound p2
  | .dec v _ _ body => (v != dstVar) && checkConstStores dstVar bound body
  | .while _ body => checkConstStores dstVar bound body
  | _ => false

private theorem checkConstStores_skip (dstVar : MlS) (bound : Nat) :
    checkConstStores dstVar bound .skip = true := rfl

private theorem writesOnlyRange_constBase {F : Type}
    (dstVar : MlS) (bound : Nat) (p : ProgHOL 64)
    (hlocals : localOnlyNoCalls p = true)
    (hav : avoidsLocal dstVar p = true)
    (hstores : checkConstStores dstVar bound p = true)
    (state : PanSemStateFiniteExact 64 F) (dst : BitVec 64)
    (hsmall : dst.toNat + bound < 2 ^ 64)
    (hdst : state.locals.lookup dstVar = some (.val (.word dst))) :
    MemOutsideUnchanged (evaluateHOLFiniteState state p).2.memory state.memory dst bound := by
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by decide
  cases shape : p with
  | skip => simp [evaluateHOLFiniteState_skip, memOutsideUnchanged_refl]
  | «return» e =>
    rw [evaluateHOLFiniteState_return]
    split
    · exact memOutsideUnchanged_refl _ _ _
    · split <;> exact memOutsideUnchanged_refl _ _ _
  | raise ex e =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> exact memOutsideUnchanged_refl _ _ _
    · exact memOutsideUnchanged_refl _ _ _
  | «break» => simp [evaluateHOLFiniteState_break, memOutsideUnchanged_refl]
  | «continue» => simp [evaluateHOLFiniteState_continue, memOutsideUnchanged_refl]
  | annot a b => simp [evaluateHOLFiniteState_annot, memOutsideUnchanged_refl]
  | primitive _ _ _ =>
    rw [evaluateHOLFiniteState_primitive]
    split
    · exact memOutsideUnchanged_refl _ _ _
    · split
      · exact memOutsideUnchanged_refl _ _ _
      · split <;> exact memOutsideUnchanged_refl _ _ _
  | assign vk v rhs =>
    cases vk with
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · exact memOutsideUnchanged_refl _ _ _
      · split <;> exact memOutsideUnchanged_refl _ _ _
    | global => simp [shape, localOnlyNoCalls] at hlocals
  | store addr src =>
    have hs : storeAddrBoundedConst dstVar bound addr 8 = true := by
      simpa [shape, checkConstStores] using hstores
    cases addr with
    | var vk v =>
      cases vk with
      | «local» =>
        have hv : v = dstVar ∧ 8 ≤ bound := by
          simpa [storeAddrBoundedConst, Bool.and_eq_true, beq_iff_eq] using hs
        rcases hv with ⟨rfl, h8b⟩
        have hev : @evalHOLExact 64 F _ state.toExact
            (fun a => Classical.propDecidable (state.memaddrs a)) (.var .local v) =
            some (.val (.word dst)) := by
          simp [evalHOLExact, hdst]
        exact (writesOnlyRange_word (dst := dst) (len := bound) hev ⟨Nat.le_refl _, by omega⟩).1
      | global => cases hs
    | op bop es =>
      cases bop <;> try cases hs
      rcases es with _ | ⟨e1, _ | ⟨e2, _ | _⟩⟩ <;> try cases hs
      cases e1 with
      | var vk1 v1 =>
        cases vk1 <;> try cases hs
        cases e2 with
        | const k =>
          have hk : v1 = dstVar ∧ k.toNat + 8 ≤ bound := by
            simpa [storeAddrBoundedConst, Bool.and_eq_true, beq_iff_eq] using hs
          rcases hk with ⟨rfl, hkb⟩
          have hev : @evalHOLExact 64 F _ state.toExact
              (fun a => Classical.propDecidable (state.memaddrs a))
              (.op .add [.var .local v1, .const k]) = some (.val (.word (dst + k))) := by
            simp [evalHOLExact, evalListHOLExact, hdst, valueIsWord, valueWord, wordOpHOL, wordOp]
          have hadd : (dst + k).toNat = dst.toNat + k.toNat := by
            rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
          exact (writesOnlyRange_word (dst := dst) (len := bound) hev ⟨by omega, by omega⟩).1
        | _ => cases hs
      | _ => cases hs
    | _ => cases hs
  | storeByte addr src =>
    have hs : storeAddrBoundedConst dstVar bound addr 1 = true := by
      simpa [shape, checkConstStores] using hstores
    cases addr with
    | var vk v =>
      cases vk with
      | «local» =>
        have hv : v = dstVar ∧ 1 ≤ bound := by
          simpa [storeAddrBoundedConst, Bool.and_eq_true, beq_iff_eq] using hs
        rcases hv with ⟨rfl, h1b⟩
        have hev : @evalHOLExact 64 F _ state.toExact
            (fun a => Classical.propDecidable (state.memaddrs a)) (.var .local v) =
            some (.val (.word dst)) := by
          simp [evalHOLExact, hdst]
        exact (writesOnlyRange_byte (dst := dst) (len := bound) hev ⟨Nat.le_refl _, by omega⟩).1
      | global => cases hs
    | op bop es =>
      cases bop <;> try cases hs
      rcases es with _ | ⟨e1, _ | ⟨e2, _ | _⟩⟩ <;> try cases hs
      cases e1 with
      | var vk1 v1 =>
        cases vk1 <;> try cases hs
        cases e2 with
        | const k =>
          have hk : v1 = dstVar ∧ k.toNat < bound := by
            simpa [storeAddrBoundedConst, Bool.and_eq_true, beq_iff_eq] using hs
          rcases hk with ⟨rfl, hkb⟩
          have hev : @evalHOLExact 64 F _ state.toExact
              (fun a => Classical.propDecidable (state.memaddrs a))
              (.op .add [.var .local v1, .const k]) = some (.val (.word (dst + k))) := by
            simp [evalHOLExact, evalListHOLExact, hdst, valueIsWord, valueWord, wordOpHOL, wordOp]
          have hadd : (dst + k).toNat = dst.toNat + k.toNat := by
            rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
          exact (writesOnlyRange_byte (dst := dst) (len := bound) hev ⟨by omega, by omega⟩).1
        | _ => cases hs
      | _ => cases hs
    | _ => cases hs
  | seq p1 p2 =>
    have hl : localOnlyNoCalls p1 = true ∧ localOnlyNoCalls p2 = true := by
      simpa [shape, localOnlyNoCalls, Bool.and_eq_true] using hlocals
    have ha : avoidsLocal dstVar p1 = true ∧ avoidsLocal dstVar p2 = true := by
      simpa [shape, avoidsLocal, Bool.and_eq_true] using hav
    have hs : checkConstStores dstVar bound p1 = true ∧ checkConstStores dstVar bound p2 = true := by
      simpa [shape, checkConstStores, Bool.and_eq_true] using hstores
    have hfd := evaluate_avoidsLocal_flowing dstVar p1 ha.1 state
    have m1 := writesOnlyRange_constBase dstVar bound p1 hl.1 ha.1 hs.1 state dst hsmall hdst
    rw [evaluateHOLFiniteState_seq_line780]
    rcases hr1 : evaluateHOLFiniteState state p1 with ⟨r1, mid⟩
    rw [hr1] at hfd m1
    dsimp only at hfd m1 ⊢
    have hle1 : mid.clock ≤ state.clock := by
      have := evaluateHOLFiniteState_clock_le state p1
      rw [hr1] at this
      exact this
    cases r1 with
    | none =>
      dsimp only
      have hmid_dst : mid.locals.lookup dstVar = some (.val (.word dst)) := (hfd (Or.inl rfl)).trans hdst
      exact memOutsideUnchanged_trans m1 (writesOnlyRange_constBase dstVar bound p2 hl.2 ha.2 hs.2 mid dst hsmall hmid_dst)
    | some _ => exact m1
  | ite cond p1 p2 =>
    have hl : localOnlyNoCalls p1 = true ∧ localOnlyNoCalls p2 = true := by
      simpa [shape, localOnlyNoCalls, Bool.and_eq_true] using hlocals
    have ha : avoidsLocal dstVar p1 = true ∧ avoidsLocal dstVar p2 = true := by
      simpa [shape, avoidsLocal, Bool.and_eq_true] using hav
    have hs : checkConstStores dstVar bound p1 = true ∧ checkConstStores dstVar bound p2 = true := by
      simpa [shape, checkConstStores, Bool.and_eq_true] using hstores
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact writesOnlyRange_constBase dstVar bound p2 hl.2 ha.2 hs.2 state dst hsmall hdst
      · exact writesOnlyRange_constBase dstVar bound p1 hl.1 ha.1 hs.1 state dst hsmall hdst
    · exact memOutsideUnchanged_refl _ _ _
  | dec v sh init body =>
    have hl : localOnlyNoCalls body = true := by simpa [shape, localOnlyNoCalls] using hlocals
    have hs : v ≠ dstVar ∧ checkConstStores dstVar bound body = true := by
      simpa [shape, checkConstStores, Bool.and_eq_true, bne_iff_ne] using hstores
    have ha_body : avoidsLocal dstVar body = true := by
      have hor : v = dstVar ∨ avoidsLocal dstVar body = true := by
        simpa [shape, avoidsLocal, Bool.or_eq_true, beq_iff_eq] using hav
      exact hor.resolve_left hs.1
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · exact memOutsideUnchanged_refl _ _ _
    · rename_i val _
      split
      · have hdst' : (setVarHOLFinite v val state).locals.lookup dstVar = some (.val (.word dst)) := by
          simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs.1, hdst]
        have ih := writesOnlyRange_constBase dstVar bound body hl ha_body hs.2 (setVarHOLFinite v val state) dst hsmall hdst'
        rcases hbr : evaluateHOLFiniteState (setVarHOLFinite v val state) body with ⟨r, s'⟩
        rw [hbr] at ih
        exact ih
      · exact memOutsideUnchanged_refl _ _ _
  | «while» cond body =>
    have hl : localOnlyNoCalls body = true := by simpa [shape, localOnlyNoCalls] using hlocals
    have ha : avoidsLocal dstVar body = true := by simpa [shape, avoidsLocal] using hav
    have hs : checkConstStores dstVar bound body = true := by simpa [shape, checkConstStores] using hstores
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · exact memOutsideUnchanged_refl _ _ _
        · rename_i nonzero
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have hcle := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body
          have hfd := evaluate_avoidsLocal_flowing dstVar body ha (decClockHOLFinite state)
          have m1 := writesOnlyRange_constBase dstVar bound body hl ha hs (decClockHOLFinite state) dst hsmall hdst
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite state) body with ⟨rb, mid⟩
          rw [hbr] at hcle hfd m1
          dsimp only at hfd m1
          have hlt_clk : mid.clock < state.clock := by
            change mid.clock ≤ state.clock - 1 at hcle; omega
          cases rb with
          | none =>
            have hmid_dst : mid.locals.lookup dstVar = some (.val (.word dst)) :=
              (hfd (Or.inl rfl)).trans hdst
            exact memOutsideUnchanged_trans m1 (writesOnlyRange_constBase dstVar bound (.while cond body)
              (by simpa [localOnlyNoCalls] using hl) (by simpa [avoidsLocal] using ha)
              (by simpa [checkConstStores] using hs) mid dst hsmall hmid_dst)
          | some r' =>
            cases r' with
            | «continue» =>
              have hmid_dst : mid.locals.lookup dstVar = some (.val (.word dst)) :=
                (hfd (Or.inr (Or.inr rfl))).trans hdst
              exact memOutsideUnchanged_trans m1 (writesOnlyRange_constBase dstVar bound (.while cond body)
                (by simpa [localOnlyNoCalls] using hl) (by simpa [avoidsLocal] using ha)
                (by simpa [checkConstStores] using hs) mid dst hsmall hmid_dst)
            | _ => exact m1
      · exact memOutsideUnchanged_refl _ _ _
    · exact memOutsideUnchanged_refl _ _ _
  | _ => simp [shape, localOnlyNoCalls] at hlocals
termination_by (state.clock, sizeOf p)
decreasing_by
  all_goals
    subst shape
    simp_wf
    try simp only [decClockHOLFinite, setVarHOLFinite]
    omega

private theorem memOutsideUnchanged_call_keccak_f1600 {F : Type}
    (state : PanSemStateFiniteExact 64 F) (stpExp : ExpHOL 64) (stp : BitVec 64)
    (hcode : state.code = originalRuntimeCode)
    (hstp_small : stp.toNat + 200 < 2 ^ 64)
    (hstp : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) stpExp = some (.val (.word stp))) :
    let out := evaluateHOLFiniteState state (.call (some (none, none)) (ofString "keccak_f1600") [stpExp])
    MemOutsideUnchanged out.2.memory state.memory stp 200 ∧ out.2.globals = state.globals := by
  dsimp only
  have hglob := evaluate_call_pure_globals state (ofString "keccak_f1600") [stpExp]
    hcode lookup_keccak_f1600 (by decide)
  refine ⟨?_, hglob⟩
  rw [evaluateHOLFiniteState_call]
  have hevargs : @evalListHOLFinite 64 F _ state (fun a => Classical.propDecidable (state.memaddrs a))
      [stpExp] = some [.val (.word stp)] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact, hstp]
  have hlook := pan_one_word_lookup state.code.lookup (ofString "keccak_f1600") (ofString "stp")
    (sourceFnBody Guest.Software.guestFn_keccak_f1600) stp (by rw [hcode]; exact lookup_keccak_f1600)
  rw [hevargs]
  dsimp only
  rw [hlook]
  dsimp only
  split
  · exact memOutsideUnchanged_refl _ _ _
  · set callee : HolFiniteMapExact MlS (ValueHOL 64) :=
      HolFiniteMapExact.empty.update (ofString "stp", .val (.word stp))
    have hloc_stp : (callEntryStateHOLFinite state callee).locals.lookup (ofString "stp") =
        some (.val (.word stp)) := by
      simp [callEntryStateHOLFinite, callee, HolFiniteMapExact.lookup_update, FUPDATE]
    have hm := writesOnlyRange_constBase (ofString "stp") 200
      (sourceFnBody Guest.Software.guestFn_keccak_f1600)
      (by decide) (by decide) (by decide)
      (callEntryStateHOLFinite state callee) stp hstp_small hloc_stp
    rcases hran : evaluateHOLFiniteState (callEntryStateHOLFinite state callee)
      (sourceFnBody Guest.Software.guestFn_keccak_f1600) with ⟨res, post⟩
    rw [hran] at hm
    dsimp only at hm ⊢
    cases res with
    | none => exact hm
    | some r =>
      cases r with
      | returned val =>
        dsimp only
        split <;> exact hm
      | «break» | «continue» | error | timeOut | finalFfi _ | exception _ _ =>
        simpa [emptyLocalsHOLFinite, callEntryStateHOLFinite, decClockHOLFinite] using hm

private def storeAddrBoundedIdx (dstVar iVar : MlS) (step off : Nat) (e : ExpHOL 64) : Bool :=
  match e with
  | .op bop es =>
    match bop with
    | .add =>
      match es with
      | e1 :: es1 =>
        match es1 with
        | e2 :: es2 =>
          match es2 with
          | [] =>
            match e1 with
            | .var vk1 v =>
              match vk1 with
              | .local =>
                match e2 with
                | .var vk2 iv =>
                  match vk2 with
                  | .local => (v == dstVar) && (iv == iVar) && decide (off ≤ step)
                  | .global => false
                | _ => false
              | .global => false
            | _ => false
          | e3 :: es3 =>
            match es3 with
            | [] =>
              match e1 with
              | .var vk1 v =>
                match vk1 with
                | .local =>
                  match e2 with
                  | .var vk2 iv =>
                    match vk2 with
                    | .local =>
                      match e3 with
                      | .const k => (v == dstVar) && (iv == iVar) && decide (k.toNat + off ≤ step)
                      | _ => false
                    | .global => false
                  | _ => false
                | .global => false
              | _ => false
            | _ :: _ => false
        | [] => false
      | [] => false
    | _ => false
  | _ => false

private def checkIdxStores (dstVar iVar : MlS) (step : Nat) : ProgHOL 64 → Bool
  | .skip => true
  | .store addr _ => storeAddrBoundedIdx dstVar iVar step 8 addr
  | .storeByte addr _ => storeAddrBoundedIdx dstVar iVar step 1 addr
  | .seq p1 p2 => checkIdxStores dstVar iVar step p1 && checkIdxStores dstVar iVar step p2
  | _ => false

private theorem writesOnlyRange_idxBody {F : Type}
    (dstVar iVar : MlS) (step : Nat) (p : ProgHOL 64)
    (hlocals : localOnlyNoCalls p = true)
    (hav_dst : avoidsLocal dstVar p = true)
    (hav_i : avoidsLocal iVar p = true)
    (hstores : checkIdxStores dstVar iVar step p = true)
    (state : PanSemStateFiniteExact 64 F) (dst wi : BitVec 64) (len : Nat)
    (hdst_small : dst.toNat + len < 2 ^ 64)
    (hwi_step : wi.toNat + step ≤ len)
    (hdst : state.locals.lookup dstVar = some (.val (.word dst)))
    (hi : state.locals.lookup iVar = some (.val (.word wi))) :
    MemOutsideUnchanged (evaluateHOLFiniteState state p).2.memory state.memory dst len := by
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by decide
  cases shape : p with
  | skip => simp [evaluateHOLFiniteState_skip, memOutsideUnchanged_refl]
  | seq p1 p2 =>
    have hl : localOnlyNoCalls p1 = true ∧ localOnlyNoCalls p2 = true := by
      simpa [shape, localOnlyNoCalls, Bool.and_eq_true] using hlocals
    have hd : avoidsLocal dstVar p1 = true ∧ avoidsLocal dstVar p2 = true := by
      simpa [shape, avoidsLocal, Bool.and_eq_true] using hav_dst
    have hi' : avoidsLocal iVar p1 = true ∧ avoidsLocal iVar p2 = true := by
      simpa [shape, avoidsLocal, Bool.and_eq_true] using hav_i
    have hs : checkIdxStores dstVar iVar step p1 = true ∧ checkIdxStores dstVar iVar step p2 = true := by
      simpa [shape, checkIdxStores, Bool.and_eq_true] using hstores
    have m1 := writesOnlyRange_idxBody dstVar iVar step p1 hl.1 hd.1 hi'.1 hs.1 state dst wi len hdst_small hwi_step hdst hi
    have hfd := evaluate_avoidsLocal_flowing dstVar p1 hd.1 state
    have hfi := evaluate_avoidsLocal_flowing iVar p1 hi'.1 state
    rw [evaluateHOLFiniteState_seq_line780]
    rcases hr1 : evaluateHOLFiniteState state p1 with ⟨r1, mid⟩
    rw [hr1] at m1 hfd hfi
    dsimp only at m1 hfd hfi ⊢
    cases r1 with
    | none =>
      dsimp only
      have m2 := writesOnlyRange_idxBody dstVar iVar step p2 hl.2 hd.2 hi'.2 hs.2 mid dst wi len hdst_small hwi_step
        ((hfd (Or.inl rfl)).trans hdst) ((hfi (Or.inl rfl)).trans hi)
      exact memOutsideUnchanged_trans m1 m2
    | some _ => exact m1
  | store addr src =>
    have hs : storeAddrBoundedIdx dstVar iVar step 8 addr = true := by
      simpa [shape, checkIdxStores] using hstores
    cases addr with
    | op bop es =>
      cases bop <;> try cases hs
      rcases es with _ | ⟨e1, _ | ⟨e2, _ | ⟨e3, _ | _⟩⟩⟩ <;> try cases hs
      · cases e1 with
        | var vk1 v1 =>
          cases vk1 <;> try cases hs
          cases e2 with
          | var vk2 v2 =>
            cases vk2 <;> try cases hs
            have hcond : (v1 = dstVar ∧ v2 = iVar) ∧ 8 ≤ step := by
              simpa [storeAddrBoundedIdx, Bool.and_eq_true, beq_iff_eq] using hs
            rcases hcond with ⟨⟨rfl, rfl⟩, h8⟩
            have hev : @evalHOLExact 64 F _ state.toExact
                (fun a => Classical.propDecidable (state.memaddrs a))
                (.op .add [.var .local v1, .var .local v2]) = some (.val (.word (dst + wi))) := by
              simp [evalHOLExact, evalListHOLExact, hdst, hi, valueIsWord, valueWord, wordOpHOL, wordOp]
            have hadd : (dst + wi).toNat = dst.toNat + wi.toNat := by
              rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
            exact (writesOnlyRange_word (dst := dst) (len := len) hev ⟨by omega, by omega⟩).1
          | _ => cases hs
        | _ => cases hs
      · cases e1 with
        | var vk1 v1 =>
          cases vk1 <;> try cases hs
          cases e2 with
          | var vk2 v2 =>
            cases vk2 <;> try cases hs
            cases e3 with
            | const k =>
              have hcond : (v1 = dstVar ∧ v2 = iVar) ∧ k.toNat + 8 ≤ step := by
                simpa [storeAddrBoundedIdx, Bool.and_eq_true, beq_iff_eq] using hs
              rcases hcond with ⟨⟨rfl, rfl⟩, hk⟩
              have hev : @evalHOLExact 64 F _ state.toExact
                  (fun a => Classical.propDecidable (state.memaddrs a))
                  (.op .add [.var .local v1, .var .local v2, .const k]) = some (.val (.word (dst + wi + k))) := by
                simp [evalHOLExact, evalListHOLExact, hdst, hi, valueIsWord, valueWord, wordOpHOL, wordOp, BitVec.add_assoc]
              have hadd1 : (dst + wi).toNat = dst.toNat + wi.toNat := by
                rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
              have hadd2 : (dst + wi + k).toNat = dst.toNat + wi.toNat + k.toNat := by
                rw [BitVec.toNat_add, hadd1, Nat.mod_eq_of_lt (by omega)]
              exact (writesOnlyRange_word (dst := dst) (len := len) hev ⟨by omega, by omega⟩).1
            | _ => cases hs
          | _ => cases hs
        | _ => cases hs
    | _ => cases hs
  | storeByte addr src =>
    have hs : storeAddrBoundedIdx dstVar iVar step 1 addr = true := by
      simpa [shape, checkIdxStores] using hstores
    cases addr with
    | op bop es =>
      cases bop <;> try cases hs
      rcases es with _ | ⟨e1, _ | ⟨e2, _ | ⟨e3, _ | _⟩⟩⟩ <;> try cases hs
      · cases e1 with
        | var vk1 v1 =>
          cases vk1 <;> try cases hs
          cases e2 with
          | var vk2 v2 =>
            cases vk2 <;> try cases hs
            have hcond : (v1 = dstVar ∧ v2 = iVar) ∧ 1 ≤ step := by
              simpa [storeAddrBoundedIdx, Bool.and_eq_true, beq_iff_eq] using hs
            rcases hcond with ⟨⟨rfl, rfl⟩, h1⟩
            have hev : @evalHOLExact 64 F _ state.toExact
                (fun a => Classical.propDecidable (state.memaddrs a))
                (.op .add [.var .local v1, .var .local v2]) = some (.val (.word (dst + wi))) := by
              simp [evalHOLExact, evalListHOLExact, hdst, hi, valueIsWord, valueWord, wordOpHOL, wordOp]
            have hadd : (dst + wi).toNat = dst.toNat + wi.toNat := by
              rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
            exact (writesOnlyRange_byte (dst := dst) (len := len) hev ⟨by omega, by omega⟩).1
          | _ => cases hs
        | _ => cases hs
      · cases e1 with
        | var vk1 v1 =>
          cases vk1 <;> try cases hs
          cases e2 with
          | var vk2 v2 =>
            cases vk2 <;> try cases hs
            cases e3 with
            | const k =>
              have hcond : (v1 = dstVar ∧ v2 = iVar) ∧ k.toNat + 1 ≤ step := by
                simpa [storeAddrBoundedIdx, Bool.and_eq_true, beq_iff_eq] using hs
              rcases hcond with ⟨⟨rfl, rfl⟩, hk⟩
              have hev : @evalHOLExact 64 F _ state.toExact
                  (fun a => Classical.propDecidable (state.memaddrs a))
                  (.op .add [.var .local v1, .var .local v2, .const k]) = some (.val (.word (dst + wi + k))) := by
                simp [evalHOLExact, evalListHOLExact, hdst, hi, valueIsWord, valueWord, wordOpHOL, wordOp, BitVec.add_assoc]
              have hadd1 : (dst + wi).toNat = dst.toNat + wi.toNat := by
                rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
              have hadd2 : (dst + wi + k).toNat = dst.toNat + wi.toNat + k.toNat := by
                rw [BitVec.toNat_add, hadd1, Nat.mod_eq_of_lt (by omega)]
              exact (writesOnlyRange_byte (dst := dst) (len := len) hev ⟨by omega, by omega⟩).1
            | _ => cases hs
          | _ => cases hs
        | _ => cases hs
    | _ => cases hs
  | _ => simp [shape, checkIdxStores] at hstores
termination_by sizeOf p
decreasing_by
  all_goals
    subst shape
    simp_wf
    try omega

private def isTrailingIncAssign (iVar : MlS) (step : BitVec 64) (p : ProgHOL 64) : Bool :=
  match p with
  | .assign vk v rhs =>
    match vk with
    | .global => false
    | .local =>
      match rhs with
      | .op bop es =>
        match bop with
        | .add =>
          match es with
          | e1 :: es1 =>
            match es1 with
            | e2 :: es2 =>
              match es2 with
              | [] =>
                match e1 with
                | .var vk' v' =>
                  match vk' with
                  | .local =>
                    match e2 with
                    | .const k => (v == iVar) && (v' == iVar) && (k == step)
                    | _ => false
                  | .global => false
                | _ => false
              | _ :: _ => false
            | [] => false
          | [] => false
        | _ => false
      | _ => false
  | _ => false

private def splitTrailingInc (iVar : MlS) (step : BitVec 64) : ProgHOL 64 → Option (ProgHOL 64)
  | .seq p1 p2 =>
    if isTrailingIncAssign iVar step p2 then some p1
    else
      match splitTrailingInc iVar step p2 with
      | some p2' => some (.seq p1 p2')
      | none => none
  | _ => none

private theorem splitTrailingInc_skip (iVar : MlS) (step : BitVec 64) :
    splitTrailingInc iVar step .skip = none := rfl

private theorem eval_splitTrailingInc {F : Type}
    (dstVar iVar : MlS) (step : BitVec 64) (body pfx : ProgHOL 64)
    (hsplit : splitTrailingInc iVar step body = some pfx)
    (hlocals : localOnlyNoCalls pfx = true)
    (hav_dst : avoidsLocal dstVar pfx = true)
    (hav_i : avoidsLocal iVar pfx = true)
    (hstores : checkIdxStores dstVar iVar step.toNat pfx = true)
    (state : PanSemStateFiniteExact 64 F) (dst wi : BitVec 64) (len : Nat)
    (hdst_small : dst.toNat + len < 2 ^ 64)
    (hwi_step : wi.toNat + step.toNat ≤ len)
    (hdst : state.locals.lookup dstVar = some (.val (.word dst)))
    (hi : state.locals.lookup iVar = some (.val (.word wi))) :
    MemOutsideUnchanged (evaluateHOLFiniteState state body).2.memory state.memory dst len ∧
    ((evaluateHOLFiniteState state body).1 = none →
      (evaluateHOLFiniteState state body).2.locals.lookup iVar = some (.val (.word (wi + step)))) := by
  cases shape : body with
  | seq p1 p2 =>
    have hsp : splitTrailingInc iVar step (.seq p1 p2) = some pfx := by
      simpa [shape] using hsplit
    cases hp2 : p2 with
    | assign vk v rhs =>
      subst hp2
      unfold splitTrailingInc at hsp
      split at hsp
      · rename_i hcond
        injection hsp with hpfx
        subst hpfx
        cases vk <;> try cases hcond
        cases rhs with
        | op bop es =>
          cases bop <;> try cases hcond
          rcases es with _ | ⟨e1, _ | ⟨e2, _ | _⟩⟩ <;> try cases hcond
          cases e1 with
          | var vk1 v' =>
            cases vk1 <;> try cases hcond
            cases e2 with
            | const k =>
              have hc : (v = iVar ∧ v' = iVar) ∧ k = step := by
                simpa [isTrailingIncAssign, Bool.and_eq_true, beq_iff_eq] using hcond
              rcases hc with ⟨⟨hv1, hv2⟩, hk⟩
              subst v; subst v'; subst k
              have m1 := writesOnlyRange_idxBody dstVar iVar step.toNat p1 hlocals hav_dst hav_i hstores
                state dst wi len hdst_small hwi_step hdst hi
              have hfi := evaluate_avoidsLocal_flowing iVar p1 hav_i state
              rw [evaluateHOLFiniteState_seq_line780]
              rcases hr1 : evaluateHOLFiniteState state p1 with ⟨r1, mid⟩
              rw [hr1] at m1 hfi
              dsimp only at m1 hfi ⊢
              cases r1 with
              | some _ => exact ⟨m1, fun h => by simp at h⟩
              | none =>
                dsimp only
                have hmid_i : mid.locals.lookup iVar = some (.val (.word wi)) := (hfi (Or.inl rfl)).trans hi
                have hrun : evaluateHOLFiniteState mid
                    (.assign .local iVar (.op .add [.var .local iVar, .const step])) =
                    (none, setVarHOLFinite iVar (.val (.word (wi + step))) mid) := by
                  simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hmid_i,
                    wordOpHOL, wordOp, valueIsWord, valueWord, lookupKvarHOLExact,
                    isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
                rw [hrun]
                exact ⟨m1, fun _ => by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
            | _ => cases hcond
          | _ => cases hcond
        | _ => cases hcond
      · have hnone : splitTrailingInc iVar step (.assign vk v rhs) = none := rfl
        rw [hnone] at hsp
        cases hsp
    | seq q1 q2 =>
      subst hp2
      unfold splitTrailingInc at hsp
      have hfalse : isTrailingIncAssign iVar step (.seq q1 q2) = false := rfl
      rw [hfalse] at hsp
      simp only [Bool.false_eq_true, ↓reduceIte] at hsp
      cases hsp2 : splitTrailingInc iVar step (.seq q1 q2) with
      | none => rw [hsp2] at hsp; cases hsp
      | some p2' =>
        rw [hsp2] at hsp
        injection hsp with hpfx
        subst hpfx
        have hl : localOnlyNoCalls p1 = true ∧ localOnlyNoCalls p2' = true := by
          simpa [localOnlyNoCalls, Bool.and_eq_true] using hlocals
        have hd : avoidsLocal dstVar p1 = true ∧ avoidsLocal dstVar p2' = true := by
          simpa [avoidsLocal, Bool.and_eq_true] using hav_dst
        have hi' : avoidsLocal iVar p1 = true ∧ avoidsLocal iVar p2' = true := by
          simpa [avoidsLocal, Bool.and_eq_true] using hav_i
        have hs : checkIdxStores dstVar iVar step.toNat p1 = true ∧
            checkIdxStores dstVar iVar step.toNat p2' = true := by
          simpa [checkIdxStores, Bool.and_eq_true] using hstores
        have m1 := writesOnlyRange_idxBody dstVar iVar step.toNat p1 hl.1 hd.1 hi'.1 hs.1
          state dst wi len hdst_small hwi_step hdst hi
        have hfd := evaluate_avoidsLocal_flowing dstVar p1 hd.1 state
        have hfi := evaluate_avoidsLocal_flowing iVar p1 hi'.1 state
        rw [evaluateHOLFiniteState_seq_line780]
        rcases hr1 : evaluateHOLFiniteState state p1 with ⟨r1, mid⟩
        rw [hr1] at m1 hfd hfi
        dsimp only at m1 hfd hfi ⊢
        cases r1 with
        | some _ => exact ⟨m1, fun h => by simp at h⟩
        | none =>
          dsimp only
          obtain ⟨m2, hpost⟩ := eval_splitTrailingInc dstVar iVar step (.seq q1 q2) p2'
            hsp2 hl.2 hd.2 hi'.2 hs.2 mid dst wi len hdst_small hwi_step
            ((hfd (Or.inl rfl)).trans hdst) ((hfi (Or.inl rfl)).trans hi)
          exact ⟨memOutsideUnchanged_trans m1 m2, hpost⟩
    | _ =>
      subst hp2
      cases hsp
  | _ =>
    subst shape
    cases hsplit
termination_by sizeOf body
decreasing_by
  all_goals
    subst shape
    try subst hp2
    simp_wf
    try omega

private theorem writesOnlyRange_strideWhile {F : Type}
    (dstVar iVar nVar : MlS) (step : BitVec 64) (cond : ExpHOL 64) (body pfx : ProgHOL 64)
    (hsplit : splitTrailingInc iVar step body = some pfx)
    (hlocals : localOnlyNoCalls pfx = true)
    (hav_dst : avoidsLocal dstVar body = true)
    (hav_n : avoidsLocal nVar body = true)
    (hav_i_pfx : avoidsLocal iVar pfx = true)
    (hav_dst_pfx : avoidsLocal dstVar pfx = true)
    (hstores : checkIdxStores dstVar iVar step.toNat pfx = true)
    (hnc : noTopContinue body = true)
    (hnb : noTopBreak body = true)
    (hstep_mod8 : step.toNat % 8 = 0 ∨ step = BitVec.ofNat 64 1)
    (hcond :
      (cond = .cmp .notLower (.var .local nVar) (.op .add [.var .local iVar, .const step])) ∨
      (cond = .cmp .lower (.var .local iVar) (.var .local nVar) ∧ step = BitVec.ofNat 64 1) ∨
      (cond = .cmp .less (.var .local iVar) (.const (BitVec.ofNat 64 136)) ∧ step = BitVec.ofNat 64 8))
    (state : PanSemStateFiniteExact 64 F) (dst n wi : BitVec 64)
    (hdst_small : dst.toNat + n.toNat < 2 ^ 64)
    (hn_small : n.toNat + step.toNat < 2 ^ 63)
    (h136 : cond = .cmp .less (.var .local iVar) (.const (BitVec.ofNat 64 136)) →
      n.toNat = 136 ∧ wi.toNat % 8 = 0)
    (hwi_le : wi.toNat ≤ n.toNat)
    (hdst : state.locals.lookup dstVar = some (.val (.word dst)))
    (hn : state.locals.lookup nVar = some (.val (.word n)))
    (hi : state.locals.lookup iVar = some (.val (.word wi))) :
    MemOutsideUnchanged (evaluateHOLFiniteState state (.while cond body)).2.memory state.memory dst n.toNat ∧
    ((evaluateHOLFiniteState state (.while cond body)).1 = none →
      ∃ wi' : BitVec 64,
        (evaluateHOLFiniteState state (.while cond body)).2.locals.lookup iVar = some (.val (.word wi')) ∧
        wi'.toNat ≤ n.toNat ∧
        (evaluateHOLFiniteState state (.while cond body)).2.locals.lookup dstVar = some (.val (.word dst)) ∧
        (evaluateHOLFiniteState state (.while cond body)).2.locals.lookup nVar = some (.val (.word n))) := by
  have h263 : (2 ^ 63 : Nat) = 9223372036854775808 := by decide
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by decide
  suffices hrec : ∀ (clk : Nat) (st : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      st.clock = clk →
      w.toNat ≤ n.toNat →
      (cond = .cmp .less (.var .local iVar) (.const (BitVec.ofNat 64 136)) →
        n.toNat = 136 ∧ w.toNat % 8 = 0) →
      st.locals.lookup dstVar = some (.val (.word dst)) →
      st.locals.lookup nVar = some (.val (.word n)) →
      st.locals.lookup iVar = some (.val (.word w)) →
      MemOutsideUnchanged (evaluateHOLFiniteState st (.while cond body)).2.memory st.memory dst n.toNat ∧
      ((evaluateHOLFiniteState st (.while cond body)).1 = none →
        ∃ wi' : BitVec 64,
          (evaluateHOLFiniteState st (.while cond body)).2.locals.lookup iVar = some (.val (.word wi')) ∧
          wi'.toNat ≤ n.toNat ∧
          (evaluateHOLFiniteState st (.while cond body)).2.locals.lookup dstVar = some (.val (.word dst)) ∧
          (evaluateHOLFiniteState st (.while cond body)).2.locals.lookup nVar = some (.val (.word n))) by
    exact hrec state.clock state wi rfl hwi_le h136 hdst hn hi
  intro clk
  induction clk using Nat.strongRecOn with
  | ind clk ih =>
    intro st w hclk hw_le hw136 hst_dst hst_n hst_i
    rw [evaluateHOLFiniteState_while_total]
    have hcond_eval : ∃ b : Bool,
        @evalHOLFinite 64 F _ st (fun a => Classical.propDecidable (st.memaddrs a)) cond =
          some (.val (.word (if b then 1 else 0))) ∧
        (b = true → w.toNat + step.toNat ≤ n.toNat) := by
      rcases hcond with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine ⟨!(decide (n < w + step)), ?_, ?_⟩
        · rw [evalHOLFinite_eq_toExact]
          simp [evalHOLExact, evalListHOLExact, hst_n, hst_i, valueIsWord, valueWord,
            wordOpHOL, wordOp, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        · intro hb
          have hadd : (w + step).toNat = w.toNat + step.toNat := by
            rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
          have hnlt : ¬ n.toNat < (w + step).toNat := by
            simpa [BitVec.lt_def] using hb
          omega
      · refine ⟨decide (w < n), ?_, ?_⟩
        · rw [evalHOLFinite_eq_toExact]
          simp [evalHOLExact, hst_n, hst_i, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        · intro hb
          have hlt : w.toNat < n.toNat := by simpa [BitVec.lt_def] using hb
          have h1 : (BitVec.ofNat 64 1).toNat = 1 := by decide
          omega
      · refine ⟨Flapjack.Compiler.Encoders.Asm.holAsmSignedLess w (BitVec.ofNat 64 136), ?_, ?_⟩
        · rw [evalHOLFinite_eq_toExact]
          simp [evalHOLExact, hst_i, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
          rfl
        · intro hb
          obtain ⟨hn136, hwmod⟩ := hw136 rfl
          have h8 : (BitVec.ofNat 64 8).toNat = 8 := by decide
          have hc136 : (BitVec.ofNat 64 136).toNat = 136 := by decide
          have hw_sign : w.toNat < 2 ^ (64 - 1) := by omega
          have h136_sign : (BitVec.ofNat 64 136).toNat < 2 ^ (64 - 1) := by decide
          have hslt : w.toNat < 136 := by
            unfold Flapjack.Compiler.Encoders.Asm.holAsmSignedLess at hb
            rw [if_pos hw_sign, if_pos h136_sign] at hb
            have hdec : w.toNat < (BitVec.ofNat 64 136).toNat := of_decide_eq_true hb
            omega
          omega
    obtain ⟨b, hevc, hb_step⟩ := hcond_eval
    rw [hevc]
    dsimp only
    cases b with
    | false =>
      rw [if_neg (by decide)]
      exact ⟨memOutsideUnchanged_refl _ _ _, fun _ => ⟨w, hst_i, hw_le, hst_dst, hst_n⟩⟩
    | true =>
      rw [if_pos (by decide)]
      by_cases hcz : st.clock = 0
      · rw [if_pos hcz]; exact ⟨memOutsideUnchanged_refl _ _ _, fun h => by simp at h⟩
      · rw [if_neg hcz]
        rw [fixClockHOLFinite_evaluateState]
        have hstep_le := hb_step rfl
        have hb_run := eval_splitTrailingInc dstVar iVar step body pfx hsplit hlocals
          hav_dst_pfx hav_i_pfx hstores (decClockHOLFinite st) dst w n.toNat
          hdst_small hstep_le hst_dst hst_i
        have hfd := evaluate_avoidsLocal_flowing dstVar body hav_dst (decClockHOLFinite st)
        have hfn := evaluate_avoidsLocal_flowing nVar body hav_n (decClockHOLFinite st)
        have hnc' := evaluate_noTopContinue body hnc (decClockHOLFinite st)
        have hnb' := evaluate_noTopBreak body hnb (decClockHOLFinite st)
        have hcle := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) body
        rcases hbr : evaluateHOLFiniteState (decClockHOLFinite st) body with ⟨rb, mid⟩
        rw [hbr] at hb_run hfd hfn hnc' hnb' hcle
        dsimp only at hb_run hfd hfn hnc' hnb' hcle
        have hlt_clk : mid.clock < clk := by
          change mid.clock ≤ st.clock - 1 at hcle; omega
        cases rb with
        | none =>
          have hmid_i := hb_run.2 rfl
          have hmid_dst : mid.locals.lookup dstVar = some (.val (.word dst)) :=
            (hfd (Or.inl rfl)).trans hst_dst
          have hmid_n : mid.locals.lookup nVar = some (.val (.word n)) :=
            (hfn (Or.inl rfl)).trans hst_n
          have hw_add : (w + step).toNat = w.toNat + step.toNat := by
            rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
          have hw'_le : (w + step).toNat ≤ n.toNat := by omega
          have hw'136 : cond = .cmp .less (.var .local iVar) (.const (BitVec.ofNat 64 136)) →
              n.toNat = 136 ∧ (w + step).toNat % 8 = 0 := by
            intro hc
            obtain ⟨hn136, hwmod⟩ := hw136 hc
            rcases hcond with rfl | ⟨rfl, _⟩ | ⟨_, rfl⟩
            · cases hc
            · cases hc
            · have h8 : (BitVec.ofNat 64 8).toNat = 8 := by decide
              exact ⟨hn136, by omega⟩
          obtain ⟨hm2, hpost⟩ := ih mid.clock hlt_clk mid (w + step) rfl hw'_le hw'136
            hmid_dst hmid_n hmid_i
          exact ⟨memOutsideUnchanged_trans hb_run.1 hm2, hpost⟩
        | some r' =>
          cases r' with
          | «continue» => exact absurd rfl hnc'
          | «break» => exact absurd rfl hnb'
          | _ => exact ⟨hb_run.1, fun h => by simp at h⟩

private theorem writesOnlyRange_lessConstWhile {F : Type}
    (dstVar iVar : MlS) (step limit : BitVec 64) (body pfx : ProgHOL 64)
    (hsplit : splitTrailingInc iVar step body = some pfx)
    (hlocals : localOnlyNoCalls pfx = true)
    (hav_dst : avoidsLocal dstVar body = true)
    (hav_i_pfx : avoidsLocal iVar pfx = true)
    (hav_dst_pfx : avoidsLocal dstVar pfx = true)
    (hstores : checkIdxStores dstVar iVar step.toNat pfx = true)
    (hnc : noTopContinue body = true)
    (hnb : noTopBreak body = true)
    (hstep_pos : 0 < step.toNat)
    (hlim_mod : limit.toNat % step.toNat = 0)
    (hlim_small : limit.toNat + step.toNat < 2 ^ 63)
    (state : PanSemStateFiniteExact 64 F) (dst wi : BitVec 64)
    (hdst_small : dst.toNat + limit.toNat < 2 ^ 64)
    (hwi_le : wi.toNat ≤ limit.toNat)
    (hwi_mod : wi.toNat % step.toNat = 0)
    (hdst : state.locals.lookup dstVar = some (.val (.word dst)))
    (hi : state.locals.lookup iVar = some (.val (.word wi))) :
    MemOutsideUnchanged
      (evaluateHOLFiniteState state (.while (.cmp .less (.var .local iVar) (.const limit)) body)).2.memory
      state.memory dst limit.toNat := by
  have h263 : (2 ^ 63 : Nat) = 9223372036854775808 := by decide
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by decide
  suffices hrec : ∀ (clk : Nat) (st : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      st.clock = clk →
      w.toNat ≤ limit.toNat →
      w.toNat % step.toNat = 0 →
      st.locals.lookup dstVar = some (.val (.word dst)) →
      st.locals.lookup iVar = some (.val (.word w)) →
      MemOutsideUnchanged
        (evaluateHOLFiniteState st (.while (.cmp .less (.var .local iVar) (.const limit)) body)).2.memory
        st.memory dst limit.toNat by
    exact hrec state.clock state wi rfl hwi_le hwi_mod hdst hi
  intro clk
  induction clk using Nat.strongRecOn with
  | ind clk ih =>
    intro st w hclk hw_le hw_mod hst_dst hst_i
    rw [evaluateHOLFiniteState_while_total]
    have hevc : @evalHOLFinite 64 F _ st (fun a => Classical.propDecidable (st.memaddrs a))
        (.cmp .less (.var .local iVar) (.const limit)) =
        some (.val (.word (if Flapjack.Compiler.Encoders.Asm.holAsmSignedLess w limit then 1 else 0))) := by
      rw [evalHOLFinite_eq_toExact]
      simp [evalHOLExact, hst_i, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      rfl
    rw [hevc]
    dsimp only
    cases hslt : Flapjack.Compiler.Encoders.Asm.holAsmSignedLess w limit with
    | false =>
      rw [if_neg (by decide)]
      exact memOutsideUnchanged_refl _ _ _
    | true =>
      rw [if_pos (by decide)]
      by_cases hcz : st.clock = 0
      · rw [if_pos hcz]; exact memOutsideUnchanged_refl _ _ _
      · rw [if_neg hcz]
        rw [fixClockHOLFinite_evaluateState]
        have hw_sign : w.toNat < 2 ^ (64 - 1) := by omega
        have hlim_sign : limit.toNat < 2 ^ (64 - 1) := by omega
        have hlt_nat : w.toNat < limit.toNat := by
          unfold Flapjack.Compiler.Encoders.Asm.holAsmSignedLess at hslt
          rw [if_pos hw_sign, if_pos hlim_sign] at hslt
          exact of_decide_eq_true hslt
        have hstep_le : w.toNat + step.toNat ≤ limit.toNat := by
          obtain ⟨qw, hqw⟩ := Nat.dvd_of_mod_eq_zero hw_mod
          obtain ⟨ql, hql⟩ := Nat.dvd_of_mod_eq_zero hlim_mod
          have hqlt : qw < ql := by
            by_contra hge
            have hge' : ql ≤ qw := Nat.le_of_not_lt hge
            have hle' : step.toNat * ql ≤ step.toNat * qw := Nat.mul_le_mul_left _ hge'
            omega
          have hq1 : qw + 1 ≤ ql := hqlt
          calc w.toNat + step.toNat = step.toNat * (qw + 1) := by rw [hqw, Nat.mul_add, Nat.mul_one]
            _ ≤ step.toNat * ql := Nat.mul_le_mul_left _ hq1
            _ = limit.toNat := hql.symm
        have hb_run := eval_splitTrailingInc dstVar iVar step body pfx hsplit hlocals
          hav_dst_pfx hav_i_pfx hstores (decClockHOLFinite st) dst w limit.toNat
          hdst_small hstep_le hst_dst hst_i
        have hfd := evaluate_avoidsLocal_flowing dstVar body hav_dst (decClockHOLFinite st)
        have hnc' := evaluate_noTopContinue body hnc (decClockHOLFinite st)
        have hnb' := evaluate_noTopBreak body hnb (decClockHOLFinite st)
        have hcle := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) body
        rcases hbr : evaluateHOLFiniteState (decClockHOLFinite st) body with ⟨rb, mid⟩
        rw [hbr] at hb_run hfd hnc' hnb' hcle
        dsimp only at hb_run hfd hnc' hnb' hcle
        have hlt_clk : mid.clock < clk := by
          change mid.clock ≤ st.clock - 1 at hcle; omega
        cases rb with
        | none =>
          have hmid_i := hb_run.2 rfl
          have hmid_dst : mid.locals.lookup dstVar = some (.val (.word dst)) :=
            (hfd (Or.inl rfl)).trans hst_dst
          have hw_add : (w + step).toNat = w.toNat + step.toNat := by
            rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
          have hw'_mod : (w + step).toNat % step.toNat = 0 := by
            rw [hw_add, Nat.add_mod_right]; exact hw_mod
          have hm2 := ih mid.clock hlt_clk mid (w + step) rfl (by omega) hw'_mod hmid_dst hmid_i
          exact memOutsideUnchanged_trans hb_run.1 hm2
        | some r' =>
          cases r' with
          | «continue» => exact absurd rfl hnc'
          | «break» => exact absurd rfl hnb'
          | _ => exact hb_run.1

private def keccakAbsorbIteProg : ProgHOL 64 :=
  ProgHOL.ite
    (ExpHOL.cmp Cmp.equal (ExpHOL.op BinOp.and [ExpHOL.var VarKind.local (ofString "blk"), ExpHOL.const (BitVec.ofNat 64 7)])
      (ExpHOL.const (BitVec.ofNat 64 0)))
    (ProgHOL.while (ExpHOL.cmp Cmp.less (ExpHOL.var VarKind.local (ofString "i")) (ExpHOL.const (BitVec.ofNat 64 136)))
      (ProgHOL.seq
        (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "stp"), ExpHOL.var VarKind.local (ofString "i")])
          (ExpHOL.op BinOp.xor
            [ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "stp"), ExpHOL.var VarKind.local (ofString "i")]),
             ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "blk"), ExpHOL.var VarKind.local (ofString "i")])]))
        (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 8)]))))
    (ProgHOL.while (ExpHOL.cmp Cmp.less (ExpHOL.var VarKind.local (ofString "i")) (ExpHOL.const (BitVec.ofNat 64 136)))
      (ProgHOL.seq
        (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "stp"), ExpHOL.var VarKind.local (ofString "i")])
          (ExpHOL.op BinOp.xor
            [ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "stp"), ExpHOL.var VarKind.local (ofString "i")]),
             ExpHOL.op BinOp.or
              [ExpHOL.loadByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "blk"), ExpHOL.var VarKind.local (ofString "i")]),
               ExpHOL.shift Shift.lsl (ExpHOL.loadByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "blk"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 1)])) (ExpHOL.const (BitVec.ofNat 64 8)),
               ExpHOL.shift Shift.lsl (ExpHOL.loadByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "blk"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 2)])) (ExpHOL.const (BitVec.ofNat 64 16)),
               ExpHOL.shift Shift.lsl (ExpHOL.loadByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "blk"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 3)])) (ExpHOL.const (BitVec.ofNat 64 24)),
               ExpHOL.shift Shift.lsl
                (ExpHOL.op BinOp.or
                  [ExpHOL.loadByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "blk"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 4)]),
                   ExpHOL.shift Shift.lsl (ExpHOL.loadByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "blk"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 4), ExpHOL.const (BitVec.ofNat 64 1)])) (ExpHOL.const (BitVec.ofNat 64 8)),
                   ExpHOL.shift Shift.lsl (ExpHOL.loadByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "blk"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 4), ExpHOL.const (BitVec.ofNat 64 2)])) (ExpHOL.const (BitVec.ofNat 64 16)),
                   ExpHOL.shift Shift.lsl (ExpHOL.loadByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "blk"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 4), ExpHOL.const (BitVec.ofNat 64 3)])) (ExpHOL.const (BitVec.ofNat 64 24))])
                (ExpHOL.const (BitVec.ofNat 64 32))]]))
        (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 8)]))))

private theorem keccakAbsorbIteProg_avoids_stp :
    avoidsLocal (ofString "stp") keccakAbsorbIteProg = true := rfl

private theorem keccakAbsorbIteProg_locals :
    localOnlyNoCalls keccakAbsorbIteProg = true := rfl

private theorem memOutsideUnchanged_call_keccak_absorb_block {F : Type}
    (state : PanSemStateFiniteExact 64 F) (stpExp blkExp : ExpHOL 64) (stp blk : BitVec 64)
    (hcode : state.code = originalRuntimeCode)
    (hstp_small : stp.toNat + 200 < 2 ^ 64)
    (hstp : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) stpExp = some (.val (.word stp)))
    (hblk : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) blkExp = some (.val (.word blk))) :
    let out := evaluateHOLFiniteState state
      (.call (some (none, none)) (ofString "keccak_absorb_block") [stpExp, blkExp])
    MemOutsideUnchanged out.2.memory state.memory stp 200 ∧ out.2.globals = state.globals := by
  dsimp only
  have h263 : (2 ^ 63 : Nat) = 9223372036854775808 := by decide
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by decide
  rw [evaluateHOLFiniteState_call]
  have hevargs : @evalListHOLFinite 64 F _ state (fun a => Classical.propDecidable (state.memaddrs a))
      [stpExp, blkExp] = some [.val (.word stp), .val (.word blk)] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact, hstp, hblk]
  have hlook := pan_two_word_lookup state.code.lookup (ofString "keccak_absorb_block")
    (ofString "stp") (ofString "blk") (sourceFnBody Guest.Software.guestFn_keccak_absorb_block)
    stp blk (by decide) (by rw [hcode]; exact lookup_keccak_absorb_block)
  rw [hevargs]
  dsimp only
  rw [hlook]
  dsimp only
  split
  · exact ⟨memOutsideUnchanged_refl _ _ _, rfl⟩
  · set callee : HolFiniteMapExact MlS (ValueHOL 64) :=
      (HolFiniteMapExact.empty.update (ofString "stp", .val (.word stp))).update
        (ofString "blk", .val (.word blk))
    have hloc_stp : (callEntryStateHOLFinite state callee).locals.lookup (ofString "stp") =
        some (.val (.word stp)) := by
      have hne : ofString "blk" ≠ ofString "stp" := by decide
      simp [callEntryStateHOLFinite, callee, HolFiniteMapExact.lookup_update, FUPDATE, hne]
    have hbody_eq : sourceFnBody Guest.Software.guestFn_keccak_absorb_block =
        ProgHOL.dec (ofString "i") .one (.const (BitVec.ofNat 64 0))
          (.seq keccakAbsorbIteProg
            (.seq (.call (some (none, none)) (ofString "keccak_f1600") [.var .local (ofString "stp")])
              (.return (.const (BitVec.ofNat 64 0))))) := rfl
    have hbody_frame :
        MemOutsideUnchanged
          (evaluateHOLFiniteState (callEntryStateHOLFinite state callee)
            (sourceFnBody Guest.Software.guestFn_keccak_absorb_block)).2.memory
          state.memory stp 200 ∧
        (evaluateHOLFiniteState (callEntryStateHOLFinite state callee)
            (sourceFnBody Guest.Software.guestFn_keccak_absorb_block)).2.globals = state.globals := by
      rw [hbody_eq]
      rw [evaluateHOLFiniteState_dec_total]
      dsimp only
      have hev0 : @evalHOLExact 64 F _ (callEntryStateHOLFinite state callee).toExact
          (fun a => Classical.propDecidable ((callEntryStateHOLFinite state callee).memaddrs a))
          (.const (BitVec.ofNat 64 0)) = some (.val (.word 0)) := rfl
      rw [hev0]
      dsimp only
      have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) = true := by
        simp [shapeEqHOL, shapeOfHOLExact]
      rw [if_pos hsh0]
      dsimp only
      set s0 := setVarHOLFinite (ofString "i") (.val (.word 0)) (callEntryStateHOLFinite state callee)
      have hs0_stp : s0.locals.lookup (ofString "stp") = some (.val (.word stp)) := by
        have hne : ofString "i" ≠ ofString "stp" := by decide
        simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hloc_stp]
      have hs0_i : s0.locals.lookup (ofString "i") = some (.val (.word 0)) := by
        simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hc0 : (0 : BitVec 64).toNat = 0 := rfl
      have hc136 : (BitVec.ofNat 64 136).toNat = 136 := rfl
      have hc8 : (BitVec.ofNat 64 8).toNat = 8 := rfl
      apply writesOnlyRange_seq
      · refine ⟨?_, evaluate_localOnlyNoCalls_globals keccakAbsorbIteProg keccakAbsorbIteProg_locals s0⟩
        dsimp only [keccakAbsorbIteProg]
        rw [evaluateHOLFiniteState_ite]
        split
        · split
          · have hm := writesOnlyRange_lessConstWhile (ofString "stp") (ofString "i")
              (BitVec.ofNat 64 8) (BitVec.ofNat 64 136)
              (ProgHOL.seq
                (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "stp"), ExpHOL.var VarKind.local (ofString "i")])
                  (ExpHOL.op BinOp.xor
                    [ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "stp"), ExpHOL.var VarKind.local (ofString "i")]),
                     ExpHOL.op BinOp.or
                      [ExpHOL.loadByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "blk"), ExpHOL.var VarKind.local (ofString "i")]),
                       ExpHOL.shift Shift.lsl (ExpHOL.loadByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "blk"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 1)])) (ExpHOL.const (BitVec.ofNat 64 8)),
                       ExpHOL.shift Shift.lsl (ExpHOL.loadByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "blk"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 2)])) (ExpHOL.const (BitVec.ofNat 64 16)),
                       ExpHOL.shift Shift.lsl (ExpHOL.loadByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "blk"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 3)])) (ExpHOL.const (BitVec.ofNat 64 24)),
                       ExpHOL.shift Shift.lsl
                        (ExpHOL.op BinOp.or
                          [ExpHOL.loadByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "blk"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 4)]),
                           ExpHOL.shift Shift.lsl (ExpHOL.loadByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "blk"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 4), ExpHOL.const (BitVec.ofNat 64 1)])) (ExpHOL.const (BitVec.ofNat 64 8)),
                           ExpHOL.shift Shift.lsl (ExpHOL.loadByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "blk"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 4), ExpHOL.const (BitVec.ofNat 64 2)])) (ExpHOL.const (BitVec.ofNat 64 16)),
                           ExpHOL.shift Shift.lsl (ExpHOL.loadByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "blk"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 4), ExpHOL.const (BitVec.ofNat 64 3)])) (ExpHOL.const (BitVec.ofNat 64 24))])
                        (ExpHOL.const (BitVec.ofNat 64 32))]]))
                (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 8)])))
              _
              rfl rfl rfl rfl rfl rfl rfl rfl
              (by omega) rfl (by omega) s0 stp (0 : BitVec 64)
              (by omega) (by omega) rfl hs0_stp hs0_i
            exact memOutsideUnchanged_mono hm (Nat.le_refl _) (by omega)
          · have hm := writesOnlyRange_lessConstWhile (ofString "stp") (ofString "i")
              (BitVec.ofNat 64 8) (BitVec.ofNat 64 136)
              (ProgHOL.seq
                (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "stp"), ExpHOL.var VarKind.local (ofString "i")])
                  (ExpHOL.op BinOp.xor
                    [ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "stp"), ExpHOL.var VarKind.local (ofString "i")]),
                     ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "blk"), ExpHOL.var VarKind.local (ofString "i")])]))
                (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 8)])))
              _
              rfl rfl rfl rfl rfl rfl rfl rfl
              (by omega) rfl (by omega) s0 stp (0 : BitVec 64)
              (by omega) (by omega) rfl hs0_stp hs0_i
            exact memOutsideUnchanged_mono hm (Nat.le_refl _) (by omega)
        · exact memOutsideUnchanged_refl _ _ _
      · intro mid hmid
        have hfd := evaluate_avoidsLocal_flowing (ofString "stp") keccakAbsorbIteProg keccakAbsorbIteProg_avoids_stp s0
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata s0 keccakAbsorbIteProg).1
        rw [hmid] at hfd hmeta
        dsimp only at hfd hmeta
        have hmid_stp : mid.locals.lookup (ofString "stp") = some (.val (.word stp)) :=
          (hfd (Or.inl rfl)).trans hs0_stp
        have hmid_code : mid.code = originalRuntimeCode := hmeta.trans hcode
        apply writesOnlyRange_seq
        · exact memOutsideUnchanged_call_keccak_f1600 mid (.var .local (ofString "stp")) stp
            hmid_code hstp_small (by simp [evalHOLExact, hmid_stp])
        · intro mid2 _
          rw [evaluateHOLFiniteState_return]
          split
          · exact ⟨memOutsideUnchanged_refl _ _ _, rfl⟩
          · split <;> exact ⟨memOutsideUnchanged_refl _ _ _, rfl⟩
    rcases hran : evaluateHOLFiniteState (callEntryStateHOLFinite state callee)
      (sourceFnBody Guest.Software.guestFn_keccak_absorb_block) with ⟨res, post⟩
    rw [hran] at hbody_frame
    dsimp only at hbody_frame ⊢
    cases res with
    | none => exact hbody_frame
    | some r =>
      cases r with
      | returned val =>
        dsimp only
        split <;> exact hbody_frame
      | «break» | «continue» | error | timeOut | finalFfi _ | exception _ _ =>
        simpa [emptyLocalsHOLFinite, callEntryStateHOLFinite, decClockHOLFinite] using hbody_frame

private def memzeroIteProg : ProgHOL 64 :=
  ProgHOL.ite
    (ExpHOL.cmp Cmp.equal (ExpHOL.op BinOp.and [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.const (BitVec.ofNat 64 7)])
      (ExpHOL.const (BitVec.ofNat 64 0)))
    (ProgHOL.seq
      (ProgHOL.while
        (ExpHOL.cmp Cmp.notLower (ExpHOL.var VarKind.local (ofString "n"))
          (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 32)]))
        (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i")]) (ExpHOL.const (BitVec.ofNat 64 0)))
          (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 8)]) (ExpHOL.const (BitVec.ofNat 64 0)))
            (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 16)]) (ExpHOL.const (BitVec.ofNat 64 0)))
              (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 24)]) (ExpHOL.const (BitVec.ofNat 64 0)))
                (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 32)])))))))
      (ProgHOL.while
        (ExpHOL.cmp Cmp.notLower (ExpHOL.var VarKind.local (ofString "n"))
          (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 8)]))
        (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i")]) (ExpHOL.const (BitVec.ofNat 64 0)))
          (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 8)])))))
    ProgHOL.skip

private theorem memzero_frame_body {F : Type}
    (state : PanSemStateFiniteExact 64 F) (dst n : BitVec 64)
    (hdst_small : dst.toNat + n.toNat < 2 ^ 64)
    (hn_small : n.toNat + 32 < 2 ^ 63)
    (hdst_loc : state.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (hn_loc : state.locals.lookup (ofString "n") = some (.val (.word n))) :
    let out := evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_memzero)
    MemOutsideUnchanged out.2.memory state.memory dst n.toNat ∧ out.2.globals = state.globals := by
  dsimp only
  have h263 : (2 ^ 63 : Nat) = 9223372036854775808 := by decide
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by decide
  have hc0 : (0 : BitVec 64).toNat = 0 := rfl
  have hc32 : (BitVec.ofNat 64 32).toNat = 32 := rfl
  have hc8 : (BitVec.ofNat 64 8).toNat = 8 := rfl
  have hc1 : (BitVec.ofNat 64 1).toNat = 1 := rfl
  have hglob := evaluate_localOnlyNoCalls_globals (sourceFnBody Guest.Software.guestFn_memzero) rfl state
  refine ⟨?_, hglob⟩
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_memzero,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  have hev0 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
      (.const (BitVec.ofNat 64 0)) = some (.val (.word 0)) := rfl
  rw [hev0]
  dsimp only
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos hsh0]
  dsimp only
  set s0 := setVarHOLFinite (ofString "i") (.val (.word 0)) state
  have hs0_i : s0.locals.lookup (ofString "i") = some (.val (.word 0)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs0_dst : s0.locals.lookup (ofString "dst") = some (.val (.word dst)) := by
    have hne : ofString "i" ≠ ofString "dst" := by decide
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hdst_loc]
  have hs0_n : s0.locals.lookup (ofString "n") = some (.val (.word n)) := by
    have hne : ofString "i" ≠ ofString "n" := by decide
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hn_loc]
  have hstep1 : MemOutsideUnchanged
      (evaluateHOLFiniteState s0 memzeroIteProg).2.memory s0.memory dst n.toNat ∧
      ((evaluateHOLFiniteState s0 memzeroIteProg).1 = none →
        ∃ wi1 : BitVec 64,
          (evaluateHOLFiniteState s0 memzeroIteProg).2.locals.lookup (ofString "i") = some (.val (.word wi1)) ∧
          wi1.toNat ≤ n.toNat ∧
          (evaluateHOLFiniteState s0 memzeroIteProg).2.locals.lookup (ofString "dst") = some (.val (.word dst)) ∧
          (evaluateHOLFiniteState s0 memzeroIteProg).2.locals.lookup (ofString "n") = some (.val (.word n))) := by
    dsimp only [memzeroIteProg]
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · simp only [evaluateHOLFiniteState_skip]
        exact ⟨memOutsideUnchanged_refl _ _ _, fun _ => ⟨(0 : BitVec 64), hs0_i, by omega, hs0_dst, hs0_n⟩⟩
      · rw [evaluateHOLFiniteState_seq_line780]
        have hw32 := writesOnlyRange_strideWhile (ofString "dst") (ofString "i") (ofString "n")
          (BitVec.ofNat 64 32)
          (ExpHOL.cmp Cmp.notLower (ExpHOL.var VarKind.local (ofString "n"))
            (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 32)]))
          (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i")]) (ExpHOL.const (BitVec.ofNat 64 0)))
            (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 8)]) (ExpHOL.const (BitVec.ofNat 64 0)))
              (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 16)]) (ExpHOL.const (BitVec.ofNat 64 0)))
                (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 24)]) (ExpHOL.const (BitVec.ofNat 64 0)))
                  (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 32)]))))))
          _
          rfl rfl rfl rfl rfl rfl rfl rfl rfl (Or.inl rfl) (Or.inl rfl)
          s0 dst n (0 : BitVec 64) hdst_small (by omega) (fun h => by cases h) (by omega) hs0_dst hs0_n hs0_i
        rcases hr32 : evaluateHOLFiniteState s0 _ with ⟨r32, s1⟩
        rw [hr32] at hw32
        dsimp only at hw32 ⊢
        cases r32 with
        | some _ => exact ⟨hw32.1, fun h => by simp at h⟩
        | none =>
          dsimp only
          obtain ⟨wi1, hs1_i, hwi1_le, hs1_dst, hs1_n⟩ := hw32.2 rfl
          have hw8 := writesOnlyRange_strideWhile (ofString "dst") (ofString "i") (ofString "n")
            (BitVec.ofNat 64 8)
            (ExpHOL.cmp Cmp.notLower (ExpHOL.var VarKind.local (ofString "n"))
              (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 8)]))
            (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i")]) (ExpHOL.const (BitVec.ofNat 64 0)))
              (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 8)])))
            _
            rfl rfl rfl rfl rfl rfl rfl rfl rfl (Or.inl rfl) (Or.inl rfl)
            s1 dst n wi1 hdst_small (by omega) (fun h => by cases h) hwi1_le hs1_dst hs1_n hs1_i
          exact ⟨memOutsideUnchanged_trans hw32.1 hw8.1, hw8.2⟩
    · exact ⟨memOutsideUnchanged_refl _ _ _, fun h => by simp at h⟩
  have hite_eq :
      ProgHOL.ite
        (ExpHOL.cmp Cmp.equal (ExpHOL.op BinOp.and [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.const (BitVec.ofNat 64 7)])
          (ExpHOL.const (BitVec.ofNat 64 0)))
        (ProgHOL.seq
          (ProgHOL.while
            (ExpHOL.cmp Cmp.notLower (ExpHOL.var VarKind.local (ofString "n"))
              (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 32)]))
            (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i")]) (ExpHOL.const (BitVec.ofNat 64 0)))
              (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 8)]) (ExpHOL.const (BitVec.ofNat 64 0)))
                (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 16)]) (ExpHOL.const (BitVec.ofNat 64 0)))
                  (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 24)]) (ExpHOL.const (BitVec.ofNat 64 0)))
                    (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 32)])))))))
          (ProgHOL.while
            (ExpHOL.cmp Cmp.notLower (ExpHOL.var VarKind.local (ofString "n"))
              (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 8)]))
            (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i")]) (ExpHOL.const (BitVec.ofNat 64 0)))
              (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 8)])))))
        ProgHOL.skip = memzeroIteProg := rfl
  rw [hite_eq]
  rw [evaluateHOLFiniteState_seq_line780]
  dsimp only
  rcases hr1 : evaluateHOLFiniteState s0 memzeroIteProg with ⟨r1, s1⟩
  rw [hr1] at hstep1
  dsimp only at hstep1 ⊢
  cases r1 with
  | some _ => exact hstep1.1
  | none =>
    dsimp only
    obtain ⟨wi1, hs1_i, hwi1_le, hs1_dst, hs1_n⟩ := hstep1.2 rfl
    have hw8b := writesOnlyRange_strideWhile (ofString "dst") (ofString "i") (ofString "n")
      (BitVec.ofNat 64 8)
      (ExpHOL.cmp Cmp.notLower (ExpHOL.var VarKind.local (ofString "n"))
        (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 8)]))
      (ProgHOL.seq (ProgHOL.storeByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i")]) (ExpHOL.const (BitVec.ofNat 64 0)))
        (ProgHOL.seq (ProgHOL.storeByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 1)]) (ExpHOL.const (BitVec.ofNat 64 0)))
          (ProgHOL.seq (ProgHOL.storeByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 2)]) (ExpHOL.const (BitVec.ofNat 64 0)))
            (ProgHOL.seq (ProgHOL.storeByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 3)]) (ExpHOL.const (BitVec.ofNat 64 0)))
              (ProgHOL.seq (ProgHOL.storeByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 4)]) (ExpHOL.const (BitVec.ofNat 64 0)))
                (ProgHOL.seq (ProgHOL.storeByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 5)]) (ExpHOL.const (BitVec.ofNat 64 0)))
                  (ProgHOL.seq (ProgHOL.storeByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 6)]) (ExpHOL.const (BitVec.ofNat 64 0)))
                    (ProgHOL.seq (ProgHOL.storeByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 7)]) (ExpHOL.const (BitVec.ofNat 64 0)))
                      (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 8)]))))))))))
      _
      rfl rfl rfl rfl rfl rfl rfl rfl rfl (Or.inl rfl) (Or.inl rfl)
      s1 dst n wi1 hdst_small (by omega) (fun h => by cases h) hwi1_le hs1_dst hs1_n hs1_i
    rw [evaluateHOLFiniteState_seq_line780]
    rcases hr2 : evaluateHOLFiniteState s1 _ with ⟨r2, s2⟩
    rw [hr2] at hw8b
    dsimp only at hw8b ⊢
    cases r2 with
    | some _ => exact memOutsideUnchanged_trans hstep1.1 hw8b.1
    | none =>
      dsimp only
      obtain ⟨wi2, hs2_i, hwi2_le, hs2_dst, hs2_n⟩ := hw8b.2 rfl
      have hw1b := writesOnlyRange_strideWhile (ofString "dst") (ofString "i") (ofString "n")
        (BitVec.ofNat 64 1)
        (ExpHOL.cmp Cmp.lower (ExpHOL.var VarKind.local (ofString "i")) (ExpHOL.var VarKind.local (ofString "n")))
        (ProgHOL.seq (ProgHOL.storeByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i")]) (ExpHOL.const (BitVec.ofNat 64 0)))
          (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 1)])))
        _
        rfl rfl rfl rfl rfl rfl rfl rfl rfl (Or.inr rfl) (Or.inr (Or.inl ⟨rfl, rfl⟩))
        s2 dst n wi2 hdst_small (by omega) (fun h => by cases h) hwi2_le hs2_dst hs2_n hs2_i
      rw [evaluateHOLFiniteState_seq_line780]
      rcases hr3 : evaluateHOLFiniteState s2 _ with ⟨r3, s3⟩
      rw [hr3] at hw1b
      dsimp only at hw1b ⊢
      cases r3 with
      | some _ => exact memOutsideUnchanged_trans (memOutsideUnchanged_trans hstep1.1 hw8b.1) hw1b.1
      | none =>
        dsimp only
        rw [evaluateHOLFiniteState_return]
        split
        · exact memOutsideUnchanged_trans (memOutsideUnchanged_trans hstep1.1 hw8b.1) hw1b.1
        · split <;> exact memOutsideUnchanged_trans (memOutsideUnchanged_trans hstep1.1 hw8b.1) hw1b.1

theorem memOutsideUnchanged_call_memzero {F : Type}
    (state : PanSemStateFiniteExact 64 F) (dstExp nExp : ExpHOL 64) (dst n : BitVec 64)
    (hcode : state.code = originalRuntimeCode)
    (hdst_small : dst.toNat + n.toNat < 2 ^ 64)
    (hn_small : n.toNat + 32 < 2 ^ 63)
    (hdst : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) dstExp = some (.val (.word dst)))
    (hn : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) nExp = some (.val (.word n))) :
    let out := evaluateHOLFiniteState state
      (.call (some (none, none)) (ofString "memzero") [dstExp, nExp])
    MemOutsideUnchanged out.2.memory state.memory dst n.toNat ∧ out.2.globals = state.globals := by
  dsimp only
  have hglob := evaluate_call_pure_globals state (ofString "memzero") [dstExp, nExp]
    hcode lookup_memzero (by decide)
  refine ⟨?_, hglob⟩
  rw [evaluateHOLFiniteState_call]
  have hevargs : @evalListHOLFinite 64 F _ state (fun a => Classical.propDecidable (state.memaddrs a))
      [dstExp, nExp] = some [.val (.word dst), .val (.word n)] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact, hdst, hn]
  have hlook := pan_two_word_lookup state.code.lookup (ofString "memzero")
    (ofString "dst") (ofString "n") (sourceFnBody Guest.Software.guestFn_memzero)
    dst n (by decide) (by rw [hcode]; exact lookup_memzero)
  rw [hevargs]
  dsimp only
  rw [hlook]
  dsimp only
  split
  · exact memOutsideUnchanged_refl _ _ _
  · set callee : HolFiniteMapExact MlS (ValueHOL 64) :=
      (HolFiniteMapExact.empty.update (ofString "dst", .val (.word dst))).update
        (ofString "n", .val (.word n))
    have hloc_dst : (callEntryStateHOLFinite state callee).locals.lookup (ofString "dst") =
        some (.val (.word dst)) := by
      have hne : ofString "n" ≠ ofString "dst" := by decide
      simp [callEntryStateHOLFinite, callee, HolFiniteMapExact.lookup_update, FUPDATE, hne]
    have hloc_n : (callEntryStateHOLFinite state callee).locals.lookup (ofString "n") =
        some (.val (.word n)) := by
      simp [callEntryStateHOLFinite, callee, HolFiniteMapExact.lookup_update, FUPDATE]
    have hm := (memzero_frame_body (callEntryStateHOLFinite state callee) dst n
      hdst_small hn_small hloc_dst hloc_n).1
    rcases hran : evaluateHOLFiniteState (callEntryStateHOLFinite state callee)
      (sourceFnBody Guest.Software.guestFn_memzero) with ⟨res, post⟩
    rw [hran] at hm
    dsimp only at hm ⊢
    cases res with
    | none => exact hm
    | some r =>
      cases r with
      | returned val => dsimp only; split <;> exact hm
      | «break» | «continue» | error | timeOut | finalFfi _ | exception _ _ =>
        simpa [emptyLocalsHOLFinite, callEntryStateHOLFinite, decClockHOLFinite] using hm

private def memcpyIteProg : ProgHOL 64 :=
  ProgHOL.ite
    (ExpHOL.cmp Cmp.equal
      (ExpHOL.op BinOp.and
        [ExpHOL.op BinOp.or [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "src")],
         ExpHOL.const (BitVec.ofNat 64 7)])
      (ExpHOL.const (BitVec.ofNat 64 0)))
    (ProgHOL.seq
      (ProgHOL.while
        (ExpHOL.cmp Cmp.notLower (ExpHOL.var VarKind.local (ofString "n"))
          (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 32)]))
        (ProgHOL.seq
          (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i")])
            (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "src"), ExpHOL.var VarKind.local (ofString "i")])))
          (ProgHOL.seq
            (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 8)])
              (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "src"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 8)])))
            (ProgHOL.seq
              (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 16)])
                (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "src"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 16)])))
              (ProgHOL.seq
                (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 24)])
                  (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "src"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 24)])))
                (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 32)])))))))
      (ProgHOL.while
        (ExpHOL.cmp Cmp.notLower (ExpHOL.var VarKind.local (ofString "n"))
          (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 8)]))
        (ProgHOL.seq
          (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i")])
            (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "src"), ExpHOL.var VarKind.local (ofString "i")])))
          (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 8)])))))
    ProgHOL.skip

private theorem memcpy_frame_body {F : Type}
    (state : PanSemStateFiniteExact 64 F) (dst n : BitVec 64)
    (hdst_small : dst.toNat + n.toNat < 2 ^ 64)
    (hn_small : n.toNat + 32 < 2 ^ 63)
    (hdst_loc : state.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (hn_loc : state.locals.lookup (ofString "n") = some (.val (.word n))) :
    let out := evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_memcpy)
    MemOutsideUnchanged out.2.memory state.memory dst n.toNat ∧ out.2.globals = state.globals := by
  dsimp only
  have h263 : (2 ^ 63 : Nat) = 9223372036854775808 := by decide
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by decide
  have hc0 : (0 : BitVec 64).toNat = 0 := rfl
  have hc32 : (BitVec.ofNat 64 32).toNat = 32 := rfl
  have hc8 : (BitVec.ofNat 64 8).toNat = 8 := rfl
  have hc1 : (BitVec.ofNat 64 1).toNat = 1 := rfl
  have hglob := evaluate_localOnlyNoCalls_globals (sourceFnBody Guest.Software.guestFn_memcpy) rfl state
  refine ⟨?_, hglob⟩
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_memcpy,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  have hev0 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
      (.const (BitVec.ofNat 64 0)) = some (.val (.word 0)) := rfl
  rw [hev0]
  dsimp only
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos hsh0]
  dsimp only
  set s0 := setVarHOLFinite (ofString "i") (.val (.word 0)) state
  have hs0_i : s0.locals.lookup (ofString "i") = some (.val (.word 0)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs0_dst : s0.locals.lookup (ofString "dst") = some (.val (.word dst)) := by
    have hne : ofString "i" ≠ ofString "dst" := by decide
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hdst_loc]
  have hs0_n : s0.locals.lookup (ofString "n") = some (.val (.word n)) := by
    have hne : ofString "i" ≠ ofString "n" := by decide
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hn_loc]
  have hstep1 : MemOutsideUnchanged
      (evaluateHOLFiniteState s0 memcpyIteProg).2.memory s0.memory dst n.toNat ∧
      ((evaluateHOLFiniteState s0 memcpyIteProg).1 = none →
        ∃ wi1 : BitVec 64,
          (evaluateHOLFiniteState s0 memcpyIteProg).2.locals.lookup (ofString "i") = some (.val (.word wi1)) ∧
          wi1.toNat ≤ n.toNat ∧
          (evaluateHOLFiniteState s0 memcpyIteProg).2.locals.lookup (ofString "dst") = some (.val (.word dst)) ∧
          (evaluateHOLFiniteState s0 memcpyIteProg).2.locals.lookup (ofString "n") = some (.val (.word n))) := by
    dsimp only [memcpyIteProg]
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · simp only [evaluateHOLFiniteState_skip]
        exact ⟨memOutsideUnchanged_refl _ _ _, fun _ => ⟨(0 : BitVec 64), hs0_i, by omega, hs0_dst, hs0_n⟩⟩
      · rw [evaluateHOLFiniteState_seq_line780]
        have hw32 := writesOnlyRange_strideWhile (ofString "dst") (ofString "i") (ofString "n")
          (BitVec.ofNat 64 32)
          (ExpHOL.cmp Cmp.notLower (ExpHOL.var VarKind.local (ofString "n"))
            (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 32)]))
          (ProgHOL.seq
            (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i")])
              (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "src"), ExpHOL.var VarKind.local (ofString "i")])))
            (ProgHOL.seq
              (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 8)])
                (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "src"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 8)])))
              (ProgHOL.seq
                (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 16)])
                  (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "src"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 16)])))
                (ProgHOL.seq
                  (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 24)])
                    (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "src"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 24)])))
                  (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 32)]))))))
          _
          rfl rfl rfl rfl rfl rfl rfl rfl rfl (Or.inl rfl) (Or.inl rfl)
          s0 dst n (0 : BitVec 64) hdst_small (by omega) (fun h => by cases h) (by omega) hs0_dst hs0_n hs0_i
        rcases hr32 : evaluateHOLFiniteState s0 _ with ⟨r32, s1⟩
        rw [hr32] at hw32
        dsimp only at hw32 ⊢
        cases r32 with
        | some _ => exact ⟨hw32.1, fun h => by simp at h⟩
        | none =>
          dsimp only
          obtain ⟨wi1, hs1_i, hwi1_le, hs1_dst, hs1_n⟩ := hw32.2 rfl
          have hw8 := writesOnlyRange_strideWhile (ofString "dst") (ofString "i") (ofString "n")
            (BitVec.ofNat 64 8)
            (ExpHOL.cmp Cmp.notLower (ExpHOL.var VarKind.local (ofString "n"))
              (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 8)]))
            (ProgHOL.seq
              (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i")])
                (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "src"), ExpHOL.var VarKind.local (ofString "i")])))
              (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 8)])))
            _
            rfl rfl rfl rfl rfl rfl rfl rfl rfl (Or.inl rfl) (Or.inl rfl)
            s1 dst n wi1 hdst_small (by omega) (fun h => by cases h) hwi1_le hs1_dst hs1_n hs1_i
          exact ⟨memOutsideUnchanged_trans hw32.1 hw8.1, hw8.2⟩
    · exact ⟨memOutsideUnchanged_refl _ _ _, fun h => by simp at h⟩
  have hite_eq :
      ProgHOL.ite
        (ExpHOL.cmp Cmp.equal
          (ExpHOL.op BinOp.and
            [ExpHOL.op BinOp.or [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "src")],
             ExpHOL.const (BitVec.ofNat 64 7)])
          (ExpHOL.const (BitVec.ofNat 64 0)))
        (ProgHOL.seq
          (ProgHOL.while
            (ExpHOL.cmp Cmp.notLower (ExpHOL.var VarKind.local (ofString "n"))
              (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 32)]))
            (ProgHOL.seq
              (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i")])
                (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "src"), ExpHOL.var VarKind.local (ofString "i")])))
              (ProgHOL.seq
                (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 8)])
                  (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "src"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 8)])))
                (ProgHOL.seq
                  (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 16)])
                    (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "src"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 16)])))
                  (ProgHOL.seq
                    (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 24)])
                      (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "src"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 24)])))
                    (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 32)])))))))
          (ProgHOL.while
            (ExpHOL.cmp Cmp.notLower (ExpHOL.var VarKind.local (ofString "n"))
              (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 8)]))
            (ProgHOL.seq
              (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i")])
                (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "src"), ExpHOL.var VarKind.local (ofString "i")])))
              (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 8)])))))
        ProgHOL.skip = memcpyIteProg := rfl
  rw [hite_eq]
  rw [evaluateHOLFiniteState_seq_line780]
  dsimp only
  rcases hr1 : evaluateHOLFiniteState s0 memcpyIteProg with ⟨r1, s1⟩
  rw [hr1] at hstep1
  dsimp only at hstep1 ⊢
  cases r1 with
  | some _ => exact hstep1.1
  | none =>
    dsimp only
    obtain ⟨wi1, hs1_i, hwi1_le, hs1_dst, hs1_n⟩ := hstep1.2 rfl
    have hw8b := writesOnlyRange_strideWhile (ofString "dst") (ofString "i") (ofString "n")
      (BitVec.ofNat 64 8)
      (ExpHOL.cmp Cmp.notLower (ExpHOL.var VarKind.local (ofString "n"))
        (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 8)]))
      (ProgHOL.seq
        (ProgHOL.storeByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i")])
          (ExpHOL.loadByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "src"), ExpHOL.var VarKind.local (ofString "i")])))
        (ProgHOL.seq
          (ProgHOL.storeByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 1)])
            (ExpHOL.loadByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "src"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 1)])))
          (ProgHOL.seq
            (ProgHOL.storeByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 2)])
              (ExpHOL.loadByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "src"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 2)])))
            (ProgHOL.seq
              (ProgHOL.storeByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 3)])
                (ExpHOL.loadByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "src"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 3)])))
              (ProgHOL.seq
                (ProgHOL.storeByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 4)])
                  (ExpHOL.loadByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "src"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 4)])))
                (ProgHOL.seq
                  (ProgHOL.storeByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 5)])
                    (ExpHOL.loadByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "src"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 5)])))
                  (ProgHOL.seq
                    (ProgHOL.storeByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 6)])
                      (ExpHOL.loadByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "src"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 6)])))
                    (ProgHOL.seq
                      (ProgHOL.storeByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 7)])
                        (ExpHOL.loadByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "src"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 7)])))
                      (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 8)]))))))))))
      _
      rfl rfl rfl rfl rfl rfl rfl rfl rfl (Or.inl rfl) (Or.inl rfl)
      s1 dst n wi1 hdst_small (by omega) (fun h => by cases h) hwi1_le hs1_dst hs1_n hs1_i
    rw [evaluateHOLFiniteState_seq_line780]
    rcases hr2 : evaluateHOLFiniteState s1 _ with ⟨r2, s2⟩
    rw [hr2] at hw8b
    dsimp only at hw8b ⊢
    cases r2 with
    | some _ => exact memOutsideUnchanged_trans hstep1.1 hw8b.1
    | none =>
      dsimp only
      obtain ⟨wi2, hs2_i, hwi2_le, hs2_dst, hs2_n⟩ := hw8b.2 rfl
      have hw1b := writesOnlyRange_strideWhile (ofString "dst") (ofString "i") (ofString "n")
        (BitVec.ofNat 64 1)
        (ExpHOL.cmp Cmp.lower (ExpHOL.var VarKind.local (ofString "i")) (ExpHOL.var VarKind.local (ofString "n")))
        (ProgHOL.seq
          (ProgHOL.storeByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i")])
            (ExpHOL.loadByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "src"), ExpHOL.var VarKind.local (ofString "i")])))
          (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 1)])))
        _
        rfl rfl rfl rfl rfl rfl rfl rfl rfl (Or.inr rfl) (Or.inr (Or.inl ⟨rfl, rfl⟩))
        s2 dst n wi2 hdst_small (by omega) (fun h => by cases h) hwi2_le hs2_dst hs2_n hs2_i
      rw [evaluateHOLFiniteState_seq_line780]
      rcases hr3 : evaluateHOLFiniteState s2 _ with ⟨r3, s3⟩
      rw [hr3] at hw1b
      dsimp only at hw1b ⊢
      cases r3 with
      | some _ => exact memOutsideUnchanged_trans (memOutsideUnchanged_trans hstep1.1 hw8b.1) hw1b.1
      | none =>
        dsimp only
        rw [evaluateHOLFiniteState_return]
        split
        · exact memOutsideUnchanged_trans (memOutsideUnchanged_trans hstep1.1 hw8b.1) hw1b.1
        · split <;> exact memOutsideUnchanged_trans (memOutsideUnchanged_trans hstep1.1 hw8b.1) hw1b.1

theorem memOutsideUnchanged_call_memcpy {F : Type}
    (state : PanSemStateFiniteExact 64 F) (dstExp srcExp nExp : ExpHOL 64) (dst src n : BitVec 64)
    (hcode : state.code = originalRuntimeCode)
    (hdst_small : dst.toNat + n.toNat < 2 ^ 64)
    (hn_small : n.toNat + 32 < 2 ^ 63)
    (hdst : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) dstExp = some (.val (.word dst)))
    (hsrc : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) srcExp = some (.val (.word src)))
    (hn : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) nExp = some (.val (.word n))) :
    let out := evaluateHOLFiniteState state
      (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp])
    MemOutsideUnchanged out.2.memory state.memory dst n.toNat ∧ out.2.globals = state.globals := by
  dsimp only
  have hglob := evaluate_call_pure_globals state (ofString "memcpy") [dstExp, srcExp, nExp]
    hcode lookup_memcpy (by decide)
  refine ⟨?_, hglob⟩
  rw [evaluateHOLFiniteState_call]
  have hevargs : @evalListHOLFinite 64 F _ state (fun a => Classical.propDecidable (state.memaddrs a))
      [dstExp, srcExp, nExp] = some [.val (.word dst), .val (.word src), .val (.word n)] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact, hdst, hsrc, hn]
  have hlook := pan_three_word_lookup state.code.lookup (ofString "memcpy")
    (ofString "dst") (ofString "src") (ofString "n") (sourceFnBody Guest.Software.guestFn_memcpy)
    dst src n (by decide) (by decide) (by decide) (by rw [hcode]; exact lookup_memcpy)
  rw [hevargs]
  dsimp only
  rw [hlook]
  dsimp only
  split
  · exact memOutsideUnchanged_refl _ _ _
  · set callee : HolFiniteMapExact MlS (ValueHOL 64) :=
      ((HolFiniteMapExact.empty.update (ofString "dst", .val (.word dst))).update
        (ofString "src", .val (.word src))).update (ofString "n", .val (.word n))
    have hloc_dst : (callEntryStateHOLFinite state callee).locals.lookup (ofString "dst") =
        some (.val (.word dst)) := by
      have hne1 : ofString "n" ≠ ofString "dst" := by decide
      have hne2 : ofString "src" ≠ ofString "dst" := by decide
      simp [callEntryStateHOLFinite, callee, HolFiniteMapExact.lookup_update, FUPDATE, hne1, hne2]
    have hloc_n : (callEntryStateHOLFinite state callee).locals.lookup (ofString "n") =
        some (.val (.word n)) := by
      simp [callEntryStateHOLFinite, callee, HolFiniteMapExact.lookup_update, FUPDATE]
    have hm := (memcpy_frame_body (callEntryStateHOLFinite state callee) dst n
      hdst_small hn_small hloc_dst hloc_n).1
    rcases hran : evaluateHOLFiniteState (callEntryStateHOLFinite state callee)
      (sourceFnBody Guest.Software.guestFn_memcpy) with ⟨res, post⟩
    rw [hran] at hm
    dsimp only at hm ⊢
    cases res with
    | none => exact hm
    | some r =>
      cases r with
      | returned val => dsimp only; split <;> exact hm
      | «break» | «continue» | error | timeOut | finalFfi _ | exception _ _ =>
        simpa [emptyLocalsHOLFinite, callEntryStateHOLFinite, decClockHOLFinite] using hm

def MemOutside3Unchanged (mem' mem : BitVec 64 → HolWordLab 64)
    (d1 : BitVec 64) (n1 : Nat) (d2 : BitVec 64) (n2 : Nat) (d3 : BitVec 64) (n3 : Nat) : Prop :=
  ∀ c : BitVec 64, c.toNat % 8 = 0 →
    (c.toNat + 8 ≤ d1.toNat ∨ d1.toNat + n1 ≤ c.toNat) →
    (c.toNat + 8 ≤ d2.toNat ∨ d2.toNat + n2 ≤ c.toNat) →
    (c.toNat + 8 ≤ d3.toNat ∨ d3.toNat + n3 ≤ c.toNat) →
    mem' c = mem c

theorem memOutside3Unchanged_refl (mem : BitVec 64 → HolWordLab 64)
    (d1 : BitVec 64) (n1 : Nat) (d2 : BitVec 64) (n2 : Nat) (d3 : BitVec 64) (n3 : Nat) :
    MemOutside3Unchanged mem mem d1 n1 d2 n2 d3 n3 :=
  fun _ _ _ _ _ => rfl

theorem memOutside3Unchanged_trans {m1 m2 m3 : BitVec 64 → HolWordLab 64}
    {d1 : BitVec 64} {n1 : Nat} {d2 : BitVec 64} {n2 : Nat} {d3 : BitVec 64} {n3 : Nat}
    (h12 : MemOutside3Unchanged m2 m1 d1 n1 d2 n2 d3 n3)
    (h23 : MemOutside3Unchanged m3 m2 d1 n1 d2 n2 d3 n3) :
    MemOutside3Unchanged m3 m1 d1 n1 d2 n2 d3 n3 :=
  fun c hc h1 h2 h3 => (h23 c hc h1 h2 h3).trans (h12 c hc h1 h2 h3)

theorem memOutside3Unchanged_of_1 {m2 m1 : BitVec 64 → HolWordLab 64}
    {d1 : BitVec 64} {n1 : Nat} (d2 : BitVec 64) (n2 : Nat) (d3 : BitVec 64) (n3 : Nat)
    (h : MemOutsideUnchanged m2 m1 d1 n1) :
    MemOutside3Unchanged m2 m1 d1 n1 d2 n2 d3 n3 :=
  fun c hc h1 _ _ => h c hc h1

theorem memOutside3Unchanged_of_2 {m2 m1 : BitVec 64 → HolWordLab 64}
    (d1 : BitVec 64) (n1 : Nat) {d2 : BitVec 64} {n2 : Nat} (d3 : BitVec 64) (n3 : Nat)
    (h : MemOutsideUnchanged m2 m1 d2 n2) :
    MemOutside3Unchanged m2 m1 d1 n1 d2 n2 d3 n3 :=
  fun c hc _ h2 _ => h c hc h2

theorem memOutside3Unchanged_of_3 {m2 m1 : BitVec 64 → HolWordLab 64}
    (d1 : BitVec 64) (n1 : Nat) (d2 : BitVec 64) (n2 : Nat) {d3 : BitVec 64} {n3 : Nat}
    (h : MemOutsideUnchanged m2 m1 d3 n3) :
    MemOutside3Unchanged m2 m1 d1 n1 d2 n2 d3 n3 :=
  fun c hc _ _ h3 => h c hc h3

private theorem writesOnly3_seq {F : Type} {state : PanSemStateFiniteExact 64 F}
    {p1 p2 : ProgHOL 64}
    {d1 : BitVec 64} {n1 : Nat} {d2 : BitVec 64} {n2 : Nat} {d3 : BitVec 64} {n3 : Nat}
    (h1 : MemOutside3Unchanged (evaluateHOLFiniteState state p1).2.memory state.memory d1 n1 d2 n2 d3 n3 ∧
          (evaluateHOLFiniteState state p1).2.globals = state.globals)
    (h2 : ∀ mid, evaluateHOLFiniteState state p1 = (none, mid) →
          MemOutside3Unchanged (evaluateHOLFiniteState mid p2).2.memory mid.memory d1 n1 d2 n2 d3 n3 ∧
          (evaluateHOLFiniteState mid p2).2.globals = mid.globals) :
    let out := evaluateHOLFiniteState state (.seq p1 p2)
    MemOutside3Unchanged out.2.memory state.memory d1 n1 d2 n2 d3 n3 ∧ out.2.globals = state.globals := by
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hr1 : evaluateHOLFiniteState state p1 with ⟨r1, mid⟩
  rw [hr1] at h1
  dsimp only at h1 ⊢
  cases r1 with
  | none =>
    dsimp only
    obtain ⟨hm2, hg2⟩ := h2 mid hr1
    exact ⟨memOutside3Unchanged_trans h1.1 hm2, hg2.trans h1.2⟩
  | some _ => exact h1

private def keccak256AbsorbLoopProg : ProgHOL 64 :=
  ProgHOL.while
    (ExpHOL.cmp Cmp.notLower (ExpHOL.var VarKind.local (ofString "n"))
      (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 136)]))
    (ProgHOL.seq
      (ProgHOL.call (some (none, none)) (ofString "keccak_absorb_block")
        [ExpHOL.var VarKind.local (ofString "stp"),
         ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "i")]])
      (ProgHOL.assign VarKind.local (ofString "i")
        (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 136)])))

private theorem keccak256AbsorbLoop_frame {F : Type}
    (state : PanSemStateFiniteExact 64 F) (stp pVal nVal iVal : BitVec 64)
    (hcode : state.code = originalRuntimeCode)
    (hstp_small : stp.toNat + 200 < 2 ^ 64)
    (hn_small : nVal.toNat + 136 < 2 ^ 64)
    (hi_le : iVal.toNat ≤ nVal.toNat)
    (hstp : state.locals.lookup (ofString "stp") = some (.val (.word stp)))
    (hp : state.locals.lookup (ofString "p") = some (.val (.word pVal)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word nVal)))
    (hi : state.locals.lookup (ofString "i") = some (.val (.word iVal))) :
    let out := evaluateHOLFiniteState state keccak256AbsorbLoopProg
    MemOutsideUnchanged out.2.memory state.memory stp 200 ∧
    out.2.globals = state.globals ∧
    (out.1 = none →
      ∃ iEnd : BitVec 64,
        out.2.locals.lookup (ofString "i") = some (.val (.word iEnd)) ∧
        iEnd.toNat ≤ nVal.toNat ∧
        nVal.toNat < iEnd.toNat + 136 ∧
        out.2.locals.lookup (ofString "stp") = some (.val (.word stp)) ∧
        out.2.locals.lookup (ofString "p") = some (.val (.word pVal)) ∧
        out.2.locals.lookup (ofString "n") = some (.val (.word nVal))) := by
  dsimp only
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by decide
  have hc136 : (BitVec.ofNat 64 136).toNat = 136 := rfl
  suffices hrec : ∀ (clk : Nat) (st : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      st.clock = clk →
      st.code = originalRuntimeCode →
      w.toNat ≤ nVal.toNat →
      st.locals.lookup (ofString "stp") = some (.val (.word stp)) →
      st.locals.lookup (ofString "p") = some (.val (.word pVal)) →
      st.locals.lookup (ofString "n") = some (.val (.word nVal)) →
      st.locals.lookup (ofString "i") = some (.val (.word w)) →
      MemOutsideUnchanged (evaluateHOLFiniteState st keccak256AbsorbLoopProg).2.memory st.memory stp 200 ∧
      (evaluateHOLFiniteState st keccak256AbsorbLoopProg).2.globals = st.globals ∧
      ((evaluateHOLFiniteState st keccak256AbsorbLoopProg).1 = none →
        ∃ iEnd : BitVec 64,
          (evaluateHOLFiniteState st keccak256AbsorbLoopProg).2.locals.lookup (ofString "i") = some (.val (.word iEnd)) ∧
          iEnd.toNat ≤ nVal.toNat ∧
          nVal.toNat < iEnd.toNat + 136 ∧
          (evaluateHOLFiniteState st keccak256AbsorbLoopProg).2.locals.lookup (ofString "stp") = some (.val (.word stp)) ∧
          (evaluateHOLFiniteState st keccak256AbsorbLoopProg).2.locals.lookup (ofString "p") = some (.val (.word pVal)) ∧
          (evaluateHOLFiniteState st keccak256AbsorbLoopProg).2.locals.lookup (ofString "n") = some (.val (.word nVal))) by
    exact hrec state.clock state iVal rfl hcode hi_le hstp hp hn hi
  intro clk
  induction clk using Nat.strongRecOn with
  | ind clk ih =>
    intro st w hclk hst_code hw_le hst_stp hst_p hst_n hst_i
    dsimp only [keccak256AbsorbLoopProg]
    rw [evaluateHOLFiniteState_while_total]
    have hcond : @evalHOLFinite 64 F _ st (fun a => Classical.propDecidable (st.memaddrs a))
        (ExpHOL.cmp Cmp.notLower (ExpHOL.var VarKind.local (ofString "n"))
          (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 136)])) =
        some (.val (.word (if !(decide (nVal < w + BitVec.ofNat 64 136)) then 1 else 0))) := by
      rw [evalHOLFinite_eq_toExact]
      simp [evalHOLExact, evalListHOLExact, hst_n, hst_i, valueIsWord, valueWord,
        wordOpHOL, wordOp, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    rw [hcond]
    dsimp only
    cases hb : !(decide (nVal < w + BitVec.ofNat 64 136)) with
    | false =>
      rw [if_neg (by decide)]
      have hw_add : (w + BitVec.ofNat 64 136).toNat = w.toNat + 136 := by
        rw [BitVec.toNat_add, hc136, Nat.mod_eq_of_lt (by omega)]
      have hlt : nVal.toNat < w.toNat + 136 := by
        have hdec : nVal < w + BitVec.ofNat 64 136 := by simpa using hb
        rw [BitVec.lt_def, hw_add] at hdec
        exact hdec
      exact ⟨memOutsideUnchanged_refl _ _ _, rfl, fun _ => ⟨w, hst_i, hw_le, hlt, hst_stp, hst_p, hst_n⟩⟩
    | true =>
      rw [if_pos (by decide)]
      have hw_add : (w + BitVec.ofNat 64 136).toNat = w.toNat + 136 := by
        rw [BitVec.toNat_add, hc136, Nat.mod_eq_of_lt (by omega)]
      have hge : w.toNat + 136 ≤ nVal.toNat := by
        have hdec : ¬ nVal < w + BitVec.ofNat 64 136 := by simpa using hb
        rw [BitVec.lt_def, hw_add] at hdec
        omega
      by_cases hcz : st.clock = 0
      · rw [if_pos hcz]; exact ⟨memOutsideUnchanged_refl _ _ _, rfl, fun h => by simp at h⟩
      · rw [if_neg hcz]
        rw [fixClockHOLFinite_evaluateState]
        let s1 := decClockHOLFinite st
        let body := ProgHOL.seq
          (ProgHOL.call (some (none, none)) (ofString "keccak_absorb_block")
            [ExpHOL.var VarKind.local (ofString "stp"),
             ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "i")]])
          (ProgHOL.assign VarKind.local (ofString "i")
            (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 136)]))
        have hbody_frame : MemOutsideUnchanged (evaluateHOLFiniteState s1 body).2.memory s1.memory stp 200 ∧
            (evaluateHOLFiniteState s1 body).2.globals = s1.globals := by
          apply writesOnlyRange_seq
          · exact memOutsideUnchanged_call_keccak_absorb_block s1
              (.var .local (ofString "stp"))
              (.op .add [.var .local (ofString "p"), .var .local (ofString "i")])
              stp (pVal + w) hst_code hstp_small
              (by simp [s1, decClockHOLFinite, evalHOLExact, hst_stp])
              (by simp [s1, decClockHOLFinite, evalHOLExact, evalListHOLExact, hst_p, hst_i,
                    wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero])
          · intro mid _
            refine ⟨?_, evaluate_localOnlyNoCalls_globals _ rfl mid⟩
            rw [evaluateHOLFiniteState_assign]
            split
            · exact memOutsideUnchanged_refl _ _ _
            · split <;> exact memOutsideUnchanged_refl _ _ _
        have hnc' := evaluate_noTopContinue body rfl s1
        have hnb' := evaluate_noTopBreak body rfl s1
        have hcle := evaluateHOLFiniteState_clock_le s1 body
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata s1 body).1
        have hfd_stp := evaluate_avoidsLocal_flowing (ofString "stp") body rfl s1
        have hfd_p := evaluate_avoidsLocal_flowing (ofString "p") body rfl s1
        have hfd_n := evaluate_avoidsLocal_flowing (ofString "n") body rfl s1
        have hstep_i : (evaluateHOLFiniteState s1 body).1 = none →
            (evaluateHOLFiniteState s1 body).2.locals.lookup (ofString "i") =
              some (.val (.word (w + BitVec.ofNat 64 136))) := by
          dsimp only [body]
          rw [evaluateHOLFiniteState_seq_line780]
          have hfi := evaluate_avoidsLocal_flowing (ofString "i")
            (ProgHOL.call (some (none, none)) (ofString "keccak_absorb_block")
              [ExpHOL.var VarKind.local (ofString "stp"),
               ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "i")]])
            rfl s1
          rcases hc1 : evaluateHOLFiniteState s1 _ with ⟨rc1, sc1⟩
          rw [hc1] at hfi
          dsimp only at hfi ⊢
          cases rc1 with
          | some r => intro h; cases h
          | none =>
            dsimp only
            have hsc1_i : sc1.locals.lookup (ofString "i") = some (.val (.word w)) :=
              (hfi (Or.inl rfl)).trans hst_i
            have hrun : evaluateHOLFiniteState sc1
                (ProgHOL.assign VarKind.local (ofString "i")
                  (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 136)])) =
                (none, setVarHOLFinite (ofString "i") (.val (.word (w + BitVec.ofNat 64 136))) sc1) := by
              simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hsc1_i,
                wordOpHOL, wordOp, valueIsWord, valueWord, lookupKvarHOLExact,
                isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
            rw [hrun]
            intro _
            simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        change (let r := evaluateHOLFiniteState s1 body; _)
        rcases hbr : evaluateHOLFiniteState s1 body with ⟨rb, mid⟩
        rw [hbr] at hbody_frame hnc' hnb' hcle hmeta hfd_stp hfd_p hfd_n hstep_i
        dsimp only at hbody_frame hnc' hnb' hcle hmeta hfd_stp hfd_p hfd_n hstep_i ⊢
        have hlt_clk : mid.clock < clk := by
          change mid.clock ≤ st.clock - 1 at hcle; omega
        cases rb with
        | none =>
          dsimp only
          have hmid_code : mid.code = originalRuntimeCode := hmeta.trans hst_code
          have hmid_stp : mid.locals.lookup (ofString "stp") = some (.val (.word stp)) :=
            (hfd_stp (Or.inl rfl)).trans hst_stp
          have hmid_p : mid.locals.lookup (ofString "p") = some (.val (.word pVal)) :=
            (hfd_p (Or.inl rfl)).trans hst_p
          have hmid_n : mid.locals.lookup (ofString "n") = some (.val (.word nVal)) :=
            (hfd_n (Or.inl rfl)).trans hst_n
          have hmid_i := hstep_i rfl
          have hrec_step := ih mid.clock hlt_clk mid (w + BitVec.ofNat 64 136) rfl hmid_code
            (by omega) hmid_stp hmid_p hmid_n hmid_i
          change MemOutsideUnchanged (evaluateHOLFiniteState mid keccak256AbsorbLoopProg).2.memory st.memory stp 200 ∧
            (evaluateHOLFiniteState mid keccak256AbsorbLoopProg).2.globals = st.globals ∧
            ((evaluateHOLFiniteState mid keccak256AbsorbLoopProg).1 = none → _)
          exact ⟨memOutsideUnchanged_trans hbody_frame.1 hrec_step.1,
                 hrec_step.2.1.trans hbody_frame.2, hrec_step.2.2⟩
        | some r =>
          cases r with
          | «continue» => exact False.elim (hnc' rfl)
          | «break» => exact False.elim (hnb' rfl)
          | returned _ | error | timeOut | finalFfi _ | exception _ _ =>
            exact ⟨hbody_frame.1, hbody_frame.2, fun h => by simp at h⟩

private def keccak256OutThenProg : ProgHOL 64 :=
  ProgHOL.seq
    (ProgHOL.store (ExpHOL.var VarKind.local (ofString "out"))
      (ExpHOL.load ShapeHOL.one (ExpHOL.var VarKind.local (ofString "stp"))))
    (ProgHOL.seq
      (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "out"), ExpHOL.const (BitVec.ofNat 64 8)])
        (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "stp"), ExpHOL.const (BitVec.ofNat 64 8)])))
      (ProgHOL.seq
        (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "out"), ExpHOL.const (BitVec.ofNat 64 16)])
          (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "stp"), ExpHOL.const (BitVec.ofNat 64 16)])))
        (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "out"), ExpHOL.const (BitVec.ofNat 64 24)])
          (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "stp"), ExpHOL.const (BitVec.ofNat 64 24)])))))

private def keccak256SqueezeProg : ProgHOL 64 :=
  ProgHOL.seq
    (ProgHOL.storeByte
      (ExpHOL.op BinOp.add [ExpHOL.var VarKind.global (ofString "keccak_pad"), ExpHOL.const (BitVec.ofNat 64 135)])
      (ExpHOL.op BinOp.or
        [ExpHOL.loadByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.global (ofString "keccak_pad"), ExpHOL.const (BitVec.ofNat 64 135)]),
         ExpHOL.const (BitVec.ofNat 64 128)]))
    (ProgHOL.seq
      (ProgHOL.call (some (none, none)) (ofString "keccak_absorb_block")
        [ExpHOL.var VarKind.local (ofString "stp"), ExpHOL.var VarKind.global (ofString "keccak_pad")])
      (ProgHOL.seq
        (ProgHOL.ite
          (ExpHOL.cmp Cmp.equal
            (ExpHOL.op BinOp.and [ExpHOL.var VarKind.local (ofString "out"), ExpHOL.const (BitVec.ofNat 64 7)])
            (ExpHOL.const (BitVec.ofNat 64 0)))
          keccak256OutThenProg
          (ProgHOL.call (some (none, none)) (ofString "memcpy")
            [ExpHOL.var VarKind.local (ofString "out"),
             ExpHOL.var VarKind.local (ofString "stp"),
             ExpHOL.const (BitVec.ofNat 64 32)]))
        (ProgHOL.return (ExpHOL.const (BitVec.ofNat 64 0)))))

private theorem keccak256Squeeze_frame {F : Type}
    (s7 : PanSemStateFiniteExact 64 F) (outVal stp pad : BitVec 64)
    (hs7_code : s7.code = originalRuntimeCode)
    (hstp_small : stp.toNat + 200 < 2 ^ 64)
    (hpad_small : pad.toNat + 136 < 2 ^ 64)
    (hout_small : outVal.toNat + 32 < 2 ^ 64)
    (hs7_stp : s7.locals.lookup (ofString "stp") = some (.val (.word stp)))
    (hs7_out : s7.locals.lookup (ofString "out") = some (.val (.word outVal)))
    (hs7_pad : s7.globals.lookup (ofString "keccak_pad") = some (.val (.word pad))) :
    let out := evaluateHOLFiniteState s7 keccak256SqueezeProg
    MemOutside3Unchanged out.2.memory s7.memory stp 200 pad 136 outVal 32 ∧
    out.2.globals = s7.globals := by
  dsimp only [keccak256SqueezeProg]
  have h263 : (2 ^ 63 : Nat) = 9223372036854775808 := by decide
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by decide
  have hc32 : (BitVec.ofNat 64 32).toNat = 32 := rfl
  have hc135 : (BitVec.ofNat 64 135).toNat = 135 := rfl
  apply writesOnly3_seq
  · have hpad_135 : (pad + BitVec.ofNat 64 135).toNat = pad.toNat + 135 := by
      rw [BitVec.toNat_add, hc135, Nat.mod_eq_of_lt (by omega)]
    have hm := @writesOnlyRange_byte F s7
      (ExpHOL.op BinOp.add [ExpHOL.var VarKind.global (ofString "keccak_pad"), ExpHOL.const (BitVec.ofNat 64 135)])
      (ExpHOL.op BinOp.or
        [ExpHOL.loadByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.global (ofString "keccak_pad"), ExpHOL.const (BitVec.ofNat 64 135)]),
         ExpHOL.const (BitVec.ofNat 64 128)])
      pad (pad + BitVec.ofNat 64 135) 136
      (by simp [evalHOLExact, evalListHOLExact, hs7_pad, wordOpHOL, wordOp, valueIsWord, valueWord])
      ⟨by omega, by omega⟩
    exact ⟨memOutside3Unchanged_of_2 stp 200 outVal 32 hm.1, hm.2⟩
  · intro s8 hs8
    let sb2 := ProgHOL.storeByte
      (ExpHOL.op BinOp.add [ExpHOL.var VarKind.global (ofString "keccak_pad"), ExpHOL.const (BitVec.ofNat 64 135)])
      (ExpHOL.op BinOp.or
        [ExpHOL.loadByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.global (ofString "keccak_pad"), ExpHOL.const (BitVec.ofNat 64 135)]),
         ExpHOL.const (BitVec.ofNat 64 128)])
    have hmeta8 := (PanRunBounded.evaluateHOLFiniteState_metadata s7 sb2).1
    have hfd8_stp := evaluate_avoidsLocal_flowing (ofString "stp") sb2 rfl s7
    have hfd8_out := evaluate_avoidsLocal_flowing (ofString "out") sb2 rfl s7
    have hg8 := evaluate_localOnlyNoCalls_globals sb2 rfl s7
    rw [hs8] at hmeta8 hfd8_stp hfd8_out hg8
    dsimp only at hmeta8 hfd8_stp hfd8_out hg8
    have hs8_code : s8.code = originalRuntimeCode := hmeta8.trans hs7_code
    have hs8_stp : s8.locals.lookup (ofString "stp") = some (.val (.word stp)) := (hfd8_stp (Or.inl rfl)).trans hs7_stp
    have hs8_out : s8.locals.lookup (ofString "out") = some (.val (.word outVal)) := (hfd8_out (Or.inl rfl)).trans hs7_out
    have hs8_pad : s8.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)) := by rw [hg8]; exact hs7_pad
    apply writesOnly3_seq
    · have hm := memOutsideUnchanged_call_keccak_absorb_block s8
        (.var .local (ofString "stp")) (.var .global (ofString "keccak_pad"))
        stp pad hs8_code hstp_small
        (by simp [evalHOLExact, hs8_stp]) (by simp [evalHOLExact, hs8_pad])
      exact ⟨memOutside3Unchanged_of_1 pad 136 outVal 32 hm.1, hm.2⟩
    · intro s9 hs9
      let cab := ProgHOL.call (some (none, none)) (ofString "keccak_absorb_block")
        [ExpHOL.var VarKind.local (ofString "stp"), ExpHOL.var VarKind.global (ofString "keccak_pad")]
      have hmeta9 := (PanRunBounded.evaluateHOLFiniteState_metadata s8 cab).1
      have hfd9_stp := evaluate_avoidsLocal_flowing (ofString "stp") cab rfl s8
      have hfd9_out := evaluate_avoidsLocal_flowing (ofString "out") cab rfl s8
      rw [hs9] at hmeta9 hfd9_stp hfd9_out
      dsimp only at hmeta9 hfd9_stp hfd9_out
      have hs9_code : s9.code = originalRuntimeCode := hmeta9.trans hs8_code
      have hs9_stp : s9.locals.lookup (ofString "stp") = some (.val (.word stp)) := (hfd9_stp (Or.inl rfl)).trans hs8_stp
      have hs9_out : s9.locals.lookup (ofString "out") = some (.val (.word outVal)) := (hfd9_out (Or.inl rfl)).trans hs8_out
      apply writesOnly3_seq
      · rw [evaluateHOLFiniteState_ite]
        have hev_cond : @evalHOLExact 64 F (by infer_instance) s9.toExact
            (fun a => Classical.propDecidable (s9.memaddrs a))
            (ExpHOL.cmp Cmp.equal
              (ExpHOL.op BinOp.and [ExpHOL.var VarKind.local (ofString "out"), ExpHOL.const (BitVec.ofNat 64 7)])
              (ExpHOL.const (BitVec.ofNat 64 0))) =
            some (.val (.word (if outVal &&& BitVec.ofNat 64 7 = BitVec.ofNat 64 0 then (1 : BitVec 64) else (0 : BitVec 64)))) := by
          simp [evalHOLExact, evalListHOLExact, hs9_out, wordOpHOL, wordOp, valueIsWord, valueWord,
            Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        rw [hev_cond]
        dsimp only
        by_cases hcond : (if outVal &&& BitVec.ofNat 64 7 = BitVec.ofNat 64 0 then (1 : BitVec 64) else (0 : BitVec 64)) = (0 : BitVec 64)
        · rw [if_pos hcond]
          have hm := memOutsideUnchanged_call_memcpy s9
            (.var .local (ofString "out")) (.var .local (ofString "stp")) (.const (BitVec.ofNat 64 32))
            outVal stp (BitVec.ofNat 64 32) hs9_code (by omega) (by omega)
            (by simp [evalHOLExact, hs9_out]) (by simp [evalHOLExact, hs9_stp]) (by simp [evalHOLExact])
          have hm3 : MemOutsideUnchanged
              (evaluateHOLFiniteState s9
                (.call (some (none, none)) (ofString "memcpy")
                  [.var .local (ofString "out"), .var .local (ofString "stp"), .const (BitVec.ofNat 64 32)])).2.memory
              s9.memory outVal 32 := hm.1
          exact ⟨memOutside3Unchanged_of_3 stp 200 pad 136 hm3, hm.2⟩
        · rw [if_neg hcond]
          have hm := writesOnlyRange_constBase (ofString "out") 32 keccak256OutThenProg
            rfl rfl rfl s9 outVal hout_small hs9_out
          exact ⟨memOutside3Unchanged_of_3 stp 200 pad 136 hm,
                 evaluate_localOnlyNoCalls_globals keccak256OutThenProg rfl s9⟩
      · intro s10 _
        rw [evaluateHOLFiniteState_return]
        have hev0 : @evalHOLExact 64 F (by infer_instance) s10.toExact
            (fun a => Classical.propDecidable (s10.memaddrs a))
            (ExpHOL.const (BitVec.ofNat 64 0)) = some (.val (.word (0 : BitVec 64))) := rfl
        rw [hev0]
        dsimp only
        split <;> exact ⟨memOutside3Unchanged_refl s10.memory stp 200 pad 136 outVal 32, rfl⟩

private def keccak256FinalizeProg : ProgHOL 64 :=
  ProgHOL.seq
    (ProgHOL.call (some (none, none)) (ofString "memzero")
      [ExpHOL.var VarKind.global (ofString "keccak_pad"), ExpHOL.const (BitVec.ofNat 64 136)])
    (ProgHOL.seq
      (ProgHOL.call (some (none, none)) (ofString "memcpy")
        [ExpHOL.var VarKind.global (ofString "keccak_pad"),
         ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "i")],
         ExpHOL.var VarKind.local (ofString "rem")])
      (ProgHOL.seq
        (ProgHOL.storeByte
          (ExpHOL.op BinOp.add [ExpHOL.var VarKind.global (ofString "keccak_pad"), ExpHOL.var VarKind.local (ofString "rem")])
          (ExpHOL.const (BitVec.ofNat 64 1)))
        keccak256SqueezeProg))

private theorem keccak256Finalize_frame {F : Type}
    (s4 : PanSemStateFiniteExact 64 F) (pVal iEnd rem outVal stp pad : BitVec 64)
    (hs4_code : s4.code = originalRuntimeCode)
    (hstp_small : stp.toNat + 200 < 2 ^ 64)
    (hpad_small : pad.toNat + 136 < 2 ^ 64)
    (hout_small : outVal.toNat + 32 < 2 ^ 64)
    (hrem_lt : rem.toNat < 136)
    (hs4_stp : s4.locals.lookup (ofString "stp") = some (.val (.word stp)))
    (hs4_p : s4.locals.lookup (ofString "p") = some (.val (.word pVal)))
    (hs4_i : s4.locals.lookup (ofString "i") = some (.val (.word iEnd)))
    (hs4_out : s4.locals.lookup (ofString "out") = some (.val (.word outVal)))
    (hs4_rem : s4.locals.lookup (ofString "rem") = some (.val (.word rem)))
    (hs4_pad : s4.globals.lookup (ofString "keccak_pad") = some (.val (.word pad))) :
    let out := evaluateHOLFiniteState s4 keccak256FinalizeProg
    MemOutside3Unchanged out.2.memory s4.memory stp 200 pad 136 outVal 32 ∧
    out.2.globals = s4.globals := by
  dsimp only [keccak256FinalizeProg]
  have h263 : (2 ^ 63 : Nat) = 9223372036854775808 := by decide
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by decide
  have hc136 : (BitVec.ofNat 64 136).toNat = 136 := rfl
  have hm0 := memOutsideUnchanged_call_memzero s4 (.var .global (ofString "keccak_pad"))
    (.const (BitVec.ofNat 64 136)) pad (BitVec.ofNat 64 136) hs4_code
    (by omega) (by omega) (by simp [evalHOLExact, hs4_pad]) (by simp [evalHOLExact])
  apply writesOnly3_seq
  · exact ⟨memOutside3Unchanged_of_2 stp 200 outVal 32 hm0.1, hm0.2⟩
  · intro s5 hs5
    let c4 := ProgHOL.call (some (none, none)) (ofString "memzero")
      [ExpHOL.var VarKind.global (ofString "keccak_pad"), ExpHOL.const (BitVec.ofNat 64 136)]
    have hmeta5 := (PanRunBounded.evaluateHOLFiniteState_metadata s4 c4).1
    have hfd5_stp := evaluate_avoidsLocal_flowing (ofString "stp") c4 rfl s4
    have hfd5_p := evaluate_avoidsLocal_flowing (ofString "p") c4 rfl s4
    have hfd5_i := evaluate_avoidsLocal_flowing (ofString "i") c4 rfl s4
    have hfd5_out := evaluate_avoidsLocal_flowing (ofString "out") c4 rfl s4
    have hfd5_rem := evaluate_avoidsLocal_flowing (ofString "rem") c4 rfl s4
    have hg5 := hm0.2
    rw [hs5] at hmeta5 hfd5_stp hfd5_p hfd5_i hfd5_out hfd5_rem hg5
    dsimp only at hmeta5 hfd5_stp hfd5_p hfd5_i hfd5_out hfd5_rem hg5
    have hs5_code : s5.code = originalRuntimeCode := hmeta5.trans hs4_code
    have hs5_stp : s5.locals.lookup (ofString "stp") = some (.val (.word stp)) := (hfd5_stp (Or.inl rfl)).trans hs4_stp
    have hs5_p : s5.locals.lookup (ofString "p") = some (.val (.word pVal)) := (hfd5_p (Or.inl rfl)).trans hs4_p
    have hs5_i : s5.locals.lookup (ofString "i") = some (.val (.word iEnd)) := (hfd5_i (Or.inl rfl)).trans hs4_i
    have hs5_out : s5.locals.lookup (ofString "out") = some (.val (.word outVal)) := (hfd5_out (Or.inl rfl)).trans hs4_out
    have hs5_rem : s5.locals.lookup (ofString "rem") = some (.val (.word rem)) := (hfd5_rem (Or.inl rfl)).trans hs4_rem
    have hs5_pad : s5.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)) := by rw [hg5]; exact hs4_pad
    have hm1 := memOutsideUnchanged_call_memcpy s5
      (.var .global (ofString "keccak_pad"))
      (.op .add [.var .local (ofString "p"), .var .local (ofString "i")])
      (.var .local (ofString "rem"))
      pad (pVal + iEnd) rem hs5_code (by omega) (by omega)
      (by simp [evalHOLExact, hs5_pad])
      (by simp [evalHOLExact, evalListHOLExact, hs5_p, hs5_i, wordOpHOL, wordOp, valueIsWord, valueWord])
      (by simp [evalHOLExact, hs5_rem])
    apply writesOnly3_seq
    · exact ⟨memOutside3Unchanged_of_2 stp 200 outVal 32
        (memOutsideUnchanged_mono (dst2 := pad) (len2 := 136) hm1.1 (Nat.le_refl _) (by omega)), hm1.2⟩
    · intro s6 hs6
      let c5 := ProgHOL.call (some (none, none)) (ofString "memcpy")
        [ExpHOL.var VarKind.global (ofString "keccak_pad"),
         ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "i")],
         ExpHOL.var VarKind.local (ofString "rem")]
      have hmeta6 := (PanRunBounded.evaluateHOLFiniteState_metadata s5 c5).1
      have hfd6_stp := evaluate_avoidsLocal_flowing (ofString "stp") c5 rfl s5
      have hfd6_out := evaluate_avoidsLocal_flowing (ofString "out") c5 rfl s5
      have hfd6_rem := evaluate_avoidsLocal_flowing (ofString "rem") c5 rfl s5
      have hg6 := hm1.2
      rw [hs6] at hmeta6 hfd6_stp hfd6_out hfd6_rem hg6
      dsimp only at hmeta6 hfd6_stp hfd6_out hfd6_rem hg6
      have hs6_code : s6.code = originalRuntimeCode := hmeta6.trans hs5_code
      have hs6_stp : s6.locals.lookup (ofString "stp") = some (.val (.word stp)) := (hfd6_stp (Or.inl rfl)).trans hs5_stp
      have hs6_out : s6.locals.lookup (ofString "out") = some (.val (.word outVal)) := (hfd6_out (Or.inl rfl)).trans hs5_out
      have hs6_rem : s6.locals.lookup (ofString "rem") = some (.val (.word rem)) := (hfd6_rem (Or.inl rfl)).trans hs5_rem
      have hs6_pad : s6.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)) := by rw [hg6]; exact hs5_pad
      apply writesOnly3_seq
      · have hpad_rem : (pad + rem).toNat = pad.toNat + rem.toNat := by
          rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
        have hm := @writesOnlyRange_byte F s6
          (ExpHOL.op BinOp.add [ExpHOL.var VarKind.global (ofString "keccak_pad"), ExpHOL.var VarKind.local (ofString "rem")])
          (ExpHOL.const (BitVec.ofNat 64 1))
          pad (pad + rem) 136
          (by simp [evalHOLExact, evalListHOLExact, hs6_pad, hs6_rem, wordOpHOL, wordOp, valueIsWord, valueWord])
          ⟨by omega, by omega⟩
        exact ⟨memOutside3Unchanged_of_2 stp 200 outVal 32 hm.1, hm.2⟩
      · intro s7 hs7
        let sb1 := ProgHOL.storeByte
          (ExpHOL.op BinOp.add [ExpHOL.var VarKind.global (ofString "keccak_pad"), ExpHOL.var VarKind.local (ofString "rem")])
          (ExpHOL.const (BitVec.ofNat 64 1))
        have hmeta7 := (PanRunBounded.evaluateHOLFiniteState_metadata s6 sb1).1
        have hfd7_stp := evaluate_avoidsLocal_flowing (ofString "stp") sb1 rfl s6
        have hfd7_out := evaluate_avoidsLocal_flowing (ofString "out") sb1 rfl s6
        have hg7 := evaluate_localOnlyNoCalls_globals sb1 rfl s6
        rw [hs7] at hmeta7 hfd7_stp hfd7_out hg7
        dsimp only at hmeta7 hfd7_stp hfd7_out hg7
        have hs7_code : s7.code = originalRuntimeCode := hmeta7.trans hs6_code
        have hs7_stp : s7.locals.lookup (ofString "stp") = some (.val (.word stp)) := (hfd7_stp (Or.inl rfl)).trans hs6_stp
        have hs7_out : s7.locals.lookup (ofString "out") = some (.val (.word outVal)) := (hfd7_out (Or.inl rfl)).trans hs6_out
        have hs7_pad : s7.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)) := by rw [hg7]; exact hs6_pad
        exact keccak256Squeeze_frame s7 outVal stp pad hs7_code hstp_small hpad_small hout_small hs7_stp hs7_out hs7_pad

private theorem keccak256_frame_body {F : Type}
    (state : PanSemStateFiniteExact 64 F) (pVal nVal outVal stp pad : BitVec 64)
    (hcode : state.code = originalRuntimeCode)
    (hstp_small : stp.toNat + 200 < 2 ^ 64)
    (hpad_small : pad.toNat + 136 < 2 ^ 64)
    (hout_small : outVal.toNat + 32 < 2 ^ 64)
    (hn_small : nVal.toNat + 136 < 2 ^ 64)
    (hp_loc : state.locals.lookup (ofString "p") = some (.val (.word pVal)))
    (hn_loc : state.locals.lookup (ofString "n") = some (.val (.word nVal)))
    (hout_loc : state.locals.lookup (ofString "out") = some (.val (.word outVal)))
    (hstp_glob : state.globals.lookup (ofString "keccak_st") = some (.val (.word stp)))
    (hpad_glob : state.globals.lookup (ofString "keccak_pad") = some (.val (.word pad))) :
    let out := evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_keccak256)
    MemOutside3Unchanged out.2.memory state.memory stp 200 pad 136 outVal 32 ∧
    out.2.globals = state.globals := by
  dsimp only
  have h263 : (2 ^ 63 : Nat) = 9223372036854775808 := by decide
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by decide
  have hc0 : (0 : BitVec 64).toNat = 0 := rfl
  have hc32 : (BitVec.ofNat 64 32).toNat = 32 := rfl
  have hc135 : (BitVec.ofNat 64 135).toNat = 135 := rfl
  have hc136 : (BitVec.ofNat 64 136).toNat = 136 := rfl
  have hc200 : (BitVec.ofNat 64 200).toNat = 200 := rfl
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_keccak256,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    List.map, Option.map]
  -- dec "stp"
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  have hev_stp : @evalHOLExact 64 F (by infer_instance) state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a))
      (.var .global (ofString "keccak_st")) = some (.val (.word stp)) := by
    simp [evalHOLExact, hstp_glob]
  rw [hev_stp]
  dsimp only
  have hsh_stp : shapeEqHOL .one (shapeOfHOLExact (.val (.word stp))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos hsh_stp]
  dsimp only
  set s0 := setVarHOLFinite (ofString "stp") (.val (.word stp)) state
  have hs0_stp : s0.locals.lookup (ofString "stp") = some (.val (.word stp)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs0_p : s0.locals.lookup (ofString "p") = some (.val (.word pVal)) := by
    have hne : ofString "stp" ≠ ofString "p" := by decide
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hp_loc]
  have hs0_n : s0.locals.lookup (ofString "n") = some (.val (.word nVal)) := by
    have hne : ofString "stp" ≠ ofString "n" := by decide
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hn_loc]
  have hs0_out : s0.locals.lookup (ofString "out") = some (.val (.word outVal)) := by
    have hne : ofString "stp" ≠ ofString "out" := by decide
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hout_loc]
  -- seq: memzero(stp, 200)
  let c0 := ProgHOL.call (some (none, none)) (ofString "memzero")
    [ExpHOL.var VarKind.local (ofString "stp"), ExpHOL.const (BitVec.ofNat 64 200)]
  apply writesOnly3_seq
  · have hm := memOutsideUnchanged_call_memzero s0 (.var .local (ofString "stp"))
      (.const (BitVec.ofNat 64 200)) stp (BitVec.ofNat 64 200) hcode
      (by omega) (by omega) (by simp [evalHOLExact, hs0_stp]) (by simp [evalHOLExact])
    exact ⟨memOutside3Unchanged_of_1 pad 136 outVal 32 hm.1, hm.2⟩
  · intro s1 hs1
    have hmeta1 := (PanRunBounded.evaluateHOLFiniteState_metadata s0 c0).1
    have hfd1_stp := evaluate_avoidsLocal_flowing (ofString "stp") c0 rfl s0
    have hfd1_p := evaluate_avoidsLocal_flowing (ofString "p") c0 rfl s0
    have hfd1_n := evaluate_avoidsLocal_flowing (ofString "n") c0 rfl s0
    have hfd1_out := evaluate_avoidsLocal_flowing (ofString "out") c0 rfl s0
    have hg1 := (memOutsideUnchanged_call_memzero s0 (.var .local (ofString "stp"))
      (.const (BitVec.ofNat 64 200)) stp (BitVec.ofNat 64 200) hcode
      (by omega) (by omega) (by simp [evalHOLExact, hs0_stp]) (by simp [evalHOLExact])).2
    rw [hs1] at hmeta1 hfd1_stp hfd1_p hfd1_n hfd1_out hg1
    dsimp only at hmeta1 hfd1_stp hfd1_p hfd1_n hfd1_out hg1
    have hs1_code : s1.code = originalRuntimeCode := hmeta1.trans hcode
    have hs1_stp : s1.locals.lookup (ofString "stp") = some (.val (.word stp)) := (hfd1_stp (Or.inl rfl)).trans hs0_stp
    have hs1_p : s1.locals.lookup (ofString "p") = some (.val (.word pVal)) := (hfd1_p (Or.inl rfl)).trans hs0_p
    have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word nVal)) := (hfd1_n (Or.inl rfl)).trans hs0_n
    have hs1_out : s1.locals.lookup (ofString "out") = some (.val (.word outVal)) := (hfd1_out (Or.inl rfl)).trans hs0_out
    have hs1_pad : s1.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)) := by rw [hg1]; exact hpad_glob
    -- dec "i" = 0
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    have hev0 : @evalHOLExact 64 F (by infer_instance) s1.toExact
        (fun a => Classical.propDecidable (s1.memaddrs a))
        (.const (BitVec.ofNat 64 0)) = some (.val (.word (0 : BitVec 64))) := rfl
    rw [hev0]
    dsimp only
    have hsh0 : shapeEqHOL ShapeHOL.one (shapeOfHOLExact (ValueHOL.val (HolWordLab.word (0 : BitVec 64)))) = true := by
      simp [shapeEqHOL, shapeOfHOLExact]
    rw [if_pos hsh0]
    dsimp only
    set s2 := setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) s1
    have hs2_stp : s2.locals.lookup (ofString "stp") = some (.val (.word stp)) := by
      have hne : ofString "i" ≠ ofString "stp" := by decide
      simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hs1_stp]
    have hs2_p : s2.locals.lookup (ofString "p") = some (.val (.word pVal)) := by
      have hne : ofString "i" ≠ ofString "p" := by decide
      simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hs1_p]
    have hs2_n : s2.locals.lookup (ofString "n") = some (.val (.word nVal)) := by
      have hne : ofString "i" ≠ ofString "n" := by decide
      simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hs1_n]
    have hs2_out : s2.locals.lookup (ofString "out") = some (.val (.word outVal)) := by
      have hne : ofString "i" ≠ ofString "out" := by decide
      simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hs1_out]
    have hs2_i : s2.locals.lookup (ofString "i") = some (.val (.word (0 : BitVec 64))) := by
      simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hloop_eq :
        ProgHOL.while
          (ExpHOL.cmp Cmp.notLower (ExpHOL.var VarKind.local (ofString "n"))
            (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 136)]))
          (ProgHOL.seq
            (ProgHOL.call (some (none, none)) (ofString "keccak_absorb_block")
              [ExpHOL.var VarKind.local (ofString "stp"),
               ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "i")]])
            (ProgHOL.assign VarKind.local (ofString "i")
              (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const (BitVec.ofNat 64 136)]))) =
        keccak256AbsorbLoopProg := rfl
    rw [hloop_eq]
    have hloop := keccak256AbsorbLoop_frame s2 stp pVal nVal (0 : BitVec 64)
      hs1_code hstp_small hn_small (by omega) hs2_stp hs2_p hs2_n hs2_i
    apply writesOnly3_seq
    · exact ⟨memOutside3Unchanged_of_1 pad 136 outVal 32 hloop.1, hloop.2.1⟩
    · intro s3 hs3
      have hmeta3 := (PanRunBounded.evaluateHOLFiniteState_metadata s2 keccak256AbsorbLoopProg).1
      have hfd3_out := evaluate_avoidsLocal_flowing (ofString "out") keccak256AbsorbLoopProg rfl s2
      rw [hs3] at hloop hmeta3 hfd3_out
      dsimp only at hloop hmeta3 hfd3_out
      obtain ⟨iEnd, hs3_i, hiEnd_le, hiEnd_lt, hs3_stp, hs3_p, hs3_n⟩ := hloop.2.2 rfl
      have hs3_code : s3.code = originalRuntimeCode := hmeta3.trans hs1_code
      have hs3_out : s3.locals.lookup (ofString "out") = some (.val (.word outVal)) :=
        (hfd3_out (Or.inl rfl)).trans hs2_out
      have hs3_pad : s3.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)) := by
        rw [hloop.2.1]; exact hs1_pad
      -- dec "rem" = n - i
      let rem : BitVec 64 := nVal - iEnd
      have hrem_nat : rem.toNat = nVal.toNat - iEnd.toNat := by
        simp [rem, BitVec.toNat_sub_of_le (BitVec.le_def.mpr hiEnd_le)]
      have hrem_lt : rem.toNat < 136 := by omega
      rw [evaluateHOLFiniteState_dec_total]
      dsimp only
      have hev_rem : @evalHOLExact 64 F (by infer_instance) s3.toExact
          (fun a => Classical.propDecidable (s3.memaddrs a))
          (.op .sub [.var .local (ofString "n"), .var .local (ofString "i")]) = some (.val (.word rem)) := by
        simp [evalHOLExact, evalListHOLExact, hs3_n, hs3_i, wordOpHOL, wordOp, valueIsWord, valueWord, rem]
      rw [hev_rem]
      dsimp only
      have hsh_rem : shapeEqHOL ShapeHOL.one (shapeOfHOLExact (ValueHOL.val (HolWordLab.word rem))) = true := by
        simp [shapeEqHOL, shapeOfHOLExact]
      rw [if_pos hsh_rem]
      dsimp only
      set s4 := setVarHOLFinite (ofString "rem") (.val (.word rem)) s3
      have hs4_stp : s4.locals.lookup (ofString "stp") = some (.val (.word stp)) := by
        have hne : ofString "rem" ≠ ofString "stp" := by decide
        simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hs3_stp]
      have hs4_p : s4.locals.lookup (ofString "p") = some (.val (.word pVal)) := by
        have hne : ofString "rem" ≠ ofString "p" := by decide
        simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hs3_p]
      have hs4_i : s4.locals.lookup (ofString "i") = some (.val (.word iEnd)) := by
        have hne : ofString "rem" ≠ ofString "i" := by decide
        simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hs3_i]
      have hs4_out : s4.locals.lookup (ofString "out") = some (.val (.word outVal)) := by
        have hne : ofString "rem" ≠ ofString "out" := by decide
        simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hs3_out]
      have hs4_rem : s4.locals.lookup (ofString "rem") = some (.val (.word rem)) := by
        simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hs4_pad : s4.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)) := hs3_pad
      have hfin_eq :
          ProgHOL.seq
            (ProgHOL.call (some (none, none)) (ofString "memzero")
              [ExpHOL.var VarKind.global (ofString "keccak_pad"), ExpHOL.const (BitVec.ofNat 64 136)])
            (ProgHOL.seq
              (ProgHOL.call (some (none, none)) (ofString "memcpy")
                [ExpHOL.var VarKind.global (ofString "keccak_pad"),
                 ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "i")],
                 ExpHOL.var VarKind.local (ofString "rem")])
              (ProgHOL.seq
                (ProgHOL.storeByte
                  (ExpHOL.op BinOp.add [ExpHOL.var VarKind.global (ofString "keccak_pad"), ExpHOL.var VarKind.local (ofString "rem")])
                  (ExpHOL.const (BitVec.ofNat 64 1)))
                (ProgHOL.seq
                  (ProgHOL.storeByte
                    (ExpHOL.op BinOp.add [ExpHOL.var VarKind.global (ofString "keccak_pad"), ExpHOL.const (BitVec.ofNat 64 135)])
                    (ExpHOL.op BinOp.or
                      [ExpHOL.loadByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.global (ofString "keccak_pad"), ExpHOL.const (BitVec.ofNat 64 135)]),
                       ExpHOL.const (BitVec.ofNat 64 128)]))
                  (ProgHOL.seq
                    (ProgHOL.call (some (none, none)) (ofString "keccak_absorb_block")
                      [ExpHOL.var VarKind.local (ofString "stp"), ExpHOL.var VarKind.global (ofString "keccak_pad")])
                    (ProgHOL.seq
                      (ProgHOL.ite
                        (ExpHOL.cmp Cmp.equal
                          (ExpHOL.op BinOp.and [ExpHOL.var VarKind.local (ofString "out"), ExpHOL.const (BitVec.ofNat 64 7)])
                          (ExpHOL.const (BitVec.ofNat 64 0)))
                        (ProgHOL.seq
                          (ProgHOL.store (ExpHOL.var VarKind.local (ofString "out"))
                            (ExpHOL.load ShapeHOL.one (ExpHOL.var VarKind.local (ofString "stp"))))
                          (ProgHOL.seq
                            (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "out"), ExpHOL.const (BitVec.ofNat 64 8)])
                              (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "stp"), ExpHOL.const (BitVec.ofNat 64 8)])))
                            (ProgHOL.seq
                              (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "out"), ExpHOL.const (BitVec.ofNat 64 16)])
                                (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "stp"), ExpHOL.const (BitVec.ofNat 64 16)])))
                              (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "out"), ExpHOL.const (BitVec.ofNat 64 24)])
                                (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "stp"), ExpHOL.const (BitVec.ofNat 64 24)]))))))
                        (ProgHOL.call (some (none, none)) (ofString "memcpy")
                          [ExpHOL.var VarKind.local (ofString "out"),
                           ExpHOL.var VarKind.local (ofString "stp"),
                           ExpHOL.const (BitVec.ofNat 64 32)]))
                      (ProgHOL.return (ExpHOL.const (BitVec.ofNat 64 0)))))))) =
          keccak256FinalizeProg := rfl
      rw [hfin_eq]
      exact keccak256Finalize_frame s4 pVal iEnd rem outVal stp pad
        hs3_code hstp_small hpad_small hout_small hrem_lt
        hs4_stp hs4_p hs4_i hs4_out hs4_rem hs4_pad

theorem memOutside3Unchanged_call_keccak256 {F : Type}
    (state : PanSemStateFiniteExact 64 F) (pExp nExp outExp : ExpHOL 64)
    (pVal nVal outVal stp pad : BitVec 64)
    (hcode : state.code = originalRuntimeCode)
    (hstp_small : stp.toNat + 200 < 2 ^ 64)
    (hpad_small : pad.toNat + 136 < 2 ^ 64)
    (hout_small : outVal.toNat + 32 < 2 ^ 64)
    (hn_small : nVal.toNat + 136 < 2 ^ 64)
    (hp : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) pExp = some (.val (.word pVal)))
    (hn : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) nExp = some (.val (.word nVal)))
    (hout : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) outExp = some (.val (.word outVal)))
    (hstp_glob : state.globals.lookup (ofString "keccak_st") = some (.val (.word stp)))
    (hpad_glob : state.globals.lookup (ofString "keccak_pad") = some (.val (.word pad))) :
    let out := evaluateHOLFiniteState state
      (.call (some (none, none)) (ofString "keccak256") [pExp, nExp, outExp])
    MemOutside3Unchanged out.2.memory state.memory stp 200 pad 136 outVal 32 ∧
    out.2.globals = state.globals := by
  dsimp only
  rw [evaluateHOLFiniteState_call]
  have hevargs : @evalListHOLFinite 64 F _ state (fun a => Classical.propDecidable (state.memaddrs a))
      [pExp, nExp, outExp] = some [.val (.word pVal), .val (.word nVal), .val (.word outVal)] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact, hp, hn, hout]
  have hlook := pan_three_word_lookup state.code.lookup (ofString "keccak256")
    (ofString "p") (ofString "n") (ofString "out") (sourceFnBody Guest.Software.guestFn_keccak256)
    pVal nVal outVal (by decide) (by decide) (by decide) (by rw [hcode]; exact lookup_keccak256)
  rw [hevargs]
  dsimp only
  rw [hlook]
  dsimp only
  split
  · exact ⟨memOutside3Unchanged_refl state.memory stp 200 pad 136 outVal 32, rfl⟩
  · set callee : HolFiniteMapExact MlS (ValueHOL 64) :=
      ((HolFiniteMapExact.empty.update (ofString "p", .val (.word pVal))).update
        (ofString "n", .val (.word nVal))).update (ofString "out", .val (.word outVal))
    have hloc_p : (callEntryStateHOLFinite state callee).locals.lookup (ofString "p") =
        some (.val (.word pVal)) := by
      have hne1 : ofString "out" ≠ ofString "p" := by decide
      have hne2 : ofString "n" ≠ ofString "p" := by decide
      simp [callEntryStateHOLFinite, callee, HolFiniteMapExact.lookup_update, FUPDATE, hne1, hne2]
    have hloc_n : (callEntryStateHOLFinite state callee).locals.lookup (ofString "n") =
        some (.val (.word nVal)) := by
      have hne1 : ofString "out" ≠ ofString "n" := by decide
      simp [callEntryStateHOLFinite, callee, HolFiniteMapExact.lookup_update, FUPDATE, hne1]
    have hloc_out : (callEntryStateHOLFinite state callee).locals.lookup (ofString "out") =
        some (.val (.word outVal)) := by
      simp [callEntryStateHOLFinite, callee, HolFiniteMapExact.lookup_update, FUPDATE]
    have hbf := keccak256_frame_body (callEntryStateHOLFinite state callee) pVal nVal outVal stp pad
      hcode hstp_small hpad_small hout_small hn_small hloc_p hloc_n hloc_out hstp_glob hpad_glob
    rcases hran : evaluateHOLFiniteState (callEntryStateHOLFinite state callee)
      (sourceFnBody Guest.Software.guestFn_keccak256) with ⟨res, post⟩
    rw [hran] at hbf
    dsimp only at hbf ⊢
    cases res with
    | none =>
      exact ⟨hbf.1, hbf.2⟩
    | some r =>
      cases r with
      | returned val =>
        dsimp only
        split <;> exact ⟨hbf.1, hbf.2⟩
      | «break» | «continue» | error | timeOut | finalFfi _ | exception _ _ =>
        simpa [emptyLocalsHOLFinite, callEntryStateHOLFinite, decClockHOLFinite] using hbf

end InitECandidate.Solver.GuestBoundHtab
