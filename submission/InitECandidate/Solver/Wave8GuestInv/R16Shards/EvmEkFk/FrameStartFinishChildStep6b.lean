import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.FrameStartFinishChildStep6m

set_option Elab.async false
set_option autoImplicit false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8Contracts.M23 (GlobalsKept)
open InitECandidate.Solver.Wave8GuestInv.R11Shards

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 2400000

def FcLogsSelfDisj {F : Type} (s0 st : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ o ∈ frameLogObjects st (globN s0 "ev", globN s0 "cur_cont"),
    Disj (frameLogs st (globN s0 "ev", globN s0 "cur_cont")) o

private theorem memW_congr_6b {F : Type} {a b : PanSemStateFiniteExact 64 F}
    (hm : a.memory = b.memory) :
    ∀ x, memW a x = memW b x := by
  intro x; unfold memW; rw [hm]

private theorem globN_congr_6b {F : Type} {a b : PanSemStateFiniteExact 64 F}
    (hg : a.globals = b.globals) :
    ∀ k, globN a k = globN b k := by
  intro k; unfold globN; rw [hg]

private theorem frameObjects_congr_6b {F : Type} {a b : PanSemStateFiniteExact 64 F}
    (hm : a.memory = b.memory) (hg : a.globals = b.globals) :
    ∀ ec, frameObjects a ec = frameObjects b ec := by
  have hmw := funext (memW_congr_6b hm)
  have hgn := funext (globN_congr_6b hg)
  intro ec
  simp only [frameObjects, frameLogs, frameRet, frameLogObjects, logOwnedIvls, logRecordIvls, hmw, hgn]

private theorem htabFootprint_congr_6b {F : Type} {a b : PanSemStateFiniteExact 64 F}
    (hm : a.memory = b.memory) :
    ∀ t, htabFootprint a t = htabFootprint b t := by
  have hmw := funext (memW_congr_6b hm)
  intro t; simp only [htabFootprint, hdr, hmw]

private theorem fixedObjects_congr_6b {F : Type} {a b : PanSemStateFiniteExact 64 F}
    (hm : a.memory = b.memory) (hg : a.globals = b.globals) :
    fixedObjects a = fixedObjects b := by
  have hmw := funext (memW_congr_6b hm)
  have hgn := funext (globN_congr_6b hg)
  simp only [fixedObjects, blockOutObjects, balObjects, balRecords, htabValues, lstObjects,
    hdr, nodeF, hmw, hgn]

theorem m08_memW_cell_6b {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {base sz off : Nat}
    (hu : M08IvlUnhit6a s post (base, sz))
    (hbase8 : base % 8 = 0) (hbnd : base + sz ≤ 2 ^ 64)
    (hoff : off + 8 ≤ sz) (hoff8 : off % 8 = 0) :
    memW post (base + off) = memW s (base + off) :=
  InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hu
    (by omega) hbnd ⟨by dsimp only; omega, by dsimp only; omega⟩

def FcIncorpSuccessStepW' : Prop :=
  ∀ {F : Type} {s0 st : PanSemStateFiniteExact 64 F} {S : List Nat},
    FcBranchState s0 st S →
    FcPoppedChild s0 st S →
    FcLogsSelfDisj s0 st →
    OpDispatchSpec.evmR st + (memW st (globN s0 "ev" + 64) + memW st (globN s0 "ev" + 192)) ≤
      OpDispatchSpec.evmR s0 →
    OpDispatchSpec.evmR st + (memW st (globN s0 "ev" + 64) + memW st (globN s0 "ev" + 192)) + 1 <
      2 ^ 64 →
    (evaluateHOLFiniteState st
      (.call (some (none, none)) (ofString "incorporate_child_on_success")
        [.var .local (ofString "child")])).1 ≠ some .timeOut →
    let prog : ProgHOL 64 :=
      .call (some (none, none)) (ofString "incorporate_child_on_success")
        [.var .local (ofString "child")]
    (∀ u, (evaluateHOLFiniteState st prog).1 ≠ some (.returned u)) ∧
    ¬ OpDispatchSpec.IsEvmErr (evaluateHOLFiniteState st prog).1 ∧
    ((evaluateHOLFiniteState st prog).1 = none →
      let post := (evaluateHOLFiniteState st prog).2
      ∃ S', FcBranchState s0 post S' ∧
        post.locals = st.locals ∧
        GlobalsKept ["heap_ptr"] st post ∧
        evmChain post = evmChain st ∧
        OpDispatchSpec.evmR post ≤
          OpDispatchSpec.evmR st + (memW st (globN s0 "ev" + 64) + memW st (globN s0 "ev" + 192)) ∧
        Inside (globN s0 "ev", 280) (globN post "scratch_ptr") scratchEnd ∧
        WordsOK post (globN s0 "ev", 280) ∧
        memW post (globN post "ev" + 16) = memW st (globN st "ev" + 16) ∧
        memW post (globN post "ev" + 40) = memW st (globN st "ev" + 40) ∧
        memW post (globN post "ev" + 232) = memW st (globN st "ev" + 232))

theorem incorporate_child_on_success_fc_step : FcIncorpSuccessStepW' := by
  intro F s0 st S hBS hPC hLSD hr_sum hgas_sum hnt
  dsimp only
  obtain ⟨hne_ret, hnone, herr⟩ := call0_outcome_fc (s := st)
    (fname := ofString "incorporate_child_on_success")
    (args := [.var .local (ofString "child")]) hnt
  have hcode : st.code = originalRuntimeCode := hBS.arena.1.code
  have harg : evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a))
      [.var .local (ofString "child")] =
      some [.val (.word (BitVec.ofNat 64 (globN s0 "ev")))] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact, evalHOLExact, hBS.locals_ok.child_lk]
  have hno_err : ¬ OpDispatchSpec.IsEvmErr (evaluateHOLFiniteState st
      (.call (some (none, none)) (ofString "incorporate_child_on_success")
        [.var .local (ofString "child")])).1 := by
    intro he
    obtain ⟨vals, body, cal, ret, v, cpost, hargs, hl, hrun, _⟩ := herr he
    rw [harg] at hargs; injection hargs with hvals; subst hvals
    have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup
        (ofString "incorporate_child_on_success") [.val (.word (BitVec.ofNat 64 (globN s0 "ev")))] =
        some (body, cal, ret) := by rwa [← hcode]
    obtain ⟨rfl, _, _, _, _⟩ :=
      R14Shards.OpHandlersA.one_word_arg_lookup lookup_incorporate_child_on_success_6a hl_orig
    exact StateRestoreEpilogue.evaluate_noCatchableRaise
      incorpSuccessCallees incorpSuccessCallees_good
      (sourceFnBody Guest.Software.guestFn_incorporate_child_on_success) (by decide)
      (callEntryStateHOLFinite st cal) hcode (ofString "EvmErr") v (by decide) (by rw [hrun])
  refine ⟨hne_ret, hno_err, fun hn => ?_⟩
  obtain ⟨vals, body, cal, ret, rv, cpost, hargs, hl, hrun, hpost_eq⟩ := hnone hn
  rw [harg] at hargs; injection hargs with hvals; subst hvals
  have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "incorporate_child_on_success") [.val (.word (BitVec.ofNat 64 (globN s0 "ev")))] =
      some (body, cal, ret) := by rwa [← hcode]
  obtain ⟨rfl, _, w_ch, hw_ch, hcal_child⟩ :=
    R14Shards.OpHandlersA.one_word_arg_lookup lookup_incorporate_child_on_success_6a hl_orig
  injection hw_ch with hw_ch'; injection hw_ch' with hw_ch_eq; subst hw_ch_eq
  obtain ⟨he_bnd, he_wok, he_lk, he_sp, hR_st⟩ := ev_head_facts_6a hBS.arena hBS.inv
  have hchild_bnd : globN s0 "ev" + 280 ≤ 2 ^ 64 := fcPoppedChild_child_bound hBS hPC
  set e0 := globN st "ev"
  set ch := globN s0 "ev"
  have he_nat : (BitVec.ofNat 64 e0).toNat = e0 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hch_nat : (BitVec.ofNat 64 ch).toNat = ch := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hhead_st : (e0, globN st "cur_cont") ∈ evmChain st := by
    rw [evmChain_cons]; exact List.mem_cons_self
  have hdisj_ch_ev : Disj (ch, 280) (e0, 280) :=
    hPC.child_disj_fo _ hhead_st (e0, 280) (by simp [frameObjects])
  set s0_c := callEntryStateHOLFinite st cal
  -- AST decomposition of guestFn_incorporate_child_on_success
  let pErr : ProgHOL 64 :=
    .call (some (none, none)) (ofString "incorporate_child_on_error") [.var .local (ofString "child")]
  let p192a : ProgHOL 64 :=
    .store (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 192)])
      (.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 192)]),
                 .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 192)])])
  let pIteRep : ProgHOL 64 :=
    .ite (.cmp .lower (.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 192)]))
            (.var .local (ofString "rep")))
      (.assign .local (ofString "rep")
        (.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 192)])))
      .skip
  let p64 : ProgHOL 64 :=
    .store (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 64)])
      (.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 64)]),
                 .var .local (ofString "rep")])
  let p72 : ProgHOL 64 :=
    .store (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 72)])
      (.op .sub [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 72)]),
                 .var .local (ofString "rep")])
  let p192b : ProgHOL 64 :=
    .store (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 192)])
      (.op .sub [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 192)]),
                 .var .local (ofString "rep")])
  let p96 : ProgHOL 64 :=
    .store (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 96)])
      (.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 96)]),
                 .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 96)])])
  let pUnion : ProgHOL 64 :=
    .call (some (none, none)) (ofString "htab_union_into")
      [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 136)]),
       .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 136)])]
  let pTail : ProgHOL 64 := .seq p96 (.seq pUnion (.return (.const 0#64)))
  let pLogs : ProgHOL 64 :=
    .dec (ofString "cl") .one (.load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 88)]))
      (.dec (ofString "n") .one (.load .one (.op .add [.var .local (ofString "cl"), .const (BitVec.ofNat 64 8)]))
        (.dec (ofString "p") .one (.load .one (.op .add [.var .local (ofString "cl"), .const (BitVec.ofNat 64 0)]))
          (.dec (ofString "i") .one (.const 0#64)
            (.seq logAppendWhileProg6 pTail))))
  have hbody_eq : sourceFnBody Guest.Software.guestFn_incorporate_child_on_success =
      .seq pErr
        (.seq p192a
          (.dec (ofString "rep") .one
            (.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 72)]))
            (.seq pIteRep (.seq p64 (.seq p72 (.seq p192b pLogs)))))) := rfl
  change evaluateHOLFiniteState s0_c
    (sourceFnBody Guest.Software.guestFn_incorporate_child_on_success) =
    (some (.returned rv), cpost) at hrun
  rw [hbody_eq, evaluateHOLFiniteState_seq_line780] at hrun
  -- Step 1: pErr = incorporate_child_on_error(child)
  rcases hr1 : evaluateHOLFiniteState s0_c pErr with ⟨res1, s1⟩
  rw [hr1] at hrun
  have hnt1 : res1 ≠ some .timeOut := by
    intro ht; rw [ht] at hrun; cases (Prod.mk.inj hrun).1
  have hres1_none : res1 = none := by
    cases res1 with
    | none => rfl
    | some r =>
      dsimp only at hrun
      injection hrun with hr_eq _
      cases r with
      | returned u =>
        exact absurd hr1.symm (by
          have := call0_ne_returned_fc s0_c (ofString "incorporate_child_on_error")
            [.var .local (ofString "child")] u
          intro heq; exact this (congrArg Prod.fst heq.symm))
      | _ => cases hr_eq
  subst hres1_none
  dsimp only at hrun
  have hcal_child' : s0_c.locals.lookup (ofString "child") =
      some (.val (.word (BitVec.ofNat 64 ch))) := hcal_child
  have harg_c : evalListHOLFinite s0_c (h := fun a => Classical.propDecidable (s0_c.memaddrs a))
      [.var .local (ofString "child")] =
      some [.val (.word (BitVec.ofNat 64 ch))] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact, evalHOLExact, hcal_child']
  have hA0 : ArenaReady s0_c :=
    ⟨guestInv_with_locals_clock st cal _ hBS.arena.1, hBS.arena.2⟩
  have hInv0 : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt s0_c S := by
    have hwt0 : WorldTyped s0_c S ↔ WorldTyped st S :=
      StateRestoreEpilogue.worldTyped_lc st cal s0_c.clock S
    have hch0 : evmChain s0_c = evmChain st := evmChain_lc_fc st cal s0_c.clock
    have hE := hBS.inv
    dsimp only [InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt] at hE ⊢
    simp only [FrameWF, MsgOwned, hwt0, hch0] at hE ⊢
    exact hE
  have hRel0 := (releaseReadyAt_lc st cal s0_c.clock S _ _).2 hBS.release
  have hR0 : OpDispatchSpec.evmR s0_c = OpDispatchSpec.evmR st := evmR_lc_fc st cal s0_c.clock
  have hs0_c_gn : globN s0_c "ev" = e0 := rfl
  have hgas_err : OpDispatchSpec.evmR s0_c + memW s0_c (ch + 64) + 1 < 2 ^ 64 := by
    rw [hR0]; change OpDispatchSpec.evmR st + memW st (ch + 64) + 1 < 2 ^ 64; omega
  obtain ⟨_, _, hnone1⟩ := incorporate_child_on_error_call_core
    hA0 hInv0 hRel0 harg_c hPC.child_scr.2 hchild_bnd hgas_err (by rw [hr1]; simp)
  have h1_facts := hnone1 (by rw [hr1])
  have hs1_eq_ev : (evaluateHOLFiniteState s0_c pErr).2 = s1 := by rw [hr1]
  rw [hs1_eq_ev, hs0_c_gn] at h1_facts
  obtain ⟨hA1, hInv1, _hRel1, hs1_loc, hs1_glob, hs1_be, hs1_ch, hs1_R, hs1_m64, hs1_mem⟩ := h1_facts
  have hs1_gn : globN s1 "ev" = e0 := by unfold globN; rw [hs1_glob]; rfl
  have hs1_ev : s1.globals.lookup (ofString "ev") = some (.val (.word (BitVec.ofNat 64 e0))) := by
    rw [hs1_glob]; exact he_lk
  have hs1_ewok : WordsOK s1 (e0, 280) := by
    have hhead1 : (globN s1 "ev", globN s1 "cur_cont") ∈ evmChain s1 := by
      rw [evmChain_cons]; exact List.mem_cons_self
    have hw := (hInv1.2.2.2.2.1 _ hhead1).1 (globN s1 "ev", 280) (by simp)
    rw [hs1_gn] at hw; exact hw.2
  have hs1_child_lk : s1.locals.lookup (ofString "child") =
      some (.val (.word (BitVec.ofNat 64 ch))) := by
    rw [hs1_loc]; exact hcal_child
  have hs1_child_mem : ∀ x : BitVec 64,
      (∀ off : Nat, off = 64 ∨ off = 72 ∨ off = 184 → x ≠ BitVec.ofNat 64 (e0 + off)) →
      s1.memory x = st.memory x := by
    intro x hx
    exact hs1_mem x (hx 64 (Or.inl rfl)) (hx 72 (Or.inr (Or.inl rfl))) (hx 184 (Or.inr (Or.inr rfl)))
  have hch_ne_ev : ∀ off1 off2 : Nat, off1 + 8 ≤ 280 → off2 + 8 ≤ 280 →
      BitVec.ofNat 64 (ch + off1) ≠ BitVec.ofNat 64 (e0 + off2) := by
    intro off1 off2 ho1 ho2 heq
    have hn := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hn
    dsimp only [Disj] at hdisj_ch_ev; omega
  have hs1_cwok : WordsOK s1 (ch, 280) := by
    refine ⟨hPC.child_scr.2.1, hPC.child_scr.2.2.1, fun k hk => ?_⟩
    obtain ⟨wk, hdom, hm⟩ := hPC.child_scr.2.2.2 k hk
    refine ⟨wk, ?_, ?_⟩
    · rw [hA1.1.memaddrs, ← hBS.arena.1.memaddrs]; exact hdom
    · dsimp only at hm ⊢
      rw [hs1_mem _ (hch_ne_ev (8 * k) 64 (by omega) (by omega))
        (hch_ne_ev (8 * k) 72 (by omega) (by omega))
        (hch_ne_ev (8 * k) 184 (by omega) (by omega))]
      exact hm
  have hs1_m192 : memW s1 (e0 + 192) = memW st (e0 + 192) := by
    unfold memW
    rw [hs1_mem (BitVec.ofNat 64 (e0 + 192))]
    · rfl
    all_goals
      intro heq; have hn := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show e0 + 192 < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show e0 + 64 < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show e0 + 72 < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show e0 + 184 < 2 ^ 64 by omega)] at hn; omega
  have hs1_cm192 : memW s1 (ch + 192) = memW st (ch + 192) := by
    unfold memW
    rw [hs1_mem _ (hch_ne_ev 192 64 (by omega) (by omega))
      (hch_ne_ev 192 72 (by omega) (by omega))
      (hch_ne_ev 192 184 (by omega) (by omega))]; rfl
  -- Step 2: p192a = store (ev + 192) ((ev + 192) + (child + 192))
  rw [evaluateHOLFiniteState_seq_line780] at hrun
  have hr2_eta := Prod.mk.eta (p := evaluateHOLFiniteState s1 p192a)
  set r2 := (evaluateHOLFiniteState s1 p192a).1
  set s2 := (evaluateHOLFiniteState s1 p192a).2
  rw [← hr2_eta] at hrun
  cases hr2 : r2 with
  | some res2 =>
    rw [hr2] at hr2_eta hrun
    have herr2 := R14Shards.OpHandlersA.store_some_eq_error' hr2_eta.symm
    subst herr2; cases (Prod.mk.inj hrun).1
  | none =>
    rw [hr2] at hr2_eta hrun; dsimp only at hrun
    have ha2 := eval_load_ev_off_6a s1 hs1_ev hs1_ewok he_bnd
      (off := 192) (by omega) (by omega)
    have hb2 := eval_load_local_off_6a s1 hs1_child_lk hs1_cwok hchild_bnd
      (off := 192) (by omega) (by omega)
    have hs2_eq := fc_store_add_words hs1_ev (by rw [hs1_gn]; exact he_nat)
      (by rw [hs1_gn]; omega) ha2 hb2 hr2_eta.symm
    have hs2_gn : globN s2 "ev" = e0 := by rw [hs2_eq]; exact hs1_gn
    have hs2_ev : s2.globals.lookup (ofString "ev") = some (.val (.word (BitVec.ofNat 64 e0))) := by
      rw [hs2_eq]; exact hs1_ev
    have hs2_ewok : WordsOK s2 (e0, 280) := by rw [hs2_eq]; exact wordsOK_updW_6a s1 hs1_ewok _ _
    have hs2_cwok : WordsOK s2 (ch, 280) := by rw [hs2_eq]; exact wordsOK_updW_6a s1 hs1_cwok _ _
    have hs2_child_lk : s2.locals.lookup (ofString "child") =
        some (.val (.word (BitVec.ofNat 64 ch))) := by rw [hs2_eq]; exact hs1_child_lk
    have hsp192_lt : memW st (e0 + 192) + memW st (ch + 192) < 2 ^ 64 := by
      rw [hR_st] at hgas_sum; omega
    have hs2_m192 : memW s2 (e0 + 192) = memW st (e0 + 192) + memW st (ch + 192) := by
      rw [hs2_eq, hs1_gn, R14Shards.OpHandlersA.memW_updW_same s1 (e0 + 192) _,
        hs1_m192, hs1_cm192]
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show memW st (e0 + 192) < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show memW st (ch + 192) < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt hsp192_lt]
    have hs2_m64 : memW s2 (e0 + 64) = memW st (e0 + 64) + memW st (ch + 64) := by
      rw [hs2_eq, hs1_gn,
        R14Shards.OpHandlersA.memW_updW_ne s1 (e0 + 192) (e0 + 64) _ (by omega) (by omega) (by omega)]
      exact hs1_m64
    -- Step 3: dec "rep" (load one (ev + 72))
    rw [evaluateHOLFiniteState_dec_total] at hrun; dsimp only at hrun
    have hld_72 := eval_load_ev_off_6a s2 hs2_ev hs2_ewok he_bnd
      (off := 72) (by omega) (by omega)
    rw [hld_72] at hrun; dsimp only at hrun
    set r72 := memW s2 (e0 + 72)
    have hr72_lt : r72 < 2 ^ 64 := OpDispatchSpec.memW_lt s2 (e0 + 72)
    have hsh_rep : shapeEqHOL .one (shapeOfHOLExact (.val (.word (BitVec.ofNat 64 r72)) : ValueHOL 64)) = true := by
      simp [shapeEqHOL, shapeOfHOLExact]
    rw [if_pos hsh_rep] at hrun
    set s3 := setVarHOLFinite (ofString "rep") (.val (.word (BitVec.ofNat 64 r72))) s2
    let pRest3 : ProgHOL 64 := .seq pIteRep (.seq p64 (.seq p72 (.seq p192b pLogs)))
    rcases hrun3 : evaluateHOLFiniteState s3 pRest3 with ⟨res3, s_end3⟩
    rw [hrun3] at hrun; dsimp only at hrun
    have hres3_eq : res3 = some (.returned rv) := (Prod.mk.inj hrun).1
    let L_rep := HolFiniteMapExact.resVarEq s_end3.locals (ofString "rep", s2.locals.lookup (ofString "rep"))
    have hcpost_s3 : { s_end3 with locals := L_rep } = cpost := (Prod.mk.inj hrun).2
    rw [hres3_eq] at hrun3
    -- Step 4: pIteRep on s3
    dsimp only [pRest3] at hrun3
    rw [evaluateHOLFiniteState_seq_line780] at hrun3
    have hs3_ev : s3.globals.lookup (ofString "ev") = some (.val (.word (BitVec.ofNat 64 e0))) := hs2_ev
    have hs3_gn : globN s3 "ev" = e0 := hs2_gn
    have hs3_ewok : WordsOK s3 (e0, 280) := hs2_ewok
    have hs3_rep_lk : s3.locals.lookup (ofString "rep") =
        some (.val (.word (BitVec.ofNat 64 r72))) := by
      simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hld_192_s3 := eval_load_ev_off_6a s3 hs3_ev hs3_ewok he_bnd
      (off := 192) (by omega) (by omega)
    have hs3_m192 : memW s3 (e0 + 192) = memW s2 (e0 + 192) := rfl
    rw [hs3_m192] at hld_192_s3
    set sp192 := memW s2 (e0 + 192)
    have hsp192_lt' : sp192 < 2 ^ 64 := by rw [hs2_m192]; exact hsp192_lt
    have hcmp_rep : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
        (.cmp .lower (.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 192)]))
          (.var .local (ofString "rep"))) =
        some (.val (.word (if BitVec.ofNat 64 sp192 < BitVec.ofNat 64 r72 then 1#64 else 0#64))) := by
      unfold evalHOLExact
      have hr_lk : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
          (.var .local (ofString "rep")) = some (.val (.word (BitVec.ofNat 64 r72))) := hs3_rep_lk
      rw [hld_192_s3, hr_lk]
      simp [Compiler.Encoders.Asm.wordCmpHOL]
    set repVal : Nat := if sp192 < r72 then sp192 else r72
    have hrep_le_72 : repVal ≤ r72 := by dsimp only [repVal]; split <;> omega
    have hrep_le_192 : repVal ≤ sp192 := by dsimp only [repVal]; split <;> omega
    have hrep_lt64 : repVal < 2 ^ 64 := by omega
    have hite_step : ∃ s4 : PanSemStateFiniteExact 64 F,
        evaluateHOLFiniteState s3 pIteRep = (none, s4) ∧
        s4.memory = s2.memory ∧ s4.globals = s2.globals ∧ s4.be = s2.be ∧
        s4.memaddrs = s2.memaddrs ∧ s4.shMemaddrs = s2.shMemaddrs ∧
        s4.code = s2.code ∧ s4.baseAddr = s2.baseAddr ∧
        s4.locals.lookup (ofString "rep") = some (.val (.word (BitVec.ofNat 64 repVal))) ∧
        s4.locals.lookup (ofString "child") = some (.val (.word (BitVec.ofNat 64 ch))) := by
      dsimp only [pIteRep]
      rw [evaluateHOLFiniteState_ite, hcmp_rep]; dsimp only
      have hlt_iff : (BitVec.ofNat 64 sp192 < BitVec.ofNat 64 r72) ↔ sp192 < r72 := by
        rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hsp192_lt', Nat.mod_eq_of_lt hr72_lt]
      by_cases hlt : sp192 < r72
      · have hlt_bv : BitVec.ofNat 64 sp192 < BitVec.ofNat 64 r72 := hlt_iff.2 hlt
        have h10 : ¬ ((1#64 : BitVec 64) = 0) := by decide
        simp only [hlt_bv, ↓reduceIte, h10]
        rw [evaluateHOLFiniteState_assign, hld_192_s3]; dsimp only
        have hvalid : s3.isValidValueHOLFinite .local (ofString "rep")
            (.val (.word (BitVec.ofNat 64 sp192))) = true := by
          simp [isValidValueHOLFinite, lookupKvarHOLExact, hs3_rep_lk, shapeOfHOLExact, shapeEqHOL]
        rw [if_pos hvalid]
        refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
        · dsimp only [repVal]; rw [if_pos hlt]
          simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        · simp [s3, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_child_lk,
            show ofString "rep" ≠ ofString "child" by decide]
      · have hlt_bv : ¬ (BitVec.ofNat 64 sp192 < BitVec.ofNat 64 r72) := fun h => hlt (hlt_iff.1 h)
        simp only [hlt_bv, ↓reduceIte, evaluateHOLFiniteState_skip]
        refine ⟨s3, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
        · dsimp only [repVal]; rw [if_neg hlt]; exact hs3_rep_lk
        · simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_child_lk,
            show ofString "rep" ≠ ofString "child" by decide]
    obtain ⟨s4, hs4_ev_ite, hs4_mem, hs4_glob, hs4_be, hs4_dom, hs4_sh, hs4_code, hs4_ba,
      hs4_rep_lk, hs4_child_lk⟩ := hite_step
    rw [hs4_ev_ite] at hrun3; dsimp only at hrun3
    -- Step 5: p64, p72, p192b on s4 -> s5 -> s6 -> s7
    have hs4_gn : globN s4 "ev" = e0 := by unfold globN; rw [hs4_glob]; exact hs2_gn
    have hs4_ev : s4.globals.lookup (ofString "ev") = some (.val (.word (BitVec.ofNat 64 e0))) := by
      rw [hs4_glob]; exact hs2_ev
    have hs4_ewok : WordsOK s4 (e0, 280) := wordsOK_of_unhit_6a hs4_dom hs2_ewok
    rw [evaluateHOLFiniteState_seq_line780] at hrun3
    have hr5_eta := Prod.mk.eta (p := evaluateHOLFiniteState s4 p64)
    set r5 := (evaluateHOLFiniteState s4 p64).1
    set s5 := (evaluateHOLFiniteState s4 p64).2
    rw [← hr5_eta] at hrun3
    cases hr5 : r5 with
    | some res5 =>
      rw [hr5] at hr5_eta hrun3
      have herr5 := R14Shards.OpHandlersA.store_some_eq_error' hr5_eta.symm
      subst herr5; cases (Prod.mk.inj hrun3).1
    | none =>
      rw [hr5] at hr5_eta hrun3; dsimp only at hrun3
      have ha5 := eval_load_ev_off_6a s4 hs4_ev hs4_ewok he_bnd
        (off := 64) (by omega) (by omega)
      have hb5 : @evalHOLExact 64 F _ s4.toExact (fun a => Classical.propDecidable (s4.memaddrs a))
          (.var .local (ofString "rep")) = some (.val (.word (BitVec.ofNat 64 repVal))) := hs4_rep_lk
      have hs5_eq := fc_store_add_words hs4_ev (by rw [hs4_gn]; exact he_nat)
        (by rw [hs4_gn]; omega) ha5 hb5 hr5_eta.symm
      have hs5_gn : globN s5 "ev" = e0 := by rw [hs5_eq]; exact hs4_gn
      have hs5_ev : s5.globals.lookup (ofString "ev") = some (.val (.word (BitVec.ofNat 64 e0))) := by
        rw [hs5_eq]; exact hs4_ev
      have hs5_ewok : WordsOK s5 (e0, 280) := by rw [hs5_eq]; exact wordsOK_updW_6a s4 hs4_ewok _ _
      have hs5_rep_lk : s5.locals.lookup (ofString "rep") =
          some (.val (.word (BitVec.ofNat 64 repVal))) := by rw [hs5_eq]; exact hs4_rep_lk
      rw [evaluateHOLFiniteState_seq_line780] at hrun3
      have hr6_eta := Prod.mk.eta (p := evaluateHOLFiniteState s5 p72)
      set r6 := (evaluateHOLFiniteState s5 p72).1
      set s6 := (evaluateHOLFiniteState s5 p72).2
      rw [← hr6_eta] at hrun3
      cases hr6 : r6 with
      | some res6 =>
        rw [hr6] at hr6_eta hrun3
        have herr6 := R14Shards.OpHandlersA.store_some_eq_error' hr6_eta.symm
        subst herr6; cases (Prod.mk.inj hrun3).1
      | none =>
        rw [hr6] at hr6_eta hrun3; dsimp only at hrun3
        have ha6 := eval_load_ev_off_6a s5 hs5_ev hs5_ewok he_bnd
          (off := 72) (by omega) (by omega)
        have hb6 : @evalHOLExact 64 F _ s5.toExact (fun a => Classical.propDecidable (s5.memaddrs a))
            (.var .local (ofString "rep")) = some (.val (.word (BitVec.ofNat 64 repVal))) := hs5_rep_lk
        have hs6_eq := fc_store_sub_words_6a hs5_ev (by rw [hs5_gn]; exact he_nat)
          (by rw [hs5_gn]; omega) ha6 hb6 hr6_eta.symm
        have hs6_gn : globN s6 "ev" = e0 := by rw [hs6_eq]; exact hs5_gn
        have hs6_ev : s6.globals.lookup (ofString "ev") = some (.val (.word (BitVec.ofNat 64 e0))) := by
          rw [hs6_eq]; exact hs5_ev
        have hs6_ewok : WordsOK s6 (e0, 280) := by rw [hs6_eq]; exact wordsOK_updW_6a s5 hs5_ewok _ _
        have hs6_rep_lk : s6.locals.lookup (ofString "rep") =
            some (.val (.word (BitVec.ofNat 64 repVal))) := by rw [hs6_eq]; exact hs5_rep_lk
        rw [evaluateHOLFiniteState_seq_line780] at hrun3
        have hr7_eta := Prod.mk.eta (p := evaluateHOLFiniteState s6 p192b)
        set r7 := (evaluateHOLFiniteState s6 p192b).1
        set s7 := (evaluateHOLFiniteState s6 p192b).2
        rw [← hr7_eta] at hrun3
        cases hr7 : r7 with
        | some res7 =>
          rw [hr7] at hr7_eta hrun3
          have herr7 := R14Shards.OpHandlersA.store_some_eq_error' hr7_eta.symm
          subst herr7; cases (Prod.mk.inj hrun3).1
        | none =>
          rw [hr7] at hr7_eta hrun3; dsimp only at hrun3
          have ha7 := eval_load_ev_off_6a s6 hs6_ev hs6_ewok he_bnd
            (off := 192) (by omega) (by omega)
          have hb7 : @evalHOLExact 64 F _ s6.toExact (fun a => Classical.propDecidable (s6.memaddrs a))
              (.var .local (ofString "rep")) = some (.val (.word (BitVec.ofNat 64 repVal))) := hs6_rep_lk
          have hs7_eq := fc_store_sub_words_6a hs6_ev (by rw [hs6_gn]; exact he_nat)
            (by rw [hs6_gn]; omega) ha7 hb7 hr7_eta.symm
          -- Memory & state properties of s7 compared to st
          have hs7_glob : s7.globals = st.globals := by
            rw [hs7_eq, hs6_eq, hs5_eq]; dsimp only; rw [hs4_glob, hs2_eq]; dsimp only; exact hs1_glob
          have hs7_be : s7.be = st.be := by
            rw [hs7_eq, hs6_eq, hs5_eq]; dsimp only; rw [hs4_be, hs2_eq]; dsimp only; exact hs1_be
          have hs7_dom : s7.memaddrs = st.memaddrs := by
            rw [hs7_eq, hs6_eq, hs5_eq]; dsimp only; rw [hs4_dom, hs2_eq]; dsimp only
            exact hA1.1.memaddrs.trans hBS.arena.1.memaddrs.symm
          have hs7_sh : s7.shMemaddrs = st.shMemaddrs := by
            rw [hs7_eq, hs6_eq, hs5_eq]; dsimp only; rw [hs4_sh, hs2_eq]; dsimp only
            exact hA1.1.shMemaddrs.trans hBS.arena.1.shMemaddrs.symm
          have hs7_code : s7.code = st.code := by
            rw [hs7_eq, hs6_eq, hs5_eq]; dsimp only; rw [hs4_code, hs2_eq]; dsimp only
            exact hA1.1.code.trans hBS.arena.1.code.symm
          have hs7_ba : s7.baseAddr = st.baseAddr := by
            rw [hs7_eq, hs6_eq, hs5_eq]; dsimp only; rw [hs4_ba, hs2_eq]; dsimp only
            exact hA1.1.baseAddr.trans hBS.arena.1.baseAddr.symm
          have hGs7 : GuestInv s7 :=
            guestInv_congr hs7_code hs7_dom hs7_sh hs7_ba hBS.arena.1
          have hs7_mem4 : ∀ x : BitVec 64,
              x ≠ BitVec.ofNat 64 (e0 + 64) →
              x ≠ BitVec.ofNat 64 (e0 + 72) →
              x ≠ BitVec.ofNat 64 (e0 + 184) →
              x ≠ BitVec.ofNat 64 (e0 + 192) →
              s7.memory x = st.memory x := by
            intro x hn64 hn72 hn184 hn192
            have hm7 : s7.memory x = s6.memory x := by
              rw [hs7_eq, hs6_gn]; dsimp only [R14Shards.OpHandlersA.updW]; rw [if_neg hn192]
            have hm6 : s6.memory x = s5.memory x := by
              rw [hs6_eq, hs5_gn]; dsimp only [R14Shards.OpHandlersA.updW]; rw [if_neg hn72]
            have hm5 : s5.memory x = s4.memory x := by
              rw [hs5_eq, hs4_gn]; dsimp only [R14Shards.OpHandlersA.updW]; rw [if_neg hn64]
            have hm2 : s2.memory x = s1.memory x := by
              rw [hs2_eq, hs1_gn]; dsimp only [R14Shards.OpHandlersA.updW]; rw [if_neg hn192]
            rw [hm7, hm6, hm5, hs4_mem, hm2]
            exact hs1_mem x hn64 hn72 hn184
          have hs7_mem_out : ∀ x : BitVec 64,
              (∀ off ∈ headSimpleOffs, x ≠ BitVec.ofNat 64 (e0 + off)) →
              s7.memory x = st.memory x := by
            intro x hx
            exact hs7_mem4 x (hx 64 (by decide)) (hx 72 (by decide))
              (hx 184 (by decide)) (hx 192 (by decide))
          have hs7_m64 : memW s7 (e0 + 64) =
              memW st (e0 + 64) + memW st (ch + 64) + repVal := by
            have hm7 : memW s7 (e0 + 64) = memW s6 (e0 + 64) := by
              rw [hs7_eq, hs6_gn]
              exact R14Shards.OpHandlersA.memW_updW_ne s6 (e0 + 192) (e0 + 64) _ (by omega) (by omega) (by omega)
            have hm6 : memW s6 (e0 + 64) = memW s5 (e0 + 64) := by
              rw [hs6_eq, hs5_gn]
              exact R14Shards.OpHandlersA.memW_updW_ne s5 (e0 + 72) (e0 + 64) _ (by omega) (by omega) (by omega)
            have hm5 : memW s5 (e0 + 64) = (BitVec.ofNat 64 (memW s4 (e0 + 64)) + BitVec.ofNat 64 repVal).toNat := by
              rw [hs5_eq, hs4_gn]; exact R14Shards.OpHandlersA.memW_updW_same s4 (e0 + 64) _
            have hm4 : memW s4 (e0 + 64) = memW s2 (e0 + 64) := by unfold memW; rw [hs4_mem]
            rw [hm7, hm6, hm5, hm4, hs2_m64]
            have hsum_lt : memW st (e0 + 64) + memW st (ch + 64) + repVal < 2 ^ 64 := by
              have : repVal ≤ memW st (e0 + 192) + memW st (ch + 192) := by
                rw [← hs2_m192]; exact hrep_le_192
              rw [hR_st] at hgas_sum; omega
            simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (show memW st (e0 + 64) + memW st (ch + 64) < 2 ^ 64 by omega),
              Nat.mod_eq_of_lt hrep_lt64, Nat.mod_eq_of_lt hsum_lt]
          have hs7_m192 : memW s7 (e0 + 192) =
              memW st (e0 + 192) + memW st (ch + 192) - repVal := by
            have hm6_192 : memW s6 (e0 + 192) = sp192 := by
              have h6 : memW s6 (e0 + 192) = memW s5 (e0 + 192) := by
                rw [hs6_eq, hs5_gn]
                exact R14Shards.OpHandlersA.memW_updW_ne s5 (e0 + 72) (e0 + 192) _ (by omega) (by omega) (by omega)
              have h5 : memW s5 (e0 + 192) = memW s4 (e0 + 192) := by
                rw [hs5_eq, hs4_gn]
                exact R14Shards.OpHandlersA.memW_updW_ne s4 (e0 + 64) (e0 + 192) _ (by omega) (by omega) (by omega)
              have h4 : memW s4 (e0 + 192) = sp192 := by unfold memW; rw [hs4_mem]; rfl
              exact h6.trans (h5.trans h4)
            rw [hs7_eq, hs6_gn, R14Shards.OpHandlersA.memW_updW_same s6 (e0 + 192) _, hm6_192]
            have hle_bv : BitVec.ofNat 64 repVal ≤ BitVec.ofNat 64 sp192 := by
              rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                Nat.mod_eq_of_lt hrep_lt64, Nat.mod_eq_of_lt hsp192_lt']
              exact hrep_le_192
            rw [BitVec.toNat_sub_of_le hle_bv, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt hsp192_lt', Nat.mod_eq_of_lt hrep_lt64, hs2_m192]
          have hs7_sum : memW s7 (e0 + 64) + memW s7 (e0 + 192) =
              memW st (e0 + 64) + memW st (e0 + 192) + (memW st (ch + 64) + memW st (ch + 192)) := by
            have hle' : repVal ≤ memW st (e0 + 192) + memW st (ch + 192) := by
              rw [← hs2_m192]; exact hrep_le_192
            rw [hs7_m64, hs7_m192]; omega
          have hs7_cell : ∀ off : Nat, off + 8 ≤ 280 →
              off ≠ 64 → off ≠ 72 → off ≠ 184 → off ≠ 192 →
              memW s7 (e0 + off) = memW st (e0 + off) := by
            intro off hoff hn64 hn72 hn184 hn192
            unfold memW; rw [hs7_mem4]
            all_goals intro heq; have he := congrArg BitVec.toNat heq
            all_goals simp only [BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (show e0 + off < 2 ^ 64 by omega),
              Nat.mod_eq_of_lt (show e0 + 64 < 2 ^ 64 by omega),
              Nat.mod_eq_of_lt (show e0 + 72 < 2 ^ 64 by omega),
              Nat.mod_eq_of_lt (show e0 + 184 < 2 ^ 64 by omega),
              Nat.mod_eq_of_lt (show e0 + 192 < 2 ^ 64 by omega)] at he
            all_goals omega
          -- Create s7_st with st.locals to apply fcBranchState_of_head_simple
          set s7_st : PanSemStateFiniteExact 64 F := { s7 with locals := st.locals, clock := s7.clock }
          have hGs7_st : GuestInv s7_st := guestInv_with_locals_clock s7 st.locals s7.clock hGs7
          have hs7_sp : memW s7_st (e0 + 16) ≤ memW st (e0 + 232) := by
            change memW s7 (e0 + 16) ≤ memW st (e0 + 232)
            rw [hs7_cell 16 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact he_sp
          have hs7_gas_lt : memW s7_st (e0 + 64) + memW s7_st (e0 + 192) +
              (((evmChain st).tail.map fun ec => memW st (ec.1 + 64) + memW st (ec.1 + 192)).sum) + 1 < 2 ^ 64 := by
            change memW s7 (e0 + 64) + memW s7 (e0 + 192) + _ + 1 < 2 ^ 64
            rw [hs7_sum]; rw [hR_st] at hgas_sum; omega
          have hs7_r_le : memW s7_st (e0 + 64) + memW s7_st (e0 + 192) +
              (((evmChain st).tail.map fun ec => memW st (ec.1 + 64) + memW st (ec.1 + 192)).sum) ≤
                OpDispatchSpec.evmR s0 := by
            change memW s7 (e0 + 64) + memW s7 (e0 + 192) + _ ≤ OpDispatchSpec.evmR s0
            rw [hs7_sum]; rw [hR_st] at hr_sum; omega
          have hBS_7st : FcBranchState s0 s7_st S :=
            fcBranchState_of_head_simple hBS hGs7_st hs7_glob hs7_be rfl hs7_mem_out
              hs7_sp hs7_gas_lt hs7_r_le
          obtain ⟨_, _, hch_7st, hfix_7st, htab_7st, hframes_7st, hR_7st⟩ :=
            evmInvAt_of_head_simple hBS.arena hBS.inv hGs7_st hs7_glob hs7_be hs7_mem_out
              hs7_sp hs7_gas_lt
          have hav_7st : AvoidsTries s7_st S (frameLogObjects st (ch, globN s0 "cur_cont")) :=
            avoidsTries_of_head_simple_6 hBS.arena hBS.inv hGs7_st hs7_glob hs7_be hs7_mem_out
              hPC.child_log_objs_avoids_tries
          -- Non-head memory unhit from st to s7
          have hu_non_ev : ∀ i : Ivl, Disj i (e0, 280) → Allocated st i →
              M08IvlUnhit6a st s7 i := by
            intro i hdi ha k _ hk1 hk2
            have hb_i : i.1 + i.2 ≤ 2 ^ 64 :=
              (InitECandidate.Solver.Wave8Contracts.M08.ivl_allocated_bound hBS.arena.2 ha).2
            refine hs7_mem4 k ?_ ?_ ?_ ?_
            all_goals
              intro heq; have hn := congrArg BitVec.toNat heq
              simp only [BitVec.toNat_ofNat,
                Nat.mod_eq_of_lt (show e0 + 64 < 2 ^ 64 by omega),
                Nat.mod_eq_of_lt (show e0 + 72 < 2 ^ 64 by omega),
                Nat.mod_eq_of_lt (show e0 + 184 < 2 ^ 64 by omega),
                Nat.mod_eq_of_lt (show e0 + 192 < 2 ^ 64 by omega)] at hn
              dsimp only [Disj] at hdi; omega
          have hu_non_ev0 : ∀ i : Ivl, Disj i (e0, 280) → (i.2 = 0 ∨ Allocated st i) →
              M08IvlUnhit6a st s7 i := by
            intro i hdi hal
            rcases hal with hz | ha
            · intro k _ hk1 hk2; omega
            · exact hu_non_ev i hdi ha
          -- Child & child-logs facts on s7
          have hu_ch : M08IvlUnhit6a st s7 (ch, 280) :=
            hu_non_ev (ch, 280) hdisj_ch_ev (Or.inr hPC.child_scr.1)
          have hs7_cwok : WordsOK s7 (ch, 280) := wordsOK_of_unhit_6a hs7_dom hPC.child_scr.2
          have hs7_cins : Inside (ch, 280) (globN s7 "scratch_ptr") scratchEnd := by
            unfold globN; rw [hs7_glob]; exact hPC.child_scr.1
          have hs7_cm : ∀ off : Nat, off + 8 ≤ 280 → off % 8 = 0 →
              memW s7 (ch + off) = memW st (ch + off) := by
            intro off hoff hoff8
            have hch8 : ch % 8 = 0 := hPC.child_scr.2.1
            exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_ch
              (by omega) hchild_bnd ⟨by dsimp only; omega, by dsimp only; omega⟩
          set cl := memW st (ch + 88)
          have hs7_cl_eq : memW s7 (ch + 88) = cl := hs7_cm 88 (by omega) (by omega)
          have hcl_bnd : cl + 24 ≤ 2 ^ 64 :=
            (InitECandidate.Solver.Wave8Contracts.M08.ivl_allocated_bound hBS.arena.2
              (Or.inr hPC.child_logs_scr.1)).2
          have hcl_ne_zero : cl ≠ 0 := by
            have hss : 0 < scratchStart := by decide
            have hfmp : scratchStart ≤ globN st "frame_mem_ptr" := hBS.arena.2.2.2.1
            have hsp : globN st "frame_mem_ptr" ≤ globN st "scratch_ptr" := hBS.arena.2.2.2.2.1
            have hin : globN st "scratch_ptr" ≤ cl := hPC.child_logs_scr.1.1
            omega
          have hdisj_cl_ev : Disj (cl, 24) (e0, 280) :=
            (hPC.child_logs_disj_fo _ hhead_st (e0, 280) (by simp [frameObjects])).1
          have hu_cl : M08IvlUnhit6a st s7 (cl, 24) :=
            hu_non_ev (cl, 24) hdisj_cl_ev (Or.inr hPC.child_logs_scr.1)
          have hs7_cl_wok : WordsOK s7 (cl, 24) := wordsOK_of_unhit_6a hs7_dom hPC.child_logs_scr.2
          have hs7_clm : ∀ off : Nat, off + 8 ≤ 24 → off % 8 = 0 →
              memW s7 (cl + off) = memW st (cl + off) := by
            intro off hoff hoff8
            have hcl8 : cl % 8 = 0 := hPC.child_logs_scr.2.1
            exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_cl
              (by omega) hcl_bnd ⟨by dsimp only; omega, by dsimp only; omega⟩
          set n := memW st (cl + 8)
          set p := memW st cl
          set cap := memW st (cl + 16)
          have hs7_n_eq : memW s7 (cl + 8) = n := hs7_clm 8 (by omega) (by omega)
          have hs7_p_eq : memW s7 cl = p := by simpa using hs7_clm 0 (by omega) (by omega)
          -- Step 8: dec cl, dec n, dec p, dec i on s7
          have hs7_child_lk : s7.locals.lookup (ofString "child") =
              some (.val (.word (BitVec.ofNat 64 ch))) := by
            rw [hs7_eq, hs6_eq, hs5_eq]; exact hs4_child_lk
          rw [show pLogs = .dec (ofString "cl") .one (.load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 88)]))
              (.dec (ofString "n") .one (.load .one (.op .add [.var .local (ofString "cl"), .const (BitVec.ofNat 64 8)]))
                (.dec (ofString "p") .one (.load .one (.op .add [.var .local (ofString "cl"), .const (BitVec.ofNat 64 0)]))
                  (.dec (ofString "i") .one (.const 0#64)
                    (.seq logAppendWhileProg6 pTail)))) from rfl] at hrun3
          rw [evaluateHOLFiniteState_dec_total] at hrun3; dsimp only at hrun3
          have hld_cl := eval_load_local_off_6a s7 hs7_child_lk hs7_cwok hchild_bnd
            (off := 88) (by omega) (by omega)
          rw [hs7_cl_eq] at hld_cl
          rw [hld_cl] at hrun3; dsimp only at hrun3
          have hsh_cl : shapeEqHOL .one (shapeOfHOLExact (.val (.word (BitVec.ofNat 64 cl)) : ValueHOL 64)) = true := by
            simp [shapeEqHOL, shapeOfHOLExact]
          rw [if_pos hsh_cl] at hrun3
          set d1 := setVarHOLFinite (ofString "cl") (.val (.word (BitVec.ofNat 64 cl))) s7
          rcases hd1_run : evaluateHOLFiniteState d1
              (.dec (ofString "n") .one (.load .one (.op .add [.var .local (ofString "cl"), .const (BitVec.ofNat 64 8)]))
                (.dec (ofString "p") .one (.load .one (.op .add [.var .local (ofString "cl"), .const (BitVec.ofNat 64 0)]))
                  (.dec (ofString "i") .one (.const 0#64)
                    (.seq logAppendWhileProg6 pTail)))) with ⟨rd1, sd1⟩
          rw [hd1_run] at hrun3; dsimp only at hrun3
          have hrd1 : rd1 = some (.returned rv) := (Prod.mk.inj hrun3).1
          rw [hrd1] at hd1_run
          rw [evaluateHOLFiniteState_dec_total] at hd1_run; dsimp only at hd1_run
          have hd1_cl_lk : d1.locals.lookup (ofString "cl") =
              some (.val (.word (BitVec.ofNat 64 cl))) := by
            simp [d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hld_n := eval_load_local_off_6a d1 hd1_cl_lk hs7_cl_wok hcl_bnd
            (off := 8) (by omega) (by omega)
          have hd1_n_eq : memW d1 (cl + 8) = n := by
            rw [memW_congr_6b (a := d1) (b := s7) rfl]; exact hs7_n_eq
          rw [hd1_n_eq] at hld_n
          rw [hld_n] at hd1_run; dsimp only at hd1_run
          have hsh_n : shapeEqHOL .one (shapeOfHOLExact (.val (.word (BitVec.ofNat 64 n)) : ValueHOL 64)) = true := by
            simp [shapeEqHOL, shapeOfHOLExact]
          rw [if_pos hsh_n] at hd1_run
          set d2 := setVarHOLFinite (ofString "n") (.val (.word (BitVec.ofNat 64 n))) d1
          rcases hd2_run : evaluateHOLFiniteState d2
              (.dec (ofString "p") .one (.load .one (.op .add [.var .local (ofString "cl"), .const (BitVec.ofNat 64 0)]))
                (.dec (ofString "i") .one (.const 0#64)
                  (.seq logAppendWhileProg6 pTail))) with ⟨rd2, sd2⟩
          rw [hd2_run] at hd1_run; dsimp only at hd1_run
          have hrd2 : rd2 = some (.returned rv) := (Prod.mk.inj hd1_run).1
          rw [hrd2] at hd2_run
          rw [evaluateHOLFiniteState_dec_total] at hd2_run; dsimp only at hd2_run
          have hd2_cl_lk : d2.locals.lookup (ofString "cl") =
              some (.val (.word (BitVec.ofNat 64 cl))) := by
            simp [d2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hd1_cl_lk,
              show ofString "n" ≠ ofString "cl" by decide]
          have hld_p := eval_load_local_off_6a d2 hd2_cl_lk hs7_cl_wok hcl_bnd
            (off := 0) (by omega) (by omega)
          have hd2_p_eq : memW d2 (cl + 0) = p := by
            rw [Nat.add_zero, memW_congr_6b (a := d2) (b := s7) rfl]; exact hs7_p_eq
          rw [hd2_p_eq] at hld_p
          rw [hld_p] at hd2_run; dsimp only at hd2_run
          have hsh_p : shapeEqHOL .one (shapeOfHOLExact (.val (.word (BitVec.ofNat 64 p)) : ValueHOL 64)) = true := by
            simp [shapeEqHOL, shapeOfHOLExact]
          rw [if_pos hsh_p] at hd2_run
          set d3 := setVarHOLFinite (ofString "p") (.val (.word (BitVec.ofNat 64 p))) d2
          rcases hd3_run : evaluateHOLFiniteState d3
              (.dec (ofString "i") .one (.const 0#64)
                (.seq logAppendWhileProg6 pTail)) with ⟨rd3, sd3⟩
          rw [hd3_run] at hd2_run; dsimp only at hd2_run
          have hrd3 : rd3 = some (.returned rv) := (Prod.mk.inj hd2_run).1
          rw [hrd3] at hd3_run
          rw [evaluateHOLFiniteState_dec_total] at hd3_run; dsimp only [evalHOLExact] at hd3_run
          have hsh_0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word (0#64 : BitVec 64)) : ValueHOL 64)) = true := by
            simp [shapeEqHOL, shapeOfHOLExact]
          rw [if_pos hsh_0] at hd3_run
          set d4 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) d3
          rcases hd4_run : evaluateHOLFiniteState d4 (.seq logAppendWhileProg6 pTail) with ⟨rd4, sd4⟩
          rw [hd4_run] at hd3_run; dsimp only at hd3_run
          have hrd4 : rd4 = some (.returned rv) := (Prod.mk.inj hd3_run).1
          rw [hrd4] at hd4_run
          have hcpost_sd4 : cpost.memory = sd4.memory ∧ cpost.globals = sd4.globals ∧
              cpost.be = sd4.be ∧ cpost.memaddrs = sd4.memaddrs ∧
              cpost.shMemaddrs = sd4.shMemaddrs ∧ cpost.code = sd4.code ∧
              cpost.baseAddr = sd4.baseAddr ∧ cpost.clock = sd4.clock := by
            have hm3 : s_end3.memory = sd1.memory ∧ s_end3.globals = sd1.globals ∧
                s_end3.be = sd1.be ∧ s_end3.memaddrs = sd1.memaddrs ∧
                s_end3.shMemaddrs = sd1.shMemaddrs ∧ s_end3.code = sd1.code ∧
                s_end3.baseAddr = sd1.baseAddr ∧ s_end3.clock = sd1.clock := by
              have := (Prod.mk.inj hrun3).2; subst this; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
            have hm2 : sd1.memory = sd2.memory ∧ sd1.globals = sd2.globals ∧
                sd1.be = sd2.be ∧ sd1.memaddrs = sd2.memaddrs ∧
                sd1.shMemaddrs = sd2.shMemaddrs ∧ sd1.code = sd2.code ∧
                sd1.baseAddr = sd2.baseAddr ∧ sd1.clock = sd2.clock := by
              have := (Prod.mk.inj hd1_run).2; subst this; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
            have hm1 : sd2.memory = sd3.memory ∧ sd2.globals = sd3.globals ∧
                sd2.be = sd3.be ∧ sd2.memaddrs = sd3.memaddrs ∧
                sd2.shMemaddrs = sd3.shMemaddrs ∧ sd2.code = sd3.code ∧
                sd2.baseAddr = sd3.baseAddr ∧ sd2.clock = sd3.clock := by
              have := (Prod.mk.inj hd2_run).2; subst this; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
            have hm0 : sd3.memory = sd4.memory ∧ sd3.globals = sd4.globals ∧
                sd3.be = sd4.be ∧ sd3.memaddrs = sd4.memaddrs ∧
                sd3.shMemaddrs = sd4.shMemaddrs ∧ sd3.code = sd4.code ∧
                sd3.baseAddr = sd4.baseAddr ∧ sd3.clock = sd4.clock := by
              have := (Prod.mk.inj hd3_run).2; subst this; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
            subst hcpost_s3
            exact ⟨hm3.1.trans (hm2.1.trans (hm1.1.trans hm0.1)),
              hm3.2.1.trans (hm2.2.1.trans (hm1.2.1.trans hm0.2.1)),
              hm3.2.2.1.trans (hm2.2.2.1.trans (hm1.2.2.1.trans hm0.2.2.1)),
              hm3.2.2.2.1.trans (hm2.2.2.2.1.trans (hm1.2.2.2.1.trans hm0.2.2.2.1)),
              hm3.2.2.2.2.1.trans (hm2.2.2.2.2.1.trans (hm1.2.2.2.2.1.trans hm0.2.2.2.2.1)),
              hm3.2.2.2.2.2.1.trans (hm2.2.2.2.2.2.1.trans (hm1.2.2.2.2.2.1.trans hm0.2.2.2.2.2.1)),
              hm3.2.2.2.2.2.2.1.trans (hm2.2.2.2.2.2.2.1.trans (hm1.2.2.2.2.2.2.1.trans hm0.2.2.2.2.2.2.1)),
              hm3.2.2.2.2.2.2.2.trans (hm2.2.2.2.2.2.2.2.trans (hm1.2.2.2.2.2.2.2.trans hm0.2.2.2.2.2.2.2))⟩
          -- Prepare hypotheses for log_append_while_fc_step at d4 with k = 0
          have hd4_s7_lc : { d4 with locals := st.locals, clock := s7.clock } = s7_st := rfl
          have hBS_d4 : FcBranchState s0 { d4 with locals := st.locals, clock := d4.clock } S :=
            fcBranchState_congr_locals_clock (st := s7_st) st.locals d4.clock hBS_7st hBS_7st.locals_ok
          have hd4_i_lk : d4.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 0))) := by
            simp [d4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hd4_p_lk : d4.locals.lookup (ofString "p") = some (.val (.word (BitVec.ofNat 64 p))) := by
            simp [d4, d3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "i" ≠ ofString "p" by decide]
          have hd4_n_lk : d4.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 n))) := by
            simp [d4, d3, d2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "i" ≠ ofString "n" by decide,
              show ofString "p" ≠ ofString "n" by decide]
          have hd4_child_lk : d4.locals.lookup (ofString "child") =
              some (.val (.word (BitVec.ofNat 64 ch))) := by
            simp [d4, d3, d2, d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs7_child_lk,
              show ofString "i" ≠ ofString "child" by decide,
              show ofString "p" ≠ ofString "child" by decide,
              show ofString "n" ≠ ofString "child" by decide,
              show ofString "cl" ≠ ofString "child" by decide]
          rcases hPC.child_logs_ok with hcl_z | ⟨_, _, hn_lt28, hn_le_cap, hcl_entries⟩
          · exact absurd hcl_z hcl_ne_zero
          have hfl_eq_p : frameLogs st (ch, globN s0 "cur_cont") = (p, 8 * cap) := rfl
          have hd4_7st_mem : d4.memory = s7_st.memory := rfl
          have hd4_7st_glob : d4.globals = s7_st.globals := rfl
          have hd4_7st_be : d4.be = s7_st.be := rfl
          have hd4_glob_st : d4.globals = st.globals := hs7_glob
          have hd4_dom_st : d4.memaddrs = st.memaddrs := hs7_dom
          have hp_alloc_d4 : Allocated d4 (p, 8 * cap) := by
            have hal := hPC.child_logs_arr_in
            rw [hfl_eq_p] at hal
            unfold Allocated
            rw [globN_congr_6b hd4_glob_st "heap_ptr", globN_congr_6b hd4_glob_st "scratch_ptr"]
            exact hal
          have hdisj_fl_ev : Disj (p, 8 * cap) (e0, 280) := by
            rw [← hfl_eq_p]
            exact (hPC.child_logs_disj_fo _ hhead_st (e0, 280) (by simp [frameObjects])).2
          have hu_fl : M08IvlUnhit6a st s7 (p, 8 * cap) := by
            refine hu_non_ev (p, 8 * cap) hdisj_fl_ev ?_
            rw [← hfl_eq_p]; exact hPC.child_logs_arr_in
          have hp_wok_st : WordsOK st (p, 8 * cap) := by
            rw [← hfl_eq_p]; exact hPC.child_logs_arr_wok
          have hp_wok_d4 : WordsOK d4 (p, 8 * cap) := wordsOK_of_unhit_6a hd4_dom_st hp_wok_st
          have hp_bnd : p + 8 * cap ≤ 2 ^ 64 := by
            have hal : Allocated st (p, 8 * cap) := by rw [← hfl_eq_p]; exact hPC.child_logs_arr_in
            exact (InitECandidate.Solver.Wave8Contracts.M08.ivl_allocated_bound hBS.arena.2 hal).2
          have hd4_pm : ∀ j, j < cap → memW d4 (p + 8 * j) = memW st (p + 8 * j) := by
            intro j hj
            have hp8 : p % 8 = 0 := hp_wok_st.1
            have hd4_s7_mem : d4.memory = s7.memory := rfl
            rw [memW_congr_6b hd4_s7_mem]
            exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_fl
              (by omega) hp_bnd ⟨by dsimp only; omega, by dsimp only; omega⟩
          -- FrameObjects and htabFootprint on d4 agree with st
          have hch_d4_st : evmChain d4 = evmChain st :=
            (OpDispatchSpec.evmChain_congr (s := s7_st) (t := d4) hd4_7st_mem hd4_7st_glob).trans hch_7st
          have hfo_d4_st : ∀ ec ∈ evmChain d4, frameObjects d4 ec = frameObjects st ec := by
            intro ec hec
            rw [hch_d4_st] at hec
            exact (frameObjects_congr_6b hd4_7st_mem hd4_7st_glob ec).trans
              (hframes_7st ec hec).1
          have hht_d4_st : ∀ t ∈ S, htabFootprint d4 t = htabFootprint st t := by
            intro t ht
            exact (htabFootprint_congr_6b hd4_7st_mem t).trans (htab_7st t ht)
          have hfix_d4_st : fixedObjects d4 = fixedObjects st :=
            (fixedObjects_congr_6b hd4_7st_mem hd4_7st_glob).trans hfix_7st
          have hp_dfo_d4 : ∀ ec ∈ evmChain d4, ∀ o ∈ frameObjects d4 ec, Disj (p, 8 * cap) o := by
            intro ec hec o ho
            rw [hfo_d4_st ec hec] at ho; rw [hch_d4_st] at hec; rw [← hfl_eq_p]
            exact (hPC.child_logs_disj_fo ec hec o ho).2
          -- Log Owned Intervals on d4 equal those on st
          have hflo_eq_st : frameLogObjects st (ch, globN s0 "cur_cont") =
              (List.range n).flatMap (fun j => logOwnedIvls st (memW st (p + 8 * (0 + j)))) := by
            unfold frameLogObjects
            dsimp only
            congr 1; funext j; rw [Nat.zero_add]
          have hrem_logs_d4 : ∀ j, 0 ≤ j → j < n →
              WordAt d4 (p + 8 * j) ∧ LogEntryOK d4 (memW d4 (p + 8 * j)) ∧
              logOwnedIvls d4 (memW d4 (p + 8 * j)) = logOwnedIvls st (memW st (p + 8 * j)) := by
            have hn_def : n = memW st (memW st (globN s0 "ev" + 88) + 8) := rfl
            have hcap_def : cap = memW st (memW st (globN s0 "ev" + 88) + 16) := rfl
            have hnc : n ≤ cap := by rw [hn_def, hcap_def]; exact hn_le_cap
            intro j _ hjn
            obtain ⟨_, hlog_st⟩ := hcl_entries j hjn
            have hjc : j < cap := Nat.lt_of_lt_of_le hjn hnc
            have hwa_d4 : WordAt d4 (p + 8 * j) := hp_wok_d4.2.2 j (by dsimp only; omega)
            rw [hd4_pm j hjc]
            set lj := memW st (p + 8 * j)
            have hmem_flo : ∀ o ∈ logOwnedIvls st lj, o ∈ frameLogObjects st (ch, globN s0 "cur_cont") := by
              intro o ho
              rw [hflo_eq_st, List.mem_flatMap]
              exact ⟨j, List.mem_range.2 hjn, by simpa using ho⟩
            have hmem_40 : (memW st (p + 8 * j), 40) ∈ logRecordIvls st lj := by
              simp [logRecordIvls, lj]
            have hd_ev : Disj (memW st (p + 8 * j), 40) (e0, 280) := by
              have hown_40 : (memW st (p + 8 * j), 40) ∈ logOwnedIvls st lj :=
                List.mem_filter.2 ⟨hmem_40, by simp⟩
              exact hPC.child_log_objs_disj_fo _ (hmem_flo _ hown_40) _ hhead_st (e0, 280) (by simp [frameObjects])
            have hd4_dom : d4.memaddrs = st.memaddrs := hs7_dom
            have hd4_glob_st : d4.globals = st.globals := hs7_glob
            have hhp_d4 : globN st "heap_ptr" ≤ globN d4 "heap_ptr" :=
              Nat.le_of_eq (globN_congr_6b hd4_glob_st "heap_ptr").symm
            have hsys_d4 : globN d4 "vm_system_address" = globN st "vm_system_address" :=
              globN_congr_6b hd4_glob_st "vm_system_address"
            obtain ⟨hlog_d4, hlo_eq⟩ := logEntry_unhit_transport_6a hBS.arena hd4_dom
              hhp_d4 hsys_d4 (fun a ha h1 h2 => hu_non_ev _ hd_ev (Or.inl hlog_st.2.1) a ha h1 h2) hlog_st
            exact ⟨hwa_d4, hlog_d4, hlo_eq⟩
          have hlo_d4_eq : (List.range (n - 0)).flatMap
              (fun j => logOwnedIvls d4 (memW d4 (p + 8 * (0 + j)))) =
              frameLogObjects st (ch, globN s0 "cur_cont") := by
            rw [Nat.sub_zero, hflo_eq_st]
            refine List.flatMap_congr fun j hj => ?_
            rw [Nat.zero_add]
            exact (hrem_logs_d4 j (Nat.zero_le j) (List.mem_range.1 hj)).2.2
          have hp_dlo_d4 : ∀ o ∈ (List.range (n - 0)).flatMap
              (fun j => logOwnedIvls d4 (memW d4 (p + 8 * (0 + j)))), Disj (p, 8 * cap) o := by
            intro o ho
            rw [hlo_d4_eq] at ho; rw [← hfl_eq_p]
            exact hLSD o ho
          have hc_dlo_d4 : ∀ o ∈ (List.range (n - 0)).flatMap
              (fun j => logOwnedIvls d4 (memW d4 (p + 8 * (0 + j)))), Disj (ch, 280) o := by
            intro o ho
            rw [hlo_d4_eq] at ho
            obtain ⟨j, hjr, hoj⟩ := List.mem_flatMap.1 (hflo_eq_st ▸ ho)
            rw [Nat.zero_add] at hoj
            obtain ⟨_, hlj_ok⟩ := hcl_entries j (List.mem_range.1 hjr)
            rcases logOwnedIvls_zero_or_heap_fc hlj_ok o hoj with hz | hin_hp
            · dsimp only [Disj]; omega
            · have hhs : globN st "heap_ptr" ≤ heapLimit := hBS.arena.2.2.1
              have hfmp : scratchStart ≤ globN st "frame_mem_ptr" := hBS.arena.2.2.2.1
              have hsp : globN st "frame_mem_ptr" ≤ globN st "scratch_ptr" := hBS.arena.2.2.2.2.1
              have hc_in : globN st "scratch_ptr" ≤ ch := hPC.child_scr.1.1
              have hin2 : o.1 + o.2 ≤ globN st "heap_ptr" := hin_hp.2
              rw [R11Shards.heapLimit_val] at hhs; rw [R11Shards.scratchStart_val] at hfmp
              dsimp only [Disj]; omega
          have hlogs_d4 : ∀ j, 0 ≤ j → j < n →
              WordAt d4 (p + 8 * j) ∧ LogEntryOK d4 (memW d4 (p + 8 * j)) :=
            fun j hj0 hjn => ⟨(hrem_logs_d4 j hj0 hjn).1, (hrem_logs_d4 j hj0 hjn).2.1⟩
          have hpw_d4 : ((List.range (n - 0)).flatMap
              (fun j => logOwnedIvls d4 (memW d4 (p + 8 * (0 + j))))).Pairwise Disj := by
            rw [hlo_d4_eq]; exact hPC.child_log_objs_pw
          have hlo_fo_d4 : ∀ o1 ∈ (List.range (n - 0)).flatMap
              (fun j => logOwnedIvls d4 (memW d4 (p + 8 * (0 + j)))),
              ∀ ec ∈ evmChain d4, ∀ o2 ∈ frameObjects d4 ec, Disj o1 o2 := by
            intro o1 ho1 ec hec o2 ho2
            rw [hlo_d4_eq] at ho1; rw [hfo_d4_st ec hec] at ho2; rw [hch_d4_st] at hec
            exact hPC.child_log_objs_disj_fo o1 ho1 ec hec o2 ho2
          have hlo_ht_d4 : ∀ o1 ∈ (List.range (n - 0)).flatMap
              (fun j => logOwnedIvls d4 (memW d4 (p + 8 * (0 + j)))),
              ∀ t ∈ S, ∀ o2 ∈ htabFootprint d4 t, Disj o1 o2 := by
            intro o1 ho1 t ht o2 ho2
            rw [hlo_d4_eq] at ho1; rw [hht_d4_st t ht] at ho2
            exact hPC.child_log_objs_disj_ht o1 ho1 t ht o2 ho2
          have hlo_fix_d4 : ∀ o1 ∈ (List.range (n - 0)).flatMap
              (fun j => logOwnedIvls d4 (memW d4 (p + 8 * (0 + j)))),
              ∀ o2 ∈ fixedObjects d4, Disj o1 o2 := by
            intro o1 ho1 o2 ho2
            rw [hlo_d4_eq] at ho1; rw [hfix_d4_st] at ho2
            exact hPC.child_log_objs_disj_fix o1 ho1 o2 ho2
          have hlo_av_d4 : AvoidsTries d4 S ((List.range (n - 0)).flatMap
              (fun j => logOwnedIvls d4 (memW d4 (p + 8 * (0 + j))))) := by
            rw [hlo_d4_eq]
            exact (avoidsTries_lc_6 d4 st.locals s7.clock S _).1 hav_7st
          have hlo_msg_d4 : ∀ o1 ∈ (List.range (n - 0)).flatMap
              (fun j => logOwnedIvls d4 (memW d4 (p + 8 * (0 + j)))),
              ∀ ec ∈ evmChain d4, Disj (memW d4 (ec.1 + 112), 176) o1 := by
            intro o1 ho1 ec hec
            rw [hlo_d4_eq] at ho1; rw [hch_d4_st] at hec
            have hm112 : memW d4 (ec.1 + 112) = memW st (ec.1 + 112) :=
              (memW_congr_6b hd4_7st_mem (ec.1 + 112)).trans
                (hframes_7st ec hec).2.2.2.2.2.2.1
            rw [hm112]
            exact hPC.child_log_objs_disj_msg o1 ho1 ec hec
          have hc_wok_d4 : WordsOK d4 (ch, 280) := wordsOK_of_unhit_6a rfl hs7_cwok
          have hc_ins_d4 : Inside (ch, 280) (globN d4 "scratch_ptr") scratchEnd := by
            rw [globN_congr_6b (a := d4) (b := s7) rfl]; exact hs7_cins
          have hc_dfo_d4 : ∀ ec ∈ evmChain d4, ∀ o ∈ frameObjects d4 ec, Disj (ch, 280) o := by
            intro ec hec o ho
            rw [hfo_d4_st ec hec] at ho; rw [hch_d4_st] at hec
            exact hPC.child_disj_fo ec hec o ho
          have hc_dht_d4 : ∀ t ∈ S, ∀ o ∈ htabFootprint d4 t, Disj (ch, 280) o := by
            intro t ht o ho
            rw [hht_d4_st t ht] at ho
            exact hPC.child_disj_ht t ht o ho
          -- Invoke log_append_while_fc_step!
          obtain ⟨wm, hwm_ev, hwm_tail, hBS_wm, hhp_wm, hgk_wm, hbe_wm, hch_wm, hR_wm, hht_wm,
              hm16_wm, hm40_wm, hm232_wm, hcwok_wm, hcins_wm, hcdht_wm, hm96_wm, hloc_wm⟩ :=
            log_append_while_fc_step n st.locals p n cap 0 (Nat.zero_le n) (Nat.sub_zero n).symm
              hn_lt28 hn_le_cap hBS_d4 hd4_i_lk hd4_n_lk hd4_p_lk (Or.inr hp_alloc_d4) hp_wok_d4
              hp_dfo_d4 hp_dlo_d4 hc_dlo_d4 hlogs_d4 hpw_d4 hlo_fo_d4 hlo_ht_d4 hlo_fix_d4
              hlo_av_d4 hlo_msg_d4 hc_wok_d4 hc_ins_d4 hc_dfo_d4 hc_dht_d4 hd4_run
          -- Step 10: p96 on wm -> wm96
          dsimp only [pTail] at hwm_tail
          rw [evaluateHOLFiniteState_seq_line780] at hwm_tail
          have hr96_eta := Prod.mk.eta (p := evaluateHOLFiniteState wm p96)
          set r96 := (evaluateHOLFiniteState wm p96).1
          set wm96 := (evaluateHOLFiniteState wm p96).2
          rw [← hr96_eta] at hwm_tail
          cases hr96 : r96 with
          | some res96 =>
            rw [hr96] at hr96_eta hwm_tail
            have herr96 := R14Shards.OpHandlersA.store_some_eq_error' hr96_eta.symm
            subst herr96; cases (Prod.mk.inj hwm_tail).1
          | none =>
            rw [hr96] at hr96_eta hwm_tail; dsimp only at hwm_tail
            set wm_st : PanSemStateFiniteExact 64 F :=
              { wm with locals := st.locals, clock := wm.clock }
            have hev_wm_d4 : wm.globals.lookup (ofString "ev") =
                some (.val (.word (BitVec.ofNat 64 e0))) := by
              rw [← hgk_wm (ofString "ev") (by decide)]
              change s7.globals.lookup (ofString "ev") = _
              rw [hs7_glob]; exact he_lk
            have hgn_wm : globN wm "ev" = e0 := by
              unfold globN; rw [hev_wm_d4]; exact he_nat
            obtain ⟨hwm_ebnd, hwm_ewok, _, hwm_esp, hwm_R_split⟩ :=
              ev_head_facts_6a hBS_wm.arena hBS_wm.inv
            have hgn_wm_st : globN wm_st "ev" = e0 := hgn_wm
            rw [hgn_wm_st] at hwm_ebnd hwm_ewok hwm_esp hwm_R_split
            have ha96 := eval_load_ev_off_6a wm hev_wm_d4
              (wordsOK_of_unhit_6a (s := wm_st) (post := wm) rfl hwm_ewok)
              hwm_ebnd (off := 96) (by omega) (by omega)
            have hchild_lk_wm : wm.locals.lookup (ofString "child") =
                some (.val (.word (BitVec.ofNat 64 ch))) := by
              rw [hloc_wm (ofString "child") (by decide)]; exact hd4_child_lk
            have hb96 := eval_load_local_off_6a wm hchild_lk_wm
              hcwok_wm hchild_bnd (off := 96) (by omega) (by omega)
            have hwm96_eq := fc_store_add_words hev_wm_d4 (by rw [hgn_wm]; exact he_nat)
              (by rw [hgn_wm]; omega) ha96 hb96 hr96_eta.symm
            set wm96_st : PanSemStateFiniteExact 64 F := { wm96 with locals := st.locals }
            have hG_wm96 : GuestInv wm96 :=
              guestInv_congr (s := wm_st) (t := wm96)
                (by rw [hwm96_eq]) (by rw [hwm96_eq]) (by rw [hwm96_eq]) (by rw [hwm96_eq])
                hBS_wm.arena.1
            have hG_wm96_st : GuestInv wm96_st :=
              guestInv_with_locals_clock wm96 st.locals wm96.clock hG_wm96
            have hwm96_glob : wm96_st.globals = wm_st.globals := by
              change wm96.globals = wm.globals; rw [hwm96_eq]
            have hwm96_be : wm96_st.be = wm_st.be := by
              change wm96.be = wm.be; rw [hwm96_eq]
            have hwm96_mem_out : ∀ x : BitVec 64,
                (∀ off ∈ headSimpleOffs, x ≠ BitVec.ofNat 64 (e0 + off)) →
                wm96_st.memory x = wm_st.memory x := by
              intro x hx
              change wm96.memory x = wm.memory x
              rw [hwm96_eq, hgn_wm]; dsimp only [R14Shards.OpHandlersA.updW]
              exact if_neg (hx 96 (by decide))
            have hwm96_m16 : memW wm96 (e0 + 16) = memW wm (e0 + 16) := by
              rw [hwm96_eq, hgn_wm]
              exact R14Shards.OpHandlersA.memW_updW_ne wm (e0 + 96) (e0 + 16) _ (by omega) (by omega) (by omega)
            have hwm96_m40 : memW wm96 (e0 + 40) = memW wm (e0 + 40) := by
              rw [hwm96_eq, hgn_wm]
              exact R14Shards.OpHandlersA.memW_updW_ne wm (e0 + 96) (e0 + 40) _ (by omega) (by omega) (by omega)
            have hwm96_m232 : memW wm96 (e0 + 232) = memW wm (e0 + 232) := by
              rw [hwm96_eq, hgn_wm]
              exact R14Shards.OpHandlersA.memW_updW_ne wm (e0 + 96) (e0 + 232) _ (by omega) (by omega) (by omega)
            have hwm96_m64 : memW wm96 (e0 + 64) = memW wm (e0 + 64) := by
              rw [hwm96_eq, hgn_wm]
              exact R14Shards.OpHandlersA.memW_updW_ne wm (e0 + 96) (e0 + 64) _ (by omega) (by omega) (by omega)
            have hwm96_m192 : memW wm96 (e0 + 192) = memW wm (e0 + 192) := by
              rw [hwm96_eq, hgn_wm]
              exact R14Shards.OpHandlersA.memW_updW_ne wm (e0 + 96) (e0 + 192) _ (by omega) (by omega) (by omega)
            have hwm96_m136 : memW wm96 (e0 + 136) = memW wm (e0 + 136) := by
              rw [hwm96_eq, hgn_wm]
              exact R14Shards.OpHandlersA.memW_updW_ne wm (e0 + 96) (e0 + 136) _ (by omega) (by omega) (by omega)
            have hsp_96 : memW wm96_st (globN wm_st "ev" + 16) ≤ memW wm_st (globN wm_st "ev" + 232) := by
              rw [hgn_wm_st, memW_congr_6b (a := wm96_st) (b := wm96) rfl, hwm96_m16,
                  ← memW_congr_6b (a := wm_st) (b := wm) rfl]
              exact hwm_esp
            have hgas_96 : memW wm96_st (globN wm_st "ev" + 64) + memW wm96_st (globN wm_st "ev" + 192) +
                (((evmChain wm_st).tail.map fun ec => memW wm_st (ec.1 + 64) + memW wm_st (ec.1 + 192)).sum) + 1 <
                2 ^ 64 := by
              rw [hgn_wm_st, memW_congr_6b (a := wm96_st) (b := wm96) rfl,
                  memW_congr_6b (a := wm96_st) (b := wm96) rfl, hwm96_m64, hwm96_m192,
                  ← memW_congr_6b (a := wm_st) (b := wm) rfl, ← memW_congr_6b (a := wm_st) (b := wm) rfl,
                  ← hwm_R_split]
              exact hBS_wm.inv.2.2.2.2.2.2.2.2.2.2.2.2
            have hr_96 : memW wm96_st (globN wm_st "ev" + 64) + memW wm96_st (globN wm_st "ev" + 192) +
                (((evmChain wm_st).tail.map fun ec => memW wm_st (ec.1 + 64) + memW wm_st (ec.1 + 192)).sum) ≤
                OpDispatchSpec.evmR s0 := by
              rw [hgn_wm_st, memW_congr_6b (a := wm96_st) (b := wm96) rfl,
                  memW_congr_6b (a := wm96_st) (b := wm96) rfl, hwm96_m64, hwm96_m192,
                  ← memW_congr_6b (a := wm_st) (b := wm) rfl, ← memW_congr_6b (a := wm_st) (b := wm) rfl,
                  ← hwm_R_split]
              exact hBS_wm.r_le
            have hBS_wm96 : FcBranchState s0 wm96_st S :=
              fcBranchState_of_head_simple hBS_wm hG_wm96_st hwm96_glob hwm96_be rfl
                (by rw [hgn_wm_st]; exact hwm96_mem_out) hsp_96 hgas_96 hr_96
            obtain ⟨_, _, hch_96, _, htab_96, _, hR_96⟩ :=
              evmInvAt_of_head_simple hBS_wm.arena hBS_wm.inv hG_wm96_st hwm96_glob hwm96_be
                (by rw [hgn_wm_st]; exact hwm96_mem_out) hsp_96 hgas_96
            have hcwok_96 : WordsOK wm96_st (ch, 280) :=
              wordsOK_of_unhit_6a (s := wm96) (post := wm96_st) rfl
                (by rw [hwm96_eq]; exact wordsOK_updW_6a wm hcwok_wm _ _)
            have hcins_96 : Inside (ch, 280) (globN wm96_st "scratch_ptr") scratchEnd := by
              rw [globN_congr_6b (a := wm96_st) (b := wm96) rfl, hwm96_eq]; exact hcins_wm
            -- Step 11: pUnion = htab_union_into(ev[136], child[136]) on wm96 -> su
            rw [evaluateHOLFiniteState_seq_line780] at hwm_tail
            rcases hru : evaluateHOLFiniteState wm96 pUnion with ⟨resu, su⟩
            rw [hru] at hwm_tail
            have hresu_none : resu = none := by
              cases resu with
              | none => rfl
              | some r =>
                dsimp only at hwm_tail
                have hr_eq : some r = some (.returned rv) := (Prod.mk.inj hwm_tail).1
                cases r with
                | returned u =>
                  have hne := call0_ne_returned_fc wm96 (ofString "htab_union_into")
                    [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 136)]),
                     .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 136)])] u
                  exact absurd (congrArg Prod.fst hru) hne
                | _ => cases Option.some.inj hr_eq
            subst hresu_none; dsimp only at hwm_tail
            -- Bridge call from wm96 to wm96_st using call0_congr_locals_6
            have hgn_96 : globN wm96 "ev" = e0 := by rw [hwm96_eq]; exact hgn_wm
            have hev_96 : wm96.globals.lookup (ofString "ev") =
                some (.val (.word (BitVec.ofNat 64 e0))) := by rw [hwm96_eq]; exact hev_wm_d4
            have hewok_96 : WordsOK wm96 (e0, 280) := by
              rw [hwm96_eq]
              exact wordsOK_updW_6a wm (wordsOK_of_unhit_6a (s := wm_st) (post := wm) rfl hwm_ewok) _ _
            have hchild_lk_96 : wm96.locals.lookup (ofString "child") =
                some (.val (.word (BitVec.ofNat 64 ch))) := by rw [hwm96_eq]; exact hchild_lk_wm
            have hcwok_96_raw : WordsOK wm96 (ch, 280) :=
              wordsOK_of_unhit_6a (s := wm96_st) (post := wm96) rfl hcwok_96
            have ha_u1 := eval_load_ev_off_6a wm96 hev_96 hewok_96
              hwm_ebnd (off := 136) (by omega) (by omega)
            have hb_u1 := eval_load_local_off_6a wm96 hchild_lk_96
              hcwok_96_raw hchild_bnd (off := 136) (by omega) (by omega)
            have ha_u2 := eval_load_ev_off_6a wm96_st hev_96
              (wordsOK_of_unhit_6a (s := wm96) (post := wm96_st) rfl hewok_96)
              hwm_ebnd (off := 136) (by omega) (by omega)
            have hb_u2 := eval_load_local_off_6a wm96_st hBS_wm96.locals_ok.child_lk
              hcwok_96 hchild_bnd (off := 136) (by omega) (by omega)
            have hmw_96_st : ∀ x, memW wm96_st x = memW wm96 x := memW_congr_6b rfl
            rw [hmw_96_st] at ha_u2
            rw [hmw_96_st] at hb_u2
            have hargs_u1 : evalListHOLFinite wm96 (h := fun a => Classical.propDecidable (wm96.memaddrs a))
                [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 136)]),
                 .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 136)])] =
                some [.val (.word (BitVec.ofNat 64 (memW wm96 (e0 + 136)))),
                      .val (.word (BitVec.ofNat 64 (memW wm96 (ch + 136))))] := by
              rw [evalListHOLFinite_eq_toExact]
              simp [evalListHOLExact, ha_u1, hb_u1]
            have hargs_u2 : evalListHOLFinite wm96_st
                (h := fun a => Classical.propDecidable (wm96.memaddrs a))
                [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 136)]),
                 .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 136)])] =
                some [.val (.word (BitVec.ofNat 64 (memW wm96 (e0 + 136)))),
                      .val (.word (BitVec.ofNat 64 (memW wm96 (ch + 136))))] := by
              rw [evalListHOLFinite_eq_toExact]
              simp only [evalListHOLExact, ha_u2, hb_u2]
              rfl
            obtain ⟨hres_u_eq, hpost_u_eq⟩ := call0_congr_locals_6 wm96 st.locals
              (ofString "htab_union_into")
              [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 136)]),
               .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 136)])]
              [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 136)]),
               .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 136)])]
              _ hargs_u1 hargs_u2
            have hru_fst : (evaluateHOLFiniteState wm96 pUnion).1 = none := by rw [hru]
            have hru_st_none : (evaluateHOLFiniteState wm96_st pUnion).1 = none :=
              hres_u_eq.symm.trans hru_fst
            have hsu_eq : su = { (evaluateHOLFiniteState wm96_st pUnion).2 with locals := wm96.locals } := by
              have h := hpost_u_eq hru_fst
              rwa [hru] at h
            obtain ⟨_, _, hqu⟩ := call_htab_union_into_head_del_step hBS_wm96 ⟨hcins_96, hcwok_96⟩
              (by rw [hru_st_none]; simp)
            obtain ⟨hBS_pu, hloc_pu, hhp_pu, hgk_pu, hch_pu, hR_pu, hunhit_pu⟩ := hqu hru_st_none
            set pu := (evaluateHOLFiniteState wm96_st pUnion).2
            -- Step 12: return 0#64 on su -> sd4
            rw [evaluateHOLFiniteState_return] at hwm_tail
            dsimp only [evalHOLExact] at hwm_tail
            have hsz0 : sizeOfShapeWithContextHOL su.structs
                (shapeOfHOLExact (.val (.word (0#64 : BitVec 64)))) ≤ 32 := by
              simp [shapeOfHOLExact]
            rw [if_pos hsz0] at hwm_tail
            have hsd4_eq : sd4 = su.emptyLocalsHOLFinite := (Prod.mk.inj hwm_tail).2.symm
            -- Assemble final post = { cpost.emptyLocalsHOLFinite with locals := st.locals }
            set post := (evaluateHOLFiniteState st
              (.call (some (none, none)) (ofString "incorporate_child_on_success")
                [.var .local (ofString "child")])).2
            have hp_loc : post.locals = st.locals := by rw [hpost_eq]
            have hp_mem : post.memory = pu.memory := by
              rw [hpost_eq]; dsimp only [emptyLocalsHOLFinite]
              rw [hcpost_sd4.1, hsd4_eq]; dsimp only [emptyLocalsHOLFinite]
              rw [hsu_eq]
            have hp_glob : post.globals = pu.globals := by
              rw [hpost_eq]; dsimp only [emptyLocalsHOLFinite]
              rw [hcpost_sd4.2.1, hsd4_eq]; dsimp only [emptyLocalsHOLFinite]
              rw [hsu_eq]
            have hp_be : post.be = pu.be := by
              rw [hpost_eq]; dsimp only [emptyLocalsHOLFinite]
              rw [hcpost_sd4.2.2.1, hsd4_eq]; dsimp only [emptyLocalsHOLFinite]
              rw [hsu_eq]
            have hp_dom : post.memaddrs = pu.memaddrs := by
              rw [hpost_eq]; dsimp only [emptyLocalsHOLFinite]
              rw [hcpost_sd4.2.2.2.1, hsd4_eq]; dsimp only [emptyLocalsHOLFinite]
              rw [hsu_eq]
            have hp_sh : post.shMemaddrs = pu.shMemaddrs := by
              rw [hpost_eq]; dsimp only [emptyLocalsHOLFinite]
              rw [hcpost_sd4.2.2.2.2.1, hsd4_eq]; dsimp only [emptyLocalsHOLFinite]
              rw [hsu_eq]
            have hp_code : post.code = pu.code := by
              rw [hpost_eq]; dsimp only [emptyLocalsHOLFinite]
              rw [hcpost_sd4.2.2.2.2.2.1, hsd4_eq]; dsimp only [emptyLocalsHOLFinite]
              rw [hsu_eq]
            have hp_ba : post.baseAddr = pu.baseAddr := by
              rw [hpost_eq]; dsimp only [emptyLocalsHOLFinite]
              rw [hcpost_sd4.2.2.2.2.2.2.1, hsd4_eq]; dsimp only [emptyLocalsHOLFinite]
              rw [hsu_eq]
            have hp_mw : ∀ a, memW post a = memW pu a := fun a => by unfold memW; rw [hp_mem]
            have hp_gn : ∀ nm, globN post nm = globN pu nm := fun nm => by unfold globN; rw [hp_glob]
            have hBS_post : FcBranchState s0 post S := by
              have hGp : GuestInv post := guestInv_congr hp_code hp_dom hp_sh hp_ba hBS_pu.arena.1
              have hloc_p_pu : post.locals = pu.locals := hp_loc.trans hloc_pu.symm
              exact fcBranchState_of_head_simple hBS_pu hGp hp_glob hp_be hloc_p_pu
                (fun x _ => hp_mem ▸ rfl)
                (by
                  rw [hp_mw]
                  exact (ev_head_facts_6a hBS_pu.arena hBS_pu.inv).2.2.2.1)
                (by
                  rw [hp_mw, hp_mw]
                  have hg_pu := hBS_pu.inv.2.2.2.2.2.2.2.2.2.2.2.2
                  have hR_pu_split := (ev_head_facts_6a hBS_pu.arena hBS_pu.inv).2.2.2.2
                  unfold OpDispatchSpec.evmR at hR_pu_split
                  omega)
                (by
                  rw [hp_mw, hp_mw]
                  have hr_pu := hBS_pu.r_le
                  rw [(ev_head_facts_6a hBS_pu.arena hBS_pu.inv).2.2.2.2] at hr_pu
                  exact hr_pu)
            have hgk_post : GlobalsKept ["heap_ptr"] st post := by
              have hgk_st_wm : GlobalsKept ["heap_ptr"] st wm_st := by
                intro g hg
                have h1 := hgk_wm g hg
                have hd4_s7_g : d4.globals = s7.globals := rfl
                rw [hd4_s7_g, hs7_glob] at h1
                exact h1
              have hgk_wm_96 : GlobalsKept ["heap_ptr"] wm_st wm96_st := by
                intro g _; exact (congrArg (fun m => m.lookup g) hwm96_glob).symm
              have hgk_pu_p : GlobalsKept ["heap_ptr"] pu post := by
                intro g _; rw [hp_glob]
              exact globalsKept_trans_6 hgk_st_wm
                (globalsKept_trans_6 hgk_wm_96 (globalsKept_trans_6 hgk_pu hgk_pu_p))
            have hch_post : evmChain post = evmChain st := by
              have hch_p_pu : evmChain post = evmChain pu :=
                OpDispatchSpec.evmChain_congr (s := pu) (t := post) hp_mem hp_glob
              have hch_wm_d4 : evmChain wm_st = evmChain d4 :=
                (evmChain_lc_fc wm st.locals wm.clock).trans hch_wm
              exact hch_p_pu.trans (hch_pu.trans (hch_96.trans (hch_wm_d4.trans hch_d4_st)))
            have hR_post : OpDispatchSpec.evmR post ≤
                OpDispatchSpec.evmR st + (memW st (ch + 64) + memW st (ch + 192)) := by
              have hR_p_pu : OpDispatchSpec.evmR post = OpDispatchSpec.evmR pu := by
                unfold OpDispatchSpec.evmR
                rw [OpDispatchSpec.evmChain_congr (s := pu) (t := post) hp_mem hp_glob]
                have hmap : ((evmChain pu).map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)) =
                    ((evmChain pu).map fun ec => memW pu (ec.1 + 64) + memW pu (ec.1 + 192)) := by
                  apply List.map_congr_left; intro ec _; rw [hp_mw, hp_mw]
                rw [hmap]
              have hR_96_wm : OpDispatchSpec.evmR wm96_st = OpDispatchSpec.evmR wm := by
                rw [hR_96, hgn_wm_st,
                    memW_congr_6b (a := wm96_st) (b := wm96) rfl,
                    memW_congr_6b (a := wm96_st) (b := wm96) rfl,
                    hwm96_m64, hwm96_m192,
                    ← memW_congr_6b (a := wm_st) (b := wm) rfl,
                    ← memW_congr_6b (a := wm_st) (b := wm) rfl,
                    ← hwm_R_split]
                exact evmR_lc_fc wm st.locals wm.clock
              have hR_d4_7st : OpDispatchSpec.evmR d4 = OpDispatchSpec.evmR s7_st := by
                unfold OpDispatchSpec.evmR
                rw [OpDispatchSpec.evmChain_congr (s := s7_st) (t := d4) hd4_7st_mem hd4_7st_glob]
                have hmap : ((evmChain s7_st).map fun ec => memW d4 (ec.1 + 64) + memW d4 (ec.1 + 192)) =
                    ((evmChain s7_st).map fun ec => memW s7_st (ec.1 + 64) + memW s7_st (ec.1 + 192)) := by
                  apply List.map_congr_left; intro ec _
                  rw [memW_congr_6b hd4_7st_mem, memW_congr_6b hd4_7st_mem]
                rw [hmap]
              rw [hR_p_pu, hR_pu, hR_96_wm, hR_wm, hR_d4_7st, hR_7st]
              have he0_def : globN st "ev" = e0 := rfl
              rw [he0_def, memW_congr_6b (a := s7_st) (b := s7) rfl,
                  memW_congr_6b (a := s7_st) (b := s7) rfl, hs7_sum, hR_st]
              omega
            -- Child scratch & WordsOK on post via hunhit_pu
            have hgn_pu_ev : globN pu "ev" = e0 := by
              have h1 := hgk_pu (ofString "ev") (by decide)
              unfold globN; rw [← h1]
              exact (globN_congr_6b (a := wm96_st) (b := wm96) rfl "ev").trans hgn_96
            have hgn_post_ev : globN post "ev" = e0 := (hp_gn "ev").trans hgn_pu_ev
            have ht0_eq : memW wm96_st (globN wm96_st "ev" + 136) = memW wm (e0 + 136) := by
              rw [globN_congr_6b (a := wm96_st) (b := wm96) rfl,
                  memW_congr_6b (a := wm96_st) (b := wm96) rfl, hgn_96]
              exact hwm96_m136
            have ht0_S : memW wm (e0 + 136) ∈ S := by
              have hh_wm : (globN wm_st "ev", globN wm_st "cur_cont") ∈ evmChain wm_st := by
                rw [evmChain_cons]; exact List.mem_cons_self
              have hfw_wm := (hBS_wm.inv.2.2.2.2.1 _ hh_wm).2.2.2.2.2.2.2.1
              rw [hgn_wm_st, memW_congr_6b (a := wm_st) (b := wm) rfl] at hfw_wm
              exact hfw_wm
            have hht_96_wm : htabFootprint wm96_st (memW wm (e0 + 136)) =
                htabFootprint wm (memW wm (e0 + 136)) :=
              (htab_96 _ ht0_S).trans (htabFootprint_congr_6b (a := wm_st) (b := wm) rfl _)
            have hu_ch_pu : M08IvlUnhit6a wm96_st pu (ch, 280) := by
              refine hunhit_pu (ch, 280) ?_ (Or.inr (Or.inr hcins_96))
              intro j hj
              rw [ht0_eq, hht_96_wm] at hj
              exact hcdht_wm _ ht0_S j hj
            have hcwok_pu : WordsOK pu (ch, 280) :=
              wordsOK_of_unhit_6a (hBS_pu.arena.1.memaddrs.trans hBS_wm96.arena.1.memaddrs.symm)
                hcwok_96
            have hcwok_post : WordsOK post (ch, 280) :=
              wordsOK_of_unhit_6a hp_dom hcwok_pu
            have hcins_post : Inside (ch, 280) (globN post "scratch_ptr") scratchEnd := by
              rw [hp_gn]
              have hsp_pu : globN pu "scratch_ptr" = globN wm96_st "scratch_ptr" := by
                unfold globN; rw [← hgk_pu (ofString "scratch_ptr") (by decide)]
              rw [hsp_pu]; exact hcins_96
            -- Parent cells 16, 40, 232 on post
            have hh_96 : (e0, globN wm96_st "cur_cont") ∈ evmChain wm96_st := by
              have h : (globN wm96_st "ev", globN wm96_st "cur_cont") ∈ evmChain wm96_st := by
                rw [evmChain_cons]; exact List.mem_cons_self
              rwa [(globN_congr_6b (a := wm96_st) (b := wm96) rfl "ev").trans hgn_96] at h
            have he0_in_96 : Allocated wm96_st (e0, 280) :=
              Or.inr (((hBS_wm96.inv.2.2.2.2.1 _ hh_96).1 (e0, 280) (by simp)).1)
            have hu_e0_pu : M08IvlUnhit6a wm96_st pu (e0, 280) := by
              refine hunhit_pu (e0, 280) ?_ (Or.inr he0_in_96)
              intro j hj
              rw [ht0_eq] at hj
              exact (hBS_wm96.inv.2.2.2.2.2.2.2.2.1 _ hh_96 (e0, 280) (by simp [frameObjects])).1
                _ ht0_S j hj
            have hpu_e0_cell : ∀ off : Nat, off + 8 ≤ 280 → off % 8 = 0 →
                memW pu (e0 + off) = memW wm96 (e0 + off) :=
              fun off hoff hoff8 =>
                (m08_memW_cell_6b hu_e0_pu hewok_96.1 hwm_ebnd hoff hoff8).trans
                  (memW_congr_6b (a := wm96_st) (b := wm96) rfl (e0 + off))
            have hd4_gn_ev : globN d4 "ev" = e0 :=
              globN_congr_6b hd4_glob_st "ev"
            have hm16_post : memW post (globN post "ev" + 16) = memW st (e0 + 16) := by
              rw [hgn_post_ev, hp_mw, hpu_e0_cell 16 (by omega) (by omega), hwm96_m16]
              rw [hd4_gn_ev] at hm16_wm
              exact hm16_wm.trans ((memW_congr_6b (a := d4) (b := s7) rfl (e0 + 16)).trans
                (hs7_cell 16 (by omega) (by omega) (by omega) (by omega) (by omega)))
            have hm40_post : memW post (globN post "ev" + 40) = memW st (e0 + 40) := by
              rw [hgn_post_ev, hp_mw, hpu_e0_cell 40 (by omega) (by omega), hwm96_m40]
              rw [hd4_gn_ev] at hm40_wm
              exact hm40_wm.trans ((memW_congr_6b (a := d4) (b := s7) rfl (e0 + 40)).trans
                (hs7_cell 40 (by omega) (by omega) (by omega) (by omega) (by omega)))
            have hm232_post : memW post (globN post "ev" + 232) = memW st (e0 + 232) := by
              rw [hgn_post_ev, hp_mw, hpu_e0_cell 232 (by omega) (by omega), hwm96_m232]
              rw [hd4_gn_ev] at hm232_wm
              exact hm232_wm.trans ((memW_congr_6b (a := d4) (b := s7) rfl (e0 + 232)).trans
                (hs7_cell 232 (by omega) (by omega) (by omega) (by omega) (by omega)))
            exact ⟨S, hBS_post, hp_loc, hgk_post, hch_post, hR_post, hcins_post, hcwok_post,
              hm16_post, hm40_post, hm232_post⟩
