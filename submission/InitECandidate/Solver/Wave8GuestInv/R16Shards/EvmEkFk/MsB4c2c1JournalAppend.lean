import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.MsB4c2c0JournalCore

/-!
# Scratch Rung B4c2c1: Journal-Append Block Combinator (`journal_append_block_step_code`)

Shared `worldEff_call0_memcpy`, `journalAppendTailProg`, and `journal_append_block_step_code`
combinator reused by `jset` (`ts+16` and `ts+48`) and `jdel` (`ts+32`).
-/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.EvmBase
open InitECandidate.Solver.Wave8GuestInv.EvmStepLemmas
open InitECandidate.Solver.Wave8GuestInv.EvmFrameSpecs
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8M19.Htab
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemBridge
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28

theorem worldEff_call0_memcpy {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff s cur Rl B gw)
    (dstExp srcExp nExp : ExpHOL 64)
    (hnt : (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "memcpy")
      [dstExp, srcExp, nExp])).1 ≠ some .timeOut)
    (hor : (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "memcpy")
      [dstExp, srcExp, nExp])).1 = none ∨
      Resumes (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "memcpy")
      [dstExp, srcExp, nExp])).1)
    (hin : ∀ (dstw srcw nw : BitVec 64),
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) dstExp =
        some (.val (.word dstw)) →
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) srcExp =
        some (.val (.word srcw)) →
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) nExp =
        some (.val (.word nw)) →
      0 < nw.toNat →
      (∃ j ∈ Rl, j.1 ≤ dstw.toNat ∧ dstw.toNat + nw.toNat ≤ j.1 + j.2) ∨
      (∃ gs ∈ B, (bufferRegion s gs).1 ≤ dstw.toNat ∧
        dstw.toNat + nw.toNat ≤ (bufferRegion s gs).1 + (bufferRegion s gs).2) ∨
      (globN s "frame_mem_ptr" ≤ dstw.toNat ∧ dstw.toNat + nw.toNat ≤ globN s "scratch_ptr") ∨
      (globN s "heap_ptr" ≤ dstw.toNat ∧ dstw.toNat + nw.toNat ≤ heapLimit)) :
    WorldEff s (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "memcpy")
      [dstExp, srcExp, nExp])).2 Rl B gw := by
  by_cases hgood : ∃ (dw sw nw : BitVec 64),
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) dstExp =
        some (.val (.word dw)) ∧
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) srcExp =
        some (.val (.word sw)) ∧
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) nExp =
        some (.val (.word nw))
  · obtain ⟨dw, sw, nw, hd, hsw, hn⟩ := hgood
    have hargs_good : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a))
        [dstExp, srcExp, nExp] = some [.val (.word dw), .val (.word sw), .val (.word nw)] := by
      rw [evalListHOLFinite_eq_toExact]
      simp [evalListHOLExact, hd, hsw, hn]
    have hb := Fast_C08WkShard03.call0_byteEff Fast_C08WkShard03.funByteEff_memcpy cur
      [dstExp, srcExp, nExp] [(dw.toNat, nw.toNat)] h.code h.arena.1
      (fun vals hargs i hi _ => by
        rw [hargs_good] at hargs
        injection hargs with hargs_eq
        subst hargs_eq
        simp only [List.mem_singleton, Fast_C08WkShard03.valWordNat] at hi
        subst hi
        exact ⟨(dw.toNat, nw.toNat), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)
      hnt hor
    exact h.of_byteEff hb (fun iv hiv hpos => by
      simp only [List.mem_singleton] at hiv
      subst hiv
      exact hin dw sw nw hd hsw hn hpos)
  · have hpost_eq : (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "memcpy")
        [dstExp, srcExp, nExp])).2 = cur := by
      rw [evaluateHOLFiniteState_call]
      rcases hargs : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a))
          [dstExp, srcExp, nExp] with _ | vals
      · rfl
      · dsimp only
        rcases hl : lookupCodeHOLFinite cur.code.lookup (ofString "memcpy") vals with _ | ⟨b', c', r'⟩
        · rfl
        · exfalso
          have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "memcpy") vals = some (b', c', r') := by
            rwa [← h.code]
          have hinst := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup (ofString "memcpy")
            _ _ b' _ r' vals c' lookup_memcpy_r16 hl'
          have hret := lookupCodeHOLFinite_installed_return cur (ofString "memcpy")
            _ _ _ _ r' vals c' (by rw [h.code]; exact lookup_memcpy_r16) hl
          subst hinst hret
          obtain ⟨dw, sw, nw, hvals, _, _, _⟩ := Fast_C08WkShard03.lookupCode_three_words
            (by decide) (by decide) (by decide) lookup_memcpy_r16 hl'
          rw [evalListHOLFinite_eq_toExact] at hargs
          simp only [evalListHOLExact] at hargs
          rcases hd : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) dstExp with _ | vd
          · simp [hd] at hargs
          · rcases hs : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) srcExp with _ | vs
            · simp [hd, hs] at hargs
            · rcases hn : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) nExp with _ | vn
              · simp [hd, hs, hn] at hargs
              · rw [hd, hs, hn] at hargs
                injection hargs with hargs_eq
                have hvals2 := hargs_eq.trans hvals
                injection hvals2 with h1 ht1; injection ht1 with h2 ht2; injection ht2 with h3 _
                subst h1 h2 h3
                exact hgood ⟨dw, sw, nw, hd, hs, hn⟩
    rwa [hpost_eq]

theorem callee_param_two_r16_code {F : Type} (state : PanSemStateFiniteExact 64 F) (fname p1 p2 : MlS)
    (s1 s2 : ShapeHOL) (body : ProgHOL 64) (ret : ShapeHOL)
    (hl : state.code.lookup fname = some ([(p1, s1), (p2, s2)], body, ret))
    (e1 e2 : ExpHOL 64)
    (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [e1, e2] = some values)
    (hlook : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret')) :
    ∃ v1 v2,
      evalAt state e1 = some v1 ∧ evalAt state e2 = some v2 ∧
      callee.lookup p1 = some v1 ∧ callee.lookup p2 = some v2 := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact] at hargs
  rcases he1 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) e1 with _ | v1
  · simp [he1] at hargs
  · rcases he2 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) e2 with _ | v2
    · simp [he1, he2] at hargs
    · simp only [he1, he2, Option.some.injEq] at hargs
      subst hargs
      unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hlook
      split at hlook
      · cases hlook
      · rename_i exactBody exactLocals exactShape raw
        have heq := Option.some.inj hlook
        rcases Prod.mk.inj heq with ⟨rfl, hrest⟩
        rcases Prod.mk.inj hrest with ⟨rfl, _⟩
        unfold lookupCodeHOLExact at raw
        rw [hl] at raw
        dsimp only at raw
        split at raw
        · rename_i hcond
          have rawEq := Option.some.inj raw
          rcases Prod.mk.inj rawEq with ⟨-, hrest2⟩
          rcases Prod.mk.inj hrest2 with ⟨hloc, -⟩
          subst hloc
          obtain ⟨hnd, -, -⟩ := hcond
          have hne : p1 ≠ p2 := by simp [List.nodup_cons] at hnd; exact hnd
          refine ⟨v1, v2, he1, he2, ?_, ?_⟩
          · simp [List.zip, List.foldl, HolFiniteMapExact.lookup_update, FUPDATE, hne]
          · simp [List.zip, List.foldl, HolFiniteMapExact.lookup_update, FUPDATE]
        · cases raw

theorem trap_with_call_no_none_resumes_code {F : Type}
    (state : PanSemStateFiniteExact 64 F) (codeVal : BitVec 64)
    (hcode : state.code = originalRuntimeCode) :
    (evaluateHOLFiniteState state
      (.call (some (none, none)) (ofString "trap_with") [.const codeVal])).1 ≠ none ∧
    ¬ Resumes (evaluateHOLFiniteState state
      (.call (some (none, none)) (ofString "trap_with") [.const codeVal])).1 := by
  have hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.const codeVal] = some [.val (.word codeVal)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
  have hlk := pan_one_word_lookup state.code.lookup (ofString "trap_with") (ofString "code")
    (sourceFnBody Guest.Software.guestFn_trap_with) codeVal
    (by rw [hcode]; exact lookup_trap_with)
  rw [evaluateHOLFiniteState_call, hargs]; dsimp only; rw [hlk]; dsimp only
  split
  · exact ⟨by simp, by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h⟩
  · have hout := evaluate_trap_with_body_outcomes
      (callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "code", .val (.word codeVal))))
    rcases hrun : evaluateHOLFiniteState
        (callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "code", .val (.word codeVal))))
        (sourceFnBody Guest.Software.guestFn_trap_with) with ⟨res, st⟩
    rw [hrun] at hout
    cases res with
    | none => exact absurd rfl hout.1
    | some r =>
      cases r with
      | returned v => exact absurd rfl (hout.2.1 v)
      | exception eid v =>
        refine ⟨by simp, ?_⟩
        rintro (⟨_, h⟩ | ⟨_, _, h, hne⟩)
        · simp at h
        · injection h with h'; injection h' with he hw; subst he hw
          exact hout.2.2 eid v hne rfl
      | _ => exact ⟨by simp, by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h⟩

def journalAppendTailProg (trapCode : BitVec 64) (e16 : ExpHOL 64) (tail : ProgHOL 64) : ProgHOL 64 :=
  .seq
    (.ite (.cmp .notLower (.var .global (ofString "journal_n")) (.var .global (ofString "journal_cap")))
      (.call (some (none, none)) (ofString "trap_with") [.const trapCode])
      .skip)
    (.dec (ofString "klen") .one (.load .one (.op .add [.var .local (ofString "t"), .const 0#64]))
      (.decCall (ofString "kc") .one (ofString "alloc") [.var .local (ofString "klen")]
        (.seq
          (.call (some (none, none)) (ofString "memcpy")
            [.var .local (ofString "kc"), .var .local (ofString "key"), .var .local (ofString "klen")])
          (.dec (ofString "r") .one
            (.op .add [.var .global (ofString "journal"),
              .panop .mul [.var .global (ofString "journal_n"), .const 32#64]])
            (.seq
              (.store (.var .local (ofString "r")) (.var .local (ofString "t")))
              (.seq
                (.store (.op .add [.var .local (ofString "r"), .const 8#64]) (.var .local (ofString "kc")))
                (.seq
                  (.store (.op .add [.var .local (ofString "r"), .const 16#64]) e16)
                  (.seq
                    (.store (.op .add [.var .local (ofString "r"), .const 24#64])
                      (.rfield 1 (.var .local (ofString "old"))))
                    (.seq
                      (.assign .global (ofString "journal_n")
                        (.op .add [.var .global (ofString "journal_n"), .const 1#64]))
                      tail)))))))))

theorem dec_ret_inv {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {nm : MlS} {init : ExpHOL 64} {bd : ProgHOL 64} {rv : ValueHOL 64}
    (h : evaluateHOLFiniteState s (.dec nm .one init bd) = (some (.returned rv), post)) :
    ∃ w : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) init =
        some (.val (.word w)) ∧
      ∃ mid, evaluateHOLFiniteState (setVarHOLFinite nm (.val (.word w)) s) bd = (some (.returned rv), mid) ∧
        post = { mid with locals := HolFiniteMapExact.resVarEq mid.locals (nm, s.locals.lookup nm) } := by
  rw [evaluateHOLFiniteState_dec_total] at h; dsimp only at h
  rcases hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) init with _ | val
  · rw [hev] at h; simp at h
  · rw [hev] at h; dsimp only at h
    rcases val with ⟨⟨w⟩⟩ | _ | _ <;> try (simp [shapeOfHOLExact, shapeEqHOL] at h; done)
    have hsh : shapeEqHOL .one (shapeOfHOLExact (.val (.word w) : ValueHOL 64)) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    rw [if_pos hsh] at h
    rcases hb : evaluateHOLFiniteState (setVarHOLFinite nm (.val (.word w)) s) bd with ⟨rb, mid⟩
    rw [hb] at h
    cases rb with
    | none => simp at h
    | some r0 =>
      cases r0 with
      | returned u =>
        dsimp only at h
        injection h with hr hso; injection hr with hr'; injection hr' with hu; subst hu
        exact ⟨w, rfl, mid, hb, hso.symm⟩
      | _ => simp at h

theorem seq_store_ret_inv {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {dst val : ExpHOL 64} {b : ProgHOL 64} {rv : ValueHOL 64}
    (h : evaluateHOLFiniteState s (.seq (.store dst val) b) = (some (.returned rv), post)) :
    ∃ mid, evaluateHOLFiniteState s (.store dst val) = (none, mid) ∧
      evaluateHOLFiniteState mid b = (some (.returned rv), post) := by
  rw [evaluateHOLFiniteState_seq_line780] at h
  rcases ha : evaluateHOLFiniteState s (.store dst val) with ⟨ra, mid⟩
  rw [ha] at h
  cases ra with
  | none => exact ⟨mid, rfl, h⟩
  | some _ =>
    have hcf := (PanRunBounded.evaluate_store_control_frame s dst val).1
    rw [ha] at hcf; rcases hcf with h0 | h0 <;> cases h0; simp at h

theorem seq_assign_ret_inv {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {vk : VarKind} {nm : MlS} {val : ExpHOL 64} {b : ProgHOL 64} {rv : ValueHOL 64}
    (h : evaluateHOLFiniteState s (.seq (.assign vk nm val) b) = (some (.returned rv), post)) :
    ∃ mid, evaluateHOLFiniteState s (.assign vk nm val) = (none, mid) ∧
      evaluateHOLFiniteState mid b = (some (.returned rv), post) := by
  rw [evaluateHOLFiniteState_seq_line780] at h
  rcases ha : evaluateHOLFiniteState s (.assign vk nm val) with ⟨ra, mid⟩
  rw [ha] at h
  cases ra with
  | none => exact ⟨mid, rfl, h⟩
  | some _ =>
    exfalso
    rw [evaluateHOLFiniteState_assign] at ha
    split at ha
    · injection ha with hr _; injection hr with hr'; subst hr'; simp at h
    · split at ha
      · simp at ha
      · injection ha with hr _; injection hr with hr'; subst hr'; simp at h

theorem seq_call0_ret_inv {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {fn : MlS} {args : List (ExpHOL 64)} {b : ProgHOL 64} {rv : ValueHOL 64}
    (h : evaluateHOLFiniteState s (.seq (.call (some (none, none)) fn args) b) = (some (.returned rv), post)) :
    ∃ mid, evaluateHOLFiniteState s (.call (some (none, none)) fn args) = (none, mid) ∧
      evaluateHOLFiniteState mid b = (some (.returned rv), post) := by
  rw [evaluateHOLFiniteState_seq_line780] at h
  rcases ha : evaluateHOLFiniteState s (.call (some (none, none)) fn args) with ⟨ra, mid⟩
  rw [ha] at h
  cases ra with
  | none => exact ⟨mid, rfl, h⟩
  | some _ =>
    exfalso
    rw [evaluateHOLFiniteState_call] at ha
    rcases hev : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
    · rw [hev] at ha; dsimp only at ha
      injection ha with hr _; injection hr with hr'; subst hr'; simp at h
    · rw [hev] at ha; dsimp only at ha
      rcases hlk : lookupCodeHOLFinite s.code.lookup fn vals with _ | ⟨body0, cal0, ret0⟩
      · rw [hlk] at ha; dsimp only at ha
        injection ha with hr _; injection hr with hr'; subst hr'; simp at h
      · rw [hlk] at ha; dsimp only at ha
        split at ha
        · injection ha with hr _; injection hr with hr'; subst hr'; simp at h
        · rcases hrb : evaluateHOLFiniteState (callEntryStateHOLFinite s cal0) body0 with ⟨rb, mb⟩
          rw [hrb] at ha
          cases rb with
          | none =>
            dsimp only at ha
            injection ha with hr _; injection hr with hr'; subst hr'; simp at h
          | some rb0 =>
            cases rb0 <;> simp only at ha
            case returned =>
              split at ha
              · simp at ha
              · injection ha with hr _; injection hr with hr'; subst hr'; simp at h
            all_goals (injection ha with hr _; injection hr with hr'; subst hr'; simp at h)

theorem store_word_none_inv {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {dstExp valExp : ExpHOL 64}
    (hrun : evaluateHOLFiniteState s (.store dstExp valExp) = (none, post))
    (hval_one : ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp =
      some v → ∃ w : BitVec 64, v = .val (.word w)) :
    ∃ (dw vw : BitVec 64),
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
        some (.val (.word dw)) ∧
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp =
        some (.val (.word vw)) ∧
      s.memaddrs dw ∧
      post = { s with memory := fun a => if a = dw then .word vw else s.memory a } := by
  rw [evaluateHOLFiniteState_store] at hrun
  rcases hx : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp with _ | dv
  · rw [hx] at hrun; simp at hrun
  · rw [hx] at hrun
    rcases dv with ⟨⟨dw⟩⟩ | _ | _ <;> try (simp at hrun; done)
    rcases hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp with _ | val
    · rw [hv] at hrun; simp at hrun
    · obtain ⟨vw, rfl⟩ := hval_one val hv
      rw [hv] at hrun
      simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL] at hrun
      by_cases hdom : s.memaddrs dw
      · simp only [hdom, ↓reduceIte] at hrun
        injection hrun with _ hp
        exact ⟨dw, vw, rfl, rfl, hdom, hp.symm⟩
      · simp [hdom] at hrun

theorem journal_append_block_step_code {F : Type}
    (s0 cur : PanSemStateFiniteExact 64 F)
    (trapCode : BitVec 64) (e16 : ExpHOL 64) (tw kw f0 f1 w16 : BitVec 64)
    (hW0 : WorldOK s0)
    (heff0 : WorldEff s0 cur [] [] ["heap_ptr"])
    (hg_all_cur : ∀ k : MlS, cur.globals.lookup k = s0.globals.lookup k)
    (hloc_t : cur.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hloc_k : cur.locals.lookup (ofString "key") = some (.val (.word kw)))
    (hloc_old : cur.locals.lookup (ofString "old") = some (.rStruct [.val (.word f0), .val (.word f1)]))
    (he16 : ∀ st : PanSemStateFiniteExact 64 F,
      st.locals.lookup (ofString "old") = some (.rStruct [.val (.word f0), .val (.word f1)]) →
      @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) e16 =
        some (.val (.word w16)))
    (htw_ok : ∀ S, TablesTyped s0 S → tw.toNat ∈ S ∧
      let jrNew :=
        (tw.toNat, journalRole s0 tw.toNat) ::
          (if w16.toNat ≠ 0 ∧ journalRole s0 tw.toNat = "ts+32" then
            [(f1.toNat, "ts.inner")] else [])
      ∀ p ∈ jrNew, p ∈ worldRoleSlots s0)
    {tail : ProgHOL 64} {rv : ValueHOL 64} {out : PanSemStateFiniteExact 64 F}
    (hflow : evaluateHOLFiniteState cur (journalAppendTailProg trapCode e16 tail) =
      (some (.returned rv), out)) :
    ∃ mid tailPost,
      WorldStepCodeSc [] ["heap_ptr", "journal_n"] s0 none mid ∧
      mid.locals.lookup (ofString "t") = some (.val (.word tw)) ∧
      mid.locals.lookup (ofString "key") = some (.val (.word kw)) ∧
      mid.locals.lookup (ofString "value") = cur.locals.lookup (ofString "value") ∧
      evaluateHOLFiniteState mid tail = (some (.returned rv), tailPost) ∧
      out = { tailPost with locals := out.locals } := by
  have hAs0 := hW0.1
  have hcode : cur.code = originalRuntimeCode := heff0.code
  obtain ⟨_, S0, hWT0⟩ := hW0
  have hW0_full : WorldOK s0 := ⟨hAs0, S0, hWT0⟩
  have hJ0 := hWT0.2.1
  obtain ⟨jnw, hjn_lk0⟩ := hAs0.2.2.2.2.2.2.2.2.2 "journal_n" (by decide)
  obtain ⟨jcw, hjc_lk0⟩ := hAs0.2.2.2.2.2.2.2.2.2 "journal_cap" (by decide)
  obtain ⟨jw, hj_lk0⟩ := hAs0.2.2.2.2.2.2.2.2.2 "journal" (by decide)
  have hjn_cur : cur.globals.lookup (ofString "journal_n") = some (.val (.word jnw)) := by
    rw [hg_all_cur]; exact hjn_lk0
  have hjc_cur : cur.globals.lookup (ofString "journal_cap") = some (.val (.word jcw)) := by
    rw [hg_all_cur]; exact hjc_lk0
  have hjn_nat : globN s0 "journal_n" = jnw.toNat := by unfold GlobalWord at hjn_lk0; simp [globN, hjn_lk0]
  have hjc_nat : globN s0 "journal_cap" = jcw.toNat := by unfold GlobalWord at hjc_lk0; simp [globN, hjc_lk0]
  have hj_nat : globN s0 "journal" = jw.toNat := by unfold GlobalWord at hj_lk0; simp [globN, hj_lk0]
  unfold journalAppendTailProg at hflow
  rw [evaluateHOLFiniteState_seq_line780] at hflow
  have hjn_lt_jc : jnw.toNat < jcw.toNat := by
    by_contra hge
    have hnl : Compiler.Encoders.Asm.wordCmpHOL .notLower jnw jcw = true := by
      simp only [Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
      have hnotlt : ¬ jnw.toNat < jcw.toNat := by omega
      simp [hnotlt]
    have hev_cmp1 : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
        (.cmp .notLower (.var .global (ofString "journal_n")) (.var .global (ofString "journal_cap"))) =
        some (.val (.word 1#64)) := by
      simp [evalHOLExact, toExact, hjn_cur, hjc_cur, hnl]
    have hite_tr : evaluateHOLFiniteState cur
        (.ite (.cmp .notLower (.var .global (ofString "journal_n")) (.var .global (ofString "journal_cap")))
          (.call (some (none, none)) (ofString "trap_with") [.const trapCode]) .skip) =
        evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "trap_with") [.const trapCode]) := by
      rw [evaluateHOLFiniteState_ite, hev_cmp1]
      simp [show (1#64 : BitVec 64) ≠ 0 by decide]
    rw [hite_tr] at hflow
    obtain ⟨_, htr_none, _⟩ := seq_call0_ret_inv (by rw [evaluateHOLFiniteState_seq_line780]; exact hflow)
    have ⟨hno_none, _⟩ := trap_with_call_no_none_resumes_code cur trapCode hcode
    exact hno_none (congrArg Prod.fst htr_none)
  have hite_ok : evaluateHOLFiniteState cur
      (.ite (.cmp .notLower (.var .global (ofString "journal_n")) (.var .global (ofString "journal_cap")))
        (.call (some (none, none)) (ofString "trap_with") [.const trapCode]) .skip) = (none, cur) := by
    have hnl : Compiler.Encoders.Asm.wordCmpHOL .notLower jnw jcw = false := by
      simp only [Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
      simp [hjn_lt_jc]
    have hev_cmp0 : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
        (.cmp .notLower (.var .global (ofString "journal_n")) (.var .global (ofString "journal_cap"))) =
        some (.val (.word 0#64)) := by
      simp [evalHOLExact, toExact, hjn_cur, hjc_cur, hnl]
    rw [evaluateHOLFiniteState_ite, hev_cmp0]
    simp [evaluateHOLFiniteState_skip]
  rw [hite_ok] at hflow; dsimp only at hflow
  have hjn_lt0 : globN s0 "journal_n" < globN s0 "journal_cap" := by omega
  have hjcap_nz : globN s0 "journal_cap" ≠ 0 := by omega
  rcases hJ0.2.2.1 with hjc0 | ⟨hal_jr0, hw_jr0⟩
  · exact absurd hjc0 hjcap_nz
  have hj_hi0 := (R10Shards.P26_P28.ivl_allocated_bound hAs0.2 hal_jr0).2
  set jrec : Ivl := (globN s0 "journal" + 32 * jnw.toNat, 32)
  have hjrec_hi : jrec.1 + 32 ≤ heapEnd := by
    have hhl_he : heapLimit ≤ heapEnd := by decide
    have hse_he : scratchEnd ≤ heapEnd := by decide
    rcases hal_jr0 with ⟨_, hhi⟩ | ⟨_, hhi⟩ <;> (have := hAs0.2.2.1; have := hAs0.2.2.2.2.1; dsimp [jrec] at *; omega)
  obtain ⟨klw, hkl_ev, m_kl, hflow_kl, hout_eq1⟩ := dec_ret_inv hflow
  set s_kl := setVarHOLFinite (ofString "klen") (.val (.word klw)) cur
  have heff_kl : WorldEff s0 s_kl [jrec] [] ["heap_ptr"] :=
    (heff0.mono (by intro _ h; cases h) (by intro _ h; cases h) (by intro _ h; exact h)).locals_clock _ _
  change evaluateHOLFiniteState s_kl _ = (some (.returned rv), m_kl) at hflow_kl
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hflow_kl
  have hkl_loc : s_kl.locals.lookup (ofString "klen") = some (.val (.word klw)) := by
    simp [s_kl, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hargs_al : evalListHOLFinite s_kl (h := fun a => Classical.propDecidable (s_kl.memaddrs a))
      [.var .local (ofString "klen")] = some [.val (.word klw)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, hkl_loc]
  have hlk_al := pan_one_word_lookup s_kl.code.lookup (ofString "alloc") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_alloc) klw (by rw [heff_kl.code]; exact lookup_alloc_r16)
  rw [hargs_al] at hflow_kl; dsimp only at hflow_kl; rw [hlk_al] at hflow_kl; dsimp only at hflow_kl
  by_cases hcz_kl : s_kl.clock = 0
  · simp [hcz_kl] at hflow_kl
  rw [if_neg hcz_kl] at hflow_kl
  obtain ⟨pw, hpw_lk⟩ : ∃ pw : BitVec 64, s_kl.globals.lookup (ofString "heap_ptr") = some (.val (.word pw)) :=
    globalWord_of_globN_pos s_kl "heap_ptr"
      (by have := heff_kl.arena.2.1; have hsb : sourceBase = 2701131776 := rfl; omega)
  let ent_al := callEntryStateHOLFinite s_kl (HolFiniteMapExact.empty.update (ofString "n", .val (.word klw)))
  rcases hrun_al : evaluateHOLFiniteState ent_al (sourceFnBody Guest.Software.guestFn_alloc) with ⟨res_al, pa_al⟩
  dsimp only [ent_al] at hrun_al
  rw [hrun_al] at hflow_kl
  have hres_al : Resumes res_al := by
    cases res_al with
    | none => simp at hflow_kl
    | some cra =>
      cases cra with
      | returned _ => exact Or.inl ⟨_, rfl⟩
      | exception eid _ =>
        dsimp only at hflow_kl; injection hflow_kl with hr_eq _; cases hr_eq
      | _ => simp at hflow_kl
  have hal_spec := InitECandidate.Solver.Wave8GuestInv.R13.alloc_body_resumes ent_al pw heff_kl.code hpw_lk
    (by dsimp only [ent_al]; rw [hrun_al]; exact hres_al)
  dsimp only [ent_al] at hal_spec; rw [hrun_al] at hal_spec
  obtain ⟨klw', hklw'_lk, hrv_al, hcmp1, hcmp2, hpa_al⟩ := hal_spec
  have hklw_eq : klw = klw' := by
    have : ent_al.locals.lookup (ofString "n") = some (.val (.word klw)) := by
      simp [ent_al, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rw [this] at hklw'_lk; injection hklw'_lk with h'; injection h' with h'; injection h'
  subst hklw_eq
  dsimp only at hrv_al hpa_al; subst hrv_al
  have hsh_pw_al : (shapeEqHOL (shapeOfHOLExact (.val (.word pw))) .one &&
      shapeEqHOL (shapeOfHOLExact (.val (.word pw))) .one) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  dsimp only at hflow_kl
  rw [if_pos hsh_pw_al] at hflow_kl
  set s_kc := setVarHOLFinite (ofString "kc") (.val (.word pw)) { pa_al with locals := s_kl.locals }
  have hs_kc_next : s_kc = { s_kl with
      globals := s_kl.globals.update (ofString "heap_ptr", .val (.word ((pw + (klw + 7)) &&& ((0 : BitVec 64) - 8)))),
      locals := s_kc.locals, clock := s_kc.clock } := by
    dsimp only [s_kc, setVarHOLFinite]; rw [hpa_al]; rfl
  obtain ⟨heff_kc, _, _, _, hpw_lo_s0, hpw_add, hhp_kc_lim, _⟩ :=
    R16Shards.worldEff_alloc_step heff_kl (by simp) hpw_lk hcmp1 hcmp2 hs_kc_next
  rcases hcont_kc : evaluateHOLFiniteState s_kc
      (.seq
        (.call (some (none, none)) (ofString "memcpy")
          [.var .local (ofString "kc"), .var .local (ofString "key"), .var .local (ofString "klen")])
        (.dec (ofString "r") .one
          (.op .add [.var .global (ofString "journal"),
            .panop .mul [.var .global (ofString "journal_n"), .const 32#64]])
          (.seq
            (.store (.var .local (ofString "r")) (.var .local (ofString "t")))
            (.seq
              (.store (.op .add [.var .local (ofString "r"), .const 8#64]) (.var .local (ofString "kc")))
              (.seq
                (.store (.op .add [.var .local (ofString "r"), .const 16#64]) e16)
                (.seq
                  (.store (.op .add [.var .local (ofString "r"), .const 24#64])
                    (.rfield 1 (.var .local (ofString "old"))))
                  (.seq
                    (.assign .global (ofString "journal_n")
                      (.op .add [.var .global (ofString "journal_n"), .const 1#64]))
                    tail))))))) with ⟨rkc, m_kc⟩
  rw [hcont_kc] at hflow_kl
  dsimp only at hflow_kl
  have hrv_kc_eq : rkc = some (.returned rv) := (Prod.mk.inj hflow_kl).1
  have hm_kl_eq : m_kl = { m_kc with locals := (HolFiniteMapExact.resVarEq m_kc.locals
      (ofString "kc", s_kl.locals.lookup (ofString "kc"))) } := ((Prod.mk.inj hflow_kl).2).symm
  cases rkc with
  | none => simp at hrv_kc_eq
  | some cr_kc =>
    cases cr_kc with
    | returned rv_kc =>
      injection hrv_kc_eq with hrv_kc'; injection hrv_kc' with hrv_kc''; subst hrv_kc''
      obtain ⟨s_mc, hmc, hcont_mc⟩ := seq_call0_ret_inv hcont_kc
      have hkc_loc : s_kc.locals.lookup (ofString "kc") = some (.val (.word pw)) := by
        simp [s_kc, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hk_loc_kc : s_kc.locals.lookup (ofString "key") = some (.val (.word kw)) := by
        simp [s_kc, s_kl, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hloc_k,
          show ofString "kc" ≠ ofString "key" by decide, show ofString "klen" ≠ ofString "key" by decide]
      have hkl_loc_kc : s_kc.locals.lookup (ofString "klen") = some (.val (.word klw)) := by
        simp [s_kc, s_kl, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "kc" ≠ ofString "klen" by decide]
      have heff_mc : WorldEff s0 s_mc [jrec] [] ["heap_ptr"] := by
        have hm := worldEff_call0_memcpy heff_kc
          (.var .local (ofString "kc")) (.var .local (ofString "key")) (.var .local (ofString "klen"))
          (by rw [hmc]; simp) (by rw [hmc]; exact Or.inl rfl)
          (fun dw sw nw hd _ hn _ => by
            simp [evalHOLExact, toExact, hkc_loc] at hd; subst hd
            simp [evalHOLExact, toExact, hkl_loc_kc] at hn; subst hn
            exact Or.inr (Or.inr (Or.inr ⟨hpw_lo_s0, by omega⟩)))
        rw [hmc] at hm; exact hm
      have hmc_g : s_mc.globals = s_kc.globals := by
        have hargs_mc : evalListHOLFinite s_kc (h := fun a => Classical.propDecidable (s_kc.memaddrs a))
            [.var .local (ofString "kc"), .var .local (ofString "key"), .var .local (ofString "klen")] =
            some [.val (.word pw), .val (.word kw), .val (.word klw)] := by
          rw [evalListHOLFinite_eq_toExact]
          simp [evalListHOLExact, evalHOLExact, toExact, hkc_loc, hk_loc_kc, hkl_loc_kc]
        have hb_mc := Fast_C08WkShard03.call0_byteEff Fast_C08WkShard03.funByteEff_memcpy s_kc
          [.var .local (ofString "kc"), .var .local (ofString "key"), .var .local (ofString "klen")]
          [(pw.toNat, klw.toNat)] heff_kc.code heff_kc.arena.1
          (fun vals hvs i hi _ => by
            rw [hargs_mc] at hvs; injection hvs with hvs_eq; subst hvs_eq
            simp only [List.mem_singleton, Fast_C08WkShard03.valWordNat] at hi
            subst hi
            exact ⟨(pw.toNat, klw.toNat), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)
          (by rw [hmc]; simp) (by rw [hmc]; exact Or.inl rfl)
        rw [hmc] at hb_mc
        exact hb_mc.globals
      have hmc_loc : s_mc.locals = s_kc.locals := by
        have hk := fun k => evaluate_avoidsLocal_flowing k
          (.call (some (none, none)) (ofString "memcpy")
            [.var .local (ofString "kc"), .var .local (ofString "key"), .var .local (ofString "klen")])
          rfl s_kc (by rw [hmc]; exact Or.inl rfl)
        apply HolFiniteMapExact.ext; funext k; simpa [hmc] using hk k
      obtain ⟨rw, hr_ev, m_r, hflow_r, hm_kc_eq⟩ := dec_ret_inv hcont_mc
      have hs_mc_g_no_hp : ∀ k : MlS, k ≠ ofString "heap_ptr" → s_mc.globals.lookup k = s0.globals.lookup k := by
        intro k hk
        rw [hmc_g, hs_kc_next]
        simp [s_kl, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hk.symm, hg_all_cur]
      have hrw_eq : rw = jw + jnw * 32#64 := by
        have hj_mc : s_mc.globals.lookup (ofString "journal") = some (.val (.word jw)) := by
          rw [hs_mc_g_no_hp _ (by decide)]; exact hj_lk0
        have hjn_mc : s_mc.globals.lookup (ofString "journal_n") = some (.val (.word jnw)) := by
          rw [hs_mc_g_no_hp _ (by decide)]; exact hjn_lk0
        simp only [evalHOLExact, evalListHOLExact, toExact, hj_mc, hjn_mc, List.all, List.map,
          Option.map, Bool.and_self, ↓reduceIte, List.foldr, valueIsWord, valueWord,
          wordOpHOL, wordOp, panOpHOL] at hr_ev
        have hz : jnw * 32#64 + (0 : BitVec 64) = jnw * 32#64 := BitVec.add_zero _
        rw [hz] at hr_ev
        injection hr_ev with hr'; injection hr' with hr'; injection hr' with hr'; exact hr'.symm
      have hrw_nat : rw.toNat = globN s0 "journal" + 32 * jnw.toNat := by
        subst hrw_eq
        have hmul : (jnw * 32#64).toNat = 32 * jnw.toNat := by
          rw [BitVec.toNat_mul, show (32#64 : BitVec 64).toNat = 32 from rfl]
          change (jnw.toNat * 32) % 2 ^ 64 = 32 * jnw.toNat
          rw [Nat.mul_comm, Nat.mod_eq_of_lt (by dsimp at hj_hi0; omega)]
        rw [BitVec.toNat_add, hj_nat, hmul, Nat.mod_eq_of_lt (by dsimp at hj_hi0; omega)]
      set s_r := setVarHOLFinite (ofString "r") (.val (.word rw)) s_mc
      have heff_r : WorldEff s0 s_r [jrec] [] ["heap_ptr"] := heff_mc.locals_clock _ _
      have hr_loc : s_r.locals.lookup (ofString "r") = some (.val (.word rw)) := by
        simp [s_r, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have ht_loc_r : s_r.locals.lookup (ofString "t") = some (.val (.word tw)) := by
        simp [s_r, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmc_loc, s_kc, s_kl, hloc_t,
          show ofString "r" ≠ ofString "t" by decide,
          show ofString "kc" ≠ ofString "t" by decide,
          show ofString "klen" ≠ ofString "t" by decide]
      have hkc_loc_r : s_r.locals.lookup (ofString "kc") = some (.val (.word pw)) := by
        simp [s_r, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmc_loc, hkc_loc,
          show ofString "r" ≠ ofString "kc" by decide]
      have hold_loc_r : s_r.locals.lookup (ofString "old") = some (.rStruct [.val (.word f0), .val (.word f1)]) := by
        simp [s_r, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmc_loc, s_kc, s_kl, hloc_old,
          show ofString "r" ≠ ofString "old" by decide,
          show ofString "kc" ≠ ofString "old" by decide,
          show ofString "klen" ≠ ofString "old" by decide]
      obtain ⟨s_st0, hst0, hflow_st0⟩ := seq_store_ret_inv hflow_r
      obtain ⟨dw0, vw0, hdw0, hvw0, _, hs_st0_eq⟩ := store_word_none_inv hst0
        (fun v hv => by simp [evalHOLExact, toExact, ht_loc_r] at hv; exact ⟨tw, hv.symm⟩)
      have hdw0_eq : dw0 = rw := by simp [evalHOLExact, toExact, hr_loc] at hdw0; exact hdw0.symm
      have hvw0_eq : vw0 = tw := by simp [evalHOLExact, toExact, ht_loc_r] at hvw0; exact hvw0.symm
      rw [hdw0_eq, hvw0_eq] at hs_st0_eq
      have heff_st0 : WorldEff s0 s_st0 [jrec] [] ["heap_ptr"] := by
        have hw := R16Shards.worldEff_store_word heff_r (.var .local (ofString "r")) (.var .local (ofString "t"))
          (fun v hv => by simp [evalHOLExact, toExact, ht_loc_r] at hv; exact ⟨tw, hv.symm⟩)
          (fun x hx _ => by
            simp [evalHOLExact, toExact, hr_loc] at hx; subst hx
            exact Or.inl ⟨jrec, List.mem_singleton.2 rfl, by dsimp [jrec]; omega, by dsimp [jrec]; omega⟩)
        rw [hst0] at hw; exact hw
      obtain ⟨s_st8, hst8, hflow_st8⟩ := seq_store_ret_inv hflow_st0
      have hst0_loc : s_st0.locals = s_r.locals := by rw [hs_st0_eq]
      obtain ⟨dw8, vw8, hdw8, hvw8, _, hs_st8_eq⟩ := store_word_none_inv hst8
        (fun v hv => by simp [evalHOLExact, toExact, hst0_loc, hkc_loc_r] at hv; exact ⟨pw, hv.symm⟩)
      have hdw8_eq : dw8 = rw + 8#64 := by
        simp [evalHOLExact, evalListHOLExact, toExact, hst0_loc, hr_loc, wordOpHOL, wordOp, valueIsWord, valueWord] at hdw8
        exact hdw8.symm
      have hvw8_eq : vw8 = pw := by simp [evalHOLExact, toExact, hst0_loc, hkc_loc_r] at hvw8; exact hvw8.symm
      rw [hdw8_eq, hvw8_eq] at hs_st8_eq
      have hrw8_nat : (rw + 8#64).toNat = rw.toNat + 8 := by
        apply BitVec.toNat_add_of_lt; change rw.toNat + 8 < 2 ^ 64; dsimp at hj_hi0; omega
      have heff_st8 : WorldEff s0 s_st8 [jrec] [] ["heap_ptr"] := by
        have hw := R16Shards.worldEff_store_word heff_st0
          (.op .add [.var .local (ofString "r"), .const 8#64]) (.var .local (ofString "kc"))
          (fun v hv => by simp [evalHOLExact, toExact, hst0_loc, hkc_loc_r] at hv; exact ⟨pw, hv.symm⟩)
          (fun x hx _ => by
            simp [evalHOLExact, evalListHOLExact, toExact, hst0_loc, hr_loc, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
            subst hx
            exact Or.inl ⟨jrec, List.mem_singleton.2 rfl, by dsimp [jrec]; omega, by dsimp [jrec]; omega⟩)
        rw [hst8] at hw; exact hw
      obtain ⟨s_st16, hst16, hflow_st16⟩ := seq_store_ret_inv hflow_st8
      have hst8_loc : s_st8.locals = s_r.locals := by rw [hs_st8_eq, hst0_loc]
      have he16_st8 := he16 s_st8 (by rw [hst8_loc]; exact hold_loc_r)
      obtain ⟨dw16, vw16, hdw16, hvw16, _, hs_st16_eq⟩ := store_word_none_inv hst16
        (fun v hv => by rw [he16_st8] at hv; injection hv with hv'; exact ⟨w16, hv'.symm⟩)
      have hdw16_eq : dw16 = rw + 16#64 := by
        simp [evalHOLExact, evalListHOLExact, toExact, hst8_loc, hr_loc, wordOpHOL, wordOp, valueIsWord, valueWord] at hdw16
        exact hdw16.symm
      have hvw16_eq : vw16 = w16 := by
        rw [he16_st8] at hvw16; injection hvw16 with h'; injection h' with h'; injection h' with h'; exact h'.symm
      rw [hdw16_eq, hvw16_eq] at hs_st16_eq
      have hrw16_nat : (rw + 16#64).toNat = rw.toNat + 16 := by
        apply BitVec.toNat_add_of_lt; change rw.toNat + 16 < 2 ^ 64; dsimp at hj_hi0; omega
      have heff_st16 : WorldEff s0 s_st16 [jrec] [] ["heap_ptr"] := by
        have hw := R16Shards.worldEff_store_word heff_st8
          (.op .add [.var .local (ofString "r"), .const 16#64]) e16
          (fun v hv => by rw [he16_st8] at hv; injection hv with hv'; exact ⟨w16, hv'.symm⟩)
          (fun x hx _ => by
            simp [evalHOLExact, evalListHOLExact, toExact, hst8_loc, hr_loc, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
            subst hx
            exact Or.inl ⟨jrec, List.mem_singleton.2 rfl, by dsimp [jrec]; omega, by dsimp [jrec]; omega⟩)
        rw [hst16] at hw; exact hw
      obtain ⟨s_st24, hst24, hflow_st24⟩ := seq_store_ret_inv hflow_st16
      have hst16_loc : s_st16.locals = s_r.locals := by rw [hs_st16_eq, hst8_loc]
      have he24 : @evalHOLExact 64 F _ s_st16.toExact (fun a => Classical.propDecidable (s_st16.memaddrs a))
          (.rfield 1 (.var .local (ofString "old"))) = some (.val (.word f1)) := by
        simp [evalHOLExact, toExact, hst16_loc, hold_loc_r]
      obtain ⟨dw24, vw24, hdw24, hvw24, _, hs_st24_eq⟩ := store_word_none_inv hst24
        (fun v hv => by rw [he24] at hv; injection hv with hv'; exact ⟨f1, hv'.symm⟩)
      have hdw24_eq : dw24 = rw + 24#64 := by
        simp [evalHOLExact, evalListHOLExact, toExact, hst16_loc, hr_loc, wordOpHOL, wordOp, valueIsWord, valueWord] at hdw24
        exact hdw24.symm
      have hvw24_eq : vw24 = f1 := by
        rw [he24] at hvw24; injection hvw24 with h'; injection h' with h'; injection h' with h'; exact h'.symm
      rw [hdw24_eq, hvw24_eq] at hs_st24_eq
      have hrw24_nat : (rw + 24#64).toNat = rw.toNat + 24 := by
        apply BitVec.toNat_add_of_lt; change rw.toNat + 24 < 2 ^ 64; dsimp at hj_hi0; omega
      have heff_st24 : WorldEff s0 s_st24 [jrec] [] ["heap_ptr"] := by
        have hw := R16Shards.worldEff_store_word heff_st16
          (.op .add [.var .local (ofString "r"), .const 24#64]) (.rfield 1 (.var .local (ofString "old")))
          (fun v hv => by rw [he24] at hv; injection hv with hv'; exact ⟨f1, hv'.symm⟩)
          (fun x hx _ => by
            simp [evalHOLExact, evalListHOLExact, toExact, hst16_loc, hr_loc, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
            subst hx
            exact Or.inl ⟨jrec, List.mem_singleton.2 rfl, by dsimp [jrec]; omega, by dsimp [jrec]; omega⟩)
        rw [hst24] at hw; exact hw
      obtain ⟨mid, hass_step, htail_run⟩ := seq_assign_ret_inv hflow_st24
      have hst24_g : s_st24.globals = s_mc.globals := by
        rw [hs_st24_eq, hs_st16_eq, hs_st8_eq, hs_st0_eq]; rfl
      have hjn_st24 : s_st24.globals.lookup (ofString "journal_n") = some (.val (.word jnw)) := by
        rw [hst24_g, hs_mc_g_no_hp _ (by decide)]; exact hjn_lk0
      have hass : evaluateHOLFiniteState s_st24
          (.assign .global (ofString "journal_n")
            (.op .add [.var .global (ofString "journal_n"), .const 1#64])) =
          (none, setGlobalHOLFinite (ofString "journal_n") (.val (.word (jnw + 1#64))) s_st24) := by
        simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, toExact,
          hjn_st24, wordOpHOL, wordOp, valueIsWord, valueWord, lookupKvarHOLExact,
          isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
      rw [hass] at hass_step
      have hmid_eq : mid = setGlobalHOLFinite (ofString "journal_n") (.val (.word (jnw + 1#64))) s_st24 :=
        ((Prod.mk.inj hass_step).2).symm
      have hmid_mem : mid.memory = s_st24.memory := by rw [hmid_eq]; rfl
      have hmid_g : mid.globals = s_st24.globals.update (ofString "journal_n", .val (.word (jnw + 1#64))) := by
        rw [hmid_eq]; rfl
      have hmid_be : mid.be = s0.be := by rw [hmid_eq]; exact heff_st24.be
      have hne_0_8 : rw ≠ rw + 8#64 := fun h => by have := congrArg BitVec.toNat h; omega
      have hne_0_16 : rw ≠ rw + 16#64 := fun h => by have := congrArg BitVec.toNat h; omega
      have hne_0_24 : rw ≠ rw + 24#64 := fun h => by have := congrArg BitVec.toNat h; omega
      have hne_16_24 : rw + 16#64 ≠ rw + 24#64 := fun h => by have := congrArg BitVec.toNat h; omega
      have hm_r0 : memW mid (globN s0 "journal" + 32 * jnw.toNat) = tw.toNat := by
        have hbv0 : BitVec.ofNat 64 (globN s0 "journal" + 32 * jnw.toNat) = rw := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_ofNat, hrw_nat, Nat.mod_eq_of_lt (by dsimp at hj_hi0; omega)]
        unfold memW; rw [hbv0, hmid_mem, hs_st24_eq, hs_st16_eq, hs_st8_eq, hs_st0_eq]
        simp [hne_0_24, hne_0_16, hne_0_8]
      have hm_r16 : memW mid (globN s0 "journal" + 32 * jnw.toNat + 16) = w16.toNat := by
        have hbv16 : BitVec.ofNat 64 (globN s0 "journal" + 32 * jnw.toNat + 16) = rw + 16#64 := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_ofNat, hrw16_nat, hrw_nat, Nat.mod_eq_of_lt (by dsimp at hj_hi0; omega)]
        unfold memW; rw [hbv16, hmid_mem, hs_st24_eq, hs_st16_eq]
        simp [hne_16_24]
      have hm_r24 : memW mid (globN s0 "journal" + 32 * jnw.toNat + 24) = f1.toNat := by
        have hbv24 : BitVec.ofNat 64 (globN s0 "journal" + 32 * jnw.toNat + 24) = rw + 24#64 := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_ofNat, hrw24_nat, hrw_nat, Nat.mod_eq_of_lt (by dsimp at hj_hi0; omega)]
        unfold memW; rw [hbv24, hmid_mem, hs_st24_eq]
        simp
      have hhp_mid_eq : globN mid "heap_ptr" = globN s_st24 "heap_ptr" := by
        apply globN_eq_of_lookup
        rw [hmid_g]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "journal_n" ≠ ofString "heap_ptr" by decide]
      have hfmp_mid_eq : globN mid "frame_mem_ptr" = globN s_st24 "frame_mem_ptr" := by
        apply globN_eq_of_lookup
        rw [hmid_g]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "journal_n" ≠ ofString "frame_mem_ptr" by decide]
      have hsp_mid_eq : globN mid "scratch_ptr" = globN s_st24 "scratch_ptr" := by
        apply globN_eq_of_lookup
        rw [hmid_g]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "journal_n" ≠ ofString "scratch_ptr" by decide]
      have hA_mid : ArenaReady mid := by
        have hG_mid : GuestInv mid := by
          have hG24 := heff_st24.arena.1
          rw [hmid_eq]
          exact ⟨hG24.code, hG24.memaddrs, hG24.shMemaddrs, hG24.baseAddr⟩
        refine ⟨hG_mid, ?_⟩
        unfold ArenaOK
        have hA24 := heff_st24.arena.2
        rw [hhp_mid_eq, hfmp_mid_eq, hsp_mid_eq]
        refine ⟨hA24.1, hA24.2.1, hA24.2.2.1, hA24.2.2.2.1, hA24.2.2.2.2.1,
          hA24.2.2.2.2.2.1, hA24.2.2.2.2.2.2.1, hA24.2.2.2.2.2.2.2.1, ?_⟩
        intro g hg
        by_cases hgj : ofString g = ofString "journal_n"
        · refine ⟨jnw + 1#64, ?_⟩
          unfold GlobalWord; rw [hmid_g, hgj]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
        · obtain ⟨w, hw⟩ := hA24.2.2.2.2.2.2.2.2 g hg
          refine ⟨w, ?_⟩
          unfold GlobalWord at hw ⊢
          rw [hmid_g]; simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hgj, hw]
      have hjn_mid : globN mid "journal_n" = globN s0 "journal_n" + 1 := by
        have hjc_max : globN s0 "journal_cap" ≤ journalCapMax := hJ0.2.1
        have hjcm_val : journalCapMax = 524288 := rfl
        have hadd1 : (jnw + 1#64).toNat = jnw.toNat + 1 := by
          apply BitVec.toNat_add_of_lt
          change jnw.toNat + 1 < 2 ^ 64; omega
        have hlk_mid : mid.globals.lookup (ofString "journal_n") = some (.val (.word (jnw + 1#64))) := by
          rw [hmid_g]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
        rw [hjn_nat]
        unfold globN; simp [hlk_mid, hadd1]
      have hg_kept_mid : GlobalsKept ["heap_ptr", "journal_n"] s0 mid := by
        intro k hk
        have hne_hp : k ≠ ofString "heap_ptr" := fun h => hk (by simp [h])
        have hne_jn : k ≠ ofString "journal_n" := fun h => hk (by simp [h])
        rw [hmid_g]
        have hlk_k : (s_st24.globals.update (ofString "journal_n", .val (.word (jnw + 1#64)))).lookup k =
            s_st24.globals.lookup k := by
          simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne_jn]
        rw [hlk_k]
        exact heff_st24.gw_kept k (by simp [hne_hp])
      have hstep : WorldStepCodeSc [] ["heap_ptr", "journal_n"] s0 none mid :=
        worldStepCodeSc_of_journal_append jnw hW0_full hA_mid hmid_be
          (by rw [hhp_mid_eq]; exact heff_st24.hp_lo) hg_kept_mid hjn_nat hjn_lt0 hjn_mid
          (fun x hx => heff_st24.out_dom x (by rwa [← hmid_mem]))
          (fun x hx => by
            rcases heff_st24.cell_frame x (by rwa [← hmid_mem]) with ⟨iv, hiv, hhit⟩ | ⟨_, h, _⟩ | hfg | hhf
            · simp only [List.mem_singleton] at hiv; subst hiv; exact Or.inl hhit
            · cases h
            · exact Or.inr (Or.inl hfg)
            · exact Or.inr (Or.inr hhf))
          (fun a ha hne => by
            have hmb_mid : memB mid a = memB s_st24 a := by
              unfold memB; rw [hmid_mem, hmid_be, heff_st24.be]
            rcases heff_st24.byte_frame a ha (by rwa [← hmb_mid]) with ⟨iv, hiv, hin⟩ | ⟨_, h, _⟩ | hfg | hhf
            · simp only [List.mem_singleton] at hiv; subst hiv; exact Or.inl hin
            · cases h
            · exact Or.inr (Or.inl hfg)
            · exact Or.inr (Or.inr hhf))
          hm_r0
          (fun S hTS => by
            dsimp only
            rw [hm_r16, hm_r24]
            exact htw_ok S hTS)
      have hs_st24_loc : s_st24.locals = s_r.locals := by rw [hs_st24_eq, hst16_loc]
      have hmid_loc : mid.locals = s_r.locals := by rw [hmid_eq]; exact hs_st24_loc
      have hmid_loc_other : ∀ x : MlS, x ≠ ofString "klen" → x ≠ ofString "kc" → x ≠ ofString "r" →
          mid.locals.lookup x = cur.locals.lookup x := by
        intro x hx_kl hx_kc hx_r
        rw [hmid_loc]
        simp [s_r, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          Ne.symm hx_r, hmc_loc, s_kc, Ne.symm hx_kc, s_kl, Ne.symm hx_kl]
      have hout_tp : out = { m_r with locals := out.locals } := by
        rw [hout_eq1, hm_kl_eq, hm_kc_eq]
      exact ⟨mid, m_r, hstep,
        (hmid_loc_other _ (by decide) (by decide) (by decide)).trans hloc_t,
        (hmid_loc_other _ (by decide) (by decide) (by decide)).trans hloc_k,
        hmid_loc_other _ (by decide) (by decide) (by decide),
        htail_run, hout_tp⟩
    | _ => simp at hflow_kl

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
