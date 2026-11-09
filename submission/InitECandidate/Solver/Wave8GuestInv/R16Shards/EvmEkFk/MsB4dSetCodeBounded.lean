import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.MsB4d0SetCodeJset

/-!
# Scratch Rung B4d: Bounded `set_code` on `EvmMsgReadyMsgBounded` & `D0PreB`

Proves that `set_code(addr, code, code_len)` under `code_len < 2^40` preserves
`EvmMsgReadyMsgBounded`, establishes `EvmStepCC ["heap_ptr", "journal_n", "scratch_ptr"]`,
and preserves `memW _ (globN s "ev" + 112)`, plus its `Hoare` call wrapper on `D0PreB`.
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
open InitECandidate.Solver.Wave8GuestInv.HtabC00Ports
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemBridge
open InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_GbodyC17ToC21
  (IvlUnhit not_cellHits_of_disj memW_eq_of_ivlUnhit)
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28

private theorem memW_store_word_exact_b4d {F : Type}
    {cur post : PanSemStateFiniteExact 64 F}
    {dstExp valExp : ExpHOL 64} {dst w : BitVec 64}
    (hdst : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) dstExp =
      some (.val (.word dst)))
    (hval : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) valExp =
      some (.val (.word w)))
    (hflow : evaluateHOLFiniteState cur (.store dstExp valExp) = (none, post)) :
    memW post dst.toNat = w.toNat := by
  rw [evaluateHOLFiniteState_store] at hflow
  simp only [hdst, hval, flattenHOL, panMemStoresHOL, panMemStoreHOL] at hflow
  by_cases hd : cur.memaddrs dst
  · simp only [hd, ↓reduceIte, Prod.mk.injEq] at hflow
    obtain ⟨-, rfl⟩ := hflow
    unfold memW
    have hbv : BitVec.ofNat 64 dst.toNat = dst := by simp
    rw [hbv]; simp
  · simp [hd] at hflow

/-- Master cell-preservation helper for the `m3 -> ms3` alloc step: an interval that is
allocated and aligned in the pre-state and disjoint from every `wsAcctBufs` buffer region is
untouched by a `WorldEff s cur [] wsAcctBufs ["heap_ptr"]` step. -/
private theorem ivlUnhit_of_worldEff_wsAcct_b4d {F : Type}
    {s cur : PanSemStateFiniteExact 64 F}
    (hAs : ArenaOK s)
    (heff : WorldEff s cur [] wsAcctBufs ["heap_ptr"])
    {i : Ivl} (hw : WordsOK s i) (hi_al : AllocatedEvmB4d s i)
    (hi_buf : ∀ gs ∈ wsAcctBufs, Disj i (bufferRegion s gs)) :
    IvlUnhit s cur i := by
  intro a ha8 hhit
  by_cases hmem : cur.memory a = s.memory a
  · exact hmem
  · exfalso
    have hd_fg := allocatedEvm_disj_freeGap_b4d hAs (Or.inr hi_al)
    have hd_hf := allocatedEvm_disj_heapFree_b4d hAs (Or.inr hi_al)
    rcases heff.cell_frame a hmem with ⟨j, hj, hpos, hc1, hc2⟩ | ⟨gs, hgs, hpos, hc1, hc2⟩
      | ⟨hpos, hc1, hc2⟩ | ⟨hpos, hc1, hc2⟩
    · exact absurd hj (by simp)
    · exact not_cellHits_of_disj hw.1 hw.2.1 ha8
        (fun hz => by
          simp only [bufferRegion] at hz ⊢
          by_cases h0 : globN s gs.1 = 0
          · rw [h0]
          · rw [if_neg h0] at hz; exfalso
            simp only [wsAcctBufs, List.mem_cons, List.not_mem_nil, or_false] at hgs
            rcases hgs with rfl | rfl | rfl <;> omega)
        hhit (hi_buf gs hgs) ⟨hc1, hc2⟩
    · exact not_cellHits_of_disj hw.1 hw.2.1 ha8
        (fun _ => by show globN s "frame_mem_ptr" % 8 = 0; exact hAs.2.2.2.2.2.2.1)
        hhit hd_fg ⟨hc1, hc2⟩
    · exact not_cellHits_of_disj hw.1 hw.2.1 ha8
        (fun _ => by show globN s "heap_ptr" % 8 = 0; exact hAs.2.2.2.2.2.1)
        hhit hd_hf ⟨hc1, hc2⟩

private theorem progWStepCode_acctCopy_mut_b4d {B : BufList} {gw : List String}
    (hhp_in : "heap_ptr" ∈ gw) (mutProg : ProgHOL 64)
    (hmut : ∀ {F : Type} (s s1 : PanSemStateFiniteExact 64 F) (bw : BitVec 64),
      WorldEff s s1 [] [] ["heap_ptr"] →
      s1.locals = s.locals.update (ofString "a", .val (.word bw)) →
      s1.locals.lookup (ofString "a") = some (.val (.word bw)) →
      globN s "heap_ptr" ≤ bw.toNat → bw.toNat + 56 ≤ heapLimit →
      (evaluateHOLFiniteState s1 mutProg).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState s1 mutProg).1 →
      WorldEff s (evaluateHOLFiniteState s1 mutProg).2 [] [] ["heap_ptr"]) :
    ProgWStepCode B gw
      (.seq
        (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
          [.var .local (ofString "a")])
        mutProg) := by
  intro F s hc hW hnt hfr
  rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
  rcases h1 : evaluateHOLFiniteState s
      (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
        [.var .local (ofString "a")]) with ⟨r1, s1⟩
  simp only [h1] at hnt hfr ⊢
  cases r1 with
  | some cr1 =>
    have hac := acct_copy_step_code s hc hW.1 (by rw [h1]; exact hnt) (by rw [h1]; exact hfr)
    rw [h1] at hac
    have hws0 : WorldStepCodeSc [] ["heap_ptr"] s (some cr1) s1 :=
      worldEff_to_worldStepCodeSc (B := []) (r := some cr1) hW
        (by decide) (by intro _ hp; cases hp) (by decide) hac.1
    exact worldStepCodeSc_mono_bufs (fun _ h => by cases h) (by simp [hhp_in]) hws0
  | none =>
    dsimp only at hnt hfr ⊢
    have hac := acct_copy_step_code s hc hW.1 (by rw [h1]; simp) (by rw [h1]; exact Or.inl rfl)
    rw [h1] at hac; dsimp only at hac
    obtain ⟨bw, hs1_loc, hbw_lo, hbw_hi⟩ := hac.2 rfl
    have hs1_a : s1.locals.lookup (ofString "a") = some (.val (.word bw)) := by
      rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hcr := contOrRes_of_flowingOrResumes_b4d hfr
    have heff2 := hmut s s1 bw hac.1 hs1_loc hs1_a hbw_lo hbw_hi hnt hcr
    have hws0 : WorldStepCodeSc [] ["heap_ptr"] s
        (evaluateHOLFiniteState s1 mutProg).1 (evaluateHOLFiniteState s1 mutProg).2 :=
      worldEff_to_worldStepCodeSc (B := []) (r := (evaluateHOLFiniteState s1 mutProg).1) hW
        (by decide) (by intro _ hp; cases hp) (by decide) heff2
    exact worldStepCodeSc_mono_bufs (fun _ h => by cases h) (by simp [hhp_in]) hws0

private theorem evaluateHOLFiniteState_seq_assoc_b4d {F : Type} (s : PanSemStateFiniteExact 64 F)
    (p1 p2 p3 : ProgHOL 64) :
    evaluateHOLFiniteState s (.seq p1 (.seq p2 p3)) =
      evaluateHOLFiniteState s (.seq (.seq p1 p2) p3) := by
  simp only [evaluateHOLFiniteState_seq_line780]
  rcases evaluateHOLFiniteState s p1 with ⟨r1, s1⟩
  cases r1 <;> rfl

private theorem progWStepCode_acctCopy_mut_tail_b4d {B : BufList} {gw : List String}
    (hB : PosBufList B) (hgw : SafeStepGlobals gw)
    (hhp_in : "heap_ptr" ∈ gw) (mutProg tailProg : ProgHOL 64)
    (hmut : ∀ {F : Type} (s s1 : PanSemStateFiniteExact 64 F) (bw : BitVec 64),
      WorldEff s s1 [] [] ["heap_ptr"] →
      s1.locals = s.locals.update (ofString "a", .val (.word bw)) →
      s1.locals.lookup (ofString "a") = some (.val (.word bw)) →
      globN s "heap_ptr" ≤ bw.toNat → bw.toNat + 56 ≤ heapLimit →
      (evaluateHOLFiniteState s1 mutProg).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState s1 mutProg).1 →
      WorldEff s (evaluateHOLFiniteState s1 mutProg).2 [] [] ["heap_ptr"])
    (htail : ProgWStepCode B gw tailProg) :
    ProgWStepCode B gw
      (.seq
        (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
          [.var .local (ofString "a")])
        (.seq mutProg tailProg)) := by
  intro F s hc hW hnt hfr
  rw [evaluateHOLFiniteState_seq_assoc_b4d] at hnt hfr ⊢
  exact progWStepCode_seq hB hgw (progWStepCode_acctCopy_mut_b4d hhp_in mutProg hmut) htail s hc hW hnt hfr

private theorem decCall_alloc_const_seq_step_b4d {F : Type}
    (s : PanSemStateFiniteExact 64 F) (x : MlS) (sz : BitVec 64) (pWrite pRest : ProgHOL 64)
    (hc : s.code = originalRuntimeCode)
    (hMB : EvmMsgReadyMsgBounded s)
    (hWrite : ∀ (pw : BitVec 64) (m1 : PanSemStateFiniteExact 64 F),
      m1.locals = s.locals.update (x, .val (.word pw)) →
      WorldEff s m1 [] wsAcctBufs ["heap_ptr"] →
      pw.toNat % 8 = 0 →
      sourceBase ≤ pw.toNat →
      globN s "heap_ptr" ≤ pw.toNat →
      pw.toNat + (sz.toNat + 7) / 8 * 8 = globN m1 "heap_ptr" →
      globN m1 "heap_ptr" ≤ heapLimit →
      WordsOK m1 (pw.toNat, (sz.toNat + 7) / 8 * 8) →
      (evaluateHOLFiniteState m1 pWrite).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState m1 pWrite).1 →
      WorldEff s (evaluateHOLFiniteState m1 pWrite).2 [] wsAcctBufs ["heap_ptr"])
    (hpWrite_loc : ∀ (m1 : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState m1 pWrite).1 = none →
      (evaluateHOLFiniteState m1 pWrite).2.locals = m1.locals)
    (hRest : ∀ (pw : BitVec 64) (m1 m2 : PanSemStateFiniteExact 64 F),
      m1.locals = s.locals.update (x, .val (.word pw)) →
      evaluateHOLFiniteState m1 pWrite = (none, m2) →
      m2.locals = s.locals.update (x, .val (.word pw)) →
      pw.toNat % 8 = 0 →
      sourceBase ≤ pw.toNat →
      globN s "heap_ptr" ≤ pw.toNat →
      pw.toNat + (sz.toNat + 7) / 8 * 8 = globN m1 "heap_ptr" →
      globN m1 "heap_ptr" ≤ heapLimit →
      WordsOK m1 (pw.toNat, (sz.toNat + 7) / 8 * 8) →
      GuestInv m1 →
      WorldEff s m2 [] wsAcctBufs ["heap_ptr"] →
      WorldStepCodeSc [] ["heap_ptr"] s none m2 →
      m2.code = originalRuntimeCode →
      EvmMsgReadyMsgBounded m2 →
      (evaluateHOLFiniteState m2 pRest).1 ≠ some .timeOut →
      FlowingOrResumes (evaluateHOLFiniteState m2 pRest).1 →
      EvmMbStep setCodeGw m2 (evaluateHOLFiniteState m2 pRest).2)
    (hnt : (evaluateHOLFiniteState s (.decCall x .one (ofString "alloc") [.const sz] (.seq pWrite pRest))).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s (.decCall x .one (ofString "alloc") [.const sz] (.seq pWrite pRest))).1) :
    EvmMbStep setCodeGw s
      (evaluateHOLFiniteState s (.decCall x .one (ofString "alloc") [.const sz] (.seq pWrite pRest))).2 := by
  have hW : WorldOK s := worldOK_of_msgBounded hMB
  have hgw_hp : SafeStepGlobals ["heap_ptr"] := by intro g hg; simp at hg; subst hg; simp
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hfr ⊢
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [.const sz] =
      some [.val (.word sz)] := rfl
  simp only [hargs] at hnt hfr ⊢
  rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "alloc") [.val (.word sz)] with
    _ | ⟨body', callee, ret'⟩
  · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [hl] at hnt hfr ⊢
    by_cases hz : s.clock = 0
    · simp [hz] at hnt
    · rw [if_neg hz] at hnt hfr ⊢
      have hlk_alloc_explicit : originalRuntimeCode.lookup (ofString "alloc") =
          some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_alloc, .one) :=
        lookup_alloc_r16
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "alloc") _ _ body'
        _ ret' [.val (.word sz)] callee (by rw [hc]; exact hlk_alloc_explicit) hl
      subst hsame
      have hret_eq := lookupCodeHOLFinite_installed_return s (ofString "alloc") _ _ _
        _ ret' [.val (.word sz)] callee (by rw [hc]; exact hlk_alloc_explicit) hl
      subst hret_eq
      obtain ⟨nw, hnw_eq, hnw_callee⟩ := Fast_C08WkShard03.lookupCode_one_word hlk_alloc_explicit (by rw [← hc]; exact hl)
      injection hnw_eq with hnw_eq'; injection hnw_eq' with hnw_eq'; injection hnw_eq' with hnw_eq'; subst hnw_eq'
      obtain ⟨pw, hpw_lk⟩ : ∃ pw : BitVec 64, s.globals.lookup (ofString "heap_ptr") = some (.val (.word pw)) :=
        globalWord_of_globN_pos s "heap_ptr" (by have := hW.1.2.1; rw [EvmBase.sourceBase_val] at this; omega)
      rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) (sourceFnBody Guest.Software.guestFn_alloc) with ⟨res, pa⟩
      simp only [hrun] at hnt hfr ⊢
      have hcr_outer := contOrRes_of_flowingOrResumes_b4d hfr
      have hres_a : Resumes res := by
        cases res with
        | none => rcases hcr_outer with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
        | some r1 =>
          cases r1 with
          | returned rv => exact Or.inl ⟨rv, rfl⟩
          | exception eid ev =>
            rcases hcr_outer with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨e', v', hc0, hne⟩⟩
            · simp at hc0
            · simp at hc0
            · simp at hc0
            · simp at hc0
            · change some (PanSemResultExact.exception eid ev) = some (PanSemResultExact.exception e' v') at hc0
              injection hc0 with hc0'; injection hc0' with he1 he2; subst he1 he2
              exact Or.inr ⟨eid, ev, rfl, hne⟩
          | timeOut => simp at hnt
          | _ => rcases hcr_outer with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
      have hal := R13.alloc_body_resumes (callEntryStateHOLFinite s callee) pw hc hpw_lk
        (by rw [hrun]; exact hres_a)
      rw [hrun] at hal
      obtain ⟨nw', hnw'_lk, hrv_eq, hcmp1, hcmp2, hpa_eq⟩ := hal
      have hnw_eq2 : sz = nw' := by
        have : (callEntryStateHOLFinite s callee).locals.lookup (ofString "n") = some (.val (.word sz)) := hnw_callee
        rw [this] at hnw'_lk; injection hnw'_lk with h'; injection h' with h'; injection h'
      subst hnw_eq2
      dsimp only at hrv_eq hpa_eq
      subst hrv_eq
      dsimp only at hnt hfr ⊢
      have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word pw))) .one &&
          shapeEqHOL (shapeOfHOLExact (.val (.word pw))) .one) = true := by
        simp [shapeOfHOLExact, shapeEqHOL]
      rw [if_pos hsh] at hnt hfr ⊢
      dsimp only at hnt hfr ⊢
      set m1 := setVarHOLFinite x (.val (.word pw)) { pa with locals := s.locals }
      have hm1_next : m1 = { s with
          globals := s.globals.update (ofString "heap_ptr", .val (.word ((pw + (sz + 7)) &&& ((0 : BitVec 64) - 8)))),
          locals := m1.locals, clock := m1.clock } := by
        dsimp only [m1, setVarHOLFinite]; rw [hpa_eq]; rfl
      have heff_s : WorldEff s s [] wsAcctBufs ["heap_ptr"] :=
        WorldEff.refl s [] wsAcctBufs ["heap_ptr"] hW.1 hc
      obtain ⟨heff_m1, _, hp_al, hp_lo_sb, hp_lo_s, hp_add, hp_hi, hwok⟩ :=
        worldEff_alloc_step heff_s (by decide) hpw_lk hcmp1 hcmp2 hm1_next
      have hm1_loc : m1.locals = s.locals.update (x, .val (.word pw)) := rfl
      rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
      rcases hrw : evaluateHOLFiniteState m1 pWrite with ⟨rw1, m2⟩
      simp only [hrw] at hnt hfr ⊢
      cases rw1 with
      | none =>
        have heff_m2 := hWrite pw m1 hm1_loc heff_m1 hp_al hp_lo_sb hp_lo_s hp_add hp_hi hwok
          (by rw [hrw]; simp) (by rw [hrw]; exact Or.inl rfl)
        rw [hrw] at heff_m2; dsimp only at heff_m2
        have hm2_loc : m2.locals = s.locals.update (x, .val (.word pw)) := by
          have hl2 := hpWrite_loc m1 (by rw [hrw])
          rw [hrw] at hl2; dsimp only at hl2; exact hl2.trans hm1_loc
        have hws12 : WorldStepCodeSc [] ["heap_ptr"] s none m2 :=
          worldEff_to_worldStepCodeSc (B := []) (r := none) hW
            (by decide) validBufList_wsAcctBufs (by decide) heff_m2
        have hs12 : EvmMbStep setCodeGw s m2 :=
          msgBounded_stepCC_of_worldStepCodeSc posBufList_nil hgw_hp
            (by intro g hg; simp at hg; subst hg; simp [setCodeGw]) hMB hws12
        have hs23 := hRest pw m1 m2 hm1_loc hrw hm2_loc hp_al hp_lo_sb hp_lo_s hp_add hp_hi hwok
          heff_m1.arena.1 heff_m2 hws12 heff_m2.code hs12.1 hnt hfr
        exact evmMbStep_with_locals_right _ _ (evmMbStep_trans (by decide) hs12 hs23)
      | some r =>
        have heff_m2 := hWrite pw m1 hm1_loc heff_m1 hp_al hp_lo_sb hp_lo_s hp_add hp_hi hwok
          (by rw [hrw]; exact hnt) (by rw [hrw]; exact contOrRes_of_flowingOrResumes_b4d hfr)
        rw [hrw] at heff_m2; dsimp only at heff_m2
        have hws12 : WorldStepCodeSc [] ["heap_ptr"] s (some r) m2 :=
          worldEff_to_worldStepCodeSc (B := []) (r := some r) hW
            (by decide) validBufList_wsAcctBufs (by decide) heff_m2
        have hs12 : EvmMbStep setCodeGw s m2 :=
          msgBounded_stepCC_of_worldStepCodeSc posBufList_nil hgw_hp
            (by intro g hg; simp at hg; subst hg; simp [setCodeGw]) hMB hws12
        exact evmMbStep_with_locals_right _ _ hs12

private theorem decCall_ro_step_b4d {F : Type}
    (s : PanSemStateFiniteExact 64 F) (x fname : MlS) (sh : ShapeHOL)
    (args : List (ExpHOL 64)) (cont : ProgHOL 64)
    (hro : ReadOnlyFn fname)
    (hc : s.code = originalRuntimeCode)
    (hMB : EvmMsgReadyMsgBounded s)
    (hcont : ∀ (v : ValueHOL 64) (s1 : PanSemStateFiniteExact 64 F),
      s1 = { s with locals := s.locals.update (x, v), clock := s1.clock } →
      s1.code = originalRuntimeCode →
      EvmMsgReadyMsgBounded s1 →
      (evaluateHOLFiniteState s1 cont).1 ≠ some .timeOut →
      FlowingOrResumes (evaluateHOLFiniteState s1 cont).1 →
      EvmMbStep setCodeGw s1 (evaluateHOLFiniteState s1 cont).2)
    (hnt : (evaluateHOLFiniteState s (.decCall x sh fname args cont)).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s (.decCall x sh fname args cont)).1) :
    EvmMbStep setCodeGw s (evaluateHOLFiniteState s (.decCall x sh fname args cont)).2 := by
  obtain ⟨params, body, ret, hlook, hspec⟩ := hro
  have hW : WorldOK s := worldOK_of_msgBounded hMB
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hfr ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · rw [hargs] at hfr; dsimp only at hfr; exact absurd hfr not_flowingOrResumes_error
  · rw [hargs] at hnt hfr; dsimp only at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · rw [if_neg hz] at hnt hfr ⊢
        have hsame := lookupCodeHOLFinite_installed_body s.code.lookup fname params body body'
          ret ret' values callee (by rw [hc]; exact hlook) hl
        subst hsame
        have hret_eq := lookupCodeHOLFinite_installed_return s fname params body' body'
          ret ret' values callee (by rw [hc]; exact hlook) hl
        subst hret_eq
        have hentryEq : callEntryStateHOLFinite s callee =
            { s with locals := callee, clock := (callEntryStateHOLFinite s callee).clock } := by
          cases s; rfl
        have hex : ∃ vs, lookupCodeHOLFinite originalRuntimeCode.lookup fname vs =
            some (body', (callEntryStateHOLFinite s callee).locals, ret') :=
          ⟨values, by simpa only [hc, callEntryStateHOLFinite] using hl⟩
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, cpost⟩
        simp only [hrun] at hnt hfr ⊢
        cases res with
        | none => exact absurd hfr not_flowingOrResumes_error
        | some r1 =>
          cases r1 with
          | returned rv =>
            dsimp only at hnt hfr ⊢
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact rv) sh && shapeEqHOL (shapeOfHOLExact rv) ret') = true
            · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
              have hro_eq := hspec (callEntryStateHOLFinite s callee) hc
                (guestInv_callEntry s callee hW.1.1) hex
                (by rw [hrun]; simp) (by rw [hrun]; exact Or.inl ⟨rv, rfl⟩)
              rw [hrun] at hro_eq; dsimp only at hro_eq
              have hcpost : cpost = { s with locals := cpost.locals, clock := cpost.clock } :=
                R13.state_trans_locals_clock hentryEq hro_eq
              set s1 := setVarHOLFinite x rv { cpost with locals := s.locals }
              have hs1_eq : s1 = { s with locals := s.locals.update (x, rv), clock := s1.clock } := by
                dsimp only [s1, setVarHOLFinite]; rw [hcpost]
              have hs1_code : s1.code = originalRuntimeCode := by rw [hs1_eq]; exact hc
              have hMB1 : EvmMsgReadyMsgBounded s1 := by
                rw [hs1_eq]; exact localsFree_evmMsgReadyMsgBounded s _ _ hMB
              have hstep2 := hcont rv s1 hs1_eq hs1_code hMB1 hnt hfr
              have hstep2_from_s : EvmMbStep setCodeGw s (evaluateHOLFiniteState s1 cont).2 := by
                have hkey : ∀ post : PanSemStateFiniteExact 64 F, EvmMbStep setCodeGw s1 post →
                    EvmMbStep setCodeGw s post := by
                  intro post h2
                  rw [hs1_eq] at h2
                  exact evmMbStep_of_pre_locals_clock h2
                exact hkey _ hstep2
              exact evmMbStep_with_locals_right _ _ hstep2_from_s
            · simp [hsh] at hfr; exact absurd hfr not_flowingOrResumes_error
          | exception eid ev =>
            have hres_e : Resumes (some (.exception eid ev)) := by
              rcases hfr with h | h | h | hr <;> try simp at h
              exact hr
            have hro_eq := hspec (callEntryStateHOLFinite s callee) hc
              (guestInv_callEntry s callee hW.1.1) hex
              (by rw [hrun]; simp) (by rw [hrun]; exact hres_e)
            rw [hrun] at hro_eq; dsimp only at hro_eq
            have hcpost : cpost = { s with locals := cpost.locals, clock := cpost.clock } :=
              R13.state_trans_locals_clock hentryEq hro_eq
            have hrefl := evmMbStep_refl (gw := setCodeGw) hMB
            have hstep_cpost : EvmMbStep setCodeGw s cpost := by
              rw [hcpost]; exact evmMbStep_with_locals_right _ _ hrefl
            exact evmMbStep_with_locals_right _ _ hstep_cpost
          | timeOut => simp at hnt
          | error | «break» | «continue» =>
            dsimp only at hfr; exact absurd hfr not_flowingOrResumes_error
          | finalFfi _ =>
            dsimp only at hfr; exact absurd hfr not_flowingOrResumes_finalFfi

private theorem worldStepCodeSc_acctCopy_mut_at_b4d {B : BufList} {gw : List String} {F : Type}
    {s : PanSemStateFiniteExact 64 F}
    (hhp_in : "heap_ptr" ∈ gw) (mutProg : ProgHOL 64)
    (hc : s.code = originalRuntimeCode) (hW : WorldOK s)
    (hmut : ∀ (s1 : PanSemStateFiniteExact 64 F) (bw : BitVec 64),
      WorldEff s s1 [] [] ["heap_ptr"] →
      s1.locals = s.locals.update (ofString "a", .val (.word bw)) →
      s1.locals.lookup (ofString "a") = some (.val (.word bw)) →
      globN s "heap_ptr" ≤ bw.toNat → bw.toNat + 56 ≤ heapLimit →
      (evaluateHOLFiniteState s1 mutProg).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState s1 mutProg).1 →
      WorldEff s (evaluateHOLFiniteState s1 mutProg).2 [] [] ["heap_ptr"])
    (hnt : (evaluateHOLFiniteState s
        (.seq
          (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
            [.var .local (ofString "a")])
          mutProg)).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s
        (.seq
          (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
            [.var .local (ofString "a")])
          mutProg)).1) :
    WorldStepCodeSc B gw s
      (evaluateHOLFiniteState s
        (.seq
          (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
            [.var .local (ofString "a")])
          mutProg)).1
      (evaluateHOLFiniteState s
        (.seq
          (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
            [.var .local (ofString "a")])
          mutProg)).2 := by
  rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
  rcases h1 : evaluateHOLFiniteState s
      (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
        [.var .local (ofString "a")]) with ⟨r1, s1⟩
  simp only [h1] at hnt hfr ⊢
  cases r1 with
  | some cr1 =>
    have hac := acct_copy_step_code s hc hW.1 (by rw [h1]; exact hnt) (by rw [h1]; exact hfr)
    rw [h1] at hac
    have hws0 : WorldStepCodeSc [] ["heap_ptr"] s (some cr1) s1 :=
      worldEff_to_worldStepCodeSc (B := []) (r := some cr1) hW
        (by decide) (by intro _ hp; cases hp) (by decide) hac.1
    exact worldStepCodeSc_mono_bufs (fun _ h => by cases h) (by simp [hhp_in]) hws0
  | none =>
    dsimp only at hnt hfr ⊢
    have hac := acct_copy_step_code s hc hW.1 (by rw [h1]; simp) (by rw [h1]; exact Or.inl rfl)
    rw [h1] at hac; dsimp only at hac
    obtain ⟨bw, hs1_loc, hbw_lo, hbw_hi⟩ := hac.2 rfl
    have hs1_a : s1.locals.lookup (ofString "a") = some (.val (.word bw)) := by
      rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hcr := contOrRes_of_flowingOrResumes_b4d hfr
    have heff2 := hmut s1 bw hac.1 hs1_loc hs1_a hbw_lo hbw_hi hnt hcr
    have hws0 : WorldStepCodeSc [] ["heap_ptr"] s
        (evaluateHOLFiniteState s1 mutProg).1 (evaluateHOLFiniteState s1 mutProg).2 :=
      worldEff_to_worldStepCodeSc (B := []) (r := (evaluateHOLFiniteState s1 mutProg).1) hW
        (by decide) (by intro _ hp; cases hp) (by decide) heff2
    exact worldStepCodeSc_mono_bufs (fun _ h => by cases h) (by simp [hhp_in]) hws0

private theorem worldStepCodeSc_acctCopy_mut_tail_at_b4d {B : BufList} {gw : List String} {F : Type}
    {s : PanSemStateFiniteExact 64 F}
    (hB : PosBufList B) (hgw : SafeStepGlobals gw)
    (hhp_in : "heap_ptr" ∈ gw) (mutProg tailProg : ProgHOL 64)
    (hc : s.code = originalRuntimeCode) (hW : WorldOK s)
    (hmut : ∀ (s1 : PanSemStateFiniteExact 64 F) (bw : BitVec 64),
      WorldEff s s1 [] [] ["heap_ptr"] →
      s1.locals = s.locals.update (ofString "a", .val (.word bw)) →
      s1.locals.lookup (ofString "a") = some (.val (.word bw)) →
      globN s "heap_ptr" ≤ bw.toNat → bw.toNat + 56 ≤ heapLimit →
      (evaluateHOLFiniteState s1 mutProg).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState s1 mutProg).1 →
      WorldEff s (evaluateHOLFiniteState s1 mutProg).2 [] [] ["heap_ptr"])
    (htail : ProgWStepCode B gw tailProg)
    (hnt : (evaluateHOLFiniteState s
        (.seq
          (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
            [.var .local (ofString "a")])
          (.seq mutProg tailProg))).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s
        (.seq
          (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
            [.var .local (ofString "a")])
          (.seq mutProg tailProg))).1) :
    WorldStepCodeSc B gw s
      (evaluateHOLFiniteState s
        (.seq
          (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
            [.var .local (ofString "a")])
          (.seq mutProg tailProg))).1
      (evaluateHOLFiniteState s
        (.seq
          (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
            [.var .local (ofString "a")])
          (.seq mutProg tailProg))).2 := by
  rw [evaluateHOLFiniteState_seq_assoc_b4d] at hnt hfr ⊢
  let p1 : ProgHOL 64 :=
    .seq (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
      [.var .local (ofString "a")]) mutProg
  have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata s p1).1
  dsimp only [p1] at hmeta
  rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
  rcases h1 : evaluateHOLFiniteState s p1 with ⟨r1, m⟩
  dsimp only [p1] at h1
  simp only [h1] at hmeta hnt hfr ⊢
  cases r1 with
  | some cr1 =>
    have hs1 := worldStepCodeSc_acctCopy_mut_at_b4d (B := B) (gw := gw) hhp_in mutProg hc hW hmut
      (by rw [h1]; exact hnt) (by rw [h1]; exact hfr)
    simpa [h1] using hs1
  | none =>
    have hs1 := worldStepCodeSc_acctCopy_mut_at_b4d (B := B) (gw := gw) hhp_in mutProg hc hW hmut
      (by rw [h1]; simp) (by rw [h1]; exact Or.inl rfl)
    simp only [h1] at hs1
    have hWm : WorldOK m := hs1.worldOK_bufs hB.1 hW
    have hs2 := htail m (hmeta.trans hc) hWm hnt hfr
    exact worldStepCodeSc_trans hB hgw hs1 hs2

private theorem evmMbStep_decCall_get_account_b4d {F : Type}
    (s : PanSemStateFiniteExact 64 F) (x : MlS) (sh : ShapeHOL)
    (args : List (ExpHOL 64)) (cont : ProgHOL 64)
    (hc : s.code = originalRuntimeCode)
    (hMB : EvmMsgReadyMsgBounded s)
    (hcont : ∀ (v : ValueHOL 64) (s1 : PanSemStateFiniteExact 64 F),
      shapeEqHOL (shapeOfHOLExact v) sh = true →
      s1.locals = s.locals.update (x, v) →
      s1.code = originalRuntimeCode →
      EvmMsgReadyMsgBounded s1 →
      (evaluateHOLFiniteState s1 cont).1 ≠ some .timeOut →
      FlowingOrResumes (evaluateHOLFiniteState s1 cont).1 →
      EvmMbStep setCodeGw s1 (evaluateHOLFiniteState s1 cont).2)
    (hnt : (evaluateHOLFiniteState s (.decCall x sh (ofString "get_account") args cont)).1 ≠
      some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s (.decCall x sh (ofString "get_account") args cont)).1) :
    EvmMbStep setCodeGw s
      (evaluateHOLFiniteState s (.decCall x sh (ofString "get_account") args cont)).2 := by
  obtain ⟨params, body, ret, hlook, hspec⟩ := wkCodeSc_get_account
  have hW : WorldOK s := worldOK_of_msgBounded hMB
  have hB_ga : ∀ p ∈ wsAcctBufs, p ∈ acctMutBufs := by
    intro p hp; simp [wsAcctBufs] at hp; rcases hp with rfl | rfl | rfl <;> simp [acctMutBufs]
  have hgw_ga : ∀ g ∈ (["heap_ptr", "scratch_ptr"] : List String), g ∈ setCodeGw := by
    intro g hg; simp at hg; rcases hg with rfl | rfl <;> decide
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hfr ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with
    _ | values
  · rw [hargs] at hfr; dsimp only at hfr; exact absurd hfr not_flowingOrResumes_error
  · rw [hargs] at hnt hfr; dsimp only at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "get_account") values with
      _ | ⟨body', callee, ret'⟩
    · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · rw [if_neg hz] at hnt hfr ⊢
        have hsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "get_account")
          params body body' ret ret' values callee (by rw [hc]; exact hlook) hl
        subst hsame
        have hret_eq := lookupCodeHOLFinite_installed_return s (ofString "get_account")
          params body' body' ret ret' values callee (by rw [hc]; exact hlook) hl
        subst hret_eq
        have hex : ∃ vs, lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "get_account") vs =
            some (body', (callEntryStateHOLFinite s callee).locals, ret') :=
          ⟨values, by simpa only [hc, callEntryStateHOLFinite] using hl⟩
        have hWent : WorldOK (callEntryStateHOLFinite s callee) :=
          localsFree_worldOK s callee (s.clock - 1) hW
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body').1
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, cpost⟩
        simp only [hrun] at hmeta hnt hfr ⊢
        have hnt_c : (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body').1 ≠
            some .timeOut := by
          simp only [hrun]; rintro rfl; simp at hnt
        cases res with
        | none => exact absurd hfr not_flowingOrResumes_error
        | some r1 =>
          cases r1 with
          | returned rv =>
            dsimp only at hnt hfr ⊢
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact rv) sh && shapeEqHOL (shapeOfHOLExact rv) ret') = true
            · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
              have hws0 := hspec (callEntryStateHOLFinite s callee) hc hWent hex hnt_c
                (by rw [hrun]; exact Or.inl ⟨rv, rfl⟩)
              rw [hrun] at hws0; dsimp only at hws0
              have hws_s : WorldStepCodeSc acctMutBufs setCodeGw (callEntryStateHOLFinite s callee)
                  (some (.returned rv)) cpost := worldStepCodeSc_mono_bufs hB_ga hgw_ga hws0
              set s1 := setVarHOLFinite x rv { cpost with locals := s.locals }
              have hs1_ws : WorldStepCodeSc acctMutBufs setCodeGw s none
                  { cpost with locals := s.locals.update (x, rv) } :=
                worldStepCodeSc_from_entry (r' := none) (callee := callee)
                  (L := s.locals.update (x, rv)) (k := cpost.clock) hws_s
              obtain ⟨hs1_mb, hs1_cc, hs1_112⟩ := msgBounded_stepCC_of_worldStepCodeSc
                posBufList_acctMutBufs safeStepGlobals_setCode (fun g hg => hg) hMB hs1_ws
              have hs1_code : s1.code = originalRuntimeCode := hmeta.trans hc
              have hsh1 : shapeEqHOL (shapeOfHOLExact rv) sh = true := (Bool.and_eq_true _ _).mp hsh |>.1
              have hstep2 := hcont rv s1 hsh1 rfl hs1_code hs1_mb hnt hfr
              exact evmMbStep_with_locals_right _ _
                (evmMbStep_trans (by decide) ⟨hs1_mb, hs1_cc, hs1_112⟩ hstep2)
            · simp [hsh] at hfr; exact absurd hfr not_flowingOrResumes_error
          | exception eid ev =>
            dsimp only at hfr ⊢
            have hres_e : Resumes (some (.exception eid ev)) := by
              rcases hfr with h | h | h | hr <;> try simp at h
              exact hr
            have hws0 := hspec (callEntryStateHOLFinite s callee) hc hWent hex hnt_c
              (by rw [hrun]; exact hres_e)
            rw [hrun] at hws0; dsimp only at hws0
            have hws_s : WorldStepCodeSc acctMutBufs setCodeGw (callEntryStateHOLFinite s callee)
                (some (.exception eid ev)) cpost := worldStepCodeSc_mono_bufs hB_ga hgw_ga hws0
            obtain ⟨hmb_e, hcc_e, h112_e⟩ := msgBounded_stepCC_of_worldStepCodeSc
              posBufList_acctMutBufs safeStepGlobals_setCode (fun g hg => hg) hMB
              (worldStepCodeSc_from_entry (r' := none) hws_s)
            exact ⟨hmb_e, hcc_e, h112_e⟩
          | timeOut => simp at hnt
          | error | «break» | «continue» =>
            dsimp only at hfr; exact absurd hfr not_flowingOrResumes_error
          | finalFfi _ =>
            dsimp only at hfr; exact absurd hfr not_flowingOrResumes_finalFfi

/-- Body step for `set_code(addr, code, code_len)` when `code_len < 2^40`. -/
theorem set_code_bounded_body_step {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (waddr wcode wcl : BitVec 64)
    (hc0 : s0.code = originalRuntimeCode)
    (hMB0 : EvmMsgReadyMsgBounded s0)
    (hwaddr_s0 : s0.locals.lookup (ofString "addr") = some (.val (.word waddr)))
    (hwcode_s0 : s0.locals.lookup (ofString "code") = some (.val (.word wcode)))
    (hwcl_s0 : s0.locals.lookup (ofString "code_len") = some (.val (.word wcl)))
    (hwcl_lt : wcl.toNat < 2 ^ 40)
    (hnt0 : (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_set_code)).1 ≠ some .timeOut)
    (hres0 : Resumes (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_set_code)).1) :
    EvmMsgReadyMsgBounded (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_set_code)).2 ∧
    EvmStepCC setCodeGw s0 (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_set_code)).2 ∧
    memW (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_set_code)).2 (globN s0 "ev" + 112) =
      memW s0 (globN s0 "ev" + 112) := by
  have hB := posBufList_acctMutBufs
  have hgw := safeStepGlobals_setCode
  have hhl_264 : heapLimit < 2 ^ 64 := by decide
  have hfr0 : FlowingOrResumes (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_set_code)).1 :=
    Or.inr (Or.inr (Or.inr hres0))
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_set_code,
    FrontendCodecComputation.declToHOLStructural, FrontendCodecComputation.funDeclToHOLStructural,
    FrontendCodecComputation.progToHOLStructural, FrontendCodecComputation.expToHOLStructural,
    FrontendCodecComputation.expListToHOLStructural, FrontendCodecComputation.shapeToHOLStructural,
    FrontendCodecComputation.shapeListToHOLStructural,
    Option.map, List.map] at hnt0 hfr0 ⊢
  exact decCall_alloc_const_seq_step_b4d s0 (ofString "h") 32#64 _ _ hc0 hMB0
    (fun wh m1 hm1_loc heff_m1 _ _ hwh_lo hwh_end _ _ hnt_k hcr_k => by
      have hwh_hi : wh.toNat + 32 ≤ heapLimit := by
        change wh.toNat + (32 + 7) / 8 * 8 = globN m1 "heap_ptr" at hwh_end; omega
      have hm1_h : m1.locals.lookup (ofString "h") = some (.val (.word wh)) := by
        rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
      have hm1_code : m1.locals.lookup (ofString "code") = some (.val (.word wcode)) := by
        rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hwcode_s0,
          show ofString "h" ≠ ofString "code" by decide]
      have hm1_cl : m1.locals.lookup (ofString "code_len") = some (.val (.word wcl)) := by
        rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hwcl_s0,
          show ofString "h" ≠ ofString "code_len" by decide]
      have hkpad_m1 : Fast_C08WkShard03.globMapN m1.globals "keccak_pad" = globN s0 "keccak_pad" :=
        globN_eq_of_lookup (heff_m1.gw_kept (ofString "keccak_pad") (by decide))
      have hkst_m1 : Fast_C08WkShard03.globMapN m1.globals "keccak_st" = globN s0 "keccak_st" :=
        globN_eq_of_lookup (heff_m1.gw_kept (ofString "keccak_st") (by decide))
      exact worldEff_call0_funByteEff_b4d heff_m1 Fast_C08WkShard03.funByteEff_keccak256 _
        [bufferRegion s0 ("keccak_st", 200), bufferRegion s0 ("keccak_pad", 136), (wh.toNat, 32)]
        (fun vals hargs i hi _ => by
          rw [evalListHOLFinite_eq_toExact] at hargs
          simp only [evalListHOLExact, evalHOLExact, hm1_code, hm1_cl, hm1_h] at hargs
          injection hargs with hargs_eq; subst hargs_eq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl | rfl
          · refine ⟨bufferRegion s0 ("keccak_st", 200), List.mem_cons_self, ?_, ?_⟩ <;>
              simp [Fast_C08WkShard03.globBufIvl, bufferRegion, hkst_m1]
          · refine ⟨bufferRegion s0 ("keccak_pad", 136), List.mem_cons_of_mem _ List.mem_cons_self, ?_, ?_⟩ <;>
              simp [Fast_C08WkShard03.globBufIvl, bufferRegion, hkpad_m1]
          · refine ⟨(wh.toNat, 32), List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), ?_, ?_⟩ <;>
              simp [Fast_C08WkShard03.valWordNat])
        (fun iv hiv _ => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hiv
          rcases hiv with rfl | rfl | rfl
          · exact Or.inr (Or.inl ⟨("keccak_st", 200), by decide, le_rfl, le_rfl⟩)
          · exact Or.inr (Or.inl ⟨("keccak_pad", 136), by decide, le_rfl, le_rfl⟩)
          · exact Or.inr (Or.inr (Or.inr ⟨hwh_lo, hwh_hi⟩)))
        hnt_k hcr_k)
    (fun m1 hnone => call0_none_locals_b4d m1 (ofString "keccak256") _ hnone)
    (fun wh _ m2 _ _ hm2_loc _ _ _ _ _ _ _ _ _ hc2 hMB2 hnt2 hfr2 => by
      have hm2_h : m2.locals.lookup (ofString "h") = some (.val (.word wh)) := by
        rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
      have hm2_code : m2.locals.lookup (ofString "code") = some (.val (.word wcode)) := by
        rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hwcode_s0,
          show ofString "h" ≠ ofString "code" by decide]
      have hm2_cl : m2.locals.lookup (ofString "code_len") = some (.val (.word wcl)) := by
        rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hwcl_s0,
          show ofString "h" ≠ ofString "code_len" by decide]
      exact decCall_ro_step_b4d m2 (ofString "eq") (ofString "memeq") .one _ _
        EvmFrameSpecs.ro_memeq hc2 hMB2
        (fun veq m3 hm3_eq hc3 hMB3 hnt3 hfr3 => by
          have hm3_loc : m3.locals = m2.locals.update (ofString "eq", veq) := by rw [hm3_eq]
          have hm3_h : m3.locals.lookup (ofString "h") = some (.val (.word wh)) := by
            rw [hm3_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm2_h,
              show ofString "eq" ≠ ofString "h" by decide]
          have hm3_code : m3.locals.lookup (ofString "code") = some (.val (.word wcode)) := by
            rw [hm3_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm2_code,
              show ofString "eq" ≠ ofString "code" by decide]
          have hm3_cl : m3.locals.lookup (ofString "code_len") = some (.val (.word wcl)) := by
            rw [hm3_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm2_cl,
              show ofString "eq" ≠ ofString "code_len" by decide]
          let pIte : ProgHOL 64 :=
            .ite (.cmp .equal (.var .local (ofString "eq")) (.const 0#64))
              (.decCall (ofString "sl") .one (ofString "alloc") [.const 16#64]
                (.seq (.store (.var .local (ofString "sl")) (.var .local (ofString "code")))
                  (.seq (.store (.op .add [.var .local (ofString "sl"), .const 8#64]) (.var .local (ofString "code_len")))
                    (.call (some (none, none)) (ofString "jset")
                      [.load .one (.op .add [.var .global (ofString "ts"), .const 48#64]),
                       .var .local (ofString "h"), .var .local (ofString "sl")]))))
              .skip
          have hIte_step : ∀ (hnt_i : (evaluateHOLFiniteState m3 pIte).1 ≠ some .timeOut)
              (hfr_i : FlowingOrResumes (evaluateHOLFiniteState m3 pIte).1),
              EvmMbStep setCodeGw m3 (evaluateHOLFiniteState m3 pIte).2 := by
            intro hnt_i hfr_i
            dsimp only [pIte] at hnt_i hfr_i ⊢
            rw [evaluateHOLFiniteState_ite] at hnt_i hfr_i ⊢
            rcases hev_c : @evalHOLExact 64 F _ m3.toExact (fun a => Classical.propDecidable (m3.memaddrs a))
                (.cmp .equal (.var .local (ofString "eq")) (.const 0#64)) with _ | cv
            · simp [hev_c] at hfr_i; exact absurd hfr_i not_flowingOrResumes_error
            · rcases cv with ⟨⟨cw⟩⟩ | _ | _
              · simp only [hev_c] at hnt_i hfr_i ⊢
                by_cases hcw : cw = 0
                · simp only [hcw, ↓reduceIte] at hnt_i hfr_i ⊢
                  rw [evaluateHOLFiniteState_skip]
                  exact evmMbStep_refl hMB3
                · simp only [hcw, ↓reduceIte] at hnt_i hfr_i ⊢
                  have hassoc_br : ∀ (st : PanSemStateFiniteExact 64 F),
                      evaluateHOLFiniteState st
                        (.seq (.store (.var .local (ofString "sl")) (.var .local (ofString "code")))
                          (.seq (.store (.op .add [.var .local (ofString "sl"), .const 8#64]) (.var .local (ofString "code_len")))
                            (.call (some (none, none)) (ofString "jset")
                              [.load .one (.op .add [.var .global (ofString "ts"), .const 48#64]),
                               .var .local (ofString "h"), .var .local (ofString "sl")]))) =
                      evaluateHOLFiniteState st
                        (.seq
                          (.seq (.store (.var .local (ofString "sl")) (.var .local (ofString "code")))
                            (.store (.op .add [.var .local (ofString "sl"), .const 8#64]) (.var .local (ofString "code_len"))))
                          (.call (some (none, none)) (ofString "jset")
                            [.load .one (.op .add [.var .global (ofString "ts"), .const 48#64]),
                             .var .local (ofString "h"), .var .local (ofString "sl")])) := by
                    intro st; simp only [evaluateHOLFiniteState_seq_line780]
                    rcases evaluateHOLFiniteState st _ with ⟨r1, _⟩; cases r1 <;> rfl
                  have hdec_assoc :
                      evaluateHOLFiniteState m3
                        (.decCall (ofString "sl") .one (ofString "alloc") [.const 16#64]
                          (.seq (.store (.var .local (ofString "sl")) (.var .local (ofString "code")))
                            (.seq (.store (.op .add [.var .local (ofString "sl"), .const 8#64]) (.var .local (ofString "code_len")))
                              (.call (some (none, none)) (ofString "jset")
                                [.load .one (.op .add [.var .global (ofString "ts"), .const 48#64]),
                                 .var .local (ofString "h"), .var .local (ofString "sl")])))) =
                      evaluateHOLFiniteState m3
                        (.decCall (ofString "sl") .one (ofString "alloc") [.const 16#64]
                          (.seq
                            (.seq (.store (.var .local (ofString "sl")) (.var .local (ofString "code")))
                              (.store (.op .add [.var .local (ofString "sl"), .const 8#64]) (.var .local (ofString "code_len"))))
                            (.call (some (none, none)) (ofString "jset")
                              [.load .one (.op .add [.var .global (ofString "ts"), .const 48#64]),
                               .var .local (ofString "h"), .var .local (ofString "sl")]))) := by
                    simp only [evaluateHOLFiniteState_decCall_fixClockRewrite]
                    rcases evalListHOLFinite m3 (h := fun a => Classical.propDecidable (m3.memaddrs a)) [.const 16#64] with _ | vs_a; · rfl
                    dsimp only
                    rcases lookupCodeHOLFinite m3.code.lookup (ofString "alloc") vs_a with _ | ⟨ba, ca, ra⟩; · rfl
                    dsimp only
                    split; · rfl
                    rcases evaluateHOLFiniteState (callEntryStateHOLFinite m3 ca) ba with ⟨ra0, pa0⟩
                    cases ra0 with
                    | none => rfl
                    | some cra =>
                      cases cra with
                      | returned rva =>
                        dsimp only
                        by_cases hsh_a : (shapeEqHOL (shapeOfHOLExact rva) .one && shapeEqHOL (shapeOfHOLExact rva) ra) = true
                        · rw [if_pos hsh_a, if_pos hsh_a, hassoc_br]
                        · rw [if_neg hsh_a, if_neg hsh_a]
                      | _ => rfl
                  rw [hdec_assoc] at hnt_i hfr_i ⊢
                  exact decCall_alloc_const_seq_step_b4d m3 (ofString "sl") 16#64 _ _ hc3 hMB3
                    (fun wsl ms1 hms1_loc heff_ms1 _ _ hwsl_lo hwsl_end _ _ hnt_st hcr_st => by
                      have hwsl_hi : wsl.toNat + 16 ≤ heapLimit := by
                        change wsl.toNat + (16 + 7) / 8 * 8 = globN ms1 "heap_ptr" at hwsl_end; omega
                      have hms1_sl : ms1.locals.lookup (ofString "sl") = some (.val (.word wsl)) := by
                        rw [hms1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
                      have hms1_code : ms1.locals.lookup (ofString "code") = some (.val (.word wcode)) := by
                        rw [hms1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm3_code,
                          show ofString "sl" ≠ ofString "code" by decide]
                      have hms1_cl : ms1.locals.lookup (ofString "code_len") = some (.val (.word wcl)) := by
                        rw [hms1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm3_cl,
                          show ofString "sl" ≠ ofString "code_len" by decide]
                      refine R16Shards.worldEff_seq hnt_st hcr_st
                        (fun _ _ => R16Shards.worldEff_store_word heff_ms1 _ _
                          (fun v hv => by simp [evalHOLExact, hms1_code] at hv; exact ⟨wcode, hv.symm⟩)
                          (fun x hx _ => by
                            simp [evalHOLExact, hms1_sl] at hx; subst hx
                            exact Or.inr (Or.inr (Or.inr ⟨hwsl_lo, by omega⟩))))
                        (fun ms2 hms2 heff_ms2 _ _ => ?_)
                      have hms2_loc : ms2.locals = ms1.locals := by
                        have hk := fun k => evaluate_avoidsLocal_flowing k
                          (.store (.var .local (ofString "sl")) (.var .local (ofString "code")))
                          rfl ms1 (by rw [hms2]; exact Or.inl rfl)
                        apply HolFiniteMapExact.ext; funext k; simpa [hms2] using hk k
                      exact R16Shards.worldEff_store_word heff_ms2 _ _
                        (fun v hv => by simp [evalHOLExact, hms2_loc, hms1_cl] at hv; exact ⟨wcl, hv.symm⟩)
                        (fun x hx _ => by
                          simp [evalHOLExact, evalListHOLExact, hms2_loc, hms1_sl, panOpHOL, wordOpHOL, wordOp,
                            valueIsWord, valueWord] at hx
                          subst hx
                          have hx8 : (wsl + 8#64).toNat = wsl.toNat + 8 := by
                            apply BitVec.toNat_add_of_lt; change wsl.toNat + 8 < 2 ^ 64; omega
                          exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))
                    (fun ms1 hnone_st => by
                      apply HolFiniteMapExact.ext; funext k
                      exact evaluate_avoidsLocal_flowing k _ rfl ms1 (Or.inl hnone_st))
                    (fun wsl ms1 ms3 hms1_loc hst_run hms3_loc _ hwsl_sb hwsl_lo hwsl_end hwsl_hl hwsl_wok
                        hG_ms1 heff_ms3 hws_ms3 hcms3 _ hnt_j hfr_j => by
                      have hwsl_hi : wsl.toNat + 16 ≤ heapLimit := by
                        change wsl.toNat + (16 + 7) / 8 * 8 = globN ms1 "heap_ptr" at hwsl_end; omega
                      have hms1_sl : ms1.locals.lookup (ofString "sl") = some (.val (.word wsl)) := by
                        rw [hms1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
                      have hms1_cl : ms1.locals.lookup (ofString "code_len") = some (.val (.word wcl)) := by
                        rw [hms1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm3_cl,
                          show ofString "sl" ≠ ofString "code_len" by decide]
                      have hst_inv : ∃ ms2 : PanSemStateFiniteExact 64 F,
                          evaluateHOLFiniteState ms1 (.store (.var .local (ofString "sl")) (.var .local (ofString "code"))) = (none, ms2) ∧
                          evaluateHOLFiniteState ms2 (.store (.op .add [.var .local (ofString "sl"), .const 8#64]) (.var .local (ofString "code_len"))) = (none, ms3) := by
                        rw [evaluateHOLFiniteState_seq_line780] at hst_run
                        rcases hs1 : evaluateHOLFiniteState ms1 (.store (.var .local (ofString "sl")) (.var .local (ofString "code"))) with ⟨r1, ms2⟩
                        rw [hs1] at hst_run
                        cases r1 with
                        | none => exact ⟨ms2, rfl, hst_run⟩
                        | some c1 => simp at hst_run
                      obtain ⟨ms2, hst1, hst2⟩ := hst_inv
                      have hms2_g : ms2.globals = ms1.globals := by
                        rw [evaluateHOLFiniteState_store] at hst1
                        revert hst1
                        rcases @evalHOLExact 64 F _ ms1.toExact (fun a => Classical.propDecidable (ms1.memaddrs a))
                            (.var .local (ofString "sl")) with _ | dv
                        · simp
                        · rcases dv with ⟨⟨dx⟩⟩ | _ | _ <;> try simp
                          rcases @evalHOLExact 64 F _ ms1.toExact (fun a => Classical.propDecidable (ms1.memaddrs a))
                              (.var .local (ofString "code")) with _ | vv
                          · simp
                          · dsimp only
                            split
                            · intro h; injection h with _ h2; rw [← h2]
                            · simp
                      have hms3_g : ms3.globals = ms2.globals := by
                        rw [evaluateHOLFiniteState_store] at hst2
                        revert hst2
                        rcases @evalHOLExact 64 F _ ms2.toExact (fun a => Classical.propDecidable (ms2.memaddrs a))
                            (.op .add [.var .local (ofString "sl"), .const 8#64]) with _ | dv
                        · simp
                        · rcases dv with ⟨⟨dx⟩⟩ | _ | _ <;> try simp
                          rcases @evalHOLExact 64 F _ ms2.toExact (fun a => Classical.propDecidable (ms2.memaddrs a))
                              (.var .local (ofString "code_len")) with _ | vv
                          · simp
                          · dsimp only
                            split
                            · intro h; injection h with _ h2; rw [← h2]
                            · simp
                      have hms2_loc : ms2.locals = ms1.locals := by
                        have hk := fun k => evaluate_avoidsLocal_flowing k
                          (.store (.var .local (ofString "sl")) (.var .local (ofString "code")))
                          rfl ms1 (by rw [hst1]; exact Or.inl rfl)
                        apply HolFiniteMapExact.ext; funext k; simpa [hst1] using hk k
                      have hhp_ms3 : globN ms3 "heap_ptr" = globN ms1 "heap_ptr" := by
                        unfold globN; rw [hms3_g, hms2_g]
                      have hwsl_in_ms3 : Inside (wsl.toNat, 16) sourceBase (globN ms3 "heap_ptr") := by
                        rw [hhp_ms3]
                        change sourceBase ≤ wsl.toNat ∧ wsl.toNat + 16 ≤ globN ms1 "heap_ptr"
                        change wsl.toNat + (16 + 7) / 8 * 8 = globN ms1 "heap_ptr" at hwsl_end
                        exact ⟨hwsl_sb, by omega⟩
                      have hwsl_words_ms3 : WordsOK ms3 (wsl.toNat, 16) := by
                        change WordsOK ms1 (wsl.toNat, 16) at hwsl_wok
                        exact wordsOK_transfer_b4d hG_ms1
                          heff_ms3.arena.1 hwsl_wok
                      have hdst8 : @evalHOLExact 64 F _ ms2.toExact (fun a => Classical.propDecidable (ms2.memaddrs a))
                          (.op .add [.var .local (ofString "sl"), .const 8#64]) = some (.val (.word (wsl + 8#64))) := by
                        simp [evalHOLExact, evalListHOLExact, toExact, hms2_loc, hms1_sl,
                          panOpHOL, wordOpHOL, wordOp, valueIsWord, valueWord]
                      have hval8 : @evalHOLExact 64 F _ ms2.toExact (fun a => Classical.propDecidable (ms2.memaddrs a))
                          (.var .local (ofString "code_len")) = some (.val (.word wcl)) := by
                        simp [evalHOLExact, toExact, hms2_loc, hms1_cl]
                      have hwsl8_eq : (wsl + 8#64).toNat = wsl.toNat + 8 := by
                        apply BitVec.toNat_add_of_lt; change wsl.toNat + 8 < 2 ^ 64; omega
                      have hwsl_len_ms3 : memW ms3 (wsl.toNat + 8) < 2 ^ 40 := by
                        have hm_eq := memW_store_word_exact_b4d hdst8 hval8 hst2
                        rw [hwsl8_eq] at hm_eq
                        rw [hm_eq]; exact hwcl_lt
                      obtain ⟨hA_m3, hM_m3, S3, hInvAt_m3, hMO_m3, hC_m3⟩ := hMB3
                      have hB_nil : PosBufList [] := posBufList_nil
                      have hgw_hp : SafeStepGlobals ["heap_ptr"] := by
                        intro g hg; simp at hg; subst hg; simp
                      obtain ⟨Sw3, Frem3, Sw3', _, _, hA_ms3, hperm_S3, hSw3_sub, _, _, _, _, _, _, _, _,
                        hInvAt_ms3', hMO_ms3', _, h112_ms3_m3, _⟩ :=
                        evmStepCC_full_of_worldStepSc hB_nil.1 hgw_hp (fun _ hg => hg)
                          hA_m3 hInvAt_m3 hMO_m3 hws_ms3.1
                      obtain ⟨hT_m3, hJ_m3, hF_m3, ⟨Nd_m3, hTr_m3⟩⟩ := hInvAt_m3.1
                      have hWT_m3 : WorldTypedWith m3 S3 Nd_m3 := ⟨hT_m3, hJ_m3, hF_m3, hTr_m3⟩
                      obtain ⟨⟨Nd_nt3, hWT_S3_ms3⟩, hgrow_nt3, hfr_nt3⟩ :=
                        hws_ms3.2 S3 Nd_m3 hWT_m3 (validBufList_disj hB_nil.1 hWT_m3)
                      obtain ⟨_, _, _, _, _, _, hv3⟩ :=
                        hws_ms3.1.1.2.2.2.2 S3 Nd_m3 hWT_m3 (validBufList_disj hB_nil.1 hWT_m3)
                      have hroots3 := code_roots_kept_of_safeGlobals hWT_m3 hB_nil hgw_hp hws_ms3.1.1.2.2.2.1 hws_ms3.1.1.2.2.1
                      have hglob_wbt3 : ∀ g ∈ (["ws", "bs", "ts"] : List String), globN ms3 g = globN m3 g := by
                        intro g hg
                        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
                        rcases hg with rfl | rfl | rfl
                        · exact (hroots3 "ws" 16 (by decide)).1
                        · exact (hroots3 "bs" 48 (by decide)).1
                        · exact (hroots3 "ts" 48 (by decide)).1
                      have hroot_eq3 : ∀ g k, (g, k) ∈ ([("ws", 16), ("bs", 48), ("ts", 48)] : List (String × Nat)) →
                          globN m3 g ≠ 0 → memW ms3 (globN m3 g + k) = memW m3 (globN m3 g + k) := by
                        intro g k hgk hgnz
                        have hk_in : (g, k) ∈ ([("ws", 16), ("ts", 40), ("ts", 48), ("bs", 48)] : List (String × Nat)) := by
                          simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hgk ⊢
                          rcases hgk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
                        obtain ⟨hg_eq, hr_eq⟩ := hroots3 g k hk_in
                        have hhr := hr_eq hgnz
                        rwa [hg_eq] at hhr
                      have hC_ms3 : CodeDbPayloadBoundedNz ms3 S3 :=
                        codeDbPayloadBoundedNz_of_nonTrieStep hB_nil.1 hA_m3 hA_ms3 hws_ms3.1.1.2.1
                          hT_m3 hF_m3 hC_m3 hv3 hgrow_nt3 hfr_nt3 hglob_wbt3 hroot_eq3
                      have hev_ms3 : globN ms3 "ev" = globN m3 "ev" :=
                        globN_eq_of_lookup (hws_ms3.1.1.2.2.1 (ofString "ev") (by decide))
                      have hglob_wbte3 : ∀ g ∈ (["ws", "bs", "ts", "ev"] : List String), globN ms3 g = globN m3 g := by
                        intro g hg
                        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
                        rcases hg with rfl | rfl | rfl | rfl
                        · exact hglob_wbt3 "ws" (by decide)
                        · exact hglob_wbt3 "bs" (by decide)
                        · exact hglob_wbt3 "ts" (by decide)
                        · exact hev_ms3
                      have hM_ms3 : MsgDisjCodeStrong ms3 :=
                        msgDisjCodeStrong_of_roots_kept hM_m3 hglob_wbte3 h112_ms3_m3 hroot_eq3 hv3
                      have hS3_sub : ∀ t ∈ S3, t ∈ Sw3' ++ Frem3 := by
                        intro t ht
                        rcases List.mem_append.1 (hperm_S3.subset ht) with htw | htf
                        · exact List.mem_append_left _ (hSw3_sub t htw)
                        · exact List.mem_append_right _ htf
                      have hMO_ms3 : MsgOwned ms3 S3 (memW ms3 (globN ms3 "ev" + 112)) :=
                        msgOwned_sub_b4d hS3_sub hMO_ms3'
                      have hslots3 : ∀ ec ∈ evmChain ms3,
                          memW ms3 (ec.1 + 136) ∈ S3 ∧ memW ms3 (ec.1 + 168) ∈ S3 ∧ memW ms3 (ec.1 + 176) ∈ S3 := by
                        have hch_ms3 : evmChain ms3 = evmChain m3 := by
                          obtain ⟨_, hstep_tmp, _⟩ := msgBounded_stepCC_of_worldStepCodeSc
                            hB_nil hgw_hp (fun _ hg => hg) ⟨hA_m3, hM_m3, S3, hInvAt_m3, hMO_m3, hC_m3⟩ hws_ms3
                          exact hstep_tmp.1.2.2.2
                        rw [hch_ms3]
                        intro ec hec
                        have hFW_s := hInvAt_m3.2.2.2.2.1 ec hec
                        have hfo_disj_s := hInvAt_m3.2.2.2.2.2.2.2.2.1 ec hec (ec.1, 280) (by simp [frameObjects])
                        have hscr_ec := hFW_s.1 (ec.1, 280) (by simp)
                        have hal_ec : (ec.1, 280).2 = 0 ∨ AllocatedEvmB4d m3 (ec.1, 280) :=
                          Or.inr (Or.inr (Or.inr hscr_ec.1))
                        have hb_ec : ec.1 + 280 ≤ 2 ^ 64 :=
                          allocatedEvm_bound_b4d hA_m3.2 (Or.inr (Or.inr hscr_ec.1))
                        have hnt_disj : ∀ j ∈ nonTrieOwned m3 S3, Disj (ec.1, 280) j := by
                          intro j hj
                          unfold nonTrieOwned at hj
                          rcases List.mem_append.1 hj with htab | hfix
                          · obtain ⟨t, ht, hit⟩ := List.mem_flatMap.1 htab
                            exact hfo_disj_s.1 t ht j hit
                          · exact hfo_disj_s.2 j hfix
                        have hunhit : IvlUnhit m3 ms3 (ec.1, 280) :=
                          ivlUnhit_of_worldStep_frameOutside_b4d hA_m3.2 hfr_nt3
                            (nonTrieOwned_zero_aligned_b4d hT_m3 hF_m3)
                            (fun _ h => by cases h)
                            hscr_ec.2.1 hscr_ec.2.2.1 hal_ec hnt_disj (fun _ h => by cases h)
                        have he1_8 : ec.1 % 8 = 0 := hscr_ec.2.1
                        rw [memW_eq_of_ivlUnhit hunhit (by omega) hb_ec ⟨by omega, by omega⟩,
                            memW_eq_of_ivlUnhit hunhit (by omega) hb_ec ⟨by omega, by omega⟩,
                            memW_eq_of_ivlUnhit hunhit (by omega) hb_ec ⟨by omega, by omega⟩]
                        exact ⟨hFW_s.2.2.2.2.2.2.2.1, hFW_s.2.2.2.2.2.2.2.2.1, hFW_s.2.2.2.2.2.2.2.2.2.1⟩
                      have hW_ms3_S3 : WorldTyped ms3 S3 :=
                        ⟨hWT_S3_ms3.1, hWT_S3_ms3.2.1, hWT_S3_ms3.2.2.1, ⟨Nd_nt3, hWT_S3_ms3.2.2.2⟩⟩
                      have hInvAt_ms3 : EvmInvAt ms3 S3 := by
                        -- Note: `evmInvAt_sub_b4d` is private in `MsB4c2dEvmBridge`, so inline its 10-line proof
                        obtain ⟨_, hne, hlen, hlast, hFW', hFR, hRW, hPW, hFO', hAT', hMarks', hRoles', hGas⟩ := hInvAt_ms3'
                        refine ⟨hW_ms3_S3, hne, hlen, hlast, ?_, hFR, hRW, hPW, ?_,
                          avoidsTries_sub_b4d hS3_sub hAT', ?_, ?_, hGas⟩
                        · intro ec hec
                          obtain ⟨h1, h2, h3⟩ := hslots3 ec hec
                          obtain ⟨f1, f2, f3, f4, f5, f6, f7, _, _, _, f11, f12, f13, f14, f15, f16, f17⟩ := hFW' ec hec
                          exact ⟨f1, f2, f3, f4, f5, f6, f7, h1, h2, h3, f11, f12, f13, f14, f15, f16,
                            msgOwned_sub_b4d hS3_sub f17⟩
                        · intro ec hec o ho
                          exact ⟨fun t ht => (hFO' ec hec o ho).1 t (hS3_sub t ht), (hFO' ec hec o ho).2⟩
                        · intro i hi
                          obtain ⟨m1, m2, m3', m4, m5, m6, m7, m8, m9⟩ := hMarks' i hi
                          refine ⟨m1, m2, m3', m4, m5, m6, m7, ?_, m9⟩
                          intro t ht
                          rcases m8 t (hS3_sub t ht) with ⟨htake, hdel⟩ | hloc
                          · exact Or.inl ⟨htake, delExclusive_sub_b4d hS3_sub hdel⟩
                          · exact Or.inr hloc
                        · refine ⟨?_, hRoles'.2.1, hRoles'.2.2⟩
                          intro a ha
                          have hhdr := (hRoles'.1 a ha).2
                          refine ⟨?_, hhdr⟩
                          rcases List.mem_append.1 ha with hwf | hjr
                          · rcases List.mem_append.1 hwf with hw | hf
                            · exact (hW_ms3_S3.1.2.2.2.2.2.2.2.2.2.2.2.1 a (List.mem_append_left _ hw)).1
                            · obtain ⟨ec, hec, ha_ec⟩ := List.mem_flatMap.1 hf
                              obtain ⟨h136, h168, h176⟩ := hslots3 ec hec
                              simp only [List.mem_cons, List.not_mem_nil, or_false] at ha_ec
                              rcases ha_ec with rfl | rfl | rfl
                              · exact h136
                              · exact h168
                              · exact h176
                          · exact (hW_ms3_S3.1.2.2.2.2.2.2.2.2.2.2.2.1 a (List.mem_append_right _ hjr)).1
                      have hwsl_fresh_m3_ms3 : Inside (wsl.toNat, 16) (globN m3 "heap_ptr") (globN ms3 "heap_ptr") :=
                        ⟨hwsl_lo, hwsl_in_ms3.2⟩
                      have hbuf_fix : ∀ gs ∈ wsAcctBufs, bufferRegion m3 gs ∈ fixedObjects m3 := by
                        intro gs hgs
                        simp only [wsAcctBufs, List.mem_cons, List.not_mem_nil, or_false] at hgs
                        rcases hgs with rfl | rfl | rfl
                        · unfold fixedObjects
                          apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
                          exact List.mem_map.2 ⟨(("keccak_pad", 136) : String × Nat), by decide, rfl⟩
                        · unfold fixedObjects
                          apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
                          exact List.mem_map.2 ⟨(("keccak_st", 200) : String × Nat), by decide, rfl⟩
                        · unfold fixedObjects
                          apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
                          exact List.mem_map.2 ⟨(("mpt_nib_scratch", 64) : String × Nat), by decide, rfl⟩
                      have hu_tab : ∀ t ∈ S3, ∀ i ∈ htabFootprint m3 t, IvlUnhit m3 ms3 i := by
                        intro t ht i hi
                        obtain ⟨hwf, hfp⟩ := hT_m3.2.1 t ht
                        obtain ⟨hal, hdisj_fix⟩ := hfp i hi
                        exact ivlUnhit_of_worldEff_wsAcct_b4d hA_m3.2 heff_ms3 (hwf.1 i hi).2
                          (allocatedEvm_of_allocated_b4d hal)
                          (fun gs hgs => hdisj_fix _ (hbuf_fix gs hgs))
                      have hfp_eq : ∀ t ∈ S3, htabFootprint ms3 t = htabFootprint m3 t := by
                        intro t ht
                        obtain ⟨hwf, _⟩ := hT_m3.2.1 t ht
                        have hfp_h : (t, 88) ∈ htabFootprint m3 t := by simp [htabFootprint]
                        obtain ⟨hinside, hwords⟩ := hwf.1 (t, 88) hfp_h
                        have ht2 : t + 88 ≤ heapEnd := hinside.2
                        have h1 : heapEnd ≤ 2 ^ 64 := by decide
                        exact (htabFootprint_eq_of_hdr_unhit (show t % 8 = 0 from hwords.1)
                          (by omega) (hu_tab t ht (t, 88) hfp_h)).2
                      have heff_ws : WorldEff m3 ms3 [] wsAcctBufs wsGw := by
                        refine ⟨heff_ms3.arena, heff_ms3.code, heff_ms3.memaddrs, heff_ms3.be,
                          heff_ms3.eshapes, heff_ms3.hp_lo, heff_ms3.fmp_eq, heff_ms3.sp_hi, ?_,
                          heff_ms3.fresh_bufs, heff_ms3.out_dom, heff_ms3.cell_frame,
                          heff_ms3.byte_frame⟩
                        intro k hk
                        refine heff_ms3.gw_kept k (fun h => hk ?_)
                        obtain ⟨x, hx, hxe⟩ := List.mem_map.1 h
                        simp only [List.mem_singleton] at hx
                        subst hx
                        exact List.mem_map.2 ⟨"heap_ptr", by simp [wsGw], hxe⟩
                      have hfix_eq : fixedObjects ms3 = fixedObjects m3 :=
                        fixedObjects_eq_of_witness_effect hWT_m3 hA_m3 heff_ws
                      have hfix_al : ∀ j ∈ fixedObjects ms3, j.2 = 0 ∨ AllocatedEvmB4d m3 j := by
                        intro j hj
                        rw [hfix_eq] at hj
                        rcases hF_m3.1 j hj with h0 | ⟨hal, _⟩
                        · exact Or.inl h0
                        · exact Or.inr (allocatedEvm_of_allocated_b4d hal)
                      have hi_al_nt_ms3 : ∀ j ∈ nonTrieOwned ms3 S3, j.2 = 0 ∨ AllocatedEvmB4d m3 j := by
                        intro j hj
                        unfold nonTrieOwned at hj
                        rcases List.mem_append.1 hj with htab | hfix
                        · obtain ⟨t, ht, hit⟩ := List.mem_flatMap.1 htab
                          rw [hfp_eq t ht] at hit
                          have hal_j := (hT_m3.2.1 t ht).2 j hit
                          exact Or.inr (allocatedEvm_of_allocated_b4d hal_j.1)
                        · exact hfix_al j hfix
                      have hwsl_disj_nt_ms3 : ∀ j ∈ nonTrieOwned ms3 S3, Disj (wsl.toNat, 16) j :=
                        fun j hj =>
                          (allocatedEvm_disj_freshHeap_b4d hA_m3.2 hA_ms3.2 hws_ms3.1.1.2.1
                            (hi_al_nt_ms3 j hj) hwsl_fresh_m3_ms3).flip
                      have hsl_ev : @evalHOLExact 64 F _ ms3.toExact
                          (fun a => Classical.propDecidable (ms3.memaddrs a))
                          (.var .local (ofString "sl")) = some (.val (.word wsl)) := by
                        have hms3_sl : ms3.locals.lookup (ofString "sl") = some (.val (.word wsl)) := by
                          rw [hms3_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
                        simp [evalHOLExact, toExact, hms3_sl]
                      have hwsl_disj_msg : Disj (memW ms3 (globN ms3 "ev" + 112), 176) (wsl.toNat, 16) := by
                        rw [hev_ms3, h112_ms3_m3]
                        exact allocatedEvm_disj_freshHeap_b4d hA_m3.2 hA_ms3.2 hws_ms3.1.1.2.1
                          (Or.inr (allocatedEvm_of_allocated_b4d hMO_m3.1)) hwsl_fresh_m3_ms3
                      obtain ⟨hMB_j, hCC_j, h112_j⟩ :=
                        jset_ts48_bounded_step ms3 S3 (.var .local (ofString "h"))
                          (.var .local (ofString "sl")) wsl hcms3 hA_ms3 hM_ms3 hInvAt_ms3 hMO_ms3 hC_ms3
                          hsl_ev hwsl_in_ms3 hwsl_words_ms3 hwsl_len_ms3 hwsl_disj_nt_ms3 hwsl_disj_msg hnt_j hfr_j
                      exact ⟨hMB_j, evmStepCC_mono_gw_b4d (fun g hg => by
                        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
                        rcases hg with rfl | rfl <;> decide) hCC_j, h112_j⟩)
                    hnt_i hfr_i
              · simp [hev_c] at hfr_i; exact absurd hfr_i not_flowingOrResumes_error
              · simp [hev_c] at hfr_i; exact absurd hfr_i not_flowingOrResumes_error
          have hIte_avoids : ∀ k : MlS, avoidsLocal k pIte = true := by
            intro k
            dsimp only [pIte, avoidsLocal]
            by_cases hk : k == ofString "sl"
            · simp [hk]
            · simp [hk]
          change EvmMbStep setCodeGw m3 (evaluateHOLFiniteState m3 (.seq pIte _)).2
          have hmeta_i := (PanRunBounded.evaluateHOLFiniteState_metadata m3 pIte).1
          rw [evaluateHOLFiniteState_seq_line780] at hnt3 hfr3 ⊢
          rcases hri : evaluateHOLFiniteState m3 pIte with ⟨ri, m4⟩
          have hri_def : evaluateHOLFiniteState m3
              (.ite (.cmp .equal (.var .local (ofString "eq")) (.const 0#64))
                (.decCall (ofString "sl") .one (ofString "alloc") [.const 16#64]
                  (.seq (.store (.var .local (ofString "sl")) (.var .local (ofString "code")))
                    (.seq (.store (.op .add [.var .local (ofString "sl"), .const 8#64])
                        (.var .local (ofString "code_len")))
                      (.call (some (none, none)) (ofString "jset")
                        [.load .one (.op .add [.var .global (ofString "ts"), .const 48#64]),
                         .var .local (ofString "h"), .var .local (ofString "sl")]))))
                .skip) = (ri, m4) := hri
          simp only [hri, hri_def] at hmeta_i hnt3 hfr3 ⊢
          cases ri with
          | some cri =>
            have hs_i := hIte_step (by rw [hri]; exact hnt3) (by rw [hri]; exact hfr3)
            rw [hri] at hs_i; exact hs_i
          | none =>
            dsimp only at hnt3 hfr3 ⊢
            have hs_i := hIte_step (by rw [hri]; simp) (by rw [hri]; exact Or.inl rfl)
            rw [hri] at hs_i; dsimp only at hs_i
            have hc4 : m4.code = originalRuntimeCode := hmeta_i.trans hc3
            have hm4_loc : m4.locals = m3.locals := by
              apply HolFiniteMapExact.ext; funext k
              have hk := evaluate_avoidsLocal_flowing k pIte (hIte_avoids k) m3
                (by rw [hri]; exact Or.inl rfl)
              simpa [hri] using hk
            have hm4_h : m4.locals.lookup (ofString "h") = some (.val (.word wh)) := by
              rw [hm4_loc]; exact hm3_h
            exact evmMbStep_trans (by decide) hs_i
              (evmMbStep_decCall_get_account_b4d m4 (ofString "a") .one [.var .local (ofString "addr")]
                (.seq (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
                    [.var .local (ofString "a")])
                  (.seq (.store (.op .add [.var .local (ofString "a"), .const 48#64])
                      (.var .local (ofString "h")))
                    (.seq (.call (some (none, none)) (ofString "modify_state_commit")
                        [.var .local (ofString "addr"), .var .local (ofString "a")])
                      (.return (.const 0#64)))))
                hc4 hs_i.1
                (fun _ m5 _ hm5_loc hc5 hMB5 hnt5 hfr5 => by
                  have hm5_h : m5.locals.lookup (ofString "h") = some (.val (.word wh)) := by
                    rw [hm5_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm4_h,
                      show ofString "a" ≠ ofString "h" by decide]
                  obtain ⟨hs5_mb, hs5_cc, hs5_112⟩ := msgBounded_stepCC_of_worldStepCodeSc hB hgw
                    (fun g hg => hg) hMB5
                    (worldStepCodeSc_acctCopy_mut_tail_at_b4d hB hgw (by decide)
                      (.store (.op .add [.var .local (ofString "a"), .const 48#64])
                        (.var .local (ofString "h")))
                      (.seq (.call (some (none, none)) (ofString "modify_state_commit")
                          [.var .local (ofString "addr"), .var .local (ofString "a")])
                        (.return (.const 0#64)))
                      hc5 (worldOK_of_msgBounded hMB5)
                      (fun s1_ac bw heff1 hs1_ac_loc hs1_ac_a hbw_lo hbw_hi _ _ =>
                        R16Shards.worldEff_store_word heff1 _ _
                          (fun v hv => by
                            have hs1_h : s1_ac.locals.lookup (ofString "h") = some (.val (.word wh)) := by
                              rw [hs1_ac_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm5_h,
                                show ofString "a" ≠ ofString "h" by decide]
                            simp [evalHOLExact, hs1_h] at hv
                            exact ⟨wh, hv.symm⟩)
                          (fun x hx _ => by
                            simp [evalHOLExact, evalListHOLExact, hs1_ac_a, panOpHOL, wordOpHOL,
                              wordOp, valueIsWord, valueWord] at hx
                            subst hx
                            have hx48 : (bw + 48#64).toNat = bw.toNat + 48 := by
                              apply BitVec.toNat_add_of_lt; change bw.toNat + 48 < 2 ^ 64; omega
                            exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))
                      (progWStepCode_seq hB hgw
                        (progWStepCode_call0 (by intro p hp; simp at hp; subst hp; simp [acctMutBufs])
                          (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> decide)
                          wkCodeSc_modify_state_commit)
                        (progWStepCode_return _ _ _))
                      hnt5 hfr5)
                  exact ⟨hs5_mb, hs5_cc, hs5_112⟩)
                hnt3 hfr3))
        hnt2 hfr2)
    hnt0 hfr0


