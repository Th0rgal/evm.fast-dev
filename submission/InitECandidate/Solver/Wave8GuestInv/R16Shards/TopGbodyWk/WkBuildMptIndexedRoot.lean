import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkBuildMptIndexedStep

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.nameCheck false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc
open InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12

/-! ## `mpt_root_body_fresh` and `eval_call_mpt_root_fresh` -/

theorem mpt_root_body_fresh {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (mark : Nat) (wm wout : BitVec 64) (Nm : List Nat)
    (hc : s.code = originalRuntimeCode)
    (hAR : ArenaReady s)
    (hB : BmiScratchOK s)
    (hB_pre : ∀ gs ∈ bmiScratch, globN s gs.1 ≠ 0 →
      globN s gs.1 + gs.2 ≤ mark ∨ globN s "scratch_ptr" ≤ globN s gs.1)
    (hFT : FreshTrie s mark wm Nm)
    (hlk_m : s.locals.lookup (ofString "m") = some (.val (.word wm)))
    (hlk_out : s.locals.lookup (ofString "out") = some (.val (.word wout)))
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_mpt_root)).1) :
    let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_mpt_root)).2
    HeapByteEff s post
      ([(wout.toNat, 32)] ++ nodeCacheIvls Nm ++ keccakBufIvls s)
      ["heap_ptr", "scratch_ptr"] := by
  intro post
  obtain ⟨hmark_hp, hmark_lo, hmark8, hwm_nat, hm_w, hN, hvs, hm_root, hext_in⟩ := hFT
  have hkc_alloc : ∀ iv ∈ keccakBufIvls s, 0 < iv.2 →
      iv.1 + iv.2 ≤ globN s "heap_ptr" ∨ globN s "scratch_ptr" ≤ iv.1 := by
    intro iv hiv hpos
    simp only [keccakBufIvls, List.mem_cons, List.not_mem_nil, or_false] at hiv
    rcases hiv with rfl | rfl
    · by_cases hz : globN s "keccak_pad" = 0
      · simp [bufferRegion, hz] at hpos
      · rcases hB_pre ("keccak_pad", 136) (by simp [bmiScratch]) hz with h1 | h2
        · dsimp only at h1; exact Or.inl (by simp [bufferRegion, hz]; omega)
        · dsimp only at h2; exact Or.inr (by simp [bufferRegion, hz]; omega)
    · by_cases hz : globN s "keccak_st" = 0
      · simp [bufferRegion, hz] at hpos
      · rcases hB_pre ("keccak_st", 200) (by simp [bmiScratch]) hz with h1 | h2
        · dsimp only at h1; exact Or.inl (by simp [bufferRegion, hz]; omega)
        · dsimp only at h2; exact Or.inr (by simp [bufferRegion, hz]; omega)
  have hkc_disj : ∀ o ∈ nodeExtents s Nm,
      Disj (bufferRegion s ("keccak_pad", 136)) o ∧
      Disj (bufferRegion s ("keccak_st", 200)) o := by
    intro o ho
    have hsub : o = (0, 0) ∨ Inside o mark (globN s "heap_ptr") := by
      rcases hext_in o ho with rfl | ⟨h1, h2⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨by omega, h2⟩
    have hd := bmiScratch_disj_fresh hAR hB hmark_lo hB_pre hsub
    exact ⟨Disj.flip (hd ("keccak_pad", 136) (by simp [bmiScratch])),
           Disj.flip (hd ("keccak_st", 200) (by simp [bmiScratch]))⟩
  let mcZero : ProgHOL 64 :=
    .call (some (none, none)) (ofString "memcpy")
      [.var .local (ofString "out"), .var .global (ofString "empty_trie_root"), .const 32]
  let mcHash : ProgHOL 64 :=
    .call (some (none, none)) (ofString "memcpy")
      [.var .local (ofString "out"), .var .local (ofString "h"), .const 32]
  let body1 : ProgHOL 64 :=
    .seq
      (.ite (.cmp .equal (.var .local (ofString "root")) (.const 0))
        (.seq mcZero (.return (.const 0)))
        .skip)
      (.decCall (ofString "h") .one (ofString "node_hash") [.var .local (ofString "root")]
        (.seq mcHash (.return (.const 0))))
  have hbody : sourceFnBody Guest.Software.guestFn_mpt_root =
      .dec (ofString "root") .one (.load .one (.op .add [.var .local (ofString "m"), .const 0])) body1 := rfl
  change HeapByteEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_mpt_root)).2 _ _
  rw [hbody] at hres ⊢
  have hwm_hi : wm.toNat + 16 ≤ 2 ^ 64 := by
    have hhl : heapLimit ≤ 2 ^ 64 := by decide
    have := hAR.2.2.1; omega
  have hwm_w : WordsOK s (wm.toNat, 16) := hwm_nat.symm ▸ hm_w
  obtain ⟨rootw, hload_ev, hroot_nat⟩ :=
    eval_load_memW_of_wordsOK (s := s) (base := wm) (off := 0) (len := 16)
      hwm_w (by simp) (by decide) hwm_hi
      (e := .op .add [.var .local (ofString "m"), .const 0])
      (by simp [evalHOLExact, evalListHOLExact, hlk_m, wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero])
  have hroot_memW : memW s mark = rootw.toNat := by rw [← hwm_nat]; simpa using hroot_nat.symm
  have hdec_eq := evaluateHOLFiniteState_dec_total s (ofString "root") .one
    (.load .one (.op .add [.var .local (ofString "m"), .const 0])) body1
  dsimp only at hdec_eq; rw [hload_ev] at hdec_eq; dsimp only at hdec_eq
  have hsh_root : shapeEqHOL .one (shapeOfHOLExact (.val (.word rootw) : ValueHOL 64)) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  rw [if_pos hsh_root] at hdec_eq
  rw [hdec_eq] at hres ⊢
  let s1 := setVarHOLFinite (ofString "root") (.val (.word rootw)) s
  have hs1_c : s1.code = originalRuntimeCode := hc
  have hs1_AR : ArenaReady s1 := ⟨guestInv_setVar _ _ _ hAR.1, hAR.2⟩
  have hs1_root : s1.locals.lookup (ofString "root") = some (.val (.word rootw)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs1_out : s1.locals.lookup (ofString "out") = some (.val (.word wout)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlk_out,
      show ofString "root" ≠ ofString "out" by decide]
  have hev_cmp : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
      (.cmp .equal (.var .local (ofString "root")) (.const 0)) =
      some (.val (.word (if rootw = 0#64 then 1 else 0))) := by
    simp [evalHOLExact, hs1_root, Compiler.Encoders.Asm.wordCmpHOL]
  by_cases hrz : rootw = 0#64
  · have hite : evaluateHOLFiniteState s1
        (.ite (.cmp .equal (.var .local (ofString "root")) (.const 0))
          (.seq mcZero (.return (.const 0))) .skip) =
        evaluateHOLFiniteState s1 (.seq mcZero (.return (.const 0))) := by
      rw [evaluateHOLFiniteState_ite, hev_cmp, if_pos hrz]; simp
    have hseq1 := evaluateHOLFiniteState_seq_line780 s1
      (.ite (.cmp .equal (.var .local (ofString "root")) (.const 0))
        (.seq mcZero (.return (.const 0))) .skip)
      (.decCall (ofString "h") .one (ofString "node_hash") [.var .local (ofString "root")]
        (.seq mcHash (.return (.const 0))))
    change evaluateHOLFiniteState s1 body1 = _ at hseq1; rw [hite] at hseq1
    obtain ⟨wetr, hwetr⟩ := hs1_AR.2.2.2.2.2.2.2.2.2 "empty_trie_root" (by decide)
    unfold GlobalWord at hwetr
    have hseq_mc := evaluateHOLFiniteState_seq_line780 s1 mcZero (.return (.const 0))
    rcases hmc_ev : evaluateHOLFiniteState s1 mcZero with ⟨rmc, smc⟩
    have hnt_mc : (evaluateHOLFiniteState s1 mcZero).1 ≠ some .timeOut := by
      rw [hmc_ev]; dsimp only; rintro rfl
      have h1 : evaluateHOLFiniteState s1 (.seq mcZero (.return (.const 0))) = (some .timeOut, smc) := by
        rw [hseq_mc, hmc_ev]
      have h2 : evaluateHOLFiniteState s1 body1 = (some .timeOut, smc) := by rw [hseq1, h1]
      dsimp only at hres; rw [h2] at hres; exact not_resumes_timeout_bmi hres
    have hmc := eval_call_memcpy_heap s1
      (.var .local (ofString "out")) (.var .global (ofString "empty_trie_root")) (.const 32)
      wout wetr 32 [(wout.toNat, 32)] ["heap_ptr", "scratch_ptr"]
      hs1_c hs1_AR
      (by simp [evalHOLExact, hs1_out]) (by simp [evalHOLExact, hwetr]) rfl
      (fun _ => ⟨(wout.toNat, 32), List.mem_cons_self, le_rfl, le_rfl⟩) hnt_mc
    have hmc_none : rmc = none := by
      cases rmc with
      | none => rfl
      | some r0 =>
        exfalso
        have hnot_res := hmc.2 (by rw [hmc_ev]; simp)
        have h1 : evaluateHOLFiniteState s1 (.seq mcZero (.return (.const 0))) = (some r0, smc) := by
          rw [hseq_mc, hmc_ev]
        have h2 : evaluateHOLFiniteState s1 body1 = (some r0, smc) := by rw [hseq1, h1]
        dsimp only at hres; rw [h2] at hres; rw [hmc_ev] at hnot_res
        exact hnot_res hres
    obtain ⟨heff_mc, _, _⟩ := hmc.1 (by rw [hmc_ev]; exact hmc_none)
    rw [hmc_ev] at heff_mc; dsimp only at heff_mc
    have hret_ev : evaluateHOLFiniteState smc (.return (.const 0)) =
        (some (.returned (.val (.word 0))), smc.emptyLocalsHOLFinite) := by
      rw [evaluateHOLFiniteState_return]; simp [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
    have hseq_mc_ev : evaluateHOLFiniteState s1 (.seq mcZero (.return (.const 0))) =
        (some (.returned (.val (.word 0))), smc.emptyLocalsHOLFinite) := by
      rw [hseq_mc, hmc_ev, hmc_none]; dsimp only; exact hret_ev
    rw [hseq_mc_ev] at hseq1; dsimp only at hseq1; rw [hseq1]; dsimp only
    have heff_post : HeapByteEff s
        { smc.emptyLocalsHOLFinite with
          locals := HolFiniteMapExact.resVarEq smc.emptyLocalsHOLFinite.locals
            (ofString "root", s.locals.lookup (ofString "root")) }
        [(wout.toNat, 32)] ["heap_ptr", "scratch_ptr"] :=
      (((HeapByteEff.refl hAR _ _).locals_clock s1.locals s1.clock).trans heff_mc).locals_clock _ _
    exact heff_post.mono
      (fun iv hiv _ => by
        simp only [List.mem_singleton] at hiv; subst hiv
        exact Or.inl ⟨(wout.toNat, 32), by simp, le_rfl, le_rfl⟩)
      (fun _ hg => hg)
  · have hite : evaluateHOLFiniteState s1
        (.ite (.cmp .equal (.var .local (ofString "root")) (.const 0))
          (.seq mcZero (.return (.const 0))) .skip) = (none, s1) := by
      rw [evaluateHOLFiniteState_ite, hev_cmp, if_neg hrz]; simp [evaluateHOLFiniteState_skip]
    have hseq1 := evaluateHOLFiniteState_seq_line780 s1
      (.ite (.cmp .equal (.var .local (ofString "root")) (.const 0))
        (.seq mcZero (.return (.const 0))) .skip)
      (.decCall (ofString "h") .one (ofString "node_hash") [.var .local (ofString "root")]
        (.seq mcHash (.return (.const 0))))
    change evaluateHOLFiniteState s1 body1 = _ at hseq1; rw [hite] at hseq1; dsimp only at hseq1
    rw [hseq1] at hres ⊢
    let dcProg : ProgHOL 64 :=
      .decCall (ofString "h") .one (ofString "node_hash") [.var .local (ofString "root")]
        (.seq mcHash (.return (.const 0)))
    have hrz_nat : rootw.toNat ≠ 0 := fun h0 => hrz (BitVec.eq_of_toNat_eq (by simpa using h0))
    have hroot_in : rootw.toNat ∈ Nm := by
      rcases hm_root with h0 | hin
      · exact absurd (hroot_memW ▸ h0) hrz_nat
      · exact hroot_memW ▸ hin
    have hN1 : NodeHeap s1 Nm := hN
    have hvs1 : NodeHeapValuePtrOK s1 Nm := hvs
    rcases eval_decCall_node_hash_resumes_step s1 Nm "h" (.var .local (ofString "root")) rootw
        (.seq mcHash (.return (.const 0)))
        hs1_c hs1_AR hN1 hvs1 hkc_disj hkc_alloc
        (by simp [evalHOLExact, hs1_root]) hroot_in (Or.inr hres) with
      ⟨_, _, _, _, _, _, heff_ex, _⟩ |
      ⟨hw, mid, hmid_c, hmid_loc, heff_mid1, _, _, _, _, _, hdc_fst, hdc_snd⟩
    · have heff_post : HeapByteEff s
          { (evaluateHOLFiniteState s1 dcProg).2 with
            locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s1 dcProg).2.locals
              (ofString "root", s.locals.lookup (ofString "root")) }
          (nodeCacheIvls Nm ++ keccakBufIvls s ++ [freeGap s]) ["heap_ptr", "scratch_ptr"] :=
        (((HeapByteEff.refl hAR _ _).locals_clock s1.locals s1.clock).trans heff_ex).locals_clock _ _
      exact heff_post.mono
        (fun iv hiv hpos => by
          rcases List.mem_append.1 hiv with h1 | hfg
          · exact Or.inl ⟨iv, List.mem_cons_of_mem _ h1, le_rfl, le_rfl⟩
          · simp only [List.mem_singleton] at hfg; subst hfg
            have hfm_sp : globN s "frame_mem_ptr" ≤ globN s "scratch_ptr" := hAR.2.2.2.2.1
            exact Or.inr (Or.inl ⟨le_rfl, by unfold freeGap; dsimp only; omega⟩))
        (fun _ hg => hg)
    · have hres_cont : Resumes (evaluateHOLFiniteState mid (.seq mcHash (.return (.const 0)))).1 :=
        hdc_fst ▸ hres
      have hmid_out : mid.locals.lookup (ofString "out") = some (.val (.word wout)) := by
        rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs1_out,
          show ofString "h" ≠ ofString "out" by decide]
      have hmid_h : mid.locals.lookup (ofString "h") = some (.val (.word hw)) := by
        rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
      have hseq_mc := evaluateHOLFiniteState_seq_line780 mid mcHash (.return (.const 0))
      rcases hmc_ev : evaluateHOLFiniteState mid mcHash with ⟨rmc, smc⟩
      have hnt_mc : (evaluateHOLFiniteState mid mcHash).1 ≠ some .timeOut := by
        rw [hmc_ev]; dsimp only; rintro rfl
        have hseq_to : evaluateHOLFiniteState mid (.seq mcHash (.return (.const 0))) = (some .timeOut, smc) := by
          rw [hseq_mc, hmc_ev]
        rw [hseq_to] at hres_cont; exact not_resumes_timeout_bmi hres_cont
      have hmc := eval_call_memcpy_heap mid
        (.var .local (ofString "out")) (.var .local (ofString "h")) (.const 32)
        wout hw 32 [(wout.toNat, 32)] ["heap_ptr", "scratch_ptr"]
        hmid_c heff_mid1.arena
        (by simp [evalHOLExact, hmid_out]) (by simp [evalHOLExact, hmid_h]) rfl
        (fun _ => ⟨(wout.toNat, 32), List.mem_cons_self, le_rfl, le_rfl⟩) hnt_mc
      have hmc_none : rmc = none := by
        cases rmc with
        | none => rfl
        | some r0 =>
          exfalso
          have hnot_res := hmc.2 (by rw [hmc_ev]; simp)
          have hseq_r : evaluateHOLFiniteState mid (.seq mcHash (.return (.const 0))) = (some r0, smc) := by
            rw [hseq_mc, hmc_ev]
          rw [hseq_r] at hres_cont; rw [hmc_ev] at hnot_res
          exact hnot_res hres_cont
      obtain ⟨heff_mc, _, _⟩ := hmc.1 (by rw [hmc_ev]; exact hmc_none)
      rw [hmc_ev] at heff_mc; dsimp only at heff_mc
      have hret_ev : evaluateHOLFiniteState smc (.return (.const 0)) =
          (some (.returned (.val (.word 0))), smc.emptyLocalsHOLFinite) := by
        rw [evaluateHOLFiniteState_return]; simp [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
      have hcont_snd : (evaluateHOLFiniteState mid (.seq mcHash (.return (.const 0)))).2 =
          smc.emptyLocalsHOLFinite := by
        have hseq_ev : evaluateHOLFiniteState mid (.seq mcHash (.return (.const 0))) =
            (some (.returned (.val (.word 0))), smc.emptyLocalsHOLFinite) := by
          rw [hseq_mc, hmc_ev, hmc_none]; dsimp only; exact hret_ev
        rw [hseq_ev]
      let tgt := { (evaluateHOLFiniteState s1 dcProg).2 with
        locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s1 dcProg).2.locals
          (ofString "root", s.locals.lookup (ofString "root")) }
      have heff_mid_tgt : HeapByteEff mid tgt [(wout.toNat, 32)] ["heap_ptr", "scratch_ptr"] := by
        have heff0 := heff_mc.locals_clock tgt.locals tgt.clock
        have hst_eq : tgt = { smc with locals := tgt.locals, clock := tgt.clock } := by
          dsimp [tgt]; rw [hdc_snd, hcont_snd]; rfl
        rwa [← hst_eq] at heff0
      have heff_s_mid : HeapByteEff s mid (nodeCacheIvls Nm ++ keccakBufIvls s) ["heap_ptr", "scratch_ptr"] :=
        ((HeapByteEff.refl hAR _ _).locals_clock s1.locals s1.clock).trans heff_mid1
      exact (heff_s_mid.mono
          (fun iv hiv _ => Or.inl ⟨iv, List.mem_cons_of_mem _ hiv, le_rfl, le_rfl⟩)
          (fun _ hg => hg)).trans
        (heff_mid_tgt.mono
          (fun iv hiv _ => by
            simp only [List.mem_singleton] at hiv; subst hiv
            exact Or.inl ⟨(wout.toNat, 32), List.mem_cons_self, le_rfl, le_rfl⟩)
          (fun _ hg => hg))

theorem eval_call_mpt_root_fresh {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (mark : Nat) (wm wout : BitVec 64) (Nm : List Nat)
    (mExp outExp : ExpHOL 64)
    (hc : s.code = originalRuntimeCode)
    (hAR : ArenaReady s)
    (hB : BmiScratchOK s)
    (hB_pre : ∀ gs ∈ bmiScratch, globN s gs.1 ≠ 0 →
      globN s gs.1 + gs.2 ≤ mark ∨ globN s "scratch_ptr" ≤ globN s gs.1)
    (hFT : FreshTrie s mark wm Nm)
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [mExp, outExp] = some [.val (.word wm), .val (.word wout)])
    (hor : (evaluateHOLFiniteState s
        (.call (some (none, none)) (ofString "mpt_root") [mExp, outExp])).1 = none ∨
      Resumes (evaluateHOLFiniteState s
        (.call (some (none, none)) (ofString "mpt_root") [mExp, outExp])).1) :
    let out := evaluateHOLFiniteState s (.call (some (none, none)) (ofString "mpt_root") [mExp, outExp])
    HeapByteEff s out.2
      ([(wout.toNat, 32)] ++ nodeCacheIvls Nm ++ keccakBufIvls s)
      ["heap_ptr", "scratch_ptr"] ∧
    ((out.1 = none ∧ out.2.locals = s.locals) ∨
     (∃ eid ev, out.1 = some (.exception eid ev) ∧ eid ≠ ofString "TrapErr")) := by
  intro out; dsimp only [out]
  rw [evaluateHOLFiniteState_call] at hor ⊢
  rw [hargs] at hor ⊢; dsimp only at hor ⊢
  set callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    ((HolFiniteMapExact.empty : HolFiniteMapExact MlS (ValueHOL 64)).update
      (ofString "m", .val (.word wm))).update
      (ofString "out", .val (.word wout))
  have hl : lookupCodeHOLFinite s.code.lookup (ofString "mpt_root")
      [.val (.word wm), .val (.word wout)] =
      some (sourceFnBody Guest.Software.guestFn_mpt_root, callee, .one) := by
    rw [hc]
    exact lookupCodeHOLFinite_two_words_bmi (by decide) lookup_mpt_root_bmi
  rw [hl] at hor ⊢; dsimp only at hor ⊢
  by_cases hcz : s.clock = 0
  · rw [if_pos hcz] at hor
    rcases hor with hn | hr <;> [cases hn; exact absurd hr not_resumes_timeout_bmi]
  · rw [if_neg hcz] at hor ⊢
    let ent := callEntryStateHOLFinite s callee
    have hent_m : ent.locals.lookup (ofString "m") = some (.val (.word wm)) := by
      simp [ent, callee, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "out" ≠ ofString "m" by decide]
    have hent_out : ent.locals.lookup (ofString "out") = some (.val (.word wout)) := by
      simp [ent, callee, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases hrun : evaluateHOLFiniteState (s.callEntryStateHOLFinite callee) (sourceFnBody Guest.Software.guestFn_mpt_root) with ⟨res, cpost⟩
    have hres_ent : Resumes res := by
      cases res with
      | none =>
        rw [hrun] at hor; dsimp only at hor
        rcases hor with hn | hr <;> [cases hn; exact absurd hr R16Shards.not_resumes_error]
      | some r0 =>
        cases r0 with
        | returned v => exact Or.inl ⟨v, rfl⟩
        | exception eid ev =>
          rw [hrun] at hor; dsimp only at hor
          rcases hor with hn | hr
          · cases hn
          · rcases hr with ⟨_, hrv⟩ | ⟨e', v', hex, hne⟩
            · cases hrv
            · injection hex with hex'; cases hex'; exact Or.inr ⟨eid, ev, rfl, hne⟩
        | timeOut =>
          rw [hrun] at hor; dsimp only at hor
          rcases hor with hn | hr <;> [cases hn; exact absurd hr not_resumes_timeout_bmi]
        | error =>
          rw [hrun] at hor; dsimp only at hor
          rcases hor with hn | hr <;> [cases hn; exact absurd hr R16Shards.not_resumes_error]
        | «break» =>
          rw [hrun] at hor; dsimp only at hor
          rcases hor with hn | hr <;> [cases hn; exact absurd hr R16Shards.not_resumes_error]
        | «continue» =>
          rw [hrun] at hor; dsimp only at hor
          rcases hor with hn | hr <;> [cases hn; exact absurd hr R16Shards.not_resumes_error]
        | finalFfi _ =>
          rw [hrun] at hor; dsimp only at hor
          rcases hor with hn | hr <;> [cases hn; exact absurd hr not_resumes_finalFfi_bmi]
    have heff_ent := mpt_root_body_fresh ent mark wm wout Nm
      hc (R16Shards.localsFree_arenaReady s _ _ hAR) hB hB_pre hFT hent_m hent_out
      (by dsimp only [ent]; rw [hrun]; exact hres_ent)
    dsimp only [ent] at heff_ent; rw [hrun] at heff_ent; dsimp only at heff_ent
    have heff_s_cpost : HeapByteEff s cpost
        ([(wout.toNat, 32)] ++ nodeCacheIvls Nm ++ keccakBufIvls s)
        ["heap_ptr", "scratch_ptr"] :=
      ((HeapByteEff.refl hAR _ _).locals_clock ent.locals ent.clock).trans heff_ent
    rcases hres_ent with ⟨v, rfl⟩ | ⟨eid, ev, rfl, hne⟩
    · rw [hrun] at hor; dsimp only at hor ⊢
      by_cases hsh : shapeEqHOL (shapeOfHOLExact v) .one = true
      · rw [if_pos hsh]
        exact ⟨heff_s_cpost.locals_clock s.locals cpost.clock, Or.inl ⟨rfl, rfl⟩⟩
      · rw [if_neg hsh] at hor
        rcases hor with hn | hr <;> [cases hn; exact absurd hr R16Shards.not_resumes_error]
    · dsimp only
      exact ⟨heff_s_cpost.locals_clock HolFiniteMapExact.empty cpost.clock, Or.inr ⟨eid, ev, rfl, hne⟩⟩

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
