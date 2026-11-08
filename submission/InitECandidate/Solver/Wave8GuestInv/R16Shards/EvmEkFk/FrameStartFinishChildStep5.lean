import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.FrameStartFinishChildStep5a

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8Contracts.M23 (EvmStep EvmKeeps EvmAvoids GlobalsKept)
open InitECandidate.Solver.Wave8GuestInv.R11Shards

/-- Weakened `FcIncorpSuccessStepW`: `heap_ptr` may grow during `log_append` and
`htab_union_into`, while all other globals are preserved. -/
def FcIncorpSuccessStepW2 : Prop :=
  ∀ {F : Type} {s0 st : PanSemStateFiniteExact 64 F} {S : List Nat},
    FcBranchState s0 st S →
    FcPoppedChild s0 st S →
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
        (∀ g : String, ofString g ≠ ofString "heap_ptr" → globN post g = globN st g) ∧
        evmChain post = evmChain st ∧
        OpDispatchSpec.evmR post ≤
          OpDispatchSpec.evmR st + (memW st (globN s0 "ev" + 64) + memW st (globN s0 "ev" + 192)) ∧
        Inside (globN s0 "ev", 280) (globN post "scratch_ptr") scratchEnd ∧
        WordsOK post (globN s0 "ev", 280) ∧
        memW post (globN post "ev" + 16) = memW st (globN st "ev" + 16) ∧
        memW post (globN post "ev" + 40) = memW st (globN st "ev" + 40) ∧
        memW post (globN post "ev" + 232) = memW st (globN st "ev" + 232))

private theorem ev_head_facts_s5b {F : Type} {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hA : ArenaReady s) (hInv : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt s S) :
    globN s "ev" + 280 ≤ 2 ^ 64 ∧
    WordsOK s (globN s "ev", 280) ∧
    s.globals.lookup (ofString "ev") =
      some (.val (.word (BitVec.ofNat 64 (globN s "ev")))) ∧
    memW s (globN s "ev" + 16) ≤ memW s (globN s "ev" + 232) ∧
    OpDispatchSpec.evmR s =
      memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192) +
        (((evmChain s).tail.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum) := by
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    rw [evmChain_cons]; exact List.mem_cons_self
  have hFW := hInv.2.2.2.2.1 _ hhead
  have hbnd := (InitECandidate.Solver.Wave8Contracts.M23.frameWF_bounds hA.2 hFW).1
  dsimp only at hbnd
  have hwok : WordsOK s (globN s "ev", 280) := (hFW.1 (globN s "ev", 280) (by simp)).2
  obtain ⟨evw, hevw⟩ := hA.2.2.2.2.2.2.2.2.2 "ev" (by decide)
  have hevw_eq : evw = BitVec.ofNat 64 (globN s "ev") := by
    apply BitVec.eq_of_toNat_eq
    unfold GlobalWord at hevw
    have hgn : globN s "ev" = evw.toNat := by simp [globN, hevw]
    rw [BitVec.toNat_ofNat, hgn, Nat.mod_eq_of_lt evw.isLt]
  subst hevw_eq
  unfold GlobalWord at hevw
  have hsp : memW s (globN s "ev" + 16) ≤ memW s (globN s "ev" + 232) := hFW.2.2.2.2.1
  have hR : OpDispatchSpec.evmR s =
      memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192) +
        (((evmChain s).tail.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum) := by
    unfold OpDispatchSpec.evmR
    conv_lhs => rw [evmChain_cons]
    conv_rhs => rw [evmChain_cons]
    simp [Nat.add_assoc]
  exact ⟨hbnd, hwok, hevw, hsp, hR⟩

private theorem disj_symm_s5b {i j : Ivl} (h : Disj i j) : Disj j i :=
  R11Shards.Disj.symm h

private theorem unhit_wordsOK_s5 {F : Type} {s post : PanSemStateFiniteExact 64 F} {ivl : Ivl}
    (hdom : post.memaddrs = s.memaddrs) (hbnd : ivl.1 + ivl.2 ≤ 2 ^ 64)
    (hu : InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post ivl)
    (hw : WordsOK s ivl) : WordsOK post ivl := by
  have hi8 : ivl.1 % 8 = 0 := hw.1
  refine ⟨hi8, hw.2.1, fun k hk => ?_⟩
  obtain ⟨w, hd, hm⟩ := hw.2.2 k hk
  have hlt : ivl.1 + 8 * k < 2 ^ 64 := by omega
  have htn : (BitVec.ofNat 64 (ivl.1 + 8 * k)).toNat = ivl.1 + 8 * k :=
    Nat.mod_eq_of_lt hlt
  have hk8 : (ivl.1 + 8 * k) % 8 = 0 := by omega
  have heq := hu (BitVec.ofNat 64 (ivl.1 + 8 * k)) (by rw [htn]; exact hk8)
    (by rw [htn]; omega) (by rw [htn]; omega)
  exact ⟨w, hdom ▸ hd, heq.trans hm⟩

private theorem unhit_wordAt_s5 {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {ivl : Ivl} {a : Nat}
    (hdom : post.memaddrs = s.memaddrs) (hbnd : ivl.1 + ivl.2 ≤ 2 ^ 64)
    (ha8 : a % 8 = 0) (ha_in : ivl.1 ≤ a ∧ a + 8 ≤ ivl.1 + ivl.2)
    (hu : InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post ivl)
    (hwa : WordAt s a) : WordAt post a ∧ memW post a = memW s a := by
  obtain ⟨w, hd, hm⟩ := hwa
  have hlt : a < 2 ^ 64 := by omega
  have htn : (BitVec.ofNat 64 a).toNat = a := Nat.mod_eq_of_lt hlt
  have heq := hu (BitVec.ofNat 64 a) (by rw [htn]; exact ha8)
    (by rw [htn]; exact ha_in.1) (by rw [htn]; exact ha_in.2)
  exact ⟨⟨w, hdom ▸ hd, heq.trans hm⟩, by unfold memW; rw [heq]⟩

private theorem unhit_logEntry_s5 {F : Type} {s post : PanSemStateFiniteExact 64 F} {log : Nat}
    (hAs : ArenaOK s)
    (hdom : post.memaddrs = s.memaddrs)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hvmsa : globN post "vm_system_address" = globN s "vm_system_address")
    (hu_rec : InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post (log, 40))
    (hok : LogEntryOK s log) :
    LogEntryOK post log ∧ logOwnedIvls post log = logOwnedIvls s log := by
  have hb : log + 40 < 2 ^ 64 := by
    have hh := hAs.2.1
    have hl := hok.2.1.2
    rw [R11Shards.heapLimit_val] at hh
    dsimp only at hl
    omega
  have hw : ∀ off ∈ ([0, 8, 16, 24, 32] : List Nat),
      memW post (log + off) = memW s (log + off) := by
    intro off hoff
    have ho : off + 8 ≤ 40 ∧ off % 8 = 0 := by revert off hoff; decide
    exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_rec
      (by have := hok.1.1; omega) (by omega) ⟨by omega, by omega⟩
  exact ⟨logEntryOK_transport_fc hok hdom hhp hw, logOwnedIvls_transport_fc hvmsa hw⟩

/-- `FcPoppedChild` transported across a `headSimpleOffs` update on the parent head `ev`. -/
theorem fcPoppedChild_of_head_simple_s5 {F : Type}
    {s0 s post : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hBS : FcBranchState s0 s S)
    (hPC : FcPoppedChild s0 s S)
    (hGp : GuestInv post)
    (hglob : post.globals = s.globals)
    (hbe : post.be = s.be)
    (hmem_out : ∀ x : BitVec 64,
      (∀ off ∈ headSimpleOffs, x ≠ BitVec.ofNat 64 (globN s "ev" + off)) →
      post.memory x = s.memory x)
    (hsp_le : memW post (globN s "ev" + 16) ≤ memW s (globN s "ev" + 232))
    (hgas_le : memW post (globN s "ev" + 64) + memW post (globN s "ev" + 192) +
      (((evmChain s).tail.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum) + 1 < 2 ^ 64)
    (hsp_eq : memW post (globN s "ev" + 16) = memW s (globN s "ev" + 16)) :
    FcPoppedChild s0 post S := by
  obtain ⟨hAp, hIp, hch, hfix, htab, hframes, _⟩ :=
    evmInvAt_of_head_simple hBS.arena hBS.inv hGp hglob hbe hmem_out hsp_le hgas_le
  set e0 := globN s "ev"
  set c0 := globN s "cur_cont"
  have hhead : (e0, c0) ∈ evmChain s := by rw [evmChain_cons]; exact List.mem_cons_self
  have hfo_head : (e0, 280) ∈ frameObjects s (e0, c0) := by simp [frameObjects]
  have he0_bnd := (ev_head_facts_s5b hBS.arena hBS.inv).1
  have hdom : post.memaddrs = s.memaddrs := hGp.memaddrs.trans hBS.arena.1.memaddrs.symm
  have hglob_eq : ∀ nm, globN post nm = globN s nm := fun nm => by simp [globN, hglob]
  have hoff_props : ∀ off ∈ headSimpleOffs,
      off + 8 ≤ 280 ∧ off % 8 = 0 ∧ off / 8 < 280 / 8 ∧ 8 * (off / 8) = off ∧
        off ≠ 136 ∧ off ≠ 232 := by
    intro off hoff; revert off hoff; decide
  have hdisj_unhit : ∀ ivl : Ivl, Disj ivl (e0, 280) → ivl.1 + ivl.2 ≤ 2 ^ 64 →
      InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post ivl := by
    intro ivl hdj hb a ha8 ha1 ha2
    apply hmem_out a
    intro off hoff heq
    have hoff_b := (hoff_props off hoff).1
    have htn : (BitVec.ofNat 64 (e0 + off)).toNat = e0 + off := Nat.mod_eq_of_lt (by omega)
    rw [heq, htn] at ha1 ha2
    rcases hdj with hd | hd | hd | hd <;> (try dsimp only at hd) <;> omega
  have hchild_bnd := fcPoppedChild_child_bound hBS hPC
  have hu_child : InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post (globN s0 "ev", 280) :=
    hdisj_unhit _ (hPC.child_disj_fo _ hhead _ hfo_head) hchild_bnd
  have hchild_cells := fcPoppedChild_child_cells_of_head_simple hBS hPC hmem_out
  have hrec_bnd := (InitECandidate.Solver.Wave8Contracts.M08.ivl_allocated_bound hBS.arena.2
    (Or.inr hPC.rec_scr.1)).2
  have hu_rec : InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post (globN s0 "cur_cont", 104) :=
    hdisj_unhit _ (hPC.rec_disj_fo _ hhead _ hfo_head) hrec_bnd
  have hcl_eq : memW post (globN s0 "ev" + 88) = memW s (globN s0 "ev" + 88) :=
    hchild_cells 88 (by omega)
  set cl := memW s (globN s0 "ev" + 88)
  have hcl_bnd := (InitECandidate.Solver.Wave8Contracts.M08.ivl_allocated_bound hBS.arena.2
    (Or.inr hPC.child_logs_scr.1)).2
  have hu_cl : InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post (cl, 24) :=
    hdisj_unhit _ (hPC.child_logs_disj_fo _ hhead _ hfo_head).1 hcl_bnd
  have hcl_words : ∀ off : Nat, off + 8 ≤ 24 → off % 8 = 0 → memW post (cl + off) = memW s (cl + off) :=
    fun off hoff hoff8 => InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_cl
      (by have := hPC.child_logs_scr.2.1; omega) (by dsimp at hcl_bnd; omega) ⟨by omega, by omega⟩
  have hfl_child_eq : frameLogs post (globN s0 "ev", globN s0 "cur_cont") =
      frameLogs s (globN s0 "ev", globN s0 "cur_cont") := by
    unfold frameLogs
    rw [hcl_eq, show memW post cl = memW s cl by simpa using hcl_words 0 (by omega) (by omega),
      hcl_words 16 (by omega) (by omega)]
  have hfl_alloc : Allocated s (frameLogs s (globN s0 "ev", globN s0 "cur_cont")) :=
    hPC.child_logs_arr_in
  have hfl_bnd := InitECandidate.Solver.Wave8Contracts.M23.allocated_le_2pow64 hBS.arena.2 hfl_alloc
  have hu_fl : InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post
      (frameLogs s (globN s0 "ev", globN s0 "cur_cont")) :=
    hdisj_unhit _ (hPC.child_logs_disj_fo _ hhead _ hfo_head).2 hfl_bnd
  have hll_post : LogsListOK post cl ∧
      frameLogObjects post (globN s0 "ev", globN s0 "cur_cont") =
        frameLogObjects s (globN s0 "ev", globN s0 "cur_cont") := by
    rcases hPC.child_logs_ok with hz | ⟨hw_cl, hal_cl, hlt_cl, hle_cl, hent_cl⟩
    · have hlo := hPC.child_logs_scr.1.1
      have hss : 0 < scratchStart := by decide
      have hfm := hBS.arena.2.2.2.1; have hsc := hBS.arena.2.2.2.2.1
      dsimp at hlo; omega
    · have hp0_eq : memW post cl = memW s cl := by simpa using hcl_words 0 (by omega) (by omega)
      have hn_eq : memW post (cl + 8) = memW s (cl + 8) := hcl_words 8 (by omega) (by omega)
      have hcap_eq : memW post (cl + 16) = memW s (cl + 16) := hcl_words 16 (by omega) (by omega)
      have hp0_8 : (memW s cl) % 8 = 0 := hPC.child_logs_arr_wok.1
      have hent_post : ∀ i < memW s (cl + 8),
          memW post (memW s cl + 8 * i) = memW s (memW s cl + 8 * i) ∧
          WordAt post (memW s cl + 8 * i) ∧
          LogEntryOK post (memW s (memW s cl + 8 * i)) ∧
          logOwnedIvls post (memW s (memW s cl + 8 * i)) =
            logOwnedIvls s (memW s (memW s cl + 8 * i)) := by
        intro i hi
        obtain ⟨hwa_i, hle_i⟩ := hent_cl i hi
        have hi_in : (frameLogs s (globN s0 "ev", globN s0 "cur_cont")).1 ≤ memW s cl + 8 * i ∧
            memW s cl + 8 * i + 8 ≤
              (frameLogs s (globN s0 "ev", globN s0 "cur_cont")).1 +
                (frameLogs s (globN s0 "ev", globN s0 "cur_cont")).2 := by
          unfold frameLogs
          have hcl_def : memW s (globN s0 "ev" + 88) = cl := rfl
          rw [hcl_def]
          have hle_cl' : memW s (cl + 8) ≤ memW s (cl + 16) := hle_cl
          dsimp only; omega
        obtain ⟨hwa_p, hmw_p⟩ := unhit_wordAt_s5 hdom hfl_bnd (by omega) hi_in hu_fl hwa_i
        set lg := memW s (memW s cl + 8 * i)
        have hlg_in : (lg, 40) ∈ frameLogObjects s (globN s0 "ev", globN s0 "cur_cont") := by
          unfold frameLogObjects; dsimp only
          have hcl_def : memW s (globN s0 "ev" + 88) = cl := rfl
          rw [hcl_def]
          refine List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, ?_⟩
          unfold logOwnedIvls
          exact List.mem_filter.2 ⟨by simp [logRecordIvls, lg], by simp⟩
        have hlg_bnd : lg + 40 ≤ 2 ^ 64 :=
          InitECandidate.Solver.Wave8Contracts.M23.allocated_le_2pow64 hBS.arena.2 (Or.inl hle_i.2.1)
        have hu_lg := hdisj_unhit (lg, 40)
          (hPC.child_log_objs_disj_fo _ hlg_in _ hhead _ hfo_head) hlg_bnd
        obtain ⟨hle_p, hown_p⟩ := unhit_logEntry_s5 hBS.arena.2 hdom
          (by rw [hglob_eq]) (hglob_eq "vm_system_address") hu_lg hle_i
        exact ⟨hmw_p, hwa_p, hle_p, hown_p⟩
      refine ⟨Or.inr ⟨unhit_wordsOK_s5 hdom (by dsimp at hcl_bnd; omega) hu_cl hw_cl, ?_,
        by rw [hn_eq]; exact hlt_cl, by rw [hn_eq, hcap_eq]; exact hle_cl, ?_⟩, ?_⟩
      · exact InitECandidate.Solver.Wave8Contracts.M23.allocated_mono
          (by rw [hglob_eq]) (by rw [hglob_eq]) hal_cl
      · intro i hi
        rw [hn_eq] at hi
        obtain ⟨hmw_p, hwa_p, hle_p, _⟩ := hent_post i hi
        rw [hp0_eq]
        exact ⟨hwa_p, by rw [hmw_p]; exact hle_p⟩
      · unfold frameLogObjects; dsimp only
        rw [hcl_eq, hn_eq, hp0_eq]
        apply List.flatMap_congr
        intro i hi
        obtain ⟨hmw_p, _, _, hown_p⟩ := hent_post i (List.mem_range.1 hi)
        rw [hmw_p, hown_p]
  have hbyte_simple : ∀ b : Nat, b < 2 ^ 64 →
      (∀ r ∈ ([(e0, 280)] : List Ivl), ¬ (r.1 ≤ b ∧ b < r.1 + r.2)) →
      memB post b = memB s b := by
    intro b hb hno
    unfold memB
    have hal_b : (panByteAlignHOL (BitVec.ofNat 64 b)).toNat = b / 8 * 8 := by
      rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
    rw [hmem_out (panByteAlignHOL (BitVec.ofNat 64 b)), hbe]
    intro off hoff heq
    have hp := hoff_props off hoff
    have htn : (BitVec.ofNat 64 (e0 + off)).toNat = e0 + off := Nat.mod_eq_of_lt (by omega)
    have h1 := congrArg BitVec.toNat heq
    rw [hal_b, htn] at h1
    exact hno (e0, 280) (by simp) ⟨by dsimp only; omega, by dsimp only; omega⟩
  have heff_s : InitECandidate.Solver.Wave8Contracts.M23.ByteRegionEffect s post [(e0, 280)] := by
    refine ⟨hGp.code.trans hBS.arena.1.code.symm, hdom,
      hGp.shMemaddrs.trans hBS.arena.1.shMemaddrs.symm,
      hGp.baseAddr.trans hBS.arena.1.baseAddr.symm, hbe, hglob, ?_, ?_, hbyte_simple⟩
    · intro a hna
      apply hmem_out a
      intro off hoff rfl
      have hp := hoff_props off hoff
      obtain ⟨_, hd, _⟩ := (ev_head_facts_s5b hBS.arena hBS.inv).2.1.2.2 (off / 8) hp.2.2.1
      exact hna (by simpa [hp.2.2.2.1] using hd)
    · intro a ha
      apply hmem_out a
      intro off hoff rfl
      have hp := hoff_props off hoff
      have htn : (BitVec.ofNat 64 (e0 + off)).toNat = e0 + off := Nat.mod_eq_of_lt (by omega)
      exact ha (e0, 280) (by simp) ⟨by rw [htn]; omega, by rw [htn]; omega⟩
  obtain ⟨hW, _, _, _, hFW_all, _, _, _, hFO_disj, hAT, _, _, _⟩ := hBS.inv
  have hav_post : AvoidsTries post S (frameLogObjects s (globN s0 "ev", globN s0 "cur_cont")) := by
    obtain ⟨Nd, hTr, hdj⟩ := hPC.child_log_objs_avoids_tries
    obtain ⟨Nd_at, hTr_at, hAT_at⟩ := hAT
    obtain ⟨hTr_int, hsub_int⟩ := R11Shards.triesTypedWith_inter hTr_at hTr
    set Ndi := Nd_at.filter (fun n => decide (n ∈ Nd))
    have hWT_i : InitECandidate.Solver.Wave8Contracts.M23.WorldTypedWith s S Ndi :=
      ⟨hW.1, hW.2.1, hW.2.2.1, hTr_int⟩
    have hrec_disj_wti : ∀ j ∈ InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls s S Ndi,
        j.2 = 0 ∨ Disj (e0, 280) j := by
      intro j hj
      unfold InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls at hj
      simp only [List.mem_append] at hj
      rcases hj with ((((h1 | h2) | h3) | h4) | h5) | h6
      · obtain ⟨t, ht, hj_t⟩ := List.mem_flatMap.1 h1
        exact Or.inr ((hFO_disj _ hhead _ hfo_head).1 t ht j hj_t)
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h2
        exact Or.inr ((hFO_disj _ hhead _ hfo_head).2 _
          (InitECandidate.Solver.Wave8Contracts.M23.typedRec_in_fixedObjects s hr))
      · simp only [List.mem_singleton] at h3; subst h3
        have hfix_j : (if globN s "journal_cap" = 0 then 0 else globN s "journal",
            32 * globN s "journal_cap") ∈ fixedObjects s := by
          unfold fixedObjects
          exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp)))
        exact Or.inr ((hFO_disj _ hhead _ hfo_head).2 _ hfix_j)
      · exact Or.inr ((hFO_disj _ hhead _ hfo_head).2 _
          (InitECandidate.Solver.Wave8Contracts.M23.blockOut_in_fixedObjects h4))
      · exact Or.inr ((hFO_disj _ hhead _ hfo_head).2 _
          (InitECandidate.Solver.Wave8Contracts.M23.bal_in_fixedObjects h5))
      · exact Or.inr (hAT_at (e0, 280)
          (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨_, hhead, rfl⟩, hfo_head⟩) j (hsub_int j h6).1)
    have hcell : InitECandidate.Solver.Wave8Contracts.M23.SameTypedCells s post S Ndi :=
      InitECandidate.Solver.Wave8Contracts.M23.ByteRegionEffect.sameTypedCells
        (Rl := []) (extra := [(e0, 280)]) hBS.arena.1.memaddrs hWT_i
        (fun _ h => by simp at h)
        (fun x hx => by simp at hx; subst hx; exact hrec_disj_wti)
        (by simpa using heff_s)
    have hFT_post := InitECandidate.Solver.Wave8Contracts.M23.fixedTyped_of_eq hAp hW.2.2.1
      (by rw [hglob_eq]) (by rw [hglob_eq]) hfix
    obtain ⟨hWT_i_post, _⟩ := InitECandidate.Solver.Wave8Contracts.M23.worldTypedWith_congr_w1
      hBS.arena hAp (by rw [hglob_eq]) (by rw [hglob_eq])
      (fun g _ => hglob_eq g) hcell hWT_i
      ⟨hFT_post, fun o ho => Or.inl (by rw [← hfix]; exact ho)⟩
    refine ⟨Ndi, hWT_i_post.2.2.2, fun o ho j hj => ?_⟩
    rw [InitECandidate.Solver.Wave8Contracts.M23.nodeExtents_eq hTr_int.1 hcell] at hj
    exact hdj o ho j (hsub_int j hj).2
  have hu_fix_i : ∀ i ∈ fixedObjects s, InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post i := by
    intro i hi
    rcases hW.2.2.1.1 i hi with h0 | ⟨hal_i, _⟩
    · intro a _ ha1 ha2; rw [h0] at ha2; omega
    · exact hdisj_unhit i (disj_symm_s5b ((hFO_disj _ hhead _ hfo_head).2 i hi))
        (InitECandidate.Solver.Wave8Contracts.M08.ivl_allocated_bound hBS.arena.2 hal_i).2
  have hmemW_ne_head : ∀ a : Nat, a < 2 ^ 64 →
      (∀ off ∈ headSimpleOffs, a ≠ e0 + off) → memW post a = memW s a := by
    intro a ha hne
    unfold memW
    rw [hmem_out (BitVec.ofNat 64 a)]
    intro off hoff heq
    have hoff_b := (hoff_props off hoff).1
    have := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt (by omega)] at this
    exact hne off hoff this
  have h136_eq : ∀ ec ∈ evmChain s, memW post (ec.1 + 136) = memW s (ec.1 + 136) := by
    intro ec hec
    have hFW_ec := hFW_all ec hec
    have hb_ec : ec.1 + 280 ≤ 2 ^ 64 :=
      (InitECandidate.Solver.Wave8Contracts.M23.frameWF_bounds hBS.arena.2 hFW_ec).1
    apply hmemW_ne_head _ (by omega)
    intro off hoff heq
    have hp := hoff_props off hoff
    by_cases hec_eq : ec.1 = e0
    · exact hp.2.2.2.2.1 (by omega)
    · rw [evmChain_cons] at hec
      rcases List.mem_cons.1 hec with hhd | htl
      · exact hec_eq (Prod.mk.inj hhd).1
      · have hpw := hBS.inv.2.2.2.2.2.2.2.1
        rw [evmChain_cons, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw
        have hdj_ec : Disj (e0, 280) (ec.1, 280) := hpw.2.2 (e0, 280) hfo_head (ec.1, 280)
          (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨ec, htl, rfl⟩, by simp [frameObjects]⟩)
        rcases hdj_ec with hd | hd | hd | hd <;> (try dsimp only at hd) <;> omega
  have hbal_eq : balRecords post = balRecords s := by
    have h264 : heapEnd ≤ 2 ^ 64 := by decide
    exact InitECandidate.Solver.Wave8Contracts.M08.balRecords_eq_of_unhit hW.1
      (hglob_eq "bal_accounts") (fun hnz i hi => by
        rcases hW.1.2.2.2.2.2.2.1 "bal_accounts" (by decide) with h0 | hmS
        · exact absurd h0 hnz
        · have hfp_ba := (hW.1.2.1 _ hmS).1.1
          have hhi_i : i.1 + i.2 ≤ heapEnd := (hfp_ba i hi).1.2
          exact hdisj_unhit i (disj_symm_s5b ((hFO_disj _ hhead _ hfo_head).1 _ hmS i hi))
            (by omega))
  have hndt_post : ∀ t1 : Nat, NonDelAccessTable s S t1 → NonDelAccessTable post S t1 := by
    intro t1 ⟨ht1_S, ht1_del, ht1_ws, ht1_bs, ht1_ba, ht1_ad, ht1_ts⟩
    have hws_g := hglob_eq "ws"
    have hbs_g := hglob_eq "bs"
    have hts_g := hglob_eq "ts"
    have hba_g := hglob_eq "bal_accounts"
    refine ⟨ht1_S, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro ec hec; rw [hch] at hec; rw [h136_eq ec hec]; exact ht1_del ec hec
    · intro hnz
      rw [hws_g] at hnz
      have hm_ws := InitECandidate.Solver.Wave8Contracts.M08.typedRecord_mem_fixedObjects s
        (r := ("ws", 40)) (by simp [InitECandidate.Solver.Wave8Contracts.M08.typedRecords])
      simp only [hnz, ↓reduceIte] at hm_ws
      rw [InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hBS.arena.2 hW.2.2.1 "ws" 40
        (by simp [InitECandidate.Solver.Wave8Contracts.M08.typedRecords]) hws_g hnz (hu_fix_i _ hm_ws)
        (by omega) (by omega)]
      exact ht1_ws hnz
    · intro hnz
      rw [hbs_g] at hnz
      have hm_bs := InitECandidate.Solver.Wave8Contracts.M08.typedRecord_mem_fixedObjects s
        (r := ("bs", 80)) (by simp [InitECandidate.Solver.Wave8Contracts.M08.typedRecords])
      simp only [hnz, ↓reduceIte] at hm_bs
      rw [InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hBS.arena.2 hW.2.2.1 "bs" 80
        (by simp [InitECandidate.Solver.Wave8Contracts.M08.typedRecords]) hbs_g hnz (hu_fix_i _ hm_bs)
        (by omega) (by omega)]
      exact ht1_bs hnz
    · rw [hba_g]; exact ht1_ba
    · intro ad had; rw [hbal_eq] at had
      have had_bal : (ad, 40) ∈ balObjects s := by
        unfold balObjects; exact List.mem_flatMap.2 ⟨ad, had, by simp⟩
      have had_fix : (ad, 40) ∈ fixedObjects s := by
        unfold fixedObjects; exact List.mem_append.2 (Or.inr had_bal)
      rcases hW.2.2.1.1 _ had_fix with h0 | ⟨hal_ad, hw_ad⟩
      · simp at h0
      have hhi_ad := (InitECandidate.Solver.Wave8Contracts.M08.ivl_allocated_bound hBS.arena.2 hal_ad).2
      have had8 := hw_ad.1
      have h0 : memW post ad = memW s ad := by
        simpa using InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit (hu_fix_i _ had_fix)
          (by omega) hhi_ad ⟨by omega, by omega⟩
      rw [h0]; exact ht1_ad ad had
    · intro hnz
      rw [hts_g] at hnz
      have hm_ts := InitECandidate.Solver.Wave8Contracts.M08.typedRecord_mem_fixedObjects s
        (r := ("ts", 72)) (by simp [InitECandidate.Solver.Wave8Contracts.M08.typedRecords])
      simp only [hnz, ↓reduceIte] at hm_ts
      rw [InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hBS.arena.2 hW.2.2.1 "ts" 72
        (by simp [InitECandidate.Solver.Wave8Contracts.M08.typedRecords]) hts_g hnz (hu_fix_i _ hm_ts)
        (by omega) (by omega)]
      exact ht1_ts hnz
  refine {
    child_scr := ⟨by rw [hglob_eq]; exact hPC.child_scr.1,
      unhit_wordsOK_s5 hdom hchild_bnd hu_child hPC.child_scr.2⟩
    rec_scr := ⟨by rw [hglob_eq]; exact hPC.rec_scr.1,
      unhit_wordsOK_s5 hdom hrec_bnd hu_rec hPC.rec_scr.2⟩
    child_disj_fo := fun ec hec o ho => by
      rw [hch] at hec; rw [(hframes ec hec).1] at ho; exact hPC.child_disj_fo ec hec o ho
    rec_disj_fo := fun ec hec o ho => by
      rw [hch] at hec; rw [(hframes ec hec).1] at ho; exact hPC.rec_disj_fo ec hec o ho
    child_disj_ht := fun t ht i hi => by
      rw [htab t ht] at hi; exact hPC.child_disj_ht t ht i hi
    rec_disj_ht := fun t ht i hi => by
      rw [htab t ht] at hi; exact hPC.rec_disj_ht t ht i hi
    child_disj_fix := fun j hj => by
      rw [hfix] at hj; exact hPC.child_disj_fix j hj
    rec_disj_fix := fun j hj => by
      rw [hfix] at hj; exact hPC.rec_disj_fix j hj
    child_logs_scr := ⟨by rw [hcl_eq, hglob_eq]; exact hPC.child_logs_scr.1,
      by rw [hcl_eq]; exact unhit_wordsOK_s5 hdom hcl_bnd hu_cl hPC.child_logs_scr.2⟩
    child_logs_disj_fo := fun ec hec o ho => by
      rw [hch] at hec; rw [(hframes ec hec).1] at ho
      rw [hcl_eq, hfl_child_eq]; exact hPC.child_logs_disj_fo ec hec o ho
    child_logs_disj_ht := fun t ht i hi => by
      rw [htab t ht] at hi; rw [hcl_eq, hfl_child_eq]; exact hPC.child_logs_disj_ht t ht i hi
    child_logs_arr_in := by
      rw [hfl_child_eq, hglob_eq, hglob_eq]; exact hPC.child_logs_arr_in
    child_logs_arr_wok := by
      rw [hfl_child_eq]; exact unhit_wordsOK_s5 hdom hfl_bnd hu_fl hPC.child_logs_arr_wok
    child_logs_ok := by rw [hcl_eq]; exact hll_post.1
    child_logs_len_le := by
      rw [hcl_eq, hcl_words 8 (by omega) (by omega), hcl_words 16 (by omega) (by omega)]
      exact hPC.child_logs_len_le
    child_log_objs_pw := by rw [hll_post.2]; exact hPC.child_log_objs_pw
    child_log_objs_disj_fo := fun o1 ho1 ec hec o2 ho2 => by
      rw [hll_post.2] at ho1; rw [hch] at hec; rw [(hframes ec hec).1] at ho2
      exact hPC.child_log_objs_disj_fo o1 ho1 ec hec o2 ho2
    child_log_objs_disj_ht := fun o1 ho1 t ht i hi => by
      rw [hll_post.2] at ho1; rw [htab t ht] at hi
      exact hPC.child_log_objs_disj_ht o1 ho1 t ht i hi
    child_log_objs_disj_fix := fun o1 ho1 j hj => by
      rw [hll_post.2] at ho1; rw [hfix] at hj
      exact hPC.child_log_objs_disj_fix o1 ho1 j hj
    child_log_objs_avoids_tries := by rw [hll_post.2]; exact hav_post
    child_log_objs_disj_msg := fun o ho ec hec => by
      rw [hll_post.2] at ho; rw [hch] at hec; rw [(hframes ec hec).2.2.2.2.2.2.1]
      exact hPC.child_log_objs_disj_msg o ho ec hec
    addr_table_ok := by
      rw [hchild_cells 168 (by omega)]; exact hndt_post _ hPC.addr_table_ok
    key_table_ok := by
      rw [hchild_cells 176 (by omega)]; exact hndt_post _ hPC.key_table_ok
    parent_room := by
      rw [hglob_eq, hsp_eq, hmemW_ne_head (e0 + 232) (by omega)
        (fun off hoff heq => (hoff_props off hoff).2.2.2.2.2 (by omega))]
      exact hPC.parent_room
    out_win_ok := fun hne2 => by
      rw [hglob_eq, (hframes (e0, c0) hhead).2.2.2.2.2.1]
      exact hPC.out_win_ok hne2 }


theorem ev_head_facts_s5c {F : Type} {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hA : ArenaReady s) (hInv : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt s S) :
    globN s "ev" + 280 ≤ 2 ^ 64 ∧
    WordsOK s (globN s "ev", 280) ∧
    s.globals.lookup (ofString "ev") =
      some (.val (.word (BitVec.ofNat 64 (globN s "ev")))) ∧
    memW s (globN s "ev" + 16) ≤ memW s (globN s "ev" + 232) ∧
    OpDispatchSpec.evmR s =
      memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192) +
        (((evmChain s).tail.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum) := by
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    rw [evmChain_cons]; exact List.mem_cons_self
  have hFW := hInv.2.2.2.2.1 _ hhead
  have hbnd := (InitECandidate.Solver.Wave8Contracts.M23.frameWF_bounds hA.2 hFW).1
  dsimp only at hbnd
  have hwok : WordsOK s (globN s "ev", 280) := (hFW.1 (globN s "ev", 280) (by simp)).2
  obtain ⟨evw, hevw⟩ := hA.2.2.2.2.2.2.2.2.2 "ev" (by decide)
  have hevw_eq : evw = BitVec.ofNat 64 (globN s "ev") := by
    apply BitVec.eq_of_toNat_eq
    unfold GlobalWord at hevw
    have hgn : globN s "ev" = evw.toNat := by simp [globN, hevw]
    rw [BitVec.toNat_ofNat, hgn, Nat.mod_eq_of_lt evw.isLt]
  subst hevw_eq
  unfold GlobalWord at hevw
  have hsp : memW s (globN s "ev" + 16) ≤ memW s (globN s "ev" + 232) := hFW.2.2.2.2.1
  have hR : OpDispatchSpec.evmR s =
      memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192) +
        (((evmChain s).tail.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum) := by
    unfold OpDispatchSpec.evmR
    conv_lhs => rw [evmChain_cons]
    conv_rhs => rw [evmChain_cons]
    simp [Nat.add_assoc]
  exact ⟨hbnd, hwok, hevw, hsp, hR⟩

private theorem disj_symm_s5c {i j : Ivl} (h : Disj i j) : Disj j i :=
  R11Shards.Disj.symm h

private theorem disj_fresh_of_zero_or_allocated_s5c {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaOK s) (hAp : ArenaOK post) (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    {j : Ivl} (hj : j.2 = 0 ∨ Allocated s j) :
    Disj j (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := by
  rcases hj with h0 | hal
  · exact Or.inl h0
  · have hsep : heapLimit ≤ scratchStart := by decide
    obtain ⟨_, hs_hp, hs_fm, hs_sc, _⟩ := hAs
    obtain ⟨_, hp_hp, _, _, _⟩ := hAp
    rcases hal with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
    · exact Or.inr (Or.inr (Or.inl (by dsimp; omega)))
    · exact Or.inr (Or.inr (Or.inr (by dsimp; omega)))

theorem unhit_wordsOK_s5c {F : Type} {s post : PanSemStateFiniteExact 64 F} {ivl : Ivl}
    (hdom : post.memaddrs = s.memaddrs) (hbnd : ivl.1 + ivl.2 ≤ 2 ^ 64)
    (hu : InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post ivl)
    (hw : WordsOK s ivl) : WordsOK post ivl := by
  have hi8 : ivl.1 % 8 = 0 := hw.1
  refine ⟨hi8, hw.2.1, fun k hk => ?_⟩
  obtain ⟨w, hd, hm⟩ := hw.2.2 k hk
  have hlt : ivl.1 + 8 * k < 2 ^ 64 := by omega
  have htn : (BitVec.ofNat 64 (ivl.1 + 8 * k)).toNat = ivl.1 + 8 * k :=
    Nat.mod_eq_of_lt hlt
  have hk8 : (ivl.1 + 8 * k) % 8 = 0 := by omega
  have heq := hu (BitVec.ofNat 64 (ivl.1 + 8 * k)) (by rw [htn]; exact hk8)
    (by rw [htn]; omega) (by rw [htn]; omega)
  exact ⟨w, hdom ▸ hd, heq.trans hm⟩

private theorem disj_sub_right_s5c {a b c : Ivl}
    (hab : Disj a b) (hlo : b.1 ≤ c.1) (hhi : c.1 + c.2 ≤ b.1 + b.2) :
    Disj a c := by
  by_cases hc0 : c.2 = 0
  · exact Or.inr (Or.inl hc0)
  · rcases hab with ha0 | hb0 | hd1 | hd2
    · exact Or.inl ha0
    · omega
    · exact Or.inr (Or.inr (Or.inl (by omega)))
    · exact Or.inr (Or.inr (Or.inr (by omega)))

theorem frameObjects_lc_s5c {F : Type} (s : PanSemStateFiniteExact 64 F)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (ec : Ivl) :
    frameObjects { s with locals := L, clock := k } ec = frameObjects s ec := rfl

theorem evmInvAt_lc_s5c {F : Type}
    (s : PanSemStateFiniteExact 64 F) (L : HolFiniteMapExact MlS (ValueHOL 64))
    (ck : Nat) (S : List Nat) :
    InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt { s with locals := L, clock := ck } S ↔
      InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt s S := by
  let st' : PanSemStateFiniteExact 64 F := { s with locals := L, clock := ck }
  have hch' : evmChain st' = evmChain s := evmChain_lc_fc s L ck
  have hf : ∀ (nodes : Nat) (Fr : List Nat) (head : Nat),
      FreeChain st' nodes head Fr ↔ FreeChain s nodes head Fr := by
    intro nodes Fr; induction Fr with
    | nil => intro _; exact Iff.rfl
    | cons _ rest ih => intro _; exact and_congr Iff.rfl (ih _)
  have hw : ∀ t, HtabWF st' t ↔ HtabWF s t := by
    intro t; simp only [HtabWF, hf]; exact Iff.rfl
  have ht : ∀ S0, TablesTyped st' S0 ↔ TablesTyped s S0 := by
    intro S0; simp only [TablesTyped, hw]; exact Iff.rfl
  have hwt : WorldTyped st' S ↔ WorldTyped s S := by
    simp only [WorldTyped, ht]; exact Iff.rfl
  dsimp only [InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt]
  simp only [st', FrameWF, MsgOwned, hwt, hch']
  exact Iff.rfl

/-- Loop invariant for the child log transfer loop in `incorporate_child_on_success`.
Notice `bs` is held on `{ s with locals := s_init.locals, clock := s.clock }` so we do
not require `FcEntryLocals s0 s` inside the `incorporate_child_on_success` callee frame! -/
structure FcLogLoopInv {F : Type}
    (s0 s_init : PanSemStateFiniteExact 64 F) (S : List Nat)
    (cl p n : Nat) (s : PanSemStateFiniteExact 64 F) : Prop where
  bs : FcBranchState s0 { s with locals := s_init.locals, clock := s.clock } S
  child_scr : Inside (globN s0 "ev", 280) (globN s "scratch_ptr") scratchEnd ∧
    WordsOK s (globN s0 "ev", 280)
  child_disj_fo : ∀ ec ∈ evmChain s, ∀ o ∈ frameObjects s ec, Disj (globN s0 "ev", 280) o
  arr_disj_head_logs :
    Disj (p, 8 * memW s_init (cl + 16)) (memW s (globN s "ev" + 88), 24) ∧
    Disj (p, 8 * memW s_init (cl + 16)) (frameLogs s (globN s "ev", globN s "cur_cont"))
  child_96 : memW s (globN s0 "ev" + 96) = memW s_init (globN s0 "ev" + 96)
  child_136 : memW s (globN s0 "ev" + 136) = memW s_init (globN s0 "ev" + 136)
  ev_16 : memW s (globN s "ev" + 16) = memW s_init (globN s_init "ev" + 16)
  ev_40 : memW s (globN s "ev" + 40) = memW s_init (globN s_init "ev" + 40)
  ev_88 : memW s (globN s "ev" + 88) = memW s_init (globN s_init "ev" + 88)
  ev_232 : memW s (globN s "ev" + 232) = memW s_init (globN s_init "ev" + 232)
  r_eq : OpDispatchSpec.evmR s = OpDispatchSpec.evmR s_init
  ch_eq : evmChain s = evmChain s_init
  gk : ∀ g : String, ofString g ≠ ofString "heap_ptr" → globN s g = globN s_init g
  hp_le : globN s_init "heap_ptr" ≤ globN s "heap_ptr"
  p_lk : s.locals.lookup (ofString "p") = some (.val (.word (BitVec.ofNat 64 p)))
  n_lk : s.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 n)))
  child_lk : s.locals.lookup (ofString "child") =
    some (.val (.word (BitVec.ofNat 64 (globN s0 "ev"))))
  idx_ex : ∃ idx : Nat, idx ≤ n ∧
    s.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 idx))) ∧
    WordsOK s (p, 8 * memW s_init (cl + 16)) ∧
    (∀ j : Nat, idx ≤ j → j < n →
      memW s (p + 8 * j) = memW s_init (p + 8 * j) ∧
      LogEntryOK s (memW s_init (p + 8 * j)) ∧
      logOwnedIvls s (memW s_init (p + 8 * j)) =
        logOwnedIvls s_init (memW s_init (p + 8 * j))) ∧
    AvoidsTries s S ((List.range (n - idx)).flatMap
      (fun j => logOwnedIvls s_init (memW s_init (p + 8 * (idx + j))))) ∧
    (∀ o ∈ (List.range (n - idx)).flatMap
        (fun j => logOwnedIvls s_init (memW s_init (p + 8 * (idx + j)))),
      (∀ ec ∈ evmChain s, ∀ o2 ∈ frameObjects s ec, Disj o o2) ∧
      (∀ t ∈ S, ∀ ht ∈ htabFootprint s t, Disj o ht) ∧
      (∀ fx ∈ fixedObjects s, Disj o fx) ∧
      (∀ ec ∈ evmChain s, Disj (memW s (ec.1 + 112), 176) o))

theorem fcLogLoop_step {F : Type}
    {s0 s_init : PanSemStateFiniteExact 64 F} {S : List Nat}
    {cl p n : Nat}
    (hp_eq : p = memW s_init cl)
    (hn_eq : n = memW s_init (cl + 8))
    (hn_le_cap : n ≤ memW s_init (cl + 16))
    (hcl_eq : cl = memW s_init (globN s0 "ev" + 88))
    (hPC_init : FcPoppedChild s0 s_init S)
    (hBS_init : FcBranchState s0 s_init S)
    (s : PanSemStateFiniteExact 64 F)
    (hI : FcLogLoopInv s0 s_init S cl p n s)
    (hact : InitECandidate.Solver.Wave8M19.LoopActive
      (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "n"))) s)
    (_hclk : s.clock ≠ 0)
    (hbody_ok :
      (evaluateHOLFiniteState (decClockHOLFinite s)
        (.seq
          (.call (some (none, none)) (ofString "log_append")
            [.var .global (ofString "ev"),
             .load .one (.op .add [.var .local (ofString "p"),
               .panop .mul [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)]])])
          (.assign .local (ofString "i")
            (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)])))).1 = none ∨
      (evaluateHOLFiniteState (decClockHOLFinite s)
        (.seq
          (.call (some (none, none)) (ofString "log_append")
            [.var .global (ofString "ev"),
             .load .one (.op .add [.var .local (ofString "p"),
               .panop .mul [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)]])])
          (.assign .local (ofString "i")
            (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)])))).1 = some .continue ∨
      (evaluateHOLFiniteState (decClockHOLFinite s)
        (.seq
          (.call (some (none, none)) (ofString "log_append")
            [.var .global (ofString "ev"),
             .load .one (.op .add [.var .local (ofString "p"),
               .panop .mul [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)]])])
          (.assign .local (ofString "i")
            (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)])))).1 = some .break) :
    FcLogLoopInv s0 s_init S cl p n
      (evaluateHOLFiniteState (decClockHOLFinite s)
        (.seq
          (.call (some (none, none)) (ofString "log_append")
            [.var .global (ofString "ev"),
             .load .one (.op .add [.var .local (ofString "p"),
               .panop .mul [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)]])])
          (.assign .local (ofString "i")
            (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)])))).2 := by
  obtain ⟨idx, hidx_le, hi_lk, harr_wok, hrem_logs, hrem_av, hrem_disj⟩ := hI.idx_ex
  have hfl_init_def : frameLogs s_init (globN s0 "ev", globN s0 "cur_cont") =
      (p, 8 * memW s_init (cl + 16)) := by
    unfold frameLogs; dsimp only; rw [← hcl_eq, ← hp_eq]
  have hfl_init_bnd : p + 8 * memW s_init (cl + 16) < 2 ^ 64 := by
    have hse : scratchEnd < 2 ^ 64 := by rw [R11Shards.scratchEnd_val]; decide
    have hhl : heapLimit < 2 ^ 64 := by rw [R11Shards.heapLimit_val]; decide
    have hh_lim := hBS_init.arena.2.2.1
    rcases hPC_init.child_logs_arr_in with ⟨_, hhi⟩ | ⟨_, hhi⟩
    · rw [hfl_init_def] at hhi; dsimp only at hhi; omega
    · rw [hfl_init_def] at hhi; dsimp only at hhi; omega
  have hn_lt_263 : n < 2 ^ 63 := by
    have hse : scratchEnd < 2 ^ 63 := by rw [R11Shards.scratchEnd_val]; decide
    have hhl : heapLimit < 2 ^ 63 := by rw [R11Shards.heapLimit_val]; decide
    have hh_lim := hBS_init.arena.2.2.1
    rcases hPC_init.child_logs_arr_in with ⟨_, hhi⟩ | ⟨_, hhi⟩
    · rw [hfl_init_def] at hhi; dsimp only at hhi; omega
    · rw [hfl_init_def] at hhi; dsimp only at hhi; omega
  have hidx_lt_n : idx < n := by
    obtain ⟨w, hw, hw_nz⟩ := hact
    rw [evalHOLFinite_eq_toExact] at hw
    obtain ⟨a, b, ha, hb, hw_eq⟩ := InitECandidate.Solver.Wave8M19.evalAt_cmp s .less _ _ w hw
    have ha' : InitECandidate.Solver.Wave8M19.evalAt s (.var .local (ofString "i")) =
        some (.val (.word (BitVec.ofNat 64 idx))) := by
      simp [InitECandidate.Solver.Wave8M19.evalAt, evalHOLExact, hi_lk]
    have hb' : InitECandidate.Solver.Wave8M19.evalAt s (.var .local (ofString "n")) =
        some (.val (.word (BitVec.ofNat 64 n))) := by
      simp [InitECandidate.Solver.Wave8M19.evalAt, evalHOLExact, hI.n_lk]
    rw [ha'] at ha; injection ha with ha; injection ha with ha; injection ha with ha
    rw [hb'] at hb; injection hb with hb; injection hb with hb; injection hb with hb
    subst ha hb
    by_contra hge
    have hslt : Flapjack.Compiler.Encoders.Asm.holAsmSignedLess
        (BitVec.ofNat 64 idx) (BitVec.ofNat 64 n) = false := by
      unfold Flapjack.Compiler.Encoders.Asm.holAsmSignedLess
      have h263 : 2 ^ 63 < 2 ^ 64 := by decide
      have h1 : (BitVec.ofNat 64 idx).toNat < 2 ^ 63 := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
      have h2 : (BitVec.ofNat 64 n).toNat < 2 ^ 63 := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
      simp only [show 64 - 1 = 63 from rfl, if_pos h1, if_pos h2, decide_eq_false_iff_not]
      change ¬ ((BitVec.ofNat 64 idx).toNat < (BitVec.ofNat 64 n).toNat)
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show idx < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega)]
      omega
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hslt] at hw_eq
    exact hw_nz hw_eq
  let sd := decClockHOLFinite s
  have hsd_ch : evmChain sd = evmChain s := evmChain_lc_fc s s.locals (s.clock - 1)
  have hsd_R : OpDispatchSpec.evmR sd = OpDispatchSpec.evmR s := evmR_lc_fc s s.locals (s.clock - 1)
  let sd_aux : PanSemStateFiniteExact 64 F :=
    { sd with locals := s_init.locals, clock := sd.clock }
  have hBS_sd_aux : FcBranchState s0 sd_aux S := by
    let s_aux : PanSemStateFiniteExact 64 F :=
      { s with locals := s_init.locals, clock := s.clock }
    have hb : FcBranchState s0 { s_aux with locals := s_init.locals, clock := sd.clock } S :=
      fcBranchState_congr_locals_clock s_init.locals sd.clock hI.bs
        (fcEntryLocals_congr_locals (s1 := s_aux) rfl hI.bs.locals_ok)
    exact hb
  have hAsd : ArenaReady sd :=
    ⟨guestInv_congr (s := sd_aux) rfl rfl rfl rfl hBS_sd_aux.arena.1, hBS_sd_aux.arena.2⟩
  have hInvsd : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt sd S :=
    (evmInvAt_lc_s5c sd s_init.locals sd.clock S).mp hBS_sd_aux.inv
  let logExp : ExpHOL 64 :=
    .load .one (.op .add [.var .local (ofString "p"),
      .panop .mul [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)]])
  let callProg : ProgHOL 64 :=
    .call (some (none, none)) (ofString "log_append") [.var .global (ofString "ev"), logExp]
  let assignProg : ProgHOL 64 :=
    .assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)])
  have hseq_eq := evaluateHOLFiniteState_seq_line780 sd callProg assignProg
  rcases hcall_res : evaluateHOLFiniteState sd callProg with ⟨r1, s1⟩
  have hr1_none : r1 = none := by
    rcases r1 with _ | r1v
    · rfl
    · exfalso
      have hseq_r : (evaluateHOLFiniteState sd (.seq callProg assignProg)).1 = some r1v := by
        rw [hseq_eq]; dsimp only; rw [hcall_res]
      have hnb := InitECandidate.Solver.Wave8M19.Htab.call0_noRetBrk sd (ofString "log_append")
        [.var .global (ofString "ev"), logExp]
      rw [hcall_res] at hnb
      rcases hbody_ok with h1 | h2 | h3
      · rw [hseq_r] at h1; cases h1
      · rw [hseq_r] at h2; exact hnb.2 h2
      · rw [hseq_r] at h3; exact hnb.1.2 h3
  subst hr1_none
  set lg := memW s_init (p + 8 * idx)
  obtain ⟨hmemW_lg, hlg_ok_s, hlg_own_s⟩ := hrem_logs idx le_rfl hidx_lt_n
  have hslot_wa : WordAt sd (p + 8 * idx) := by
    have hwa := harr_wok.2.2 idx (by omega)
    exact ⟨hwa.choose, hwa.choose_spec.1, hwa.choose_spec.2⟩
  obtain ⟨w_slot, hdom_slot, hmem_slot⟩ := hslot_wa
  have haddr_bv : BitVec.ofNat 64 p + BitVec.ofNat 64 idx * BitVec.ofNat 64 8 =
      BitVec.ofNat 64 (p + 8 * idx) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show p < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show idx < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show (8 : Nat) < 2 ^ 64 by decide),
      Nat.mod_eq_of_lt (show idx * 8 < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show p + idx * 8 < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show p + 8 * idx < 2 ^ 64 by omega)]
    omega
  have hw_slot_eq : w_slot = BitVec.ofNat 64 lg := by
    apply BitVec.eq_of_toNat_eq
    have hm : memW s (p + 8 * idx) = w_slot.toNat := by
      unfold memW; change (match sd.memory _ with | .word v => v.toNat) = _; rw [hmem_slot]
    have hlg_def : lg = memW s_init (p + 8 * idx) := rfl
    rw [BitVec.toNat_ofNat, hlg_def, ← hmemW_lg, hm, Nat.mod_eq_of_lt w_slot.isLt]
  have hlog_arg : @evalHOLExact 64 F _ sd.toExact (fun a => Classical.propDecidable (sd.memaddrs a))
      logExp = some (.val (.word (BitVec.ofNat 64 lg))) := by
    have hp_sd : sd.locals.lookup (ofString "p") = some (.val (.word (BitVec.ofNat 64 p))) := hI.p_lk
    have hi_sd : sd.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 idx))) := hi_lk
    have hadd0 : BitVec.ofNat 64 p + (BitVec.ofNat 64 idx * BitVec.ofNat 64 8 + (0 : BitVec 64)) =
        BitVec.ofNat 64 (p + 8 * idx) := by
      change BitVec.ofNat 64 p + (BitVec.ofNat 64 idx * BitVec.ofNat 64 8 + 0#64) = _
      rw [BitVec.add_zero, haddr_bv]
    simp only [logExp, evalHOLExact, evalListHOLExact, hp_sd, hi_sd, panOpHOL, isWfShapeExactHOL,
      memLoadHOLExact, ↓reduceIte, valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map,
      Option.map, List.foldr, Bool.and_self]
    rw [hadd0]
    simp only [hdom_slot, ↓reduceIte, hmem_slot, hw_slot_eq]
  have hlg_wa : WordAt sd lg := by
    have hwa := hlg_ok_s.1.2.2 0 (show 0 < 40 / 8 by decide)
    dsimp only [Nat.mul_zero, Nat.add_zero] at hwa
    exact hwa
  have hlg_ok_sd : LogEntryOK sd lg := hlg_ok_s
  have hlg_own_sd : logOwnedIvls sd lg = logOwnedIvls s_init lg := hlg_own_s
  have hrange_split :
      (List.range (n - idx)).flatMap
        (fun j => logOwnedIvls s_init (memW s_init (p + 8 * (idx + j)))) =
      logOwnedIvls s_init lg ++
        (List.range (n - (idx + 1))).flatMap
          (fun j => logOwnedIvls s_init (memW s_init (p + 8 * (idx + 1 + j)))) := by
    have hsub : n - idx = 1 + (n - (idx + 1)) := by omega
    rw [hsub, List.range_add, List.flatMap_append, List.flatMap_map]
    simp only [List.range_one, List.flatMap_cons, List.flatMap_nil, List.append_nil, Nat.add_zero]
    congr 1; apply List.flatMap_congr; intro j _; congr 2; omega
  have hflo_init_eq : frameLogObjects s_init (globN s0 "ev", globN s0 "cur_cont") =
      (List.range n).flatMap (fun j => logOwnedIvls s_init (memW s_init (p + 8 * j))) := by
    unfold frameLogObjects; dsimp only; rw [← hcl_eq, ← hn_eq, ← hp_eq]
  have hpart := fcLogTransfer_prefix_partition ([] : List Ivl)
    (fun j => logOwnedIvls s_init (memW s_init (p + 8 * j)))
    (n := n) (k := idx) hidx_le List.Pairwise.nil
    (by rw [← hflo_init_eq]; exact hPC_init.child_log_objs_pw)
    (fun _ h => by cases h)
  have hrem_pw : ((List.range (n - idx)).flatMap
      (fun j => logOwnedIvls s_init (memW s_init (p + 8 * (idx + j))))).Pairwise Disj := hpart.2.1
  have hlg_disj_tail : ∀ a ∈ logOwnedIvls s_init lg,
      ∀ b ∈ (List.range (n - (idx + 1))).flatMap
        (fun j => logOwnedIvls s_init (memW s_init (p + 8 * (idx + 1 + j)))), Disj a b := by
    rw [hrange_split, List.pairwise_append] at hrem_pw
    exact hrem_pw.2.2
  have hlg_pw : (logOwnedIvls sd lg).Pairwise Disj := by
    rw [hrange_split, List.pairwise_append] at hrem_pw
    rw [hlg_own_sd]; exact hrem_pw.1
  have hlg_in_rem : ∀ o ∈ logOwnedIvls sd lg,
      o ∈ (List.range (n - idx)).flatMap
        (fun j => logOwnedIvls s_init (memW s_init (p + 8 * (idx + j)))) := by
    intro o ho
    rw [hlg_own_sd] at ho
    rw [hrange_split]
    exact List.mem_append_left _ ho
  have hlg_disj_fo : ∀ ec ∈ evmChain sd, ∀ o1 ∈ logOwnedIvls sd lg,
      ∀ o2 ∈ frameObjects sd ec, Disj o1 o2 := by
    intro ec hec o1 ho1 o2 ho2
    rw [hsd_ch] at hec
    have ho2' : o2 ∈ frameObjects s ec := ho2
    exact (hrem_disj o1 (hlg_in_rem o1 ho1)).1 ec hec o2 ho2'
  have hlg_disj_ht : ∀ o ∈ logOwnedIvls sd lg, ∀ t ∈ S,
      ∀ j ∈ htabFootprint sd t, Disj o j :=
    fun o ho t ht j hj => (hrem_disj o (hlg_in_rem o ho)).2.1 t ht j hj
  have hlg_disj_fix : ∀ o ∈ logOwnedIvls sd lg, ∀ j ∈ fixedObjects sd, Disj o j :=
    fun o ho j hj => (hrem_disj o (hlg_in_rem o ho)).2.2.1 j hj
  have hlg_avoids : AvoidsTries sd S (logOwnedIvls sd lg) := by
    obtain ⟨Nd, hTr, hdj⟩ := hrem_av
    exact ⟨Nd, hTr, fun o ho j hj => hdj o (hlg_in_rem o ho) j hj⟩
  have hlg_disj_msg : ∀ o ∈ logOwnedIvls sd lg,
      ∀ ec ∈ evmChain sd, Disj (memW sd (ec.1 + 112), 176) o := by
    intro o ho ec hec
    rw [hsd_ch] at hec
    exact (hrem_disj o (hlg_in_rem o ho)).2.2.2 ec hec
  have hcall_none : (evaluateHOLFiniteState sd callProg).1 = none := by rw [hcall_res]
  have hstep_call := call_log_append_step_fc hAsd hInvsd
    hlog_arg hlg_wa hlg_ok_sd hlg_pw hlg_disj_fo hlg_disj_ht hlg_disj_fix hlg_avoids hlg_disj_msg
    hcall_none
  have hs1_def : (evaluateHOLFiniteState sd callProg).2 = s1 := by rw [hcall_res]
  rw [hs1_def] at hstep_call
  obtain ⟨hAs1, hInvs1, hs1_loc, hs1_be, hs1_gk, hs1_hp, hs1_ch, hs1_R, hs1_fix, hs1_ht,
    hs1_cells, hs1_logs, hs1_tail_fo, hs1_head_fo, hs1_unhit, hs1_av, hs1_e16⟩ := hstep_call
  have hs1_nonHeap : ∀ g : String, ofString g ≠ ofString "heap_ptr" →
      globN s1 g = globN sd g := fun g hne =>
    InitECandidate.Solver.Wave8Contracts.M08.globN_eq_of_lookup
      (hs1_gk (ofString g) (by simp [hne]))
  let s1_aux : PanSemStateFiniteExact 64 F :=
    { s1 with locals := s_init.locals, clock := s1.clock }
  have hAs1_aux : ArenaReady s1_aux :=
    ⟨guestInv_congr (s := s1) rfl rfl rfl rfl hAs1.1, hAs1.2⟩
  have hInvs1_aux : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt s1_aux S :=
    (evmInvAt_lc_s5c s1 s_init.locals s1.clock S).mpr hInvs1
  have hch_aux : evmChain s1_aux = evmChain sd_aux :=
    (evmChain_lc_fc s1 s_init.locals s1.clock).trans
      (hs1_ch.trans (evmChain_lc_fc sd s_init.locals sd.clock).symm)
  have hR_aux : OpDispatchSpec.evmR s1_aux = OpDispatchSpec.evmR sd_aux :=
    (evmR_lc_fc s1 s_init.locals s1.clock).trans
      (hs1_R.trans (evmR_lc_fc sd s_init.locals sd.clock).symm)
  have hcells_aux : ∀ ec ∈ evmChain sd_aux, frameScratch s1_aux ec = frameScratch sd_aux ec ∧
      memW s1_aux (ec.1 + 24) = memW sd_aux (ec.1 + 24) ∧
      memW s1_aux (ec.1 + 32) = memW sd_aux (ec.1 + 32) ∧
      memW s1_aux (ec.1 + 40) = memW sd_aux (ec.1 + 40) ∧
      memW s1_aux (ec.1 + 112) = memW sd_aux (ec.1 + 112) ∧
      memW s1_aux (ec.2 + 56) = memW sd_aux (ec.2 + 56) := by
    intro ec hec
    rw [evmChain_lc_fc sd s_init.locals sd.clock] at hec
    exact hs1_cells ec hec
  have hlogs_aux : ∀ ec ∈ evmChain sd_aux,
      frameLogs s1_aux ec = frameLogs sd_aux ec ∨
        Inside (frameLogs s1_aux ec) sourceBase (globN s1_aux "heap_ptr") := by
    intro ec hec
    rw [evmChain_lc_fc sd s_init.locals sd.clock] at hec
    exact hs1_logs ec hec
  have hBS_s1_aux : FcBranchState s0 s1_aux S :=
    fcBranchState_of_log_step_fc hBS_sd_aux hAs1_aux hInvs1_aux hs1_hp hch_aux hR_aux rfl
      (hs1_nonHeap "ev" (by decide)) hs1_fix hs1_ht hcells_aux hlogs_aux
  have hhead_sd : (globN sd "ev", globN sd "cur_cont") ∈ evmChain sd := by
    rw [evmChain_cons]; exact List.mem_cons_self
  have hl0_in_fo : (memW sd (globN sd "ev" + 88), 24) ∈
      frameObjects sd (globN sd "ev", globN sd "cur_cont") := by simp [frameObjects]
  have hfl_in_fo : frameLogs sd (globN sd "ev", globN sd "cur_cont") ∈
      frameObjects sd (globN sd "ev", globN sd "cur_cont") := by simp [frameObjects]
  have hse_lt : scratchEnd < 2 ^ 64 := by rw [R11Shards.scratchEnd_val]; decide
  have hsep_hs : heapLimit ≤ scratchStart := by decide
  have hdom_s1 : s1.memaddrs = sd.memaddrs := hAs1.1.memaddrs.trans hAsd.1.memaddrs.symm
  -- Head frame (globN sd "ev", 280) unhit across log_append:
  have he_lt : globN sd "ev" + 280 < 2 ^ 64 := by
    have hFW := hInvsd.2.2.2.2.1 _ hhead_sd
    exact lt_of_le_of_lt (hFW.1 (globN sd "ev", 280) (by simp)).1.2 hse_lt
  have hpw_fo : (frameObjects sd (globN sd "ev", globN sd "cur_cont")).Pairwise Disj := by
    have hpw := hInvsd.2.2.2.2.2.2.2.1
    rw [evmChain_cons, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw
    exact hpw.1
  have hu_ev : InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit sd s1 (globN sd "ev", 280) := by
    have hpw_fo' := hpw_fo
    unfold frameObjects at hpw_fo'
    have hrest := (List.pairwise_cons.1 hpw_fo').1
    exact hs1_unhit (globN sd "ev", 280) he_lt
      (Or.inr ((hInvsd.2.2.2.2.1 _ hhead_sd).1 (globN sd "ev", 280) (by simp)).1)
      (hrest _ (by simp)) (hrest _ (by simp))
  have he_wok := (ev_head_facts_s5c hAsd hInvsd).2.1
  have hev_88_s1 : memW s1 (globN s1 "ev" + 88) = memW sd (globN sd "ev" + 88) := by
    rw [hs1_nonHeap "ev" (by decide)]
    exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_ev
      (by have := he_wok.1; omega) (le_of_lt he_lt)
      ⟨by dsimp only; omega, by dsimp only; omega⟩
  have hev_232_s1 : memW s1 (globN s1 "ev" + 232) = memW sd (globN sd "ev" + 232) := by
    rw [hs1_nonHeap "ev" (by decide)]
    exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_ev
      (by have := he_wok.1; omega) (le_of_lt he_lt)
      ⟨by dsimp only; omega, by dsimp only; omega⟩
  -- Child frame (globN s0 "ev", 280) unhit across log_append:
  have hchild_lt : globN s0 "ev" + 280 < 2 ^ 64 := by
    have := hI.child_scr.1.2; dsimp only at this; omega
  have hchild_disj_fo_sd : ∀ ec ∈ evmChain sd, ∀ o ∈ frameObjects sd ec,
      Disj (globN s0 "ev", 280) o := by
    intro ec hec o ho
    rw [hsd_ch] at hec
    have ho' : o ∈ frameObjects s ec := ho
    exact hI.child_disj_fo ec hec o ho'
  have hchild_scr_sd : Inside (globN s0 "ev", 280) (globN sd "scratch_ptr") scratchEnd ∧
      WordsOK sd (globN s0 "ev", 280) := hI.child_scr
  have hu_child_s1 : InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit sd s1 (globN s0 "ev", 280) :=
    hs1_unhit (globN s0 "ev", 280) hchild_lt (Or.inr hchild_scr_sd.1)
      (hchild_disj_fo_sd _ hhead_sd _ hl0_in_fo)
      (hchild_disj_fo_sd _ hhead_sd _ hfl_in_fo)
  have hchild_wok_s1 : WordsOK s1 (globN s0 "ev", 280) :=
    unhit_wordsOK_s5c hdom_s1 (le_of_lt hchild_lt) hu_child_s1 hchild_scr_sd.2
  have hchild_96_s1 : memW s1 (globN s0 "ev" + 96) = memW s_init (globN s0 "ev" + 96) :=
    (InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_child_s1
      (by have := hI.child_scr.2.1; omega) (le_of_lt hchild_lt)
      ⟨by dsimp only; omega, by dsimp only; omega⟩).trans hI.child_96
  have hchild_136_s1 : memW s1 (globN s0 "ev" + 136) = memW s_init (globN s0 "ev" + 136) :=
    (InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_child_s1
      (by have := hI.child_scr.2.1; omega) (le_of_lt hchild_lt)
      ⟨by dsimp only; omega, by dsimp only; omega⟩).trans hI.child_136
  -- Child log array (p, 8 * cap_c) unhit across log_append:
  have harr_alloc_sd : Allocated sd (p, 8 * memW s_init (cl + 16)) := by
    rcases hPC_init.child_logs_arr_in with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
    · rw [hfl_init_def] at hlo hhi
      exact Or.inl ⟨hlo, le_trans hhi hI.hp_le⟩
    · rw [hfl_init_def] at hlo hhi
      have hsc_eq : globN sd "scratch_ptr" = globN s_init "scratch_ptr" :=
        hI.gk "scratch_ptr" (by decide)
      exact Or.inr ⟨by dsimp only at hlo ⊢; omega, hhi⟩
  have hu_arr_s1 : InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit sd s1
      (p, 8 * memW s_init (cl + 16)) :=
    hs1_unhit _ hfl_init_bnd harr_alloc_sd hI.arr_disj_head_logs.1 hI.arr_disj_head_logs.2
  have harr_wok_s1 : WordsOK s1 (p, 8 * memW s_init (cl + 16)) :=
    unhit_wordsOK_s5c hdom_s1 (le_of_lt hfl_init_bnd) hu_arr_s1 harr_wok
  -- Helper: any interval in `fo_old` or `logOwnedIvls sd lg` or `(p', 8*cap')`:
  obtain ⟨p', cap', hfl_s1_head, hp'_cases, hfo_s1_head⟩ := hs1_head_fo
  have hfo_sd_sub : ∀ o, o ∈
      ([(globN sd "ev", 280), (globN sd "cur_cont", 104),
        (memW sd (globN sd "ev" + 8), 32 * memW sd (globN sd "ev" + 232)),
        (memW sd (globN sd "ev" + 24), memW sd (globN sd "ev" + 40)),
        (memW sd (globN sd "ev" + 88), 24), (p', 8 * cap'),
        frameRet sd (globN sd "ev", globN sd "cur_cont")] ++
       frameLogObjects sd (globN sd "ev", globN sd "cur_cont") ++
       logOwnedIvls sd lg) →
      o ∈ frameObjects sd (globN sd "ev", globN sd "cur_cont") ∨
      o = (p', 8 * cap') ∨
      o ∈ logOwnedIvls sd lg := by
    intro o ho
    rcases List.mem_append.1 ho with ho1 | ho_lg
    · rcases List.mem_append.1 ho1 with ho_hdr | ho_flo
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho_hdr
        rcases ho_hdr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact Or.inl (by simp [frameObjects])
        · exact Or.inl (by simp [frameObjects])
        · exact Or.inl (by simp [frameObjects])
        · exact Or.inl (by simp [frameObjects])
        · exact Or.inl (by simp [frameObjects])
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl (by simp [frameObjects])
      · exact Or.inl (by unfold frameObjects; exact List.mem_append_right _ ho_flo)
    · exact Or.inr (Or.inr ho_lg)
  have hlg_in_heap : ∀ o ∈ logOwnedIvls sd lg,
      o.2 = 0 ∨ Inside o sourceBase (globN sd "heap_ptr") := by
    intro o ho
    have hmem_rec := (List.mem_filter.1 ho).1
    simp only [logRecordIvls, List.mem_cons, List.not_mem_nil, or_false] at hmem_rec
    rcases hmem_rec with rfl | rfl | rfl | rfl
    · exact Or.inr hlg_ok_sd.2.1
    · exact Or.inr hlg_ok_sd.2.2.2.2.1
    · exact Or.inr hlg_ok_sd.2.2.2.2.2.1
    · exact Or.inr hlg_ok_sd.2.2.2.2.2.2
  have hchild_disj_fo_s1 : ∀ ec ∈ evmChain s1, ∀ o ∈ frameObjects s1 ec,
      Disj (globN s0 "ev", 280) o := by
    intro ec hec o ho
    rw [hs1_ch, evmChain_cons] at hec
    rcases List.mem_cons.1 hec with rfl | htl
    · rw [hfo_s1_head] at ho
      rcases hfo_sd_sub o ho with ho_old | rfl | ho_lg
      · exact hchild_disj_fo_sd _ hhead_sd o ho_old
      · rcases hp'_cases with heq | hfresh
        · rw [heq]; exact hchild_disj_fo_sd _ hhead_sd _ hfl_in_fo
        · have hd := disj_fresh_of_zero_or_allocated_s5c hAsd.2 hAs1.2 hs1_hp
            (Or.inr (Or.inr hchild_scr_sd.1))
          exact disj_sub_right_s5c hd hfresh.1
            (by have := hfresh.2; dsimp only at this ⊢; omega)
      · rcases hlg_in_heap o ho_lg with h0 | hin_h
        · exact Or.inr (Or.inl h0)
        · have hsep : heapLimit ≤ scratchStart := by decide
          have hh_lim := hAsd.2.2.1
          have hss_fm := hAsd.2.2.2.1
          have hsc_lo := hAsd.2.2.2.2.1
          have hch_lo : globN sd "scratch_ptr" ≤ globN s0 "ev" := hchild_scr_sd.1.1
          have ho_hi : o.1 + o.2 ≤ globN sd "heap_ptr" := hin_h.2
          exact Or.inr (Or.inr (Or.inr (by dsimp only; omega)))
    · rw [hs1_tail_fo ec htl] at ho
      exact hchild_disj_fo_sd ec (List.mem_of_mem_tail htl) o ho
  have harr_disj_head_logs_s1 :
      Disj (p, 8 * memW s_init (cl + 16)) (memW s1 (globN s1 "ev" + 88), 24) ∧
      Disj (p, 8 * memW s_init (cl + 16)) (frameLogs s1 (globN s1 "ev", globN s1 "cur_cont")) := by
    refine ⟨by rw [hev_88_s1]; exact hI.arr_disj_head_logs.1, ?_⟩
    rw [hs1_nonHeap "ev" (by decide), hs1_nonHeap "cur_cont" (by decide), hfl_s1_head]
    rcases hp'_cases with heq | hfresh
    · rw [heq]; exact hI.arr_disj_head_logs.2
    · have hd := disj_fresh_of_zero_or_allocated_s5c hAsd.2 hAs1.2 hs1_hp (Or.inr harr_alloc_sd)
      exact disj_sub_right_s5c hd hfresh.1
        (by have := hfresh.2; dsimp only at this ⊢; omega)
  -- Remaining logs j ≥ idx + 1 across log_append:
  have hrem_logs_s1 : ∀ j : Nat, idx + 1 ≤ j → j < n →
      memW s1 (p + 8 * j) = memW s_init (p + 8 * j) ∧
      LogEntryOK s1 (memW s_init (p + 8 * j)) ∧
      logOwnedIvls s1 (memW s_init (p + 8 * j)) =
        logOwnedIvls s_init (memW s_init (p + 8 * j)) := by
    intro j hj_lo hj_lt
    obtain ⟨hmw_j, hok_j, hown_j⟩ := hrem_logs j (by omega) hj_lt
    have hmw_j_s1 : memW s1 (p + 8 * j) = memW s_init (p + 8 * j) :=
      (InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_arr_s1
        (by have := harr_wok.1; omega) (le_of_lt hfl_init_bnd)
        ⟨by dsimp only; omega, by dsimp only; omega⟩).trans hmw_j
    set lg_j := memW s_init (p + 8 * j)
    have hlg_j_in_tail : (lg_j, 40) ∈ (List.range (n - (idx + 1))).flatMap
        (fun k => logOwnedIvls s_init (memW s_init (p + 8 * (idx + 1 + k)))) := by
      refine List.mem_flatMap.2 ⟨j - (idx + 1), List.mem_range.2 (by omega), ?_⟩
      rw [show idx + 1 + (j - (idx + 1)) = j by omega]
      have hvmsa_ne : (lg_j, 40) ≠ (globN s_init "vm_system_address", 20) := by
        intro heq; have h2 := congrArg Prod.snd heq; dsimp only at h2; omega
      exact List.mem_filter.2 ⟨by simp [logRecordIvls, lg_j], bne_iff_ne.2 hvmsa_ne⟩
    have hlg_j_in_rem : (lg_j, 40) ∈ (List.range (n - idx)).flatMap
        (fun k => logOwnedIvls s_init (memW s_init (p + 8 * (idx + k)))) := by
      rw [hrange_split]; exact List.mem_append_right _ hlg_j_in_tail
    have hok_j_sd : LogEntryOK sd lg_j := hok_j
    have hlg_j_lt : lg_j + 40 < 2 ^ 64 := by
      have hh := hAsd.2.2.1
      have hhl : heapLimit < 2 ^ 64 := by rw [R11Shards.heapLimit_val]; decide
      have hin := hok_j_sd.2.1.2
      dsimp only [lg_j] at hin ⊢
      omega
    have hu_lg_j : InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit sd s1 (lg_j, 40) := by
      have hhead_s : (globN sd "ev", globN sd "cur_cont") ∈ evmChain s := hsd_ch ▸ hhead_sd
      have hl0_in_fo_s : (memW sd (globN sd "ev" + 88), 24) ∈
          frameObjects s (globN sd "ev", globN sd "cur_cont") := by
        rw [← frameObjects_lc_s5c s s.locals (s.clock - 1)]; exact hl0_in_fo
      have hfl_in_fo_s : frameLogs sd (globN sd "ev", globN sd "cur_cont") ∈
          frameObjects s (globN sd "ev", globN sd "cur_cont") := by
        rw [← frameObjects_lc_s5c s s.locals (s.clock - 1)]; exact hfl_in_fo
      exact hs1_unhit (lg_j, 40) hlg_j_lt (Or.inl hok_j_sd.2.1)
        ((hrem_disj _ hlg_j_in_rem).1 _ hhead_s _ hl0_in_fo_s)
        ((hrem_disj _ hlg_j_in_rem).1 _ hhead_s _ hfl_in_fo_s)
    have hwords_j : ∀ off ∈ ([0, 8, 16, 24, 32] : List Nat),
        memW s1 (lg_j + off) = memW sd (lg_j + off) := by
      intro off hoff
      have ho : off + 8 ≤ 40 ∧ off % 8 = 0 := by revert off hoff; decide
      exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_lg_j
        (by have := hok_j.1.1; omega) (le_of_lt hlg_j_lt) ⟨by dsimp only; omega, by dsimp only; omega⟩
    have hok_j_s1 : LogEntryOK s1 lg_j :=
      logEntryOK_transport_fc hok_j hdom_s1 hs1_hp hwords_j
    have hown_j_s1 : logOwnedIvls s1 lg_j = logOwnedIvls s_init lg_j :=
      (logOwnedIvls_transport_fc (hs1_nonHeap "vm_system_address" (by decide)) hwords_j).trans hown_j
    exact ⟨hmw_j_s1, hok_j_s1, hown_j_s1⟩
  have hrem_av_s1 : AvoidsTries s1 S ((List.range (n - (idx + 1))).flatMap
      (fun j => logOwnedIvls s_init (memW s_init (p + 8 * (idx + 1 + j))))) := by
    apply hs1_av
    obtain ⟨Nd, hTr, hdj⟩ := hrem_av
    exact ⟨Nd, hTr, fun o ho j hj => hdj o (by rw [hrange_split]; exact List.mem_append_right _ ho) j hj⟩
  have hrem_disj_s1 : ∀ o ∈ (List.range (n - (idx + 1))).flatMap
        (fun j => logOwnedIvls s_init (memW s_init (p + 8 * (idx + 1 + j)))),
      (∀ ec ∈ evmChain s1, ∀ o2 ∈ frameObjects s1 ec, Disj o o2) ∧
      (∀ t ∈ S, ∀ ht ∈ htabFootprint s1 t, Disj o ht) ∧
      (∀ fx ∈ fixedObjects s1, Disj o fx) ∧
      (∀ ec ∈ evmChain s1, Disj (memW s1 (ec.1 + 112), 176) o) := by
    intro o ho_tail
    have ho_rem : o ∈ (List.range (n - idx)).flatMap
        (fun j => logOwnedIvls s_init (memW s_init (p + 8 * (idx + j)))) := by
      rw [hrange_split]; exact List.mem_append_right _ ho_tail
    obtain ⟨hd_fo, hd_ht, hd_fix, hd_msg⟩ := hrem_disj o ho_rem
    -- Also show o is zero-len or allocated in sd (since o ∈ logOwnedIvls s_init lg_j and LogEntryOK sd lg_j)
    obtain ⟨k, hk_r, ho_k⟩ := List.mem_flatMap.1 ho_tail
    have hk_lt : idx + 1 + k < n := by have := List.mem_range.1 hk_r; omega
    obtain ⟨_, hok_k, hown_k⟩ := hrem_logs (idx + 1 + k) (by omega) hk_lt
    have ho_k_s : o ∈ logOwnedIvls s (memW s_init (p + 8 * (idx + 1 + k))) := hown_k ▸ ho_k
    have hok_k_sd : LogEntryOK sd (memW s_init (p + 8 * (idx + 1 + k))) := hok_k
    have ho_alloc_sd : o.2 = 0 ∨ Allocated sd o := by
      have hmem_rec : o ∈ logRecordIvls sd (memW s_init (p + 8 * (idx + 1 + k))) :=
        (List.mem_filter.1 ho_k_s).1
      simp only [logRecordIvls, List.mem_cons, List.not_mem_nil, or_false] at hmem_rec
      rcases hmem_rec with rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inl hok_k_sd.2.1)
      · exact Or.inr (Or.inl hok_k_sd.2.2.2.2.1)
      · exact Or.inr (Or.inl hok_k_sd.2.2.2.2.2.1)
      · exact Or.inr (Or.inl hok_k_sd.2.2.2.2.2.2)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro ec hec o2 ho2
      rw [hs1_ch, evmChain_cons] at hec
      have hhead_s : (globN sd "ev", globN sd "cur_cont") ∈ evmChain s := hsd_ch ▸ hhead_sd
      rcases List.mem_cons.1 hec with rfl | htl
      · rw [hfo_s1_head] at ho2
        rcases hfo_sd_sub o2 ho2 with ho_old | rfl | ho_lg
        · have ho_old' : o2 ∈ frameObjects s (globN sd "ev", globN sd "cur_cont") := ho_old
          exact hd_fo _ hhead_s o2 ho_old'
        · rcases hp'_cases with heq | hfresh
          · rw [heq]
            have hfl_in_fo_s : frameLogs sd (globN sd "ev", globN sd "cur_cont") ∈
                frameObjects s (globN sd "ev", globN sd "cur_cont") := hfl_in_fo
            exact hd_fo _ hhead_s _ hfl_in_fo_s
          · have hd := disj_fresh_of_zero_or_allocated_s5c hAsd.2 hAs1.2 hs1_hp ho_alloc_sd
            exact disj_sub_right_s5c hd hfresh.1
              (by have := hfresh.2; dsimp only at this ⊢; omega)
        · rw [hlg_own_sd] at ho_lg
          exact disj_symm_s5c (hlg_disj_tail o2 ho_lg o ho_tail)
      · rw [hs1_tail_fo ec htl] at ho2
        have ho2' : o2 ∈ frameObjects s ec := ho2
        exact hd_fo ec (hsd_ch ▸ List.mem_of_mem_tail htl) o2 ho2'
    · intro t ht j hj; rw [hs1_ht t ht] at hj; exact hd_ht t ht j hj
    · intro fx hfx; rw [hs1_fix] at hfx; exact hd_fix fx hfx
    · intro ec hec
      rw [hs1_ch] at hec
      rw [(hs1_cells ec hec).2.2.2.2.1]
      exact hd_msg ec (hsd_ch ▸ hec)
  -- Now evaluate `assignProg`: `i = i + 1` on `s1`!
  have hi_s1 : s1.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 idx))) := by
    rw [hs1_loc]; exact hi_lk
  have hadd_i : BitVec.ofNat 64 idx + BitVec.ofNat 64 1 = BitVec.ofNat 64 (idx + 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show idx < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show (1 : Nat) < 2 ^ 64 by decide),
      Nat.mod_eq_of_lt (show idx + 1 < 2 ^ 64 by omega)]
  have hasgn_eq : evaluateHOLFiniteState s1 assignProg =
      (none, setVarHOLFinite (ofString "i") (.val (.word (BitVec.ofNat 64 (idx + 1)))) s1) := by
    dsimp only [assignProg]
    rw [evaluateHOLFiniteState_assign]
    have hev_i : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
        (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)]) =
        some (.val (.word (BitVec.ofNat 64 (idx + 1)))) := by
      simp [evalHOLExact, evalListHOLExact, hi_s1, wordOpHOL, wordOp,
        valueIsWord, valueWord, hadd_i]
    have hval_i : s1.isValidValueHOLFinite .local (ofString "i")
        (.val (.word (BitVec.ofNat 64 (idx + 1)))) = true := by
      simp [isValidValueHOLFinite, lookupKvarHOLExact, hi_s1, shapeOfHOLExact, shapeEqHOL]
    simp only [hev_i, hval_i, ↓reduceIte, setKvarHOLFinite]
  have hbody_state : (evaluateHOLFiniteState sd (.seq callProg assignProg)).2 =
      setVarHOLFinite (ofString "i") (.val (.word (BitVec.ofNat 64 (idx + 1)))) s1 := by
    rw [hseq_eq]; dsimp only; rw [hcall_res]; dsimp only; rw [hasgn_eq]
  rw [hbody_state]
  let s2 := setVarHOLFinite (ofString "i") (.val (.word (BitVec.ofNat 64 (idx + 1)))) s1
  have hs2_ch : evmChain s2 = evmChain s1 :=
    evmChain_lc_fc s1 s2.locals s1.clock
  have hs2_R : OpDispatchSpec.evmR s2 = OpDispatchSpec.evmR s1 :=
    evmR_lc_fc s1 s2.locals s1.clock
  have hs2_bs : FcBranchState s0 { s2 with locals := s_init.locals, clock := s2.clock } S :=
    hBS_s1_aux
  have hs2_i : s2.locals.lookup (ofString "i") =
      some (.val (.word (BitVec.ofNat 64 (idx + 1)))) := by
    simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs2_p : s2.locals.lookup (ofString "p") =
      some (.val (.word (BitVec.ofNat 64 p))) := by
    have hne : ofString "i" ≠ ofString "p" := by decide
    have hp_sd : sd.locals.lookup (ofString "p") = some (.val (.word (BitVec.ofNat 64 p))) := hI.p_lk
    simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hs1_loc, hp_sd]
  have hs2_n : s2.locals.lookup (ofString "n") =
      some (.val (.word (BitVec.ofNat 64 n))) := by
    have hne : ofString "i" ≠ ofString "n" := by decide
    have hn_sd : sd.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 n))) := hI.n_lk
    simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hs1_loc, hn_sd]
  have hs2_child : s2.locals.lookup (ofString "child") =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "ev")))) := by
    have hne : ofString "i" ≠ ofString "child" := by decide
    have hch_sd : sd.locals.lookup (ofString "child") =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "ev")))) := hI.child_lk
    simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hs1_loc, hch_sd]
  have hev_s1 : globN s1 "ev" = globN sd "ev" := hs1_nonHeap "ev" (by decide)
  have hsc_s1 : globN s1 "scratch_ptr" = globN sd "scratch_ptr" := hs1_nonHeap "scratch_ptr" (by decide)
  have hchild_scr_s2 : Inside (globN s0 "ev", 280) (globN s2 "scratch_ptr") scratchEnd ∧
      WordsOK s2 (globN s0 "ev", 280) :=
    ⟨by change Inside _ (globN s1 "scratch_ptr") _; rw [hsc_s1]; exact hI.child_scr.1, hchild_wok_s1⟩
  have hchild_disj_fo_s2 : ∀ ec ∈ evmChain s2, ∀ o ∈ frameObjects s2 ec,
      Disj (globN s0 "ev", 280) o := by
    intro ec hec o ho
    rw [hs2_ch] at hec
    have ho' : o ∈ frameObjects s1 ec := ho
    exact hchild_disj_fo_s1 ec hec o ho'
  have hev_16_s2 : memW s2 (globN s2 "ev" + 16) = memW s_init (globN s_init "ev" + 16) := by
    change memW s1 (globN s1 "ev" + 16) = _; rw [hev_s1, hs1_e16]; exact hI.ev_16
  have hev_40_s2 : memW s2 (globN s2 "ev" + 40) = memW s_init (globN s_init "ev" + 40) := by
    change memW s1 (globN s1 "ev" + 40) = _; rw [hev_s1, (hs1_cells _ hhead_sd).2.2.2.1]; exact hI.ev_40
  have hgk_s2 : ∀ g : String, ofString g ≠ ofString "heap_ptr" → globN s2 g = globN s_init g :=
    fun g hne => (hs1_nonHeap g hne).trans (hI.gk g hne)
  have hrem_disj_s2 : ∀ o ∈ (List.range (n - (idx + 1))).flatMap
        (fun j => logOwnedIvls s_init (memW s_init (p + 8 * (idx + 1 + j)))),
      (∀ ec ∈ evmChain s2, ∀ o2 ∈ frameObjects s2 ec, Disj o o2) ∧
      (∀ t ∈ S, ∀ ht ∈ htabFootprint s2 t, Disj o ht) ∧
      (∀ fx ∈ fixedObjects s2, Disj o fx) ∧
      (∀ ec ∈ evmChain s2, Disj (memW s2 (ec.1 + 112), 176) o) := by
    intro o ho
    obtain ⟨h1, h2, h3, h4⟩ := hrem_disj_s1 o ho
    refine ⟨?_, h2, h3, ?_⟩
    · intro ec hec o2 ho2
      rw [hs2_ch] at hec
      have ho2' : o2 ∈ frameObjects s1 ec := ho2
      exact h1 ec hec o2 ho2'
    · intro ec hec
      rw [hs2_ch] at hec
      exact h4 ec hec
  have hidx_ex_s2 : ∃ idx' : Nat, idx' ≤ n ∧
      s2.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 idx'))) ∧
      WordsOK s2 (p, 8 * memW s_init (cl + 16)) ∧
      (∀ j : Nat, idx' ≤ j → j < n →
        memW s2 (p + 8 * j) = memW s_init (p + 8 * j) ∧
        LogEntryOK s2 (memW s_init (p + 8 * j)) ∧
        logOwnedIvls s2 (memW s_init (p + 8 * j)) =
          logOwnedIvls s_init (memW s_init (p + 8 * j))) ∧
      AvoidsTries s2 S ((List.range (n - idx')).flatMap
        (fun j => logOwnedIvls s_init (memW s_init (p + 8 * (idx' + j))))) ∧
      (∀ o ∈ (List.range (n - idx')).flatMap
          (fun j => logOwnedIvls s_init (memW s_init (p + 8 * (idx' + j)))),
        (∀ ec ∈ evmChain s2, ∀ o2 ∈ frameObjects s2 ec, Disj o o2) ∧
        (∀ t ∈ S, ∀ ht ∈ htabFootprint s2 t, Disj o ht) ∧
        (∀ fx ∈ fixedObjects s2, Disj o fx) ∧
        (∀ ec ∈ evmChain s2, Disj (memW s2 (ec.1 + 112), 176) o)) :=
    ⟨idx + 1, by omega, hs2_i, harr_wok_s1, hrem_logs_s1, hrem_av_s1, hrem_disj_s2⟩
  have hs1_R_s : OpDispatchSpec.evmR s1 = OpDispatchSpec.evmR s :=
    hs1_R.trans (evmR_lc_fc s s.locals (s.clock - 1))
  have hs1_ch_s : evmChain s1 = evmChain s :=
    hs1_ch.trans (evmChain_lc_fc s s.locals (s.clock - 1))
  exact FcLogLoopInv.mk hs2_bs hchild_scr_s2 hchild_disj_fo_s2 harr_disj_head_logs_s1
    hchild_96_s1 hchild_136_s1 hev_16_s2 hev_40_s2 (hev_88_s1.trans hI.ev_88)
    (hev_232_s1.trans hI.ev_232) (hs2_R.trans (hs1_R_s.trans hI.r_eq))
    (hs2_ch.trans (hs1_ch_s.trans hI.ch_eq))
    hgk_s2 (le_trans hI.hp_le hs1_hp) hs2_p hs2_n hs2_child hidx_ex_s2

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
