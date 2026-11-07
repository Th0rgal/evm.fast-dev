import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.FrameStartFinishChild

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8Contracts.M23 (EvmStep EvmKeeps EvmAvoids GlobalsKept)
open InitECandidate.Solver.Wave8GuestInv.R11Shards

private theorem resVarEq_update_self_fc {L : HolFiniteMapExact MlS (ValueHOL 64)}
    {nm : MlS} {v : ValueHOL 64} :
    HolFiniteMapExact.resVarEq (L.update (nm, v)) (nm, L.lookup nm) = L := by
  apply HolFiniteMapExact.ext
  funext k
  have h := PanRunBounded.resVarEq_lookup (L.update (nm, v)) nm k (L.lookup nm)
  change (HolFiniteMapExact.resVarEq (L.update (nm, v)) (nm, L.lookup nm)).lookup k = _ at h
  change (HolFiniteMapExact.resVarEq (L.update (nm, v)) (nm, L.lookup nm)).lookup k = L.lookup k
  rw [h]
  by_cases hk : k = nm
  · subst hk; simp
  · rw [if_neg hk, HolFiniteMapExact.lookup_update, FUPDATE]
    simp [Ne.symm hk]

theorem evmInvAt_of_head_payload_bre {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat} {buf : Ivl}
    (hAs : ArenaReady s)
    (hInv : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt s S)
    (heff : InitECandidate.Solver.Wave8Contracts.M23.ByteRegionEffect s post [buf])
    (hbuf : buf = (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232)) ∨
            buf = (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40)) ∨
            buf = frameRet s (globN s "ev", globN s "cur_cont")) :
    ArenaReady post ∧
    InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt post S ∧
    evmChain post = evmChain s ∧
    fixedObjects post = fixedObjects s ∧
    (∀ t ∈ S, htabFootprint post t = htabFootprint s t) ∧
    (∀ ec ∈ evmChain s, frameObjects post ec = frameObjects s ec ∧
      frameScratch post ec = frameScratch s ec ∧
      frameLogs post ec = frameLogs s ec ∧
      (∀ k, k + 8 ≤ 280 → k % 8 = 0 → memW post (ec.1 + k) = memW s (ec.1 + k)) ∧
      (∀ k, k + 8 ≤ 104 → k % 8 = 0 → memW post (ec.2 + k) = memW s (ec.2 + k))) ∧
    OpDispatchSpec.evmR post = OpDispatchSpec.evmR s := by
  obtain ⟨hW, hch_ne, hch_len, hch_last, hFW_all, hFR_all, hRW, hFO_pw, hFO_disj, hAT, hMarks, hRoles, hgas_s⟩ := hInv
  obtain ⟨Nd_at, hTr_at, hAT_at⟩ := hAT
  have hWT : InitECandidate.Solver.Wave8Contracts.M23.WorldTypedWith s S Nd_at :=
    ⟨hW.1, hW.2.1, hW.2.2.1, hTr_at⟩
  set e0 := globN s "ev"
  set c0 := globN s "cur_cont"
  have hch_cons : ∃ tl, evmChain s = (e0, c0) :: tl := ⟨_, rfl⟩
  obtain ⟨chTail, hch_eq⟩ := hch_cons
  have hhead_mem : (e0, c0) ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_self
  have hhead_FW := hFW_all _ hhead_mem
  have hdom_eq : post.memaddrs = s.memaddrs := heff.memaddrs
  have hglob : post.globals = s.globals := heff.globals
  have hglob_eq : ∀ nm, globN post nm = globN s nm := fun nm => by simp [globN, hglob]
  have hGp : GuestInv post :=
    guestInv_congr heff.code heff.memaddrs heff.shMemaddrs heff.baseAddr hAs.1
  have hApost : ArenaReady post := ⟨hGp, arenaOK_congr hglob hAs.2⟩
  have hh : globN s "heap_ptr" ≤ globN post "heap_ptr" := by rw [hglob_eq]
  have hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by rw [hglob_eq]
  have hbuf_fo : buf ∈ frameObjects s (e0, c0) := by
    rcases hbuf with rfl | rfl | rfl <;> simp [frameObjects]
  have hbuf_8 : buf.1 % 8 = 0 := by
    rcases hbuf with rfl | rfl | rfl
    · exact (hhead_FW.1 (memW s (e0 + 8), 32 * memW s (e0 + 232)) (by simp)).2.1
    · exact hhead_FW.2.2.1.1
    · rcases hhead_FW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with ⟨h216_0, _⟩ | ⟨_, hw_ret⟩
      · unfold frameRet; simp [h216_0]
      · exact hw_ret.1
  have hRl8_buf : ∀ x ∈ ([buf] : List Ivl), x.1 % 8 = 0 := by
    intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact hbuf_8
  have hbuf_disj_wti : ∀ i ∈ InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls s S Nd_at,
      i.2 = 0 ∨ Disj buf i := by
    intro i hi
    unfold InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls at hi
    simp only [List.mem_append] at hi
    rcases hi with ((((h1 | h2) | h3) | h4) | h5) | h6
    · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 h1
      exact Or.inr ((hFO_disj _ hhead_mem _ hbuf_fo).1 t ht i hfp)
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h2
      exact Or.inr ((hFO_disj _ hhead_mem _ hbuf_fo).2 _
        (InitECandidate.Solver.Wave8Contracts.M23.typedRec_in_fixedObjects s hr))
    · simp only [List.mem_singleton] at h3; subst h3
      have hfix_j : (if globN s "journal_cap" = 0 then 0 else globN s "journal",
          32 * globN s "journal_cap") ∈ fixedObjects s := by
        unfold fixedObjects
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp)))
      exact Or.inr ((hFO_disj _ hhead_mem _ hbuf_fo).2 _ hfix_j)
    · exact Or.inr ((hFO_disj _ hhead_mem _ hbuf_fo).2 _
        (InitECandidate.Solver.Wave8Contracts.M23.blockOut_in_fixedObjects h4))
    · exact Or.inr ((hFO_disj _ hhead_mem _ hbuf_fo).2 _
        (InitECandidate.Solver.Wave8Contracts.M23.bal_in_fixedObjects h5))
    · exact Or.inr (hAT_at _ (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨_, hhead_mem, rfl⟩, hbuf_fo⟩) i h6)
  have hcell : InitECandidate.Solver.Wave8Contracts.M23.SameTypedCells s post S Nd_at :=
    InitECandidate.Solver.Wave8Contracts.M23.ByteRegionEffect.sameTypedCells
      (Rl := []) (extra := [buf]) hAs.1.memaddrs hWT
      (fun _ h => by simp at h)
      (fun x hx => by simp at hx; subst hx; exact hbuf_disj_wti)
      (by simpa using heff)
  have hfeq := InitECandidate.Solver.Wave8Contracts.M23.fixedObjects_eq_of_nonHeapGlobalsKept
    hAs.2 hWT.1 hWT.2.2.1 hcell (fun name _ _ _ => by rw [hglob])
  have hFT_post := InitECandidate.Solver.Wave8Contracts.M23.fixedTyped_of_eq hApost hWT.2.2.1 hh hsc hfeq
  obtain ⟨hWT_post, _⟩ := InitECandidate.Solver.Wave8Contracts.M23.worldTypedWith_congr_w1 hAs hApost hh hsc
    (fun g _ => hglob_eq g) hcell hWT
    ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
  have hW_post : WorldTyped post S :=
    ⟨hWT_post.1, hWT_post.2.1, hWT_post.2.2.1, Nd_at, hWT_post.2.2.2⟩
  have hpw_head_tail :
      (frameObjects s (e0, c0)).Pairwise Disj ∧
      (∀ o1 ∈ frameObjects s (e0, c0),
        ∀ ec ∈ chTail, ∀ o2 ∈ frameObjects s ec, Disj o1 o2) := by
    have hpw := hFO_pw
    rw [hch_eq, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw
    refine ⟨hpw.1, fun o1 ho1 ec hec o2 ho2 => hpw.2.2 o1 ho1 o2 ?_⟩
    exact List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨ec, hec, rfl⟩, ho2⟩
  have hbuf_disj_head :
      Disj buf (e0, 280) ∧
      Disj buf (c0, 104) ∧
      Disj buf (memW s (e0 + 88), 24) ∧
      Disj buf (frameLogs s (e0, c0)) ∧
      (∀ o ∈ frameLogObjects s (e0, c0), Disj buf o) := by
    have hpw0 := hpw_head_tail.1
    unfold frameObjects at hpw0
    simp only [List.cons_append, List.nil_append, List.pairwise_cons] at hpw0
    obtain ⟨hp0, hp1, hp2, hp3, hp4, hp5, hp6, _⟩ := hpw0
    rcases hbuf with rfl | rfl | rfl
    · exact ⟨R11Shards.Disj.symm (hp0 _ (by simp)),
        R11Shards.Disj.symm (hp1 _ (by simp)),
        hp2 _ (by simp), hp2 _ (by simp),
        fun o ho => hp2 o (by simp [ho])⟩
    · exact ⟨R11Shards.Disj.symm (hp0 _ (by simp)),
        R11Shards.Disj.symm (hp1 _ (by simp)),
        hp3 _ (by simp), hp3 _ (by simp),
        fun o ho => hp3 o (by simp [ho])⟩
    · exact ⟨R11Shards.Disj.symm (hp0 _ (by simp)),
        R11Shards.Disj.symm (hp1 _ (by simp)),
        R11Shards.Disj.symm (hp4 _ (by simp)),
        R11Shards.Disj.symm (hp5 _ (by simp)),
        fun o ho => hp6 o ho⟩
  have hdisj_buf_nonpay : ∀ ec ∈ evmChain s,
      Disj buf (ec.1, 280) ∧
      Disj buf (ec.2, 104) ∧
      Disj buf (memW s (ec.1 + 88), 24) ∧
      Disj buf (frameLogs s ec) ∧
      (∀ i < memW s (memW s (ec.1 + 88) + 8),
        Disj buf (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40)) := by
    intro ec hec
    rw [hch_eq, List.mem_cons] at hec
    rcases hec with rfl | htail
    · refine ⟨hbuf_disj_head.1, hbuf_disj_head.2.1, hbuf_disj_head.2.2.1,
        hbuf_disj_head.2.2.2.1, fun i hi => hbuf_disj_head.2.2.2.2 _ ?_⟩
      unfold frameLogObjects; dsimp only
      exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, by
        unfold logOwnedIvls logRecordIvls; exact List.mem_filter.2 ⟨by simp, by simp⟩⟩
    · refine ⟨hpw_head_tail.2 _ hbuf_fo ec htail _ (by simp [frameObjects]),
        hpw_head_tail.2 _ hbuf_fo ec htail _ (by simp [frameObjects]),
        hpw_head_tail.2 _ hbuf_fo ec htail _ (by simp [frameObjects]),
        hpw_head_tail.2 _ hbuf_fo ec htail _ (by simp [frameObjects]),
        fun i hi => hpw_head_tail.2 _ hbuf_fo ec htail _ ?_⟩
      unfold frameObjects; apply List.mem_append_right
      unfold frameLogObjects; dsimp only
      exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, by
        unfold logOwnedIvls logRecordIvls; exact List.mem_filter.2 ⟨by simp, by simp⟩⟩
  have hrec_eq : ∀ ec ∈ evmChain s,
      (∀ k, k + 8 ≤ 280 → k % 8 = 0 → memW post (ec.1 + k) = memW s (ec.1 + k)) ∧
      (∀ k, k + 8 ≤ 104 → k % 8 = 0 → memW post (ec.2 + k) = memW s (ec.2 + k)) ∧
      (∀ k, k + 8 ≤ 24 → k % 8 = 0 → memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨hb_e, hb_c, hb_88, _⟩ := InitECandidate.Solver.Wave8Contracts.M23.frameWF_bounds hAs.2 hFW
    have he8 : ec.1 % 8 = 0 := (hFW.1 (ec.1, 280) (by simp)).2.1
    have hc8 : ec.2 % 8 = 0 := (hFW.1 (ec.2, 104) (by simp)).2.1
    have h88_8 : (memW s (ec.1 + 88)) % 8 = 0 := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).2.1
    obtain ⟨hd_e, hd_c, hd_88, _, _⟩ := hdisj_buf_nonpay ec hec
    exact ⟨fun k hk hk8 => R14Shards.OpHandlersA.memW_eq_of_disj_eff heff hRl8_buf hb_e he8 hk8 hk
        (fun x hx => by simp at hx; subst hx; exact hd_e),
      fun k hk hk8 => R14Shards.OpHandlersA.memW_eq_of_disj_eff heff hRl8_buf hb_c hc8 hk8 hk
        (fun x hx => by simp at hx; subst hx; exact hd_c),
      fun k hk hk8 => R14Shards.OpHandlersA.memW_eq_of_disj_eff heff hRl8_buf hb_88 h88_8 hk8 hk
        (fun x hx => by simp at hx; subst hx; exact hd_88)⟩
  have hchain_aux : ∀ (fuel e c : Nat),
      (∀ ec ∈ evmChainFrom s fuel e c, ec ∈ evmChain s) →
      evmChainFrom post fuel e c = evmChainFrom s fuel e c := by
    intro fuel; induction fuel with
    | zero => intros; rfl
    | succ fuel ih =>
      intro e c hsub
      have hec : (e, c) ∈ evmChain s := hsub (e, c) (by simp [evmChainFrom])
      obtain ⟨_, hc_eq, _⟩ := hrec_eq (e, c) hec
      have hc16 := hc_eq 16 (by omega) (by omega)
      have hc0 : memW post c = memW s c := by simpa using hc_eq 0 (by omega) (by omega)
      have hc8 := hc_eq 8 (by omega) (by omega)
      simp only [evmChainFrom, hc16, hc0, hc8]
      split
      · rfl
      · rename_i hne16
        rw [ih]; intro ec' hec'; exact hsub ec' (by simp [evmChainFrom, hne16, hec'])
  have hchain_eq : evmChain post = evmChain s := by
    unfold evmChain; rw [hglob_eq "ev", hglob_eq "cur_cont"]
    exact hchain_aux _ _ _ (fun _ h => h)
  have hframeLogs_eq : ∀ ec ∈ evmChain s, frameLogs post ec = frameLogs s ec := by
    intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    unfold frameLogs
    rw [he_eq 88 (by omega) (by omega),
        show memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) by simpa using h88_eq 0 (by omega) (by omega),
        h88_eq 16 (by omega) (by omega)]
  have hframeRet_eq : ∀ ec ∈ evmChain s, frameRet post ec = frameRet s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameRet
    rw [he_eq 216 (by omega) (by omega), he_eq 144 (by omega) (by omega)]
  have hlogs_congr : ∀ ec ∈ evmChain s,
      frameLogObjects post ec = frameLogObjects s ec ∧ LogsListOK post (memW post (ec.1 + 88)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨_, _, _, hfob⟩ := InitECandidate.Solver.Wave8Contracts.M23.frameWF_bounds hAs.2 hFW
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    obtain ⟨_, _, _, hd_fl, hd_lr⟩ := hdisj_buf_nonpay ec hec
    have hl0 : memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) := by
      simpa using h88_eq 0 (by omega) (by omega)
    have hl8 : memW post (memW s (ec.1 + 88) + 8) = memW s (memW s (ec.1 + 88) + 8) :=
      h88_eq 8 (by omega) (by omega)
    have hl16 : memW post (memW s (ec.1 + 88) + 16) = memW s (memW s (ec.1 + 88) + 16) :=
      h88_eq 16 (by omega) (by omega)
    have harr_eq : ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
        memW post (memW s (memW s (ec.1 + 88)) + 8 * i) = memW s (memW s (memW s (ec.1 + 88)) + 8 * i) := by
      intro i hi
      have hfl_in : frameLogs s ec ∈ frameObjects s ec := by simp [frameObjects]
      have hlen_le : memW s (memW s (ec.1 + 88) + 8) ≤ memW s (memW s (ec.1 + 88) + 16) :=
        hFW.2.2.2.2.2.2.2.2.2.2.2.1
      have hfl_b : (frameLogs s ec).1 + (frameLogs s ec).2 ≤ 2 ^ 64 := by
        rcases hfob _ hfl_in with h0 | hb
        · unfold frameLogs at h0; dsimp only at h0; omega
        · exact hb
      have hfl_8 : (memW s (memW s (ec.1 + 88))) % 8 = 0 := hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
      exact R14Shards.OpHandlersA.memW_eq_of_disj_eff heff hRl8_buf hfl_b hfl_8 (by omega)
        (by unfold frameLogs; dsimp only; omega)
        (fun x hx => by simp at hx; subst hx; exact hd_fl)
    have hlr_eq : ∀ i (hi : i < memW s (memW s (ec.1 + 88) + 8)) off, off + 8 ≤ 40 → off % 8 = 0 →
        memW post (memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + off) =
          memW s (memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + off) := by
      intro i hi off hoff hoff8
      have hlr_in : (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40) ∈ frameObjects s ec := by
        unfold frameObjects; apply List.mem_append_right
        unfold frameLogObjects; dsimp only
        exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, by
          unfold logOwnedIvls logRecordIvls; exact List.mem_filter.2 ⟨by simp, by simp⟩⟩
      have hlr_b : memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + 40 ≤ 2 ^ 64 := by
        rcases hfob _ hlr_in with h0 | hb
        · dsimp only at h0; omega
        · exact hb
      have hlr_8 : (memW s (memW s (memW s (ec.1 + 88)) + 8 * i)) % 8 = 0 := by
        rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨_, _, _, _, hent⟩
        · have he88_in := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).1.1
          have h1 := hAs.2.2.2.1; have h2 := hAs.2.2.2.2.1
          rw [R11Shards.scratchStart_val] at h1; dsimp only at he88_in; omega
        · exact (hent i hi).2.1.1
      exact R14Shards.OpHandlersA.memW_eq_of_disj_eff heff hRl8_buf hlr_b hlr_8 hoff8 hoff
        (fun x hx => by simp at hx; subst hx; exact hd_lr i hi)
    refine ⟨?_, ?_⟩
    · unfold frameLogObjects; dsimp only
      rw [he_eq 88 (by omega) (by omega), hl8]
      apply List.flatMap_congr; intro i hi; rw [List.mem_range] at hi
      rw [hl0, harr_eq i hi]
      have r0 := hlr_eq i hi 0 (by omega) (by omega)
      have r8 := hlr_eq i hi 8 (by omega) (by omega)
      have r16 := hlr_eq i hi 16 (by omega) (by omega)
      have r24 := hlr_eq i hi 24 (by omega) (by omega)
      have r32 := hlr_eq i hi 32 (by omega) (by omega)
      simp only [Nat.add_zero] at r0
      unfold logOwnedIvls logRecordIvls
      rw [r0, r8, r16, r24, r32, hglob_eq "vm_system_address"]
    · rw [he_eq 88 (by omega) (by omega)]
      rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨hw_l, hal_l, hlt28, hle_cap, hent⟩
      · exact Or.inl hz
      · right
        refine ⟨(R14Shards.OpHandlersA.wordsOK_congr_dom hdom_eq).2 hw_l,
          InitECandidate.Solver.Wave8Contracts.M23.allocated_mono hh hsc hal_l,
          by rw [hl8]; exact hlt28, by rw [hl8, hl16]; exact hle_cap, fun i hi => ?_⟩
        rw [hl8] at hi; rw [hl0]
        obtain ⟨hwa, hle⟩ := hent i hi
        refine ⟨(R14Shards.OpHandlersA.wordAt_congr_dom hdom_eq).2 hwa, ?_⟩
        rw [harr_eq i hi]
        have r0 := hlr_eq i hi 0 (by omega) (by omega)
        have r8 := hlr_eq i hi 8 (by omega) (by omega)
        have r16 := hlr_eq i hi 16 (by omega) (by omega)
        have r24 := hlr_eq i hi 24 (by omega) (by omega)
        have r32 := hlr_eq i hi 32 (by omega) (by omega)
        simp only [Nat.add_zero] at r0
        unfold LogEntryOK at hle ⊢
        rw [r0, r8, r16, r24, r32, hglob_eq "heap_ptr"]
        exact ⟨(R14Shards.OpHandlersA.wordsOK_congr_dom hdom_eq).2 hle.1, hle.2⟩
  have hframeObjects_eq : ∀ ec ∈ evmChain s, frameObjects post ec = frameObjects s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameObjects
    rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega),
        he_eq 24 (by omega) (by omega), he_eq 40 (by omega) (by omega),
        he_eq 88 (by omega) (by omega),
        hframeLogs_eq ec hec, hframeRet_eq ec hec, (hlogs_congr ec hec).1]
  have hframeScratch_eq : ∀ ec ∈ evmChain s, frameScratch post ec = frameScratch s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameScratch
    rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega),
        he_eq 88 (by omega) (by omega)]
  have hmap_fo_eq : (evmChain s).map (frameObjects post) = (evmChain s).map (frameObjects s) :=
    List.map_congr_left hframeObjects_eq
  have hframeRoleSlots_eq : frameRoleSlots post (evmChain s) = frameRoleSlots s (evmChain s) := by
    unfold frameRoleSlots; apply List.flatMap_congr; intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    rw [he_eq 136 (by omega) (by omega), he_eq 168 (by omega) (by omega),
        he_eq 176 (by omega) (by omega)]
  have hfp_eq_all : ∀ t ∈ S, htabFootprint post t = htabFootprint s t :=
    fun t ht => InitECandidate.Solver.Wave8Contracts.M23.htabFootprint_eq hcell ht (hWT.1.2.1 t ht).1
  have hsum_eq :
      ((evmChain s).map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)) =
        ((evmChain s).map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)) := by
    apply List.map_congr_left; intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    rw [he_eq 64 (by omega) (by omega), he_eq 192 (by omega) (by omega)]
  have hR_eq : OpDispatchSpec.evmR post = OpDispatchSpec.evmR s := by
    unfold OpDispatchSpec.evmR; rw [hchain_eq, hsum_eq]
  refine ⟨hApost, ?_, hchain_eq, hfeq, hfp_eq_all, ?_, hR_eq⟩
  · unfold InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt
    refine ⟨hW_post, ?_⟩
    dsimp only; rw [hchain_eq]
    refine ⟨hch_ne, hch_len, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨ec, hec, hk0⟩ := hch_last
      have hec_mem := List.mem_of_mem_getLast? hec
      exact ⟨ec, hec, by rw [(hrec_eq ec hec_mem).2.1 16 (by omega) (by omega)]; exact hk0⟩
    · intro ec hec
      obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
      obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, _, c17⟩ := hFW_all ec hec
      have hlo_ok := (hlogs_congr ec hec).2
      have hmsg_ok : MsgOwned post S (memW post (ec.1 + 112)) := by
        rw [he_eq 112 (by omega) (by omega)]
        obtain ⟨hal_m, hw_m, hdt, hdf, hdfo, Nd_m, hTr_m, hdj_m⟩ := c17
        obtain ⟨hTr_int, hsub_int⟩ := R11Shards.triesTypedWith_inter hTr_at hTr_m
        set Ndi := Nd_at.filter (fun n => decide (n ∈ Nd_m))
        have hcell_i : InitECandidate.Solver.Wave8Contracts.M23.SameTypedCells s post S Ndi := by
          have hwti_sub : ∀ i ∈ InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls s S Ndi,
              i ∈ InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls s S Nd_at := by
            intro i hi; unfold InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls at hi ⊢
            rcases List.mem_append.1 hi with hpre | hne
            · exact List.mem_append_left _ hpre
            · apply List.mem_append_right; unfold nodeExtents at hne ⊢
              obtain ⟨n, hn, hnx⟩ := List.mem_flatMap.1 hne
              exact List.mem_flatMap.2 ⟨n, (List.mem_filter.1 hn).1, hnx⟩
          refine ⟨hcell.1, hcell.2.1, hcell.2.2.1, hcell.2.2.2.1,
            fun a ha ha8 ⟨i, hi, h1, h2⟩ => hcell.2.2.2.2.1 a ha ha8 ⟨i, hwti_sub i hi, h1, h2⟩,
            fun b hb ⟨i, hi, h1, h2⟩ => hcell.2.2.2.2.2 b hb ⟨i, hwti_sub i hi, h1, h2⟩⟩
        obtain ⟨hWT_i_post, _⟩ := InitECandidate.Solver.Wave8Contracts.M23.worldTypedWith_congr_w1 hAs hApost hh hsc
          (fun g _ => hglob_eq g) hcell_i ⟨hWT.1, hWT.2.1, hWT.2.2.1, hTr_int⟩
          ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
        refine ⟨InitECandidate.Solver.Wave8Contracts.M23.allocated_mono hh hsc hal_m,
          (R14Shards.OpHandlersA.wordsOK_congr_dom hdom_eq).2 hw_m,
          fun t ht i hi => by rw [hfp_eq_all t ht] at hi; exact hdt t ht i hi,
          by rw [hfeq]; exact hdf,
          by rw [hchain_eq]; intro ec' hec' o ho; rw [hframeObjects_eq ec' hec'] at ho; exact hdfo ec' hec' o ho,
          Ndi, hWT_i_post.2.2.2, fun o ho j hj => ?_⟩
        rw [InitECandidate.Solver.Wave8Contracts.M23.nodeExtents_eq hTr_int.1 hcell_i] at hj
        exact hdj_m o ho j (hsub_int j hj).2
      unfold FrameWF; dsimp only
      rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega),
          he_eq 88 (by omega) (by omega), he_eq 24 (by omega) (by omega),
          he_eq 40 (by omega) (by omega), he_eq 16 (by omega) (by omega),
          he_eq 32 (by omega) (by omega), he_eq 136 (by omega) (by omega),
          he_eq 168 (by omega) (by omega), he_eq 176 (by omega) (by omega),
          h88_eq 16 (by omega) (by omega), h88_eq 8 (by omega) (by omega),
          hframeLogs_eq ec hec,
          he_eq 216 (by omega) (by omega), he_eq 144 (by omega) (by omega),
          hframeRet_eq ec hec,
          hglob_eq "scratch_ptr", hglob_eq "frame_mem_ptr", hglob_eq "heap_ptr", hglob_eq "evm_empty"]
      rw [he_eq 88 (by omega) (by omega)] at hlo_ok
      refine ⟨fun i hi => ⟨(c1 i hi).1, (R14Shards.OpHandlersA.wordsOK_congr_dom hdom_eq).2 (c1 i hi).2⟩,
        c2, (R14Shards.OpHandlersA.wordsOK_congr_dom hdom_eq).2 c3, c4, c5, c6, c7, c8, c9, c10, c11, c12,
        c13, (R14Shards.OpHandlersA.wordsOK_congr_dom hdom_eq).2 c14, ?_, hlo_ok, hmsg_ok⟩
      rcases c15 with h0 | ⟨hin, hw⟩
      · exact Or.inl h0
      · exact Or.inr ⟨hin, (R14Shards.OpHandlersA.wordsOK_congr_dom hdom_eq).2 hw⟩
    · intro ec hec
      have hec_mem : ec ∈ evmChain s := List.mem_of_mem_tail hec
      obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec_mem
      unfold FrameRoom
      rw [he_eq 16 (by omega) (by omega), he_eq 232 (by omega) (by omega)]
      exact hFR_all ec hec
    · intro i hi
      have hi0 : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
      have hi1 : (evmChain s)[i + 1] ∈ evmChain s := List.getElem_mem _
      rw [(hrec_eq _ hi0).2.1 80 (by omega) (by omega),
          (hrec_eq _ hi0).2.1 72 (by omega) (by omega),
          (hrec_eq _ hi1).1 40 (by omega) (by omega)]
      exact hRW i hi
    · rw [hmap_fo_eq]; exact hFO_pw
    · intro ec hec o ho
      rw [hframeObjects_eq ec hec] at ho; rw [hfeq]
      exact ⟨fun t ht i hi => by rw [hfp_eq_all t ht] at hi; exact (hFO_disj ec hec o ho).1 t ht i hi,
        (hFO_disj ec hec o ho).2⟩
    · rw [hmap_fo_eq]
      refine ⟨Nd_at, hWT_post.2.2.2, fun o ho j hj => ?_⟩
      rw [InitECandidate.Solver.Wave8Contracts.M23.nodeExtents_eq hTr_at.1 hcell] at hj
      exact hAT_at o ho j hj
    · have hworldRefs_eq : worldTableRefs post S = worldTableRefs s S := by
        unfold worldTableRefs recordSlots
        rw [hglob_eq "ws", hglob_eq "bs", hglob_eq "ts",
            show globalTableRoots.map (globN post) = globalTableRoots.map (globN s) by
              simp only [globalTableRoots, List.map, hglob_eq],
            InitECandidate.Solver.Wave8Contracts.M23.balRecords_eq hWT.1 hcell (hglob_eq "bal_accounts"),
            hglob_eq "journal_n", hglob_eq "journal"]
        have hws_sl : (if globN s "ws" = 0 then [] else wsTableSlots.map fun k => memW post (globN s "ws" + k)) =
            (if globN s "ws" = 0 then [] else wsTableSlots.map fun k => memW s (globN s "ws" + k)) := by
          split; · rfl
          rename_i hnz; apply List.map_congr_left; intro k hk
          exact InitECandidate.Solver.Wave8Contracts.M23.memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 40) (by decide) hnz
            (by simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl <;> omega)
        have hbs_sl : (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW post (globN s "bs" + k)) =
            (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW s (globN s "bs" + k)) := by
          split; · rfl
          rename_i hnz; apply List.map_congr_left; intro k hk
          exact InitECandidate.Solver.Wave8Contracts.M23.memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 80) (by decide) hnz
            (by simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
        have hts_sl : (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW post (globN s "ts" + k)) =
            (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW s (globN s "ts" + k)) := by
          split; · rfl
          rename_i hnz; apply List.map_congr_left; intro k hk
          exact InitECandidate.Solver.Wave8Contracts.M23.memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 72) (by decide) hnz
            (by simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
        have hnest_bs : (if globN s "bs" ≠ 0 ∧ memW post (globN s "bs" + 32) ∈ S then htabValues post (memW post (globN s "bs" + 32)) else []) =
            (if globN s "bs" ≠ 0 ∧ memW s (globN s "bs" + 32) ∈ S then htabValues s (memW s (globN s "bs" + 32)) else []) := by
          by_cases hnz : globN s "bs" = 0
          · simp [hnz]
          · rw [InitECandidate.Solver.Wave8Contracts.M23.memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 80) (by decide) hnz (by omega)]
            by_cases hmS : memW s (globN s "bs" + 32) ∈ S
            · simp [hnz, hmS, InitECandidate.Solver.Wave8Contracts.M23.htabValues_eq hcell hmS (hWT.1.2.1 _ hmS).1]
            · simp [hnz, hmS]
        have hnest_ts : (if globN s "ts" ≠ 0 ∧ memW post (globN s "ts" + 32) ∈ S then htabValues post (memW post (globN s "ts" + 32)) else []) =
            (if globN s "ts" ≠ 0 ∧ memW s (globN s "ts" + 32) ∈ S then htabValues s (memW s (globN s "ts" + 32)) else []) := by
          by_cases hnz : globN s "ts" = 0
          · simp [hnz]
          · rw [InitECandidate.Solver.Wave8Contracts.M23.memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 72) (by decide) hnz (by omega)]
            by_cases hmS : memW s (globN s "ts" + 32) ∈ S
            · simp [hnz, hmS, InitECandidate.Solver.Wave8Contracts.M23.htabValues_eq hcell hmS (hWT.1.2.1 _ hmS).1]
            · simp [hnz, hmS]
        have hbal_fl : (balRecords s).flatMap (fun ad => [memW post ad, memW post (ad + 8)]) =
            (balRecords s).flatMap (fun ad => [memW s ad, memW s (ad + 8)]) := by
          apply List.flatMap_congr; intro ad had
          have had_mem := InitECandidate.Solver.Wave8Contracts.M23.balRecord_ivl_mem had
          rcases InitECandidate.Solver.Wave8Contracts.M23.fixedObject_le_2pow64 hAs.2 hWT.2.2.1
              (InitECandidate.Solver.Wave8Contracts.M23.bal_in_fixedObjects had_mem) with h0 | had_bnd
          · dsimp only at h0; omega
          · dsimp only at had_bnd
            have hwti_ad := InitECandidate.Solver.Wave8Contracts.M23.mem_worldTypedIvls_bal (S := S) (Nd := Nd_at) had_mem
            rw [InitECandidate.Solver.Wave8Contracts.M23.memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩,
                InitECandidate.Solver.Wave8Contracts.M23.memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩]
        have hjrn_mp : (List.range (globN s "journal_n")).map (fun k => memW post (globN s "journal" + 32 * k)) =
            (List.range (globN s "journal_n")).map (fun k => memW s (globN s "journal" + 32 * k)) := by
          apply List.map_congr_left; intro k hk; rw [List.mem_range] at hk
          have hjc_le := hWT.2.1.1
          have hjc_ne : globN s "journal_cap" ≠ 0 := by omega
          rcases hWT.2.1.2.2.1 with h0 | ⟨hal, _⟩
          · exact absurd h0 hjc_ne
          · have hbnd := InitECandidate.Solver.Wave8Contracts.M23.allocated_le_2pow64 hAs.2 hal; dsimp only at hbnd
            have hkle : 32 * k + 8 ≤ 32 * globN s "journal_cap" := by omega
            exact InitECandidate.Solver.Wave8Contracts.M23.memW_eq_of_cellHits hcell (by omega)
              (InitECandidate.Solver.Wave8Contracts.M23.mem_worldTypedIvls_journal (S := S) (Nd := Nd_at) hjc_ne)
              ⟨by dsimp only; omega, by dsimp only; omega⟩
        dsimp only
        rw [hglob_eq "bs", hglob_eq "ts", hws_sl, hbs_sl, hts_sl, hnest_bs, hnest_ts, hbal_fl, hjrn_mp]
      have hdelEx_iff : ∀ i t, DelExclusive post S (evmChain s) i t ↔ DelExclusive s S (evmChain s) i t := by
        intro i t; unfold DelExclusive; rw [hworldRefs_eq]
        refine and_congr Iff.rfl (forall_congr' fun j => forall_congr' fun hj =>
          forall_congr' fun k => imp_congr_right fun hk => ?_)
        have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
        have hk_ok : k + 8 ≤ 280 ∧ k % 8 = 0 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
        rw [(hrec_eq _ hj_mem).1 k hk_ok.1 hk_ok.2]
      intro i hi
      have hi_mem : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
      have hm_eq := (hrec_eq _ hi_mem).2.1 48 (by omega) (by omega)
      have hmm_eq := (hrec_eq _ hi_mem).2.1 56 (by omega) (by omega)
      have he24_eq := (hrec_eq _ hi_mem).1 24 (by omega) (by omega)
      have htake_eq : ((evmChain s).take (i + 1)).map (fun ec => memW post (ec.1 + 136)) =
          ((evmChain s).take (i + 1)).map (fun ec => memW s (ec.1 + 136)) := by
        apply List.map_congr_left; intro ec hec
        exact (hrec_eq ec (List.mem_of_mem_take hec)).1 136 (by omega) (by omega)
      have hM := hMarks i hi; dsimp only at hM ⊢
      rw [hm_eq, hmm_eq, he24_eq, hframeScratch_eq _ hi_mem, hfeq, htake_eq]
      obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := hM
      refine ⟨m1, m2, m3, m4, ?_, m6, m7, ?_, m9⟩
      · intro j hj hij
        have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
        rw [hframeScratch_eq _ hj_mem, hframeObjects_eq _ hj_mem, hframeLogs_eq _ hj_mem,
            (hrec_eq _ hj_mem).1 112 (by omega) (by omega)]
        exact m5 j hj hij
      · intro t ht
        rw [hfp_eq_all t ht, hdelEx_iff i t]; exact m8 t ht
    · have hcg : ∀ g ∈ InitECandidate.Solver.Wave8Contracts.M23.coreWorldGlobals,
          globN post g = globN s g := fun g _ => hglob_eq g
      rw [InitECandidate.Solver.Wave8Contracts.M23.worldRoleSlots_eq hAs.2 hWT.1 hWT.2.2.1 hcell hcg,
          hframeRoleSlots_eq,
          InitECandidate.Solver.Wave8Contracts.M23.journalRoleSlots_eq hAs.2 hWT.2.1 hWT.2.2.1 hcell hcg]
      unfold RolesOK at hRoles ⊢
      refine ⟨fun a ha => ?_, hRoles.2⟩
      obtain ⟨haS, hkl⟩ := hRoles.1 a ha
      have htb := ((hWT.1.2.1 a.1 haS).1.1 (a.1, 88) (by simp [htabFootprint])).1
      rw [InitECandidate.Solver.Wave8Contracts.M23.htab_hdr_eq hcell haS htb 0 (by omega)]
      exact ⟨haS, hkl⟩
    · rw [hsum_eq]; exact hgas_s
  · intro ec hec
    obtain ⟨he_eq, hc_eq, _⟩ := hrec_eq ec hec
    exact ⟨hframeObjects_eq ec hec, hframeScratch_eq ec hec, hframeLogs_eq ec hec, he_eq, hc_eq⟩

theorem fcBranchState_of_head_payload_bre {F : Type}
    {s0 s post : PanSemStateFiniteExact 64 F} {S : List Nat} {buf : Ivl}
    (h : FcBranchState s0 s S)
    (heff : InitECandidate.Solver.Wave8Contracts.M23.ByteRegionEffect s post [buf])
    (hloc : post.locals = s.locals)
    (hbuf : buf = (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232)) ∨
            buf = (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40)) ∨
            buf = frameRet s (globN s "ev", globN s "cur_cont")) :
    FcBranchState s0 post S ∧
    evmChain post = evmChain s ∧
    OpDispatchSpec.evmR post = OpDispatchSpec.evmR s ∧
    (∀ off, off + 8 ≤ 280 → off % 8 = 0 → memW post (globN s "ev" + off) = memW s (globN s "ev" + off)) := by
  obtain ⟨hAp, hIp, hch, hfix, htab, hframes, hRp⟩ :=
    evmInvAt_of_head_payload_bre h.arena h.inv heff hbuf
  have hhp : globN s "heap_ptr" ≤ globN post "heap_ptr" := by
    unfold globN; rw [heff.globals]
  have hRel := releaseReadyAt_transport h.release hhp hch
    (fun ec hec => (hframes ec hec).2.1)
    (fun ec hec => ⟨(hframes ec hec).2.2.2.1 24 (by omega) (by omega),
      (hframes ec hec).2.2.2.1 40 (by omega) (by omega)⟩)
    (fun ec hec => Or.inl (hframes ec hec).2.2.1)
    (fun ec hec => (hframes ec hec).2.2.2.1 112 (by omega) (by omega))
    (fun t ht => Or.inl (htab t ht)) hfix
  have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by simp [evmChain, evmChainFrom]
  refine ⟨⟨hAp, hIp, hRel, fcEntryLocals_congr_locals hloc h.locals_ok,
    hch.trans h.chain_eq, ?_, ?_, ?_, ?_⟩, hch, hRp, (hframes _ hhead_mem).2.2.2.1⟩
  · rw [hch]; exact h.length_eq
  · rw [hRp]; exact h.r_le
  · intro ec hec
    rw [hch] at hec
    obtain ⟨a, b, c, d⟩ := h.cells ec hec
    have hf := (hframes ec hec).2.2.2
    exact ⟨(hf.1 24 (by omega) (by omega)).trans a,
      (hf.1 32 (by omega) (by omega)).trans b,
      (hf.1 40 (by omega) (by omega)).trans c,
      (hf.2 56 (by omega) (by omega)).trans d⟩
  · have hev : globN post "ev" = globN s "ev" := by unfold globN; rw [heff.globals]
    exact hev.trans h.ev_eq

private theorem void_call_ne_returned_fc {F : Type}
    (s : PanSemStateFiniteExact 64 F) (fn : MlS) (args : List (ExpHOL 64)) (u : ValueHOL 64) :
    (evaluateHOLFiniteState s (.call (some (none, none)) fn args)).1 ≠ some (.returned u) :=
  call0_ne_returned_fc s fn args u

def FcStackPushStepW_sc : Prop :=
  ∀ {F : Type} {s0 st : PanSemStateFiniteExact 64 F} {S : List Nat},
    FcBranchState s0 st S →
    memW st (globN st "ev" + 16) + 1 ≤ memW st (globN st "ev" + 232) →
    ∀ (vExp : ExpHOL 64) (vv : ValueHOL 64),
    evalAt st vExp = some vv →
    shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact vv) = true →
    (evaluateHOLFiniteState st
      (.call (some (none, none)) (ofString "stack_push") [vExp])).1 ≠ some .timeOut →
    let prog : ProgHOL 64 := .call (some (none, none)) (ofString "stack_push") [vExp]
    (∀ u, (evaluateHOLFiniteState st prog).1 ≠ some (.returned u)) ∧
    ¬ OpDispatchSpec.IsEvmErr (evaluateHOLFiniteState st prog).1 ∧
    ((evaluateHOLFiniteState st prog).1 = none →
      let post := (evaluateHOLFiniteState st prog).2
      FcBranchState s0 post S ∧
      (∀ g : String, ofString g ≠ ofString "scratch_ptr" → globN post g = globN st g) ∧
      post.locals = st.locals ∧
      evmChain post = evmChain st ∧
      OpDispatchSpec.evmR post ≤ OpDispatchSpec.evmR st)

theorem fcStackPushStepW : FcStackPushStepW_sc := by
  intro F s0 st S hBS hroom vExp vv hvv hsh hnt
  dsimp only
  refine ⟨fun u => void_call_ne_returned_fc st (ofString "stack_push") [vExp] u, ?_⟩
  have hv_struct : ∃ vw0 vw1 vw2 vw3 : BitVec 64,
      vv = .rStruct [.val (.word vw0), .val (.word vw1), .val (.word vw2), .val (.word vw3)] := by
    rw [shapeEqHOL_eq_true] at hsh
    rcases vv with _ | fs | _
    · simp [shapeOfHOLExact] at hsh
    · simp only [shapeOfHOLExact, ShapeHOL.comb.injEq] at hsh
      rcases fs with _ | ⟨f0, _ | ⟨f1, _ | ⟨f2, _ | ⟨f3, _ | _⟩⟩⟩⟩
      · simp at hsh
      · simp at hsh
      · simp at hsh
      · simp at hsh
      · simp only [List.map, List.cons.injEq] at hsh
        obtain ⟨h0, h1, h2, h3, _⟩ := hsh
        rcases f0 with ⟨⟨w0⟩⟩ | _ | _ <;> simp [shapeOfHOLExact] at h0
        rcases f1 with ⟨⟨w1⟩⟩ | _ | _ <;> simp [shapeOfHOLExact] at h1
        rcases f2 with ⟨⟨w2⟩⟩ | _ | _ <;> simp [shapeOfHOLExact] at h2
        rcases f3 with ⟨⟨w3⟩⟩ | _ | _ <;> simp [shapeOfHOLExact] at h3
        exact ⟨w0, w1, w2, w3, rfl⟩
      · simp at hsh
    · simp [shapeOfHOLExact] at hsh
  obtain ⟨vw0, vw1, vw2, vw3, rfl⟩ := hv_struct
  have hhead_mem : (globN st "ev", globN st "cur_cont") ∈ evmChain st := by
    simp [evmChain, evmChainFrom]
  have hFW0 := hBS.inv.2.2.2.2.1 _ hhead_mem
  have hb_ev := (InitECandidate.Solver.Wave8Contracts.M23.frameWF_bounds hBS.arena.2 hFW0).1
  dsimp only at hb_ev
  have hev_pos : 0 < globN st "ev" := by
    obtain ⟨hin1, _⟩ := (hFW0.1 (globN st "ev", 280) (by simp)).1
    have h1 := hBS.arena.2.2.2.1; have h2 := hBS.arena.2.2.2.2.1
    rw [R11Shards.scratchStart_val] at h1; dsimp only at hin1; omega
  obtain ⟨evw, hevw, hevw_nat⟩ := InitECandidate.Solver.Wave8Contracts.M23.global_word_of_pos st "ev" hev_pos
  have hcode : st.code = originalRuntimeCode := hBS.arena.1.code
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  have hargs : evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a))
      [vExp] = some [.rStruct [.val (.word vw0), .val (.word vw1), .val (.word vw2), .val (.word vw3)]] := by
    unfold evalAt at hvv
    simp [evalListHOLFinite, evalListHOLExact, hvv]
  rw [hargs] at hnt ⊢; dsimp only at hnt ⊢
  have hlook : PanSemStateFiniteExact.lookupCodeHOLFinite st.code.lookup (ofString "stack_push")
      [.rStruct [.val (.word vw0), .val (.word vw1), .val (.word vw2), .val (.word vw3)]] =
      some (sourceFnBody Guest.Software.guestFn_stack_push,
        HolFiniteMapExact.empty.update (ofString "v",
          .rStruct [.val (.word vw0), .val (.word vw1), .val (.word vw2), .val (.word vw3)]), .one) := by
    rw [hcode]
    let varg : ValueHOL 64 := .rStruct [.val (.word vw0), .val (.word vw1), .val (.word vw2), .val (.word vw3)]
    have hraw : lookupCodeHOLExact originalRuntimeCode.lookup (ofString "stack_push") [varg] =
        some (sourceFnBody Guest.Software.guestFn_stack_push,
          (fun key => if key = ofString "v" then some varg else none), .one) := by
      have hsh4 : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact varg) = true := by
        rw [shapeEqHOL_eq_true]; simp [varg, shapeOfHOLExact]
      simp [lookupCodeHOLExact, R14Shards.OpHandlersA.lookup_stack_push, hsh4]
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite
    split
    · rename_i hmiss; rw [hraw] at hmiss; cases hmiss
    · rename_i fb fl fs hfound
      have heq := Option.some.inj (hfound.symm.trans hraw)
      obtain ⟨hfb, hrest⟩ := Prod.mk.inj heq
      obtain ⟨hfl, hfs⟩ := Prod.mk.inj hrest
      subst hfb hfl hfs
      apply congrArg (fun (loc : HolFiniteMapExact MlS (ValueHOL 64)) =>
        some (sourceFnBody Guest.Software.guestFn_stack_push, loc, ShapeHOL.one))
      apply HolFiniteMapExact.ext; funext key
      by_cases hk : key = ofString "v"
      · subst hk; simp [varg, HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty]
      · simp [hk, Ne.symm hk, HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty]
  rw [hlook] at hnt ⊢; dsimp only at hnt ⊢
  by_cases hclk0 : st.clock = 0
  · rw [if_pos hclk0] at hnt; exact absurd rfl hnt
  · rw [if_neg hclk0] at hnt ⊢
    set ce := callEntryStateHOLFinite st (HolFiniteMapExact.empty.update (ofString "v",
      .rStruct [.val (.word vw0), .val (.word vw1), .val (.word vw2), .val (.word vw3)])) with hce_def
    let growBranch : ProgHOL 64 :=
      .seq
        (.ite (.cmp .notLower (.var .local (ofString "cap")) (.const 1024#64))
          (.raise (ofString "EvmErr") (.const 3#64))
          .skip)
        (.dec (ofString "ncap") .one (.panop .mul [.var .local (ofString "cap"), .const 2#64])
          (.seq
            (.ite (.cmp .lower (.const 1024#64) (.var .local (ofString "ncap")))
              (.assign .local (ofString "ncap") (.const 1024#64))
              .skip)
            (.decCall (ofString "ns") .one (ofString "scratch_alloc")
              [.panop .mul [.var .local (ofString "ncap"), .const 32#64]]
              (.seq
                (.call (some (none, none)) (ofString "memcpy")
                  [.var .local (ofString "ns"),
                   .load .one (.op .add [.var .global (ofString "ev"), .const 8#64]),
                   .panop .mul [.var .local (ofString "sp"), .const 32#64]])
                (.seq
                  (.store (.op .add [.var .global (ofString "ev"), .const 8#64]) (.var .local (ofString "ns")))
                  (.store (.op .add [.var .global (ofString "ev"), .const 232#64]) (.var .local (ofString "ncap"))))))))
    let tailProg : ProgHOL 64 :=
      .seq
        (.ite (.cmp .equal (.var .local (ofString "sp")) (.const 1024#64))
          (.raise (ofString "EvmErr") (.const 3#64))
          .skip)
        (.seq
          (.store
            (.op .add
              [.load .one (.op .add [.var .global (ofString "ev"), .const 8#64]),
               .panop .mul [.var .local (ofString "sp"), .const 32#64]])
            (.var .local (ofString "v")))
          (.seq
            (.store (.op .add [.var .global (ofString "ev"), .const 16#64])
              (.op .add [.var .local (ofString "sp"), .const 1#64]))
            (.return (.const 0#64))))
    have hbody : sourceFnBody Guest.Software.guestFn_stack_push =
        .dec (ofString "sp") .one (.load .one (.op .add [.var .global (ofString "ev"), .const 16#64]))
          (.dec (ofString "cap") .one (.load .one (.op .add [.var .global (ofString "ev"), .const 232#64]))
            (.seq
              (.ite (.cmp .notLower (.var .local (ofString "sp")) (.var .local (ofString "cap")))
                growBranch
                .skip)
              tailProg)) := rfl
    rw [hbody] at hnt ⊢
    rw [evaluateHOLFiniteState_dec_total] at hnt ⊢; dsimp only at hnt ⊢
    rcases hload_sp : @evalHOLExact 64 F _ ce.toExact (fun a => Classical.propDecidable (ce.memaddrs a))
        (.load .one (.op .add [.var .global (ofString "ev"), .const 16#64])) with _ | vsp
    · dsimp only
      refine ⟨?_, fun h => by cases h⟩
      rintro ⟨_, h⟩; cases h
    · simp only [hload_sp] at hnt ⊢
      obtain ⟨spw, rfl, hspw_eq⟩ := R14Shards.OpHandlersA.evalAt_loadG_word ce "ev" 16#64 vsp hload_sp
      have h16_n : (16#64 : BitVec 64).toNat = 16 := rfl
      have hce_gm16 : memW ce (globN ce "ev" + 16) = memW st (globN st "ev" + 16) := rfl
      rw [h16_n, hce_gm16] at hspw_eq
      have hsh_sp : shapeEqHOL .one (shapeOfHOLExact (.val (.word spw))) = true := by
        simp [shapeEqHOL, shapeOfHOLExact]
      rw [if_pos hsh_sp] at hnt ⊢
      set s1 := setVarHOLFinite (ofString "sp") (.val (.word spw)) ce with hs1
      rw [evaluateHOLFiniteState_dec_total] at hnt ⊢; dsimp only at hnt ⊢
      rcases hload_cap : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
          (.load .one (.op .add [.var .global (ofString "ev"), .const 232#64])) with _ | vcap
      · dsimp only
        refine ⟨?_, fun h => by cases h⟩
        rintro ⟨_, h⟩; cases h
      · simp only [hload_cap] at hnt ⊢
        obtain ⟨capw, rfl, hcapw_eq⟩ := R14Shards.OpHandlersA.evalAt_loadG_word s1 "ev" 232#64 vcap hload_cap
        have h232_n : (232#64 : BitVec 64).toNat = 232 := rfl
        have hs1_gm232 : memW s1 (globN s1 "ev" + 232) = memW st (globN st "ev" + 232) := rfl
        rw [h232_n, hs1_gm232] at hcapw_eq
        have hsh_cap : shapeEqHOL .one (shapeOfHOLExact (.val (.word capw))) = true := by
          simp [shapeEqHOL, shapeOfHOLExact]
        rw [if_pos hsh_cap] at hnt ⊢
        set s2 := setVarHOLFinite (ofString "cap") (.val (.word capw)) s1 with hs2
        have hs2_sp : s2.locals.lookup (ofString "sp") = some (.val (.word spw)) := by
          simp [hs2, hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "cap" ≠ ofString "sp" by decide]
        have hs2_cap : s2.locals.lookup (ofString "cap") = some (.val (.word capw)) := by
          simp [hs2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hs2_v : s2.locals.lookup (ofString "v") =
            some (.rStruct [.val (.word vw0), .val (.word vw1), .val (.word vw2), .val (.word vw3)]) := by
          simp [hs2, hs1, hce_def, callEntryStateHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "cap" ≠ ofString "v" by decide, show ofString "sp" ≠ ofString "v" by decide]
        have hcap_le1024 : capw.toNat ≤ 1024 := by rw [hcapw_eq]; exact hFW0.2.2.2.2.2.1
        have hsp_lt_cap : ¬ (capw ≤ spw) := by
          rw [BitVec.le_def]; omega
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
        have hcmp_grow : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
            (.cmp .notLower (.var .local (ofString "sp")) (.var .local (ofString "cap"))) =
            some (.val (.word 0#64)) := by
          simp [evalHOLExact, hs2_sp, hs2_cap, Compiler.Encoders.Asm.wordCmpHOL, hsp_lt_cap]
        rw [hcmp_grow] at hnt ⊢
        have h0_eq : (0#64 : BitVec 64) = 0 := rfl
        simp only [h0_eq, ↓reduceIte, evaluateHOLFiniteState_skip] at hnt ⊢
        dsimp only [tailProg] at hnt ⊢
        have hsp_ne1024 : spw ≠ 1024#64 := by
          intro heq; subst heq
          have : (1024#64 : BitVec 64).toNat = 1024 := rfl
          omega
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
        have hcmp_1024 : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
            (.cmp .equal (.var .local (ofString "sp")) (.const 1024#64)) =
            some (.val (.word 0#64)) := by
          simp [evalHOLExact, hs2_sp, Compiler.Encoders.Asm.wordCmpHOL, hsp_ne1024]
        rw [hcmp_1024] at hnt ⊢
        simp only [h0_eq, ↓reduceIte, evaluateHOLFiniteState_skip] at hnt ⊢
        rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
        let hst_v_pair := s2.evaluateHOLFiniteState
            (.store
              (.op .add
                [.load .one (.op .add [.var .global (ofString "ev"), .const 8#64]),
                 .panop .mul [.var .local (ofString "sp"), .const 32#64]])
              (.var .local (ofString "v")))
        have hst_v : s2.evaluateHOLFiniteState
            (.store
              (.op .add
                [.load .one (.op .add [.var .global (ofString "ev"), .const 8#64]),
                 .panop .mul [.var .local (ofString "sp"), .const 32#64]])
              (.var .local (ofString "v"))) = hst_v_pair := rfl
        change ¬OpDispatchSpec.IsEvmErr _ ∧ _
        rw [hst_v] at hnt ⊢
        rcases hst_v_pair with ⟨rv_st, m1⟩
        dsimp only at hnt ⊢
        cases rv_st with
        | some res_v =>
          have herr := R14Shards.OpHandlersA.store_some_eq_error' hst_v; subst herr
          dsimp only
          refine ⟨?_, fun h => by cases h⟩
          rintro ⟨_, h⟩; cases h
        | none =>
          dsimp only at hnt ⊢
          have hs2_ev : s2.globals.lookup (ofString "ev") = some (.val (.word evw)) := hevw
          have hs2_ma : s2.memaddrs = ordinaryDomain := hBS.arena.1.memaddrs
          have hstk_ptr_bound : memW st (globN st "ev" + 8) + 32 * memW st (globN st "ev" + 232) ≤ 2 ^ 64 := by
            obtain ⟨_, hin2⟩ := (hFW0.1 (memW st (globN st "ev" + 8), 32 * memW st (globN st "ev" + 232)) (by simp)).1
            rw [R11Shards.scratchEnd_val] at hin2; dsimp only at hin2; omega
          have hd_v_stk := OpHandlers.ScratchByteEff.of_store_struct4
            (s := s2) (post := m1)
            (Rl := [(memW st (globN st "ev" + 8), 32 * memW st (globN st "ev" + 232))])
            hs2_ma hst_v
            (fun v hv => by
              change s2.locals.lookup (ofString "v") = some v at hv
              rw [hs2_v] at hv; injection hv with hv'
              exact ⟨vw0, vw1, vw2, vw3, hv'.symm⟩)
            (fun addr hdst => by
              have hmem_load8 : ∃ stkw : BitVec 64, s2.memory (evw + 8#64) = .word stkw ∧
                  addr = stkw + spw * 32#64 := by
                rcases hm8 : s2.memory (evw + 8#64) with ⟨stkw⟩
                refine ⟨stkw, rfl, ?_⟩
                simp [evalHOLExact, evalListHOLExact, hs2_ev, hs2_sp,
                  wordOpHOL, wordOp, panOpHOL, valueIsWord, valueWord, memLoadHOLExact, hm8] at hdst
                by_cases hdm8 : s2.memaddrs (evw + 8#64)
                · simp [hdm8, valueWord] at hdst; exact hdst.symm
                · simp [hdm8] at hdst
              obtain ⟨stkw, hm8, haddr_eq⟩ := hmem_load8
              have hev8_eq : evw + 8#64 = BitVec.ofNat 64 (globN st "ev" + 8) := by
                apply BitVec.eq_of_toNat_eq
                have : (8#64 : BitVec 64).toNat = 8 := rfl
                rw [BitVec.toNat_add, hevw_nat, this, BitVec.toNat_ofNat]
              have hstkw_nat : stkw.toNat = memW st (globN st "ev" + 8) := by
                have hs2_mem : s2.memory = st.memory := rfl
                rw [hs2_mem, hev8_eq] at hm8
                unfold memW; rw [hm8]
              have hsp32_nat : (spw * 32#64).toNat = 32 * spw.toNat := by
                have : (32#64 : BitVec 64).toNat = 32 := rfl
                rw [BitVec.toNat_mul, this, Nat.mod_eq_of_lt (by omega)]; omega
              have haddr_nat : addr.toNat = memW st (globN st "ev" + 8) + 32 * spw.toNat := by
                rw [haddr_eq, BitVec.toNat_add, hstkw_nat, hsp32_nat, Nat.mod_eq_of_lt (by omega)]
              exact ⟨by omega, ⟨(memW st (globN st "ev" + 8), 32 * memW st (globN st "ev" + 232)),
                by simp, by dsimp only; omega, by dsimp only; omega⟩⟩)
          obtain ⟨hsbe_v, hm1_loc, hm1_glob⟩ := hd_v_stk
          set m1s : PanSemStateFiniteExact 64 F := { m1 with locals := st.locals } with hm1s_def
          have hm1s_glob : m1s.globals = st.globals := hm1_glob
          have hbre_m1s : InitECandidate.Solver.Wave8Contracts.M23.ByteRegionEffect st m1s
              [(memW st (globN st "ev" + 8), 32 * memW st (globN st "ev" + 232))] :=
            ⟨hsbe_v.code, hsbe_v.memaddrs, hsbe_v.shMemaddrs, hsbe_v.baseAddr, hsbe_v.be,
             hm1s_glob, hsbe_v.out_dom, hsbe_v.cell_frame, hsbe_v.byte_frame⟩
          obtain ⟨hBS_m1s, hch_m1s, hR_m1s, he0_m1s⟩ :=
            fcBranchState_of_head_payload_bre hBS hbre_m1s rfl (Or.inl rfl)
          rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
          let hst_sp_pair := m1.evaluateHOLFiniteState
              (.store (.op .add [.var .global (ofString "ev"), .const 16#64])
                (.op .add [.var .local (ofString "sp"), .const 1#64]))
          have hst_sp : m1.evaluateHOLFiniteState
              (.store (.op .add [.var .global (ofString "ev"), .const 16#64])
                (.op .add [.var .local (ofString "sp"), .const 1#64])) = hst_sp_pair := rfl
          rw [hst_sp] at hnt ⊢
          rcases hst_sp_pair with ⟨rsp_st, m2⟩
          dsimp only at hnt ⊢
          cases rsp_st with
          | some res_sp =>
            have herr := R14Shards.OpHandlersA.store_some_eq_error' hst_sp; subst herr
            dsimp only
            refine ⟨?_, fun h => by cases h⟩
            rintro ⟨_, h⟩; cases h
          | none =>
            dsimp only at hnt ⊢
            have hm1_ev : m1.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
              rw [hm1_glob]; exact hs2_ev
            have hm1_sp : m1.locals.lookup (ofString "sp") = some (.val (.word spw)) := by
              rw [hm1_loc]; exact hs2_sp
            obtain ⟨w_sp1, hw_sp1_ev, hm2_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := m1) (post := m2)
              (gname := "ev") (gbase := globN st "ev") (off := 16) hm1_ev hevw_nat (by omega)
              (fun v hv => by
                simp [evalHOLExact, evalListHOLExact, hm1_sp, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
                exact ⟨_, hv.symm⟩) hst_sp
            have hw_sp1_val : w_sp1 = spw + 1#64 := by
              simp [evalHOLExact, evalListHOLExact, hm1_sp, wordOpHOL, wordOp, valueIsWord, valueWord] at hw_sp1_ev
              exact hw_sp1_ev.symm
            subst hw_sp1_val
            rw [evaluateHOLFiniteState_return] at hnt ⊢
            have hc0_m2 : @evalHOLExact 64 F _ m2.toExact (fun a => Classical.propDecidable (m2.memaddrs a)) (ExpHOL.const 0) =
                some (.val (.word 0#64)) := rfl
            rw [hc0_m2] at hnt ⊢; dsimp only at hnt ⊢
            have hsz0 : sizeOfShapeWithContextHOL m2.structs
                (shapeOfHOLExact (.val (.word 0#64))) ≤ 32 := by
              simp [shapeOfHOLExact]
            rw [if_pos hsz0] at hnt ⊢
            dsimp only
            have hsh_ret : shapeEqHOL (shapeOfHOLExact (.val (.word 0#64) : ValueHOL 64)) .one = true := by
              simp [shapeOfHOLExact, shapeEqHOL]
            rw [if_pos hsh_ret]
            dsimp only
            refine ⟨?_, fun _ => ?_⟩
            · rintro ⟨_, h⟩; cases h
            · let postC : PanSemStateFiniteExact 64 F :=
                { m2.emptyLocalsHOLFinite with locals := st.locals }
              change FcBranchState s0 postC S ∧ _
              have hm1s_ev_eq : globN m1s "ev" = globN st "ev" := by unfold globN; rw [hm1s_glob]
              have hpost_glob : postC.globals = m1s.globals := by
                simp [postC, emptyLocalsHOLFinite, hm2_eq, hm1s_def]
              have hpostC_mem : postC.memory = R14Shards.OpHandlersA.updW m1s.memory (BitVec.ofNat 64 (globN m1s "ev" + 16)) (spw + 1#64) := by
                rw [hm1s_ev_eq]
                simp [postC, emptyLocalsHOLFinite, hm2_eq, hm1s_def]
              have hGp_postC : GuestInv postC :=
                guestInv_congr (s := m1s)
                  (by simp [postC, emptyLocalsHOLFinite, hm2_eq, hm1s_def])
                  (by simp [postC, emptyLocalsHOLFinite, hm2_eq, hm1s_def])
                  (by simp [postC, emptyLocalsHOLFinite, hm2_eq, hm1s_def])
                  (by simp [postC, emptyLocalsHOLFinite, hm2_eq, hm1s_def])
                  hBS_m1s.arena.1
              have hmem_out : ∀ x : BitVec 64,
                  (∀ off ∈ headSimpleOffs, x ≠ BitVec.ofNat 64 (globN m1s "ev" + off)) →
                  postC.memory x = m1s.memory x := by
                intro x hx
                rw [hpostC_mem]
                have hx16 : x ≠ BitVec.ofNat 64 (globN m1s "ev" + 16) := hx 16 (by decide)
                simp [R14Shards.OpHandlersA.updW, hx16]
              have hpostC_16 : memW postC (globN m1s "ev" + 16) = spw.toNat + 1 := by
                unfold memW; rw [hpostC_mem]
                simp only [R14Shards.OpHandlersA.updW, ↓reduceIte]
                have : (1#64 : BitVec 64).toNat = 1 := rfl
                rw [BitVec.toNat_add, this, Nat.mod_eq_of_lt (by omega)]
              have hpostC_64 : memW postC (globN m1s "ev" + 64) = memW m1s (globN m1s "ev" + 64) := by
                unfold memW; rw [hpostC_mem]
                have hne : BitVec.ofNat 64 (globN m1s "ev" + 64) ≠ BitVec.ofNat 64 (globN m1s "ev" + 16) := by
                  intro heq; have h := congrArg BitVec.toNat heq
                  rw [hm1s_ev_eq] at h; simp only [BitVec.toNat_ofNat] at h; omega
                simp [R14Shards.OpHandlersA.updW, hne]
              have hpostC_192 : memW postC (globN m1s "ev" + 192) = memW m1s (globN m1s "ev" + 192) := by
                unfold memW; rw [hpostC_mem]
                have hne : BitVec.ofNat 64 (globN m1s "ev" + 192) ≠ BitVec.ofNat 64 (globN m1s "ev" + 16) := by
                  intro heq; have h := congrArg BitVec.toNat heq
                  rw [hm1s_ev_eq] at h; simp only [BitVec.toNat_ofNat] at h; omega
                simp [R14Shards.OpHandlersA.updW, hne]
              have hm1s_232 : memW m1s (globN m1s "ev" + 232) = memW st (globN st "ev" + 232) := by
                rw [hm1s_ev_eq]; exact he0_m1s 232 (by omega) (by omega)
              have hR_m1s_decomp : OpDispatchSpec.evmR m1s =
                  memW m1s (globN m1s "ev" + 64) + memW m1s (globN m1s "ev" + 192) +
                    (((evmChain m1s).tail.map fun ec => memW m1s (ec.1 + 64) + memW m1s (ec.1 + 192)).sum) := by
                unfold OpDispatchSpec.evmR
                conv_lhs => rw [evmChain_cons]
                conv_rhs => rw [evmChain_cons]
                simp [Nat.add_assoc]
              have hgas_m1s := hBS_m1s.inv.2.2.2.2.2.2.2.2.2.2.2.2
              have hBS_postC : FcBranchState s0 postC S :=
                fcBranchState_of_head_simple hBS_m1s hGp_postC hpost_glob
                  (by simp [postC, emptyLocalsHOLFinite, hm2_eq, hm1s_def])
                  rfl hmem_out
                  (by rw [hpostC_16, hm1s_232]; omega)
                  (by rw [hpostC_64, hpostC_192]; simpa [evmChain_cons, Nat.add_assoc] using hgas_m1s)
                  (by rw [hpostC_64, hpostC_192, ← hR_m1s_decomp]; exact hBS_m1s.r_le)
              have hch_postC : evmChain postC = evmChain m1s :=
                (evmInvAt_of_head_simple hBS_m1s.arena hBS_m1s.inv hGp_postC hpost_glob
                  (by simp [postC, emptyLocalsHOLFinite, hm2_eq, hm1s_def])
                  hmem_out (by rw [hpostC_16, hm1s_232]; omega)
                  (by rw [hpostC_64, hpostC_192]; simpa [evmChain_cons, Nat.add_assoc] using hgas_m1s)).2.2.1
              have hR_postC : OpDispatchSpec.evmR postC = OpDispatchSpec.evmR m1s := by
                rw [(evmInvAt_of_head_simple hBS_m1s.arena hBS_m1s.inv hGp_postC hpost_glob
                  (by simp [postC, emptyLocalsHOLFinite, hm2_eq, hm1s_def])
                  hmem_out (by rw [hpostC_16, hm1s_232]; omega)
                  (by rw [hpostC_64, hpostC_192]; simpa [evmChain_cons, Nat.add_assoc] using hgas_m1s)).2.2.2.2.2.2,
                  hpostC_64, hpostC_192, ← hR_m1s_decomp]
              refine ⟨hBS_postC, fun g _ => ?_, rfl, hch_postC.trans hch_m1s, by rw [hR_postC, hR_m1s]⟩
              unfold globN; rw [hpost_glob, hm1s_glob]

private def addrCallees_fc (f : MlS) : Bool :=
  f == ofString "bswap64" || f == ofString "u256_from_be" || f == ofString "address_to_u256"

private theorem addrCallees_fc_good :
    ∀ f, addrCallees_fc f = true → ∀ values body callee rs,
      lookupCodeHOLFinite originalRuntimeCode.lookup f values =
        some (body, callee, rs) →
      StateRestoreEpilogue.noCatchableRaise addrCallees_fc body = true := by
  intro f hf values body callee rs hfound
  obtain ⟨params, rs', hinst⟩ := InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
  simp only [addrCallees_fc, Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with (rfl | rfl) | rfl
  · have hl := lookup_of_guestAst_getElem 23 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_bswap64) rfl
    change originalRuntimeCode.lookup (ofString "bswap64") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 86 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_u256_from_be) rfl
    change originalRuntimeCode.lookup (ofString "u256_from_be") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 445 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_address_to_u256) rfl
    change originalRuntimeCode.lookup (ofString "address_to_u256") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl

def FcAddrToU256StepW_sc : Prop :=
  ∀ {F : Type} {s0 st : PanSemStateFiniteExact 64 F} {S : List Nat},
    FcBranchState s0 st S →
    memW st (globN st "ev" + 16) + 1 ≤ memW st (globN st "ev" + 232) →
    ∀ (caExp : ExpHOL 64) (caw : BitVec 64),
    evalAt st caExp = some (.val (.word caw)) →
    (evaluateHOLFiniteState st
      (.decCall (ofString "av") (.comb [.one, .one, .one, .one]) (ofString "address_to_u256")
        [caExp]
        (.call (some (none, none)) (ofString "stack_push") [.var .local (ofString "av")]))).1 ≠
      some .timeOut →
    let prog : ProgHOL 64 :=
      .decCall (ofString "av") (.comb [.one, .one, .one, .one]) (ofString "address_to_u256")
        [caExp]
        (.call (some (none, none)) (ofString "stack_push") [.var .local (ofString "av")])
    (∀ u, (evaluateHOLFiniteState st prog).1 ≠ some (.returned u)) ∧
    ¬ OpDispatchSpec.IsEvmErr (evaluateHOLFiniteState st prog).1 ∧
    ((evaluateHOLFiniteState st prog).1 = none →
      let post := (evaluateHOLFiniteState st prog).2
      FcBranchState s0 post S ∧
      (∀ g : String, ofString g ≠ ofString "scratch_ptr" → globN post g = globN st g) ∧
      post.locals = st.locals ∧
      evmChain post = evmChain st ∧
      OpDispatchSpec.evmR post ≤ OpDispatchSpec.evmR st)

theorem fcAddrToU256StepW : FcAddrToU256StepW_sc := by
  intro F s0 st S hBS hroom caExp caw hca hnt
  dsimp only
  have hret_addr : ∀ u, (evaluateHOLFiniteState st
      (.decCall (ofString "av") (.comb [.one, .one, .one, .one]) (ofString "address_to_u256")
        [caExp]
        (.call (some (none, none)) (ofString "stack_push") [.var .local (ofString "av")]))).1 ≠
      some (.returned u) :=
    decCall_ne_returned_fc (fun t u => void_call_ne_returned_fc t (ofString "stack_push") _ u) st
  refine ⟨hret_addr, ?_⟩
  have hcode : st.code = originalRuntimeCode := hBS.arena.1.code
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  have hargs : evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a))
      [caExp] = some [.val (.word caw)] := by
    unfold evalAt at hca
    simp [evalListHOLFinite, evalListHOLExact, hca]
  rw [hargs] at hnt ⊢; dsimp only at hnt ⊢
  have hlk_inst : originalRuntimeCode.lookup (ofString "address_to_u256") =
      some ([(ofString "a", .one)], sourceFnBody Guest.Software.guestFn_address_to_u256,
        .comb [.one, .one, .one, .one]) :=
    lookup_of_guestAst_getElem 445 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_address_to_u256) rfl
  have hlook : PanSemStateFiniteExact.lookupCodeHOLFinite st.code.lookup (ofString "address_to_u256") [.val (.word caw)] =
      some (sourceFnBody Guest.Software.guestFn_address_to_u256,
        HolFiniteMapExact.empty.update (ofString "a", .val (.word caw)),
        .comb [.one, .one, .one, .one]) := by
    rw [hcode]
    have hraw : lookupCodeHOLExact originalRuntimeCode.lookup (ofString "address_to_u256") [.val (.word caw)] =
        some (sourceFnBody Guest.Software.guestFn_address_to_u256,
          (fun key => if key = ofString "a" then some (.val (.word caw)) else none),
          .comb [.one, .one, .one, .one]) := by
      simp [lookupCodeHOLExact, hlk_inst, shapeOfHOLExact, shapeEqHOL]
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite
    split
    · rename_i hmiss; rw [hraw] at hmiss; cases hmiss
    · rename_i fb fl fs hfound
      have heq := Option.some.inj (hfound.symm.trans hraw)
      obtain ⟨hfb, hrest⟩ := Prod.mk.inj heq
      obtain ⟨hfl, hfs⟩ := Prod.mk.inj hrest
      subst hfb hfl hfs
      apply congrArg (fun (loc : HolFiniteMapExact MlS (ValueHOL 64)) =>
        some (sourceFnBody Guest.Software.guestFn_address_to_u256, loc,
          ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]))
      apply HolFiniteMapExact.ext; funext key
      by_cases hk : key = ofString "a"
      · subst hk; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty]
      · simp [hk, Ne.symm hk, HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty]
  rw [hlook] at hnt ⊢; dsimp only at hnt ⊢
  by_cases hclk0 : st.clock = 0
  · rw [if_pos hclk0] at hnt; exact absurd rfl hnt
  · rw [if_neg hclk0] at hnt ⊢
    set ce := callEntryStateHOLFinite st
      (HolFiniteMapExact.empty.update (ofString "a", .val (.word caw))) with hce_def
    have hce_code : ce.code = originalRuntimeCode := hcode
    have hncr_body := StateRestoreEpilogue.evaluate_noCatchableRaise addrCallees_fc addrCallees_fc_good
      (sourceFnBody Guest.Software.guestFn_address_to_u256) rfl ce hce_code
    have hro_body := R14Shards.OpHandlersA.evaluate_readOnlyProg R14Shards.OpHandlersA.opRoCallees
      R14Shards.OpHandlersA.opRoCallees_good
      (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_address_to_u256).body) rfl ce hce_code
    let hb_pair := ce.evaluateHOLFiniteState (sourceFnBody Guest.Software.guestFn_address_to_u256)
    have hb : ce.evaluateHOLFiniteState (sourceFnBody Guest.Software.guestFn_address_to_u256) = hb_pair := rfl
    rw [hb] at hnt ⊢
    rcases hb_pair with ⟨br, bs⟩
    dsimp only at hnt ⊢
    cases br with
    | none =>
      refine ⟨?_, fun h => by cases h⟩
      rintro ⟨_, h⟩; cases h
    | some r =>
      cases r with
      | timeOut => exact absurd rfl hnt
      | error | «break» | «continue» | finalFfi _ =>
        refine ⟨?_, fun h => by cases h⟩
        rintro ⟨_, h⟩; cases h
      | exception eid ev =>
        refine ⟨?_, fun h => by cases h⟩
        rintro ⟨v, hv⟩
        injection hv with hv'
        rcases PanSemResultExact.exception.inj hv' with ⟨heid, rfl⟩
        exact hncr_body (ofString "EvmErr") ev (by decide) (by rw [hb, heid])
      | returned rv =>
        dsimp only at hnt ⊢
        by_cases hsh_rv : (shapeEqHOL (shapeOfHOLExact rv) (.comb [.one, .one, .one, .one]) &&
            shapeEqHOL (shapeOfHOLExact rv) (.comb [.one, .one, .one, .one])) = true
        · rw [if_pos hsh_rv] at hnt ⊢
          have hsh1 : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact rv) = true := by
            have h1 := (Bool.and_eq_true _ _).mp hsh_rv |>.1
            rw [shapeEqHOL_eq_true] at h1 ⊢
            exact h1.symm
          have hlf : R14Shards.OpHandlersA.LocFrame ce bs := by
            have h : R14Shards.OpHandlersA.LocFrame ce
                (evaluateHOLFiniteState ce (sourceFnBody Guest.Software.guestFn_address_to_u256)).2 :=
              hro_body.to_resumes (by
                show InitECandidate.Solver.Wave8Contracts.M23.Resumes
                  (evaluateHOLFiniteState ce (sourceFnBody Guest.Software.guestFn_address_to_u256)).1
                rw [hb]; exact Or.inl ⟨rv, rfl⟩)
            rw [hb] at h; exact h
          set mid := setVarHOLFinite (ofString "av") rv { bs with locals := st.locals } with hmid_def
          have hmid_eq : mid = { st with locals := st.locals.update (ofString "av", rv), clock := bs.clock } := by
            dsimp only [R14Shards.OpHandlersA.LocFrame] at hlf
            rw [hmid_def, setVarHOLFinite, hlf, hce_def, callEntryStateHOLFinite]
          have hloc_mid : FcEntryLocals s0 { st with locals := st.locals.update (ofString "av", rv), clock := bs.clock } := by
            obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11⟩ := hBS.locals_ok
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "av" ≠ ofString "rec" by decide, l1]
            · simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "av" ≠ ofString "child" by decide, l2]
            · simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "av" ≠ ofString "parent" by decide, l3]
            · simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "av" ≠ ofString "kind" by decide, l4]
            · simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "av" ≠ ofString "msg" by decide, l5]
            · simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "av" ≠ ofString "new_account_charged" by decide, l6]
            · simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "av" ≠ ofString "child_mark" by decide, l7]
            · simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "av" ≠ ofString "child_mem_mark" by decide, l8]
            · simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "av" ≠ ofString "out_start" by decide, l9]
            · simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "av" ≠ ofString "out_size" by decide, l10]
            · simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "av" ≠ ofString "contract_address" by decide, l11]
          have hBS_mid : FcBranchState s0 mid S := by
            rw [hmid_eq]
            exact fcBranchState_congr_locals_clock _ _ hBS hloc_mid
          have hroom_mid : memW mid (globN mid "ev" + 16) + 1 ≤ memW mid (globN mid "ev" + 232) := by
            rw [hmid_eq]; exact hroom
          have hav_eval : evalAt mid (.var .local (ofString "av")) = some rv := by
            rw [hmid_eq]; simp [evalAt, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE]
          have hnt_sp : (evaluateHOLFiniteState mid
              (.call (some (none, none)) (ofString "stack_push") [.var .local (ofString "av")])).1 ≠
              some .timeOut := by
            intro ht; rw [ht] at hnt; exact hnt rfl
          obtain ⟨_, hnoerr_sp, hok_sp⟩ :=
            fcStackPushStepW hBS_mid hroom_mid (.var .local (ofString "av")) rv hav_eval hsh1 hnt_sp
          let hsp_pair := mid.evaluateHOLFiniteState
              (.call (some (none, none)) (ofString "stack_push") [.var .local (ofString "av")])
          have hsp_run : mid.evaluateHOLFiniteState
              (.call (some (none, none)) (ofString "stack_push") [.var .local (ofString "av")]) = hsp_pair := rfl
          rw [hsp_run] at hnoerr_sp hok_sp ⊢
          rcases hsp_pair with ⟨spr, sps⟩
          dsimp only at hnoerr_sp hok_sp ⊢
          refine ⟨hnoerr_sp, fun hspr_none => ?_⟩
          obtain ⟨hBS_sps, hglob_sps, hloc_sps, hch_sps, hR_sps⟩ := hok_sp hspr_none
          have hres_loc : HolFiniteMapExact.resVarEq sps.locals (ofString "av", st.locals.lookup (ofString "av")) = st.locals := by
            rw [hloc_sps, hmid_eq]
            exact resVarEq_update_self_fc
          have hBS_final : FcBranchState s0
              { sps with locals := HolFiniteMapExact.resVarEq sps.locals (ofString "av", st.locals.lookup (ofString "av")) } S :=
            fcBranchState_congr_locals_clock _ sps.clock hBS_sps
              (fcEntryLocals_congr_locals (s1 := st) (s2 := { sps with locals := _ }) hres_loc hBS.locals_ok)
          have hglob_final : ∀ g : String, ofString g ≠ ofString "scratch_ptr" →
              globN { sps with locals := HolFiniteMapExact.resVarEq sps.locals (ofString "av", st.locals.lookup (ofString "av")) } g =
                globN st g := by
            intro g hg
            have h1 : globN { sps with locals := HolFiniteMapExact.resVarEq sps.locals (ofString "av", st.locals.lookup (ofString "av")) } g =
                globN sps g := rfl
            have h2 : globN mid g = globN st g := by rw [hmid_eq]; rfl
            exact h1.trans ((hglob_sps g hg).trans h2)
          have hch_final : evmChain { sps with locals := HolFiniteMapExact.resVarEq sps.locals (ofString "av", st.locals.lookup (ofString "av")) } =
              evmChain st := by
            have h1 := evmChain_lc_fc sps (HolFiniteMapExact.resVarEq sps.locals (ofString "av", st.locals.lookup (ofString "av"))) sps.clock
            have h2 : evmChain mid = evmChain st := by rw [hmid_eq]; exact evmChain_lc_fc st _ _
            exact h1.trans (hch_sps.trans h2)
          have hR_final : OpDispatchSpec.evmR { sps with locals := HolFiniteMapExact.resVarEq sps.locals (ofString "av", st.locals.lookup (ofString "av")) } ≤
              OpDispatchSpec.evmR st := by
            have h1 := evmR_lc_fc sps (HolFiniteMapExact.resVarEq sps.locals (ofString "av", st.locals.lookup (ofString "av"))) sps.clock
            have h2 : OpDispatchSpec.evmR mid = OpDispatchSpec.evmR st := by rw [hmid_eq]; exact evmR_lc_fc st _ _
            rw [h1, ← h2]; exact hR_sps
          exact ⟨hBS_final, hglob_final, hres_loc, hch_final, hR_final⟩
        · rw [if_neg hsh_rv]
          refine ⟨?_, fun h => by cases h⟩
          rintro ⟨_, h⟩; cases h

def fcMinTail_sc : ProgHOL 64 :=
  .decCall (ofString "actual") .one (ofString "min")
    [.var .local (ofString "out_size"),
     .load .one (.op .add [.var .local (ofString "child"), .const 128#64])]
    (.ite (.cmp .notEqual (.var .local (ofString "actual")) (.const 0#64))
      (.call (some (none, none)) (ofString "memcpy")
        [.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]),
             .var .local (ofString "out_start")],
         .load .one (.op .add [.var .global (ofString "ev"), .const 144#64]),
         .var .local (ofString "actual")])
      .skip)

def FcMinTailStepW_sc : Prop :=
  ∀ {F : Type} {s0 st : PanSemStateFiniteExact 64 F} {S : List Nat},
    FcBranchState s0 st S →
    (out_win : memW s0 (globN s0 "cur_cont" + 80) = 0 ∨
      memW s0 (globN s0 "cur_cont" + 72) + memW s0 (globN s0 "cur_cont" + 80) ≤
        memW st (globN st "ev" + 40)) →
    (evaluateHOLFiniteState st fcMinTail_sc).1 ≠ some .timeOut →
    (∀ u, (evaluateHOLFiniteState st fcMinTail_sc).1 ≠ some (.returned u)) ∧
    ¬ OpDispatchSpec.IsEvmErr (evaluateHOLFiniteState st fcMinTail_sc).1 ∧
    ((evaluateHOLFiniteState st fcMinTail_sc).1 = none →
      let post := (evaluateHOLFiniteState st fcMinTail_sc).2
      FcBranchState s0 post S ∧
      post.locals = st.locals ∧
      post.globals = st.globals ∧
      evmChain post = evmChain st ∧
      OpDispatchSpec.evmR post ≤ OpDispatchSpec.evmR st)

theorem fcMinTailStepW : FcMinTailStepW_sc := by
  intro F s0 st S hBS out_win hnt
  have hret_min : ∀ u, (evaluateHOLFiniteState st fcMinTail_sc).1 ≠ some (.returned u) := by
    dsimp only [fcMinTail_sc]
    refine decCall_ne_returned_fc (p := .ite _ _ _) ?_ st
    intro F' t u'
    rw [evaluateHOLFiniteState_ite]
    cases @evalHOLExact 64 F' _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
        (.cmp .notEqual (.var .local (ofString "actual")) (.const 0#64)) with
    | none => simp
    | some vc =>
      cases vc with
      | val wl =>
        cases wl with
        | word w =>
          dsimp only
          split
          · simp [evaluateHOLFiniteState_skip]
          · exact void_call_ne_returned_fc t (ofString "memcpy") _ u'
      | _ => simp
  refine ⟨hret_min, ?_⟩
  dsimp only [fcMinTail_sc] at hnt ⊢
  have hcode : st.code = originalRuntimeCode := hBS.arena.1.code
  have hosz_lk := hBS.locals_ok.osz_lk
  have hos_lk := hBS.locals_ok.os_lk
  have hchild_lk := hBS.locals_ok.child_lk
  rcases hload_c128 : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
      (.load .one (.op .add [.var .local (ofString "child"), .const 128#64])) with _ | vc128
  · have hargs_none : evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a))
        [.var .local (ofString "out_size"),
         .load .one (.op .add [.var .local (ofString "child"), .const 128#64])] = none := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hosz_lk] at hload_c128 ⊢
      rw [hload_c128]
    rw [evaluateHOLFiniteState_decCall_args_none st _ _ _ _ _ hargs_none]
    refine ⟨?_, fun h => by cases h⟩
    rintro ⟨_, h⟩; cases h
  · have hargs_l : ∃ c128w : BitVec 64, vc128 = .val (.word c128w) := by
      simp [evalHOLExact, evalListHOLExact] at hload_c128
      rw [hchild_lk] at hload_c128
      simp [valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at hload_c128
      rcases hm : st.memory (BitVec.ofNat 64 (globN s0 "ev") + 128#64) with ⟨y⟩
      rw [hm] at hload_c128
      exact ⟨y, hload_c128.2.symm⟩
    obtain ⟨c128w, rfl⟩ := hargs_l
    set oszw : BitVec 64 := BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont" + 80)) with hoszw_def
    have hargs : evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a))
        [.var .local (ofString "out_size"),
         .load .one (.op .add [.var .local (ofString "child"), .const 128#64])] =
        some [.val (.word oszw), .val (.word c128w)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hosz_lk] at hload_c128 ⊢
      rw [hoszw_def] at *; rw [hload_c128]
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite, hargs] at hnt ⊢; dsimp only at hnt ⊢
    have hlook := pan_two_word_lookup st.code.lookup (ofString "min")
      (ofString "a") (ofString "b") (sourceFnBody Guest.Software.guestFn_min) oszw c128w
      (by decide) (by rw [hcode]; exact OpHandlersB.lookup_min_b)
    rw [hlook] at hnt ⊢; dsimp only at hnt ⊢
    by_cases hclk0 : st.clock = 0
    · rw [if_pos hclk0] at hnt; exact absurd rfl hnt
    · rw [if_neg hclk0] at hnt ⊢
      let cmap := (HolFiniteMapExact.empty.update (ofString "a", ValueHOL.val (.word oszw))).update
        (ofString "b", ValueHOL.val (.word c128w))
      set ce := callEntryStateHOLFinite st cmap with hce_def
      have hce_a : ce.locals.lookup (ofString "a") = some (.val (.word oszw)) := by
        simp [hce_def, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "b" ≠ ofString "a" by decide]
      have hce_b : ce.locals.lookup (ofString "b") = some (.val (.word c128w)) := by
        simp [hce_def, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      set actw : BitVec 64 := if oszw < c128w then oszw else c128w with hactw_def
      have hmin_run : ce.evaluateHOLFiniteState (sourceFnBody Guest.Software.guestFn_min) =
          (some (PanSemResultExact.returned (.val (.word actw))), ce.emptyLocalsHOLFinite) :=
        eval_min_body_exact ce hce_a hce_b
      rw [hmin_run] at hnt ⊢; dsimp only at hnt ⊢
      have hsh_act : (shapeEqHOL (shapeOfHOLExact (.val (.word actw) : ValueHOL 64)) .one &&
          shapeEqHOL (shapeOfHOLExact (.val (.word actw) : ValueHOL 64)) .one) = true := by
        simp [shapeOfHOLExact, shapeEqHOL]
      rw [if_pos hsh_act] at hnt ⊢
      set mid := setVarHOLFinite (ofString "actual") (.val (.word actw))
        { ce.emptyLocalsHOLFinite with locals := st.locals } with hmid_def
      have hmid_eq : mid = { st with locals := st.locals.update (ofString "actual", .val (.word actw)), clock := st.clock - 1 } := by
        rfl
      have hmid_act : mid.locals.lookup (ofString "actual") = some (.val (.word actw)) := by
        rw [hmid_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
      have hmid_os : mid.locals.lookup (ofString "out_start") =
          some (.val (.word (BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont" + 72))))) := by
        rw [hmid_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "actual" ≠ ofString "out_start" by decide, hos_lk]
      rw [evaluateHOLFiniteState_ite] at hnt ⊢
      have hcmp_act : @evalHOLExact 64 F _ mid.toExact (fun a => Classical.propDecidable (mid.memaddrs a))
          (.cmp .notEqual (.var .local (ofString "actual")) (.const 0#64)) =
          some (.val (.word (if actw ≠ 0#64 then 1 else 0))) := by
        simp [evalHOLExact, hmid_act, Compiler.Encoders.Asm.wordCmpHOL]
      rw [hcmp_act] at hnt ⊢; dsimp only at hnt ⊢
      by_cases hact0 : actw = 0#64
      · simp only [hact0, ne_eq, not_true_eq_false, ↓reduceIte, evaluateHOLFiniteState_skip] at hnt ⊢
        refine ⟨?_, fun _ => ?_⟩
        · rintro ⟨_, h⟩; cases h
        · have hres_loc : HolFiniteMapExact.resVarEq mid.locals (ofString "actual", st.locals.lookup (ofString "actual")) = st.locals := by
            rw [hmid_eq]; exact resVarEq_update_self_fc
          let post0 : PanSemStateFiniteExact 64 F :=
            { mid with locals := HolFiniteMapExact.resVarEq mid.locals (ofString "actual", st.locals.lookup (ofString "actual")) }
          change FcBranchState s0 post0 S ∧ post0.locals = st.locals ∧ post0.globals = st.globals ∧
            evmChain post0 = evmChain st ∧ OpDispatchSpec.evmR post0 ≤ OpDispatchSpec.evmR st
          have hpost0_eq : post0 = { st with clock := st.clock - 1 } := by
            dsimp only [post0]; rw [hres_loc, hmid_eq]
          rw [hpost0_eq]
          have hBS_post : FcBranchState s0 { st with clock := st.clock - 1 } S :=
            fcBranchState_congr_locals_clock st.locals (st.clock - 1) hBS
              (fcEntryLocals_congr_locals (s1 := st) (s2 := { st with clock := st.clock - 1 }) rfl hBS.locals_ok)
          have hch_post0 : evmChain { st with clock := st.clock - 1 } = evmChain st :=
            evmChain_lc_fc st st.locals (st.clock - 1)
          have hR_post0 : OpDispatchSpec.evmR { st with clock := st.clock - 1 } = OpDispatchSpec.evmR st :=
            evmR_lc_fc st st.locals (st.clock - 1)
          exact ⟨hBS_post, rfl, rfl, hch_post0, le_of_eq hR_post0⟩
      · have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
        simp only [hact0, ne_eq, not_false_eq_true, ↓reduceIte, h10] at hnt ⊢
        let dstExp : ExpHOL 64 := .op .add
          [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]),
           .var .local (ofString "out_start")]
        let srcExp : ExpHOL 64 := .load .one (.op .add [.var .global (ofString "ev"), .const 144#64])
        let nExp : ExpHOL 64 := .var .local (ofString "actual")
        rcases hload24 : @evalHOLExact 64 F _ mid.toExact (fun a => Classical.propDecidable (mid.memaddrs a))
            (.load .one (.op .add [.var .global (ofString "ev"), .const 24#64])) with _ | v24
        · have hargs_m_none : evalListHOLFinite mid (h := fun a => Classical.propDecidable (mid.memaddrs a))
              [dstExp, srcExp, nExp] = none := by
            simp [dstExp, evalListHOLFinite, evalListHOLExact, evalHOLExact] at hload24 ⊢
            rw [hload24]
          rw [evaluateHOLFiniteState_call, hargs_m_none]; dsimp only
          refine ⟨?_, fun h => by cases h⟩
          rintro ⟨_, h⟩; cases h
        · obtain ⟨w24, rfl, hw24_eq⟩ := R14Shards.OpHandlersA.evalAt_loadG_word mid "ev" 24#64 v24 hload24
          have h24_n : (24#64 : BitVec 64).toNat = 24 := rfl
          have hmid_gm24 : memW mid (globN mid "ev" + 24) = memW st (globN st "ev" + 24) := by rw [hmid_eq]; rfl
          rw [h24_n, hmid_gm24] at hw24_eq
          have hdst_ev0 : @evalHOLExact 64 F _ mid.toExact (fun a => Classical.propDecidable (mid.memaddrs a)) dstExp =
              some (.val (.word (w24 + BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont" + 72))))) := by
            have hos_ev : @evalHOLExact 64 F _ mid.toExact (fun a => Classical.propDecidable (mid.memaddrs a))
                (.var .local (ofString "out_start")) =
                some (.val (.word (BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont" + 72))))) := by
              simp [evalHOLExact, hmid_os]
            have hlist : @evalListHOLExact 64 F _ mid.toExact (fun a => Classical.propDecidable (mid.memaddrs a))
                [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "out_start")] =
                some [.val (.word w24), .val (.word (BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont" + 72))))] := by
              unfold evalListHOLExact; rw [hload24]
              unfold evalListHOLExact; rw [hos_ev]
              rfl
            dsimp only [dstExp]
            unfold evalHOLExact
            rw [hlist]; simp [valueIsWord, valueWord, wordOpHOL, wordOp]
          rcases hload144 : @evalHOLExact 64 F _ mid.toExact (fun a => Classical.propDecidable (mid.memaddrs a))
              srcExp with _ | v144
          · have hargs_m_none : evalListHOLFinite mid (h := fun a => Classical.propDecidable (mid.memaddrs a))
                [dstExp, srcExp, nExp] = none := by
              simp [evalListHOLFinite, evalListHOLExact, hdst_ev0, hload144]
            rw [evaluateHOLFiniteState_call, hargs_m_none]; dsimp only
            refine ⟨?_, fun h => by cases h⟩
            rintro ⟨_, h⟩; cases h
          · obtain ⟨w144, rfl, _⟩ := R14Shards.OpHandlersA.evalAt_loadG_word mid "ev" 144#64 v144 hload144
            set osw : BitVec 64 := BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont" + 72)) with hosw_def
            have hdst_ev : @evalHOLExact 64 F _ mid.toExact (fun a => Classical.propDecidable (mid.memaddrs a)) dstExp =
                some (.val (.word (w24 + osw))) := hdst_ev0
            have hn_ev : @evalHOLExact 64 F _ mid.toExact (fun a => Classical.propDecidable (mid.memaddrs a)) nExp =
                some (.val (.word actw)) := hmid_act
            have hact_pos : 0 < actw.toNat := by
              exact Nat.pos_of_ne_zero (fun h0 => hact0 (BitVec.eq_of_toNat_eq h0))
            have hact_le_osz : actw.toNat ≤ oszw.toNat := by
              rw [hactw_def]
              split_ifs with hlt
              · exact le_refl _
              · exact Nat.le_of_not_lt (mt BitVec.lt_def.2 hlt)
            have hoszw_le : oszw.toNat ≤ memW s0 (globN s0 "cur_cont" + 80) := by
              rw [hoszw_def, BitVec.toNat_ofNat]; exact Nat.mod_le _ _
            have hosz_ne0 : memW s0 (globN s0 "cur_cont" + 80) ≠ 0 := by omega
            have hout_le : memW s0 (globN s0 "cur_cont" + 72) + memW s0 (globN s0 "cur_cont" + 80) ≤
                memW st (globN st "ev" + 40) := by
              rcases out_win with h0 | hle
              · exact absurd h0 hosz_ne0
              · exact hle
            have hhead_mem : (globN st "ev", globN st "cur_cont") ∈ evmChain st := by
              simp [evmChain, evmChainFrom]
            have hFW0 := hBS.inv.2.2.2.2.1 _ hhead_mem
            have hmem_bnd : memW st (globN st "ev" + 24) + memW st (globN st "ev" + 40) ≤ 2 ^ 64 := by
              rcases (InitECandidate.Solver.Wave8Contracts.M23.frameWF_bounds hBS.arena.2 hFW0).2.2.2
                  (memW st (globN st "ev" + 24), memW st (globN st "ev" + 40)) (by simp [frameObjects]) with h0 | hb
              · dsimp only at h0; omega
              · exact hb
            have hosw_nat : osw.toNat = memW s0 (globN s0 "cur_cont" + 72) := by
              rw [hosw_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
            have hdst_nat : (w24 + osw).toNat = memW st (globN st "ev" + 24) + memW s0 (globN s0 "cur_cont" + 72) := by
              rw [BitVec.toNat_add, hw24_eq, hosw_nat, Nat.mod_eq_of_lt (by omega)]
            have hnt_mc : (evaluateHOLFiniteState mid
                (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp])).1 ≠ some .timeOut := by
              intro ht
              have : (evaluateHOLFiniteState mid (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp])).1 = some .timeOut := ht
              rcases hmc : evaluateHOLFiniteState mid (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp]) with ⟨mr, ms⟩
              rw [hmc] at this hnt; subst this; exact hnt rfl
            have hmc_spec := M11.eval_call_memcpy_bre mid dstExp srcExp nExp
              (w24 + osw) w144 actw [(memW st (globN st "ev" + 24), memW st (globN st "ev" + 40))]
              (by rw [hmid_eq]; exact hcode)
              (by rw [hmid_eq]; exact hBS.arena.1.memaddrs)
              hdst_ev hload144 hn_ev
              (fun _ => ⟨(memW st (globN st "ev" + 24), memW st (globN st "ev" + 40)),
                by simp, by rw [hdst_nat]; dsimp only; omega, by rw [hdst_nat]; dsimp only; omega⟩)
              hnt_mc
            rcases hmc_run : evaluateHOLFiniteState mid
                (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp]) with ⟨mr, ms⟩
            rw [hmc_run] at hmc_spec
            dsimp only at hmc_spec ⊢
            refine ⟨?_, fun hmr_none => ?_⟩
            · rintro ⟨ev, hev⟩
              have hnr := hmc_spec.2 (by rw [hev]; simp)
              exact hnr (Or.inr ⟨ofString "EvmErr", ev, hev, by decide⟩)
            · obtain ⟨hbre_mid_ms, hloc_ms⟩ := hmc_spec.1 hmr_none
              set postM : PanSemStateFiniteExact 64 F :=
                { ms with locals := HolFiniteMapExact.resVarEq ms.locals (ofString "actual", st.locals.lookup (ofString "actual")) } with hpostM_def
              have hpostM_loc : postM.locals = st.locals := by
                change HolFiniteMapExact.resVarEq ms.locals (ofString "actual", st.locals.lookup (ofString "actual")) = st.locals
                rw [hloc_ms, hmid_eq]; exact resVarEq_update_self_fc
              have hbre_st_postM : InitECandidate.Solver.Wave8Contracts.M23.ByteRegionEffect st postM
                  [(memW st (globN st "ev" + 24), memW st (globN st "ev" + 40))] :=
                ⟨hbre_mid_ms.code.trans (by rw [hmid_eq]),
                 hbre_mid_ms.memaddrs.trans (by rw [hmid_eq]),
                 hbre_mid_ms.shMemaddrs.trans (by rw [hmid_eq]),
                 hbre_mid_ms.baseAddr.trans (by rw [hmid_eq]),
                 hbre_mid_ms.be.trans (by rw [hmid_eq]),
                 hbre_mid_ms.globals.trans (by rw [hmid_eq]),
                 hbre_mid_ms.out_dom,
                 fun a ha => (hbre_mid_ms.cell_frame a ha).trans (by rw [hmid_eq]),
                 fun b hb hno => (hbre_mid_ms.byte_frame b hb hno).trans (by rw [hmid_eq]; rfl)⟩
              obtain ⟨hBS_postM, hch_postM, hR_postM, _⟩ :=
                fcBranchState_of_head_payload_bre hBS hbre_st_postM hpostM_loc (Or.inr (Or.inl rfl))
              exact ⟨hBS_postM, hpostM_loc, hbre_st_postM.globals, hch_postM, le_of_eq hR_postM⟩

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
