import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.Group05bEnv3

/-! # OpHandlerSpec Group 05bEnv3b (`OpHandlers-A`): `EvmInv` preservation under `bs+56..72` effect -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8Contracts.M23

theorem evmInv_of_bs56_effect {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv s) (hbs0 : globN s "bs" ≠ 0)
    (heff : ByteRegionEffect s post [(globN s "bs" + 56, 16)]) :
    EvmInv post ∧ post.globals = s.globals ∧ evmChain post = evmChain s ∧ evmR post = evmR s := by
  obtain ⟨hAs, S, hW, hch_ne, hch_len, hch_last, hFW_all, hFR_all, hRW, hFO_pw, hFO_disj,
    ⟨Nd, hTr, hAT⟩, hMarks, hRoles, hGas⟩ := hInv
  have hglob_eq : ∀ nm, globN post nm = globN s nm := fun nm => by simp [globN, heff.globals]
  have hdom_eq : post.memaddrs = s.memaddrs := heff.memaddrs
  have hh : globN s "heap_ptr" ≤ globN post "heap_ptr" := by rw [hglob_eq]
  have hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by rw [hglob_eq]
  have hApost : ArenaReady post :=
    ⟨guestInv_congr heff.code heff.memaddrs heff.shMemaddrs heff.baseAddr hAs.1,
     arenaOK_congr heff.globals hAs.2⟩
  obtain ⟨hW_post, hfeq, hfp_eq_all, hhtabHdr_eq, hwrs_eq, hjrs_eq, hworldRefs_eq,
    hTr_lift, hfix_bs, hRl8, hsub_bs⟩ := bs56_world_congr hAs S hW Nd hTr hbs0 heff
  have hdj_fo : ∀ ec ∈ evmChain s, ∀ o ∈ frameObjects s ec, Disj (globN s "bs" + 56, 16) o :=
    fun ec hec o ho => hsub_bs o (Wave8Contracts.M23.Disj.symm ((hFO_disj ec hec o ho).2 _ hfix_bs))
  have hrec_eq : ∀ ec ∈ evmChain s,
      (∀ k, k + 8 ≤ 280 → k % 8 = 0 → memW post (ec.1 + k) = memW s (ec.1 + k)) ∧
      (∀ k, k + 8 ≤ 104 → k % 8 = 0 → memW post (ec.2 + k) = memW s (ec.2 + k)) ∧
      (∀ k, k + 8 ≤ 24 → k % 8 = 0 → memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨hb1, hb2, hb88, _⟩ := frameWF_bounds hAs.2 hFW
    have he1_8 : ec.1 % 8 = 0 := (hFW.1 (ec.1, 280) (by simp)).2.1
    have he2_8 : ec.2 % 8 = 0 := (hFW.1 (ec.2, 104) (by simp)).2.1
    have he88_8 : (memW s (ec.1 + 88)) % 8 = 0 := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).2.1
    refine ⟨fun k hk hk8 => memW_eq_of_disj_eff heff hRl8 hb1 he1_8 hk8 hk
              (fun x hx => by simp at hx; subst hx; exact hdj_fo ec hec (ec.1, 280) (by simp [frameObjects])),
            fun k hk hk8 => memW_eq_of_disj_eff heff hRl8 hb2 he2_8 hk8 hk
              (fun x hx => by simp at hx; subst hx; exact hdj_fo ec hec (ec.2, 104) (by simp [frameObjects])),
            fun k hk hk8 => memW_eq_of_disj_eff heff hRl8 hb88 he88_8 hk8 hk
              (fun x hx => by simp at hx; subst hx; exact hdj_fo ec hec (memW s (ec.1 + 88), 24) (by simp [frameObjects]))⟩
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
      · rename_i hne16; rw [ih]; intro ec' hec'; exact hsub ec' (by simp [evmChainFrom, hne16, hec'])
  have hchain_eq : evmChain post = evmChain s := by
    unfold evmChain; rw [hglob_eq "ev", hglob_eq "cur_cont"]; exact hchain_aux _ _ _ (fun _ h => h)
  have hframeLogs_eq : ∀ ec ∈ evmChain s, frameLogs post ec = frameLogs s ec := by
    intro ec hec; obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec; unfold frameLogs
    rw [he_eq 88 (by omega) (by omega),
        show memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) by simpa using h88_eq 0 (by omega) (by omega),
        h88_eq 16 (by omega) (by omega)]
  have hframeRet_eq : ∀ ec ∈ evmChain s, frameRet post ec = frameRet s ec := by
    intro ec hec; obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec; unfold frameRet
    rw [he_eq 216 (by omega) (by omega), he_eq 144 (by omega) (by omega)]
  have hlogs_congr : ∀ ec ∈ evmChain s,
      frameLogObjects post ec = frameLogObjects s ec ∧ LogsListOK post (memW post (ec.1 + 88)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨_, _, _, hfob⟩ := frameWF_bounds hAs.2 hFW
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    have hl0 : memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) := by
      simpa using h88_eq 0 (by omega) (by omega)
    have hl8 := h88_eq 8 (by omega) (by omega)
    have hl16 := h88_eq 16 (by omega) (by omega)
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
      exact memW_eq_of_disj_eff heff hRl8 hfl_b hfl_8 (by omega)
        (by unfold frameLogs; dsimp only; omega)
        (fun x hx => by simp at hx; subst hx; exact hdj_fo ec hec _ hfl_in)
    have hlr_eq : ∀ i (_ : i < memW s (memW s (ec.1 + 88) + 8)) off, off + 8 ≤ 40 → off % 8 = 0 →
        memW post (memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + off) =
          memW s (memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + off) := by
      intro i hi off hoff hoff8
      have hlr_in : (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40) ∈ frameObjects s ec := by
        unfold frameObjects; apply List.mem_append_right; unfold frameLogObjects; dsimp only
        exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi,
          by unfold logOwnedIvls logRecordIvls; exact List.mem_filter.2 ⟨by simp, by simp⟩⟩
      have hlr_b : memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + 40 ≤ 2 ^ 64 := by
        rcases hfob _ hlr_in with h0 | hb
        · dsimp only at h0; omega
        · exact hb
      have hlr_8 : (memW s (memW s (memW s (ec.1 + 88)) + 8 * i)) % 8 = 0 := by
        rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨_, _, _, _, hent⟩
        · have he88_in := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).1.1
          have h1 := hAs.2.2.2.1; have h2 := hAs.2.2.2.2.1
          rw [Wave8Contracts.M23.scratchStart_val] at h1; dsimp only at he88_in; omega
        · exact (hent i hi).2.1.1
      exact memW_eq_of_disj_eff heff hRl8 hlr_b hlr_8 hoff8 hoff
        (fun x hx => by simp at hx; subst hx; exact hdj_fo ec hec _ hlr_in)
    refine ⟨?_, ?_⟩
    · unfold frameLogObjects; dsimp only; rw [he_eq 88 (by omega) (by omega), hl8]
      apply List.flatMap_congr; intro i hi; rw [List.mem_range] at hi; rw [hl0, harr_eq i hi]
      have r0 := hlr_eq i hi 0 (by omega) (by omega); simp only [Nat.add_zero] at r0
      unfold logOwnedIvls logRecordIvls
      rw [r0, hlr_eq i hi 8 (by omega) (by omega), hlr_eq i hi 16 (by omega) (by omega),
          hlr_eq i hi 24 (by omega) (by omega), hlr_eq i hi 32 (by omega) (by omega),
          hglob_eq "vm_system_address"]
    · rw [he_eq 88 (by omega) (by omega)]
      rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨hw_l, hal_l, hlt28, hle_cap, hent⟩
      · exact Or.inl hz
      · right; refine ⟨(wordsOK_congr_dom hdom_eq).2 hw_l, allocated_mono hh hsc hal_l,
          by rw [hl8]; exact hlt28, by rw [hl8, hl16]; exact hle_cap, fun i hi => ?_⟩
        rw [hl8] at hi; rw [hl0]; obtain ⟨hwa, hle⟩ := hent i hi
        refine ⟨(wordAt_congr_dom hdom_eq).2 hwa, ?_⟩; rw [harr_eq i hi]
        have r0 := hlr_eq i hi 0 (by omega) (by omega); simp only [Nat.add_zero] at r0
        unfold LogEntryOK at hle ⊢
        rw [r0, hlr_eq i hi 8 (by omega) (by omega), hlr_eq i hi 16 (by omega) (by omega),
            hlr_eq i hi 24 (by omega) (by omega), hlr_eq i hi 32 (by omega) (by omega), hglob_eq "heap_ptr"]
        exact ⟨(wordsOK_congr_dom hdom_eq).2 hle.1, hle.2⟩
  have hframeObjects_eq : ∀ ec ∈ evmChain s, frameObjects post ec = frameObjects s ec := by
    intro ec hec; obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec; unfold frameObjects
    rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega),
        he_eq 24 (by omega) (by omega), he_eq 40 (by omega) (by omega),
        he_eq 88 (by omega) (by omega), hframeLogs_eq ec hec, hframeRet_eq ec hec, (hlogs_congr ec hec).1]
  have hframeScratch_eq : ∀ ec ∈ evmChain s, frameScratch post ec = frameScratch s ec := by
    intro ec hec; obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec; unfold frameScratch
    rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega), he_eq 88 (by omega) (by omega)]
  have hmap_fo_eq : (evmChain s).map (frameObjects post) = (evmChain s).map (frameObjects s) :=
    List.map_congr_left hframeObjects_eq
  have hframeRoleSlots_eq : frameRoleSlots post (evmChain s) = frameRoleSlots s (evmChain s) := by
    unfold frameRoleSlots; apply List.flatMap_congr; intro ec hec; obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    rw [he_eq 136 (by omega) (by omega), he_eq 168 (by omega) (by omega), he_eq 176 (by omega) (by omega)]
  have hR_eq : evmR post = evmR s :=
    evmR_eq_of_chain_and_words hchain_eq (fun ec hec =>
      ⟨(hrec_eq ec hec).1 64 (by omega) (by omega), (hrec_eq ec hec).1 192 (by omega) (by omega)⟩)
  refine ⟨⟨hApost, S, hW_post, ?_⟩, heff.globals, hchain_eq, hR_eq⟩
  dsimp only; rw [hchain_eq]
  refine ⟨hch_ne, hch_len, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨ec, hec, hk0⟩ := hch_last
    exact ⟨ec, hec, by rw [(hrec_eq ec (List.mem_of_mem_getLast? hec)).2.1 16 (by omega) (by omega)]; exact hk0⟩
  · intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, _, c17⟩ := hFW_all ec hec
    have hlo_ok := (hlogs_congr ec hec).2
    have hmsg_ok : MsgOwned post S (memW post (ec.1 + 112)) := by
      rw [he_eq 112 (by omega) (by omega)]
      obtain ⟨hal_m, hw_m, hdt, hdf, hdfo, Nd_m, hTr_m, hdj_m⟩ := c17
      obtain ⟨hTr_int, hsub_int⟩ := Wave8Contracts.M23.triesTypedWith_inter hTr hTr_m
      set Ndi := Nd.filter (fun n => decide (n ∈ Nd_m))
      obtain ⟨hTr_post_int, hne_int⟩ := hTr_lift hTr_int
      refine ⟨allocated_mono hh hsc hal_m, (wordsOK_congr_dom hdom_eq).2 hw_m,
        fun t ht i hi => by rw [hfp_eq_all t ht] at hi; exact hdt t ht i hi,
        by rw [hfeq]; exact hdf,
        by rw [hchain_eq]; intro ec' hec' o ho; rw [hframeObjects_eq ec' hec'] at ho; exact hdfo ec' hec' o ho,
        Ndi, hTr_post_int, fun o ho j hj => ?_⟩
      rw [hne_int] at hj
      exact hdj_m o ho j (hsub_int j hj).2
    unfold FrameWF; dsimp only
    rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega),
        he_eq 88 (by omega) (by omega), he_eq 24 (by omega) (by omega),
        he_eq 40 (by omega) (by omega), he_eq 16 (by omega) (by omega),
        he_eq 32 (by omega) (by omega), he_eq 136 (by omega) (by omega),
        he_eq 168 (by omega) (by omega), he_eq 176 (by omega) (by omega),
        h88_eq 16 (by omega) (by omega), h88_eq 8 (by omega) (by omega),
        hframeLogs_eq ec hec, he_eq 216 (by omega) (by omega), he_eq 144 (by omega) (by omega),
        hframeRet_eq ec hec, hglob_eq "scratch_ptr", hglob_eq "frame_mem_ptr",
        hglob_eq "heap_ptr", hglob_eq "evm_empty"]
    rw [he_eq 88 (by omega) (by omega)] at hlo_ok
    refine ⟨fun i hi => ⟨(c1 i hi).1, (wordsOK_congr_dom hdom_eq).2 (c1 i hi).2⟩,
      c2, (wordsOK_congr_dom hdom_eq).2 c3, c4, c5, c6, c7, c8, c9, c10, c11, c12,
      c13, (wordsOK_congr_dom hdom_eq).2 c14, ?_, hlo_ok, hmsg_ok⟩
    rcases c15 with h0 | ⟨hin, hw⟩
    · exact Or.inl h0
    · exact Or.inr ⟨hin, (wordsOK_congr_dom hdom_eq).2 hw⟩
  · intro ec hec
    have hec_mem := List.mem_of_mem_tail hec; unfold FrameRoom
    rw [(hrec_eq ec hec_mem).1 16 (by omega) (by omega), (hrec_eq ec hec_mem).1 232 (by omega) (by omega)]
    exact hFR_all ec hec
  · intro i hi
    have hi0 : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
    have hi1 : (evmChain s)[i + 1] ∈ evmChain s := List.getElem_mem _
    rw [(hrec_eq _ hi0).2.1 80 (by omega) (by omega), (hrec_eq _ hi0).2.1 72 (by omega) (by omega),
        (hrec_eq _ hi1).1 40 (by omega) (by omega)]
    exact hRW i hi
  · rw [hmap_fo_eq]; exact hFO_pw
  · intro ec hec o ho; rw [hframeObjects_eq ec hec] at ho; rw [hfeq]
    exact ⟨fun t ht i hi => by rw [hfp_eq_all t ht] at hi; exact (hFO_disj ec hec o ho).1 t ht i hi,
      (hFO_disj ec hec o ho).2⟩
  · rw [hmap_fo_eq]
    obtain ⟨hTr_post, hne_Nd⟩ := hTr_lift hTr
    refine ⟨Nd, hTr_post, fun o ho j hj => ?_⟩
    rw [hne_Nd] at hj
    exact hAT o ho j hj
  · have hdelEx_iff : ∀ i t, DelExclusive post S (evmChain s) i t ↔ DelExclusive s S (evmChain s) i t := by
      intro i t; unfold DelExclusive; rw [hworldRefs_eq]
      refine and_congr Iff.rfl (forall_congr' fun j => forall_congr' fun hj =>
        forall_congr' fun k => imp_congr_right fun hk => ?_)
      have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
      have hk_ok : k + 8 ≤ 280 ∧ k % 8 = 0 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl <;> omega
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
    · intro t ht; rw [hfp_eq_all t ht, hdelEx_iff i t]; exact m8 t ht
  · rw [hwrs_eq, hframeRoleSlots_eq, hjrs_eq]
    unfold RolesOK at hRoles ⊢
    exact ⟨fun a ha => ⟨(hRoles.1 a ha).1, by
      rw [hhtabHdr_eq a.1 (hRoles.1 a ha).1 0 (by omega)]; exact (hRoles.1 a ha).2⟩, hRoles.2⟩
  · have hsum_eq : ((evmChain s).map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)).sum =
        ((evmChain s).map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum := by
      unfold evmR at hR_eq; rw [hchain_eq] at hR_eq; exact hR_eq
    rw [hsum_eq]; exact hGas

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
