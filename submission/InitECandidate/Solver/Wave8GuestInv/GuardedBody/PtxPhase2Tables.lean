import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase1Geometry

/-! World-typing transport for `htab_new`, `htab_set`, and `MsgReady` assembly
in Phase 2 of `process_transaction`. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.Phase2

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Backend
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.Phase1

theorem worldOwned_zero_or_allocated {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hW : WorldTypedWith s S Nd) :
    ∀ j ∈ worldOwned s S Nd, j = (0, 0) ∨ Allocated s j := by
  obtain ⟨hT, _, hF, hTr⟩ := hW
  intro j hj
  unfold worldOwned at hj
  rcases List.mem_append.1 hj with h1 | hnd
  · rcases List.mem_append.1 h1 with htab | hfix
    · obtain ⟨t, ht, hj_fp⟩ := List.mem_flatMap.1 htab
      exact Or.inr (((hT.2.1 t ht).2 j hj_fp).1)
    · rcases hF.1 j hfix with hz | ⟨hal, _⟩
      · exact Or.inl (Prod.ext (normalized_mem_zero hfix hz) hz)
      · exact Or.inr hal
  · obtain ⟨n, hn, hj_n⟩ := List.mem_flatMap.1 hnd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj_n
    rcases hj_n with rfl | rfl
    · exact Or.inr (hTr.1.1 n hn).2.2.2.1
    · unfold nodePath
      split_ifs with hc
      · have hk := (hTr.1.1 n hn).2.2.2.2.2.2.2.2 hc.1
        exact Or.inr ((hk.resolve_left hc.2).2.1)
      · exact Or.inl rfl

theorem ivlUnhit_of_frameOutside_aligned {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {keep : List Ivl} {fresh i : Ivl}
    (hfr : FrameOutside s post keep fresh)
    (hk_al : ∀ j ∈ keep, j.1 % 8 = 0 ∧ j.2 % 8 = 0)
    (hf_al : fresh.1 % 8 = 0 ∧ fresh.2 % 8 = 0)
    (hi0 : i.2 = 0 → i.1 % 8 = 0)
    (hk : ∀ j ∈ keep, Disj i j) (hf : Disj i fresh) :
    IvlUnhit s post i := by
  intro a ha8 hhit
  obtain ⟨hi1, hi2⟩ := hhit
  apply hfr a
  · intro j hj hcj
    obtain ⟨hj1, hj2⟩ := hk_al j hj
    obtain ⟨hc1, hc2⟩ := hcj
    rcases hk j hj with hd | hd | hd | hd
    · have := hi0 hd; omega
    · omega
    · omega
    · omega
  · intro hcf
    obtain ⟨hf1, hf2⟩ := hf_al
    obtain ⟨hc1, hc2⟩ := hcf
    rcases hf with hd | hd | hd | hd
    · have := hi0 hd; omega
    · omega
    · omega
    · omega

theorem ivl_disj_free_of_zero_or_allocated {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaOK s) (hAp : ArenaOK post) (hag : AllocatorGrows s post)
    {j : Ivl} (hj : j = (0, 0) ∨ Allocated s j) :
    Disj j (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") ∧
    Disj j (globN post "scratch_ptr", globN s "scratch_ptr" - globN post "scratch_ptr") := by
  have hsep : heapLimit ≤ scratchStart := by decide
  obtain ⟨_, hs_hp, hs_fm, hs_sc, _⟩ := hAs
  obtain ⟨_, hp_hp, hp_fm, hp_sc, _⟩ := hAp
  have hg_hp := hag.1; have hg_sc := hag.2
  rcases hj with rfl | ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
  · exact ⟨disj_zero_left _, disj_zero_left _⟩
  · exact ⟨Or.inr (Or.inr (Or.inl (by dsimp; omega))),
      Or.inr (Or.inr (Or.inl (by dsimp; omega)))⟩
  · exact ⟨Or.inr (Or.inr (Or.inr (by dsimp; omega))),
      Or.inr (Or.inr (Or.inr (by dsimp; omega)))⟩

theorem ivl_unhit_free_of_zero_or_allocated {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaOK s) (hAp : ArenaOK post) (hag : AllocatorGrows s post)
    {keep : List Ivl} {fresh : Ivl}
    (hfr : FrameOutside s post keep fresh)
    (hk_sub : ∀ k ∈ keep, k = (globN post "scratch_ptr", globN s "scratch_ptr" - globN post "scratch_ptr"))
    (hf_eq : fresh = (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr"))
    {j : Ivl} (hj0 : j.2 = 0 → j.1 % 8 = 0) (hj : j = (0, 0) ∨ Allocated s j) :
    IvlUnhit s post j := by
  obtain ⟨hd_hp, hd_sc⟩ := ivl_disj_free_of_zero_or_allocated hAs hAp hag hj
  obtain ⟨_, _, _, _, _, hs_hp8, _, hs_sc8⟩ := hAs
  obtain ⟨_, _, _, _, _, hp_hp8, _, hp_sc8⟩ := hAp
  have hg_hp := hag.1; have hg_sc := hag.2
  exact ivlUnhit_of_frameOutside_aligned hfr
    (fun k hk => by rw [hk_sub k hk]; exact ⟨hp_sc8, by omega⟩)
    (by rw [hf_eq]; exact ⟨hs_hp8, by omega⟩)
    hj0
    (fun k hk => by rw [hk_sub k hk]; exact hd_sc)
    (by rw [hf_eq]; exact hd_hp)

theorem unhit_of_worldTypedIvls {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat}
    (hunhit : ∀ j ∈ worldOwned s S Nd, IvlUnhit s post j) :
    ∀ i ∈ worldTypedIvls s S Nd, IvlUnhit s post i := by
  intro i hi
  rcases worldTypedIvls_mem hi with rfl | ho
  · intro _ _ hch; unfold CellHits at hch; dsimp at hch; omega
  · exact hunhit i ho

theorem worldTypedWith_htab_new {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaReady s) {S Nd : List Nat} (hW : WorldTypedWith s S Nd)
    {t : Nat}
    (hAp : ArenaReady post) (hag : AllocatorGrows s post) (hwf_t : HtabWF post t)
    (hfp_t : ∀ i ∈ htabFootprint post t, Allocated post i ∧
      (Inside i (globN s "heap_ptr") (globN post "heap_ptr") ∨
        Inside i (globN post "scratch_ptr") (globN s "scratch_ptr")))
    (hfr : FrameOutside s post
      [(globN post "scratch_ptr", globN s "scratch_ptr" - globN post "scratch_ptr")]
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr"))
    (hbe : post.be = s.be)
    (hg_kept : ∀ name, name ∉ ["heap_ptr", "scratch_ptr"] →
      s.globals.lookup (ofString name) = post.globals.lookup (ofString name)) :
    t ∉ S ∧ t ≠ 0 ∧
    (∀ a ∈ worldRoleSlots post ++ journalRoleSlots post, a.1 ≠ t) ∧
    WorldTypedWith post (S ++ [t]) Nd ∧
    worldRoleSlots post = worldRoleSlots s ∧
    journalRoleSlots post = journalRoleSlots s ∧
    (∀ u ∈ S, hdr post u 0 = hdr s u 0) ∧
    (∀ b : Ivl, (b.2 = 0 → b.1 % 8 = 0) → Inside b sourceBase (globN s "heap_ptr") →
      (∀ j ∈ worldOwned s S Nd, Disj b j) →
      Inside b sourceBase (globN post "heap_ptr") ∧
      (∀ o ∈ worldOwned post (S ++ [t]) Nd, Disj b o) ∧
      IvlUnhit s post b) := by
  have hgs : WorldGlobalsSame s post :=
    worldGlobalsSame_of_kept hg_kept (fun name hn => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl))
  have hsb : 24 < sourceBase := by decide
  have hsb264 : sourceBase < 2 ^ 64 := by decide
  have hsep : heapLimit ≤ scratchStart := by decide
  obtain ⟨hs_lo, hs_hp, hs_fm, hs_sc, hs_end, hs_hp8, hs_fm8, hs_sc8⟩ := hAs.2
  obtain ⟨hp_lo, hp_hp, hp_fm, hp_sc, hp_end, hp_hp8, hp_fm8, hp_sc8⟩ := hAp.2
  have hg_hp := hag.1; have hg_sc := hag.2
  have hf_al : (globN s "heap_ptr") % 8 = 0 ∧ (globN post "heap_ptr" - globN s "heap_ptr") % 8 = 0 :=
    ⟨hs_hp8, by omega⟩
  have hs_al : (globN post "scratch_ptr") % 8 = 0 ∧ (globN s "scratch_ptr" - globN post "scratch_ptr") % 8 = 0 :=
    ⟨hp_sc8, by omega⟩
  have hm0 : memW post 0 = memW s 0 ∧ memW post 16 = memW s 16 := by
    have hlow : ∀ a : Nat, a + 8 ≤ sourceBase → memW post a = memW s a := fun a ha => by
      have ha_lt : a < 2 ^ 64 := by omega
      have hm := hfr (BitVec.ofNat 64 a)
        (fun j hj hcj => by
          simp only [List.mem_singleton] at hj; subst hj
          obtain ⟨h1, _⟩ := hcj
          dsimp at h1
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at h1
          omega)
        (fun hcf => by
          obtain ⟨h1, _⟩ := hcf
          dsimp at h1
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at h1
          omega)
      unfold memW; rw [hm]
    exact ⟨hlow 0 (by omega), hlow 16 (by omega)⟩
  have hunhit_owned : ∀ j ∈ worldOwned s S Nd, IvlUnhit s post j := fun j hj =>
    ivl_unhit_free_of_zero_or_allocated hAs.2 hAp.2 hag hfr
      (fun k hk => List.mem_singleton.1 hk) rfl (worldOwned_zero_aligned hW j hj)
      (worldOwned_zero_or_allocated hW j hj)
  have hunhit : ∀ i ∈ worldTypedIvls s S Nd, IvlUnhit s post i :=
    unhit_of_worldTypedIvls hunhit_owned
  have hrec_ti : ∀ (g : String) (sz : Nat), (g, sz) ∈ typedRecords → sz ≠ 0 →
      globN s g ≠ 0 → (globN s g, sz) ∈ worldTypedIvls s S Nd := by
    intro g sz hrec hsz hnz
    apply mem_normalized (hn := fun h => absurd h hsz)
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
      (List.mem_map.2 ⟨(g, sz), hrec, by simp [hnz]⟩)))))
  have hbo_u : globN s "bo" ≠ 0 → IvlUnhit s post (globN s "bo", 88) := fun hnz =>
    hunhit _ (hrec_ti "bo" 88 (by simp [typedRecords]) (by decide) hnz)
  have hbase := worldTypedWith_congr_bo hAs hAp hbe hag hgs hW
    (fun u hu i hi => hunhit_owned i
      (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_flatMap.2 ⟨u, hu, hi⟩))))))
    (fun hnz => hunhit _ (hrec_ti "ws" 40 (by simp [typedRecords]) (by decide) hnz))
    (fun hnz => hunhit _ (hrec_ti "bs" 80 (by simp [typedRecords]) (by decide) hnz))
    (fun hnz => hunhit _ (hrec_ti "ts" 72 (by simp [typedRecords]) (by decide) hnz))
    (fun hnz => hunhit_owned _ (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr
      (fixed_mem_raw (by simp [fixedRaw]) (by dsimp; omega)))))))
    (fun i hi h24 => hunhit_owned i (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr
      (fixed_mem_raw (block_mem_raw hi) (by omega)))))))
    (fun i hi => by
      by_cases hz : i.2 = 0
      · have hb := normalized_mem_zero hi hz
        have hi_eq : i = (0, 0) := Prod.ext hb hz
        intro _ _ hch; rw [hi_eq] at hch; unfold CellHits at hch; dsimp at hch; omega
      · exact hunhit_owned i (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr
          (fixed_mem_raw (bal_mem_raw hi) hz))))))
    (fun o ho => hunhit_owned o (List.mem_append.2 (Or.inr ho)))
    (fun hnz k hk => by
      have hk_in : k % 8 = 0 ∧ k + 8 ≤ 88 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      have hbo_g : globN post "bo" = globN s "bo" := hgs.1 ("bo", 88) (by simp [globalBuffers])
      simpa [hbo_g] using
        rec_word_eq_of_unhit hAs.2 hW.2.2.1 "bo" 88 (by simp [typedRecords]) hbo_g hnz (hbo_u hnz) hk_in.1 hk_in.2)
    hm0
  obtain ⟨hW_S, howned_S, hwrs_eq, hjr_eq, hhdr_S⟩ := hbase
  have ht_fp_disj : ∀ i ∈ htabFootprint post t, ∀ j ∈ worldOwned post S Nd, Disj i j := by
    intro i hi j hj
    rw [howned_S] at hj
    obtain ⟨hd_hp, hd_sc⟩ := ivl_disj_free_of_zero_or_allocated hAs.2 hAp.2 hag
      (worldOwned_zero_or_allocated hW j hj)
    rcases (hfp_t i hi).2 with hin_hp | hin_sc
    · have hin' : Inside i (globN s "heap_ptr") (globN s "heap_ptr" + (globN post "heap_ptr" - globN s "heap_ptr")) := by
        unfold Inside at hin_hp ⊢; omega
      exact disj_symm (disj_of_inside_right hin' hd_hp)
    · have hin' : Inside i (globN post "scratch_ptr") (globN post "scratch_ptr" + (globN s "scratch_ptr" - globN post "scratch_ptr")) := by
        unfold Inside at hin_sc ⊢; omega
      exact disj_symm (disj_of_inside_right hin' hd_sc)
  have ht_not_S : t ∉ S := by
    intro ht_in
    have hmem_ow : (t, 88) ∈ worldOwned post S Nd := by
      unfold worldOwned
      apply List.mem_append.2; left; apply List.mem_append.2; left
      exact List.mem_flatMap.2 ⟨t, ht_in, by simp [htabFootprint]⟩
    have hd := ht_fp_disj (t, 88) (by simp [htabFootprint]) (t, 88) hmem_ow
    rcases hd with hd | hd | hd | hd <;> dsimp at hd <;> omega
  have ht_nz : t ≠ 0 := by
    have hlo := (hwf_t.1 (t, 88) (by simp [htabFootprint])).1.1
    have hsb0 : 0 < sourceBase := by decide
    dsimp at hlo; omega
  obtain ⟨hT_S, hJ_S, hF_S, hTr_S⟩ := hW_S
  have hslot_ne_t : ∀ a ∈ worldRoleSlots post ++ journalRoleSlots post, a.1 ≠ t := by
    intro a ha heq
    have haS := (hT_S.2.2.2.2.2.2.2.2.2.2.2.1 a ha).1
    rw [heq] at haS
    exact ht_not_S haS
  have hsub_St : ∀ u ∈ S, u ∈ S ++ [t] := fun u hu => List.mem_append.2 (Or.inl hu)
  have hroot_sub : ∀ {v : Nat}, RootIn S v → RootIn (S ++ [t]) v := by
    rintro v (rfl | hv)
    · exact Or.inl rfl
    · exact Or.inr (hsub_St v hv)
  have hval_sub : ∀ {u : Nat}, HtabValuesIn post u S → HtabValuesIn post u (S ++ [t]) :=
    fun hv i hi => hsub_St _ (hv i hi)
  have hT_ext : TablesTyped post (S ++ [t]) := by
    obtain ⟨hndS, hTt, hTp, hwsR, hbsR, htsR, hgR, hbsN, htsN, hbalT, hboT, hroles⟩ := hT_S
    refine ⟨List.nodup_append.2 ⟨hndS, List.nodup_singleton t, fun x hxS y hy heq => by
        have := List.mem_singleton.1 hy; subst this; subst heq; exact ht_not_S hxS⟩,
      ?_, ?_,
      fun k hk hnz => hroot_sub (hwsR k hk hnz),
      fun k hk hnz => hroot_sub (hbsR k hk hnz),
      fun k hk hnz => hroot_sub (htsR k hk hnz),
      fun g hg => hroot_sub (hgR g hg),
      ?_, ?_, ?_, hboT, ?_⟩
    · intro u hu
      rcases List.mem_append.1 hu with huS | hut
      · exact hTt u huS
      · simp only [List.mem_singleton] at hut; subst hut
        refine ⟨hwf_t, fun i hi => ⟨(hfp_t i hi).1, fun j hj => ?_⟩⟩
        apply ht_fp_disj i hi j
        unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hj)))
    · intro u hu v hv hne i hi j hj
      rcases List.mem_append.1 hu with huS | hut <;> rcases List.mem_append.1 hv with hvS | hvt
      · exact hTp u huS v hvS hne i hi j hj
      · simp only [List.mem_singleton] at hvt; subst hvt
        apply disj_symm; apply ht_fp_disj j hj i
        unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_flatMap.2 ⟨u, huS, hi⟩))))
      · simp only [List.mem_singleton] at hut; subst hut
        apply ht_fp_disj i hi j
        unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_flatMap.2 ⟨v, hvS, hj⟩))))
      · simp only [List.mem_singleton] at hut hvt; subst hut; exact absurd hvt.symm hne
    · intro hnz hm
      rcases List.mem_append.1 hm with hmS | hmt
      · exact hval_sub (hbsN hnz hmS)
      · simp only [List.mem_singleton] at hmt
        rcases hbsR 32 (by simp [bsTableSlots]) hnz with h0 | hmS
        · exact absurd (h0.symm.trans hmt).symm ht_nz
        · exact absurd (hmt ▸ hmS) ht_not_S
    · intro hnz hm
      rcases List.mem_append.1 hm with hmS | hmt
      · exact hval_sub (htsN hnz hmS)
      · simp only [List.mem_singleton] at hmt
        rcases htsR 32 (by simp [tsTableSlots]) hnz with h0 | hmS
        · exact absurd (h0.symm.trans hmt).symm ht_nz
        · exact absurd (hmt ▸ hmS) ht_not_S
    · intro ad had
      obtain ⟨h0, h8, hrest⟩ := hbalT ad had
      exact ⟨hsub_St _ h0, hsub_St _ h8, hrest⟩
    · exact ⟨fun a ha => ⟨hsub_St _ (hroles.1 a ha).1, (hroles.1 a ha).2⟩, hroles.2.1, hroles.2.2⟩
  have hJ_ext : JournalTyped post (S ++ [t]) :=
    ⟨hJ_S.1, hJ_S.2.1, hJ_S.2.2.1, fun i hi => hsub_St _ (hJ_S.2.2.2 i hi)⟩
  have hTr_ext : TriesTypedWith post (S ++ [t]) Nd := by
    refine ⟨hTr_S.1, fun o ho => ⟨fun u hu i hi => ?_, (hTr_S.2.1 o ho).2⟩, ?_⟩
    · rcases List.mem_append.1 hu with huS | hut
      · exact (hTr_S.2.1 o ho).1 u huS i hi
      · simp only [List.mem_singleton] at hut; subst hut
        apply disj_symm; apply ht_fp_disj i hi o
        unfold worldOwned; exact List.mem_append.2 (Or.inr ho)
    · intro hnz
      obtain ⟨hr24, hr32⟩ := hTr_S.2.2 hnz
      refine ⟨hr24, fun hm => ?_⟩
      rcases List.mem_append.1 hm with hmS | hmt
      · exact hr32 hmS
      · simp only [List.mem_singleton] at hmt
        rcases hT_S.2.2.2.1 32 (by simp [wsTableSlots]) hnz with h0 | hmS
        · exact absurd (h0.symm.trans hmt).symm ht_nz
        · exact absurd (hmt ▸ hmS) ht_not_S
  refine ⟨ht_not_S, ht_nz, hslot_ne_t, ⟨hT_ext, hJ_ext, hF_S, hTr_ext⟩, hwrs_eq, hjr_eq, hhdr_S, ?_⟩
  intro b hb0 hb_in hb_disj
  obtain ⟨hd_hp, hd_sc⟩ := ivl_disj_free_of_zero_or_allocated hAs.2 hAp.2 hag (Or.inr (Or.inl hb_in))
  refine ⟨⟨hb_in.1, Nat.le_trans hb_in.2 hag.1⟩, ?_, ?_⟩
  · intro o ho
    unfold worldOwned at ho
    rcases List.mem_append.1 ho with h1 | hnd
    · rcases List.mem_append.1 h1 with htab | hfix
      · rw [List.flatMap_append] at htab
        rcases List.mem_append.1 htab with htabS | htab_t
        · apply hb_disj o; rw [← howned_S]; unfold worldOwned
          exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl htabS)))
        · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at htab_t
          rcases (hfp_t o htab_t).2 with hin_hp | hin_sc
          · exact Or.inr (Or.inr (Or.inl (Nat.le_trans hb_in.2 hin_hp.1)))
          · exact Or.inr (Or.inr (Or.inl (by unfold Inside at hb_in hin_sc; omega)))
      · apply hb_disj o; rw [← howned_S]; unfold worldOwned
        exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hfix)))
    · apply hb_disj o; rw [← howned_S]; unfold worldOwned
      exact List.mem_append.2 (Or.inr hnd)
  · exact ivlUnhit_of_frameOutside_aligned hfr
      (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact hs_al)
      hf_al hb0
      (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact hd_sc)
      hd_hp

theorem zero_not_mem_S {F : Type} {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hT : TablesTyped s S) : 0 ∉ S := by
  intro h0
  have hlo := ((hT.2.1 0 h0).1.1 (0, 88) (by simp [htabFootprint])).1.1
  have hsb : 0 < sourceBase := by decide
  dsimp at hlo; omega

theorem worldTypedWith_perm {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S S' Nd : List Nat} (hp : S.Perm S') (hW : WorldTypedWith s S Nd) :
    WorldTypedWith s S' Nd := by
  obtain ⟨hT, hJ, hF, hTr⟩ := hW
  have hmem : ∀ x, x ∈ S' ↔ x ∈ S := fun x => hp.symm.mem_iff
  have hroot : ∀ {v}, RootIn S v → RootIn S' v := by
    rintro v (rfl | hv)
    · exact Or.inl rfl
    · exact Or.inr ((hmem v).2 hv)
  have hval : ∀ {u}, HtabValuesIn s u S → HtabValuesIn s u S' :=
    fun hv i hi => (hmem _).2 (hv i hi)
  obtain ⟨hnd, hTt, hTp, hws, hbs, hts, hg, hbsN, htsN, hbal, hbo, hroles⟩ := hT
  refine ⟨⟨hp.nodup_iff.1 hnd,
    fun u hu => hTt u ((hmem u).1 hu),
    fun u hu v hv => hTp u ((hmem u).1 hu) v ((hmem v).1 hv),
    fun k hk hnz => hroot (hws k hk hnz),
    fun k hk hnz => hroot (hbs k hk hnz),
    fun k hk hnz => hroot (hts k hk hnz),
    fun g hgm => hroot (hg g hgm),
    fun hnz hm => hval (hbsN hnz ((hmem _).1 hm)),
    fun hnz hm => hval (htsN hnz ((hmem _).1 hm)),
    fun ad had => ⟨(hmem _).2 (hbal ad had).1, (hmem _).2 (hbal ad had).2.1, (hbal ad had).2.2⟩,
    hbo,
    ⟨fun a ha => ⟨(hmem _).2 (hroles.1 a ha).1, (hroles.1 a ha).2⟩, hroles.2⟩⟩,
    ⟨hJ.1, hJ.2.1, hJ.2.2.1, fun i hi => (hmem _).2 (hJ.2.2.2 i hi)⟩,
    hF,
    ⟨hTr.1, fun o ho => ⟨fun u hu => (hTr.2.1 o ho).1 u ((hmem u).1 hu), (hTr.2.1 o ho).2⟩,
      fun hnz => ⟨(hTr.2.2 hnz).1, fun hm => (hTr.2.2 hnz).2 ((hmem _).1 hm)⟩⟩⟩

theorem worldTypedWith_erase_local {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hW : WorldTypedWith s S Nd) {t : Nat}
    (hlocal : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ t) :
    WorldTypedWith s (S.erase t) Nd := by
  obtain ⟨hT, hJ, hF, hTr⟩ := hW
  have h0S : 0 ∉ S := zero_not_mem_S hT
  have hmem_er : ∀ {x}, x ∈ S → x ≠ t → x ∈ S.erase t := fun hx hne =>
    (List.Nodup.mem_erase_iff hT.1).2 ⟨hne, hx⟩
  have hsub_er : ∀ {x}, x ∈ S.erase t → x ∈ S := fun hx => List.mem_of_mem_erase hx
  have hwrs_ne : ∀ x r, x ≠ 0 → (x, r) ∈
      (recRoles s "ws" [(16, "ws+16"), (32, "ws+32")] ++
      recRoles s "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"), (40, "bs+40"),
        (48, "bs+48"), (72, "bs+72")] ++
      recRoles s "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"), (40, "ts+40"),
        (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] ++
      [(globN s "bal_accounts", "bal_accounts"), (globN s "bal_idx_accts", "bal_idx_accts"),
        (globN s "bal_idx_stor", "bal_idx_stor")] ++
      nestRoles s "bs" "bs.inner" ++ nestRoles s "ts" "ts.inner" ++
      (balRecords s).flatMap fun ad => [(memW s ad, "bal.stor"), (memW s (ad + 8), "bal.reads")]) →
      x ≠ t := by
    intro x r hxnz hmem
    have hfw : (x, r) ∈ worldRoleSlots s := by
      unfold worldRoleSlots
      exact List.mem_filter.2 ⟨hmem, by simp [hxnz]⟩
    exact hlocal (x, r) (List.mem_append.2 (Or.inl hfw))
  obtain ⟨hnd, hTt, hTp, hws, hbs, hts, hg, hbsN, htsN, hbal, hbo, hroles⟩ := hT
  refine ⟨⟨hnd.erase t,
    fun u hu => hTt u (hsub_er hu),
    fun u hu v hv => hTp u (hsub_er hu) v (hsub_er hv),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbo, ?_⟩, ?_, hF, ?_⟩
  · intro k hk hnz
    rcases hws k hk hnz with h0 | hm
    · exact Or.inl h0
    · right; apply hmem_er hm
      have hnz_v : memW s (globN s "ws" + k) ≠ 0 := fun h0 => h0S (h0 ▸ hm)
      simp only [wsTableSlots, List.mem_singleton] at hk; subst hk
      apply hwrs_ne _ "ws+32" hnz_v
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      unfold recRoles; simp [hnz]
  · intro k hk hnz
    rcases hbs k hk hnz with h0 | hm
    · exact Or.inl h0
    · right; apply hmem_er hm
      have hnz_v : memW s (globN s "bs" + k) ≠ 0 := fun h0 => h0S (h0 ▸ hm)
      have hb_in : ∃ r, (memW s (globN s "bs" + k), r) ∈
          recRoles s "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"), (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] := by
        unfold recRoles; simp only [hnz, ↓reduceIte]
        simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨"bs+8", by simp⟩
        · exact ⟨"bs+16", by simp⟩
        · exact ⟨"bs+24", by simp⟩
        · exact ⟨"bs+32", by simp⟩
        · exact ⟨"bs+40", by simp⟩
        · exact ⟨"bs+48", by simp⟩
        · exact ⟨"bs+72", by simp⟩
      obtain ⟨r, hr_mem⟩ := hb_in
      apply hwrs_ne _ r hnz_v
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; left; apply List.mem_append.2; left; exact List.mem_append.2 (Or.inr hr_mem)
  · intro k hk hnz
    rcases hts k hk hnz with h0 | hm
    · exact Or.inl h0
    · right; apply hmem_er hm
      have hnz_v : memW s (globN s "ts" + k) ≠ 0 := fun h0 => h0S (h0 ▸ hm)
      have ht_in : ∃ r, (memW s (globN s "ts" + k), r) ∈
          recRoles s "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"), (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] := by
        unfold recRoles; simp only [hnz, ↓reduceIte]
        simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨"ts+8", by simp⟩
        · exact ⟨"ts+16", by simp⟩
        · exact ⟨"ts+24", by simp⟩
        · exact ⟨"ts+32", by simp⟩
        · exact ⟨"ts+40", by simp⟩
        · exact ⟨"ts+48", by simp⟩
        · exact ⟨"ts+56", by simp⟩
        · exact ⟨"ts+64", by simp⟩
      obtain ⟨r, hr_mem⟩ := ht_in
      apply hwrs_ne _ r hnz_v
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; left; exact List.mem_append.2 (Or.inr hr_mem)
  · intro g hgm
    rcases hg g hgm with h0 | hm
    · exact Or.inl h0
    · right; apply hmem_er hm
      have hnz_v : globN s g ≠ 0 := fun h0 => h0S (h0 ▸ hm)
      have hg_in : (globN s g, g) ∈
          [(globN s "bal_accounts", "bal_accounts"), (globN s "bal_idx_accts", "bal_idx_accts"),
           (globN s "bal_idx_stor", "bal_idx_stor")] := by
        simp only [globalTableRoots, List.mem_cons, List.not_mem_nil, or_false] at hgm
        rcases hgm with rfl | rfl | rfl <;> simp
      apply hwrs_ne _ g hnz_v
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      exact List.mem_append.2 (Or.inr hg_in)
  · intro hnz hm i hi
    have hmS := hsub_er hm
    have hvS := hbsN hnz hmS i hi
    have hvnz : nodeF s (hdr s (memW s (globN s "bs" + 32)) 5) (memW s (hdr s (memW s (globN s "bs" + 32)) 6 + 8 * i)) 8 ≠ 0 :=
      fun h0 => h0S (h0 ▸ hvS)
    have h32nz : memW s (globN s "bs" + 32) ≠ 0 := fun h0 => h0S (h0 ▸ hmS)
    apply hmem_er hvS
    apply hwrs_ne _ "bs.inner" hvnz
    apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
    unfold nestRoles; simp only [hnz, h32nz, ↓reduceIte]
    exact List.mem_map.2 ⟨_, List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩, rfl⟩
  · intro hnz hm i hi
    have hmS := hsub_er hm
    have hvS := htsN hnz hmS i hi
    have hvnz : nodeF s (hdr s (memW s (globN s "ts" + 32)) 5) (memW s (hdr s (memW s (globN s "ts" + 32)) 6 + 8 * i)) 8 ≠ 0 :=
      fun h0 => h0S (h0 ▸ hvS)
    have h32nz : memW s (globN s "ts" + 32) ≠ 0 := fun h0 => h0S (h0 ▸ hmS)
    apply hmem_er hvS
    apply hwrs_ne _ "ts.inner" hvnz
    apply List.mem_append.2; left; apply List.mem_append.2; right
    unfold nestRoles; simp only [hnz, h32nz, ↓reduceIte]
    exact List.mem_map.2 ⟨_, List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩, rfl⟩
  · intro ad had
    obtain ⟨h0, h8, hrest⟩ := hbal ad had
    have h0nz : memW s ad ≠ 0 := fun h => h0S (h ▸ h0)
    have h8nz : memW s (ad + 8) ≠ 0 := fun h => h0S (h ▸ h8)
    refine ⟨hmem_er h0 ?_, hmem_er h8 ?_, hrest⟩
    · apply hwrs_ne _ "bal.stor" h0nz
      apply List.mem_append.2; right; exact List.mem_flatMap.2 ⟨ad, had, by simp⟩
    · apply hwrs_ne _ "bal.reads" h8nz
      apply List.mem_append.2; right; exact List.mem_flatMap.2 ⟨ad, had, by simp⟩
  · exact ⟨fun a ha => ⟨hmem_er (hroles.1 a ha).1 (hlocal a ha), (hroles.1 a ha).2⟩, hroles.2⟩
  · refine ⟨hJ.1, hJ.2.1, hJ.2.2.1, fun i hi => hmem_er (hJ.2.2.2 i hi) ?_⟩
    have hj_in : (memW s (globN s "journal" + 32 * i), journalRole s (memW s (globN s "journal" + 32 * i))) ∈ journalRoleSlots s := by
      unfold journalRoleSlots
      exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, by simp⟩
    exact hlocal _ (List.mem_append.2 (Or.inr hj_in))
  · exact ⟨hTr.1, fun o ho => ⟨fun u hu => (hTr.2.1 o ho).1 u (hsub_er hu), (hTr.2.1 o ho).2⟩,
      fun hnz => ⟨(hTr.2.2 hnz).1, fun hm => (hTr.2.2 hnz).2 (hsub_er hm)⟩⟩

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.Phase2
