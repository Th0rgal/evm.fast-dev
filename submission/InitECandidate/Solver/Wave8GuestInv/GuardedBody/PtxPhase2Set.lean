import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase2Tables

/-! Local-table `htab_set` world-typing transport and `MsgReady` assembly
for Phase 2 of `process_transaction`. -/

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

theorem worldTypedWith_htab_set_local {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaReady s) {S Nd : List Nat} (hW : WorldTypedWith s S Nd)
    {t : Nat} (htS : t ∈ S)
    (hlocal : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ t)
    (hAp : ArenaReady post) (hwf_t : HtabWF post t)
    (hhdr0_t : hdr post t 0 = hdr s t 0)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hfp_t : ∀ i ∈ htabFootprint post t, Allocated post i ∧
      ((∃ j ∈ htabFootprint s t, Inside i j.1 (j.1 + j.2)) ∨
        Inside i (globN s "heap_ptr") (globN s "heap_ptr" + (globN post "heap_ptr" - globN s "heap_ptr"))))
    (hfr : FrameOutside s post (htabFootprint s t)
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr"))
    (hbe : post.be = s.be)
    (hg_kept : ∀ name : MlS, name ∉ (["heap_ptr"] : List String).map ofString →
      s.globals.lookup name = post.globals.lookup name) :
    WorldTypedWith post S Nd ∧
    worldRoleSlots post = worldRoleSlots s ∧
    journalRoleSlots post = journalRoleSlots s ∧
    (∀ u ∈ S, hdr post u 0 = hdr s u 0) ∧
    OwnedGrows s post (worldOwned s S Nd) (worldOwned post S Nd) ∧
    (∀ b : Ivl, (b.2 = 0 → b.1 % 8 = 0) → Inside b sourceBase (globN s "heap_ptr") →
      (∀ j ∈ worldOwned s S Nd, Disj b j) →
      Inside b sourceBase (globN post "heap_ptr") ∧
      (∀ o ∈ worldOwned post S Nd, Disj b o) ∧
      IvlUnhit s post b) := by
  have hW_er := worldTypedWith_erase_local hW hlocal
  obtain ⟨hT, hJ, hF, hTr⟩ := hW
  have hgs : WorldGlobalsSame s post :=
    ⟨fun gn hgn => globN_eq_of_lookup (hg_kept (ofString gn.1)
        ((by decide : ∀ gn ∈ globalBuffers, ofString gn.1 ∉ (["heap_ptr"] : List String).map ofString) gn hgn)),
     fun g hg => globN_eq_of_lookup (hg_kept (ofString g)
        ((by decide : ∀ g ∈ globalTableRoots, ofString g ∉ (["heap_ptr"] : List String).map ofString) g hg)),
     globN_eq_of_lookup (hg_kept (ofString "journal") (by decide)),
     globN_eq_of_lookup (hg_kept (ofString "journal_cap") (by decide)),
     globN_eq_of_lookup (hg_kept (ofString "journal_n") (by decide))⟩
  have hag : AllocatorGrows s post := by
    refine ⟨hhp, ?_⟩
    rw [globN_eq_of_lookup (hg_kept (ofString "scratch_ptr") (by decide))]
  obtain ⟨hs_lo, _, _, _, _, hs_hp8, _, _⟩ := hAs.2
  obtain ⟨_, _, _, _, _, hp_hp8, _, _⟩ := hAp.2
  have hsb264 : sourceBase < 2 ^ 64 := by decide
  have hf_al : (globN s "heap_ptr") % 8 = 0 ∧ (globN post "heap_ptr" - globN s "heap_ptr") % 8 = 0 :=
    ⟨hs_hp8, by omega⟩
  have ht_al : ∀ j ∈ htabFootprint s t, j.1 % 8 = 0 ∧ j.2 % 8 = 0 := fun j hj => by
    have hw := ((hT.2.1 t htS).1.1 j hj).2
    exact ⟨hw.1, hw.2.1⟩
  have hm0 : memW post 0 = memW s 0 ∧ memW post 16 = memW s 16 := by
    have hlow : ∀ a : Nat, a + 8 ≤ sourceBase → memW post a = memW s a := fun a ha => by
      have ha_lt : a < 2 ^ 64 := by omega
      have hm := hfr (BitVec.ofNat 64 a)
        (fun j hj hcj => by
          obtain ⟨h1, _⟩ := hcj
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at h1
          have hlo := ((hT.2.1 t htS).1.1 j hj).1.1
          omega)
        (fun hcf => by
          obtain ⟨h1, _⟩ := hcf
          dsimp at h1
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at h1
          omega)
      unfold memW; rw [hm]
    exact ⟨hlow 0 (by decide), hlow 16 (by decide)⟩
  have hunhit_disj : ∀ i : Ivl, (i.2 = 0 → i.1 % 8 = 0) →
      (∀ j ∈ htabFootprint s t, Disj i j) →
      (i = (0, 0) ∨ Allocated s i) → IvlUnhit s post i := fun i hi0 hdi hal => by
    obtain ⟨hd_hp, _⟩ := ivl_disj_free_of_zero_or_allocated hAs.2 hAp.2 hag hal
    exact ivlUnhit_of_frameOutside_aligned hfr ht_al hf_al hi0 hdi hd_hp
  have hunhit_er_owned : ∀ o ∈ worldOwned s (S.erase t) Nd, IvlUnhit s post o := by
    intro o ho
    have hal := worldOwned_zero_or_allocated hW_er o ho
    apply hunhit_disj o (worldOwned_zero_aligned hW_er o ho) ?_ hal
    unfold worldOwned at ho
    rcases List.mem_append.1 ho with h1 | hnd
    · rcases List.mem_append.1 h1 with htab | hfix
      · obtain ⟨u, hu_er, ho_fp⟩ := List.mem_flatMap.1 htab
        obtain ⟨hne, huS⟩ := (List.Nodup.mem_erase_iff hT.1).1 hu_er
        exact fun j hj => hT.2.2.1 u huS t htS hne o ho_fp j hj
      · exact fun j hj => disj_symm (((hT.2.1 t htS).2 j hj).2 o hfix)
    · exact fun j hj => (hTr.2.1 o hnd).1 t htS j hj
  have hunhit_er : ∀ i ∈ worldTypedIvls s (S.erase t) Nd, IvlUnhit s post i :=
    unhit_of_worldTypedIvls hunhit_er_owned
  have hrec_ti : ∀ (g : String) (sz : Nat), (g, sz) ∈ typedRecords → sz ≠ 0 →
      globN s g ≠ 0 → (globN s g, sz) ∈ worldTypedIvls s (S.erase t) Nd := by
    intro g sz hrec hsz hnz
    apply mem_normalized (hn := fun h => absurd h hsz)
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
      (List.mem_map.2 ⟨(g, sz), hrec, by simp [hnz]⟩)))))
  have hbo_u : globN s "bo" ≠ 0 → IvlUnhit s post (globN s "bo", 88) := fun hnz =>
    hunhit_er _ (hrec_ti "bo" 88 (by simp [typedRecords]) (by decide) hnz)
  have hbase := worldTypedWith_congr_bo hAs hAp hbe hag hgs hW_er
    (fun u hu i hi => hunhit_er_owned i
      (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_flatMap.2 ⟨u, hu, hi⟩))))))
    (fun hnz => hunhit_er _ (hrec_ti "ws" 40 (by simp [typedRecords]) (by decide) hnz))
    (fun hnz => hunhit_er _ (hrec_ti "bs" 80 (by simp [typedRecords]) (by decide) hnz))
    (fun hnz => hunhit_er _ (hrec_ti "ts" 72 (by simp [typedRecords]) (by decide) hnz))
    (fun hnz => hunhit_er_owned _ (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr
      (fixed_mem_raw (by simp [fixedRaw]) (by dsimp; omega)))))))
    (fun i hi h24 => hunhit_er_owned i (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr
      (fixed_mem_raw (block_mem_raw hi) (by omega)))))))
    (fun i hi => by
      by_cases hz : i.2 = 0
      · have hb := normalized_mem_zero hi hz
        have hi_eq : i = (0, 0) := Prod.ext hb hz
        intro _ _ hch; rw [hi_eq] at hch; unfold CellHits at hch; dsimp at hch; omega
      · exact hunhit_er_owned i (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr
          (fixed_mem_raw (bal_mem_raw hi) hz))))))
    (fun o ho => hunhit_er_owned o (List.mem_append.2 (Or.inr ho)))
    (fun hnz k hk => by
      have hk_in : k % 8 = 0 ∧ k + 8 ≤ 88 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      have hbo_g : globN post "bo" = globN s "bo" := hgs.1 ("bo", 88) (by simp [globalBuffers])
      simpa [hbo_g] using
        rec_word_eq_of_unhit hAs.2 hW_er.2.2.1 "bo" 88 (by simp [typedRecords]) hbo_g hnz (hbo_u hnz) hk_in.1 hk_in.2)
    hm0
  obtain ⟨hW_post_er, howned_er, hwrs_eq, hjr_eq, hhdr_er⟩ := hbase
  have ht_fp_disj_er : ∀ i ∈ htabFootprint post t, ∀ o ∈ worldOwned post (S.erase t) Nd, Disj i o := by
    intro i hi o ho
    rw [howned_er] at ho
    rcases (hfp_t i hi).2 with ⟨j, hj, hin_j⟩ | hin_hp
    · apply disj_of_inside_left hin_j
      unfold worldOwned at ho
      rcases List.mem_append.1 ho with h1 | hnd
      · rcases List.mem_append.1 h1 with htab | hfix
        · obtain ⟨u, hu_er, ho_fp⟩ := List.mem_flatMap.1 htab
          obtain ⟨hne, huS⟩ := (List.Nodup.mem_erase_iff hT.1).1 hu_er
          exact hT.2.2.1 t htS u huS hne.symm j hj o ho_fp
        · exact ((hT.2.1 t htS).2 j hj).2 o hfix
      · exact disj_symm ((hTr.2.1 o hnd).1 t htS j hj)
    · obtain ⟨hd_hp, _⟩ := ivl_disj_free_of_zero_or_allocated hAs.2 hAp.2 hag
        (worldOwned_zero_or_allocated hW_er o ho)
      exact disj_symm (disj_of_inside_right hin_hp hd_hp)
  have ht_not_er : t ∉ S.erase t := by
    intro hm; exact ((List.Nodup.mem_erase_iff hT.1).1 hm).1 rfl
  have ht_nz : t ≠ 0 := fun h0 => zero_not_mem_S hT (h0 ▸ htS)
  obtain ⟨hT_er, hJ_er, hF_er, hTr_er⟩ := hW_post_er
  have hsub_add : ∀ u ∈ S.erase t, u ∈ S.erase t ++ [t] := fun u hu => List.mem_append.2 (Or.inl hu)
  have hroot_add : ∀ {v}, RootIn (S.erase t) v → RootIn (S.erase t ++ [t]) v := by
    rintro v (rfl | hv); exact Or.inl rfl; exact Or.inr (hsub_add v hv)
  have hval_add : ∀ {u}, HtabValuesIn post u (S.erase t) → HtabValuesIn post u (S.erase t ++ [t]) :=
    fun hv i hi => hsub_add _ (hv i hi)
  have hW_added : WorldTypedWith post (S.erase t ++ [t]) Nd := by
    obtain ⟨hnd_er, hTt_er, hTp_er, hws_er, hbs_er, hts_er, hg_er, hbsN_er, htsN_er, hbal_er, hbo_er, hroles_er⟩ := hT_er
    refine ⟨⟨List.nodup_append.2 ⟨hnd_er, List.nodup_singleton t, fun x hx y hy heq => by
        have := List.mem_singleton.1 hy; subst this; subst heq; exact ht_not_er hx⟩,
      ?_, ?_,
      fun k hk hnz => hroot_add (hws_er k hk hnz),
      fun k hk hnz => hroot_add (hbs_er k hk hnz),
      fun k hk hnz => hroot_add (hts_er k hk hnz),
      fun g hg => hroot_add (hg_er g hg),
      ?_, ?_,
      fun ad had => ⟨hsub_add _ (hbal_er ad had).1, hsub_add _ (hbal_er ad had).2.1, (hbal_er ad had).2.2⟩,
      hbo_er,
      ⟨fun a ha => ⟨hsub_add _ (hroles_er.1 a ha).1, (hroles_er.1 a ha).2⟩, hroles_er.2⟩⟩,
      ⟨hJ_er.1, hJ_er.2.1, hJ_er.2.2.1, fun i hi => hsub_add _ (hJ_er.2.2.2 i hi)⟩,
      hF_er,
      ⟨hTr_er.1, fun o ho => ⟨?_, (hTr_er.2.1 o ho).2⟩, ?_⟩⟩
    · intro u hu
      rcases List.mem_append.1 hu with huer | hut
      · exact hTt_er u huer
      · simp only [List.mem_singleton] at hut; subst hut
        refine ⟨hwf_t, fun i hi => ⟨(hfp_t i hi).1, fun j hj => ?_⟩⟩
        apply ht_fp_disj_er i hi j
        unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hj)))
    · intro u hu v hv hne i hi j hj
      rcases List.mem_append.1 hu with huer | hut <;> rcases List.mem_append.1 hv with hver | hvt
      · exact hTp_er u huer v hver hne i hi j hj
      · simp only [List.mem_singleton] at hvt; subst hvt
        apply disj_symm; apply ht_fp_disj_er j hj i
        unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_flatMap.2 ⟨u, huer, hi⟩))))
      · simp only [List.mem_singleton] at hut; subst hut
        apply ht_fp_disj_er i hi j
        unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_flatMap.2 ⟨v, hver, hj⟩))))
      · simp only [List.mem_singleton] at hut hvt; subst hut; exact absurd hvt.symm hne
    · intro hnz hm
      rcases List.mem_append.1 hm with hmer | hmt
      · exact hval_add (hbsN_er hnz hmer)
      · simp only [List.mem_singleton] at hmt
        rcases hbs_er 32 (by simp [bsTableSlots]) hnz with h0 | hmer
        · exact absurd (h0.symm.trans hmt).symm ht_nz
        · exact absurd (hmt ▸ hmer) ht_not_er
    · intro hnz hm
      rcases List.mem_append.1 hm with hmer | hmt
      · exact hval_add (htsN_er hnz hmer)
      · simp only [List.mem_singleton] at hmt
        rcases hts_er 32 (by simp [tsTableSlots]) hnz with h0 | hmer
        · exact absurd (h0.symm.trans hmt).symm ht_nz
        · exact absurd (hmt ▸ hmer) ht_not_er
    · intro u hu i hi
      rcases List.mem_append.1 hu with huer | hut
      · exact (hTr_er.2.1 o ho).1 u huer i hi
      · simp only [List.mem_singleton] at hut; subst hut
        apply disj_symm; apply ht_fp_disj_er i hi o
        unfold worldOwned; exact List.mem_append.2 (Or.inr ho)
    · intro hnz
      refine ⟨(hTr_er.2.2 hnz).1, fun hm => ?_⟩
      rcases List.mem_append.1 hm with hmer | hmt
      · exact (hTr_er.2.2 hnz).2 hmer
      · simp only [List.mem_singleton] at hmt
        rcases hws_er 32 (by simp [wsTableSlots]) hnz with h0 | hmer
        · exact absurd (h0.symm.trans hmt).symm ht_nz
        · exact absurd (hmt ▸ hmer) ht_not_er
  have hperm : (S.erase t ++ [t]).Perm S :=
    (List.perm_append_singleton t (S.erase t)).trans (List.perm_cons_erase htS).symm
  have hW_post : WorldTypedWith post S Nd := worldTypedWith_perm hperm hW_added
  have hhdr_all : ∀ u ∈ S, hdr post u 0 = hdr s u 0 := by
    intro u hu
    by_cases hut : u = t
    · subst hut; exact hhdr0_t
    · exact hhdr_er u ((List.Nodup.mem_erase_iff hT.1).2 ⟨hut, hu⟩)
  have hog : OwnedGrows s post (worldOwned s S Nd) (worldOwned post S Nd) := by
    intro o ho
    have hsub_ow_er : ∀ x ∈ worldOwned s (S.erase t) Nd, x ∈ worldOwned s S Nd := by
      intro x hx; unfold worldOwned at hx ⊢
      rcases List.mem_append.1 hx with h1 | hnd
      · apply List.mem_append.2; left
        rcases List.mem_append.1 h1 with htab | hfix
        · apply List.mem_append.2; left
          obtain ⟨u, huer, hxfp⟩ := List.mem_flatMap.1 htab
          exact List.mem_flatMap.2 ⟨u, List.mem_of_mem_erase huer, hxfp⟩
        · exact List.mem_append.2 (Or.inr hfix)
      · exact List.mem_append.2 (Or.inr hnd)
    unfold worldOwned at ho
    rcases List.mem_append.1 ho with h1 | hnd
    · rcases List.mem_append.1 h1 with htab | hfix
      · obtain ⟨u, huS, hofp⟩ := List.mem_flatMap.1 htab
        by_cases hut : u = t
        · subst hut
          rcases (hfp_t o hofp).2 with ⟨j, hj, hin_j⟩ | hin_hp
          · refine Or.inr (Or.inl ⟨j, ?_, hin_j⟩)
            unfold worldOwned
            exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_flatMap.2 ⟨u, huS, hj⟩))))
          · right; right
            unfold Inside at hin_hp ⊢; omega
        · have huer : u ∈ S.erase t := (List.Nodup.mem_erase_iff hT.1).2 ⟨hut, huS⟩
          have ho_er : o ∈ worldOwned post (S.erase t) Nd := by
            unfold worldOwned
            exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_flatMap.2 ⟨u, huer, hofp⟩))))
          rw [howned_er] at ho_er
          exact Or.inr (Or.inl ⟨o, hsub_ow_er o ho_er, ⟨le_rfl, le_rfl⟩⟩)
      · have ho_er : o ∈ worldOwned post (S.erase t) Nd := by
          unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hfix)))
        rw [howned_er] at ho_er
        exact Or.inr (Or.inl ⟨o, hsub_ow_er o ho_er, ⟨le_rfl, le_rfl⟩⟩)
    · have ho_er : o ∈ worldOwned post (S.erase t) Nd := by
        unfold worldOwned; exact List.mem_append.2 (Or.inr hnd)
      rw [howned_er] at ho_er
      exact Or.inr (Or.inl ⟨o, hsub_ow_er o ho_er, ⟨le_rfl, le_rfl⟩⟩)
  refine ⟨hW_post, hwrs_eq, hjr_eq, hhdr_all, hog, ?_⟩
  intro b hb0 hb_in hb_disj
  obtain ⟨hd_hp, _⟩ := ivl_disj_free_of_zero_or_allocated hAs.2 hAp.2 hag (Or.inr (Or.inl hb_in))
  refine ⟨⟨hb_in.1, Nat.le_trans hb_in.2 hhp⟩, ?_, ?_⟩
  · intro o ho
    rcases hog o ho with rfl | ⟨j, hj, hin_j⟩ | hin_hp
    · exact disj_zero_right b
    · exact disj_of_inside_right hin_j (hb_disj j hj)
    · exact Or.inr (Or.inr (Or.inl (Nat.le_trans hb_in.2 hin_hp.1)))
  · exact ivlUnhit_of_frameOutside_aligned hfr ht_al hf_al hb0
      (fun j hj => hb_disj j (by
        unfold worldOwned
        exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_flatMap.2 ⟨t, htS, hj⟩))))))
      hd_hp

theorem rolesOK_msgReady {F : Type} {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hT : TablesTyped s S)
    {aa ak : Nat}
    (haa_S : aa ∈ S) (hak_S : ak ∈ S) (haa_ne_ak : aa ≠ ak)
    (haa_klen : hdr s aa 0 = 20) (hak_klen : hdr s ak 0 = 52)
    (haa_local : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ aa)
    (hak_local : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ ak) :
    RolesOK s S (worldRoleSlots s ++ [(aa, "frame.addr"), (ak, "frame.key")]) (journalRoleSlots s) := by
  have hroles := hT.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨hr1, hr2, hr3⟩ := hroles
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    rw [List.append_assoc] at ha
    rcases List.mem_append.1 ha with hw | hrest
    · exact hr1 a (List.mem_append.2 (Or.inl hw))
    · rcases List.mem_append.1 hrest with hfk | hjr
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfk
        rcases hfk with rfl | rfl
        · exact ⟨haa_S, haa_klen⟩
        · exact ⟨hak_S, hak_klen⟩
      · exact hr1 a (List.mem_append.2 (Or.inr hjr))
  · rw [List.pairwise_append]
    refine ⟨hr2, ?_, ?_⟩
    · rw [List.pairwise_cons]
      refine ⟨fun b hb heq => ?_, List.pairwise_singleton _ _⟩
      simp only [List.mem_singleton] at hb; subst hb
      exact absurd heq haa_ne_ak
    · intro a ha b hb heq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact absurd heq (haa_local a (List.mem_append.2 (Or.inl ha)))
      · exact absurd heq (hak_local a (List.mem_append.2 (Or.inl ha)))
  · intro a ha b hb heq
    rw [List.append_assoc] at hb
    rcases List.mem_append.1 hb with hw | hrest
    · exact hr3 a ha b (List.mem_append.2 (Or.inl hw)) heq
    · rcases List.mem_append.1 hrest with hfk | hjr
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfk
        rcases hfk with rfl | rfl
        · exact absurd heq (haa_local a (List.mem_append.2 (Or.inr ha)))
        · exact absurd heq (hak_local a (List.mem_append.2 (Or.inr ha)))
      · exact hr3 a ha b (List.mem_append.2 (Or.inr hjr)) heq

theorem msgReady_of_parts {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaReady s) {S Nd : List Nat} (hW : WorldTypedWith s S Nd)
    {m aa ak : Nat} (hm_loc : locN s "msg" = m)
    (hm152 : memW s (m + 152) = aa) (hm160 : memW s (m + 160) = ak)
    (haa_S : aa ∈ S) (hak_S : ak ∈ S) (haa_ne_ak : aa ≠ ak)
    (haa_klen : hdr s aa 0 = 20) (hak_klen : hdr s ak 0 = 52)
    (haa_local : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ aa)
    (hak_local : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ ak)
    (hm_in : Inside (m, 176) sourceBase (globN s "heap_ptr"))
    (hm8 : m % 8 = 0)
    (hm_disj : ∀ o ∈ worldOwned s S Nd, Disj (m, 176) o)
    (hmgas : memW s (m + 40) < 2 ^ 63) :
    MsgReady s := by
  have hm_words : WordsOK s (m, 176) := by
    refine ⟨hm8, by omega, fun k hk => ?_⟩
    have hhi := (ivl_allocated_bound hA.2 (Or.inl hm_in)).1
    exact wordAt_of_ordinary hA.1 (by omega) (by unfold Inside at hm_in; omega) (by dsimp at hhi; omega)
  refine ⟨hA, S, ⟨hW.1, hW.2.1, hW.2.2.1, Nd, hW.2.2.2⟩, ?_⟩
  rw [hm_loc, hm152, hm160]
  refine ⟨haa_S, hak_S, hm_in, hm_words, ?_, ?_, ?_, hmgas,
    rolesOK_msgReady hW.1 haa_S hak_S haa_ne_ak haa_klen hak_klen haa_local hak_local⟩
  · intro t ht i hi
    exact hm_disj i (by unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_flatMap.2 ⟨t, ht, hi⟩)))))
  · intro j hj
    exact hm_disj j (by unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hj))))
  · refine ⟨Nd, hW.2.2.2, fun o ho j hj => ?_⟩
    simp only [List.mem_singleton] at ho; subst ho
    exact hm_disj j (by unfold worldOwned; exact List.mem_append.2 (Or.inr hj))

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.Phase2
